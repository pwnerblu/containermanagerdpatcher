/*
 * containermanagerdpatcher.c
 *
 * Patches -[MCMFileManager createDirectoryAtURL:withIntermediateDirectories:mode:class:error:]
 * in iOS 8.x containermanagerd (arm64) to skip the fcntl(F_SETPROTECTIONCLASS) call
 * that fails against an incompatible SEP, using the function's own built-in bypass path.
 *
 * The IMP already has:
 *   0x10000fb04: mov  x21, x5      <- save class arg
 *   ...
 *   0x10000fbb0: cmn  w21, #1      <- if (class == -1)
 *   0x10000fbb4: b.eq skip_fcntl  <- skip opendir + fcntl(F_SETPROTECTIONCLASS)
 *
 * We patch the first instruction to:
 *   movn x21, #0                   <- force x21 = -1 regardless of caller's class arg
 *
 * This makes the function skip SEP interaction entirely and just create the directory,
 * returning YES with no error -- using the code path that was always there.
 *
 * Usage:
 *   ./containermanagerdpatcher <input> <output>
 *   (patch notes written to <output>.patch)
 *
 * Build:
 *   gcc -Wall -o containermanagerdpatcher containermanagerdpatcher.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>

/* ── Mach-O structures (64-bit LE only) ─────────────────────────────────── */

#define MH_MAGIC_64   0xFEEDFACFU
#define LC_SEGMENT_64 0x19U

typedef struct {
    uint32_t magic, cputype, cpusubtype, filetype;
    uint32_t ncmds, sizeofcmds, flags, reserved;
} mach_header_64;

typedef struct {
    uint32_t cmd, cmdsize;
    char     segname[16];
    uint64_t vmaddr, vmsize, fileoff, filesize;
    uint32_t maxprot, initprot, nsects, flags;
} segment_command_64;

/* ── ObjC runtime structures (old pointer ABI, iOS 8 arm64) ─────────────── */

typedef struct {
    uint32_t flags, instanceStart, instanceSize, reserved;
    uint64_t ivarLayout;
    uint64_t name;          /* -> const char* */
    uint64_t baseMethods;   /* -> method_list_t */
    uint64_t baseProtocols;
    uint64_t ivars;
    uint64_t weakIvarLayout;
    uint64_t baseProperties;
} class_ro64;

typedef struct {
    uint32_t entsizeAndFlags;
    uint32_t count;
} method_list_hdr;

typedef struct {
    uint64_t name;   /* SEL -> const char* */
    uint64_t types;  /* const char*        */
    uint64_t imp;    /* IMP vmaddr         */
} method64;

/* ── patch constants ─────────────────────────────────────────────────────── */

/*
 * We match any selector that starts with this prefix. The full selector is
 * "createDirectoryAtURL:withIntermediateDirectories:mode:class:error:"
 * but we use a prefix match to handle any trailing variation.
 */
#define TARGET_SEL "createDirectoryAtURL:withIntermediateDirectories:mode:class:error:"

/*
 * Patch site: IMP + 0x1c bytes (7th instruction, after the callee-save prologue).
 *
 * IMP+0x00  stp x24, x23, [sp, #-0x40]!    ; prologue
 * IMP+0x04  stp x22, x21, [sp, #0x10]
 * IMP+0x08  stp x20, x19, [sp, #0x20]
 * IMP+0x0c  stp x29, x30, [sp, #0x30]
 * IMP+0x10  add x29, sp,  #0x30
 * IMP+0x14  sub sp,  sp,  #0x20
 * IMP+0x18  mov x20, x6                     ; save error** arg
 * IMP+0x1c  mov x21, x5   <-- PATCH HERE   ; save class arg
 *
 * Before: mov x21, x5   = ORR X21, XZR, X5 = 0xAA0503F5 (LE bytes: F5 03 05 AA)
 * After:  movn x21, #0  = MOVN X21, #0      = 0x92800015 (LE bytes: 15 00 80 92)
 *
 * ARM64 MOVN encoding: sf(1)|opc(2=00)|100101|hw(2)|imm16(16)|Rd(5)
 *   sf=1, opc=00 (MOVN), hw=00 (lsl 0), imm16=0x0000, Rd=21
 *   = 1_00_100101_00_0000000000000000_10101 = 0x92800015
 *   W21 = lower 32 bits = 0xFFFFFFFF = -1 as int32, so cmn w21,#1 sets Z flag -> b.eq taken.
 */
#define PATCH_OFFSET_FROM_IMP 0x1c

static const uint8_t EXPECTED[4] = { 0xF5, 0x03, 0x05, 0xAA };  /* mov  x21, x5  (0xAA0503F5) */
static const uint8_t PATCHED[4]  = { 0x15, 0x00, 0x80, 0x92 };  /* movn x21, #0  (0x92800015) */

/* ── globals ─────────────────────────────────────────────────────────────── */

static uint8_t *g_buf  = NULL;
static size_t   g_size = 0;
static uint64_t g_slide = 0;   /* vmaddr of __TEXT - fileoff of __TEXT (= vmaddr since fileoff=0) */

/* ── helpers ─────────────────────────────────────────────────────────────── */

static uint64_t vm2fo(uint64_t vm)   { return vm - g_slide; }
static int      infile(uint64_t fo, size_t n) { return fo + n <= g_size; }

static const char *vmstr(uint64_t vm)
{
    if (vm < g_slide) return NULL;
    uint64_t fo = vm2fo(vm);
    if (fo >= g_size) return NULL;
    uint8_t *p = g_buf + fo;
    if (!memchr(p, 0, g_size - fo)) return NULL;
    return (const char *)p;
}

/* ── find the IMP ────────────────────────────────────────────────────────── */

static uint64_t find_imp(void)
{
    /* Verify Mach-O magic */
    mach_header_64 *hdr = (mach_header_64 *)g_buf;
    if (g_size < sizeof(*hdr) || hdr->magic != MH_MAGIC_64) {
        fprintf(stderr, "error: not a 64-bit Mach-O (LE)\n");
        return 0;
    }

    /* Pass 1: find __TEXT slide */
    uint8_t *lc = g_buf + sizeof(mach_header_64);
    for (uint32_t i = 0; i < hdr->ncmds; i++) {
        segment_command_64 *seg = (segment_command_64 *)lc;
        if (seg->cmd == LC_SEGMENT_64
            && strncmp(seg->segname, "__TEXT", 6) == 0
            && seg->fileoff == 0 && seg->vmaddr != 0)
        {
            g_slide = seg->vmaddr;
            break;
        }
        lc += seg->cmdsize;
    }

    if (g_slide == 0) {
        fprintf(stderr, "error: could not find __TEXT segment\n");
        return 0;
    }

    /*
     * Pass 2: scan entire file in 8-byte steps for a class_ro64 whose name
     * field resolves to exactly "MCMFileManager".  Then walk its method list
     * for our target selector.  This approach is robust: it doesn't rely on
     * section names or hardcoded offsets.
     */
    for (uint64_t fo = 0; fo + sizeof(class_ro64) <= g_size; fo += 8) {
        class_ro64 *ro = (class_ro64 *)(g_buf + fo);

        /* Filter: name must be a plausible vmaddr pointing into the file */
        if (ro->name < g_slide || ro->name >= g_slide + g_size) continue;

        const char *cn = vmstr(ro->name);
        if (!cn || strcmp(cn, "MCMFileManager") != 0) continue;

        /* baseMethods must be non-zero and within file */
        if (ro->baseMethods == 0) continue;
        uint64_t ml_fo = vm2fo(ro->baseMethods);
        if (!infile(ml_fo, sizeof(method_list_hdr))) continue;

        method_list_hdr *mlh = (method_list_hdr *)(g_buf + ml_fo);
        if (mlh->count == 0 || mlh->count > 512) continue;

        uint64_t arr_fo = ml_fo + sizeof(method_list_hdr);
        for (uint32_t m = 0; m < mlh->count; m++) {
            uint64_t mfo = arr_fo + (uint64_t)m * sizeof(method64);
            if (!infile(mfo, sizeof(method64))) break;

            method64 *mt = (method64 *)(g_buf + mfo);
            if (mt->name < g_slide || mt->name >= g_slide + g_size) continue;

            const char *sel = vmstr(mt->name);
            if (!sel) continue;

            if (strcmp(sel, TARGET_SEL) == 0) {
                printf("[*] Found: -[MCMFileManager %s]\n", sel);
                printf("[*] IMP vmaddr:   0x%016llx\n", (unsigned long long)mt->imp);
                printf("[*] IMP fileoff:  0x%llx\n",
                       (unsigned long long)vm2fo(mt->imp));
                return mt->imp;
            }
        }
    }

    fprintf(stderr, "error: could not find -[MCMFileManager %s]\n", TARGET_SEL);
    fprintf(stderr, "       Is this the right binary? Only iOS 8.x arm64 containermanagerd is supported.\n");
    return 0;
}

/* ── main ────────────────────────────────────────────────────────────────── */

int main(int argc, char *argv[])
{
    if (argc != 3) {
        fprintf(stderr,
            "usage: %s <input_binary> <output_binary>\n"
            "       Writes patched binary to <output_binary>\n"
            "       Writes patch notes to  <output_binary>.patch\n",
            argv[0]);
        return 1;
    }

    const char *in_path  = argv[1];
    const char *out_path = argv[2];

    /* ── load ── */
    FILE *fp = fopen(in_path, "rb");
    if (!fp) { perror(in_path); return 1; }
    fseek(fp, 0, SEEK_END);
    g_size = (size_t)ftell(fp);
    rewind(fp);
    g_buf = malloc(g_size);
    if (!g_buf) { fprintf(stderr, "error: out of memory\n"); fclose(fp); return 1; }
    if (fread(g_buf, 1, g_size, fp) != g_size) {
        fprintf(stderr, "error: short read\n"); fclose(fp); return 1;
    }
    fclose(fp);
    printf("[*] Loaded %s (%zu bytes)\n", in_path, g_size);

    /* ── find IMP ── */
    uint64_t imp_vm = find_imp();
    if (!imp_vm) { free(g_buf); return 1; }

    /* ── locate and verify patch site ── */
    uint64_t patch_vm = imp_vm + PATCH_OFFSET_FROM_IMP;
    uint64_t patch_fo = vm2fo(patch_vm);

    printf("[*] Patch site vmaddr:  0x%016llx\n", (unsigned long long)patch_vm);
    printf("[*] Patch site fileoff: 0x%llx\n",    (unsigned long long)patch_fo);

    if (!infile(patch_fo, 4)) {
        fprintf(stderr, "error: patch site falls outside the file\n");
        free(g_buf); return 1;
    }

    uint8_t *site = g_buf + patch_fo;
    printf("[*] Bytes at site: %02X %02X %02X %02X  (expected: %02X %02X %02X %02X)\n",
           site[0], site[1], site[2], site[3],
           EXPECTED[0], EXPECTED[1], EXPECTED[2], EXPECTED[3]);

    if (memcmp(site, EXPECTED, 4) != 0) {
        fprintf(stderr,
            "error: unexpected bytes at patch site.\n"
            "       Binary may already be patched, wrong version, or IMP was relocated.\n"
            "       Aborting without modifying anything.\n");
        free(g_buf); return 1;
    }
    printf("[*] Pre-patch check passed  (mov x21, x5 confirmed)\n");

    /* ── apply patch ── */
    memcpy(site, PATCHED, 4);
    printf("[*] Patch written:  mov x21, x5  ->  movn x21, #0  (x21 = -1)\n");

    /* ── write patched binary ── */
    FILE *out = fopen(out_path, "wb");
    if (!out) { perror(out_path); free(g_buf); return 1; }
    if (fwrite(g_buf, 1, g_size, out) != g_size) {
        fprintf(stderr, "error: write failed\n"); fclose(out); free(g_buf); return 1;
    }
    fclose(out);

    /* preserve mode bits from original */
    struct stat st;
    if (stat(in_path, &st) == 0)
        chmod(out_path, st.st_mode);

    printf("[*] Patched binary -> %s\n", out_path);

    /* ── write .patch sidecar ── */
    size_t sp_len = strlen(out_path) + 8;
    char *sidecar = malloc(sp_len);
    snprintf(sidecar, sp_len, "%s.patch", out_path);

    FILE *pf = fopen(sidecar, "w");
    if (pf) {
        fprintf(pf, "containermanagerd patch: class=-1 bypass\n");
        fprintf(pf, "=========================================\n\n");
        fprintf(pf, "Target method:\n");
        fprintf(pf, "  -[MCMFileManager %s]\n\n", TARGET_SEL);
        fprintf(pf, "Problem:\n");
        fprintf(pf, "  iOS 8.x containermanagerd calls fcntl(fd, F_SETPROTECTIONCLASS=0x40, class)\n");
        fprintf(pf, "  via opendir/dirfd to assign a Data Protection class to every new container\n");
        fprintf(pf, "  directory. When booting iOS 8.x against an iOS 10.3.3 SEP (incompatible key\n");
        fprintf(pf, "  material / different epoch), this fcntl fails, containermanagerd cannot\n");
        fprintf(pf, "  create app containers, and the device hangs at the Apple logo.\n\n");
        fprintf(pf, "Solution:\n");
        fprintf(pf, "  The IMP has a built-in bypass when the class argument is -1:\n\n");
        fprintf(pf, "    IMP+0x00: stp  x24, x23, [sp, #-0x40]!  ; callee-save prologue\n");
        fprintf(pf, "    IMP+0x04: stp  x22, x21, [sp, #0x10]\n");
        fprintf(pf, "    IMP+0x08: stp  x20, x19, [sp, #0x20]\n");
        fprintf(pf, "    IMP+0x0c: stp  x29, x30, [sp, #0x30]\n");
        fprintf(pf, "    IMP+0x10: add  x29, sp,  #0x30\n");
        fprintf(pf, "    IMP+0x14: sub  sp,  sp,  #0x20\n");
        fprintf(pf, "    IMP+0x18: mov  x20, x6          ; save error** arg\n");
        fprintf(pf, "    IMP+0x1c: mov  x21, x5          ; x21 = class arg  <-- PATCH HERE\n");
        fprintf(pf, "    ...       (mkpath_np / mkdir call)\n");
        fprintf(pf, "    IMP+0xc8: cmn  w21, #1          ; if (x21 == -1)\n");
        fprintf(pf, "    IMP+0xcc: b.eq skip_fcntl       ;   skip opendir + fcntl entirely\n");
        fprintf(pf, "    IMP+0xd0: (opendir / dirfd / fcntl(F_SETPROTECTIONCLASS) path)\n");
        fprintf(pf, "    skip_fcntl:\n");
        fprintf(pf, "    IMP+0x174: mov  x21, #0         ; error = nil\n");
        fprintf(pf, "    IMP+0x178: mov  w23, #1         ; return YES\n\n");
        fprintf(pf, "  We patch IMP+0x04 (mov x21, x5) to (movn x21, #0), forcing the class\n");
        fprintf(pf, "  register to -1 unconditionally. The directory is still created by\n");
        fprintf(pf, "  mkpath_np/mkdir normally; only the protection class assignment is skipped.\n");
        fprintf(pf, "  No NSError is set. The function returns YES. One 4-byte write.\n\n");
        fprintf(pf, "Binary patch:\n");
        fprintf(pf, "  File:         %s\n", in_path);
        fprintf(pf, "  IMP vmaddr:   0x%016llx\n", (unsigned long long)imp_vm);
        fprintf(pf, "  Patch vmaddr: 0x%016llx  (IMP + %d)\n",
                (unsigned long long)patch_vm, PATCH_OFFSET_FROM_IMP);
        fprintf(pf, "  Patch offset: 0x%llx\n\n", (unsigned long long)patch_fo);
        fprintf(pf, "  Offset       Before                       After\n");
        fprintf(pf, "  0x%08llx  %02X %02X %02X %02X  (mov x21, x5)    %02X %02X %02X %02X  (movn x21, #0 / mov x21, #-1)\n\n",
                (unsigned long long)patch_fo,
                EXPECTED[0], EXPECTED[1], EXPECTED[2], EXPECTED[3],
                PATCHED[0],  PATCHED[1],  PATCHED[2],  PATCHED[3]);
        fprintf(pf, "ARM64 encoding:\n");
        fprintf(pf, "  mov  x21, x5   ORR X21, XZR, X5   sf=1 N=1 Rm=5 Rd=21  -> 0xAA0503F5\n");
        fprintf(pf, "  movn x21, #0   MOVN X21, #0,lsl#0  sf=1 opc=00 hw=00 imm16=0 Rd=21 -> 0x92800015\n");
        fprintf(pf, "  (little-endian in file: F5 03 05 AA  ->  15 00 80 92)\n\n");
        fprintf(pf, "Side effects:\n");
        fprintf(pf, "  - App container directories have no Data Protection class (equivalent\n");
        fprintf(pf, "    to NSFileProtectionNone / class D). Files within them inherit whatever\n");
        fprintf(pf, "    protection class the VFS assigns by default (typically unprotected).\n");
        fprintf(pf, "  - The no-class: variant of createDirectoryAtURL: is unaffected (it\n");
        fprintf(pf, "    already passes class=-1 and behaves identically after this patch).\n");
        fprintf(pf, "  - removeItemAtURL:, copy/move methods, and all other MCMFileManager\n");
        fprintf(pf, "    methods are unmodified.\n");
        fclose(pf);
        printf("[*] Patch notes   -> %s\n", sidecar);
    } else {
        fprintf(stderr, "warning: could not write sidecar: %s\n", strerror(errno));
    }
    free(sidecar);
    free(g_buf);

    printf("\n[+] Done.\n");
    return 0;
}
