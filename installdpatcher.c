/*
 * installpatcher.c
 *
 * Patches -[MIFileManager createDirectoryAtURL:withIntermediateDirectories:mode:class:error:]
 * in iOS 8.x installd (arm64) to bypass fcntl(F_SETPROTECTIONCLASS) against an
 * incompatible SEP, using the function's own built-in class=-1 skip path.
 *
 * Identical strategy to containermanagerdpatcher: force x21 = -1 at IMP+0x20
 * so the cmn w21,#1 / b.eq at IMP+0xf8/0xfc always branches to the success path.
 *
 * The difference from containermanagerd:
 *   - Class is MIFileManager (MobileInstallation.framework) not MCMFileManager
 *   - IMP prologue is one instruction longer (stp x26,x25 before stp x24,x23)
 *     so the mov x21, x5 is at IMP+0x20 not IMP+0x1c
 *   - Everything else (bypass branch, success path encoding) is identical
 *
 * Usage:
 *   ./installpatcher <input> <output>
 *   Patch notes written to <output>.patch
 *
 * Build:
 *   gcc -Wall -o installpatcher installpatcher.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>

/* ── Mach-O (64-bit LE) ─────────────────────────────────────────────────── */

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

/* ── ObjC (old pointer ABI, iOS 8 arm64) ────────────────────────────────── */

typedef struct {
    uint32_t flags, instanceStart, instanceSize, reserved;
    uint64_t ivarLayout;
    uint64_t name;        /* -> const char* */
    uint64_t baseMethods; /* -> method_list_t */
    uint64_t baseProtocols, ivars, weakIvarLayout, baseProperties;
} class_ro64;

typedef struct { uint32_t entsizeAndFlags, count; } method_list_hdr;

typedef struct {
    uint64_t name;  /* SEL  -> const char* */
    uint64_t types; /* const char*         */
    uint64_t imp;   /* IMP vmaddr          */
} method64;

/* ── patch constants ─────────────────────────────────────────────────────── */

#define TARGET_CLASS  "MIFileManager"
#define TARGET_SEL    "createDirectoryAtURL:withIntermediateDirectories:mode:class:error:"

/*
 * IMP layout (installd 8.2 arm64):
 *   IMP+0x00  stp x26, x25, [sp, #-0x50]!   ; prologue (one extra stp vs containermanagerd)
 *   IMP+0x04  stp x24, x23, [sp, #0x10]
 *   IMP+0x08  stp x22, x21, [sp, #0x20]
 *   IMP+0x0c  stp x20, x19, [sp, #0x30]
 *   IMP+0x10  stp x29, x30, [sp, #0x40]
 *   IMP+0x14  add x29, sp,  #0x40
 *   IMP+0x18  sub sp,  sp,  #0x20
 *   IMP+0x1c  mov x20, x6          ; save error** arg
 *   IMP+0x20  mov x21, x5          ; save class arg  <-- PATCH HERE
 *   ...
 *   IMP+0xf8  cmn w21, #1          ; if (class == -1)
 *   IMP+0xfc  b.eq skip_fcntl      ;   skip opendir+fcntl
 *   ...
 *   skip_fcntl:
 *   IMP+0x1bc mov x21, #0          ; error = nil
 *   IMP+0x1c0 mov w23, #1          ; return YES
 */
#define PATCH_OFFSET_FROM_IMP 0x20

/* mov x21, x5   = ORR X21, XZR, X5 = 0xAA0503F5  LE: F5 03 05 AA */
static const uint8_t EXPECTED[4] = { 0xF5, 0x03, 0x05, 0xAA };

/* movn x21, #0  = MOVN X21, #0     = 0x92800015  LE: 15 00 80 92
   -> X21 = 0xFFFFFFFFFFFFFFFF, W21 = 0xFFFFFFFF = -1 (int32)
   -> cmn w21, #1 sets Z flag -> b.eq taken -> skip fcntl */
static const uint8_t PATCHED[4]  = { 0x15, 0x00, 0x80, 0x92 };

/* ── globals ─────────────────────────────────────────────────────────────── */

static uint8_t *g_buf  = NULL;
static size_t   g_size = 0;
static uint64_t g_slide = 0;

/* ── helpers ─────────────────────────────────────────────────────────────── */

static uint64_t    vm2fo(uint64_t vm)          { return vm - g_slide; }
static int         infile(uint64_t fo, size_t n) { return fo + n <= g_size; }
static const char *vmstr(uint64_t vm) {
    if (vm < g_slide) return NULL;
    uint64_t fo = vm2fo(vm);
    if (fo >= g_size) return NULL;
    uint8_t *p = g_buf + fo;
    if (!memchr(p, 0, g_size - fo)) return NULL;
    return (const char *)p;
}

/* ── find IMP ────────────────────────────────────────────────────────────── */

static uint64_t find_imp(void)
{
    mach_header_64 *hdr = (mach_header_64 *)g_buf;
    if (g_size < sizeof(*hdr) || hdr->magic != MH_MAGIC_64) {
        fprintf(stderr, "error: not a 64-bit Mach-O (LE)\n"); return 0;
    }

    /* Find __TEXT slide */
    uint8_t *lc = g_buf + sizeof(mach_header_64);
    for (uint32_t i = 0; i < hdr->ncmds; i++) {
        segment_command_64 *seg = (segment_command_64 *)lc;
        if (seg->cmd == LC_SEGMENT_64
            && strncmp(seg->segname, "__TEXT", 6) == 0
            && seg->fileoff == 0 && seg->vmaddr != 0) {
            g_slide = seg->vmaddr; break;
        }
        lc += seg->cmdsize;
    }
    if (g_slide == 0) {
        fprintf(stderr, "error: no __TEXT segment\n"); return 0;
    }

    /* Scan for class_ro64 with name == TARGET_CLASS */
    for (uint64_t fo = 0; fo + sizeof(class_ro64) <= g_size; fo += 8) {
        class_ro64 *ro = (class_ro64 *)(g_buf + fo);
        if (ro->name < g_slide || ro->name >= g_slide + g_size) continue;
        const char *cn = vmstr(ro->name);
        if (!cn || strcmp(cn, TARGET_CLASS) != 0) continue;
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
            if (!sel || strcmp(sel, TARGET_SEL) != 0) continue;

            printf("[*] Found: -[%s %s]\n", TARGET_CLASS, sel);
            printf("[*] IMP vmaddr:   0x%016llx\n", (unsigned long long)mt->imp);
            printf("[*] IMP fileoff:  0x%llx\n",    (unsigned long long)vm2fo(mt->imp));
            return mt->imp;
        }
    }

    fprintf(stderr, "error: could not find -[%s %s]\n", TARGET_CLASS, TARGET_SEL);
    fprintf(stderr, "       Is this iOS 8.x arm64 installd?\n");
    return 0;
}

/* ── main ────────────────────────────────────────────────────────────────── */

int main(int argc, char *argv[])
{
    if (argc != 3) {
        fprintf(stderr,
            "usage: %s <input_binary> <output_binary>\n"
            "       Patches -[MIFileManager createDirectoryAtURL:...:mode:class:error:]\n"
            "       to skip fcntl(F_SETPROTECTIONCLASS) on incompatible SEP.\n",
            argv[0]);
        return 1;
    }

    const char *in_path  = argv[1];
    const char *out_path = argv[2];

    /* load */
    FILE *fp = fopen(in_path, "rb");
    if (!fp) { perror(in_path); return 1; }
    fseek(fp, 0, SEEK_END);
    g_size = (size_t)ftell(fp); rewind(fp);
    g_buf = malloc(g_size);
    if (!g_buf) { fprintf(stderr, "error: out of memory\n"); fclose(fp); return 1; }
    if (fread(g_buf, 1, g_size, fp) != g_size) {
        fprintf(stderr, "error: short read\n"); fclose(fp); return 1;
    }
    fclose(fp);
    printf("[*] Loaded %s (%zu bytes)\n", in_path, g_size);

    /* find IMP */
    uint64_t imp_vm = find_imp();
    if (!imp_vm) { free(g_buf); return 1; }

    /* patch site */
    uint64_t patch_vm = imp_vm + PATCH_OFFSET_FROM_IMP;
    uint64_t patch_fo = vm2fo(patch_vm);
    printf("[*] Patch site vmaddr:  0x%016llx\n", (unsigned long long)patch_vm);
    printf("[*] Patch site fileoff: 0x%llx\n",    (unsigned long long)patch_fo);

    if (!infile(patch_fo, 4)) {
        fprintf(stderr, "error: patch site outside file bounds\n"); free(g_buf); return 1;
    }

    uint8_t *site = g_buf + patch_fo;
    printf("[*] Bytes at site: %02X %02X %02X %02X  (expected: %02X %02X %02X %02X)\n",
           site[0], site[1], site[2], site[3],
           EXPECTED[0], EXPECTED[1], EXPECTED[2], EXPECTED[3]);

    if (memcmp(site, EXPECTED, 4) != 0) {
        fprintf(stderr,
            "error: unexpected bytes at patch site.\n"
            "       Already patched, wrong version, or IMP relocated. Aborting.\n");
        free(g_buf); return 1;
    }
    printf("[*] Pre-patch check passed  (mov x21, x5 confirmed)\n");

    memcpy(site, PATCHED, 4);
    printf("[*] Patch applied:  mov x21, x5  ->  movn x21, #0  (x21 = -1)\n");

    /* write output */
    FILE *out = fopen(out_path, "wb");
    if (!out) { perror(out_path); free(g_buf); return 1; }
    if (fwrite(g_buf, 1, g_size, out) != g_size) {
        fprintf(stderr, "error: write failed\n"); fclose(out); free(g_buf); return 1;
    }
    fclose(out);
    struct stat st;
    if (stat(in_path, &st) == 0) chmod(out_path, st.st_mode);
    printf("[*] Patched binary -> %s\n", out_path);

    /* sidecar */
    size_t sp_len = strlen(out_path) + 8;
    char *sidecar = malloc(sp_len);
    snprintf(sidecar, sp_len, "%s.patch", out_path);
    FILE *pf = fopen(sidecar, "w");
    if (pf) {
        fprintf(pf, "installd patch: MIFileManager class=-1 bypass\n");
        fprintf(pf, "==============================================\n\n");
        fprintf(pf, "Target method:\n");
        fprintf(pf, "  -[%s %s]\n\n", TARGET_CLASS, TARGET_SEL);
        fprintf(pf, "Problem:\n");
        fprintf(pf, "  installd uses MIFileManager (MobileInstallation.framework) to create\n");
        fprintf(pf, "  directories for app staging, log, and data paths. Each call includes a\n");
        fprintf(pf, "  Data Protection class argument (typically 4 = NSFileProtectionNone or\n");
        fprintf(pf, "  3 = CompleteUntilFirstUserAuthentication). On iOS 8.x with an iOS 10.3.3\n");
        fprintf(pf, "  SEP, the fcntl(fd, F_SETPROTECTIONCLASS=0x40, class) call inside this\n");
        fprintf(pf, "  method fails with ENOTSUP (errno 45), causing installd to abort setting\n");
        fprintf(pf, "  up its directories and crash-loop on every boot.\n\n");
        fprintf(pf, "Solution:\n");
        fprintf(pf, "  The IMP contains a built-in bypass: when the class argument is -1 the\n");
        fprintf(pf, "  opendir/dirfd/fcntl sequence is skipped entirely:\n\n");
        fprintf(pf, "    IMP+0x00  stp  x26, x25, [sp, #-0x50]!  ; prologue\n");
        fprintf(pf, "    IMP+0x04  stp  x24, x23, [sp, #0x10]\n");
        fprintf(pf, "    IMP+0x08  stp  x22, x21, [sp, #0x20]\n");
        fprintf(pf, "    IMP+0x0c  stp  x20, x19, [sp, #0x30]\n");
        fprintf(pf, "    IMP+0x10  stp  x29, x30, [sp, #0x40]\n");
        fprintf(pf, "    IMP+0x14  add  x29, sp,  #0x40\n");
        fprintf(pf, "    IMP+0x18  sub  sp,  sp,  #0x20\n");
        fprintf(pf, "    IMP+0x1c  mov  x20, x6          ; save error** arg\n");
        fprintf(pf, "    IMP+0x20  mov  x21, x5          ; save class arg  <-- PATCH HERE\n");
        fprintf(pf, "    ...       mkpath_np / mkdir path ...\n");
        fprintf(pf, "    IMP+0xf8  cmn  w21, #1          ; if (class == -1)\n");
        fprintf(pf, "    IMP+0xfc  b.eq skip_fcntl       ;   jump over opendir+fcntl\n");
        fprintf(pf, "    ...       opendir / dirfd / fcntl(F_SETPROTECTIONCLASS) ...\n");
        fprintf(pf, "    skip_fcntl:\n");
        fprintf(pf, "    IMP+0x1bc mov  x21, #0          ; error = nil\n");
        fprintf(pf, "    IMP+0x1c0 mov  w23, #1          ; return YES\n\n");
        fprintf(pf, "  Patching IMP+0x20 (mov x21, x5) to (movn x21, #0) forces x21=-1\n");
        fprintf(pf, "  unconditionally. Directories are created by mkpath_np/mkdir normally;\n");
        fprintf(pf, "  only the protection class assignment via the SEP is skipped.\n\n");
        fprintf(pf, "Note:\n");
        fprintf(pf, "  This is the same pattern as the containermanagerd MCMFileManager patch.\n");
        fprintf(pf, "  The only structural difference is the prologue saves x26/x25 first\n");
        fprintf(pf, "  (one extra stp), pushing the mov x21,x5 from IMP+0x1c to IMP+0x20.\n\n");
        fprintf(pf, "Binary patch:\n");
        fprintf(pf, "  File:         %s\n", in_path);
        fprintf(pf, "  IMP vmaddr:   0x%016llx\n", (unsigned long long)imp_vm);
        fprintf(pf, "  Patch vmaddr: 0x%016llx  (IMP + 0x%x)\n",
                (unsigned long long)patch_vm, PATCH_OFFSET_FROM_IMP);
        fprintf(pf, "  Patch offset: 0x%llx\n\n", (unsigned long long)patch_fo);
        fprintf(pf, "  Offset       Before                          After\n");
        fprintf(pf, "  0x%08llx  %02X %02X %02X %02X  (mov  x21, x5)   %02X %02X %02X %02X  (movn x21, #0)\n\n",
                (unsigned long long)patch_fo,
                EXPECTED[0], EXPECTED[1], EXPECTED[2], EXPECTED[3],
                PATCHED[0],  PATCHED[1],  PATCHED[2],  PATCHED[3]);
        fprintf(pf, "ARM64 encoding:\n");
        fprintf(pf, "  mov  x21, x5   ORR X21, XZR, X5    sf=1 N=1 Rm=5 Rd=21  -> 0xAA0503F5\n");
        fprintf(pf, "  movn x21, #0   MOVN X21, #0, lsl#0 sf=1 opc=00 hw=00 imm16=0 Rd=21 -> 0x92800015\n");
        fprintf(pf, "  (little-endian in file: F5 03 05 AA  ->  15 00 80 92)\n");
        fclose(pf);
        printf("[*] Patch notes   -> %s\n", sidecar);
    }
    free(sidecar);
    free(g_buf);
    printf("\n[+] Done.\n");
    return 0;
}
