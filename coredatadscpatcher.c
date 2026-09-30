/*
 * coredatapatcher.c
 *
 * Patches the iOS 8.x arm64 dyld shared cache to fix
 * -[NSSQLCore fileProtectionLevel] in CoreData.framework,
 * making it unconditionally return 0 (NSFileProtectionNone).
 *
 * NSSQLCore caches the store's requested data-protection class in a
 * 3-bit bitfield ("fileProtectionType") inside its private _sqlCoreFlags
 * ivar. fileProtectionLevel is just a getter that ubfx's those 3 bits
 * back out. Forcing it to always return 0 means CoreData never asks to
 * open/create a SQLite store under a protected class (Complete /
 * CompleteUntilFirstUserAuthentication / CompleteUnlessOpen), which is
 * what triggers the SQLITE_CANTOPEN (14) -> NSCocoaErrorDomain 256 ->
 * "no persistent stores" abort seen in assetsd on an incompatible
 * (10.3.3) SEP.
 *
 * Note: this only affects the *request* CoreData makes when it creates
 * a store. It does not change the on-disk protection class of files
 * that already exist. Existing Photos.sqlite / WAL / SHM files created
 * under a protected class will still need to be deleted so they get
 * recreated unprotected after this patch is applied.
 *
 * Strategy:
 *   -[NSSQLCore fileProtectionLevel] begins with:
 *     adrp x8, #<page>              ; ivar-offset var page
 *     ldrsw x8, [x8, #<off>]        ; OBJC_IVAR_$_NSSQLCore._sqlCoreFlags
 *     ldr  w8, [x0, x8]             ; load _sqlCoreFlags
 *     ubfx w0, w8, #6, #3           ; extract fileProtectionType
 *     ret
 *   We replace the first two instructions (adrp + ldrsw, 8 bytes) with
 *   "mov w0, #0 / ret", so the function always returns 0 regardless of
 *   self or the real flags value.
 *
 *   The patch site is located robustly: parse DSC header -> mappings ->
 *   image list -> find CoreData Mach-O -> walk ObjC class list for
 *   NSSQLCore -> walk method list for fileProtectionLevel -> convert IMP
 *   vmaddr to cache file offset -> verify exact original bytes -> patch.
 *
 * Usage:
 *   ./coredatapatcher <input_cache> <output_cache>
 *   Patch notes written to <output_cache>.patch
 *
 * Build:
 *   gcc -Wall -o coredatapatcher coredatapatcher.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>

/* ── DSC structures ─────────────────────────────────────────────────────── */

#define DSC_MAGIC_ARM64 "dyld_v1   arm64"

typedef struct {
    char     magic[16];
    uint32_t mappingOffset;
    uint32_t mappingCount;
    uint32_t imagesOffset;
    uint32_t imagesCount;
    uint64_t dyldBaseAddress;
    /* ... more fields we don't need */
} dsc_header;

typedef struct {
    uint64_t address;
    uint64_t size;
    uint64_t fileOffset;
    uint32_t maxProt;
    uint32_t initProt;
} dsc_mapping;

typedef struct {
    uint64_t address;
    uint64_t modTime;
    uint64_t inode;
    uint32_t pathFileOffset;
    uint32_t pad;
} dsc_image;

/* ── Mach-O structures (64-bit LE) ─────────────────────────────────────── */

#define MH_MAGIC_64    0xFEEDFACFU
#define LC_SEGMENT_64  0x19U
#define LC_ID_DYLIB    0x0DU

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
    uint64_t name;
    uint64_t baseMethods;
    uint64_t baseProtocols, ivars, weakIvarLayout, baseProperties;
} class_ro64;

typedef struct { uint32_t entsizeAndFlags, count; } method_list_hdr;

typedef struct {
    uint64_t name;
    uint64_t types;
    uint64_t imp;
} method64;

/* ── patch constants ─────────────────────────────────────────────────────── */

#define TARGET_LIB      "CoreData"
#define TARGET_CLASS    "NSSQLCore"
#define TARGET_SEL      "fileProtectionLevel"

/*
 * IMP first two instructions (prologue):
 *   adrp  x8, #<page>          e.g. LE: E8 F8 08 90 (8.2) / 08 AB 08 F0 (8.0)
 *   ldrsw x8, [x8, #0x340]     LE: 08 41 83 B9
 *
 * The adrp immediate encodes a PC-relative *page* address for the
 * compiler-generated ivar-offset variable (OBJC_IVAR_$_NSSQLCore.
 * _sqlCoreFlags). That variable lives at a different address in each
 * build's __DATA, so the adrp immediate bits differ release to release
 * even though it's functionally the same instruction (adrp x8, #page).
 * We verify it by opcode+register only (mask off the immediate), and
 * verify the ldrsw exactly, since that operand (#0x340, the ivar's byte
 * offset within the object) is stable as long as the ivar layout is
 * unchanged.
 *
 * Replacement:
 *   mov w0, #0                  = 0x52800000  LE: 00 00 80 52
 *   ret                         = 0xD65F03C0  LE: C0 03 5F D6
 *
 * Effect: fileProtectionLevel always returns 0 (NSFileProtectionNone),
 * so CoreData never requests a protected data-protection class when
 * creating/opening a SQLite persistent store.
 */

/* ADRP <Xd>, #imm : bit31=1 (op), bits28:24=0b10000, bits4:0=Rd.
 * immlo (bits30:29) and immhi (bits23:5) are the variable page offset,
 * so they're masked out. We require Rd == x8. */
#define ADRP_X8_MASK   0x9F00001Fu
#define ADRP_X8_VALUE  0x90000008u

/* LDRSW X8, [X8, #0x340] -- fixed, stable across builds */
#define LDRSW_X8_X8_0x340  0xB9834108u

static const uint8_t PATCHED[8] = {
    0x00, 0x00, 0x80, 0x52,   /* mov w0, #0 */
    0xC0, 0x03, 0x5F, 0xD6    /* ret        */
};

static int site_matches_original(const uint8_t *site, uint32_t *out_word1)
{
    uint32_t word1, word2;
    memcpy(&word1, site,     4);   /* assumes LE host; fine on x86/arm64 */
    memcpy(&word2, site + 4, 4);
    if (out_word1) *out_word1 = word1;
    return (word1 & ADRP_X8_MASK) == ADRP_X8_VALUE &&
           word2 == LDRSW_X8_X8_0x340;
}

/* ── globals ─────────────────────────────────────────────────────────────── */

static uint8_t  *g_buf  = NULL;
static size_t    g_size = 0;

static dsc_mapping g_mappings[32];
static uint32_t    g_nmappings = 0;

/* ── helpers ─────────────────────────────────────────────────────────────── */

static uint64_t vm2fo(uint64_t vmaddr)
{
    for (uint32_t i = 0; i < g_nmappings; i++) {
        dsc_mapping *m = &g_mappings[i];
        if (vmaddr >= m->address && vmaddr < m->address + m->size)
            return m->fileOffset + (vmaddr - m->address);
    }
    return UINT64_MAX;
}

static int infile(uint64_t fo, size_t n)
{
    return fo != UINT64_MAX && fo + n <= g_size;
}

static const char *vmstr(uint64_t vmaddr)
{
    uint64_t fo = vm2fo(vmaddr);
    if (!infile(fo, 1)) return NULL;
    uint8_t *p = g_buf + fo;
    uint8_t *end = g_buf + g_size;
    if (!memchr(p, 0, (size_t)(end - p))) return NULL;
    return (const char *)p;
}

/* ── find IMP ────────────────────────────────────────────────────────────── */

static uint64_t find_imp(void)
{
    dsc_header *hdr = (dsc_header *)g_buf;

    if (g_size < sizeof(dsc_header) ||
        memcmp(hdr->magic, DSC_MAGIC_ARM64, strlen(DSC_MAGIC_ARM64)) != 0) {
        fprintf(stderr, "error: not an arm64 dyld shared cache\n");
        return 0;
    }

    uint32_t moff = hdr->mappingOffset;
    uint32_t mcnt = hdr->mappingCount;
    if (mcnt > 32) mcnt = 32;
    g_nmappings = mcnt;
    for (uint32_t i = 0; i < mcnt; i++) {
        uint64_t entry = moff + (uint64_t)i * sizeof(dsc_mapping);
        if (!infile(entry, sizeof(dsc_mapping))) break;
        memcpy(&g_mappings[i], g_buf + entry, sizeof(dsc_mapping));
    }
    printf("[*] Loaded %u DSC mappings\n", g_nmappings);

    uint32_t ioff = hdr->imagesOffset;
    uint32_t icnt = hdr->imagesCount;
    printf("[*] Scanning %u DSC images for %s...\n", icnt, TARGET_LIB);

    for (uint32_t i = 0; i < icnt; i++) {
        uint64_t ientry = ioff + (uint64_t)i * sizeof(dsc_image);
        if (!infile(ientry, sizeof(dsc_image))) break;

        dsc_image img;
        memcpy(&img, g_buf + ientry, sizeof(dsc_image));

        uint64_t img_fo = vm2fo(img.address);
        if (!infile(img_fo, sizeof(mach_header_64))) continue;

        mach_header_64 *mh = (mach_header_64 *)(g_buf + img_fo);
        if (mh->magic != MH_MAGIC_64) continue;

        int is_target = 0;
        uint8_t *lc = g_buf + img_fo + sizeof(mach_header_64);
        uint8_t *lc_end = lc + mh->sizeofcmds;
        uint8_t *lc_ptr = lc;

        for (uint32_t c = 0; c < mh->ncmds && lc_ptr + 8 <= lc_end; c++) {
            uint32_t cmd     = *(uint32_t *)(lc_ptr);
            uint32_t cmdsize = *(uint32_t *)(lc_ptr + 4);
            if (cmdsize == 0 || lc_ptr + cmdsize > lc_end) break;

            if (cmd == LC_ID_DYLIB) {
                uint32_t name_off = *(uint32_t *)(lc_ptr + 8);
                const char *dylib_name = (const char *)(lc_ptr + name_off);
                if ((uint8_t *)dylib_name < lc_end &&
                    strstr(dylib_name, TARGET_LIB)) {
                    is_target = 1;
                    printf("[*] Found %s: image[%u] vmaddr=%#llx name=%s\n",
                           TARGET_LIB, i,
                           (unsigned long long)img.address, dylib_name);
                    break;
                }
            }
            lc_ptr += cmdsize;
        }
        if (!is_target) continue;

        /*
         * Found CoreData. Scan the whole cache file in 8-byte steps for a
         * class_ro64 whose name field resolves to "NSSQLCore". Same
         * approach as the PhotoLibraryServices/installd/containermanagerd
         * patchers in this toolset.
         */
        printf("[*] Scanning for class_ro64 '%s'...\n", TARGET_CLASS);

        for (uint64_t fo = 0;
             fo + sizeof(class_ro64) <= g_size;
             fo += 8)
        {
            class_ro64 *ro = (class_ro64 *)(g_buf + fo);

            uint64_t name_fo = vm2fo(ro->name);
            if (!infile(name_fo, 1)) continue;

            const char *cn = (const char *)(g_buf + name_fo);
            if (strcmp(cn, TARGET_CLASS) != 0) continue;

            if (!ro->baseMethods) continue;
            uint64_t ml_fo = vm2fo(ro->baseMethods);
            if (!infile(ml_fo, sizeof(method_list_hdr))) continue;

            method_list_hdr *mlh = (method_list_hdr *)(g_buf + ml_fo);
            if (!mlh->count || mlh->count > 512) continue;

            printf("[*] Found %s class_ro64 at file offset %#llx "
                   "(%u methods)\n",
                   TARGET_CLASS, (unsigned long long)fo, mlh->count);

            uint64_t arr_fo = ml_fo + sizeof(method_list_hdr);
            for (uint32_t m = 0; m < mlh->count; m++) {
                uint64_t mfo = arr_fo + (uint64_t)m * sizeof(method64);
                if (!infile(mfo, sizeof(method64))) break;

                method64 *mt = (method64 *)(g_buf + mfo);
                const char *sel = vmstr(mt->name);
                if (!sel || strcmp(sel, TARGET_SEL) != 0) continue;

                printf("[*] Found: -[%s %s]\n", TARGET_CLASS, sel);
                printf("[*] IMP vmaddr:         %#llx\n",
                       (unsigned long long)mt->imp);

                uint64_t imp_fo = vm2fo(mt->imp);
                printf("[*] IMP cache fileoff:  %#llx\n",
                       (unsigned long long)imp_fo);

                if (!infile(imp_fo, 8)) {
                    fprintf(stderr,
                        "error: IMP file offset %#llx is outside cache\n",
                        (unsigned long long)imp_fo);
                    return 0;
                }
                return mt->imp;
            }
        }

        fprintf(stderr,
            "error: found %s but could not locate "
            "-[%s %s] in method list\n",
            TARGET_LIB, TARGET_CLASS, TARGET_SEL);
        return 0;
    }

    fprintf(stderr, "error: %s not found in DSC image list\n", TARGET_LIB);
    return 0;
}

/* ── main ────────────────────────────────────────────────────────────────── */

int main(int argc, char *argv[])
{
    if (argc != 3) {
        fprintf(stderr,
            "usage: %s <input_cache> <output_cache>\n"
            "       Patches -[NSSQLCore fileProtectionLevel] in CoreData.framework\n"
            "       to always return 0 (NSFileProtectionNone), preventing CoreData\n"
            "       from requesting a protected data-protection class on stores it\n"
            "       creates/opens -- fixes assetsd crashes on an incompatible SEP.\n"
            "       Patch notes written to <output_cache>.patch\n",
            argv[0]);
        return 1;
    }

    const char *in_path  = argv[1];
    const char *out_path = argv[2];

    FILE *fp = fopen(in_path, "rb");
    if (!fp) { perror(in_path); return 1; }
    fseek(fp, 0, SEEK_END);
    g_size = (size_t)ftell(fp); rewind(fp);
    g_buf = malloc(g_size);
    if (!g_buf) {
        fprintf(stderr, "error: out of memory (%zu bytes)\n", g_size);
        fclose(fp); return 1;
    }
    if (fread(g_buf, 1, g_size, fp) != g_size) {
        fprintf(stderr, "error: short read\n"); fclose(fp); return 1;
    }
    fclose(fp);
    printf("[*] Loaded %s (%zu bytes)\n", in_path, g_size);

    uint64_t imp_vm = find_imp();
    if (!imp_vm) { free(g_buf); return 1; }

    uint64_t patch_fo = vm2fo(imp_vm);

    printf("[*] Patch site vmaddr:      %#llx\n", (unsigned long long)imp_vm);
    printf("[*] Patch site cache_foff:  %#llx\n", (unsigned long long)patch_fo);

    if (!infile(patch_fo, 8)) {
        fprintf(stderr, "error: patch site outside cache bounds\n");
        free(g_buf); return 1;
    }

    uint8_t *site = g_buf + patch_fo;
    uint32_t orig_word1 = 0;

    printf("[*] Bytes at site: %02X %02X %02X %02X %02X %02X %02X %02X\n",
           site[0], site[1], site[2], site[3],
           site[4], site[5], site[6], site[7]);

    if (!site_matches_original(site, &orig_word1)) {
        fprintf(stderr,
            "error: unexpected instructions at patch site.\n"
            "       Expected adrp x8,#<page> ; ldrsw x8,[x8,#0x340] but\n"
            "       got word1=%#010x word2=%#010x.\n"
            "       Cache may already be patched, wrong version, or the\n"
            "       ivar layout changed in this build. Aborting rather\n"
            "       than patching blind.\n",
            *(uint32_t *)site, *(uint32_t *)(site + 4));
        free(g_buf); return 1;
    }
    printf("[*] Pre-patch verification passed (adrp x8,#0x%x_page "
           "+ ldrsw x8,[x8,#0x340] confirmed)\n", orig_word1 & ~ADRP_X8_MASK);

    uint8_t original[8];
    memcpy(original, site, 8);

    memcpy(site, PATCHED, 8);
    printf("[*] Patch applied:\n"
           "[*]   adrp x8,#page          ->  mov w0, #0\n"
           "[*]   ldrsw x8,[x8,#0x340]   ->  ret\n");

    FILE *out = fopen(out_path, "wb");
    if (!out) { perror(out_path); free(g_buf); return 1; }
    if (fwrite(g_buf, 1, g_size, out) != g_size) {
        fprintf(stderr, "error: write failed\n"); fclose(out); free(g_buf); return 1;
    }
    fclose(out);

    struct stat st;
    if (stat(in_path, &st) == 0) chmod(out_path, st.st_mode);
    printf("[*] Patched cache -> %s\n", out_path);

    size_t sp_len = strlen(out_path) + 8;
    char *sidecar = malloc(sp_len);
    snprintf(sidecar, sp_len, "%s.patch", out_path);

    FILE *pf = fopen(sidecar, "w");
    if (pf) {
        fprintf(pf, "dyld_arm64_cache patch: fileProtectionLevel force-None\n");
        fprintf(pf, "========================================================\n\n");
        fprintf(pf, "Target framework:\n");
        fprintf(pf, "  CoreData.framework (in dyld shared cache)\n\n");
        fprintf(pf, "Target method:\n");
        fprintf(pf, "  -[NSSQLCore fileProtectionLevel]\n\n");
        fprintf(pf, "Problem:\n");
        fprintf(pf, "  NSSQLCore stores the requested SQLite data-protection class\n");
        fprintf(pf, "  as a 3-bit field in its private _sqlCoreFlags ivar:\n\n");
        fprintf(pf, "    beganTransaction:1 ignoreEntityCaching:1 storeMetadataClean:1\n");
        fprintf(pf, "    useToManyCaching:1 useSyntaxColoredLogging:1\n");
        fprintf(pf, "    checkedExternalReferences:1 fileProtectionType:3 _RESERVED:23\n\n");
        fprintf(pf, "  fileProtectionLevel just extracts that field (ubfx w0,w8,#6,#3).\n");
        fprintf(pf, "  On an incompatible (10.3.3) SEP, opening/creating a SQLite store\n");
        fprintf(pf, "  under a protected class (e.g. NSFileProtectionComplete-\n");
        fprintf(pf, "  UntilFirstUserAuthentication, the Photos.sqlite default) fails\n");
        fprintf(pf, "  because the class key can't be unwrapped. sqlite3_open returns\n");
        fprintf(pf, "  SQLITE_CANTOPEN (14), CoreData surfaces NSCocoaErrorDomain 256,\n");
        fprintf(pf, "  -addPersistentStoreWithType:...: fails, and callers like assetsd\n");
        fprintf(pf, "  that don't handle the failure hit\n");
        fprintf(pf, "  'NSPersistentStoreCoordinator has no persistent stores' and abort.\n\n");
        fprintf(pf, "Solution:\n");
        fprintf(pf, "  Force fileProtectionLevel to always return 0 (NSFileProtectionNone)\n");
        fprintf(pf, "  so CoreData never asks for a protected class in the first place.\n");
        fprintf(pf, "  We replace the first two instructions of the IMP (adrp + ldrsw,\n");
        fprintf(pf, "  8 bytes) with mov w0, #0 / ret -- the smallest change that makes\n");
        fprintf(pf, "  the getter unconditionally report 'None' without touching the\n");
        fprintf(pf, "  ivar layout, the setter, or any other code.\n\n");
        fprintf(pf, "  NOTE: this changes what new/rewritten stores request. Any existing\n");
        fprintf(pf, "  Photos.sqlite / -wal / -shm files already created under a protected\n");
        fprintf(pf, "  class still carry that class on-disk and must be deleted so they\n");
        fprintf(pf, "  get recreated unprotected once this patch is loaded.\n\n");
        fprintf(pf, "ARM64 encoding (this build):\n");
        fprintf(pf, "  adrp  x8, #page           LE: %02X %02X %02X %02X"
                    "  (immediate varies per build/link address)\n",
                original[0], original[1], original[2], original[3]);
        fprintf(pf, "  ldrsw x8, [x8, #0x340]    LE: %02X %02X %02X %02X"
                    "  (fixed -- same ivar offset every build)\n",
                original[4], original[5], original[6], original[7]);
        fprintf(pf, "  mov w0, #0  = MOVZ W0,#0   = 0x52800000  LE: 00 00 80 52\n");
        fprintf(pf, "  ret         = RET           = 0xD65F03C0  LE: C0 03 5F D6\n\n");
        fprintf(pf, "Binary patch:\n");
        fprintf(pf, "  Cache file:   %s\n", in_path);
        fprintf(pf, "  IMP vmaddr:   %#016llx\n", (unsigned long long)imp_vm);
        fprintf(pf, "  Cache offset: %#016llx\n\n", (unsigned long long)patch_fo);
        fprintf(pf, "  Offset         Before                               After\n");
        fprintf(pf, "  %#010llx   %02X %02X %02X %02X %02X %02X %02X %02X"
                    "   %02X %02X %02X %02X %02X %02X %02X %02X\n\n",
                (unsigned long long)patch_fo,
                original[0],original[1],original[2],original[3],
                original[4],original[5],original[6],original[7],
                PATCHED[0], PATCHED[1], PATCHED[2], PATCHED[3],
                PATCHED[4], PATCHED[5], PATCHED[6], PATCHED[7]);
        fprintf(pf, "Pairs well with:\n");
        fprintf(pf, "  dscpatcher.c (-[PLModelMigrator skipDataProtectionForFilePath:])\n");
        fprintf(pf, "  which stops PhotoLibraryServices from calling\n");
        fprintf(pf, "  fcntl(F_SETPROTECTIONCLASS) on Photos files in the first place.\n");
        fprintf(pf, "  This patch handles the CoreData/SQLite side of the same problem.\n");
        fclose(pf);
        printf("[*] Patch notes   -> %s\n", sidecar);
    }

    free(sidecar);
    free(g_buf);
    printf("\n[+] Done.\n");
    return 0;
}
