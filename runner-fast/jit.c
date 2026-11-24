/* The driver: which functions to compile, the cache, the C compiler,
   and loading the compiled code.

   The functions compiled are those that the terms on standard input
   name, and every function their code can call: the closure, which the
   driver finds by building (reading and compiling to the machine's
   code) each definition in it.  A definition that cannot be built is
   left alone, so that the interpreter stops at its call as the
   reference does.  The unit of compilation is a define line.  Each unit
   is written as C (gen.c), named by a hash of that C, and compiled once
   into an object file in the cache; the units of a run are linked into
   one shared library, named by a hash of the names of its units, and
   loaded.  Anything that fails here leaves the run to the interpreter.

   The places it uses are found when it runs: the root of the
   repository is BOYMOO_FAST_ROOT, or the current directory; the C it
   writes includes fastrt.h from ROOT/runner-fast and run.h from
   ROOT/runner; and the cache is BOYMOO_FAST_CACHE, or
   ROOT/build/runner-fast/cache. */

#include <dlfcn.h>
#include <spawn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include "fast.h"

extern char **environ;

/* The options of the C compiler for the code written. */
#ifndef FAST_CFLAGS
#define FAST_CFLAGS "-O2"
#endif

static int verbose;

static void note(const char *fmt, const char *a)
{
    if (verbose) {
        fputs("boymoo-run-fast: ", stderr);
        fprintf(stderr, fmt, a);
        fputc('\n', stderr);
    }
}

/* A hash of 128 bits, as 32 hexadecimal digits. */
static void hash128(const char *s, size_t n, const char *salt, char hex[33])
{
    unsigned long long h1 = 1469598103934665603ULL, h2 = 0x9E3779B97F4A7C15ULL;
    size_t i;
    for (; *salt; salt++) {
        h1 = (h1 ^ (unsigned char)*salt) * 1099511628211ULL;
        h2 = (h2 ^ (unsigned char)*salt) * 0x100000001B3ULL + 0x632BE59BD9B4E019ULL;
    }
    for (i = 0; i < n; i++) {
        h1 = (h1 ^ (unsigned char)s[i]) * 1099511628211ULL;
        h2 = ((h2 ^ (unsigned char)s[i]) * 0x100000001B3ULL) ^ (h2 >> 29);
    }
    h1 ^= h1 >> 33; h1 *= 0xFF51AFD7ED558CCDULL; h1 ^= h1 >> 33;
    h2 ^= h2 >> 31; h2 *= 0xC4CEB9FE1A85EC53ULL; h2 ^= h2 >> 33;
    snprintf(hex, 33, "%016llx%016llx", h1, h2);
}

void hash128_text(const char *s, size_t n, char hex[33])
{
    hash128(s, n, "fingerprint", hex);
}

/* Function numbers by the text of their names. */
typedef struct { char *name; size_t len; long k; } NameEnt;
static NameEnt *ntab;
static size_t ntab_cap;

static unsigned long hstr(const char *s, size_t n)
{
    unsigned long h = 2166136261UL;
    while (n-- > 0)
        h = (h ^ (unsigned char)*s++) * 16777619UL;
    return h;
}

static void names_build(void)
{
    size_t k, i, cnt = 0;
    for (k = 0; k < nfns; k++)
        if (fns[k].line != NULL)
            cnt++;
    for (ntab_cap = 1024; ntab_cap < 2 * cnt + 2; ntab_cap *= 2)
        ;
    ntab = calloc(ntab_cap, sizeof(NameEnt));
    for (k = 0; k < nfns; k++) {
        if (fns[k].line == NULL)
            continue;
        out_len = 0;
        print_datum(fns[k].sym);
        i = hstr(out, out_len) & (ntab_cap - 1);
        while (ntab[i].name != NULL)
            i = (i + 1) & (ntab_cap - 1);
        ntab[i].name = malloc(out_len);
        memcpy(ntab[i].name, out, out_len);
        ntab[i].len = out_len;
        ntab[i].k = (long)k;
    }
}

static long names_find(const unsigned char *s, size_t n)
{
    size_t i = hstr((const char *)s, n) & (ntab_cap - 1);
    for (; ntab[i].name != NULL; i = (i + 1) & (ntab_cap - 1))
        if (ntab[i].len == n && memcmp(ntab[i].name, s, n) == 0)
            return ntab[i].k;
    return -1;
}

/* The closure. */
static long *work;
static size_t nwork, work_cap;
static char *seen;

static void add(long k)
{
    if (k < 0 || (size_t)k >= nfns || seen[k])
        return;
    seen[k] = 1;
    if (nwork == work_cap) {
        work_cap = work_cap ? 2 * work_cap : 1024;
        work = realloc(work, work_cap * sizeof(long));
    }
    work[nwork++] = k;
}

/* The words of standard input that may name functions. */
static void scan_input(const unsigned char *p, size_t n)
{
    const unsigned char *e = p + n, *s;
    while (p < e) {
        unsigned c = *p;
        if (c == '"') {
            for (p++; p < e && *p != '"' && *p != '\n'; p++)
                if (*p == '\\')
                    p++;
            p++;
        } else if (c == '#' && p + 1 < e && p[1] == '\\') {
            p += 3;
        } else if (c == ' ' || c == '(' || c == ')' || c == '\n' || c == '\'') {
            p++;
        } else {
            s = p;
            while (p < e && *p != ' ' && *p != '(' && *p != ')' && *p != '\n') {
                if (*p == '|') {
                    for (p++; p < e && *p != '|' && *p != '\n'; p++)
                        if (*p == '\\')
                            p++;
                }
                p++;
            }
            if (p > e)
                p = e;
            add(names_find(s, (size_t)(p - s)));
        }
    }
}

typedef struct {
    const unsigned char *line;
    long *fn;           /* its functions, by position */
    size_t n;
    char hash[33];
    char *c;            /* its C, while it is needed */
    size_t clen;
} Unit;
static Unit *units;
static size_t nunits;

static int unit_cmp(const void *a, const void *b)
{
    return strcmp(((const Unit *)a)->hash, ((const Unit *)b)->hash);
}

static int pos_cmp(const void *a, const void *b)
{
    long x = *(const long *)a, y = *(const long *)b;
    return fns[x].pos - fns[y].pos;
}

static int line_cmp(const void *a, const void *b)
{
    const unsigned char *x = fns[*(const long *)a].line, *y = fns[*(const long *)b].line;
    if (x != y)
        return x < y ? -1 : 1;
    return pos_cmp(a, b);
}

static int ptr_cmp(const void *a, const void *b)
{
    const unsigned char *x = *(const unsigned char *const *)a, *y = *(const unsigned char *const *)b;
    return x < y ? -1 : x > y;
}

static int exists(const char *path)
{
    struct stat st;
    return stat(path, &st) == 0;
}

static int write_file(const char *path, const char *s, size_t n)
{
    FILE *f = fopen(path, "wb");
    if (f == NULL)
        return 0;
    if (fwrite(s, 1, n, f) != n) {
        fclose(f);
        return 0;
    }
    return fclose(f) == 0;
}

/* Runs shell commands, at most two at a time; 1 if all succeed. */
static int run_all(char **cmds, size_t n)
{
    pid_t pids[2];
    size_t next = 0, running = 0, i;
    int ok = 1, st;
    while (next < n || running > 0) {
        while (running < 2 && next < n && ok) {
            char *argv[4];
            argv[0] = "/bin/sh";
            argv[1] = "-c";
            argv[2] = cmds[next];
            argv[3] = NULL;
            note("%s", cmds[next]);
            if (posix_spawn(&pids[running], "/bin/sh", NULL, NULL, argv, environ) != 0) {
                ok = 0;
                break;
            }
            running++;
            next++;
        }
        if (running == 0)
            break;
        {
            pid_t p = wait(&st);
            if (p < 0)
                return 0;
            for (i = 0; i < running; i++)
                if (pids[i] == p) {
                    pids[i] = pids[running - 1];
                    running--;
                    break;
                }
            if (!WIFEXITED(st) || WEXITSTATUS(st) != 0)
                ok = 0;
        }
    }
    return ok;
}

/* Each batch of units is written and compiled in a folder of this
   process, and each object then moved into the cache by a rename, so
   that runs at the same time never see half of a file. */
static int compile_units(const char *cache, const char *src)
{
    char **cmds = NULL, path[4096], tmpdir[4096];
    size_t ncmds = 0, i = 0, j, bytes;
    int ok;
    char *cmd, *mv;
    size_t len, cap, mlen, mcap;
    snprintf(tmpdir, sizeof tmpdir, "%s/obj/tmp%ld", cache, (long)getpid());
    mkdir(tmpdir, 0777);
    while (i < nunits) {
        if (exists((snprintf(path, sizeof path, "%s/obj/%s.o", cache, units[i].hash), path))) {
            i++;
            continue;
        }
        cap = 4096;
        cmd = malloc(cap);
        mcap = 4096;
        mv = malloc(mcap);
        len = (size_t)snprintf(cmd, cap, "cd '%s' && cc %s -w -fPIC %s -c", tmpdir, FAST_CFLAGS, src);
        mlen = (size_t)snprintf(mv, mcap, " && mv");
        bytes = 0;
        for (j = 0; i < nunits && j < 200 && bytes < 1500000; i++) {
            snprintf(path, sizeof path, "%s/obj/%s.o", cache, units[i].hash);
            if (exists(path))
                continue;
            snprintf(path, sizeof path, "%s/%s.c", tmpdir, units[i].hash);
            if (!write_file(path, units[i].c, units[i].clen))
                return 0;
            if (len + 64 > cap) {
                cap *= 2;
                cmd = realloc(cmd, cap);
            }
            if (mlen + 64 > mcap) {
                mcap *= 2;
                mv = realloc(mv, mcap);
            }
            len += (size_t)snprintf(cmd + len, cap - len, " %s.c", units[i].hash);
            mlen += (size_t)snprintf(mv + mlen, mcap - mlen, " %s.o", units[i].hash);
            bytes += units[i].clen;
            j++;
        }
        cmd = realloc(cmd, len + mlen + 64);
        snprintf(cmd + len, mlen + 64, " %s %s .. %s", verbose ? "1>&2" : ">/dev/null 2>&1", mv,
                 verbose ? "1>&2" : ">/dev/null 2>&1");
        free(mv);
        cmds = realloc(cmds, (ncmds + 1) * sizeof(char *));
        cmds[ncmds++] = cmd;
    }
    ok = run_all(cmds, ncmds);
    for (i = 0; i < ncmds; i++)
        free(cmds[i]);
    free(cmds);
    if (getenv("BOYMOO_FAST_KEEP") == NULL) {
        for (i = 0; i < nunits; i++) {
            snprintf(path, sizeof path, "%s/%s.c", tmpdir, units[i].hash);
            remove(path);
            snprintf(path, sizeof path, "%s/%s.o", tmpdir, units[i].hash);
            remove(path);
        }
        rmdir(tmpdir);
    }
    return ok;
}

static int link_set(const char *cache, const char *src, const char *set)
{
    char path[4096], tmp[4096], *cmd;
    size_t i, cap;
    long pid = (long)getpid();
    FILE *f;
    int ok;
    snprintf(path, sizeof path, "%s/set/%s.%ld.c", cache, set, pid);
    f = fopen(path, "wb");
    if (f == NULL)
        return 0;
    fputs("#include \"fastrt.h\"\n", f);
    for (i = 0; i < nunits; i++)
        fprintf(f, "extern const struct fast_unit U_%s;\n", units[i].hash);
    fputs("const struct fast_unit *const fast_units[] = {\n", f);
    for (i = 0; i < nunits; i++)
        fprintf(f, "    &U_%s,\n", units[i].hash);
    fprintf(f, "    0};\nconst unsigned long fast_nunits = %lu;\n", (unsigned long)nunits);
    if (fclose(f) != 0)
        return 0;
    /* The list of objects, for the linker. */
    snprintf(tmp, sizeof tmp, "%s/set/%s.%ld.list", cache, set, pid);
    f = fopen(tmp, "wb");
    if (f == NULL)
        return 0;
    for (i = 0; i < nunits; i++)
        fprintf(f, "%s/obj/%s.o\n", cache, units[i].hash);
    if (fclose(f) != 0)
        return 0;
    cap = 3 * strlen(cache) + strlen(src) + 6 * 64 + 512;
    cmd = malloc(cap);
    snprintf(cmd, cap,
             "cd '%s/set' && cc %s -w -fPIC %s -dynamiclib -undefined dynamic_lookup "
             "-o %s.tmp%ld %s.%ld.c -filelist %s.%ld.list %s && mv %s.tmp%ld %s.dylib",
             cache, FAST_CFLAGS, src, set, pid, set, pid, set, pid,
             verbose ? "1>&2" : ">/dev/null 2>&1", set, pid, set);
    ok = run_all(&cmd, 1);
    free(cmd);
    remove(path);
    remove(tmp);
    return ok;
}

static int load_set(const char *path)
{
    void *h = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    const struct fast_unit *const *us;
    const unsigned long *nu;
    size_t i, j, nk, nc, a, b, pc;
    if (h == NULL) {
        note("dlopen: %s", dlerror());
        return 0;
    }
    us = (const struct fast_unit *const *)dlsym(h, "fast_units");
    nu = (const unsigned long *)dlsym(h, "fast_nunits");
    if (us == NULL || nu == NULL || *nu != nunits)
        return 0;
    /* Check every unit first, then fill the tables. */
    for (i = 0; i < nunits; i++) {
        if (us[i]->n != units[i].n)
            return 0;
        for (j = 0; j < units[i].n; j++) {
            long k = units[i].fn[j];
            out_len = 0;
            print_datum(fns[k].sym);
            code_counts(k, &nk, &nc);
            if (strlen(us[i]->fns[j].name) != out_len ||
                memcmp(us[i]->fns[j].name, out, out_len) != 0 ||
                us[i]->fns[j].nK != nk || us[i]->fns[j].nC != nc)
                return 0;
        }
    }
    /* the tables of inlined code: by name and ordinal */
    for (i = 0; i < nunits; i++) {
        const struct fast_unit *u = us[i];
        long *xf;
        if (u->broken)
            return 0;
        xf = malloc((u->nx + 1) * sizeof(long));
        for (j = 0; j < u->nx; j++) {
            xf[j] = names_find((const unsigned char *)u->xnames[j], strlen(u->xnames[j]));
            if (xf[j] < 0 || !fns[xf[j]].built) {
                free(xf);
                return 0;
            }
        }
        for (a = 0; a < 2; a++) {
            size_t m = a ? u->nxc : u->nxk;
            const long *d = a ? u->xcd : u->xkd;
            for (j = 0; j < m; j++) {
                long k = xf[d[2 * j]];
                const Code *c = &fns[k].code;
                size_t want = (size_t)d[2 * j + 1], seen = 0;
                for (pc = 0; pc < c->n; pc += c->op[pc] == O_RET ? 1 : 2) {
                    int hit = a ? (c->op[pc] == O_CALL || c->op[pc] == O_TCALL)
                                : (c->op[pc] == O_CONST && !const_inline(consts[c->op[pc + 1]]));
                    if (hit && seen++ == want)
                        break;
                }
                if (pc >= c->n) {
                    free(xf);
                    return 0;
                }
                if (a)
                    u->xc[j] = c->op[pc + 1];
                else
                    u->xk[j] = (unsigned)c->op[pc + 1];
            }
        }
        free(xf);
    }
    for (i = 0; i < nunits; i++)
        for (j = 0; j < units[i].n; j++) {
            long k = units[i].fn[j];
            const struct fast_fn *f = &us[i]->fns[j];
            const Code *c = &fns[k].code;
            for (pc = 0, a = 0, b = 0; pc < c->n; pc += c->op[pc] == O_RET ? 1 : 2)
                if (c->op[pc] == O_CONST && !const_inline(consts[c->op[pc + 1]]))
                    f->K[a++] = (unsigned)c->op[pc + 1];
                else if (c->op[pc] == O_CALL || c->op[pc] == O_TCALL)
                    f->C[b++] = c->op[pc + 1];
            natv[k] = f->fn;
        }
    return 1;
}

/* The places of a run, as absolute paths, since the compiler is run in
   other directories: the options -I for the C written, the cache, and
   the stamp, a hash of the text of the two headers that the C written
   includes and of the compiler's options, which enters every name in the
   cache.  0 if they cannot be found. */
static char incs[8300], cachedir[4096], stamp[33];

static int mkdirs(const char *path)
{
    char p[4096];
    size_t i, n = strlen(path);
    if (n == 0 || n >= sizeof p)
        return 0;
    memcpy(p, path, n + 1);
    for (i = 1; i <= n; i++)
        if (p[i] == '/' || p[i] == '\0') {
            char c = p[i];
            p[i] = '\0';
            mkdir(p, 0777);
            p[i] = c;
        }
    return exists(path);
}

static int read_into(const char *path, char **buf, size_t *len)
{
    FILE *f = fopen(path, "rb");
    char b[4096];
    size_t got;
    if (f == NULL)
        return 0;
    while ((got = fread(b, 1, sizeof b, f)) > 0) {
        *buf = realloc(*buf, *len + got);
        if (*buf == NULL) {
            fclose(f);
            return 0;
        }
        memcpy(*buf + *len, b, got);
        *len += got;
    }
    fclose(f);
    return 1;
}

static int places(void)
{
    const char *root = getenv("BOYMOO_FAST_ROOT"), *cache = getenv("BOYMOO_FAST_CACHE");
    char r[4096], p[4096], *text = NULL;
    size_t len = 0;
    int ok;
    if (root == NULL || root[0] == '\0')
        root = ".";
    if (realpath(root, r) == NULL || strchr(r, '\'') != NULL) {
        note("%s", "the root of the repository cannot be found");
        return 0;
    }
    snprintf(incs, sizeof incs, "-I'%s/runner-fast' -I'%s/runner'", r, r);
    snprintf(p, sizeof p, "%s/runner-fast/fastrt.h", r);
    ok = read_into(p, &text, &len);
    snprintf(p, sizeof p, "%s/runner/run.h", r);
    ok = ok && read_into(p, &text, &len);
    if (!ok) {
        note("%s", "the headers fastrt.h and run.h cannot be read");
        free(text);
        return 0;
    }
    hash128(text, len, "stamp " FAST_CFLAGS, stamp);
    free(text);
    if (cache == NULL || cache[0] == '\0') {
        snprintf(p, sizeof p, "%s/build/runner-fast/cache", r);
        cache = p;
    }
    if (!mkdirs(cache) || realpath(cache, cachedir) == NULL || strchr(cachedir, '\'') != NULL) {
        note("%s", "the cache cannot be made");
        return 0;
    }
    return 1;
}

void jit_prepare(const unsigned char *in, size_t n, int vb)
{
    const char *cache = cachedir, *src = incs;
    char path[4096], set[33], *keys;
    size_t i, j, total = 0;
    long *order;
    clock_t t0 = clock();
    double tgen;
    verbose = vb;
    if (!places())
        return;
    names_build();
    native_prepare(names_find);
    seen = calloc(nfns + 1, 1);
    scan_input(in, n);
    for (i = 0; i < nwork; i++) {
        long k = work[i];
        const Code *c;
        size_t pc;
        if (!try_build(k))
            continue;
        c = &fns[k].code;
        for (pc = 0; pc < c->n; pc += c->op[pc] == O_RET ? 1 : 2)
            if (c->op[pc] == O_CALL || c->op[pc] == O_TCALL)
                add(c->op[pc + 1]);
    }
    /* The units: every built function of each line reached. */
    {
        char *lineseen = calloc(nfns + 1, 1);
        size_t m = 0;
        order = malloc((nfns + 1) * sizeof(long));
        for (i = 0; i < nwork; i++)
            if (fns[work[i]].built)
                lineseen[work[i]] = 1;
        /* mark every function whose line is reached */
        {
            const unsigned char **lines = malloc((nwork + 1) * sizeof(*lines));
            size_t nl = 0, lo, hi, mid;
            for (i = 0; i < nwork; i++)
                if (lineseen[work[i]])
                    lines[nl++] = fns[work[i]].line;
            /* sort the lines to look them up */
            qsort(lines, nl, sizeof(*lines), ptr_cmp);
            for (i = 0; i < nfns; i++) {
                if (!fns[i].built || fns[i].line == NULL)
                    continue;
                lo = 0;
                hi = nl;
                while (lo < hi) {
                    mid = (lo + hi) / 2;
                    if (lines[mid] < fns[i].line)
                        lo = mid + 1;
                    else
                        hi = mid;
                }
                if (lo < nl && lines[lo] == fns[i].line)
                    order[m++] = (long)i;
            }
            free(lines);
        }
        free(lineseen);
        qsort(order, m, sizeof(long), line_cmp);
        units = calloc(m + 1, sizeof(Unit));
        for (i = 0; i < m; i = j) {
            Unit *u = &units[nunits++];
            for (j = i; j < m && fns[order[j]].line == fns[order[i]].line; j++)
                ;
            u->line = fns[order[i]].line;
            u->fn = order + i;
            u->n = j - i;
            gen_unit(u->fn, u->n, "UNIT");
            hash128(gen_out, gen_len, stamp, u->hash);
            {
                size_t hl;
                u->c = malloc(gen_len + 64);
                snprintf(u->c, 64, "#define UNIT U_%s\n", u->hash);
                hl = strlen(u->c);
                memcpy(u->c + hl, gen_out, gen_len);
                u->clen = hl + gen_len;
            }
            total += u->clen;
        }
    }
    if (nunits == 0)
        return;
    qsort(units, nunits, sizeof(Unit), unit_cmp);
    keys = malloc(nunits * 33 + 1);
    for (i = 0; i < nunits; i++)
        memcpy(keys + 33 * i, units[i].hash, 33);
    hash128(keys, nunits * 33, stamp, set);
    free(keys);
    tgen = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (verbose)
        fprintf(stderr, "boymoo-run-fast: %lu functions reached, %lu units, %lu bytes of C, %.3f s to build and write\n",
                (unsigned long)nwork, (unsigned long)nunits, (unsigned long)total, tgen);
    snprintf(path, sizeof path, "%s/set/%s.dylib", cache, set);
    if (!exists(path)) {
        snprintf(path, sizeof path, "%s/obj", cache);
        mkdir(cache, 0777);
        mkdir(path, 0777);
        snprintf(path, sizeof path, "%s/set", cache);
        mkdir(path, 0777);
        if (!compile_units(cache, src) || !link_set(cache, src, set)) {
            note("%s", "compiling failed; the interpreter runs everything");
            return;
        }
        snprintf(path, sizeof path, "%s/set/%s.dylib", cache, set);
    }
    for (i = 0; i < nunits; i++) {
        free(units[i].c);
        units[i].c = NULL;
    }
    if (!load_set(path)) {
        note("%s", "loading the compiled code failed; the interpreter runs everything");
        for (i = 0; i < nfns; i++)
            natv[i] = nat_interp;
        return;
    }
    native_install(names_find, verbose);
    if (verbose)
        fprintf(stderr, "boymoo-run-fast: loaded %s, %.3f s in all\n", path,
                (double)(clock() - t0) / CLOCKS_PER_SEC);
}
