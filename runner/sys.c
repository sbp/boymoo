/* The runner's contact with the system: its arguments, the files it
   reads, standard input and output, and the stops.  It uses only the
   library of ISO C.  README.md in this directory gives the usage. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "run.h"

static char **files;
static int place_file = -1;
static long place_line, term_line;
static int stopping;

void set_place(int file, long line)
{
    place_file = file;
    place_line = line;
}

/* Ends the run: a message on standard error, and STATUS. */
void stop(int status, const char *msg, V v)
{
    fflush(stdout);
    if (place_file >= 0)
        fprintf(stderr, "boymoo-run: %s, line %ld: ", files[place_file], place_line);
    else if (term_line > 0)
        fprintf(stderr, "boymoo-run: standard input, line %ld: ", term_line);
    else
        fputs("boymoo-run: ", stderr);
    fputs(msg, stderr);
    if (v != NOV && !stopping) {
        stopping = 1;
        out_len = 0;
        print_datum(v);
        fputc(' ', stderr);
        fwrite(out, 1, out_len > 2000 ? 2000 : out_len, stderr);
        if (out_len > 2000)
            fputs(" ...", stderr);
    }
    fputc('\n', stderr);
    exit(status);
}

static int printable(const unsigned char *p, const unsigned char *e)
{
    for (; p < e; p++)
        if (*p < 32 || *p > 126)
            return 0;
    return 1;
}

static int word(const unsigned char *p, const unsigned char *e, const char *w)
{
    size_t n = strlen(w);
    return (size_t)(e - p) > n + 1 && memcmp(p + 1, w, n) == 0 && (p[n + 1] == ' ' || p[n + 1] == ')');
}

/* Reads the data of a line after its word, and checks that they fill it. */
static void line_data(const unsigned char *p, const unsigned char *e, size_t skip, int count)
{
    p += skip;
    while (count-- > 0) {
        if (p == e || *p != ' ')
            stop(S_INPUT, "not in the format: a line has too few data", NOV);
        p = read_datum(p + 1, e);
    }
    if (e - p != 1 || *p != ')')
        stop(S_INPUT, "not in the format: a line has too many data", NOV);
}

/* The words of the ground theory and of statements other than those
   that declare packages. */
static const char *const skipped[] = {
    "primitive", "specials", "clause", "define", "constrain", "choose",
    "theorem", "axiom", "reserve", NULL};

/* Reads a file: program text, whose define and attach lines it takes;
   or, if PACKAGES, the ground theory or statements, whose package and
   hidden-package lines it takes. */
static void load(int file, int packages)
{
    FILE *f = fopen(files[file], "rb");
    unsigned char *text = NULL, *p, *e, *end;
    size_t n = 0, cap = 0, got;
    long line = 0;
    int i;
    if (f == NULL) {
        set_place(-1, 0);
        fprintf(stderr, "boymoo-run: cannot open %s\n", files[file]);
        exit(S_INPUT);
    }
    do {
        if (cap - n < 65536) {
            size_t c = cap ? 2 * cap : 1 << 20;
            text = xalloc(text, cap, c);
            cap = c;
        }
        got = fread(text + n, 1, cap - n, f);
        n += got;
    } while (got > 0);
    if (ferror(f)) {
        fprintf(stderr, "boymoo-run: cannot read %s\n", files[file]);
        exit(S_INPUT);
    }
    fclose(f);
    end = text + n;
    for (p = text; p < end; p = e + 1) {
        set_place(file, ++line);
        e = memchr(p, '\n', (size_t)(end - p));
        if (e == NULL)
            stop(S_INPUT, "not in the format: the last line has no line feed", NOV);
        if (!printable(p, e) || e - p < 3 || *p != '(' || e[-1] != ')')
            stop(S_INPUT, "not in the format: not a line", NOV);
        if (!packages && word(p, e, "define"))
            index_define(p, e, file, line);
        else if (!packages && word(p, e, "attach")) {
            line_data(p, e, 7, 2);
            set_attach();
        } else if (packages && word(p, e, "package")) {
            line_data(p, e, 8, 2);
            declare_package(0);
        } else if (packages && word(p, e, "hidden-package")) {
            line_data(p, e, 15, 2);
            declare_package(1);
        } else {
            for (i = 0; packages && skipped[i] != NULL && !word(p, e, skipped[i]); i++)
                ;
            if (!packages || skipped[i] == NULL)
                stop(S_INPUT, "a line whose word may not stand in this file", NOV);
        }
    }
    if (packages)
        xalloc(text, cap, 0);
    set_place(-1, 0);
}

static int usage(void)
{
    fputs("usage: boymoo-run [-l] [-v] [-j] [-m megabytes] [-p packages] ... program ...\n"
          "Reads the packages of each file named by -p and the program text of each\n"
          "other file, in order; then computes the value of the term on each line of\n"
          "standard input and writes it on a line of standard output.  With -j it\n"
          "starts with the prelude: ash and binary-logxor, defined.\n", stderr);
    return S_INPUT;
}

int main(int argc, char **argv)
{
    int i = 1, eager = 0, stats = 0, c, nprog = 0;
    unsigned long mb = 4096;
    char *rest;
    unsigned char *buf = NULL;
    size_t n, cap = 0;
    clock_t t0, t1, t2;
    for (; i < argc && argv[i][0] == '-' && strcmp(argv[i], "-p") != 0; i++) {
        if (strcmp(argv[i], "-l") == 0)
            eager = 1;
        else if (strcmp(argv[i], "-v") == 0)
            stats = 1;
        else if (strcmp(argv[i], "-j") == 0)
            prelude = 1;
        else if (strcmp(argv[i], "-m") == 0 && i + 1 < argc) {
            mb = strtoul(argv[++i], &rest, 10);
            if (*rest != '\0' || mb == 0)
                return usage();
        } else
            return usage();
    }
    files = argv;
    mem_limit = mb > ((size_t)-1) / 1048576 ? (size_t)-1 : (size_t)mb * 1048576;
    heap_init();
    data_init();
    t0 = clock();
    for (; i < argc; i++) {
        if (strcmp(argv[i], "-p") == 0 && i + 1 < argc)
            load(++i, 1);
        else if (argv[i][0] != '-') {
            load(i, 0);
            nprog++;
        } else
            return usage();
    }
    if (nprog == 0)
        return usage();
    if (eager)
        build_all();
    t1 = clock();
    for (;;) {
        n = 0;
        while ((c = getchar()) != EOF && c != '\n') {
            if (n == cap) {
                size_t m = cap ? 2 * cap : 4096;
                buf = xalloc(buf, cap, m);
                cap = m;
            }
            buf[n++] = (unsigned char)c;
        }
        if (c == EOF && n == 0)
            break;
        term_line++;
        if (n == 0 || !printable(buf, buf + n) || read_datum(buf, buf + n) != buf + n)
            stop(S_INPUT, "not in the format: a line that is not one datum", NOV);
        out_len = 0;
        print_datum(run_term());
        out_put("\n", 1);
        fwrite(out, 1, out_len, stdout);
        if (c == EOF)
            break;
    }
    t2 = clock();
    if (fflush(stdout) != 0 || ferror(stdout)) {
        fputs("boymoo-run: cannot write the output\n", stderr);
        return S_INPUT;
    }
    if (stats)
        fprintf(stderr, "boymoo-run: load %.3f s, run %.3f s (processor time); "
                "%lu definitions compiled; %lu collections; peak memory %lu KB\n",
                (double)(t1 - t0) / CLOCKS_PER_SEC, (double)(t2 - t1) / CLOCKS_PER_SEC,
                defs_built, gc_count, (unsigned long)(mem_peak / 1024));
    return S_VALUE;
}
