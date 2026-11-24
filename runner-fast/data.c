/* Symbols, packages, strings, and the text of data (spec/formats.md,
   section 2): the reader, which accepts only the one text of each
   datum, and the printer.  Neither, nor equal(), uses the C stack in
   proportion to the depth of a datum: each keeps its own stack.

   A symbol is an entry of a table that is never collected.  A hash
   table maps a package and a name to the symbol that the name gives in
   that package: the package's own symbol of that name, or the symbol it
   imports.  This is exactly intern-in-package-of-symbol; reading the
   text PKG::NAME also requires that the symbol found belongs to PKG,
   which is the rule of existence (spec/language.md, section 2). */

#include <string.h>
#include "run.h"

Sym *syms;
size_t nsyms;
static size_t syms_cap;
Pkg *pkgs;
static size_t npkgs, pkgs_cap;
V S_QUOTE = NOV, S_LAMBDA = NOV, S_IF = NOV, S_LIST = NOV, S_RETURN_LAST = NOV,
  S_MBE1_RAW = NOV;

typedef struct { long pkg, sym; } Ent;   /* sym < 0: empty */
static Ent *tab;
static size_t tab_cap, tab_n;

static void *grow(void *p, size_t *cap, size_t size, size_t want)
{
    size_t c = *cap ? *cap : 64;
    while (c < want) {
        if (c > ((size_t)-1 / size) / 2)
            stop(S_MEMORY, "memory exhausted: a table is too large", NOV);
        c *= 2;
    }
    if (c != *cap) {
        p = xalloc(p, *cap * size, c * size);
        *cap = c;
    }
    return p;
}

static unsigned long hash(long pkg, const unsigned char *s, size_t n)
{
    unsigned long h = 2166136261UL ^ (unsigned long)pkg;
    while (n-- > 0)
        h = ((h ^ *s++) * 16777619UL) & 0xFFFFFFFFUL;
    return h;
}

static size_t slot(long pkg, const unsigned char *s, size_t n)
{
    size_t i = hash(pkg, s, n) & (tab_cap - 1);
    Sym *y;
    while (tab[i].sym >= 0) {
        y = &syms[tab[i].sym];
        if (tab[i].pkg == pkg && y->len == n && memcmp(y->name, s, n) == 0)
            break;
        i = (i + 1) & (tab_cap - 1);
    }
    return i;
}

static void tab_insert(long pkg, long sym)
{
    size_t i, old = tab_cap;
    Ent *t = tab;
    if (2 * (tab_n + 1) > tab_cap) {
        tab_cap = old ? 2 * old : 4096;
        tab = xalloc(NULL, 0, tab_cap * sizeof(Ent));
        for (i = 0; i < tab_cap; i++)
            tab[i].sym = -1;
        for (i = 0; i < old; i++)
            if (t[i].sym >= 0)
                tab[slot(t[i].pkg, syms[t[i].sym].name, syms[t[i].sym].len)] = t[i];
        xalloc(t, old * sizeof(Ent), 0);
    }
    i = slot(pkg, syms[sym].name, syms[sym].len);
    tab[i].pkg = pkg;
    tab[i].sym = sym;
    tab_n++;
}

static int is(const unsigned char *s, size_t n, const char *z)
{
    return strlen(z) == n && memcmp(s, z, n) == 0;
}

static V sym_new(long pkg, const unsigned char *s, size_t n)
{
    Sym *y;
    int i;
    const Pkg *k = &pkgs[pkg];
    V v = MKSYM(nsyms);
    if (nsyms >= 0x1FFFFFFEUL)
        stop(S_MEMORY, "memory exhausted: too many symbols", NOV);
    syms = grow(syms, &syms_cap, sizeof(Sym), nsyms + 1);
    y = &syms[nsyms];
    y->name = xalloc(NULL, 0, n + 1);
    memcpy(y->name, s, n);
    y->len = n;
    y->pkg = (int)pkg;
    y->prim = -1;
    y->fn = -1;
    for (i = 0; i < NPRIMS; i++)
        if (is(k->name, k->len, prim_pkg[i]) && is(s, n, prim_name[i]))
            y->prim = i;
    if (is(k->name, k->len, "COMMON-LISP")) {
        if (is(s, n, "QUOTE")) S_QUOTE = v;
        if (is(s, n, "LAMBDA")) S_LAMBDA = v;
        if (is(s, n, "IF")) S_IF = v;
        if (is(s, n, "LIST")) S_LIST = v;
    } else if (is(k->name, k->len, "ACL2")) {
        if (is(s, n, "RETURN-LAST")) S_RETURN_LAST = v;
        if (is(s, n, "MBE1-RAW")) S_MBE1_RAW = v;
    }
    tab_insert(pkg, (long)nsyms);
    nsyms++;
    return v;
}

static long last_pkg = -1;

long pkg_find(const unsigned char *name, size_t len)
{
    size_t i;
    if (last_pkg >= 0 && pkgs[last_pkg].len == len && memcmp(pkgs[last_pkg].name, name, len) == 0)
        return last_pkg;
    for (i = 0; i < npkgs; i++)
        if (pkgs[i].len == len && memcmp(pkgs[i].name, name, len) == 0)
            return last_pkg = (long)i;
    return -1;
}

static long pkg_add(const unsigned char *name, size_t len)
{
    Pkg *k;
    pkgs = grow(pkgs, &pkgs_cap, sizeof(Pkg), npkgs + 1);
    k = &pkgs[npkgs];
    k->name = xalloc(NULL, 0, len + 1);
    memcpy(k->name, name, len);
    k->len = len;
    k->declared = k->hidden = 0;
    k->imports = 0;
    return (long)npkgs++;
}

/* COMMON-LISP::NIL and COMMON-LISP::T exist from the start, so that the
   ground theory's first line, which declares COMMON-LISP with the
   imports NIL, can be read. */
void data_init(void)
{
    pkg_add((const unsigned char *)"COMMON-LISP", 11);
    sym_new(0, (const unsigned char *)"NIL", 3);
    sym_new(0, (const unsigned char *)"T", 1);
}

/* The symbol that NAME gives in the package PKG. */
V intern_in(int pkg, const unsigned char *name, size_t len)
{
    size_t i = slot(pkg, name, len);
    return tab[i].sym >= 0 ? MKSYM(tab[i].sym) : sym_new(pkg, name, len);
}

/* The symbol written PKG::NAME, which must exist. */
static V intern_text(const unsigned char *p, size_t pl, const unsigned char *s, size_t n)
{
    long k = pkg_find(p, pl);
    size_t i;
    if (k < 0)
        stop(S_INPUT, "not in the format: a symbol of a package that is not declared", NOV);
    i = slot(k, s, n);
    if (tab[i].sym >= 0) {
        if (syms[tab[i].sym].pkg != k)
            stop(S_INPUT, "not in the format: a symbol that does not exist, since its package imports one of that name", NOV);
        return MKSYM(tab[i].sym);
    }
    if (!pkgs[k].declared)
        stop(S_INPUT, "not in the format: a symbol of a package that is not declared", NOV);
    return sym_new(k, s, n);
}

static unsigned char *buf1, *buf2;   /* names being read */
static size_t cap1, cap2;

static size_t strbytes(V v, unsigned char **b, size_t *cap)
{
    size_t i, n = STRLEN(v);
    *b = grow(*b, cap, 1, n + 1);
    for (i = 0; i < n; i++)
        (*b)[i] = (unsigned char)STRBYTE(v, i);
    return n;
}

/* Declares a package; its name and its list of imports are on the stack. */
void declare_package(int hidden)
{
    V name = stk[sp - 2], imps = stk[sp - 1], x;
    size_t n, i;
    long k;
    if (!IS_STRING(name) || STRLEN(name) == 0)
        stop(S_INPUT, "a package's name must be a string that is not empty", name);
    n = strbytes(name, &buf1, &cap1);
    k = pkg_find(buf1, n);
    if (k >= 0 && pkgs[k].declared) {
        if (!equal(consts[pkgs[k].imports], imps))
            stop(S_INPUT, "a package declared again with other imports:", name);
        if (!hidden)
            pkgs[k].hidden = 0;
        sp -= 2;
        return;
    }
    if (k < 0)
        k = pkg_add(buf1, n);
    for (x = imps; IS_CONS(x); x = CDR(x)) {
        const Sym *y;
        if (!IS_SYM(CAR(x)))
            stop(S_INPUT, "a package's imports must be symbols:", name);
        y = &syms[SYMIDX(CAR(x))];
        if (is(y->name, y->len, "ACL2-PKG-WITNESS"))
            stop(S_INPUT, "a package may not import a symbol named ACL2-PKG-WITNESS:", name);
        i = slot(k, y->name, y->len);
        if (tab[i].sym >= 0)
            stop(S_INPUT, "a package imports two symbols of one name:", name);
        tab_insert(k, (long)SYMIDX(CAR(x)));
    }
    if (x != NIL)
        stop(S_INPUT, "a package's imports must be a true list:", name);
    pkgs[k].declared = 1;
    pkgs[k].hidden = hidden;
    pkgs[k].imports = add_const(imps);
    sp -= 2;
}

V mkstring(const unsigned char *s, size_t len)
{
    size_t i, nw = 1 + (len + 3) / 4;
    V v;
    need(0, nw + 1);
    v = mkbox(B_STRING, nw);
    for (i = 1; i <= nw; i++)
        BOX(v)[i] = 0;
    BOX(v)[1] = (V)len;
    for (i = 0; i < len; i++)
        BOX(v)[2 + i / 4] |= (V)((unsigned long)s[i] << (8 * (i % 4)));
    return v;
}

/* The reader.  It reads the text between rp and rend, and pushes each
   datum it reads on the stack. */

static const unsigned char *rp, *rend;
#define AT(k) ((rend - rp) > (k) ? rp[k] : 0)

static void bad(const char *what)
{
    stop(S_INPUT, what, NOV);
}

static int plain(int c)
{
    return (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') ||
           (c != 0 && strchr("-+*/<=>!?$%&_^~.@", c) != NULL);
}

static int hex(int c)
{
    return c >= '0' && c <= '9' ? c - '0' : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1;
}

static int hex2(void)
{
    int a = hex(AT(0)), b = hex(AT(1));
    if (a < 0 || b < 0)
        bad("not in the format: an escape that is not two hexadecimal digits in upper case");
    rp += 2;
    return 16 * a + b;
}

/* The characters of a string or of a name between bars, up to DELIM.
   Returns their number, in *B. */
static size_t escaped(int delim, unsigned char **b, size_t *cap)
{
    size_t n = 0;
    int c;
    rp++;
    for (;;) {
        c = AT(0);
        if (c == 0)
            bad("not in the format: a string or a name with no end");
        if (c == delim)
            break;
        if (c == '\\') {
            rp++;
            c = hex2();
            if (c >= 32 && c <= 126 && c != delim && c != '\\')
                bad("not in the format: a character escaped that is written as itself");
        } else
            rp++;
        *b = grow(*b, cap, 1, n + 1);
        (*b)[n++] = (unsigned char)c;
    }
    rp++;
    return n;
}

/* One part of a symbol: a run of plain characters, or a name between
   bars that cannot be written as such a run. */
static size_t part(const unsigned char **s, unsigned char **b, size_t *cap)
{
    size_t i, n;
    if (AT(0) == '|') {
        n = escaped('|', b, cap);
        for (i = 0; i < n && plain((*b)[i]); i++)
            ;
        if (n > 0 && i == n)
            bad("not in the format: a part of a symbol between bars that needs none");
        *s = *b;
        return n;
    }
    *s = rp;
    while (plain(AT(0)))
        rp++;
    if (rp == *s)
        bad("not in the format: a part of a symbol is missing");
    return (size_t)(rp - *s);
}

static void read_number(void)
{
    const unsigned char *s = rp;
    V v;
    while (plain(AT(0)))
        rp++;
    v = num_read(s, rp);
    if (v == NOV)
        bad("not in the format: a number that is not in its one text");
    push(v);
}

static void read_atom(void)
{
    const unsigned char *s, *p, *q;
    size_t n, pl;
    int c = AT(0);
    V v;
    if (c == '"') {
        n = escaped('"', &buf1, &cap1);
        push(mkstring(buf1, n));
    } else if (c == '#' && AT(1) == '\\') {
        rp += 2;
        push(MKCHAR(hex2()));
    } else if (c == '#' && AT(1) == 'C' && AT(2) == '(') {
        rp += 3;
        read_number();
        if (AT(0) != ' ')
            bad("not in the format: a complex rational");
        rp++;
        read_number();
        if (AT(0) != ')' || stk[sp - 1] == MKFIX(0))
            bad("not in the format: a complex rational");
        rp++;
        v = num_complex(stk[sp - 2], stk[sp - 1]);
        sp -= 2;
        push(v);
    } else if (c == '|' || plain(c)) {
        s = rp;
        while (c != '|' && plain(AT(0)))
            rp++;
        if (c != '|' && !(AT(0) == ':' && AT(1) == ':')) {
            rp = s;
            read_number();
            return;
        }
        rp = s;
        pl = part(&p, &buf1, &cap1);
        if (AT(0) != ':' || AT(1) != ':')
            bad("not in the format: a symbol with no package");
        rp += 2;
        n = part(&q, &buf2, &cap2);
        push(intern_text(p, pl, q, n));
    } else
        bad("not in the format: a datum was expected");
}

static size_t *lists;   /* the number of elements read of each open list */
static size_t lists_cap;

static void build_list(size_t n, int dotted)
{
    V tail;
    need(n, 0);
    tail = dotted ? stk[--sp] : NIL;
    while (n-- > 0)
        tail = mkcons(stk[--sp], tail);
    push(tail);
}

/* Reads one datum, which begins at P and ends at or before E; pushes it,
   and returns the place after it. */
const unsigned char *read_datum(const unsigned char *p, const unsigned char *e)
{
    size_t depth = 0;
    rp = p;
    rend = e;
    for (;;) {
        if (AT(0) == '(') {
            rp++;
            lists = grow(lists, &lists_cap, sizeof(size_t), depth + 1);
            lists[depth++] = 0;
            continue;
        }
        read_atom();
        for (;;) {
            if (depth == 0)
                return rp;
            lists[depth - 1]++;
            if (AT(0) == ' ' && AT(1) == '.' && AT(2) == ' ') {
                rp += 3;
                if (AT(0) == '(')
                    bad("not in the format: a list after ' . '");
                read_atom();
                if (stk[sp - 1] == NIL || AT(0) != ')')
                    bad("not in the format: what follows ' . '");
                rp++;
                build_list(lists[--depth], 1);
            } else if (AT(0) == ' ') {
                rp++;
                break;
            } else if (AT(0) == ')') {
                rp++;
                build_list(lists[--depth], 0);
            } else
                bad("not in the format: a space or ')' was expected");
        }
    }
}

/* The place after the datum that begins at P, found without reading it;
   NULL if the text ends first. */
const unsigned char *skip_datum(const unsigned char *p, const unsigned char *e)
{
    size_t depth = 0;
    unsigned char c;
    for (; p < e; p++) {
        c = *p;
        if (c == '"' || c == '|') {
            for (p++; p < e && *p != c; p++)
                ;
            if (p == e)
                return NULL;
        } else if (c == '(')
            depth++;
        else if (c == ')') {
            if (depth == 0)
                return p;
            if (--depth == 0)
                return p + 1;
        } else if (c == ' ' && depth == 0)
            return p;
    }
    return depth > 0 ? NULL : p;
}

/* equal, with a stack of the pairs still to compare. */

static V *pairs;
static size_t npairs, pairs_cap;

static int same_string(V a, V b)
{
    size_t i;
    if (BOX(a)[0] != BOX(b)[0])
        return 0;
    for (i = 1; i <= BSIZE(a); i++)
        if (BOX(a)[i] != BOX(b)[i])
            return 0;
    return 1;
}

int equal(V a, V b)
{
    size_t base = npairs;
    for (;;) {
        if (a != b) {
            if (IS_CONS(a) && IS_CONS(b)) {
                /* For the fast runner: a part that is the same object
                   needs no comparison and no entry on the stack. */
                if (CAR(a) == CAR(b)) {
                    a = CDR(a);
                    b = CDR(b);
                    continue;
                }
                if (CDR(a) == CDR(b)) {
                    a = CAR(a);
                    b = CAR(b);
                    continue;
                }
                if (npairs + 2 > pairs_cap)
                    pairs = grow(pairs, &pairs_cap, sizeof(V), npairs + 2);
                pairs[npairs++] = CDR(a);
                pairs[npairs++] = CDR(b);
                a = CAR(a);
                b = CAR(b);
                continue;
            }
            if (!IS_BOX(a) || !IS_BOX(b) ||
                !(IS_STRING(a) ? IS_STRING(b) && same_string(a, b) : big_equal(a, b))) {
                npairs = base;
                return 0;
            }
        }
        if (npairs == base)
            return 1;
        npairs -= 2;
        a = pairs[npairs];
        b = pairs[npairs + 1];
    }
}

/* The printer, which appends to out. */

char *out;
size_t out_len;
static size_t out_cap;

void out_put(const char *s, size_t n)
{
    out = grow(out, &out_cap, 1, out_len + n + 1);
    memcpy(out + out_len, s, n);
    out_len += n;
}

static void put_char(unsigned c, int delim)
{
    char b[3];
    if (c >= 32 && c <= 126 && (int)c != delim && c != '\\') {
        b[0] = (char)c;
        out_put(b, 1);
    } else {
        b[0] = '\\';
        b[1] = "0123456789ABCDEF"[c / 16];
        b[2] = "0123456789ABCDEF"[c % 16];
        out_put(b, 3);
    }
}

static void put_part(const unsigned char *s, size_t n)
{
    size_t i;
    for (i = 0; i < n && plain(s[i]); i++)
        ;
    if (n > 0 && i == n) {
        out_put((const char *)s, n);
        return;
    }
    out_put("|", 1);
    for (i = 0; i < n; i++)
        put_char(s[i], '|');
    out_put("|", 1);
}

static void print_atom(V v)
{
    char b[4];
    size_t i;
    if (IS_SYM(v)) {
        const Sym *y = &syms[SYMIDX(v)];
        put_part(pkgs[y->pkg].name, pkgs[y->pkg].len);
        out_put("::", 2);
        put_part(y->name, y->len);
    } else if (IS_CHAR(v)) {
        b[0] = '#';
        b[1] = '\\';
        b[2] = "0123456789ABCDEF"[CHARCODE(v) / 16];
        b[3] = "0123456789ABCDEF"[CHARCODE(v) % 16];
        out_put(b, 4);
    } else if (IS_STRING(v)) {
        out_put("\"", 1);
        for (i = 0; i < STRLEN(v); i++)
            put_char(STRBYTE(v, i), '"');
        out_put("\"", 1);
    } else
        num_print(v);
}

static V *todo;   /* pairs of a step and a datum: 0 print it, 1 print the
                     rest of a list, 2 close a dotted list */
static size_t ntodo, todo_cap;

static void later(V step, V v)
{
    todo = grow(todo, &todo_cap, sizeof(V), ntodo + 2);
    todo[ntodo++] = step;
    todo[ntodo++] = v;
}

void print_datum(V v)
{
    V step;
    later(0, v);
    while (ntodo > 0) {
        ntodo -= 2;
        step = todo[ntodo];
        v = todo[ntodo + 1];
        if (step == 2)
            out_put(")", 1);
        else if (step == 1 && IS_CONS(v)) {
            out_put(" ", 1);
            later(1, CDR(v));
            later(0, CAR(v));
        } else if (step == 1 && v == NIL)
            out_put(")", 1);
        else if (step == 1) {
            out_put(" . ", 3);
            later(2, NIL);
            later(0, v);
        } else if (IS_CONS(v)) {
            out_put("(", 1);
            later(1, CDR(v));
            later(0, CAR(v));
        } else
            print_atom(v);
    }
}
