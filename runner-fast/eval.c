/* Definitions, the compiler and the machine that computes values
   (spec/language.md, section 4).

   Loading program text only indexes each define line: the names of its
   functions and their numbers of arguments.  A line is read and
   compiled when one of its functions is first called.  The compiler
   turns a term into code for a stack machine, checking as it goes that
   the term is a term (spec/language.md, section 5).  Variables are
   slots of a frame on the value stack; an IF jumps; a call in the last
   position of a body reuses its caller's frame; and a lambda
   application in the last position replaces the frame with its own.
   A lambda application elsewhere moves the frame by an offset that the
   compiler knows.  The machine keeps its own stack of return points, so
   the depth of a
   program's recursion is bounded by memory, not by the C stack.  Only
   the compiler recurses in C, once for each level of nesting of a term,
   and it stops at MAXNEST levels. */

#include <string.h>
#include "fast.h"

const char *const prim_pkg[NPRIMS] = {
    "ACL2", "ACL2", "ACL2", "ACL2", "ACL2", "ACL2", "COMMON-LISP",
    "COMMON-LISP", "COMMON-LISP", "COMMON-LISP", "COMMON-LISP",
    "COMMON-LISP", "COMMON-LISP", "ACL2", "COMMON-LISP", "COMMON-LISP",
    "COMMON-LISP", "COMMON-LISP", "COMMON-LISP", "COMMON-LISP",
    "COMMON-LISP", "COMMON-LISP", "ACL2", "COMMON-LISP", "ACL2", "ACL2",
    "COMMON-LISP", "COMMON-LISP", "COMMON-LISP", "COMMON-LISP", "ACL2",
    "COMMON-LISP"};
const char *const prim_name[NPRIMS] = {
    "ACL2-NUMBERP", "BAD-ATOM<=", "BINARY-*", "BINARY-+", "UNARY--",
    "UNARY-/", "<", "CAR", "CDR", "CHAR-CODE", "CHARACTERP", "CODE-CHAR",
    "COMPLEX", "COMPLEX-RATIONALP", "COERCE", "CONS", "CONSP",
    "DENOMINATOR", "EQUAL", "IF", "IMAGPART", "INTEGERP",
    "INTERN-IN-PACKAGE-OF-SYMBOL", "NUMERATOR", "PKG-IMPORTS",
    "PKG-WITNESS", "RATIONALP", "REALPART", "STRINGP", "SYMBOL-NAME",
    "SYMBOL-PACKAGE-NAME", "SYMBOLP"};
const int prim_arity[NPRIMS] = {
    1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1,
    1, 1, 1, 1, 1, 1, 1, 1};

#define MAXNEST 10000

Fn *fns;
size_t nfns;
static size_t fns_cap;
NatFn *natv;
unsigned long defs_built;

static long fn_of(V s)
{
    Sym *y = &syms[SYMIDX(s)];
    Fn *f;
    if (y->fn >= 0)
        return y->fn;
    if (nfns == fns_cap) {
        size_t cap = fns_cap ? 2 * fns_cap : 4096;
        fns = xalloc(fns, fns_cap * sizeof(Fn), cap * sizeof(Fn));
        natv = xalloc(natv, fns_cap * sizeof(NatFn), cap * sizeof(NatFn));
        fns_cap = cap;
    }
    f = &fns[nfns];
    f->sym = s;
    f->arity = -1;
    f->line = f->end = NULL;
    f->file = f->pos = f->built = 0;
    f->lineno = 0;
    f->attach = -1;
    f->code.op = NULL;
    f->code.n = f->code.maxstack = 0;
    natv[nfns] = nat_interp;
    return y->fn = (long)nfns++;
}

static void bad(const char *what, V v) { stop(S_INPUT, what, v); }

/* Records the functions of the define line P..E (without its line feed).
   Where two lines define one function, the later is in force
   (spec/formats.md, section 5). */
void index_define(const unsigned char *p, const unsigned char *e, int file, long line)
{
    const unsigned char *start = p, *q;
    long k, n;
    int pos = 0;
    V name;
    q = skip_datum(p + 8, e);
    if (q == NULL || q == e || *q != ' ')
        bad("not in the format: a define line", NOV);
    p = q;
    while (e - p > 2 && p[0] == ' ' && p[1] == '(') {
        p = read_datum(p + 2, e);
        name = stk[--sp];
        if (!IS_SYM(name) || p == e || *p != ' ')
            bad("not in the format: a definition", NOV);
        p++;
        if (e - p > 17 && memcmp(p, "COMMON-LISP::NIL ", 17) == 0) {
            n = 0;
            p += 16;
        } else if (p < e && *p == '(') {
            for (n = 1, q = p + 1; (q = skip_datum(q, e)) != NULL && q < e && *q == ' '; q++)
                n++;
            if (q == NULL || q == e || *q != ')')
                bad("not in the format: the formals of a definition", NOV);
            p = q + 1;
        } else
            bad("not in the format: the formals of a definition", NOV);
        q = p < e && *p == ' ' ? skip_datum(p + 1, e) : NULL;
        if (q == NULL || q == e || *q != ')')
            bad("not in the format: a definition", NOV);
        p = q + 1;
        if (syms[SYMIDX(name)].prim >= 0)
            bad("a define line defines a primitive:", name);
        k = fn_of(name);
        if (fns[k].line == start)
            bad("a define line defines a function twice:", name);
        fns[k].line = start;   /* a later definition is in force */
        fns[k].end = e;
        fns[k].file = file;
        fns[k].lineno = line;
        fns[k].pos = pos++;
        fns[k].arity = n;
    }
    if (pos == 0 || e - p != 1 || *p != ')')
        bad("not in the format: a define line", NOV);
}

void set_attach(void)
{
    V f = stk[sp - 2], g = stk[sp - 1];
    long kf, kg;
    sp -= 2;
    if (!IS_SYM(f) || !IS_SYM(g) || syms[SYMIDX(f)].prim >= 0)
        bad("not in the format: an attach line", NOV);
    kf = fn_of(f);
    kg = fn_of(g);
    fns[kf].attach = kg;
}

/* The compiler. */


static long *cb;              /* the code being compiled */
static size_t cb_n, cb_cap;
static long depth, maxdepth;  /* values on the stack above the frame */
static long fbase;            /* where the frame of the lambda being
                                 compiled begins, from that of the body */

static void emit(long x)
{
    if (cb_n == cb_cap) {
        size_t cap = cb_cap ? 2 * cb_cap : 1024;
        cb = xalloc(cb, cb_cap * sizeof(long), cap * sizeof(long));
        cb_cap = cap;
    }
    cb[cb_n++] = x;
}

static void up(long d)
{
    depth += d;
    if (depth > maxdepth)
        maxdepth = depth;
}

/* The length of a true list, or -1. */
static long length(V x)
{
    long n = 0;
    for (; IS_CONS(x); x = CDR(x))
        n++;
    return x == NIL ? n : -1;
}

/* Whether X is a true list of distinct variables (spec/language.md,
   section 5, in the part that matters to running: symbols other than T,
   NIL and keywords). */
static int variables(V x)
{
    V y, z;
    for (y = x; IS_CONS(y); y = CDR(y)) {
        V v = CAR(y);
        if (!IS_SYM(v) || v == NIL || v == T ||
            (pkgs[syms[SYMIDX(v)].pkg].len == 7 &&
             memcmp(pkgs[syms[SYMIDX(v)].pkg].name, "KEYWORD", 7) == 0))
            return 0;
        for (z = CDR(y); IS_CONS(z); z = CDR(z))
            if (CAR(z) == v)
                return 0;
    }
    return y == NIL;
}

/* The function that a call of S runs: S itself, or what is attached. */
static V resolve(V s)
{
    int i;
    long k;
    for (i = 0; i < 1000; i++) {
        k = syms[SYMIDX(s)].fn;
        if (syms[SYMIDX(s)].prim >= 0 || k < 0 || fns[k].attach < 0)
            return s;
        s = fns[fns[k].attach].sym;
    }
    bad("attachments that form a cycle, at", s);
    return s;
}

static void comp(V x, V scope, int tail, int nest)
{
    V h, args, y;
    long n, i, k, d;
    size_t l1, l2 = 0;
    int p;
    if (nest > MAXNEST)
        bad("a term nested more deeply than the runner allows", NOV);
    if (IS_SYM(x)) {
        for (i = 0, y = scope; IS_CONS(y) && CAR(y) != x; y = CDR(y))
            i++;
        if (!IS_CONS(y))
            bad("not a term: a variable that is not bound:", x);
        emit(O_VAR);
        emit(i);
        up(1);
        if (tail)
            emit(O_RET);
        return;
    }
    if (!IS_CONS(x))
        bad("not a term:", x);
    h = CAR(x);
    args = CDR(x);
    if (h == S_QUOTE) {
        if (!IS_CONS(args) || CDR(args) != NIL)
            bad("not a term:", x);
        emit(O_CONST);
        emit((long)add_const(CAR(args)));
        up(1);
        if (tail)
            emit(O_RET);
        return;
    }
    if ((n = length(args)) < 0)
        bad("not a term:", x);
    if (IS_CONS(h)) {
        V formals = IS_CONS(CDR(h)) ? CAR(CDR(h)) : NIL;
        if (CAR(h) != S_LAMBDA || length(h) != 3 || !variables(formals) ||
            length(formals) != n)
            bad("not a term:", x);
        for (y = args; IS_CONS(y); y = CDR(y))
            comp(CAR(y), scope, 0, nest + 1);
        if (tail) {
            emit(O_REBIND);
            emit(n);
            depth = n;
            comp(CAR(CDR(CDR(h))), formals, 1, nest + 1);
        } else {
            long d0 = depth - n, outer = fbase;
            emit(O_ENTER);
            emit(d0 - outer);
            fbase = d0;
            comp(CAR(CDR(CDR(h))), formals, 0, nest + 1);
            fbase = outer;
            emit(O_LEAVE);
            emit(d0 - outer);
            depth = d0 + 1;
        }
        return;
    }
    if (!IS_SYM(h))
        bad("not a term:", x);
    if (h == S_IF) {
        if (n != 3)
            bad("not a term:", x);
        comp(CAR(args), scope, 0, nest + 1);
        emit(O_JNIL);
        l1 = cb_n;
        emit(0);
        d = --depth;
        comp(CAR(CDR(args)), scope, tail, nest + 1);
        if (!tail) {
            emit(O_JMP);
            l2 = cb_n;
            emit(0);
        }
        depth = d;
        cb[l1] = (long)cb_n;
        comp(CAR(CDR(CDR(args))), scope, tail, nest + 1);
        if (!tail)
            cb[l2] = (long)cb_n;
        return;
    }
    if (h == S_RETURN_LAST && n == 3 && IS_CONS(CAR(args)) && CAR(CAR(args)) == S_QUOTE &&
        IS_CONS(CDR(CAR(args))) && CAR(CDR(CAR(args))) == S_MBE1_RAW &&
        CDR(CDR(CAR(args))) == NIL) {
        /* The executable half of an mbe is checked, and not run. */
        size_t mark = cb_n;
        d = depth;
        comp(CAR(CDR(args)), scope, 0, nest + 1);
        cb_n = mark;
        depth = d;
        comp(CAR(CDR(CDR(args))), scope, tail, nest + 1);
        return;
    }
    h = resolve(h);
    p = syms[SYMIDX(h)].prim;
    k = p >= 0 ? -1 : fn_of(h);
    if (p >= 0 ? prim_arity[p] != n : fns[k].arity >= 0 && fns[k].arity != n)
        bad("not a term: a call with the wrong number of arguments:", x);
    for (y = args; IS_CONS(y); y = CDR(y))
        comp(CAR(y), scope, 0, nest + 1);
    emit(p >= 0 ? O_PRIM : tail ? O_TCALL : O_CALL);
    emit(p >= 0 ? p : k);
    depth -= n - 1;
    if (depth > maxdepth)
        maxdepth = depth;
    if (p >= 0 && tail)
        emit(O_RET);
}

static void compile(V body, V formals, Code *c)
{
    cb_n = 0;
    fbase = 0;
    depth = maxdepth = length(formals);
    comp(body, formals, 1, 0);
    c->op = xalloc(NULL, 0, cb_n * sizeof(long));
    memcpy(c->op, cb, cb_n * sizeof(long));
    c->n = cb_n;
    c->maxstack = (size_t)maxdepth + 1;
}

/* Reads and compiles the define line of the function K. */
static void build(long k)
{
    const unsigned char *p = fns[k].line, *e = fns[k].end;
    size_t base = sp, i;
    long j;
    V d;
    Code c;
    set_place(fns[k].file, fns[k].lineno);
    p = read_datum(p + 8, e);
    while (p < e && *p == ' ')
        p = read_datum(p + 1, e);
    if (e - p != 1 || *p != ')')
        bad("not in the format: a define line", NOV);
    for (i = base + 1; i < sp; i++) {
        d = stk[i];
        if (length(d) != 3 || !IS_SYM(CAR(d)) || !variables(CAR(CDR(d))))
            bad("not in the format: a definition", NOV);
        j = fn_of(CAR(d));
        if (fns[j].line != fns[k].line)
            continue;   /* a later line defines it */
        if (fns[j].arity != length(CAR(CDR(d))))
            bad("not in the format: a definition", NOV);
        compile(CAR(CDR(CDR(d))), CAR(CDR(d)), &c);
        fns[j].code = c;
        fns[j].built = 1;
        defs_built++;
    }
    sp = base;
    set_place(-1, 0);
}

static void ensure_built(long k)
{
    if (fns[k].built)
        return;
    if (fns[k].line == NULL)
        stop(S_NO_VALUE, "no value: a call of a function that has no definition and no attachment:", fns[k].sym);
    build(k);
}

void build_all(void)
{
    size_t k;
    for (k = 0; k < nfns; k++)
        if (fns[k].line != NULL && !fns[k].built)
            build((long)k);
}

/* The primitives that the machine does not do itself. */

static unsigned char *sbuf;
static size_t sbuf_cap;

static void sbuf_room(size_t n)
{
    if (n >= sbuf_cap) {
        sbuf = xalloc(sbuf, sbuf_cap, n + 1);
        sbuf_cap = n + 1;
    }
}

/* Copies the bytes of a string into sbuf, and returns their number. */
static size_t sbuf_string(V str)
{
    size_t i, n = STRLEN(str);
    sbuf_room(n);
    for (i = 0; i < n; i++)
        sbuf[i] = (unsigned char)STRBYTE(str, i);
    return n;
}

static void prim(int p);
V rt_prim(int p, size_t top)
{
    sp = top;
    prim(p);
    return stk[sp - 1];
}

void rt_grow(size_t top, size_t n)
{
    sp = top;
    stk_reserve(n);
}

static void prim(int p)
{
    V a = stk[sp - 1], b = sp >= 2 ? stk[sp - 2] : NIL, r = NIL, x;
    size_t i, n;
    long k;
    switch (p) {
    case P_ACL2_NUMBERP: r = IS_NUM(a) ? T : NIL; break;
    case P_BAD_ATOM_LE: sp--; r = NIL; break;
    case P_TIMES: r = num_mul(b, a); sp--; break;
    case P_PLUS: r = num_add(b, a); sp--; break;
    case P_MINUS: r = num_neg(a); break;
    case P_RECIP: r = num_inv(a); break;
    case P_LESS: r = num_less(b, a) ? T : NIL; sp--; break;
    case P_CAR: r = IS_CONS(a) ? CAR(a) : NIL; break;
    case P_CDR: r = IS_CONS(a) ? CDR(a) : NIL; break;
    case P_CHAR_CODE: r = MKFIX(IS_CHAR(a) ? (long)CHARCODE(a) : 0L); break;
    case P_CHARACTERP: r = IS_CHAR(a) ? T : NIL; break;
    case P_CODE_CHAR:
        r = MKCHAR(IS_FIX(a) && FIXVAL(a) >= 0 && FIXVAL(a) <= 255 ? (unsigned)FIXVAL(a) : 0u);
        break;
    case P_COMPLEX: r = num_complex(b, a); sp--; break;
    case P_COMPLEX_RATIONALP: r = IS_COMPLEX(a) ? T : NIL; break;
    case P_COERCE:
        if (a == S_LIST) {
            if (IS_STRING(b)) {
                need(STRLEN(b), 0);
                b = stk[sp - 2];
                for (i = STRLEN(b); i-- > 0;)
                    r = mkcons(MKCHAR(STRBYTE(b, i)), r);
            }
        } else {
            for (n = 0, x = b; IS_CONS(x); x = CDR(x))
                n++;
            sbuf_room(n);
            for (i = 0, x = b; i < n; i++, x = CDR(x))
                sbuf[i] = (unsigned char)(IS_CHAR(CAR(x)) ? CHARCODE(CAR(x)) : 0u);
            r = mkstring(sbuf, n);
        }
        sp--;
        break;
    case P_CONS:
        need(1, 0);
        r = mkcons(stk[sp - 2], stk[sp - 1]);
        sp--;
        break;
    case P_CONSP: r = IS_CONS(a) ? T : NIL; break;
    case P_DENOMINATOR: r = num_part(a, 1); break;
    case P_EQUAL: r = equal(b, a) ? T : NIL; sp--; break;
    case P_IMAGPART: r = num_part(a, 3); break;
    case P_INTEGERP: r = IS_INT(a) ? T : NIL; break;
    case P_INTERN:
        if (IS_STRING(b) && IS_SYM(a)) {
            n = sbuf_string(b);
            r = intern_in(syms[SYMIDX(a)].pkg, sbuf, n);
        }
        sp--;
        break;
    case P_NUMERATOR: r = num_part(a, 0); break;
    case P_PKG_IMPORTS:
    case P_PKG_WITNESS:
        if (!IS_STRING(a)) {
            k = pkg_find((const unsigned char *)"ACL2", 4);
            if (k < 0)
                stop(S_INPUT, "the package ACL2 is not declared", NOV);
            r = p == P_PKG_IMPORTS ? NIL
                : intern_in((int)k, (const unsigned char *)"ACL2-PKG-WITNESS", 16);
            break;
        }
        n = sbuf_string(a);
        k = pkg_find(sbuf, n);
        if (k < 0 || !pkgs[k].declared || pkgs[k].hidden)
            stop(S_NO_VALUE, p == P_PKG_IMPORTS
                 ? "no value: pkg-imports of a string that names no package, or a hidden one:"
                 : "no value: pkg-witness of a string that names no package, or a hidden one:", a);
        r = p == P_PKG_IMPORTS ? consts[pkgs[k].imports]
            : intern_in((int)k, (const unsigned char *)"ACL2-PKG-WITNESS", 16);
        break;
    case P_RATIONALP: r = IS_RAT(a) ? T : NIL; break;
    case P_REALPART: r = num_part(a, 2); break;
    case P_STRINGP: r = IS_STRING(a) ? T : NIL; break;
    case P_SYMBOL_NAME:
        r = IS_SYM(a) ? mkstring(syms[SYMIDX(a)].name, syms[SYMIDX(a)].len) : mkstring(NULL, 0);
        break;
    case P_SYMBOL_PACKAGE_NAME:
        if (!IS_SYM(a)) {
            r = mkstring(NULL, 0);
            break;
        }
        if (pkgs[syms[SYMIDX(a)].pkg].hidden)
            stop(S_NO_VALUE, "no value: symbol-package-name of a symbol of a hidden package:", a);
        r = mkstring(pkgs[syms[SYMIDX(a)].pkg].name, pkgs[syms[SYMIDX(a)].pkg].len);
        break;
    case P_SYMBOLP: r = IS_SYM(a) ? T : NIL; break;
    }
    stk[sp - 1] = r;
}

/* For the fast runner. */

long fn_lookup(V s)
{
    return IS_SYM(s) ? syms[SYMIDX(s)].fn : -1;
}

char *trap_active;
jmp_buf stop_trap;

/* Builds the line of K as a call would, but a stop is caught: the line
   is then left unbuilt, so that the call, when the interpreter makes it,
   stops as the reference does. */
int try_build(long k)
{
    static char on;
    size_t base = sp, nc = nconsts, i;
    unsigned long nb = defs_built;
    const unsigned char *line = fns[k].line;
    if (fns[k].built)
        return 1;
    if (line == NULL)
        return 0;
    trap_active = &on;
    if (setjmp(stop_trap) == 0) {
        build(k);
        trap_active = NULL;
        return 1;
    }
    trap_active = NULL;
    sp = base;
    set_place(-1, 0);
    for (i = 0; i < nfns; i++)
        if (fns[i].line == line && fns[i].built) {
            fns[i].built = 0;
            xalloc(fns[i].code.op, fns[i].code.n * sizeof(long), 0);
            fns[i].code.op = NULL;
        }
    defs_built = nb;
    (void)nc;
    return 0;
}

/* The machine. */

typedef struct { long fn; size_t pc, fp; } Ret;   /* fn -1: the term */
static Ret *rets;
static size_t nrets, rets_cap;
static const long *top_op;
char *stack_floor;

static void more_rets(void)
{
    size_t cap = rets_cap ? 2 * rets_cap : 1024;
    if (cap > (size_t)-1 / sizeof(Ret))
        stop(S_MEMORY, "memory exhausted: the recursion is too deep", NOV);
    rets = xalloc(rets, rets_cap * sizeof(Ret), cap * sizeof(Ret));
    rets_cap = cap;
}

/* Runs code OP of function FN (-1: the term) from PC, with its frame at
   FP and the top of its stack at S, until it returns to the return
   point BASE. */
static V machine(long fn, const long *op, size_t pc, size_t fp, size_t s, size_t base)
{
    long k;
    V *st, a, b, v;
#define SYNC (sp = s)
#define RELOAD (st = stk, s = sp)
    st = stk;
    for (;;) {
        switch (op[pc]) {
        case O_CONST:
            st[s++] = consts[op[pc + 1]];
            pc += 2;
            break;
        case O_VAR:
            st[s] = st[fp + (size_t)op[pc + 1]];
            s++;
            pc += 2;
            break;
        case O_JNIL:
            pc = st[--s] == NIL ? (size_t)op[pc + 1] : pc + 2;
            break;
        case O_JMP:
            pc = (size_t)op[pc + 1];
            break;
        case O_PRIM:
            a = st[s - 1];
            b = s - fp >= 2 ? st[s - 2] : NIL;
            switch (op[pc + 1]) {
            case P_CAR: st[s - 1] = IS_CONS(a) ? CAR(a) : NIL; break;
            case P_CDR: st[s - 1] = IS_CONS(a) ? CDR(a) : NIL; break;
            case P_CONSP: st[s - 1] = IS_CONS(a) ? T : NIL; break;
            case P_SYMBOLP: st[s - 1] = IS_SYM(a) ? T : NIL; break;
            case P_INTEGERP: st[s - 1] = IS_INT(a) ? T : NIL; break;
            case P_EQUAL:
                s--;
                st[s - 1] = a == b || equal(a, b) ? T : NIL;
                break;
            case P_CONS:
                if (cell_top < cell_cap) {
                    s--;
                    st[s - 1] = mkcons(b, a);
                    break;
                }
                SYNC; prim(P_CONS); RELOAD;
                break;
            case P_PLUS:
                if (IS_FIX(a) && IS_FIX(b)) {
                    long r = FIXVAL(b) + FIXVAL(a);
                    if (r >= FIXMIN && r <= FIXMAX) {
                        s--;
                        st[s - 1] = MKFIX(r);
                        break;
                    }
                }
                SYNC; prim(P_PLUS); RELOAD;
                break;
            case P_TIMES:
                if (IS_FIX(a) && IS_FIX(b)) {
                    long long r = (long long)FIXVAL(b) * FIXVAL(a);
                    if (r >= FIXMIN && r <= FIXMAX) {
                        s--;
                        st[s - 1] = MKFIX((long)r);
                        break;
                    }
                }
                SYNC; prim(P_TIMES); RELOAD;
                break;
            case P_MINUS:
                if (IS_FIX(a) && a != MKFIX(FIXMIN)) {
                    st[s - 1] = MKFIX(-FIXVAL(a));
                    break;
                }
                SYNC; prim(P_MINUS); RELOAD;
                break;
            case P_LESS:
                if (IS_FIX(a) && IS_FIX(b)) {
                    s--;
                    st[s - 1] = FIXVAL(b) < FIXVAL(a) ? T : NIL;
                    break;
                }
                SYNC; prim(P_LESS); RELOAD;
                break;
            default:
                SYNC; prim((int)op[pc + 1]); RELOAD;
                break;
            }
            pc += 2;
            break;
        case O_CALL:
        case O_TCALL:
            k = op[pc + 1];
            if (natv[k] != nat_interp && !STACK_LOW()) {
                size_t ar = (size_t)fns[k].arity;
                if (op[pc] == O_CALL) {
                    SYNC;
                    v = natv[k](s - ar, k);
                    st = stk;
                    s -= ar;
                    st[s++] = v;
                    pc += 2;
                    break;
                }
                memmove(st + fp, st + s - ar, ar * sizeof(V));
                s = fp + ar;
                SYNC;
                v = natv[k](fp, k);
                st = stk;
                goto ret;
            }
            if (!fns[k].built) {
                SYNC; ensure_built(k); RELOAD;
            }
            if (op[pc] == O_CALL) {
                if (nrets == rets_cap)
                    more_rets();
                rets[nrets].fn = fn;
                rets[nrets].pc = pc + 2;
                rets[nrets].fp = fp;
                nrets++;
                fp = s - (size_t)fns[k].arity;
            } else {
                memmove(st + fp, st + s - fns[k].arity, (size_t)fns[k].arity * sizeof(V));
                s = fp + (size_t)fns[k].arity;
            }
            if (stk_cap - fp < fns[k].code.maxstack) {
                SYNC; stk_reserve(fns[k].code.maxstack + (s - fp)); RELOAD;
            }
            fn = k;
            op = fns[k].code.op;
            pc = 0;
            break;
        case O_RET:
            v = st[s - 1];
        ret:
            s = fp;
            if (nrets == base) {
                SYNC;
                return v;
            }
            nrets--;
            fn = rets[nrets].fn;
            pc = rets[nrets].pc;
            fp = rets[nrets].fp;
            op = fn >= 0 ? fns[fn].code.op : top_op;
            st[s++] = v;
            break;
        case O_ENTER:
            fp += (size_t)op[pc + 1];
            pc += 2;
            break;
        case O_LEAVE:
            v = st[s - 1];
            s = fp;
            fp -= (size_t)op[pc + 1];
            st[s++] = v;
            pc += 2;
            break;
        case O_REBIND:
            memmove(st + fp, st + s - op[pc + 1], (size_t)op[pc + 1] * sizeof(V));
            s = fp + (size_t)op[pc + 1];
            pc += 2;
            break;
        }
    }
}

/* Function K, its arguments at stk[fp], run in the interpreter. */
V interp_fn(long k, size_t fp)
{
    size_t ar;
    sp = fp + (fns[k].arity > 0 ? (size_t)fns[k].arity : 0);
    if (!fns[k].built)
        ensure_built(k);
    ar = (size_t)fns[k].arity;
    sp = fp + ar;
    if (stk_cap - fp < fns[k].code.maxstack)
        stk_reserve(fns[k].code.maxstack + ar);
    return machine(k, fns[k].code.op, 0, fp, fp + ar, nrets);
}

V nat_interp(size_t fp, long k)
{
    return interp_fn(k, fp);
}

V run_term(void)
{
    Code top;
    size_t fp;
    V v;
    set_place(-1, 0);
    compile(stk[sp - 1], NIL, &top);
    sp--;
    fp = sp;
    nrets = 0;
    stk_reserve(top.maxstack);
    top_op = top.op;
    v = machine(-1, top.op, 0, fp, fp, 0);
    xalloc(top.op, top.n * sizeof(long), 0);
    return v;
}
