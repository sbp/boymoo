/* The translator from the machine's code to C.  Each operation of a
   function's code becomes the C that does what the machine does for it
   (eval.c, machine()).  The depth of the operand stack is known at
   every point of the code, so every slot is stk[fp + n] for a number n
   written into the C; a jump is a goto; a call is a C call; a tail call
   of the function itself is a jump to its start, and any other tail call
   is a C tail call that does not grow the C stack.  Constants that are
   symbols, conses or boxes are read from the table of constants by an
   index that the driver fills when the code is loaded, and called
   functions are found by number the same way, so the C depends only on
   the shape of the code and can be kept between runs. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "fast.h"

char *gen_out;
size_t gen_len;
static size_t gen_cap;

static void put(const char *s, size_t n)
{
    if (gen_cap - gen_len < n + 1) {
        size_t c = gen_cap ? gen_cap : 65536;
        while (c - gen_len < n + 1)
            c *= 2;
        gen_out = xalloc(gen_out, gen_cap, c);
        gen_cap = c;
    }
    memcpy(gen_out + gen_len, s, n);
    gen_len += n;
}

#include <stdarg.h>
static void pf(const char *fmt, ...)
{
    char b[512];
    int n;
    va_list ap;
    va_start(ap, fmt);
    n = vsnprintf(b, sizeof b, fmt, ap);
    va_end(ap);
    put(b, (size_t)n);
}

int const_inline(V v)
{
    return v == NIL || v == T || IS_FIX(v) || IS_CHAR(v);
}

/* The text of a symbol as a C string literal. */
static void put_name(V s)
{
    size_t i;
    out_len = 0;
    print_datum(s);
    put("\"", 1);
    for (i = 0; i < out_len; i++) {
        if (out[i] == '"' || out[i] == '\\')
            put("\\", 1);
        put(out + i, 1);
    }
    put("\"", 1);
}

/* Inlining.  A call of a small function that is not the function
   being written is replaced by that function's code, with its frame at
   the place of its arguments.  At a call that is not in the last
   position, its returns store the value and jump past it, and its tail
   calls become calls; at a tail call, its returns return and its tail
   calls stay tail calls.  The constants and calls of inlined code are
   found, when the unit is loaded, by the name of the inlined function
   and their ordinal in its code: the tables X below. */

#define INL_MAX_OPS 48       /* words of code of a function inlined */
#define INL_MAX_DEPTH 3

static long xname[4096];     /* functions named by the X tables */
static size_t nxname;
static long xk[2 * 8192], xc[2 * 8192];   /* pairs: name index, ordinal */
static size_t nxk, nxc;
static int x_full;
static long host;            /* the function being written */
static const long *g_unit;
static size_t g_n, g_idx, g_nk, g_nc, g_lab, g_maxtop;
static long chain[INL_MAX_DEPTH + 1];

static size_t xname_of(long k)
{
    size_t i;
    for (i = 0; i < nxname; i++)
        if (xname[i] == k)
            return i;
    if (nxname == sizeof xname / sizeof xname[0]) {
        x_full = 1;
        return 0;
    }
    xname[nxname] = k;
    return nxname++;
}

static size_t ordinal(long k, size_t at, int calls)
{
    const long *op = fns[k].code.op;
    size_t pc, n = 0;
    for (pc = 0; pc < at; pc += op[pc] == O_RET ? 1 : 2)
        if (calls ? (op[pc] == O_CALL || op[pc] == O_TCALL)
                  : (op[pc] == O_CONST && !const_inline(consts[op[pc + 1]])))
            n++;
    return n;
}

/* The C expression of a constant or of a called function's number. */
static void ref(char *b, size_t bn, long k, size_t pc, int depth, int calls)
{
    if (depth == 0) {
        if (calls)
            snprintf(b, bn, "C%zu[%zu]", g_idx, g_nc++);
        else
            snprintf(b, bn, "consts[K%zu[%zu]]", g_idx, g_nk++);
        return;
    }
    if (calls) {
        if (nxc >= sizeof xc / sizeof xc[0] / 2) { x_full = 1; snprintf(b, bn, "XC[0]"); return; }
        xc[2 * nxc] = (long)xname_of(k);
        xc[2 * nxc + 1] = (long)ordinal(k, pc, 1);
        snprintf(b, bn, "XC[%zu]", nxc++);
    } else {
        if (nxk >= sizeof xk / sizeof xk[0] / 2) { x_full = 1; snprintf(b, bn, "consts[XK[0]]"); return; }
        xk[2 * nxk] = (long)xname_of(k);
        xk[2 * nxk + 1] = (long)ordinal(k, pc, 0);
        snprintf(b, bn, "consts[XK[%zu]]", nxk++);
    }
}

static int inlinable(long k2, int depth)
{
    int i;
    if (k2 == host || !fns[k2].built || fns[k2].line == NULL || fns[k2].arity < 0 ||
        fns[k2].code.n > INL_MAX_OPS ||
        depth >= INL_MAX_DEPTH || native_named(k2) || getenv("BOYMOO_FAST_NOINLINE"))
        return 0;
    for (i = 0; i < depth; i++)
        if (chain[i] == k2)
            return 0;
    return 1;
}

enum { M_TOP, M_CALL, M_TAIL };

/* Writes the code of K with its frame at FO; MODE as above; END the
   label a return in M_CALL mode jumps to. */
static void emit(long k, long fo, int mode, int depth, size_t end)
{
    const Code *c = &fns[k].code;
    const long *op = c->op;
    size_t pc, i, lid = g_lab++;
    long t, b = fo, x, *tst, *bst;
    char *lab, r1[64];
    int live = 1;
    tst = xalloc(NULL, 0, (c->n + 1) * sizeof(long));
    bst = xalloc(NULL, 0, (c->n + 1) * sizeof(long));
    lab = xalloc(NULL, 0, c->n + 1);
    memset(lab, 0, c->n + 1);
    chain[depth] = k;
    for (pc = 0; pc < c->n; pc += op[pc] == O_RET ? 1 : 2)
        if (op[pc] == O_JNIL || op[pc] == O_JMP)
            lab[op[pc + 1]] = 1;
    if ((size_t)fo + c->maxstack > g_maxtop)
        g_maxtop = (size_t)fo + c->maxstack;
    t = fo + fns[k].arity;
    for (pc = 0; pc < c->n; pc += op[pc] == O_RET ? 1 : 2) {
        if (lab[pc]) {
            if (!live) {
                t = tst[pc];
                b = bst[pc];
            }
            live = 1;
            pf("L%zu_%zu:;\n", lid, pc);
        }
        if (!live) {
            /* unreachable code still holds constants and calls */
            if (depth == 0 && op[pc] == O_CONST && !const_inline(consts[op[pc + 1]]))
                g_nk++;
            if (depth == 0 && (op[pc] == O_CALL || op[pc] == O_TCALL))
                g_nc++;
            continue;
        }
        switch (op[pc]) {
        case O_CONST: {
            V v = consts[op[pc + 1]];
            if (const_inline(v))
                pf("    S(%ld) = (V)0x%lXu;\n", t, (unsigned long)v);
            else {
                ref(r1, sizeof r1, k, pc, depth, 0);
                pf("    S(%ld) = %s;\n", t, r1);
            }
            t++;
            break;
        }
        case O_VAR:
            pf("    S(%ld) = S(%ld);\n", t, b + op[pc + 1]);
            t++;
            break;
        case O_JNIL:
            t--;
            pf("    if (S(%ld) == NIL) goto L%zu_%ld;\n", t, lid, op[pc + 1]);
            tst[op[pc + 1]] = t;
            bst[op[pc + 1]] = b;
            break;
        case O_JMP:
            pf("    goto L%zu_%ld;\n", lid, op[pc + 1]);
            tst[op[pc + 1]] = t;
            bst[op[pc + 1]] = b;
            live = 0;
            break;
        case O_RET:
            if (mode == M_CALL) {
                if (t - 1 != fo)
                    pf("    S(%ld) = S(%ld);\n", fo, t - 1);
                pf("    goto E%zu;\n", end);
            } else
                pf("    return S(%ld);\n", t - 1);
            live = 0;
            break;
        case O_ENTER:
            b += op[pc + 1];
            break;
        case O_LEAVE:
            pf("    S(%ld) = S(%ld);\n", b, t - 1);
            t = b + 1;
            b -= op[pc + 1];
            break;
        case O_REBIND:
            x = op[pc + 1];
            for (i = 0; i < (size_t)x; i++)
                if (b + (long)i != t - x + (long)i)
                    pf("    S(%ld) = S(%ld);\n", b + (long)i, t - x + (long)i);
            t = b + x;
            break;
        case O_PRIM: {
            int p = (int)op[pc + 1], a = prim_arity[p];
            long r = t - a;   /* where the result goes */
            switch (p) {
            case P_CAR: pf("    S(%ld) = f_car(S(%ld));\n", r, r); break;
            case P_CDR: pf("    S(%ld) = f_cdr(S(%ld));\n", r, r); break;
            case P_CONSP: pf("    S(%ld) = f_bool(IS_CONS(S(%ld)));\n", r, r); break;
            case P_SYMBOLP: pf("    S(%ld) = f_bool(IS_SYM(S(%ld)));\n", r, r); break;
            case P_INTEGERP: pf("    S(%ld) = f_bool(IS_INT(S(%ld)));\n", r, r); break;
            case P_CHARACTERP: pf("    S(%ld) = f_bool(IS_CHAR(S(%ld)));\n", r, r); break;
            case P_STRINGP: pf("    S(%ld) = f_bool(IS_STRING(S(%ld)));\n", r, r); break;
            case P_RATIONALP: pf("    S(%ld) = f_bool(IS_RAT(S(%ld)));\n", r, r); break;
            case P_ACL2_NUMBERP: pf("    S(%ld) = f_bool(IS_NUM(S(%ld)));\n", r, r); break;
            case P_COMPLEX_RATIONALP: pf("    S(%ld) = f_bool(IS_COMPLEX(S(%ld)));\n", r, r); break;
            case P_BAD_ATOM_LE: pf("    S(%ld) = NIL;\n", r); break;
            case P_EQUAL: pf("    S(%ld) = f_equal(S(%ld), S(%ld));\n", r, r, r + 1); break;
            case P_CONS: pf("    { V v = f_cons(S(%ld), S(%ld), fp + %ld); S(%ld) = v; }\n", r, r + 1, t, r); break;
            case P_PLUS: pf("    { V v = f_plus(S(%ld), S(%ld), fp + %ld); S(%ld) = v; }\n", r, r + 1, t, r); break;
            case P_TIMES: pf("    { V v = f_times(S(%ld), S(%ld), fp + %ld); S(%ld) = v; }\n", r, r + 1, t, r); break;
            case P_LESS: pf("    { V v = f_less(S(%ld), S(%ld), fp + %ld); S(%ld) = v; }\n", r, r + 1, t, r); break;
            case P_MINUS: pf("    { V v = f_minus(S(%ld), fp + %ld); S(%ld) = v; }\n", r, t, r); break;
            default: pf("    { V v = rt_prim(%d, fp + %ld); S(%ld) = v; }\n", p, t, r); break;
            }
            t = r + 1;
            break;
        }
        case O_CALL:
        case O_TCALL: {
            long k2 = op[pc + 1], na = fns[k2].arity;
            size_t j;
            int tail = op[pc] == O_TCALL;
            char callee[64];
            ref(r1, sizeof r1, k, pc, depth, 1);
            if (na < 0) {
                /* no definition: the interpreter stops at the call */
                pf("    return interp_fn(%s, fp + %ld);\n", r1, t);
                live = 0;
                break;
            }
            /* a tail call in inlined code at a call that is not a tail
               call is a call followed by a return */
            if (tail && mode == M_CALL)
                tail = 0;
            if (inlinable(k2, depth)) {
                if (tail)
                    emit(k2, t - na, M_TAIL, depth + 1, 0);
                else {
                    size_t e = g_lab++;
                    emit(k2, t - na, M_CALL, depth + 1, e);
                    pf("E%zu:;\n", e);
                }
                chain[depth] = k;
            } else {
                for (j = 0; j < g_n && g_unit[j] != k2; j++)
                    ;
                if (j < g_n)
                    snprintf(callee, sizeof callee, "F%zu", j);
                else
                    snprintf(callee, sizeof callee, "natv[%s]", r1);
                if (!tail) {
                    pf("    { V v; if (STACK_LOW()) v = interp_fn(%s, fp + %ld); "
                       "else v = %s(fp + %ld, %s); S(%ld) = v; }\n",
                       r1, t - na, callee, t - na, r1, t - na);
                } else {
                    for (i = 0; i < (size_t)na; i++)
                        if ((long)i != t - na + (long)i)
                            pf("    S(%ld) = S(%ld);\n", (long)i, t - na + (long)i);
                    if (k2 == host)
                        pf("    goto body;\n");
                    else
                        pf("    MUSTTAIL return %s(fp, %s);\n", callee, r1);
                }
            }
            if (tail)
                live = 0;
            else if (op[pc] == O_TCALL) {
                /* M_CALL: the value is that of the inlined function */
                if (t - na != fo)
                    pf("    S(%ld) = S(%ld);\n", fo, t - na);
                pf("    goto E%zu;\n", end);
                live = 0;
            } else
                t = t - na + 1;
            break;
        }
        }
    }
    xalloc(tst, (c->n + 1) * sizeof(long), 0);
    xalloc(bst, (c->n + 1) * sizeof(long), 0);
    xalloc(lab, c->n + 1, 0);
}

static void fn_c(long k, const long *unit, size_t n, size_t idx)
{
    size_t p0, at;
    char num[16];
    host = k;
    g_unit = unit;
    g_n = n;
    g_idx = idx;
    g_nk = g_nc = 0;
    g_lab = 0;
    g_maxtop = 0;
    pf("static V F%zu(size_t fp, long k)\n{\n    (void)k;\n", idx);
    p0 = gen_len;
    pf("    if (stk_cap - fp < %10s)\n        rt_grow(fp + %ld, %10s);\nbody:\n", "", fns[k].arity, "");
    emit(k, 0, M_TOP, 0, 0);
    pf("    return NIL;\n}\n\n");
    /* the room the frame needs, inlined frames included */
    snprintf(num, sizeof num, "%10lu", (unsigned long)g_maxtop);
    at = p0 + strlen("    if (stk_cap - fp < ");
    memcpy(gen_out + at, num, 10);
    at = p0 + strlen("    if (stk_cap - fp < ") + 10 + strlen(")\n        rt_grow(fp + ");
    {
        char ar[32];
        snprintf(ar, sizeof ar, "%ld, ", fns[k].arity);
        at += strlen(ar);
    }
    memcpy(gen_out + at, num, 10);
}

/* The numbers of constants not written in, and of calls, in the code of
   K; the driver walks the code in the same way to fill the tables. */
void code_counts(long k, size_t *nk, size_t *nc)
{
    const Code *c = &fns[k].code;
    size_t pc;
    *nk = *nc = 0;
    for (pc = 0; pc < c->n; pc += c->op[pc] == O_RET ? 1 : 2)
        if (c->op[pc] == O_CONST && !const_inline(consts[c->op[pc + 1]]))
            ++*nk;
        else if (c->op[pc] == O_CALL || c->op[pc] == O_TCALL)
            ++*nc;
}

void gen_unit(const long *unit, size_t n, const char *uname)
{
    size_t i, nk, nc;
    gen_len = 0;
    pf("#include \"fastrt.h\"\n\n/*");
    for (i = 0; i < n; i++) {
        put(" ", 1);
        put_name(fns[unit[i]].sym);
    }
    pf(" */\n\n");
    /* For profiles, with BOYMOO_FAST_NAMES=1: each function has the name
       of its definition, every character that C does not allow in a name
       being written as _. */
    if (getenv("BOYMOO_FAST_NAMES") != NULL)
        for (i = 0; i < n; i++) {
            size_t j;
            out_len = 0;
            print_datum(fns[unit[i]].sym);
            pf("#define F%zu P_", i);
            for (j = 0; j < out_len; j++) {
                char ch = out[j];
                if (!((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9')))
                    ch = '_';
                put(&ch, 1);
            }
            pf("\n");
        }
    for (i = 0; i < n; i++) {
        code_counts(unit[i], &nk, &nc);
        pf("static V F%zu(size_t fp, long k);\nstatic unsigned K%zu[%zu];\nstatic long C%zu[%zu];\n",
           i, i, nk ? nk : 1, i, nc ? nc : 1);
    }
    put("\n", 1);
    nxname = nxk = nxc = 0;
    x_full = 0;
    pf("#define XCAT2(a, b) a##b\n#define XCAT(a, b) XCAT2(a, b)\n#define XK XCAT(UNIT, _XK)\n#define XC XCAT(UNIT, _XC)\n"
       "extern unsigned XK[];\nextern long XC[];\n");
    for (i = 0; i < n; i++)
        fn_c(unit[i], unit, n, i);
    pf("unsigned XK[%zu];\nlong XC[%zu];\n", nxk ? nxk : 1, nxc ? nxc : 1);
    pf("static const char *const XN[] = {");
    for (i = 0; i < nxname; i++) {
        put_name(fns[xname[i]].sym);
        put(", ", 2);
    }
    pf("0};\nstatic const long XKD[] = {");
    for (i = 0; i < 2 * nxk; i++)
        pf("%ld, ", xk[i]);
    pf("0};\nstatic const long XCD[] = {");
    for (i = 0; i < 2 * nxc; i++)
        pf("%ld, ", xc[i]);
    pf("0};\n");
    pf("static const struct fast_fn FNS[] = {\n");
    for (i = 0; i < n; i++) {
        code_counts(unit[i], &nk, &nc);
        put("    {", 5);
        put_name(fns[unit[i]].sym);
        pf(", F%zu, K%zu, %zu, C%zu, %zu},\n", i, i, nk, i, nc);
    }
    pf("};\nconst struct fast_unit %s = {%zu, FNS, %zu, XN, %zu, XKD, XK, %zu, XCD, XC, %d};\n",
       uname, n, nxname, nxk, nxc, x_full);
}
