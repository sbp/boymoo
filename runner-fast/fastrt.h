/* What the generated C sees of the runner: the data of run.h, the
   native-function table, and inline forms of the machine's fast paths.
   Every generated function has the type NatFn: its arguments are the
   ARITY words at stk[fp], its frame is stk[fp] onward, and it returns
   its value.  Every datum it holds across anything that can collect is
   in its frame, below sp at that point, exactly as in the interpreter. */

#ifndef FASTRT_H
#define FASTRT_H

#include <string.h>
#include "run.h"

typedef V (*NatFn)(size_t fp, long k);
extern NatFn *natv;            /* by function number; nat_interp if none */
extern char *stack_floor;      /* below this the C stack is too short */
V nat_interp(size_t fp, long k);       /* runs function K in the interpreter */
V interp_fn(long k, size_t fp);
V rt_prim(int p, size_t top);  /* the primitive P on stk[..top) */
void rt_grow(size_t top, size_t n);
V num_quotient(V a, V b);    /* of integers a >= 0 by b > 0, rounded down; NOV otherwise */
V num_bits(V a, V b, int op); /* integers below 2^127 bit by bit: 0 and, 1 or, 2 xor, 3 eqv; NOV otherwise */
V num_shift(V i, V c);        /* i times 2^c rounded down, both and the result below 2^127; NOV otherwise */

struct fast_fn {
    const char *name;
    NatFn fn;
    unsigned *K;      /* the constants of its code that are not written in */
    size_t nK;
    long *C;          /* the functions its code calls */
    size_t nC;
};
struct fast_unit {
    size_t n;
    const struct fast_fn *fns;
    size_t nx;                 /* the functions inlined, by name */
    const char *const *xnames;
    size_t nxk;                /* their constants: name index, ordinal */
    const long *xkd;
    unsigned *xk;
    size_t nxc;                /* their calls: name index, ordinal */
    const long *xcd;
    long *xc;
    int broken;                /* the tables overflowed: do not use */
};

#define S(i) (stk[fp + (i)])
#define STACK_LOW() ((char *)__builtin_frame_address(0) < stack_floor)
#define MUSTTAIL __attribute__((musttail))

static inline V f_car(V a) { return IS_CONS(a) ? CAR(a) : NIL; }
static inline V f_cdr(V a) { return IS_CONS(a) ? CDR(a) : NIL; }
static inline V f_bool(int c) { return c ? T : NIL; }

static inline V f_cons(V a, V d, size_t top)
{
    if (cell_top < cell_cap) {
        size_t i = cell_top++;
        cells[2 * i] = a;
        cells[2 * i + 1] = d;
        return MKCONS(i);
    }
    return rt_prim(P_CONS, top);
}

static inline V f_equal(V a, V b)
{
    if (a == b)
        return T;
    if ((a & 1) || (b & 1))
        return NIL;
    return equal(a, b) ? T : NIL;
}

static inline V f_plus(V b, V a, size_t top)
{
    if (IS_FIX(a) && IS_FIX(b)) {
        long r = FIXVAL(b) + FIXVAL(a);
        if (r >= FIXMIN && r <= FIXMAX)
            return MKFIX(r);
    }
    return rt_prim(P_PLUS, top);
}

static inline V f_times(V b, V a, size_t top)
{
    if (IS_FIX(a) && IS_FIX(b)) {
        long long r = (long long)FIXVAL(b) * FIXVAL(a);
        if (r >= FIXMIN && r <= FIXMAX)
            return MKFIX((long)r);
    }
    return rt_prim(P_TIMES, top);
}

static inline V f_minus(V a, size_t top)
{
    if (IS_FIX(a) && a != MKFIX(FIXMIN))
        return MKFIX(-FIXVAL(a));
    return rt_prim(P_MINUS, top);
}

static inline V f_less(V b, V a, size_t top)
{
    if (IS_FIX(a) && IS_FIX(b))
        return FIXVAL(b) < FIXVAL(a) ? T : NIL;
    return rt_prim(P_LESS, top);
}

#endif
