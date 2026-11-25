/* The functions of the prelude on strings and lists: length, char and
   subseq (README.md, "The prelude").  ACL2 defines each through the list
   of the characters of a string, so that a call costs time and memory in
   proportion to the length of the string; here a string's length and its
   bytes are at hand.  Each gives, for every argument, the value that its
   definition in ACL2 gives:

     (length x)        (if (stringp x) (len (coerce x 'list)) (len x))
     (char s n)        (nth n (coerce s 'list))
     (subseq seq a e)  (subseq-list L a (if e e (length seq))), where L is
                       seq, or the list of its characters if it is a
                       string, and the result is then made a string
     (subseq-list l a e)  (take (+ e (- a)) (nthcdr a l))

   nth, nthcdr and take count down a positive integer and take any other
   argument as 0 (zp); car and cdr of an atom are nil; take goes on past
   the end of its list with nil; and coerce makes nil, as any element
   that is not a character, the character of code 0.  A datum is moved
   by the collector, so a value is read from stk again after anything
   that can collect. */

#include "prelude.h"

/* The natural number N as an integer. */
static V natural(size_t n)
{
    V hi;
    if (n <= (size_t)FIXMAX)
        return MKFIX((long)n);
    hi = num_mul(natural(n >> 28), MKFIX(1L << 28));
    return num_add(hi, MKFIX((long)(n & ((1UL << 28) - 1))));
}

/* What zp leaves of V to count down: V if it is a positive integer, and
   otherwise 0; (size_t)-1 if V is at least 10^18, above every length of
   a string or a list. */
static size_t count_of(V v)
{
    unsigned long long n = 0;
    size_t i;
    if (IS_FIX(v))
        return FIXVAL(v) > 0 ? (size_t)FIXVAL(v) : 0;
    if (!IS_BIG(v) || BTYPE(v) != B_POS)
        return 0;
    if (BSIZE(v) > 2)
        return (size_t)-1;
    for (i = BSIZE(v); i-- > 0;)
        n = n * 1000000000ULL + BOX(v)[1 + i];
    return n > (size_t)-1 ? (size_t)-1 : (size_t)n;
}

/* The number of characters of a string, or of conses of a list. */
static size_t length_of(V x)
{
    size_t n = 0;
    if (IS_STRING(x))
        return STRLEN(x);
    for (; IS_CONS(x); x = CDR(x))
        n++;
    return n;
}

V pre_length(size_t base)
{
    return natural(length_of(stk[base]));
}

V pre_char(size_t base)
{
    V s = stk[base];
    size_t i;
    if (!IS_STRING(s))
        return NIL;
    i = count_of(stk[base + 1]);
    return i < STRLEN(s) ? MKCHAR(STRBYTE(s, i)) : NIL;
}

V pre_subseq(size_t base)
{
    V e = stk[base + 2], a = stk[base + 1], d, r, rest;
    size_t n, from, len, i;
    if (e == NIL)
        e = stk[base + 2] = natural(length_of(stk[base]));
    a = stk[base + 1];
    if (IS_FIX(e) && IS_FIX(a)) {
        long m = FIXVAL(e) - FIXVAL(a);
        n = m > 0 ? (size_t)m : 0;
    } else {
        d = num_neg(IS_NUM(a) ? a : MKFIX(0));
        e = stk[base + 2];
        d = num_add(IS_NUM(e) ? e : MKFIX(0), d);
        n = count_of(d);
    }
    from = count_of(stk[base + 1]);
    if (IS_STRING(stk[base])) {
        unsigned char *buf;
        if (n > mem_limit)
            stop(S_MEMORY, "memory exhausted: a datum is too large", NOV);
        buf = xalloc(NULL, 0, n + 1);
        rest = stk[base];
        len = STRLEN(rest);
        for (i = 0; i < n; i++)
            buf[i] = from < len && i < len - from ? (unsigned char)STRBYTE(rest, from + i) : 0;
        r = mkstring(buf, n);
        xalloc(buf, n + 1, 0);
        return r;
    } else {
        V *elt;
        if (n > mem_limit / (2 * sizeof(V)))
            stop(S_MEMORY, "memory exhausted: a datum is too large", NOV);
        need(n, 0);
        elt = xalloc(NULL, 0, (n + 1) * sizeof(V));
        rest = stk[base];
        for (i = 0; i < from; i++) {
            if (!IS_CONS(rest)) {
                rest = NIL;
                break;
            }
            rest = CDR(rest);
        }
        for (i = 0; i < n; i++) {
            elt[i] = IS_CONS(rest) ? CAR(rest) : NIL;
            rest = IS_CONS(rest) ? CDR(rest) : NIL;
        }
        for (r = NIL, i = n; i-- > 0;)
            r = mkcons(elt[i], r);
        xalloc(elt, (n + 1) * sizeof(V), 0);
        return r;
    }
}
