/* Numbers: integers of any size, fractions and complex rationals.

   An integer from -2^29 to 2^29 - 1 is immediate; a larger one is a box
   that holds its sign and its magnitude in base 10^9, so that reading
   and writing it in decimal takes time in proportion to its length.
   Arithmetic is done on copies held outside the heap: Z, an integer;
   Q, a rational in lowest terms with a positive denominator; N, a
   number, as a real and an imaginary part.  A result is put back into
   the heap only when it is complete, so that no collection can happen
   while a calculation holds data of the heap.  Multiplication and
   division are the methods of the schoolbook (division by Knuth's
   algorithm D); greatest common divisors are by Euclid's algorithm. */

#include <string.h>
#include "run.h"

#define BASE 1000000000UL
typedef unsigned long long U;

typedef struct { int neg; size_t n, cap; V *d; } Z;
typedef struct { Z n, d; } Q;
typedef struct { Q re, im; } N;

static void zinit(Z *z, size_t cap)
{
    z->neg = 0;
    z->n = 0;
    z->cap = cap ? cap : 1;
    if (z->cap > (size_t)-1 / sizeof(V))
        stop(S_MEMORY, "memory exhausted: a number is too large", NOV);
    z->d = xalloc(NULL, 0, z->cap * sizeof(V));
}

/* A Z whose CAP is 0 is a view of digits it does not own. */
static void zfree(Z *z)
{
    if (z->cap > 0)
        xalloc(z->d, z->cap * sizeof(V), 0);
}

static void znorm(Z *z)
{
    while (z->n > 0 && z->d[z->n - 1] == 0)
        z->n--;
    if (z->n == 0)
        z->neg = 0;
}

static void zset(Z *z, long long v)
{
    U m = v < 0 ? 0ULL - (U)v : (U)v;
    zinit(z, 3);
    z->neg = v < 0;
    while (m > 0) {
        z->d[z->n++] = (V)(m % BASE);
        m /= BASE;
    }
}

static void zcopy(const Z *a, Z *r)
{
    zinit(r, a->n);
    memcpy(r->d, a->d, a->n * sizeof(V));
    r->n = a->n;
    r->neg = a->neg;
}

static int zone(const Z *z) { return z->n == 1 && z->d[0] == 1 && !z->neg; }

/* Copies an integer of the heap. */
static void ztake(Z *z, V v)
{
    if (IS_FIX(v)) {
        zset(z, FIXVAL(v));
        return;
    }
    zinit(z, BSIZE(v));
    memcpy(z->d, BOX(v) + 1, BSIZE(v) * sizeof(V));
    z->n = BSIZE(v);
    z->neg = BTYPE(v) == B_NEG;
}

static int zfits(const Z *z)
{
    return z->n == 0 || (z->n == 1 && z->d[0] <= (z->neg ? 536870912UL : 536870911UL));
}

static size_t zwords(const Z *z) { return zfits(z) ? 0 : z->n + 1; }

/* Puts an integer into the heap, in space already reserved. */
static V zput(const Z *z)
{
    V b;
    if (zfits(z))
        return z->n == 0 ? MKFIX(0) : z->neg ? MKFIX(-(long)z->d[0]) : MKFIX((long)z->d[0]);
    b = mkbox(z->neg ? B_NEG : B_POS, z->n);
    memcpy(BOX(b) + 1, z->d, z->n * sizeof(V));
    return b;
}

/* A view of an integer of the heap, or of an immediate one put into TMP.
   It is valid until the next allocation in the heap. */
static void zview(Z *z, V v, V *tmp)
{
    long k;
    unsigned long m;
    z->cap = 0;
    if (IS_FIX(v)) {
        k = FIXVAL(v);
        m = k < 0 ? 0UL - (unsigned long)k : (unsigned long)k;
        z->neg = k < 0;
        z->n = 0;
        z->d = tmp;
        if (m > 0)
            tmp[z->n++] = (V)m;
    } else {
        z->neg = BTYPE(v) == B_NEG;
        z->n = BSIZE(v);
        z->d = BOX(v) + 1;
    }
}

static V zresult(Z *r)
{
    V v;
    need(0, zwords(r));
    v = zput(r);
    zfree(r);
    return v;
}

static int zcmpm(const Z *a, const Z *b)
{
    size_t i;
    if (a->n != b->n)
        return a->n < b->n ? -1 : 1;
    for (i = a->n; i-- > 0;)
        if (a->d[i] != b->d[i])
            return a->d[i] < b->d[i] ? -1 : 1;
    return 0;
}

static int zcmp(const Z *a, const Z *b)
{
    if (a->neg != b->neg)
        return a->neg ? -1 : 1;
    return a->neg ? zcmpm(b, a) : zcmpm(a, b);
}

static void zaddm(const Z *a, const Z *b, Z *r)
{
    size_t i, n = a->n > b->n ? a->n : b->n;
    U c = 0;
    zinit(r, n + 1);
    for (i = 0; i < n; i++) {
        c += (U)(i < a->n ? a->d[i] : 0) + (i < b->n ? b->d[i] : 0);
        r->d[i] = (V)(c % BASE);
        c /= BASE;
    }
    r->d[n] = (V)c;
    r->n = n + 1;
}

/* |a| - |b|, where |a| >= |b|. */
static void zsubm(const Z *a, const Z *b, Z *r)
{
    size_t i;
    long long t, br = 0;
    zinit(r, a->n);
    for (i = 0; i < a->n; i++) {
        t = (long long)a->d[i] - (long long)(i < b->n ? b->d[i] : 0) - br;
        br = t < 0;
        r->d[i] = (V)(t < 0 ? t + (long long)BASE : t);
    }
    r->n = a->n;
}

static void zadd(const Z *a, const Z *b, Z *r)
{
    if (a->neg == b->neg) {
        zaddm(a, b, r);
        r->neg = a->neg;
    } else if (zcmpm(a, b) >= 0) {
        zsubm(a, b, r);
        r->neg = a->neg;
    } else {
        zsubm(b, a, r);
        r->neg = b->neg;
    }
    znorm(r);
}

static void zmul(const Z *a, const Z *b, Z *r)
{
    size_t i, j;
    U c, ai;
    zinit(r, a->n + b->n);
    if (a->n == 0 || b->n == 0)
        return;
    for (i = 0; i < a->n + b->n; i++)
        r->d[i] = 0;
    for (i = 0; i < a->n; i++) {
        if ((ai = a->d[i]) == 0)
            continue;
        for (c = 0, j = 0; j < b->n; j++) {
            c += ai * b->d[j] + r->d[i + j];
            r->d[i + j] = (V)(c % BASE);
            c /= BASE;
        }
        r->d[i + b->n] = (V)c;
    }
    r->n = a->n + b->n;
    r->neg = a->neg != b->neg;
    znorm(r);
}

/* The quotient and remainder of the magnitudes, for b not 0. */
static void zdivmod(const Z *a, const Z *b, Z *q, Z *r)
{
    size_t n = b->n, m, i, j;
    U f, c, rem, num, qh, rh, p;
    long long t, br;
    Z u, v;
    if (zcmpm(a, b) < 0) {
        zinit(q, 1);
        zcopy(a, r);
        r->neg = 0;
        return;
    }
    if (n == 1) {
        zinit(q, a->n);
        for (rem = 0, i = a->n; i-- > 0;) {
            c = rem * BASE + a->d[i];
            q->d[i] = (V)(c / b->d[0]);
            rem = c % b->d[0];
        }
        q->n = a->n;
        znorm(q);
        zset(r, (long long)rem);
        return;
    }
    m = a->n - n;
    f = BASE / ((U)b->d[n - 1] + 1);
    zinit(&u, a->n + 1);
    zinit(&v, n);
    for (c = 0, i = 0; i < a->n; i++) {
        c += (U)a->d[i] * f;
        u.d[i] = (V)(c % BASE);
        c /= BASE;
    }
    u.d[a->n] = (V)c;
    for (c = 0, i = 0; i < n; i++) {
        c += (U)b->d[i] * f;
        v.d[i] = (V)(c % BASE);
        c /= BASE;
    }
    zinit(q, m + 1);
    q->n = m + 1;
    for (j = m + 1; j-- > 0;) {
        num = (U)u.d[j + n] * BASE + u.d[j + n - 1];
        qh = num / v.d[n - 1];
        rh = num % v.d[n - 1];
        while (qh >= BASE || qh * v.d[n - 2] > rh * BASE + u.d[j + n - 2]) {
            qh--;
            rh += v.d[n - 1];
            if (rh >= BASE)
                break;
        }
        for (c = 0, br = 0, i = 0; i < n; i++) {
            p = qh * v.d[i] + c;
            c = p / BASE;
            t = (long long)u.d[i + j] - (long long)(p % BASE) - br;
            br = t < 0;
            u.d[i + j] = (V)(t < 0 ? t + (long long)BASE : t);
        }
        t = (long long)u.d[j + n] - (long long)c - br;
        if (t < 0) {
            u.d[j + n] = (V)(t + (long long)BASE);
            qh--;
            for (c = 0, i = 0; i < n; i++) {
                c += (U)u.d[i + j] + v.d[i];
                u.d[i + j] = (V)(c % BASE);
                c /= BASE;
            }
            u.d[j + n] = (V)((u.d[j + n] + c) % BASE);
        } else
            u.d[j + n] = (V)t;
        q->d[j] = (V)qh;
    }
    znorm(q);
    zinit(r, n);
    for (rem = 0, i = n; i-- > 0;) {
        c = rem * BASE + u.d[i];
        r->d[i] = (V)(c / f);
        rem = c % f;
    }
    r->n = n;
    znorm(r);
    zfree(&u);
    zfree(&v);
}

static U zsmall(const Z *z) { return z->n == 0 ? 0 : z->n == 1 ? z->d[0] : (U)z->d[1] * BASE + z->d[0]; }

/* The greatest common divisor of the magnitudes. */
static void zgcd(const Z *a, const Z *b, Z *g)
{
    Z x, y, q, r;
    U s, t, w;
    zcopy(a, &x);
    zcopy(b, &y);
    x.neg = y.neg = 0;
    while (y.n > 0) {
        if (x.n <= 2 && y.n <= 2) {
            for (s = zsmall(&x), t = zsmall(&y); t != 0; s = t, t = w)
                w = s % t;
            zfree(&x);
            zfree(&y);
            zset(g, (long long)s);
            return;
        }
        zdivmod(&x, &y, &q, &r);
        zfree(&q);
        zfree(&x);
        x = y;
        y = r;
    }
    zfree(&y);
    *g = x;
}

static void qfree(Q *q) { zfree(&q->n); zfree(&q->d); }

static void qzero(Q *q) { zinit(&q->n, 1); zset(&q->d, 1); }

static void qtake(Q *q, V v)
{
    if (IS_RATIO(v)) {
        ztake(&q->n, BOX(v)[1]);
        ztake(&q->d, BOX(v)[2]);
    } else if (IS_INT(v)) {
        ztake(&q->n, v);
        zset(&q->d, 1);
    } else
        qzero(q);
}

static size_t qwords(const Q *q) { return zone(&q->d) ? zwords(&q->n) : zwords(&q->n) + zwords(&q->d) + 3; }

static V qput(const Q *q)
{
    V n, d, b;
    if (zone(&q->d))
        return zput(&q->n);
    n = zput(&q->n);
    d = zput(&q->d);
    b = mkbox(B_RATIO, 2);
    BOX(b)[1] = n;
    BOX(b)[2] = d;
    return b;
}

/* The quotient of A by B, which divides it. */
static void zquo(const Z *a, const Z *b, Z *q)
{
    Z r;
    zdivmod(a, b, q, &r);
    zfree(&r);
    q->neg = a->neg != b->neg;
    znorm(q);
}

/* A/B + C/D, by Knuth's method (The Art of Computer Programming, volume
   2, section 4.5.1): with G = gcd(B, D), the sum is T/(B/G * D) for
   T = A*(D/G) + C*(B/G), and only gcd(T, G) remains to divide out. */
static void qadd(const Q *a, const Q *b, Q *r)
{
    Z g, h, e, f, x, y, t, k;
    if (zone(&a->d) && zone(&b->d)) {
        zadd(&a->n, &b->n, &r->n);
        zset(&r->d, 1);
        return;
    }
    zgcd(&a->d, &b->d, &g);
    zquo(&b->d, &g, &e);
    zquo(&a->d, &g, &f);
    zmul(&a->n, &e, &x);
    zmul(&b->n, &f, &y);
    zadd(&x, &y, &t);
    zfree(&x);
    zfree(&y);
    if (t.n == 0) {
        r->n = t;
        zset(&r->d, 1);
    } else {
        zgcd(&t, &g, &h);
        zquo(&t, &h, &r->n);
        zquo(&b->d, &h, &k);
        zmul(&f, &k, &r->d);
        zfree(&t);
        zfree(&h);
        zfree(&k);
    }
    zfree(&g);
    zfree(&e);
    zfree(&f);
}

/* A/B * C/D, as (A/gcd(A,D)) * (C/gcd(C,B)) over (B/gcd(C,B)) * (D/gcd(A,D)). */
static void qmul(const Q *a, const Q *b, Q *r)
{
    Z g, h, w, x, y, z;
    if (a->n.n == 0 || b->n.n == 0) {
        zinit(&r->n, 1);
        zset(&r->d, 1);
        return;
    }
    zgcd(&a->n, &b->d, &g);
    zgcd(&b->n, &a->d, &h);
    zquo(&a->n, &g, &w);
    zquo(&b->n, &h, &x);
    zquo(&a->d, &h, &y);
    zquo(&b->d, &g, &z);
    zmul(&w, &x, &r->n);
    zmul(&y, &z, &r->d);
    zfree(&g);
    zfree(&h);
    zfree(&w);
    zfree(&x);
    zfree(&y);
    zfree(&z);
}

static int qcmp(const Q *a, const Q *b)
{
    Z x, y;
    int c;
    if (zone(&a->d) && zone(&b->d))
        return zcmp(&a->n, &b->n);
    zmul(&a->n, &b->d, &x);
    zmul(&b->n, &a->d, &y);
    c = zcmp(&x, &y);
    zfree(&x);
    zfree(&y);
    return c;
}

/* The reciprocal of a rational that is not 0. */
static void qinv(const Q *a, Q *r)
{
    zcopy(&a->d, &r->n);
    zcopy(&a->n, &r->d);
    r->n.neg = a->n.neg;
    r->d.neg = 0;
}

static void ntake(N *x, V v)
{
    if (IS_COMPLEX(v)) {
        qtake(&x->re, BOX(v)[1]);
        qtake(&x->im, BOX(v)[2]);
    } else {
        qtake(&x->re, v);
        qzero(&x->im);
    }
}

static void nfree(N *x) { qfree(&x->re); qfree(&x->im); }

/* Puts a number into the heap and frees it. */
static V nput(N *x)
{
    V re, im, b;
    if (x->im.n.n == 0) {
        need(0, qwords(&x->re));
        b = qput(&x->re);
    } else {
        need(0, qwords(&x->re) + qwords(&x->im) + 3);
        re = qput(&x->re);
        im = qput(&x->im);
        b = mkbox(B_COMPLEX, 2);
        BOX(b)[1] = re;
        BOX(b)[2] = im;
    }
    nfree(x);
    return b;
}

static V fix_or_big(long long n)
{
    Z z;
    V v;
    if (n >= FIXMIN && n <= FIXMAX)
        return MKFIX((long)n);
    zset(&z, n);
    need(0, zwords(&z));
    v = zput(&z);
    zfree(&z);
    return v;
}

V num_add(V a, V b)
{
    N x, y, r;
    Z p, q, z;
    V s[1], t[1];
    if (IS_FIX(a) && IS_FIX(b))
        return fix_or_big((long long)FIXVAL(a) + FIXVAL(b));
    if (IS_INT(a) && IS_INT(b)) {
        zview(&p, a, s);
        zview(&q, b, t);
        zadd(&p, &q, &z);
        return zresult(&z);
    }
    ntake(&x, a);
    ntake(&y, b);
    qadd(&x.re, &y.re, &r.re);
    qadd(&x.im, &y.im, &r.im);
    nfree(&x);
    nfree(&y);
    return nput(&r);
}

V num_mul(V a, V b)
{
    N x, y, r;
    Q p, q;
    Z u, w, z;
    V s[1], t[1];
    if (IS_FIX(a) && IS_FIX(b))
        return fix_or_big((long long)FIXVAL(a) * FIXVAL(b));
    if (IS_INT(a) && IS_INT(b)) {
        zview(&u, a, s);
        zview(&w, b, t);
        zmul(&u, &w, &z);
        return zresult(&z);
    }
    ntake(&x, a);
    ntake(&y, b);
    qmul(&x.re, &y.re, &p);
    qmul(&x.im, &y.im, &q);
    q.n.neg = !q.n.neg;
    znorm(&q.n);
    qadd(&p, &q, &r.re);
    qfree(&p);
    qfree(&q);
    qmul(&x.re, &y.im, &p);
    qmul(&x.im, &y.re, &q);
    qadd(&p, &q, &r.im);
    qfree(&p);
    qfree(&q);
    nfree(&x);
    nfree(&y);
    return nput(&r);
}

V num_neg(V a)
{
    N x;
    if (IS_FIX(a))
        return fix_or_big(-(long long)FIXVAL(a));
    ntake(&x, a);
    x.re.n.neg = !x.re.n.neg;
    x.im.n.neg = !x.im.n.neg;
    znorm(&x.re.n);
    znorm(&x.im.n);
    return nput(&x);
}

/* The reciprocal: 1/(a+bi) is (a-bi)/(a^2+b^2), and that of 0 is 0. */
V num_inv(V a)
{
    N x, r;
    Q s, t, m;
    ntake(&x, a);
    if (x.im.n.n == 0) {
        if (x.re.n.n == 0)
            return nput(&x);
        qinv(&x.re, &r.re);
        qzero(&r.im);
    } else {
        qmul(&x.re, &x.re, &s);
        qmul(&x.im, &x.im, &t);
        qadd(&s, &t, &m);
        qfree(&s);
        qfree(&t);
        qinv(&m, &s);
        qmul(&x.re, &s, &r.re);
        qmul(&x.im, &s, &r.im);
        r.im.n.neg = !r.im.n.neg;
        znorm(&r.im.n);
        qfree(&s);
        qfree(&m);
    }
    nfree(&x);
    return nput(&r);
}

int num_less(V a, V b)
{
    N x, y;
    Z p, q;
    V s[1], t[1];
    int c;
    if (IS_FIX(a) && IS_FIX(b))
        return FIXVAL(a) < FIXVAL(b);
    if (IS_INT(a) && IS_INT(b)) {
        zview(&p, a, s);
        zview(&q, b, t);
        return zcmp(&p, &q) < 0;
    }
    ntake(&x, IS_NUM(a) ? a : MKFIX(0));
    ntake(&y, IS_NUM(b) ? b : MKFIX(0));
    c = qcmp(&x.re, &y.re);
    if (c == 0)
        c = qcmp(&x.im, &y.im);
    nfree(&x);
    nfree(&y);
    return c < 0;
}

/* The functions of the prelude (README.md, "The prelude").  Each gives
   the value that its definition in ACL2 gives, for every argument. */

/* The floor of A/B, for B positive. */
static void zfloor(const Z *a, const Z *b, Z *q)
{
    Z r, one, s;
    zdivmod(a, b, q, &r);
    if (a->neg && r.n > 0) {
        zset(&one, 1);
        zaddm(q, &one, &s);
        zfree(q);
        zfree(&one);
        *q = s;
    }
    q->neg = a->neg;
    znorm(q);
    zfree(&r);
}

/* (ash i c): the floor of i times 2^c, where an argument that is not an
   integer counts as 0. */
V num_ash(V a, V b)
{
    Z i, p, t, r;
    V s[1];
    unsigned long e;
    int down;
    if (!IS_INT(a) || a == MKFIX(0))
        return MKFIX(0);
    if (!IS_INT(b) || b == MKFIX(0))
        return a;
    zview(&i, a, s);
    down = IS_FIX(b) ? FIXVAL(b) < 0 : BTYPE(b) == B_NEG;
    e = IS_FIX(b) ? (unsigned long)(down ? -FIXVAL(b) : FIXVAL(b)) : 0;
    if (down && (!IS_FIX(b) || e / 30 >= i.n))   /* 2^e is above |i|, which is below 10^(9n) */
        return i.neg ? MKFIX(-1) : MKFIX(0);
    if (!IS_FIX(b))
        stop(S_MEMORY, "memory exhausted: a number is too large", NOV);
    zset(&p, 1);
    zset(&t, 2);
    for (;;) {                  /* p becomes 2^e, by squaring */
        if (e & 1) {
            zmul(&p, &t, &r);
            zfree(&p);
            p = r;
        }
        if ((e >>= 1) == 0)
            break;
        zmul(&t, &t, &r);
        zfree(&t);
        t = r;
    }
    zfree(&t);
    if (down)
        zfloor(&i, &p, &r);
    else
        zmul(&i, &p, &r);
    zfree(&p);
    return zresult(&r);
}

/* The magnitude of Z, less 1 if Z is negative, in base 2^32 in the N
   words of W, where N is at least the number of digits of Z.  In two's
   complement a negative integer -m has exactly the bits that m - 1
   lacks. */
static void zbits(const Z *z, V *w, size_t n)
{
    size_t i, k;
    U c;
    for (k = 0; k < n; k++)
        w[k] = 0;
    for (i = z->n; i-- > 0;)
        for (c = z->d[i], k = 0; k < n; k++) {
            c += (U)w[k] * BASE;
            w[k] = (V)(c & 0xFFFFFFFFUL);
            c >>= 32;
        }
    for (k = 0; z->neg; k++) {
        if (w[k] != 0) {
            w[k]--;
            break;
        }
        w[k] = (V)0xFFFFFFFFUL;
    }
}

/* (binary-logxor i j): the integer whose bits in two's complement are
   those in which i and j differ, where an argument that is not an
   integer counts as 0.  It is negative when one of the two is. */
V num_logxor(V a, V b)
{
    Z x, y, r, one, t;
    V s[1], u[1], *w;
    size_t n, i, k;
    U c;
    zview(&x, IS_INT(a) ? a : MKFIX(0), s);
    zview(&y, IS_INT(b) ? b : MKFIX(0), u);
    n = (x.n > y.n ? x.n : y.n) + 1;
    if (n > (size_t)-1 / (2 * sizeof(V)) - 1)
        stop(S_MEMORY, "memory exhausted: a number is too large", NOV);
    w = xalloc(NULL, 0, 2 * n * sizeof(V));
    zbits(&x, w, n);
    zbits(&y, w + n, n);
    zinit(&r, 2 * n + 1);
    for (k = n; k-- > 0;) {     /* r becomes r * 2^32 + the word k */
        c = (U)((w[k] ^ w[n + k]) & 0xFFFFFFFFUL);
        for (i = 0; i < r.n; i++) {
            c += (U)r.d[i] << 32;
            r.d[i] = (V)(c % BASE);
            c /= BASE;
        }
        for (; c > 0; c /= BASE)
            r.d[r.n++] = (V)(c % BASE);
    }
    xalloc(w, 2 * n * sizeof(V), 0);
    if (x.neg != y.neg) {       /* the bits it lacks: it is -(r + 1) */
        zset(&one, 1);
        zaddm(&r, &one, &t);
        zfree(&r);
        zfree(&one);
        r = t;
        r.neg = 1;
        znorm(&r);
    }
    return zresult(&r);
}

/* The numerator, the denominator, the real part or the imaginary part. */
V num_part(V a, int which)
{
    switch (which) {
    case 0: return IS_RATIO(a) ? BOX(a)[1] : IS_INT(a) ? a : MKFIX(0);
    case 1: return IS_RATIO(a) ? BOX(a)[2] : MKFIX(1);
    case 2: return IS_COMPLEX(a) ? BOX(a)[1] : IS_RAT(a) ? a : MKFIX(0);
    default: return IS_COMPLEX(a) ? BOX(a)[2] : MKFIX(0);
    }
}

V num_complex(V a, V b)
{
    N x;
    qtake(&x.re, IS_RAT(a) ? a : MKFIX(0));
    qtake(&x.im, IS_RAT(b) ? b : MKFIX(0));
    return nput(&x);
}

static void zread(Z *z, const unsigned char *s, const unsigned char *e)
{
    const unsigned char *p;
    U v;
    zinit(z, (size_t)(e - s) / 9 + 1);
    while (e > s) {
        for (v = 0, p = e - s > 9 ? e - 9 : s; p < e; p++)
            v = v * 10 + (U)(*p - '0');
        z->d[z->n++] = (V)v;
        e = e - s > 9 ? e - 9 : s;
    }
    znorm(z);
}

static int digits(const unsigned char *s, const unsigned char *e)
{
    if (s == e || *s < '1' || *s > '9')
        return 0;
    for (; s < e; s++)
        if (*s < '0' || *s > '9')
            return 0;
    return 1;
}

/* Reads an integer or a fraction in its one text; NOV if S..E is not
   one.  It allocates, and so may collect. */
V num_read(const unsigned char *s, const unsigned char *e)
{
    const unsigned char *slash = s, *m = s;
    N x;
    Z g;
    int neg = 0;
    if (m < e && *m == '-')
        neg = 1, m++;
    while (slash < e && *slash != '/')
        slash++;
    if (slash == e) {
        if (!(e - m == 1 && *m == '0' && !neg) && !digits(m, e))
            return NOV;
        zread(&x.re.n, m, e);
        zset(&x.re.d, 1);
    } else {
        if (!digits(m, slash) || !digits(slash + 1, e) || (e - slash == 2 && slash[1] == '1'))
            return NOV;
        zread(&x.re.n, m, slash);
        zread(&x.re.d, slash + 1, e);
        zgcd(&x.re.n, &x.re.d, &g);
        if (!zone(&g)) {
            zfree(&g);
            qfree(&x.re);
            return NOV;
        }
        zfree(&g);
    }
    x.re.n.neg = neg;
    qzero(&x.im);
    return nput(&x);
}

static void print_nat(U n, int pad)
{
    char b[24];
    int i = 24;
    do {
        b[--i] = (char)('0' + n % 10);
        n /= 10;
    } while (n > 0 || 24 - i < pad);
    out_put(b + i, (size_t)(24 - i));
}

static void print_int(V v)
{
    size_t i, n;
    if (IS_FIX(v)) {
        long k = FIXVAL(v);
        if (k < 0)
            out_put("-", 1);
        print_nat(k < 0 ? (U)-k : (U)k, 1);
        return;
    }
    n = BSIZE(v);
    if (BTYPE(v) == B_NEG)
        out_put("-", 1);
    print_nat(BOX(v)[n], 1);
    for (i = n - 1; i-- > 0;)
        print_nat(BOX(v)[1 + i], 9);
}

static void print_rat(V v)
{
    if (IS_RATIO(v)) {
        print_int(BOX(v)[1]);
        out_put("/", 1);
        print_int(BOX(v)[2]);
    } else
        print_int(v);
}

void num_print(V v)
{
    if (IS_COMPLEX(v)) {
        out_put("#C(", 3);
        print_rat(BOX(v)[1]);
        out_put(" ", 1);
        print_rat(BOX(v)[2]);
        out_put(")", 1);
    } else
        print_rat(v);
}

/* Whether two boxed numbers are the same number.  The parts of a
   fraction or a complex rational are integers or fractions, which
   equal() compares without going deeper. */
int big_equal(V a, V b)
{
    size_t i, n = BSIZE(a);
    if (BOX(a)[0] != BOX(b)[0])
        return 0;
    if (BTYPE(a) > B_NEG)
        return equal(BOX(a)[1], BOX(b)[1]) && equal(BOX(a)[2], BOX(b)[2]);
    for (i = 1; i <= n; i++)
        if (BOX(a)[i] != BOX(b)[i])
            return 0;
    return 1;
}
