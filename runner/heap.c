/* Memory: the heap of conses and boxes, its collector, the value stack
   and the table of constants.

   Every datum that is not immediate lives in one of two spaces: the
   space of conses, two words each, and the space of boxes.  Allocation
   takes the next free words.  When a space is full the collector copies
   every datum reachable from the roots (the value stack and the table
   of constants) into fresh spaces, by the method of Cheney: it copies
   the roots, then scans what it has copied, copying what that refers
   to, so that it needs no stack of its own however deep the data.  A
   datum it has moved leaves behind a forwarding word.  After a
   collection each space is made large enough that at least half of it
   is free.

   A caller that will allocate first calls need() with the number of
   conses and words it will take.  need() may collect, which moves data,
   so a caller reads the data it works on from the stack only after
   need() returns; the allocations that follow cannot collect.

   Every block of memory that the runner holds for long is counted
   against mem_limit, so that exhaustion of memory ends in a clean stop
   and never in a failure of the system. */

#include <stdlib.h>
#include <string.h>
#include "run.h"

V *cells, *words, *stk, *consts;
size_t cell_top, cell_cap, word_top, word_cap, sp, stk_cap, nconsts;
static size_t consts_cap;
size_t mem_limit, mem_used, mem_peak;
unsigned long gc_count;

#define MAXSPACE ((size_t)1 << 29)   /* so that an index fits in a datum */

/* Changes the size of the block P from OLD bytes to N, counting it. */
void *xalloc(void *p, size_t old, size_t n)
{
    void *q;
    if (n == 0) {
        free(p);
        mem_used -= old;
        return NULL;
    }
    if (n > old && n - old > mem_limit - mem_used)
        stop(S_MEMORY, "memory exhausted: the limit set by -m is reached", NOV);
    q = realloc(p, n);
    if (q == NULL)
        stop(S_MEMORY, "memory exhausted: the system refused more", NOV);
    mem_used = mem_used - old + n;
    if (mem_used > mem_peak)
        mem_peak = mem_used;
    return q;
}

static size_t bytes(size_t n, size_t size)
{
    if (n > (size_t)-1 / size)
        stop(S_MEMORY, "memory exhausted: a size is too large", NOV);
    return n * size;
}

void heap_init(void)
{
    cell_cap = word_cap = (size_t)1 << 16;
    cells = xalloc(NULL, 0, bytes(2 * cell_cap, sizeof(V)));
    words = xalloc(NULL, 0, bytes(word_cap, sizeof(V)));
    stk_reserve(1024);
}

/* The spaces a collection copies into, and how much of each is used. */
static V *to_cells, *to_words;
static size_t to_cell_top, to_word_top;

static V forward(V v)
{
    size_t i, n;
    V *h;
    if (IS_CONS(v)) {
        i = (size_t)v >> 2;
        if (cells[2 * i] == NOV)
            return cells[2 * i + 1];
        n = to_cell_top++;
        to_cells[2 * n] = cells[2 * i];
        to_cells[2 * n + 1] = cells[2 * i + 1];
        cells[2 * i] = NOV;
        cells[2 * i + 1] = MKCONS(n);
        return MKCONS(n);
    }
    if (IS_BOX(v)) {
        h = BOX(v);
        if ((h[0] & 7) == B_FWD)
            return h[1];
        n = (size_t)(h[0] >> 3) + 1;
        memcpy(to_words + to_word_top, h, n * sizeof(V));
        h[0] = B_FWD;
        h[1] = MKBOX(to_word_top);
        to_word_top += n;
        return h[1];
    }
    return v;
}

static size_t grown(size_t cap, size_t used)
{
    while (used > cap / 2) {
        if (cap >= MAXSPACE)
            stop(S_MEMORY, "memory exhausted: the heap is at its largest", NOV);
        cap *= 2;
    }
    return cap;
}

static void collect(size_t ncons, size_t nwords)
{
    size_t i, cs = 0, ws = 0, cc, wc;
    to_cells = xalloc(NULL, 0, bytes(2 * cell_cap, sizeof(V)));
    to_words = xalloc(NULL, 0, bytes(word_cap, sizeof(V)));
    to_cell_top = to_word_top = 0;
    for (i = 0; i < sp; i++)
        stk[i] = forward(stk[i]);
    for (i = 0; i < nconsts; i++)
        consts[i] = forward(consts[i]);
    while (cs < 2 * to_cell_top || ws < to_word_top) {
        for (; cs < 2 * to_cell_top; cs++)
            to_cells[cs] = forward(to_cells[cs]);
        while (ws < to_word_top) {
            V h = to_words[ws];
            if ((h & 7) == B_RATIO || (h & 7) == B_COMPLEX) {
                to_words[ws + 1] = forward(to_words[ws + 1]);
                to_words[ws + 2] = forward(to_words[ws + 2]);
            }
            ws += (size_t)(h >> 3) + 1;
        }
    }
    xalloc(cells, bytes(2 * cell_cap, sizeof(V)), 0);
    xalloc(words, bytes(word_cap, sizeof(V)), 0);
    cells = to_cells;
    words = to_words;
    cell_top = to_cell_top;
    word_top = to_word_top;
    if (ncons > MAXSPACE || nwords > MAXSPACE)
        stop(S_MEMORY, "memory exhausted: a datum is too large", NOV);
    cc = grown(cell_cap, cell_top + ncons);
    wc = grown(word_cap, word_top + nwords);
    if (cc > cell_cap)
        cells = xalloc(cells, 2 * cell_cap * sizeof(V), bytes(2 * cc, sizeof(V)));
    if (wc > word_cap)
        words = xalloc(words, word_cap * sizeof(V), bytes(wc, sizeof(V)));
    cell_cap = cc;
    word_cap = wc;
    gc_count++;
}

void need(size_t ncons, size_t nwords)
{
    if (ncons > cell_cap - cell_top || nwords > word_cap - word_top)
        collect(ncons, nwords);
}

V mkcons(V a, V d)
{
    size_t i = cell_top++;
    cells[2 * i] = a;
    cells[2 * i + 1] = d;
    return MKCONS(i);
}

V mkbox(int type, size_t n)
{
    size_t o = word_top;
    words[o] = (V)(((unsigned long)n << 3) | (unsigned long)type);
    word_top += n + 1;
    return MKBOX(o);
}

void stk_reserve(size_t n)
{
    size_t cap = stk_cap ? stk_cap : 1024;
    if (n <= stk_cap - sp)
        return;
    while (n > cap - sp) {
        if (cap > ((size_t)-1 / sizeof(V)) / 2)
            stop(S_MEMORY, "memory exhausted: the stack is too deep", NOV);
        cap *= 2;
    }
    stk = xalloc(stk, stk_cap * sizeof(V), cap * sizeof(V));
    stk_cap = cap;
}

void push(V v)
{
    stk_reserve(1);
    stk[sp++] = v;
}

size_t add_const(V v)
{
    if (nconsts == consts_cap) {
        size_t cap = consts_cap ? 2 * consts_cap : 1024;
        consts = xalloc(consts, consts_cap * sizeof(V), bytes(cap, sizeof(V)));
        consts_cap = cap;
    }
    consts[nconsts] = v;
    return nconsts++;
}
