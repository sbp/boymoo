/* Native forms of functions of the program text.  Each entry of the
   table below names a function, the number of its arguments, the
   fingerprint its definition must have, and a C function that computes
   it.  The native form is used only when the program text defines the
   function, and every function its code can reach, by exactly the lines
   whose fingerprint is recorded: a hash of those lines, in the order a
   walk of the code first meets them (fingerprint() below).  It answers
   only on the arguments on which its answer is plain, and on any other
   it runs the definition.  BOYMOO_FAST_NATIVE=0 turns the table off.

   A native function that makes a datum first sets sp, the top of the
   value stack, to the end of its own arguments.  The collector takes
   every word below sp as in use, and the frames of the callers are below
   the arguments, so that nothing a caller holds is lost when memory is
   collected inside the native function. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "fast.h"

/* The hash of the lines that define K and everything its code reaches,
   in the order a walk of the code first meets them. */
static void fingerprint(long k, char hex[33])
{
    long *todo = malloc(nfns * sizeof(long));
    char *seen = calloc(nfns, 1);
    const unsigned char **lines = malloc(nfns * sizeof(*lines));
    size_t nt = 0, nl = 0, i, j, len = 0;
    char *text;
    todo[nt++] = k;
    seen[k] = 1;
    for (i = 0; i < nt; i++) {
        long f = todo[i];
        const Code *c;
        size_t pc;
        if (!try_build(f)) {
            lines[nl++] = (const unsigned char *)"(unbuilt)\n";
            continue;
        }
        for (j = 0; j < nl && lines[j] != fns[f].line; j++)
            ;
        if (j == nl)
            lines[nl++] = fns[f].line;
        c = &fns[f].code;
        for (pc = 0; pc < c->n; pc += c->op[pc] == O_RET ? 1 : 2)
            if ((c->op[pc] == O_CALL || c->op[pc] == O_TCALL) && !seen[c->op[pc + 1]]) {
                seen[c->op[pc + 1]] = 1;
                todo[nt++] = c->op[pc + 1];
            }
    }
    for (i = 0; i < nl; i++)
        len += (size_t)(strchr((const char *)lines[i], '\n') - (const char *)lines[i]) + 1;
    text = malloc(len + 1);
    for (len = 0, i = 0; i < nl; i++) {
        size_t m = (size_t)(strchr((const char *)lines[i], '\n') - (const char *)lines[i]) + 1;
        memcpy(text + len, lines[i], m);
        len += m;
    }
    hash128_text(text, len, hex);
    free(text);
    free(todo);
    free(seen);
    free(lines);
}

/* The library's functions on strings.  ACL2 defines them through the
   list of a string's characters, so that each call costs the length of
   the string; here a string's length and its bytes are at hand.  Each
   answers natively only for the arguments on which the answer is plain
   (a string, and indices within it), and runs the definition otherwise. */

static NatFn length_orig, char_orig, subseq_orig, append_orig, less_orig;

static V string_of(V a, size_t from, size_t n, V b, size_t m, int *ok)
{
    unsigned char *buf = malloc(n + m + 1);
    size_t i;
    V r;
    *ok = buf != NULL;
    if (buf == NULL)
        return NIL;
    for (i = 0; i < n; i++)
        buf[i] = (unsigned char)STRBYTE(a, from + i);
    for (i = 0; i < m; i++)
        buf[n + i] = (unsigned char)STRBYTE(b, i);
    r = mkstring(buf, n + m);
    free(buf);
    return r;
}

/* (length x): the number of characters of a string. */
static V nat_length(size_t fp, long k)
{
    V a = stk[fp];
    if (IS_STRING(a) && STRLEN(a) <= (size_t)FIXMAX)
        return MKFIX((long)STRLEN(a));
    return length_orig(fp, k);
}

/* (char s n): the character at index n of a string, for 0 <= n < its length. */
static V nat_char(size_t fp, long k)
{
    V s = stk[fp], n = stk[fp + 1];
    if (IS_STRING(s) && IS_FIX(n) && FIXVAL(n) >= 0 && (size_t)FIXVAL(n) < STRLEN(s))
        return MKCHAR(STRBYTE(s, (size_t)FIXVAL(n)));
    return char_orig(fp, k);
}

/* (subseq s start end): the characters of a string from start up to end,
   for 0 <= start <= end <= its length, end being its length when nil. */
static V nat_subseq(size_t fp, long k)
{
    V s = stk[fp], a = stk[fp + 1], e = stk[fp + 2];
    sp = fp + 3;
    if (IS_STRING(s) && IS_FIX(a) && (e == NIL || IS_FIX(e)) && STRLEN(s) <= (size_t)FIXMAX) {
        long len = (long)STRLEN(s), start = FIXVAL(a), end = e == NIL ? len : FIXVAL(e);
        if (0 <= start && start <= end && end <= len) {
            int ok;
            V r = string_of(s, (size_t)start, (size_t)(end - start), s, 0, &ok);
            if (ok)
                return r;
        }
    }
    return subseq_orig(fp, k);
}

/* (string-append s1 s2): the characters of one string and then of another. */
static V nat_string_append(size_t fp, long k)
{
    V a = stk[fp], b = stk[fp + 1];
    sp = fp + 2;
    if (IS_STRING(a) && IS_STRING(b)) {
        int ok;
        V r = string_of(a, 0, STRLEN(a), b, STRLEN(b), &ok);
        if (ok)
            return r;
    }
    return append_orig(fp, k);
}

/* (string< s1 s2), which ACL2 defines on the lists of the characters of
   the two strings: for two strings, the index of the first place at which
   s1 has the character of the smaller code, or ends when s2 does not, and
   nil when there is no such place. */
static V nat_string_less(size_t fp, long k)
{
    V a = stk[fp], b = stk[fp + 1];
    if (IS_STRING(a) && IS_STRING(b) && STRLEN(a) <= (size_t)FIXMAX) {
        size_t n = STRLEN(a), m = STRLEN(b), i;
        for (i = 0; i < n && i < m; i++) {
            unsigned x = STRBYTE(a, i), y = STRBYTE(b, i);
            if (x != y)
                return x < y ? MKFIX((long)i) : NIL;
        }
        return i < m ? MKFIX((long)i) : NIL;
    }
    return less_orig(fp, k);
}

/* (nonnegative-integer-quotient i j), which ACL2 defines by taking j from
   i until less than j is left, a recursion as deep as the quotient: for
   integers i >= 0 and j > 0, the quotient rounded down, by division. */
static NatFn quotient_orig;

static V nat_quotient(size_t fp, long k)
{
    V q = (sp = fp + 2, num_quotient(stk[fp], stk[fp + 1]));
    return q != NOV ? q : quotient_orig(fp, k);
}

/* (binary-logand i j), (binary-logior i j), (binary-logxor i j) and
   (binary-logeqv i j), which ACL2 defines one bit at a time through floor:
   for two integers below 2^127 in magnitude, the machine's operation on
   numbers of 128 bits. */
static NatFn logand_orig, logior_orig, logxor_orig, logeqv_orig;

static V nat_logand(size_t fp, long k)
{
    V r = (sp = fp + 2, num_bits(stk[fp], stk[fp + 1], 0));
    return r != NOV ? r : logand_orig(fp, k);
}

static V nat_logior(size_t fp, long k)
{
    V r = (sp = fp + 2, num_bits(stk[fp], stk[fp + 1], 1));
    return r != NOV ? r : logior_orig(fp, k);
}

static V nat_logxor(size_t fp, long k)
{
    V r = (sp = fp + 2, num_bits(stk[fp], stk[fp + 1], 2));
    return r != NOV ? r : logxor_orig(fp, k);
}

static V nat_logeqv(size_t fp, long k)
{
    V r = (sp = fp + 2, num_bits(stk[fp], stk[fp + 1], 3));
    return r != NOV ? r : logeqv_orig(fp, k);
}

/* (ash i c), which ACL2 defines as the floor of i times 2^c, with 2^c
   made by one multiplication for each bit of the shift: for integers i
   and c with i and the result below 2^127 in magnitude, the machine's
   shift of a number of 128 bits. */
static NatFn ash_orig;

static V nat_ash(size_t fp, long k)
{
    V r = (sp = fp + 2, num_shift(stk[fp], stk[fp + 1]));
    return r != NOV ? r : ash_orig(fp, k);
}

/* The functions computed natively: the name, the number of arguments,
   the fingerprint its definition must have, and the native function. */
static const struct native {
    const char *name;
    long arity;
    const char *print;
    NatFn fn;
    NatFn *orig;
} natives[] = {
    {"COMMON-LISP::LENGTH", 1, "632dc9c397cbb009240d46cf8e2ab594", nat_length, &length_orig},
    {"COMMON-LISP::CHAR", 2, "a0554e87125b22c19dc46ac38aa64e4a", nat_char, &char_orig},
    {"COMMON-LISP::SUBSEQ", 3, "1221e857a158a5c30bb8a0efeb59eb2a", nat_subseq, &subseq_orig},
    {"ACL2::STRING-APPEND", 2, "44eec3995eec702248f747c6d482accf", nat_string_append, &append_orig},
    {"ACL2::NONNEGATIVE-INTEGER-QUOTIENT", 2, "cfb4342f75aff8574f436865d8877d71", nat_quotient, &quotient_orig},
    {"ACL2::BINARY-LOGAND", 2, "89f95ced204ab156ca96f8e51114db87", nat_logand, &logand_orig},
    {"ACL2::BINARY-LOGIOR", 2, "c0ac0a436880002e14b242357f3113dc", nat_logior, &logior_orig},
    {"ACL2::BINARY-LOGXOR", 2, "e2dec0d955011f0df5916518bfe3ed80", nat_logxor, &logxor_orig},
    {"ACL2::BINARY-LOGEQV", 2, "8f1604a273296d8d521930d76bcd0cbd", nat_logeqv, &logeqv_orig},
    {"COMMON-LISP::STRING<", 2, "a74f29ac7bf90202d803bc986070ccd5", nat_string_less, &less_orig},
    {"COMMON-LISP::ASH", 2, "78faf3eae3110cd72f08e499a84c408e", nat_ash, &ash_orig},
};

#define NNATIVES (sizeof natives / sizeof natives[0])
static long native_k[NNATIVES];
static int native_ready;

/* Find the functions of the table in the program, before any C is written. */
void native_prepare(long (*find)(const unsigned char *, size_t))
{
    size_t i;
    for (i = 0; i < NNATIVES; i++)
        native_k[i] = find((const unsigned char *)natives[i].name, strlen(natives[i].name));
    native_ready = 1;
}

/* Is K a function of the table?  Such a function is never written into
   its callers, so that every call of it goes by the table of entry points. */
int native_named(long k)
{
    size_t i;
    for (i = 0; native_ready && i < NNATIVES; i++)
        if (native_k[i] == k)
            return 1;
    return 0;
}

void native_install(long (*find)(const unsigned char *, size_t), int verbose)
{
    const char *e = getenv("BOYMOO_FAST_NATIVE");
    size_t i;
    if (e != NULL && strcmp(e, "0") == 0)
        return;
    for (i = 0; i < NNATIVES; i++) {
        const struct native *n = &natives[i];
        long k = find((const unsigned char *)n->name, strlen(n->name));
        char fp[33];
        if (k < 0 || fns[k].arity != n->arity)
            continue;
        fingerprint(k, fp);
        if (verbose)
            fprintf(stderr, "boymoo-run-fast: %s: fingerprint %s, expected %s: %s\n", n->name, fp,
                    n->print, strcmp(fp, n->print) == 0 ? "native" : "the definition");
        if (strcmp(fp, n->print) != 0)
            continue;
        *n->orig = natv[k];
        natv[k] = n->fn;
    }
}
