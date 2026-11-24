/* Declarations shared by the interpreter (eval.c), the translator to C
   (gen.c) and the driver of the C compiler (jit.c). */

#ifndef FAST_H
#define FAST_H

#include "fastrt.h"

enum { O_CONST, O_VAR, O_PRIM, O_CALL, O_TCALL, O_JNIL, O_JMP, O_RET,
       O_ENTER, O_LEAVE, O_REBIND };

typedef struct {
    long *op;
    size_t n, maxstack;
} Code;

typedef struct {
    V sym;
    long arity;                       /* -1 if not known */
    const unsigned char *line, *end;  /* its define line, or NULL */
    int file, pos, built;
    long lineno, attach;              /* attach: a function, or -1 */
    Code code;
} Fn;

extern Fn *fns;
extern size_t nfns;
extern const int prim_arity[NPRIMS];
long fn_lookup(V s);                  /* its function number, or -1 */
int try_build(long k);                /* 1 if built; never stops */
extern char *trap_active;             /* set: stop() longjmps to stop_trap */
#include <setjmp.h>
extern jmp_buf stop_trap;

/* native.c */
void native_install(long (*find)(const unsigned char *, size_t), int verbose);
void native_prepare(long (*find)(const unsigned char *, size_t));
int native_named(long k);
void hash128_text(const char *s, size_t n, char hex[33]);

/* jit.c */
void jit_prepare(const unsigned char *in, size_t n, int verbose);

/* gen.c: the C of the unit of the define line whose functions are
   UNIT[0..N), into the buffer out (out_len). */
void gen_unit(const long *unit, size_t n, const char *uname);
void code_counts(long k, size_t *nk, size_t *nc);
extern char *gen_out;
extern size_t gen_len;
int const_inline(V v);               /* a constant written into the C */

#endif
