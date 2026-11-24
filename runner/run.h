/* The reference runner of Boymoo: declarations shared by its sources.
   README.md in this directory says what the runner does and how its
   sources divide the work. */

#ifndef RUN_H
#define RUN_H

#include <stddef.h>
#include <stdint.h>

/* A datum is a word of at least 32 bits, of which the runner uses 32.
   Its low bits say what it is:
     ..00   a cons: the rest is its index in the space of conses;
     ..10   a box (a large integer, a fraction, a complex rational or a
            string): the rest is the offset of its header in the space
            of boxes;
     ..01   an integer from -2^29 to 2^29 - 1, held in the rest;
     .011   a character: the rest is its code;
     .111   a symbol: the rest is its index in the table of symbols.
   Every datum has exactly one representation, so two immediate data
   (integers, characters, symbols) are the same object exactly when
   their words are equal. */
typedef uint_least32_t V;

#define IS_CONS(v) (((v) & 3) == 0)
#define IS_BOX(v)  (((v) & 3) == 2)
#define IS_FIX(v)  (((v) & 3) == 1)
#define IS_CHAR(v) (((v) & 7) == 3)
#define IS_SYM(v)  (((v) & 7) == 7)

#define FIXMIN (-536870912L)
#define FIXMAX 536870911L
#define MKFIX(n)  ((V)(((unsigned long)((n) - FIXMIN) << 2) | 1))
#define FIXVAL(v) ((long)((v) >> 2) + FIXMIN)
#define MKCHAR(c) ((V)(((unsigned long)(c) << 3) | 3))
#define CHARCODE(v) ((unsigned)((v) >> 3))
#define MKSYM(i)  ((V)(((unsigned long)(i) << 3) | 7))
#define SYMIDX(v) ((size_t)((v) >> 3))
#define MKCONS(i) ((V)((unsigned long)(i) << 2))
#define MKBOX(o)  ((V)(((unsigned long)(o) << 2) | 2))

#define NIL MKSYM(0)          /* COMMON-LISP::NIL */
#define T   MKSYM(1)          /* COMMON-LISP::T */
#define NOV ((V)0xFFFFFFFFUL) /* no datum; never the index of a symbol */

/* The heap: two spaces, one of conses and one of boxes, each collected
   by copying (heap.c). */
extern V *cells, *words;
extern size_t cell_top, cell_cap, word_top, word_cap;
#define CAR(v) (cells[2 * ((size_t)(v) >> 2)])
#define CDR(v) (cells[2 * ((size_t)(v) >> 2) + 1])

/* A box is a header word, (n << 3) | type, and n words.  A large
   integer holds its magnitude in base 10^9, least significant first;
   a fraction its numerator and denominator; a complex rational its
   real and imaginary parts; a string its length and then its bytes,
   four to a word. */
enum { B_POS = 1, B_NEG, B_RATIO, B_COMPLEX, B_STRING, B_FWD = 7 };
#define BOX(v)   (words + ((size_t)(v) >> 2))
#define BTYPE(v) ((int)(BOX(v)[0] & 7))
#define BSIZE(v) ((size_t)(BOX(v)[0] >> 3))
#define IS_BIG(v)    (IS_BOX(v) && BTYPE(v) <= B_NEG)
#define IS_RATIO(v)  (IS_BOX(v) && BTYPE(v) == B_RATIO)
#define IS_COMPLEX(v) (IS_BOX(v) && BTYPE(v) == B_COMPLEX)
#define IS_STRING(v) (IS_BOX(v) && BTYPE(v) == B_STRING)
#define IS_INT(v)    (IS_FIX(v) || IS_BIG(v))
#define IS_RAT(v)    (IS_INT(v) || IS_RATIO(v))
#define IS_NUM(v)    (IS_RAT(v) || IS_COMPLEX(v))
#define STRLEN(v)    ((size_t)BOX(v)[1])
#define STRBYTE(v, i) ((unsigned)(BOX(v)[2 + (i) / 4] >> (8 * ((i) % 4))) & 0xFFu)

/* The value stack of the machine (eval.c), whose entries the collector
   updates; every datum that must survive an allocation lives there or
   in the table of constants. */
extern V *stk;
extern size_t sp, stk_cap;
extern V *consts;
extern size_t nconsts;

/* heap.c */
extern size_t mem_limit, mem_used, mem_peak;
extern unsigned long gc_count;
void *xalloc(void *p, size_t old, size_t n);
void heap_init(void);
void need(size_t ncons, size_t nwords);
V mkcons(V a, V d);
V mkbox(int type, size_t n);
void push(V v);
void stk_reserve(size_t n);
size_t add_const(V v);

/* num.c */
V num_add(V a, V b);
V num_mul(V a, V b);
V num_neg(V a);
V num_inv(V a);
int num_less(V a, V b);
V num_ash(V a, V b);        /* the prelude */
V num_logxor(V a, V b);
V num_part(V a, int which); /* 0 numerator, 1 denominator, 2 real, 3 imaginary */
V num_complex(V a, V b);
V num_read(const unsigned char *s, const unsigned char *e); /* NOV if not canonical */
void num_print(V v);
int big_equal(V a, V b);

/* data.c: symbols, packages, text */
typedef struct {
    unsigned char *name;
    size_t len;
    int pkg;     /* the package whose symbol it is */
    int prim;    /* the number of the primitive it names, or -1 */
    long fn;     /* its function record, or -1 */
} Sym;
typedef struct {
    unsigned char *name;
    size_t len;
    int declared, hidden;
    size_t imports;    /* index of its list of imports among the constants */
} Pkg;
extern Sym *syms;
extern size_t nsyms;
extern Pkg *pkgs;
extern V S_QUOTE, S_LAMBDA, S_IF, S_LIST, S_RETURN_LAST, S_MBE1_RAW;
void data_init(void);
long pkg_find(const unsigned char *name, size_t len);
V intern_in(int pkg, const unsigned char *name, size_t len);
void declare_package(int hidden);   /* name and imports on the stack */
V mkstring(const unsigned char *s, size_t len);
const unsigned char *read_datum(const unsigned char *p, const unsigned char *e);
const unsigned char *skip_datum(const unsigned char *p, const unsigned char *e);
int equal(V a, V b);
void print_datum(V v);
extern char *out;      /* text written by print_datum and num_print */
extern size_t out_len;
void out_put(const char *s, size_t n);

/* eval.c */
enum { P_ACL2_NUMBERP, P_BAD_ATOM_LE, P_TIMES, P_PLUS, P_MINUS, P_RECIP,
       P_LESS, P_CAR, P_CDR, P_CHAR_CODE, P_CHARACTERP, P_CODE_CHAR,
       P_COMPLEX, P_COMPLEX_RATIONALP, P_COERCE, P_CONS, P_CONSP,
       P_DENOMINATOR, P_EQUAL, P_IF, P_IMAGPART, P_INTEGERP, P_INTERN,
       P_NUMERATOR, P_PKG_IMPORTS, P_PKG_WITNESS, P_RATIONALP, P_REALPART,
       P_STRINGP, P_SYMBOL_NAME, P_SYMBOL_PACKAGE_NAME, P_SYMBOLP, NPRIMS };
extern const char *const prim_pkg[NPRIMS], *const prim_name[NPRIMS];
extern int prelude;                 /* whether the runner starts with the prelude (-j) */
void index_define(const unsigned char *p, const unsigned char *e, int file, long line);
void set_attach(void);              /* two symbols on the stack */
void build_all(void);
V run_term(void);                   /* the term on the stack */
extern unsigned long defs_built;

/* sys.c: every contact with the system */
enum { S_VALUE = 0, S_NO_VALUE = 1, S_INPUT = 2, S_MEMORY = 3 };
void stop(int status, const char *msg, V v);
void set_place(int file, long line);

#endif
