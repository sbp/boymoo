/* The functions of the prelude on strings and lists, which prelude.c
   computes for both runners (README.md, "The prelude").  Each takes its
   arguments from stk[base] onward, all below sp, and gives its value. */

#ifndef PRELUDE_H
#define PRELUDE_H

#include "run.h"

V pre_length(size_t base);   /* (length x) */
V pre_char(size_t base);     /* (char s n) */
V pre_subseq(size_t base);   /* (subseq seq start end) */

#endif
