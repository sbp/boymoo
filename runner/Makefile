# The reference runner of Boymoo, for the make of POSIX.1-2001.
# Run from the root of the repository:
#
#     make -f runner/Makefile
#
# It writes build/runner/boymoo-run.  CC, CFLAGS, LDFLAGS and OUT may be
# given on the command line, for example
#
#     make -f runner/Makefile CC=clang CFLAGS='-std=c99 -pedantic-errors -Wall -Wextra -Werror -Wvla -O2'

.POSIX:

CC = c99
CFLAGS = -O 1
LDFLAGS =
OUT = build/runner
SRC = runner/sys.c runner/heap.c runner/num.c runner/data.c runner/eval.c runner/prelude.c

all: $(OUT)/boymoo-run

$(OUT)/boymoo-run: $(SRC) runner/run.h runner/prelude.h
	mkdir -p $(OUT)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $(OUT)/boymoo-run $(SRC)

clean:
	rm -f $(OUT)/boymoo-run
