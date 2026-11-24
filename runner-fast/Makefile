# The fast runner of Boymoo, for the make of POSIX.1-2001.  Run from the
# root of the repository:
#
#     make -f runner-fast/Makefile
#
# It writes build/runner-fast/boymoo-run-fast.  It compiles heap.c and
# includes run.h from runner/, the reference runner's files, unchanged.
# CC, CFLAGS, LDFLAGS, LIBS and OUT may be given on the command line.
# The C that the fast runner writes when it runs is compiled by cc, with
# the options that jit.c names (FAST_CFLAGS); README.md in this directory
# says what that compiler must support.

.POSIX:

CC = cc
CFLAGS = -std=c99 -O2 -Wall -Wextra
LDFLAGS =
LIBS = -lpthread
OUT = build/runner-fast
SRC = runner-fast/sys.c runner/heap.c runner-fast/num.c runner-fast/data.c \
      runner-fast/eval.c runner-fast/gen.c runner-fast/jit.c runner-fast/native.c
HDR = runner/run.h runner-fast/fast.h runner-fast/fastrt.h

all: $(OUT)/boymoo-run-fast

$(OUT)/boymoo-run-fast: $(SRC) $(HDR)
	mkdir -p $(OUT)
	$(CC) $(CFLAGS) -Irunner-fast -Irunner $(LDFLAGS) -o $(OUT)/boymoo-run-fast $(SRC) $(LIBS)

clean:
	rm -f $(OUT)/boymoo-run-fast
