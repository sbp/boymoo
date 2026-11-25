#!/bin/sh
# The checker of spec/logic.md, compiled by the compiler of
# compiler/README.md and run as an executable.  From the root of the
# repository:
#
#     sh compiler/check.sh LIBRARY STATEMENTS PROOFS [LIBRARY-PROOFS]
#
# The arguments are those of checker/check.sh: each is a file, which may be
# empty, and the fourth input defaults to empty. The output is the verdict
# line of spec/formats.md, section 9, alone, with no line explaining a
# rejection. The exit status is 0 when the checker gave a verdict, and
# otherwise that of the step that failed. A file of 2^32 bytes or more
# cannot be given to the checker: it then writes `invalid checker input
# frame`.
#
# It needs the compiled checker, build/compiler/checker, which
# sh compiler/build-checker.sh writes. It writes the bytes of
# spec/ground.txt and of the four inputs as the five fields of the
# checker's input (compiler/frame.sh) and gives them to the checker on its
# standard input.

if [ $# -ne 3 ] && [ $# -ne 4 ]; then
    echo "usage: sh compiler/check.sh LIBRARY STATEMENTS PROOFS [LIBRARY-PROOFS]" >&2
    exit 2
fi
for f do
    if [ ! -f "$f" ]; then
        echo "compiler/check.sh: no file $f" >&2
        exit 2
    fi
done
if [ ! -x build/compiler/checker ]; then
    echo "compiler/check.sh: run sh compiler/build-checker.sh first" >&2
    exit 2
fi

export LC_ALL=C
. compiler/frame.sh
{
    frame_field spec/ground.txt
    frame_field "$1"
    frame_field "$2"
    frame_field "$3"
    if [ $# -eq 4 ]; then frame_field "$4"; else printf '\000\000\000\000'; fi
} | build/compiler/checker
