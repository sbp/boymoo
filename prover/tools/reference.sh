#!/bin/sh
# A runner for the prover's run scripts: the reference runner with its prelude
# (the option -j), which computes ash and binary-logxor itself. From the root
# of the repository:
#
#     RUNNER=prover/tools/reference.sh sh prover/SET/run.sh
#
# The prelude acts only for program text that does not define its two
# functions, so the library's program text is given without their two lines:
# build/prover/library-prelude.program, which this script writes when it is
# missing or older than the library's program text.
set -eu
lib=build/export/library.program
less=build/prover/library-prelude.program
if [ ! -s "$less" ] || [ "$lib" -nt "$less" ]; then
    mkdir -p build/prover
    grep -v -e '^(define COMMON-LISP::NIL (COMMON-LISP::ASH ' \
        -e '^(define COMMON-LISP::NIL (ACL2::BINARY-LOGXOR ' "$lib" > "$less.$$"
    mv "$less.$$" "$less"
fi
if [ ! -x build/runner/boymoo-run ]; then
    make -s -f runner/Makefile >&2
fi
for argument do
    shift
    [ "$argument" != "$lib" ] || argument=$less
    set -- "$@" "$argument"
done
exec build/runner/boymoo-run -j "$@"
