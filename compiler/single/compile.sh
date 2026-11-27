#!/bin/sh
# Compiles an input with the single-pass compiler on the reference runner,
# with its prelude, and writes the executable to standard output. From the
# root of the repository, after sh compiler/single/build.sh:
#
#     sh compiler/single/compile.sh [-v] INPUT > EXECUTABLE
#
# With -v the runner also prints its time and peak of memory.
set -eu
export LC_ALL=C

if [ "${1-}" = -v ]; then
    verbose=-v
    shift
else
    verbose=
fi
if [ "$#" -ne 1 ] || [ ! -r "$1" ]; then
    echo 'Usage: sh compiler/single/compile.sh [-v] INPUT' >&2
    exit 2
fi

dir=$(mktemp -d build/compiler/single/compile.XXXXXX)
trap 'rm -rf "$dir"' EXIT
trap 'exit 1' HUP INT TERM

. checker/quote.sh
{
    printf '(BOYMOO-COMPILER::COMPILE-TEXT '
    quote "$1"
    printf ')\n'
} > "$dir/input.term"

build/runner/boymoo-run ${verbose:+"$verbose"} -j -p spec/ground.txt \
    -p build/compiler/single/compiler.statements build/compiler/single/ground.program \
    build/compiler/single/library.statements build/compiler/single/compiler.program \
    < "$dir/input.term" > "$dir/output.string"

. compiler/decode.sh
decode_string "$dir/output.string"
