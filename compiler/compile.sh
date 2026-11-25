#!/bin/sh
set -eu
export LC_ALL=C

if [ "${1-}" = -v ]; then
    verbose=-v
    shift
else
    verbose=
fi
if [ "$#" -ne 1 ] || [ ! -r "$1" ]; then
    echo 'Usage: sh compiler/compile.sh [-v] INPUT' >&2
    exit 2
fi

dir=$(mktemp -d build/compiler/compile.XXXXXX)
trap 'rm -rf "$dir"' EXIT
trap 'exit 1' HUP INT TERM

. checker/quote.sh
{
    printf '(BOYMOO-COMPILER::COMPILE-TEXT '
    quote "$1"
    printf ')\n'
} > "$dir/input.term"

build/runner/boymoo-run ${verbose:+"$verbose"} -j -p spec/ground.txt \
    -p build/compiler/compiler.statements build/compiler/ground.program \
    build/compiler/library.statements build/compiler/compiler.program \
    < "$dir/input.term" > "$dir/output.string"

. compiler/decode.sh
decode_string "$dir/output.string"
