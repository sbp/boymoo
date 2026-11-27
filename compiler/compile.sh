#!/bin/sh
# Compiles an input with the many-pass compiler on the reference runner,
# with its prelude, and writes the executable to standard output. From the
# root of the repository, after sh compiler/build.sh:
#
#     sh compiler/compile.sh [-v] [-m MEGABYTES] INPUT > EXECUTABLE
#
# With -v the runner also prints its time and peak of memory. With -m the
# runner holds at most MEGABYTES megabytes (runner/README.md); without it,
# the runner's own default applies.
set -eu
export LC_ALL=C

verbose=
limit=
while [ "$#" -gt 1 ]; do
    case $1 in
        -v) verbose=-v; shift ;;
        -m) limit=$2; shift 2 ;;
        *) break ;;
    esac
done
if [ "$#" -ne 1 ] || [ ! -r "$1" ]; then
    echo 'Usage: sh compiler/compile.sh [-v] [-m MEGABYTES] INPUT' >&2
    exit 2
fi

mkdir -p build/compiler
dir=$(mktemp -d build/compiler/compile.XXXXXX)
trap 'rm -rf "$dir"' EXIT
trap 'exit 1' HUP INT TERM

. checker/quote.sh
{
    printf '(BOYMOO-COMPILER::COMPILE-TEXT '
    quote "$1"
    printf ')\n'
} > "$dir/input.term"

build/runner/boymoo-run ${verbose:+"$verbose"} -j ${limit:+-m "$limit"} -p spec/ground.txt \
    -p build/compiler/compiler.statements build/compiler/ground.program \
    build/compiler/library.statements build/compiler/compiler.program \
    < "$dir/input.term" > "$dir/output.string"

. compiler/decode.sh
decode_string "$dir/output.string"
