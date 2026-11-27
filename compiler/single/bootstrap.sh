#!/bin/sh
# Builds the single-pass compiler with compiler/single/build.sh, writes its
# input, build/compiler/single/compiler.input, has the reference runner
# compile it to build/compiler/single/compiler-1, has compiler-1 compile the
# same input to build/compiler/single/compiler-2, prints the time of each,
# and compares the two byte for byte. From the root of the repository:
#
#     sh compiler/single/bootstrap.sh
set -eu

sh compiler/single/build.sh
dir=build/compiler/single
input=$dir/compiler.input
{
    awk '/^\((package|hidden-package) /' spec/ground.txt "$dir/compiler.statements"
    cat "$dir/ground.program" "$dir/library.statements" "$dir/compiler.program"
    printf '(entry BOYMOO-COMPILER::COMPILE-TEXT)\n'
} > "$input"

echo 'Reference runner compiling the compiler:' >&2
time -p sh compiler/single/compile.sh -v "$input" > "$dir/compiler-1" || exit $?
chmod +x "$dir/compiler-1"

echo 'Compiled compiler compiling the same input:' >&2
time -p "$dir/compiler-1" < "$input" > "$dir/compiler-2" || exit $?
chmod +x "$dir/compiler-2"

if cmp "$dir/compiler-1" "$dir/compiler-2"; then
    echo 'The two compiler executables are byte-for-byte identical.'
else
    exit 1
fi
