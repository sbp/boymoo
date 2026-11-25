#!/bin/sh
set -eu

sh compiler/build.sh
dir=build/compiler
input=$dir/compiler.input
{
    awk '/^\((package|hidden-package) /' spec/ground.txt "$dir/compiler.statements"
    cat "$dir/ground.program" "$dir/library.statements" "$dir/compiler.program"
    printf '(entry BOYMOO-COMPILER::COMPILE-TEXT)\n'
} > "$input"

echo 'Reference runner compiling the compiler:' >&2
time -p sh compiler/compile.sh -v "$input" > "$dir/compiler-1" || exit $?
chmod +x "$dir/compiler-1"

echo 'Compiled compiler compiling the same input:' >&2
time -p "$dir/compiler-1" < "$input" > "$dir/compiler-2" || exit $?
chmod +x "$dir/compiler-2"

if cmp "$dir/compiler-1" "$dir/compiler-2"; then
    echo 'The two compiler executables are byte-for-byte identical.'
else
    exit 1
fi
