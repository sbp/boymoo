#!/bin/sh
# Builds the many-pass compiler and bootstraps it from the reference
# runner. From the root of the repository:
#
#     sh compiler/bootstrap.sh
#
# compiler/build.sh certifies and exports the books into build/compiler;
# the input build/compiler/compiler.input is the compiler's program text
# with the entry BOYMOO-COMPILER::COMPILE-TEXT. The reference runner,
# through compiler/compile.sh with a limit of 1,024 megabytes, runs the
# compiler on that input and writes build/compiler/compiler-1; compiler-1
# compiles the same input to compiler-2. The script prints the time of
# each step and compares compiler-1 with compiler-2, which must be the same
# byte for byte.
#
# With REF naming another compiled compiler, such as the single-pass
# compiler build/compiler/single/compiler-2 that sh
# compiler/single/bootstrap.sh writes, REF also compiles the input to
# build/compiler/ref-1, ref-1 compiles it to build/compiler/ref-2, and
# ref-2 must be compiler-2 byte for byte.
#
# Each executable is written under a new name and then renamed, so that a
# copy still running from an earlier bootstrap is not changed under it.
set -eu

dir=build/compiler
ref=${REF-}
if [ -n "$ref" ] && [ ! -x "$ref" ]; then
    echo "compiler/bootstrap.sh: REF names no executable: $ref" >&2
    exit 2
fi
if [ ! -x build/runner/boymoo-run ]; then
    echo 'compiler/bootstrap.sh requires build/runner/boymoo-run' >&2
    exit 2
fi

# The books of the compiler in order, as compiler/build.sh lists them; a
# book that is not yet written is left out.
books=
for b in a64 read index data sha256 macos linux runtime qir rt-qir resolve \
    simplify lower expand opt abi isel rega \
    proofs/rega-check emit compile; do
    if [ -f "compiler/$b.lisp" ]; then
        books="$books $b"
    fi
done
# shellcheck disable=SC2086
sh compiler/build.sh -d "$dir" -x $books

input=$dir/compiler.input
{
    awk '/^\((package|hidden-package) /' spec/ground.txt "$dir/compiler.statements"
    cat "$dir/ground.program" "$dir/library.statements" "$dir/compiler.program"
    printf '(entry BOYMOO-COMPILER::COMPILE-TEXT)\n'
} > "$input"

# Writes the output of a step to $dir/NAME through a new name.
place() {
    chmod +x "$dir/$1.tmp"
    mv "$dir/$1.tmp" "$dir/$1"
}

echo 'Reference runner compiling the many-pass compiler:' >&2
time -p sh compiler/compile.sh -v -m 1024 "$input" > "$dir/compiler-1.tmp"
place compiler-1

echo 'compiler-1 compiling the same input:' >&2
time -p "$dir/compiler-1" < "$input" > "$dir/compiler-2.tmp"
place compiler-2

if ! cmp "$dir/compiler-1" "$dir/compiler-2"; then
    exit 1
fi
echo 'The two compiler executables are byte-for-byte identical.'

if [ -n "$ref" ]; then
    echo "$ref compiling the many-pass compiler:" >&2
    time -p "$ref" < "$input" > "$dir/ref-1.tmp"
    place ref-1
    echo 'ref-1 compiling the same input:' >&2
    time -p "$dir/ref-1" < "$input" > "$dir/ref-2.tmp"
    place ref-2
    if cmp "$dir/ref-2" "$dir/compiler-2"; then
        echo "The compiler compiled by $ref writes compiler-2 again, byte for byte."
    else
        exit 1
    fi
fi
