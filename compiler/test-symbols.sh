#!/bin/sh
set -eu
export LC_ALL=C

if [ "$#" -gt 1 ]; then
    printf 'Usage: sh compiler/test-symbols.sh [COMPILER]\n' >&2
    exit 2
fi

mkdir -p build/compiler
dir=$(mktemp -d build/compiler/symbols.XXXXXX)
trap 'rm -rf "$dir"' EXIT
trap 'exit 1' HUP INT TERM
source=compiler/test-symbols.txt
awk '/^\((package|hidden-package) /' "$source" > "$dir/packages"
awk '/^\(define /' "$source" > "$dir/program"
{
    awk '/^\((package|hidden-package) /' spec/ground.txt
    cat "$source"
    printf '(entry BOYMOO-SYMBOL-TEST::MAIN)\n'
} > "$dir/input"
if [ "$#" -eq 1 ]; then
    "$1" < "$dir/input" > "$dir/executable"
else
    sh compiler/single/build.sh
    sh compiler/single/compile.sh "$dir/input" > "$dir/executable"
fi
chmod +x "$dir/executable"
. checker/quote.sh

check() {
    name=$1
    expected_status=$2
    expected=$3
    {
        printf '(BOYMOO-SYMBOL-TEST::MAIN '
        quote "$dir/stdin"
        printf ')\n'
    } > "$dir/term"
    reference_status=0
    build/runner/boymoo-run -j -p spec/ground.txt -p "$dir/packages" \
        "$dir/program" < "$dir/term" > "$dir/reference.out" 2> "$dir/reference.err" ||
        reference_status=$?
    native_status=0
    "$dir/executable" < "$dir/stdin" > "$dir/native.out" 2> "$dir/native.err" ||
        native_status=$?
    if [ "$reference_status" -ne "$expected_status" ] ||
       [ "$native_status" -ne "$expected_status" ]; then
        printf '%s: reference status %s, compiled status %s, expected %s.\n' \
            "$name" "$reference_status" "$native_status" "$expected_status" >&2
        cat "$dir/reference.err" "$dir/native.err" >&2
        exit 1
    fi
    if [ "$expected_status" -eq 0 ]; then
        test ! -s "$dir/reference.err"
        test ! -s "$dir/native.err"
        printf '%s' "$expected" > "$dir/expected"
        cmp "$dir/expected" "$dir/native.out"
        printf '"%s"\n' "$expected" > "$dir/expected"
        cmp "$dir/expected" "$dir/reference.out"
    else
        test ! -s "$dir/reference.out"
        test ! -s "$dir/native.out"
        sed 's/^boymoo-run: standard input, line 1: //' "$dir/reference.err" > "$dir/stop"
        cmp "$dir/stop" "$dir/native.err"
        grep -Fq "no value: $expected" "$dir/native.err"
    fi
    printf 'Both programs agree on %s (status %s).\n' "$name" "$expected_status"
}

# The first two names have the same hash.
awk 'BEGIN {
    printf "I0000000a0000001@"
    for (i = 0; i < 3998; i++) printf "%08d", i
}' > "$dir/stdin"
check 're-interning 4,000 names' 0 'symbols agree'
printf 'P' > "$dir/stdin"
check 'imports and witnesses' 0 'packages agree'
printf 'W' > "$dir/stdin"
check 'the witness query for a hidden package' 1 'pkg-witness of a string'
printf 'H' > "$dir/stdin"
check 'the import query for a hidden package' 1 'pkg-imports of a string'
printf 'S' > "$dir/stdin"
check 'the package name of a hidden symbol' 1 'symbol-package-name of a symbol'
