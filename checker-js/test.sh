#!/bin/sh
set -eu
export LC_ALL=C

if [ "$#" -gt 1 ]; then
    printf '%s\n' 'Usage: sh checker-js/test.sh [ENGINE]' >&2
    exit 2
fi
engine=${1:-${BOYMOO_ENGINE:-}}
mkdir -p build
scratch=$(mktemp -d build/checker-js-test.XXXXXX)
trap 'rm -rf "$scratch"' 0
trap 'exit 2' HUP INT TERM
empty="$scratch/empty"
: > "$empty"
failed=0

run() {
    directory=$1
    label=$2
    expected=$3
    library="$directory/library.txt"
    statements="$directory/statements.txt"
    proofs="$directory/proofs.txt"
    library_proofs="$directory/library-proofs.txt"
    [ -f "$library" ] || library=$empty
    [ -f "$statements" ] || statements=$empty
    [ -f "$proofs" ] || proofs=$empty
    [ -f "$library_proofs" ] || library_proofs=$empty
    actual=
    if sh checker-js/check.sh "$library" "$statements" "$proofs" "$library_proofs" "$engine" > "$scratch/verdict"; then
        IFS= read -r actual < "$scratch/verdict" || actual=
    fi
    if [ "$actual" = "$expected" ]; then
        printf '%s\t%s\n' "$label" "$actual"
    else
        printf '%s\tFAIL, expected [%s], got [%s]\n' "$label" "$expected" "$actual"
        failed=1
    fi
}

run spec/example spec/example accepted
for directory in checker-js/cases/*; do
    [ -d "$directory" ] || continue
    expected=$(cat "$directory/verdict.txt")
    run "$directory" "${directory##*/}" "$expected"
done
if [ "$failed" -ne 0 ]; then
    printf '%s\n' 'some checker tests failed'
    exit 1
fi
printf '%s\n' 'all checker tests passed'
