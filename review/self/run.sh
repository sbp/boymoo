#!/bin/sh
# Run from the repository root.
set -eu

out=build/self
mkdir -p "$out" build/export
: > "$out/empty"

# The checker build uses the exporter's list of ground definitions.
python3 -B review/self/pilot.py ground-functions > build/export/ground-fns.lsp
sh checker/build.sh
make -s -f runner/Makefile

statements=build/checker/checker.statements
python3 -B checker/skips.py "$out/empty" "$statements" > "$out/all-skips.proofs"
python3 -B review/self/pilot.py "$statements" "$out/all-skips.proofs" "$out"
python3 -B review/self/pilot.py "$statements" "$out/all-skips.proofs" "$out" logical

# Time both checker commands with the build in place.
check_pair() {
    label=$1
    input=$2
    proofs=$3
    status=0
    {
        time -p sh checker-js/check.sh "$out/empty" "$input" "$proofs" node \
            > "$out/$label.javascript.verdict"
    } 2> "$out/$label.javascript.time" || status=1
    {
        time -p env RUNNER=build/runner/boymoo-run \
            sh checker/check.sh "$out/empty" "$input" "$proofs" \
            > "$out/$label.runner.verdict"
    } 2> "$out/$label.runner.time" || status=1

    for checker in javascript runner; do
        printf '%s %s\n' "$label" "$checker"
        cat "$out/$label.$checker.verdict" "$out/$label.$checker.time"
    done
    js=$(sed -n '1p' "$out/$label.javascript.verdict")
    runner=$(sed -n '1p' "$out/$label.runner.verdict")
    if [ "$js" != "$runner" ]; then
        printf '%s\n' 'The checkers gave different verdicts.' >&2
        return 1
    fi
    [ "$status" -eq 0 ] && [ "$js" = accepted ]
}

check_pair source "$statements" "$out/checker.proofs"
check_pair logical "$out/logical.statements" "$out/logical.proofs"
count=$(awk 'END { print NR }' "$out/all-skips.proofs")
printf 'Recursive entries proved: %s\nSkips left: 0\n' "$count"
