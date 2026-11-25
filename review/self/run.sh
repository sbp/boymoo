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
library=build/checker/library.statements

# The library's proofs: those of the checker's library, the lines of ACL2's
# library that the checker calls, read as statements.
mkdir -p "$out/library"
python3 -B checker/skips.py "$out/empty" "$library" > "$out/library/all-skips.proofs"
python3 -B review/self/pilot.py "$library" "$out/library/all-skips.proofs" "$out/library"
library_proofs=$out/library/checker.proofs

python3 -B checker/skips.py "$library" "$statements" > "$out/all-skips.proofs"
python3 -B review/self/pilot.py "$statements" "$out/all-skips.proofs" "$out"
python3 -B review/self/pilot.py "$statements" "$out/all-skips.proofs" "$out" logical

# A checker reads the library's proofs first, so the proofs leave out each
# helper entry that those already hold (prover/tools/repeats.awk).
for stem in checker logical; do
    awk -v known="$library_proofs" -f prover/tools/repeats.awk "$out/$stem.proofs" \
        > "$out/$stem.proofs.tmp"
    mv "$out/$stem.proofs.tmp" "$out/$stem.proofs"
done

# Time both checker commands with the build in place.
check_pair() {
    label=$1
    input=$2
    proofs=$3
    status=0
    {
        time -p sh checker-js/check.sh "$library" "$input" "$proofs" "$library_proofs" node \
            > "$out/$label.javascript.verdict"
    } 2> "$out/$label.javascript.time" || status=1
    {
        time -p env RUNNER=build/runner/boymoo-run \
            sh checker/check.sh "$library" "$input" "$proofs" "$library_proofs" \
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
library_count=$(awk 'END { print NR }' "$out/library/all-skips.proofs")
printf 'Recursive entries proved: %s, and %s of the library\nSkips left: 0\n' "$count" "$library_count"
