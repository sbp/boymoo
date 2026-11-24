# Evaluate one canonical term per input line on the runner.
# From the repository root, run sh prover/b1/run.sh [-v] [BOOK].
# BOOK defaults to the last export. RUNNER may name the runner executable.

. prover/b1/tools/artifacts.sh

stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/b1/run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-}
if [ "$#" -eq 0 ] && [ -f "$b1_work/exported" ]; then
    read -r book < "$b1_work/exported"
fi
if ! b1_certified "$book" || ! b1_exported "$book"; then
    echo 'prover/b1/run.sh: name a book exported by sh prover/b1/build.sh' >&2
    exit 2
fi
b1_tempdir || exit 2
: "${BOYMOO_FAST_CACHE:=$b1_work/fast-cache}"
export BOYMOO_FAST_CACHE

if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner/boymoo-run
    if [ ! -x "$RUNNER" ]; then
        RUNNER=$b1_work/runner/boymoo-run
        make -s -f runner/Makefile OUT="$b1_work/runner" >&2 || exit 2
    fi
fi

output=$b1_exports/$book
library=build/export/library
exec "$RUNNER" $stats -m 2500 -p spec/ground.txt -p "$library.statements" \
    -p "$output.statements" "$library.program" "$output.program"
