# Evaluate canonical terms on the runner, one per input line.
# Run from the repository root with sh prover/t3/run.sh [-v] [BOOK].

. prover/t3/tools/artifacts.sh

stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/t3/run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-}
if [ "$#" -eq 0 ] && [ -f "$t3_work/exported" ]; then
    IFS= read -r book < "$t3_work/exported"
fi
if ! t3_certified "$book" || ! t3_exported "$book"; then
    echo 'prover/t3/run.sh: name a book exported by sh prover/t3/build.sh' >&2
    exit 2
fi

if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner/boymoo-run
    if [ ! -x "$RUNNER" ]; then
        make -s -f runner/Makefile OUT="$t3_work/runner" >&2 || exit 2
        RUNNER=$t3_work/runner/boymoo-run
    fi
fi

library=build/export/library
out=$t3_exports/$book
BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-$t3_work/runner-fast}
export BOYMOO_FAST_CACHE
# An empty stats flag supplies no argument.
exec timeout --foreground -k 15 "$t3_limit" "$RUNNER" $stats -m 2500 \
    -p spec/ground.txt -p "$library.statements" -p "$out.statements" \
    "$library.program" "$out.program"
