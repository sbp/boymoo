# Run one canonical term per input line. Use sh prover/t4/run.sh [-v] [BOOK].
# BOOK defaults to the last exported T4 prefix. RUNNER selects the executable.

. prover/t4/tools/artifacts.sh || exit 2
stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/t4/run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-}
if [ "$#" -eq 0 ] && [ -f "$t4_work/exported" ]; then
    book=$(cat "$t4_work/exported")
fi
if ! grep -Fxq -- "$book" "$t4_order" || ! t4_readback_ok "$t4_exports/$book"; then
    echo 'prover/t4/run.sh: name a book exported by sh prover/t4/build.sh' >&2
    exit 2
fi
if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner/boymoo-run
    if [ ! -x "$RUNNER" ]; then
        RUNNER=$t4_work/runner/boymoo-run
        make -s -f runner/Makefile OUT="$t4_work/runner" >&2 || exit 2
    fi
fi
: "${BOYMOO_FAST_CACHE:=$t4_work/open-cache}"
export BOYMOO_FAST_CACHE

library=build/export/library
out=$t4_exports/$book
set -- -m 2500 -p spec/ground.txt -p "$library.statements" \
    -p "$out.statements" "$library.program" "$out.program"
if [ -n "$stats" ]; then
    set -- "$stats" "$@"
fi
exec "$RUNNER" "$@"
