# Run one canonical term per input line. Use sh prover/h1/run.sh [-v] [BOOK].
# BOOK defaults to the last exported prefix. RUNNER may name the executable.

. prover/h1/tools/artifacts.sh || exit 2
stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h1/run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-}
if [ "$#" -eq 0 ] && [ -s "$h1_work/exported" ]; then
    book=$(cat "$h1_work/exported") || exit 2
fi
if ! h1_has_book "$book" || ! h1_certified "$book" || ! h1_exported "$book"; then
    echo 'prover/h1/run.sh: name a book exported by sh prover/h1/build.sh' >&2
    exit 2
fi

mkdir -p "$h1_work/tmp" || exit 2
TMPDIR=$PWD/$h1_work/tmp
BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-$h1_work/fast-cache}
export TMPDIR BOYMOO_FAST_CACHE
if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner/boymoo-run
    if [ ! -x "$RUNNER" ]; then
        RUNNER=$h1_work/runner/boymoo-run
        make -s -f runner/Makefile OUT="$h1_work/runner" >&2 || exit 2
    fi
fi

library=build/export/library
output=$h1_exports/$book
set -- -m 2500 -p spec/ground.txt -p "$library.statements" \
    -p "$output.statements" "$library.program" "$output.program"
[ -z "$stats" ] || set -- "$stats" "$@"
exec "$RUNNER" "$@"
