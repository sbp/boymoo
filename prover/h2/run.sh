# From the repository root, use sh prover/h2/run.sh [-v] [BOOK].
# Reads one canonical term per line. BOOK defaults to the last exported prefix.

. prover/h2/tools/artifacts.sh || exit 2
stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h2/run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-$(cat "$h2_work/exported" 2>/dev/null)}
if grep -Fxq -- "$book" "$h2_order" && h2_certified "$book" && h2_exported "$book"; then
    out=$h2_exports/$book
else
    echo 'prover/h2/run.sh: select a book exported by sh prover/h2/build.sh' >&2
    exit 2
fi
library=build/export/library
mkdir -p "$h2_work/tmp" || exit 2
TMPDIR=$PWD/$h2_work/tmp
BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-$h2_work/open-cache}
export TMPDIR BOYMOO_FAST_CACHE
if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner/boymoo-run
    if [ ! -x "$RUNNER" ]; then
        RUNNER=$h2_work/runner/boymoo-run
        make -s -f runner/Makefile OUT="$h2_work/runner" >&2 || exit 2
    fi
fi
# An empty stats flag supplies no argument.
exec "$RUNNER" $stats -m 2500 -p spec/ground.txt -p "$library.statements" \
    -p "$out.statements" "$library.program" "$out.program"
