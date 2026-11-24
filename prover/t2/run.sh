# Evaluate one canonical term per input line on the runner.
# From the repository root, run sh prover/t2/run.sh [-v] [BOOK] after the build.
# BOOK defaults to the last exported book. The -v flag prints statistics.

. prover/t2/tools/artifacts.sh

stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/t2/run.sh [-v] [BOOK]' >&2
    exit 2
fi

book=${1-}
if [ "$#" -eq 0 ] && [ -s "$t2_work/exported" ]; then
    IFS= read -r book < "$t2_work/exported"
fi
if ! t2_certified "$book" snapshot || ! t2_exported "$book"; then
    echo 'prover/t2/run.sh: name a book exported by sh prover/t2/build.sh' >&2
    exit 2
fi
t2_use_work_tmp || exit 2
if [ -z "${RUNNER-}" ]; then
    if [ -x build/runner-fast/boymoo-run-fast ]; then
        RUNNER=build/runner-fast/boymoo-run-fast
    elif [ -x build/runner/boymoo-run ]; then
        RUNNER=build/runner/boymoo-run
    else
        RUNNER=$t2_work/runner/boymoo-run
        make -s -f runner/Makefile OUT="$t2_work/runner" >&2 || exit 2
    fi
fi

BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-$t2_work/fast-cache}
export BOYMOO_FAST_CACHE

library=build/export/library
exec timeout --foreground -k 15 "${T2_CALL_SECONDS:-1800}" \
    "$RUNNER" $stats -m 2500 -p spec/ground.txt -p "$library.statements" \
    -p "$t2_output.statements" "$library.program" "$t2_output.program"
