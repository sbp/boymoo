# Evaluate one canonical term per input line on the runner.
# Run from the repository root with sh prover/b2/run.sh [-v] [BOOK].
# BOOK defaults to the last export. With -v the runner prints its statistics.

. prover/b2/tools/artifacts.sh

stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/b2/run.sh [-v] [BOOK]' >&2
    exit 2
fi

book=${1-}
if [ "$#" -eq 0 ] && [ -r "$b2_work/exported" ]; then
    book=$(cat "$b2_work/exported")
fi
if [ -z "$book" ] || ! b2_certified "$book" || ! b2_exported "$book"; then
    echo 'prover/b2/run.sh: name a current book exported by sh prover/b2/build.sh' >&2
    exit 2
fi
if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner/boymoo-run
    if [ ! -x "$RUNNER" ]; then
        RUNNER=$b2_work/runner/boymoo-run
        make -s -f runner/Makefile OUT="$b2_work/runner" >&2 || exit 2
    fi
fi

b2_run $stats
