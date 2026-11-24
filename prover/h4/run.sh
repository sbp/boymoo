#!/bin/sh
# Read one canonical term per input line. Use -v for timing and peak memory.
# Run from the repository root. BOOK defaults to the last exported prefix.

stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h4/run.sh [-v] [BOOK]' >&2
    exit 2
fi
. prover/h4/tools/run-book.sh
h4_book "${1-}" exported || exit 2
BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-$h4_work/cache}
export BOYMOO_FAST_CACHE
library=build/export/library
if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner/boymoo-run
    if [ ! -x "$RUNNER" ]; then
        RUNNER=build/prover/h4/runner/boymoo-run
        make -s -f runner/Makefile OUT=build/prover/h4/runner >&2 || exit 2
    fi
fi
if [ -n "$stats" ]; then
    set -- "$stats"
else
    set --
fi
exec "$RUNNER" "$@" -m 2500 -p spec/ground.txt -p "$library.statements" \
    -p "$out.statements" "$library.program" "$out.program"
