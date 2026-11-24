#!/bin/sh
# From the repository root, run sh prover/l1/run.sh [-v] [BOOK].
# Standard input supplies one canonical term per line. RUNNER selects the executable.

. prover/l1/tools/artifacts.sh || exit 2
stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/l1/run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-$(cat "$l1_work/exported" 2>/dev/null)}
if ! l1_certified "$book" || ! l1_exported "$book"; then
    echo 'prover/l1/run.sh: name a book exported by sh prover/l1/build.sh' >&2
    exit 2
fi
mkdir -p "$l1_work/compile-tmp" || exit 2
TMPDIR=$(cd "$l1_work/compile-tmp" && pwd -P) || exit 2
BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-$l1_work/fast-cache}
export TMPDIR BOYMOO_FAST_CACHE
if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner-fast/boymoo-run-fast
    if [ ! -x "$RUNNER" ]; then
        RUNNER=$l1_work/runner-fast/boymoo-run-fast
        make -s -f runner-fast/Makefile OUT="$l1_work/runner-fast" >&2 || exit 2
    fi
fi

library=build/export/library
out=$l1_exports/$book
set -- -m 2500 -p spec/ground.txt -p "$library.statements" \
    -p "$out.statements" "$library.program" "$out.program"
if [ -n "$stats" ]; then
    set -- "$stats" "$@"
fi
exec "$RUNNER" "$@"
