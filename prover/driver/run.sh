#!/bin/sh
# Read one canonical term per line from the repository root.
set -eu

if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != -v ]; }; then
    printf '%s\n' 'usage: sh prover/driver/run.sh [-v]' >&2
    exit 2
fi

work=build/prover/driver
book=$work/acl2/driver
out=$work/export/driver
if [ ! -s "$book.cert" ] || [ ! -s "$out.statements" ] ||
   [ ! -s "$out.program" ] || [ ! -s "$out.readback" ] ||
   [ "$book.cert" -nt "$out.readback" ] || [ "$book.cert" -nt "$out.statements" ] ||
   [ "$book.cert" -nt "$out.program" ]; then
    printf '%s\n' 'Run sh prover/driver/build.sh to certify and export the driver.' >&2
    exit 2
fi

if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner-fast/boymoo-run-fast
    if [ ! -x "$RUNNER" ]; then
        RUNNER=$work/runner-fast/boymoo-run-fast
        make -s -f runner-fast/Makefile OUT="$work/runner-fast" >&2
    fi
fi
BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-$work/fastcache}
export BOYMOO_FAST_CACHE
library=build/export/library
exec "$RUNNER" "$@" -m 1800 -p spec/ground.txt -p "$library.statements" \
    -p "$out.statements" "$library.program" "$out.program"
