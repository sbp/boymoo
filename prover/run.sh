# Runs one canonical term per input line.
# From the repository root, run sh prover/run.sh [-v] [BOOK] after prover/build.sh.
# BOOK defaults to the last exported prefix. The values use spec/formats.md.

stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-$(if [ -r build/prover/exported ]; then cat build/prover/exported; fi)}
if ! grep -Fxq -- "$book" prover/ORDER; then
    echo 'prover/run.sh: name a book exported by sh prover/build.sh' >&2
    exit 2
fi
dir=build/prover/acl2
out=build/export/books/$dir/$book
library=build/export/library
if [ ! -f "$dir/$book.cert" ] || [ "$dir/$book.cert" -nt "$out.program" ] ||
   [ ! -s "$out.statements" ] || [ ! -f "$out.program" ] || [ ! -s "$out.readback" ]; then
    echo "prover/run.sh: run sh prover/build.sh $book to export this book" >&2
    exit 2
fi
if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner/boymoo-run
    if [ ! -x "$RUNNER" ]; then
        RUNNER=build/prover/runner/boymoo-run
        make -s -f runner/Makefile OUT=build/prover/runner >&2 || exit 2
    fi
fi

# An empty stats flag supplies no argument.
exec "$RUNNER" $stats -m 2200 -p spec/ground.txt -p "$library.statements" \
    -p "$out.statements" "$library.program" "$out.program"
