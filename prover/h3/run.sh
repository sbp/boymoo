# Run from the repository root with sh prover/h3/run.sh [-v] [BOOK].
# Reads one term in the format of spec/formats.md per line.

stats=
if [ "${1-}" = -v ]; then
    stats=-v
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h3/run.sh [-v] [BOOK]' >&2
    exit 2
fi
work=build/prover/h3
book=${1-$(if [ -r "$work/exported" ]; then cat "$work/exported"; fi)}
last=$(if [ -r "$work/certified" ]; then cat "$work/certified"; fi)
if ! awk -v book="$book" -v last="$last" '
    $0 == book { wanted = NR }
    $0 == last { certified = NR }
    END { exit !(wanted && certified && wanted <= certified) }
' prover/h3/ORDER; then
    echo 'prover/h3/run.sh: run sh prover/h3/build.sh to export a book' >&2
    exit 2
fi

base=build/prover/acl2/h3/$book
out=build/export/books/$base
library=build/export/library
if [ ! -f "$base.cert" ] || [ "$base.cert" -nt "$out.statements" ] ||
   [ "$base.cert" -nt "$out.program" ] || [ "$base.cert" -nt "$out.readback" ] ||
   [ ! -s "$out.statements" ] || [ ! -f "$out.program" ] || [ ! -s "$out.readback" ]; then
    echo "prover/h3/run.sh: run sh prover/h3/build.sh $book to export this book" >&2
    exit 2
fi
if [ -z "${RUNNER-}" ]; then
    RUNNER=build/runner/boymoo-run
    if [ ! -x "$RUNNER" ]; then
        RUNNER=build/prover/h3/runner/boymoo-run
        make -s -f runner/Makefile OUT=build/prover/h3/runner >&2 || exit 2
    fi
fi

BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-$work/fast-cache}
export BOYMOO_FAST_CACHE

# An empty stats flag supplies no argument.
exec "$RUNNER" $stats -m 2500 -p spec/ground.txt -p "$library.statements" \
    -p "$out.statements" "$library.program" "$out.program"
