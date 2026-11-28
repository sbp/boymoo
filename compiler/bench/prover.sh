set -eu
export LC_ALL=C

if [ "$#" -lt 1 ]; then
    printf 'Usage: sh compiler/bench/prover.sh PROVER-INPUT [EXPORT [BOOK ...]]\n' >&2
    exit 2
fi

prover_input=$1
shift
export_dir=${1-build/export}
if [ "$#" -gt 0 ]; then shift; fi
if [ "$#" -eq 0 ]; then set -- build/choice misc/hidden-defpkg-checks/top; fi
compiler=${COMPILER:-build/compiler/compiler-2}

if [ ! -x "$compiler" ]; then
    printf 'No executable compiler %s.\n' "$compiler" >&2
    exit 2
fi
for path in "$prover_input" "$export_dir/library.statements"; do
    if [ ! -s "$path" ]; then
        printf 'Missing input %s.\n' "$path" >&2
        exit 2
    fi
done
for book do
    for suffix in statements aids; do
        path=$export_dir/books/$book.$suffix
        if [ ! -f "$path" ]; then
            printf 'Missing input %s.\n' "$path" >&2
            exit 2
        fi
    done
done

mkdir -p build/compiler/bench
dir=$(mktemp -d build/compiler/bench/prover.XXXXXX)
printf 'Prover benchmark results are in %s.\n' "$dir" >&2
cleanup() {
    for path in "$dir/prover" "$dir"/book-*.out; do
        if [ -f "$path" ]; then rm "$path"; fi
    done
}
trap cleanup EXIT
trap 'exit 2' HUP INT TERM

: > "$dir/empty"
printf 'benchmark\telapsed_seconds\tpeak_resident_bytes\n' > "$dir/results.tsv"
. compiler/frame.sh

measure() {
    python3 compiler/bench/measure.py "$2" "$3" "${4}.err" > "${4}.measure"
    read -r elapsed peak < "${4}.measure"
    printf '%s\t%s\t%s\n' "$1" "$elapsed" "$peak" >> "$dir/results.tsv"
}

measure compile-prover "$compiler" "$dir/prover" "$dir/compile" < "$prover_input"
test -s "$dir/prover"
chmod +x "$dir/prover"

frame_book() {
    frame_field "$dir/empty" &&
    frame_field "$export_dir/library.statements" &&
    frame_field "$export_dir/books/$1.statements" &&
    frame_field "$export_dir/books/$1.aids" &&
    frame_field "$dir/empty" &&
    frame_field "$dir/empty"
}

run_book() {
    stem=$dir/$2
    (frame_book "$1" && : > "$stem.framed") |
        measure "$1" "$dir/prover" "$stem.out" "$stem"
    test -f "$stem.framed"
    test -s "$stem.out"
    rm "$stem.out"
}

index=0
for book do
    index=$((index + 1))
    run_book "$book" "book-$index"
done
cat "$dir/results.tsv"
