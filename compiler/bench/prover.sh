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
reference=build/compiler/single/compiler-2
candidate=build/compiler/compiler-2
compiler_input=build/compiler/single/compiler.input

for path in "$prover_input" "$compiler_input" "$export_dir/library.statements"; do
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
    for path in "$dir/compiler" "$dir/reference.prover" \
                "$dir/recompiled.prover" "$dir/candidate.prover" "$dir"/book-*.out; do
        if [ -f "$path" ]; then rm "$path"; fi
    done
}
trap cleanup EXIT
trap 'exit 2' HUP INT TERM

: > "$dir/empty"
printf 'benchmark\tcompiler\telapsed_seconds\tpeak_resident_bytes\n' > "$dir/results.tsv"
. compiler/frame.sh

measure() {
    python3 compiler/bench/measure.py "$3" "$4" "${5}.err" > "${5}.measure"
    read -r elapsed peak < "${5}.measure"
    printf '%s\t%s\t%s\t%s\n' "$1" "$2" "$elapsed" "$peak" >> "$dir/results.tsv"
}

"$candidate" < "$compiler_input" > "$dir/compiler"
test -s "$dir/compiler"
chmod +x "$dir/compiler"
measure compile-prover reference "$reference" "$dir/reference.prover" "$dir/compile.reference" \
    < "$prover_input"
measure compile-prover candidate "$dir/compiler" "$dir/recompiled.prover" "$dir/compile.candidate" \
    < "$prover_input"
test -s "$dir/reference.prover"
cmp "$dir/reference.prover" "$dir/recompiled.prover"
cmp "$dir/compile.reference.err" "$dir/compile.candidate.err"
rm "$dir/compiler" "$dir/recompiled.prover"

python3 compiler/bench/measure.py "$candidate" "$dir/candidate.prover" "$dir/setup.err" \
    < "$prover_input" > "$dir/setup.measure"
test -s "$dir/candidate.prover"
chmod +x "$dir/reference.prover" "$dir/candidate.prover"

frame_book() {
    frame_field "$dir/empty" &&
    frame_field "$export_dir/library.statements" &&
    frame_field "$export_dir/books/$1.statements" &&
    frame_field "$export_dir/books/$1.aids" &&
    frame_field "$dir/empty" &&
    frame_field "$dir/empty"
}

run_book() {
    for side in reference candidate; do
        stem=$dir/$2.$side
        (frame_book "$1" && : > "$stem.framed") |
            measure "$1" "$side" "$dir/$side.prover" "$stem.out" "$stem"
        test -f "$stem.framed"
    done
    cmp "$dir/$2.reference.out" "$dir/$2.candidate.out"
    cmp "$dir/$2.reference.err" "$dir/$2.candidate.err"
    rm "$dir/$2.reference.out" "$dir/$2.candidate.out"
}

index=0
for book do
    index=$((index + 1))
    run_book "$book" "book-$index"
done
cat "$dir/results.tsv"
