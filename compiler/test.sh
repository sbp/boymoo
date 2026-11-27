#!/bin/sh
# Compares the executables that two compilers write from the same inputs.
# From the root of the repository:
#
#     sh compiler/test.sh [-q] [--books EXPORT] [--prover INPUT EXPORT] [NEW [REFERENCE]]
#
# NEW is the many-pass compiler, build/compiler/compiler-2 by default
# (sh compiler/bootstrap.sh writes it); REFERENCE is the single-pass
# compiler, build/compiler/single/compiler-2 by default. Each input is
# compiled by both; the compilers must agree on whether they write an
# executable, and the two executables must give the same standard output,
# standard error and exit status on each standard input. The inputs:
#
# - the single-pass compiler's own input,
#   build/compiler/single/compiler.input, given to itself;
# - the compiled checker, build/compiler/checker-test/checker.input, on
#   spec/example and on every case of checker/cases/ whose verdict is
#   recorded, whose verdict must also match the record (left out with -q);
# - the program of compiler/test-numbers.sh, on an empty input;
# - compiler/test-symbols.txt, on the five inputs of compiler/test-symbols.sh;
# - the programs of compiler/test-front.sh, on the input "correct";
# - with --books, the compiled checker on every book of export/books.txt
#   that EXPORT/books holds, with EXPORT/library.statements as its library
#   and proofs that skip every obligation, as compiler/test-checker.sh
#   checks the books;
# - with --prover, the compiled prover, whose input INPUT is written as
#   compiler/build-prover.sh writes it, on spec/example, on lines 7, 19,
#   39, 57 and 1492 of EXPORT/library.statements (each with the lines
#   before it as the library, and the measures of
#   build/termination/library.measures as aids when that file exists), and
#   on the first 12 books of export/books.txt that EXPORT/books holds and
#   the books of prover/driver/expected.tsv, each with its aids. Each run of
#   the prover is stopped after 300 seconds.
#
# The work directory is build/compiler/test, or the directory that
# COMPILER_TEST_WORK names; two runs at once need different ones.
#
# It prints one line for each difference and a summary, and exits with
# status 1 if there is a difference. It needs the inputs that
# sh compiler/single/bootstrap.sh and sh compiler/build-checker.sh write.
set -eu
export LC_ALL=C

quick=0
books=
prover=
prover_export=
while [ "$#" -gt 0 ]; do
    case $1 in
        -q) quick=1; shift ;;
        --books) [ "$#" -ge 2 ] || exit 2; books=$2; shift 2 ;;
        --prover) [ "$#" -ge 3 ] || exit 2; prover=$2; prover_export=$3; shift 3 ;;
        *) break ;;
    esac
done
new=${1:-build/compiler/compiler-2}
ref=${2:-build/compiler/single/compiler-2}
work=${COMPILER_TEST_WORK:-build/compiler/test}
rm -rf "$work"
mkdir -p "$work"
. compiler/frame.sh

compared=0
differences=0

differ() {
    printf 'DIFFERENT: %s\n' "$1"
    differences=$((differences + 1))
}

# compile_pair NAME INPUT: compiles INPUT with both compilers into
# $work/NAME.ref and $work/NAME.new. Its status is 0 when both wrote an
# executable, 1 when both refused the input, and 2 when they disagree.
compile_pair() {
    rs=0
    "$ref" < "$2" > "$work/$1.ref" 2> "$work/$1.ref.cerr" || rs=$?
    ns=0
    "$new" < "$2" > "$work/$1.new" 2> "$work/$1.new.cerr" || ns=$?
    compared=$((compared + 1))
    if [ "$rs" -ne "$ns" ] || ! cmp -s "$work/$1.ref.cerr" "$work/$1.new.cerr"; then
        differ "$1: the compilers gave status $rs and $ns"
        return 2
    fi
    if [ "$rs" -ne 0 ]; then return 1; fi
    chmod +x "$work/$1.ref" "$work/$1.new"
    return 0
}

# run_pair NAME CASE STDIN: runs both executables of NAME on the file STDIN.
run_pair() {
    rs=0
    "$work/$1.ref" < "$3" > "$work/run.ref.out" 2> "$work/run.ref.err" || rs=$?
    ns=0
    "$work/$1.new" < "$3" > "$work/run.new.out" 2> "$work/run.new.err" || ns=$?
    compared=$((compared + 1))
    if [ "$rs" -ne "$ns" ]; then
        differ "$1 on $2: status $rs and $ns"
    elif ! cmp -s "$work/run.ref.out" "$work/run.new.out"; then
        differ "$1 on $2: standard output"
    elif ! cmp -s "$work/run.ref.err" "$work/run.new.err"; then
        differ "$1 on $2: standard error"
    fi
}

# 1. The single-pass compiler compiling itself.
if compile_pair compiler build/compiler/single/compiler.input; then
    run_pair compiler compiler.input build/compiler/single/compiler.input
fi

# 2. The compiled checker.
if [ "$quick" -eq 0 ] && compile_pair checker build/compiler/checker-test/checker.input; then
    : > "$work/empty"
    checker_case() {
        {
            frame_field spec/ground.txt
            for part in library statements proofs library-proofs; do
                if [ -f "$1/$part.txt" ]; then frame_field "$1/$part.txt"
                else frame_field "$work/empty"; fi
            done
        } > "$work/frame"
        run_pair checker "$1" "$work/frame"
        if ! printf '%s\n' "$2" | cmp -s - "$work/run.new.out"; then
            differ "checker on $1: verdict is not the recorded $2"
        fi
    }
    checker_case spec/example accepted
    for verdict in checker/cases/*/verdict.txt; do
        IFS= read -r expected < "$verdict" || :
        checker_case "${verdict%/verdict.txt}" "$expected"
    done
fi

# 3. The numeric primitives and the prelude, as compiler/test-numbers.sh
# writes them.
dir=$work/numbers
mkdir -p "$dir"
compiler=build/compiler/single
eval "$(sed -n '/^cat > "\$dir\/program"/,/^printf .(entry BOYMOO-COMPILER::NUMBER-TEST)/p' \
    compiler/test-numbers.sh)"
: > "$work/empty"
if compile_pair numbers "$dir/input"; then
    run_pair numbers empty "$work/empty"
fi

# 4. Symbols, as compiler/test-symbols.sh runs them.
{
    awk '/^\((package|hidden-package) /' spec/ground.txt
    cat compiler/test-symbols.txt
    printf '(entry BOYMOO-SYMBOL-TEST::MAIN)\n'
} > "$work/symbols.input"
if compile_pair symbols "$work/symbols.input"; then
    awk 'BEGIN {
        printf "I0000000a0000001@"
        for (i = 0; i < 3998; i++) printf "%08d", i
    }' > "$work/stdin"
    run_pair symbols intern "$work/stdin"
    for c in P W H S; do
        printf '%s' "$c" > "$work/stdin"
        run_pair symbols "$c" "$work/stdin"
    done
fi

# 5. The programs of compiler/test-front.sh.
front() {
    name=$1
    {
        awk '/^\((package|hidden-package) /' spec/ground.txt
        printf '%s' "$2"
        cat "$work/front.program"
        printf '(entry ACL2::MAIN)\n'
    } > "$work/$name.input"
    if compile_pair "$name" "$work/$name.input"; then
        printf correct > "$work/stdin"
        run_pair "$name" correct "$work/stdin"
    fi
}
main() {
    printf '(define COMMON-LISP::NIL (ACL2::MAIN %s %s))\n' "$1" "$2" > "$work/front.program"
}
main '(COMMON-LISP::QUOTE)' '(COMMON-LISP::CAR (COMMON-LISP::CONS COMMON-LISP::QUOTE (COMMON-LISP::QUOTE "tail")))'
front quote-formal ''
main '(ACL2::X)' '(ACL2::SYMBOL-PACKAGE-NAME (COMMON-LISP::QUOTE EXAMPLE::X))'
front package-repeat '(hidden-package "EXAMPLE" (COMMON-LISP::CAR))
(package "EXAMPLE" (COMMON-LISP::CAR))
(package "EXAMPLE" (COMMON-LISP::CAR))
'
: > "$work/front.program"
front undefined-entry '(constrain ((ACL2::MAIN 1)) COMMON-LISP::NIL)
'
main '(ACL2::X)' '(COMMON-LISP::QUOTE ACL2::CAR)'
front imported-spelling ''
main '(ACL2::X)' '(COMMON-LISP::QUOTE "a\61")'
front printable-escape ''
main '(ACL2::X)' '((COMMON-LISP::LAMBDA (ACL2::Y ACL2::Y) ACL2::Y) ACL2::X (COMMON-LISP::QUOTE "second"))'
front duplicate-lambda-formal ''
main '(ACL2::&)' 'ACL2::&'
front ampersand-formal ''
printf '(attach ACL2::SELECT COMMON-LISP::IF)\n(define COMMON-LISP::NIL (ACL2::MAIN (ACL2::X) (ACL2::SELECT ACL2::X ACL2::X ACL2::X)))\n' > "$work/front.program"
front attachment-to-if ''
main '(ACL2::X)' '(COMMON-LISP::IF (COMMON-LISP::CONSP (COMMON-LISP::QUOTE (0 5 -7 -4611686018427387904 4611686018427387904 1/2 -7/3 1/18446744073709551616 #C(0 -1/2) #C(-7/3 1/18446744073709551616)))) ACL2::X (COMMON-LISP::QUOTE "missing numbers"))'
front canonical-numbers ''
for number in 2/4 4/2 1/1 0/5 -0 +5 007 1/0 1/-2 '#C(1 0)' '#C(2/4 1)'; do
    main '(ACL2::X)' "(COMMON-LISP::QUOTE $number)"
    front number-text ''
done

# 6. The books, as compiler/test-checker.sh checks them.
if [ -n "$books" ] && [ -s "$work/checker.new" ]; then
    eval "$(sed -n '/^write_skips() {/,/^}/p' compiler/test-checker.sh)"
    : > "$work/empty"
    book_runs=0
    awk '{ sub(/#.*/, ""); sub(/^[[:space:]]+/, ""); sub(/[[:space:]]+$/, ""); if (length) print }' \
        export/books.txt > "$work/books.txt"
    while IFS= read -r name; do
        statements=$books/books/$name.statements
        [ -f "$statements" ] || continue
        write_skips "$books/library.statements" "$statements" > "$work/book.proofs"
        {
            frame_field spec/ground.txt
            frame_field "$books/library.statements"
            frame_field "$statements"
            frame_field "$work/book.proofs"
            frame_field "$work/empty"
        } > "$work/frame"
        run_pair checker "$name" "$work/frame"
        book_runs=$((book_runs + 1))
    done < "$work/books.txt"
    rm -f "$work/frame"
    printf 'Books checked by both checkers: %d.\n' "$book_runs"
fi

# 7. The compiled prover.
prover_case() {
    # prover_case NAME LIBRARY STATEMENTS AIDS
    {
        printf '\000\000\000\000'
        frame_field "$2"
        frame_field "$3"
        frame_field "$4"
        printf '\000\000\000\000'
        printf '\000\000\000\000'
    } > "$work/frame"
    # The time of macOS, found on the PATH, gives the elapsed time and,
    # with -l, the peak of resident memory.
    rs=0
    env time -l timeout 300 "$work/prover.ref" < "$work/frame" > "$work/run.ref.out" \
        2> "$work/run.ref.err" || rs=$?
    ns=0
    env time -l timeout 300 "$work/prover.new" < "$work/frame" > "$work/run.new.out" \
        2> "$work/run.new.err" || ns=$?
    compared=$((compared + 1))
    awk -v name="$1" -v bytes="$(wc -c < "$work/run.new.out")" '
        / real / { t[FILENAME] = $1 }
        /maximum resident set size/ { m[FILENAME] = $1 }
        END { printf "prover on %s: %d bytes; reference %s s, %d bytes resident; new %s s, %d bytes resident\n",
              name, bytes, t[ARGV[1]], m[ARGV[1]], t[ARGV[2]], m[ARGV[2]] }' \
        "$work/run.ref.err" "$work/run.new.err"
    if [ "$rs" -ne "$ns" ]; then
        differ "prover on $1: status $rs and $ns"
    elif ! cmp -s "$work/run.ref.out" "$work/run.new.out"; then
        differ "prover on $1: standard output"
    fi
}
if [ -n "$prover" ] && compile_pair prover "$prover"; then
    : > "$work/empty"
    prover_case spec/example "$work/empty" spec/example/statements.txt "$work/empty"
    aids=$work/empty
    if [ -f build/termination/library.measures ]; then
        awk '{ if ($0 !~ / "(declared|default)"\)$/) sub(/\)$/, " \"default\")")
               print }' build/termination/library.measures > "$work/library.aids"
        aids=$work/library.aids
    fi
    for number in 7 19 39 57 1492; do
        : > "$work/prefix"
        awk -v number="$number" -v prefix="$work/prefix" '
            NR < number { print > prefix }
            NR == number { print; exit }' "$prover_export/library.statements" > "$work/statement"
        prover_case "library line $number" "$work/prefix" "$work/statement" "$aids"
    done
    {
        awk '{ sub(/#.*/, ""); sub(/^[[:space:]]+/, ""); sub(/[[:space:]]+$/, ""); if (length) print }' \
            export/books.txt |
            while IFS= read -r name; do
                if [ -f "$prover_export/books/$name.statements" ]; then printf '%s\n' "$name"; fi
            done | head -n 12
        awk -F '\t' 'NR > 1 && $1 != "spec/example" && $1 !~ /^library line / { print $1 }' \
            prover/driver/expected.tsv
    } > "$work/prover-books.txt"
    while IFS= read -r name; do
        aids=$prover_export/books/$name.aids
        [ -f "$aids" ] || aids=$work/empty
        prover_case "$name" "$prover_export/library.statements" \
            "$prover_export/books/$name.statements" "$aids"
    done < "$work/prover-books.txt"
    rm -f "$work/prover.ref" "$work/prover.new" "$work/frame" "$work/prefix"
fi

printf 'Compared %d compilations and runs of %s with %s; %d differed.\n' \
    "$compared" "$new" "$ref" "$differences"
[ "$differences" -eq 0 ]
