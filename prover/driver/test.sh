#!/bin/sh
# Judge the prover's proof files with both checkers.
#
#     sh prover/driver/test.sh [--sets A,B] [--record] [TABLE]
#
# TABLE (prover/driver/expected.tsv if none is named) has a line of headings and
# then a line for each input: the input, the number of its obligations that the
# prover proves, the number of its obligations, and the verdict, with tabs
# between. An input is spec/example, "library line N" (line N of the library's
# statements, with the lines before it as the library) or an exported book.
# For each input the driver, with the sets named by --sets (all eleven if none
# are), writes a proof file; the checker in ACL2 Core and the second checker
# judge it; and the two must give the same verdict, which with the two counts
# must be the table's. With --record nothing is compared with the table: its
# first column is read, and the table that was observed is printed.
set -eu
export LC_ALL=C

work=build/prover/driver
exported=build/export
expected=prover/driver/expected.tsv
sets=T1,H4,H3,B2,T3,B1,T2,T4,L1,H2,H1
record=0
compare=${PROVER_TEST_COMPARE:-0}
seconds=${PROVER_TEST_SECONDS:-240}
compared=0
matched=0
failed=0
tab=$(printf '\t')

fail() {
    printf 'prover/driver/test.sh: %s\n' "$*" >&2
    exit 1
}

usage() {
    printf '%s\n' 'usage: sh prover/driver/test.sh [--sets A,B] [--record] [TABLE]' >&2
    exit 2
}

while [ "$#" -gt 0 ]; do
    case $1 in
        --sets) [ "$#" -ge 2 ] || usage; sets=$2; shift 2 ;;
        --record) record=1; shift ;;
        -*) usage ;;
        *) break ;;
    esac
done
[ "$#" -le 1 ] || usage
[ "$#" -eq 0 ] || expected=$1
[ -f "$expected" ] || fail "no table $expected"
if [ "$compare" = 1 ]; then
    case $seconds in ''|0*|*[!0-9]*) fail 'PROVER_TEST_SECONDS must be a positive integer.' ;; esac
fi

mkdir -p "$work"
scratch=$work/test.$$
mkdir "$scratch"
trap 'rm -rf "$scratch"' 0
trap 'exit 1' HUP INT TERM

. checker/quote.sh
: > "$scratch/empty"
: > "$scratch/library.aids"
# The aids of an input "library line N" are the measures that ACL2 stores for
# the library, which sh review/termination/run.sh writes.
measures=build/termination/library.measures
if grep -q "^library line " "$expected"; then
    [ -f "$measures" ] ||
        fail "no $measures: run sh review/termination/run.sh first"
    awk '{ if ($0 !~ / "(declared|default)"\)$/) sub(/\)$/, " \"default\")")
           print }' "$measures" > "$scratch/library.aids"
fi
quote spec/ground.txt > "$scratch/ground"

case_inputs() {
    case $1 in
        spec/example)
            library=$scratch/empty
            statements=spec/example/statements.txt
            aids=$scratch/empty ;;
        'library line '*)
            number=${1#library line }
            library=$scratch/prefix
            statements=$scratch/statement
            aids=$scratch/library.aids
            : > "$library"
            awk -v number="$number" -v prefix="$library" '
                NR < number { print > prefix }
                NR == number { print; found = 1; exit }
                END { if (!found) exit 1 }' "$exported/library.statements" > "$statements" ||
                fail "library has no line $number" ;;
        *)
            library=$exported/library.statements
            statements=$exported/books/$1.statements
            aids=$exported/books/$1.aids ;;
    esac
}

check_core() {
    quote "$library" > "$scratch/library"
    quote "$statements" > "$scratch/statements"
    {
        printf '(ACL2::LEN (BOYMOO-PROVER::DRIVER-ENTRIES-FROM-ANSWERS '
        cat "$scratch/library"; printf ' '
        cat "$scratch/statements"; printf ' (COMMON-LISP::QUOTE COMMON-LISP::NIL)))\n'
        printf '(BOYMOO::CHECK '
        cat "$scratch/ground"; printf ' '
        cat "$scratch/library"; printf ' '
        cat "$scratch/statements"; printf ' '
        quote "$scratch/proofs"; printf ')\n'
    } > "$scratch/terms"
    sh prover/driver/run.sh < "$scratch/terms" > "$scratch/core"
}

observed_result() {
    awk -F '"' '
        FILENAME == ARGV[1] {
            if (FNR == 1 && $0 ~ /^[0-9]+$/) obligations = $0 + 0
            else if (FNR == 2 && NF == 5 && $1 == "(" && $3 == " " && $5 == ")") verdict = $2
            else bad = 1
            next
        }
        FNR == 1 && $0 == verdict {
            if (verdict == "accepted") skipped = 0
            else if (verdict ~ /^provisional skipped [0-9]+ assumed [0-9]+ given-definitions [0-9]+ given-facts [0-9]+$/) {
                split(verdict, words, " ")
                skipped = words[3] + 0
            } else bad = 1
            if (!bad && obligations != "" && skipped <= obligations) {
                printf "%d\t%d\t%s\n", obligations - skipped, obligations, verdict
                found = 1
            }
        }
        END { if (!found) exit 1 }' "$scratch/core" "$scratch/second"
}

compare_proofs() {
    fast_status=0
    compiled_status=0
    PROVER_DRIVER=fast timeout -k 5 "$seconds" sh prover/driver/prove.sh \
        --sets "$sets" "$library" "$statements" "$aids" > "$scratch/fast" || fast_status=$?
    PROVER_DRIVER=compiled timeout -k 5 "$seconds" sh prover/driver/prove.sh \
        --sets "$sets" "$library" "$statements" "$aids" > "$scratch/proofs" || compiled_status=$?
    compared=$((compared + 1))
    if [ "$fast_status" -eq 0 ] && [ "$compiled_status" -eq 0 ]; then
        if cmp -s "$scratch/fast" "$scratch/proofs"; then
            matched=$((matched + 1))
            return 0
        fi
        printf '%s differs between the drivers.\n' "$input" >&2
        cmp "$scratch/fast" "$scratch/proofs" >&2 || :
    else
        printf '%s gave status %d on the fast runner and %d on the compiled driver.\n' \
            "$input" "$fast_status" "$compiled_status" >&2
    fi
    failed=1
    return "$compiled_status"
}

case_failure() {
    [ "$compare" = 1 ] || fail "$*"
    printf 'prover/driver/test.sh: %s\n' "$*" >&2
    failed=1
}

{
    IFS= read -r header
    printf '%s\n' "$header" > "$scratch/results.tsv"
    while IFS="$tab" read -r input proved obligations verdict; do
        case_inputs "$input"
        if [ "$compare" = 1 ]; then
            compare_proofs || continue
        else
            sh prover/driver/prove.sh --sets "$sets" "$library" "$statements" "$aids" > "$scratch/proofs" ||
                fail "could not prove $input"
        fi
        if ! check_core; then
            case_failure "ACL2 Core checker failed on $input"
            continue
        fi
        if ! NODE_OPTIONS="${NODE_OPTIONS:+$NODE_OPTIONS }--max-old-space-size=704" \
            sh checker-js/check.sh "$library" "$statements" "$scratch/proofs" node > "$scratch/second"; then
            case_failure "second checker failed on $input"
            continue
        fi
        if ! observed=$(observed_result); then
            cat "$scratch/core" "$scratch/second" >&2
            case_failure "could not confirm the verdict for $input"
            continue
        fi
        [ "$record" -eq 1 ] || [ "$observed" = "$proved$tab$obligations$tab$verdict" ] ||
            case_failure "$input gave $observed"
        printf '%s\t%s\n' "$input" "$observed" >> "$scratch/results.tsv"
    done
} < "$expected"
cat "$scratch/results.tsv"
if [ "$compare" = 1 ]; then
    printf '%d of %d proof files matched byte for byte.\n' "$matched" "$compared"
    [ "$failed" -eq 0 ] || exit 1
fi
if [ "$record" -eq 0 ]; then
    if [ "$expected" = prover/driver/expected.tsv ]; then
        [ "$compare" = 1 ] || mv "$scratch/results.tsv" "$work/test.tsv"
        printf '%s\n' 'All driver tests passed.'
    else
        printf 'All tests of %s passed.\n' "$expected"
    fi
fi
