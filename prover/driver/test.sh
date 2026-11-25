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

{
    IFS= read -r header
    printf '%s\n' "$header" > "$scratch/results.tsv"
    while IFS="$tab" read -r input proved obligations verdict; do
        case_inputs "$input"
        sh prover/driver/prove.sh --sets "$sets" "$library" "$statements" "$aids" > "$scratch/proofs" ||
            fail "could not prove $input"
        check_core || fail "ACL2 Core checker failed on $input"
        NODE_OPTIONS="${NODE_OPTIONS:+$NODE_OPTIONS }--max-old-space-size=704" \
            sh checker-js/check.sh "$library" "$statements" "$scratch/proofs" node > "$scratch/second" ||
            fail "second checker failed on $input"
        if ! observed=$(observed_result); then
            cat "$scratch/core" "$scratch/second" >&2
            fail "could not confirm the verdict for $input"
        fi
        [ "$record" -eq 1 ] || [ "$observed" = "$proved$tab$obligations$tab$verdict" ] ||
            fail "$input gave $observed"
        printf '%s\t%s\n' "$input" "$observed" >> "$scratch/results.tsv"
    done
} < "$expected"
cat "$scratch/results.tsv"
if [ "$record" -eq 0 ]; then
    if [ "$expected" = prover/driver/expected.tsv ]; then
        mv "$scratch/results.tsv" "$work/test.tsv"
        printf '%s\n' 'All driver tests passed.'
    else
        printf 'All tests of %s passed.\n' "$expected"
    fi
fi
