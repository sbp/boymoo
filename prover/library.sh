#!/bin/sh
# Prove the statements of the library with the prover, and write the
# library's proofs (spec/formats.md, section 6), the fourth input of a
# checker.  From the root of the repository, after sh prover/build-all.sh
# and sh review/termination/run.sh:
#
#     sh prover/library.sh [-j JOBS] [-p PIECE] [-t SECONDS] [-s SETS] [-a | -f] OUT
#
# The obligations of build/export/library.statements are proved in three
# passes. First in pieces: PIECE (20) consecutive lines that have
# obligations, with the lines between them, given to the driver as the
# statements, and the lines before the piece as the library. Then alone:
# each obligation that its piece left as a skip, or whose piece did not end
# within the time, given to the driver as the one statement, with the lines
# before it as the library. Last, each obligation still unproved is given
# to each set alone, in the order of SETS, until one proves it: a set alone
# holds less memory than the driver trying the sets in turn. By default SETS
# is L1,H2,T1,H4,H3,B2,T3,B1,T2,T4,H1, the driver's order with L1 and H2
# first, the order with which the library has been proved in full
# (PLAN.md, step 6): L1 alone proves the theorems about the warrants of
# loop$ functions, such as APPLY$-UNTIL$, for which the driver runs out of
# memory. Each run of the
# driver has SECONDS (600) and the memory limit of prover/driver/run.sh; JOBS (3) run at a time. The aids
# are the measures that sh review/termination/run.sh writes.
#
# The proofs are joined in the order of the library. A piece is proved with
# the lines before it as given, so it may state again a helper entry that an
# earlier piece stated, under the same name: a define, lemma or choose
# entry whose head line was written before is left out, with its proofs
# and, for a definition, the measure or skip entry that follows it for it.
# An obligation that no run proved keeps its skip entry, and a checker then
# counts it as given. OUT ends up holding the library's proofs, and the
# script prints how many obligations are proved.
#
# What each run of the driver gave is kept under build/prover/library/, and
# a later run of this script runs only the pieces and obligations that were
# not run before; with -a it runs none and only joins what is there, and
# with -f it empties build/prover/library/ first and runs them all, as it
# must after the prover changes.
set -u
export LC_ALL=C

jobs=3
piece=20
seconds=600
sets=L1,H2,T1,H4,H3,B2,T3,B1,T2,T4,H1
assemble_only=0
fresh=0
usage() {
    echo 'usage: sh prover/library.sh [-j JOBS] [-p PIECE] [-t SECONDS] [-s SETS] [-a | -f] OUT' >&2
    exit 2
}
fail() {
    echo "prover/library.sh: $*" >&2
    exit 1
}

library=build/export/library.statements
work=build/prover/library
measures=build/termination/library.measures

# One run of the driver (the script calls itself for each).
if [ "${1-}" = --run ]; then
    kind=$2 first=$3 last=$4 seconds=$5
    unit=$work/$kind/$first
    rm -rf "$unit"
    mkdir -p "$unit" || exit 2
    awk -v a="$first" 'NR < a' "$library" > "$unit/library"
    awk -v a="$first" -v b="$last" 'NR >= a && NR <= b' "$library" > "$unit/statements"
    start=$(date +%s)
    timeout "$seconds" sh prover/driver/prove.sh "$unit/library" "$unit/statements" \
        "$work/aids" > "$unit/proofs" 2> "$unit/errors"
    status=$?
    rm -f "$unit/library" "$unit/statements"
    [ "$status" -eq 0 ] || rm -f "$unit/proofs"
    printf '%s %s %d %d\n' "$first" "$last" "$status" "$(($(date +%s) - start))" > "$unit/status"
    exit 0
fi

# One obligation given to each set alone, until one proves it.
if [ "${1-}" = --alone ]; then
    k=$2 seconds=$3 sets=$4
    unit=$work/alone/$k
    skip=$(awk -F '\t' -v k="$k" '$1 == k { print $2 }' "$work/obligations")
    rm -rf "$unit"
    mkdir -p "$unit" || exit 2
    awk -v a="$k" 'NR < a' "$library" > "$unit/library"
    awk -v a="$k" 'NR == a' "$library" > "$unit/statements"
    for set in $(echo "$sets" | tr , ' '); do
        start=$(date +%s)
        timeout "$seconds" sh prover/driver/prove.sh --sets "$set" "$unit/library" \
            "$unit/statements" "$work/aids" > "$unit/proofs.$set" 2> "$unit/errors.$set"
        status=$?
        printf '%s %d %d\n' "$set" "$status" "$(($(date +%s) - start))" >> "$unit/tried"
        if [ "$status" -eq 0 ] && ! grep -qxF "$skip" "$unit/proofs.$set"; then
            mv "$unit/proofs.$set" "$unit/proofs"
            break
        fi
        rm -f "$unit/proofs.$set"
    done
    rm -f "$unit/library" "$unit/statements"
    echo done > "$unit/status"
    exit 0
fi

while [ "$#" -gt 0 ]; do
    case $1 in
        -j) [ "$#" -ge 2 ] || usage; jobs=$2; shift 2 ;;
        -p) [ "$#" -ge 2 ] || usage; piece=$2; shift 2 ;;
        -t) [ "$#" -ge 2 ] || usage; seconds=$2; shift 2 ;;
        -s) [ "$#" -ge 2 ] || usage; sets=$2; shift 2 ;;
        -a) assemble_only=1; shift ;;
        -f) fresh=1; shift ;;
        -*) usage ;;
        *) break ;;
    esac
done
[ "$#" -eq 1 ] || usage
[ "$assemble_only" -eq 1 ] && [ "$fresh" -eq 1 ] && usage
out=$1
[ -s "$library" ] || fail "no $library: run sh export/run.sh first"
[ -f "$measures" ] || fail "no $measures: run sh review/termination/run.sh first"
[ "$fresh" -eq 0 ] || rm -rf "$work" || exit 2
mkdir -p "$work/piece" "$work/single" "$work/alone" || exit 2

# The aids: the measures, each marked as the driver's test marks them.
awk '{ if ($0 !~ / "(declared|default)"\)$/) sub(/\)$/, " \"default\")")
       print }' "$measures" > "$work/aids"

# Each line of the library with obligations, and its skip entry.
awk '
function first_function(line,    s, depth, i, c) {
    s = substr(line, 9)
    if (substr(s, 1, 1) == "(") {
        depth = 0
        for (i = 1; i <= length(s); i++) {
            c = substr(s, i, 1)
            if (c == "(") depth++
            else if (c == ")") { depth--; if (depth == 0) break }
        }
        s = substr(s, i + 1)
    } else
        sub(/^[^ ]+/, "", s)
    sub(/^ \(/, "", s)
    sub(/ .*$/, "", s)
    return s
}
/^\(theorem / { print NR "\t(skip " $2 ")"; next }
/^\(define / { if ($2 != "COMMON-LISP::NIL") print NR "\t(skip " first_function($0) ")"; next }
/^\(constrain / { if ($0 !~ /\) COMMON-LISP::NIL\)$/) {
    s = $0; sub(/^\(constrain \(\(/, "", s); sub(/ .*$/, "", s); print NR "\t(skip " s ")" } }
' "$library" > "$work/obligations"
total=$(wc -l < "$work/obligations" | tr -d ' ')

# The pieces: the first and last line of each run of PIECE obligations.
awk -F '\t' -v n="$piece" '
    (NR - 1) % n == 0 { if (NR > 1) print first, last; first = $1 }
    { last = $1 }
    END { if (NR) print first, last }' "$work/obligations" > "$work/pieces"

if [ "$assemble_only" -eq 0 ]; then
    # First pass: every piece not already run.
    while read -r first last; do
        [ -f "$work/piece/$first/status" ] || echo "piece $first $last"
    done < "$work/pieces" |
        xargs -P "$jobs" -n 3 sh -c 'sh prover/library.sh --run "$0" "$1" "$2" '"$seconds"
    # Second pass: each obligation of a piece that did not end, or that its
    # piece left as a skip, not already run alone.
    while read -r first last; do
        proofs=$work/piece/$first/proofs
        awk -F '\t' -v a="$first" -v b="$last" -v proofs="$proofs" '
            BEGIN { while ((getline line < proofs) > 0) if (line ~ /^\(skip /) skipped[line] = 1 }
            $1 >= a && $1 <= b && (!(proofs_exist) || ($2 in skipped)) { print $1 }
        ' proofs_exist="$([ -f "$proofs" ] && echo 1 || echo 0)" "$work/obligations"
    done < "$work/pieces" |
        while read -r k; do
            [ -f "$work/single/$k/status" ] || echo "single $k $k"
        done |
        xargs -P "$jobs" -n 3 sh -c 'sh prover/library.sh --run "$0" "$1" "$2" '"$seconds"
    # Third pass: each obligation that neither its piece nor its own run
    # proved, not already given to the sets alone.
    while read -r first last; do
        awk -F '\t' -v a="$first" -v b="$last" -v work="$work" '
            function proved(f, skip,    line, n, found) {
                n = 0; found = 0
                while ((getline line < f) > 0) { n++; if (line == skip) found = 1 }
                close(f)
                return n > 0 && !found
            }
            $1 >= a && $1 <= b {
                piece = work "/piece/" a "/proofs"
                if (proved(piece, $2) || proved(work "/single/" $1 "/proofs", $2)) next
                print $1
            }' "$work/obligations"
    done < "$work/pieces" |
        while read -r k; do
            [ -f "$work/alone/$k/status" ] || echo "$k"
        done |
        xargs -P "$jobs" -n 1 sh -c 'sh prover/library.sh --alone "$0" '"$seconds $sets"
fi

# Join: each piece's proofs with every skip replaced by the proof of that
# obligation alone where there is one; for a piece that did not end, the
# proofs of its obligations alone, or their skips. Then leave out repeats.
while read -r first last; do
    proofs=$work/piece/$first/proofs
    awk -F '\t' -v a="$first" -v b="$last" -v work="$work" -v proofs="$proofs" '
        # Print the proof of obligation K alone, if there is one, and say so.
        function single(k,    f, line, n) {
            f = work "/alone/" k "/proofs"
            if ((getline line < f) <= 0) { close(f); f = work "/single/" k "/proofs" } else { print line; n = 1 }
            while ((getline line < f) > 0) { print line; n++ }
            close(f)
            return n > 0
        }
        $1 >= a && $1 <= b { line_of[$2] = $1; order[++count] = $1; skip_of[$1] = $2 }
        END {
            if ((getline line < proofs) > 0) {
                do {
                    if (!((line in line_of) && single(line_of[line]))) print line
                } while ((getline line < proofs) > 0)
            } else
                for (i = 1; i <= count; i++) {
                    if (!single(order[i])) print skip_of[order[i]]
                }
        }' "$work/obligations"
done < "$work/pieces" |
awk -f prover/tools/repeats.awk > "$out.tmp" || exit 2
mv "$out.tmp" "$out"

skips=$(awk -F '\t' 'NR == FNR { name[$2] = 1; next } ($0 in name) { n++ } END { print n + 0 }' \
    "$work/obligations" "$out")
echo "$((total - skips)) of $total obligations of the library proved; $skips left as skips; $(wc -c < "$out" | tr -d ' ') bytes in $out"
