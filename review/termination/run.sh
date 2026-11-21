#!/bin/sh
# The comparison of the obligations of termination that the checker
# computes with ACL2's measure conjectures (review/termination/README.md).
# From the root of the repository:
#
#     sh review/termination/run.sh            the library and every book of export/books.txt
#     sh review/termination/run.sh BOOK ...   the library and the books named
#
# It needs what checker/build.sh needs, the books of the checker and the
# printer certified by checker/build.sh and export/certify.sh, which it
# runs, the files that export/run.sh
# writes under build/export/ (the statements of the library and of each
# book, and the prover's aids), the books build/outer and build/choice
# that export/run.sh certifies, and timeout, xargs, sort, comm and the
# usual POSIX tools.  It runs one ACL2 process for the library and one for
# each book, two at a time (review/termination/one.sh), and prints a line
# for the ground theory, the library and each book, and a last line that
# says whether every definition compared agreed.  It writes the same to
# build/termination/summary.txt, and, for each target, a line for each
# definition to build/termination/library.txt or
# build/termination/books/BOOK.txt.

if [ ! -f build/export/library.statements ]; then
    echo "review/termination/run.sh: no build/export/library.statements; run sh export/run.sh first" >&2
    exit 2
fi
sh checker/build.sh || exit 2
sh export/certify.sh || exit $?

dir=build/termination
mkdir -p "$dir/books"
if [ $# -gt 0 ]; then
    printf '%s\n' "$@" > "$dir/books.list"
else
    sed 's/#.*//; s/[[:space:]]*$//; /^$/d' export/books.txt > "$dir/books.list"
fi

start=$(date +%s)
sh review/termination/one.sh :library || exit $?

# The book of cases, review/termination/cases.lisp, certified into
# build/termination/ and exported as export/run.sh exports build/choice.
rm -f "$dir"/cases.*
cp review/termination/cases.lisp "$dir/cases.lisp"
echo '(certify-book "build/termination/cases" 0 nil)' |
    timeout 600 acl2 > "$dir/cases.log" 2>&1
if [ -f "$dir/cases.cert" ]; then
    sh export/book.sh build/termination/cases || exit $?
    sh review/termination/one.sh build/termination/cases || exit $?
fi

xargs -n 1 -P 2 sh review/termination/one.sh < "$dir/books.list" || exit $?
end=$(date +%s)

# The counts of one file of results, for the definitions of the set SET:
# a line NAME: ..., and the word "bad" at its start if a definition differs,
# a function is not accounted for, or the run did not finish.
counts() {
    awk -v set="$2" -v name="$3" '
        $1 == "define" && $2 == set {
            n++; f += $6
            if ($5 == "agree") { a++; e++ }
            else if ($5 == "agree-tidy") a++
            else if ($5 == "agree-repeats") { a++; rp++ }
            else if ($5 == "agree-order") { o++; bad = 1 }
            else if ($5 == "differ") { d++; bad = 1 }
            else if ($5 == "no-justification") { nj++; bad = 1 }
            else { nc++; why[$5 ($8 == "" ? "" : " " $8)]++ }
        }
        $1 == "uncovered" && set != "ground" {
            if ($3 == "loop$" || $3 == "subversive") { nc++; why[$3]++ } else { u++; bad = 1 }
        }
        $1 == "refused" && $2 == set { r++; bad = 1 }
        $1 == "functions" { done = 1; fns = $2 }
        $1 == "error" { err = 1 }
        END {
            if (!done || err) { print "bad " name ": the comparison did not finish"; exit }
            s = name ": " n + 0 " definitions (" f + 0 " functions), " \
                a + 0 " agree (" e + 0 " exactly), " d + 0 " differ"
            if (rp) s = s " (" rp " in another order, from the removal of repeats)"
            if (o) s = s ", " o " have the same clauses in another order"
            if (nj) s = s ", " nj " have obligations but no justification in ACL2"
            if (u) s = s ", " u " functions with a justification have no define with obligations"
            if (r) s = s ", " r " lines refused"
            if (nc) {
                s = s "; not comparable: " nc
                sep = " ("
                for (k in why) { s = s sep why[k] " " k; sep = ", " }
                s = s ")"
            }
            if (set != "library" && set != "ground") s = s "; " fns " functions with a justification"
            print (bad ? "bad " : "") s
        }' "$1"
}

# Whether the measure and relation that the prover's aids AIDS give each
# function are those of ACL2's world, MEASURES.
aids() {
    sed -n 's/^\((measure .*\) "[a-z]*")$/\1)/p' "$1" | sort -u > "$dir/aids.tmp"
    sort -u "$2" > "$dir/measures.tmp"
    if cmp -s "$dir/aids.tmp" "$dir/measures.tmp"; then
        echo "same"
    else
        echo "different"
    fi
}

# Whether each definition of the book of cases has the class that
# review/termination/cases.txt gives.
cases() {
    f=$dir/books/build/termination/cases.txt
    if [ ! -f "$f" ]; then
        echo "bad cases: the book of cases was not certified, exported or compared; see $dir/cases.log"
        return
    fi
    sed 's/#.*//; /^$/d' review/termination/cases.txt | sort > "$dir/cases.want"
    awk '$1 == "define" { print $4, $5 } $1 == "uncovered" { print $2, "uncovered", $3 }' "$f" |
        sort > "$dir/cases.got"
    n=$(wc -l < "$dir/cases.want" | tr -d ' ')
    if [ "$(comm -23 "$dir/cases.want" "$dir/cases.got")" = "" ]; then
        echo "cases: all $n definitions of review/termination/cases.lisp have the class that cases.txt gives"
    else
        echo "bad cases: these definitions of review/termination/cases.lisp do not have the class that cases.txt gives: $(comm -23 "$dir/cases.want" "$dir/cases.got" | tr '\n' ';')"
    fi
    rm -f "$dir/cases.want" "$dir/cases.got"
}

{
    echo "sh review/termination/run.sh, run on $(date +%Y-%m-%d) in $((end - start)) seconds"
    echo
    cases
    counts "$dir/library.txt" ground "ground theory"
    counts "$dir/library.txt" library library
    while read -r book; do
        f=$dir/books/$book.txt
        if [ ! -f "build/export/books/$book.statements" ]; then
            echo "bad $book: not exported"
        elif [ ! -f "$f" ]; then
            echo "bad $book: no result"
        else
            line=$(counts "$f" book "$book")
            if [ -f "$dir/books/$book.measures" ] &&
               [ "$(aids "build/export/books/$book.aids" "$dir/books/$book.measures")" != same ]; then
                line="bad $line; the aids give other measures than ACL2's world"
            fi
            echo "$line"
        fi
    done < "$dir/books.list"
} > "$dir/summary.tmp"
rm -f "$dir/aids.tmp" "$dir/measures.tmp"

# The books in all: each definition once for each book whose statements
# hold it, and once for each distinct define line.  A book's statements
# hold those of the books it includes, and two books may define one name
# differently, so a definition is told by the text of its define line.
: > "$dir/defines.tmp"
while read -r book; do
    f=$dir/books/$book.txt
    [ -f "$f" ] || continue
    awk 'FNR == NR { if ($1 == "define" && $2 == "book") want[$3] = $5 " " $6 " " $7 " " $8 " " $9; next }
         FNR in want { print want[FNR] "\t" $0 }' "$f" "build/export/books/$book.statements" >> "$dir/defines.tmp"
done < "$dir/books.list"
# The steps of the normal form that changed each side, from the notes
# "checker=..." and "acl2=..." of the definitions that agree in normal
# form, for the library and the ground theory and for the distinct define
# lines of the books.
{
    awk '$1 == "define" && ($5 == "agree-tidy" || $5 == "agree-repeats") { print $8, $9 }' "$dir/library.txt"
    awk -F '\t' '!($2 in seen) { seen[$2] = 1; split($1, w, " ")
                                 if (w[1] == "agree-tidy" || w[1] == "agree-repeats") print w[4], w[5] }' "$dir/defines.tmp"
} | awk '{ n++; for (i = 1; i <= 2; i++) { split($i, a, "="); m = split(a[2], b, ",")
                                           for (j = 1; j <= m; j++) if (b[j] != "-") c[a[1] " " b[j]]++ } }
         END { s = "steps of the normal form, over the " n + 0 " definitions of the ground theory, the library and the distinct define lines of the books that agree in it:"
               sep = " "; for (x in c) { s = s sep c[x] " " x; sep = ", " }; print s }' > "$dir/steps.tmp"
awk -F '\t' '
    { split($1, w, " "); n++; c[w[1]]++; f += w[2]; k += w[3]
      if (!($2 in seen)) { seen[$2] = 1; d++; dc[w[1]]++; df += w[2]; dk += w[3] } }
    function list(a,   s, sep, x) { s = ""; sep = ""; for (x in a) { s = s sep a[x] " " x; sep = ", " }; return s }
    END {
        print "books in all: " n + 0 " definitions (" f + 0 " functions, " k + 0 " clauses): " list(c)
        print "books in all, each distinct define line once: " d + 0 " definitions (" df + 0 " functions, " dk + 0 " clauses): " list(dc)
    }' "$dir/defines.tmp" >> "$dir/summary.tmp"
cat "$dir/steps.tmp" >> "$dir/summary.tmp"
rm -f "$dir/steps.tmp"
rm -f "$dir/defines.tmp"

if grep -q '^bad ' "$dir/summary.tmp"; then
    last="some definitions do not agree, or the comparison did not finish"
    status=1
else
    last="all compared definitions agree"
    status=0
fi
{
    sed 's/^bad //' "$dir/summary.tmp"
    echo
    echo "$last"
} > "$dir/summary.txt"
rm -f "$dir/summary.tmp"
cat "$dir/summary.txt"
exit $status
