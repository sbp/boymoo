#!/bin/sh
# Whether the two checkers of PLAN.md, step 4, agree.  From the root of the
# repository:
#
#     sh checks/agree.sh [ENGINE]
#
# The first checker, in checker/, runs on the reference runner; the second,
# in checker-js/, runs on the JavaScript engine ENGINE, a name found on the
# PATH or a path, node by default.  It shows what step 4 asks:
#
#   - both give accepted on spec/example;
#   - both give the first line of verdict.txt on every case of
#     checker/cases/ and of checker-js/cases/;
#   - on each book of export/books.txt, with build/export/library.statements
#     as the library, the two tools that write a skip for each obligation,
#     checker/skips.py and checker-js/skips.js, write the same file, and the
#     two checkers give the same verdict on it.
#
# It prints a line for each set and a last line that says whether all
# passed, and writes what each checker gave to build/agree/.  It needs what
# checker/check.sh needs (ACL2 when the checker must be built), python3, the
# engine, and node for checker-js/skips.js, which is written for Node.

engine=${1:-node}
if ! command -v "$engine" > /dev/null 2>&1; then
    echo "checks/agree.sh: no JavaScript engine $engine" >&2
    exit 2
fi
case ${engine##*/} in
    node|node[0-9]*) node=$engine ;;
    *) node=node ;;
esac

if [ -z "$RUNNER" ]; then
    RUNNER=build/runner/boymoo-run
    make -s -f runner/Makefile > /dev/null || exit 2
fi
sh checker/build.sh || exit 2
. checker/quote.sh

a=build/agree
rm -rf "$a"
mkdir -p "$a/q" "$a/js-skips"
: > "$a/empty"
library=build/export/library.statements
quote spec/ground.txt > "$a/q/ground"
failed=0
tab=$(printf '\t')

input() {
    if [ -f "$1" ]; then echo "$1"; else echo "$a/empty"; fi
}

# The first line that each checker gives on LIBRARY STATEMENTS PROOFS, the
# first checker's in $one and the second's in $two.  QLIBRARY, if given, is
# the library already written as a quoted constant.
both() {
    if [ -n "$4" ]; then cp "$4" "$a/q/library"; else quote "$1" > "$a/q/library"; fi
    quote "$2" > "$a/q/statements"
    quote "$3" > "$a/q/proofs"
    one=$(run_check "$a/q/ground" "$a/q/library" "$a/q/statements" "$a/q/proofs" | sed -n 1p)
    two=$(sh checker-js/check.sh "$1" "$2" "$3" "$engine" 2> /dev/null | sed -n 1p)
}

# spec/example
both "$a/empty" spec/example/statements.txt spec/example/proofs.txt ""
if [ "$one" = accepted ] && [ "$two" = accepted ]; then
    echo "spec/example: both give accepted"
else
    echo "spec/example: FAILED, the first gives \"$one\", the second \"$two\""
    failed=1
fi

# The cases of both checkers
for set in checker/cases checker-js/cases; do
    n=0
    bad=0
    out=$a/$(echo "$set" | tr '/' '-').txt
    : > "$out"
    for d in "$set"/*/; do
        [ -f "$d/verdict.txt" ] || continue
        name=$(basename "$d")
        expected=$(sed -n 1p "$d/verdict.txt")
        both "$(input "$d/library.txt")" "$(input "$d/statements.txt")" \
             "$(input "$d/proofs.txt")" ""
        echo "$name$tab$expected$tab$one$tab$two" >> "$out"
        n=$((n + 1))
        if [ "$one" != "$expected" ] || [ "$two" != "$expected" ]; then
            echo "  $set/$name: expected \"$expected\", the first gives \"$one\", the second \"$two\""
            bad=$((bad + 1))
        fi
    done
    if [ $bad -eq 0 ]; then
        echo "$set: both give the verdict of all $n cases"
    else
        echo "$set: FAILED on $bad of $n cases"
        failed=1
    fi
done

# The books
quote "$library" > "$a/library.q"
sed 's/#.*//; s/[[:space:]]*$//; /^$/d' export/books.txt > "$a/books.names"
n=0
skipbad=0
bad=0
: > "$a/books.txt"
while read -r book; do
    statements=build/export/books/$book.statements
    if [ ! -f "$statements" ]; then
        echo "  $book: not exported"
        skipbad=$((skipbad + 1))
        continue
    fi
    mine=$a/skips/$book.proofs
    theirs=$a/js-skips/$book.proofs
    mkdir -p "$(dirname "$mine")" "$(dirname "$theirs")"
    python3 checker/skips.py "$library" "$statements" > "$mine"
    "$node" checker-js/skips.js "$library" "$statements" > "$theirs" 2> /dev/null
    if ! cmp -s "$mine" "$theirs"; then
        echo "  $book: the two tools write different skips"
        skipbad=$((skipbad + 1))
    fi
    both "$library" "$statements" "$mine" "$a/library.q"
    echo "$book$tab$one$tab$two" >> "$a/books.txt"
    n=$((n + 1))
    if [ "$one" != "$two" ] || [ -z "$one" ]; then
        echo "  $book: the first gives \"$one\", the second \"$two\""
        bad=$((bad + 1))
    fi
done < "$a/books.names"
if [ $skipbad -eq 0 ]; then
    echo "books: the two tools write the same skips for all $n books"
else
    echo "books: FAILED, the skips differ or are missing for $skipbad books"
    failed=1
fi
if [ $bad -eq 0 ]; then
    echo "books: both give the same verdict on all $n books"
else
    echo "books: FAILED, the verdicts differ on $bad of $n books"
    failed=1
fi

if [ $failed -eq 0 ]; then
    echo "the two checkers agree"
else
    echo "the two checkers do NOT agree"
    exit 1
fi
