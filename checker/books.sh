#!/bin/sh
# The checker on the books of export/books.txt, from the root of the
# repository:
#
#     sh checker/books.sh [COUNT]
#
# For each book, or for the first COUNT, the library is
# build/export/library.statements, the statements are the book's, which
# export/run.sh wrote, and the proofs skip every obligation: checker/skips.py
# writes them to build/checker/skips/BOOK.proofs.  It runs the checker on the
# runner and writes build/checker/books.txt, a line for each book: its name,
# a tab and the verdict.  It also writes build/checker/books-list.txt, the
# list that checker/acl2-check.sh reads to compute the same verdicts in
# ACL2.  At the end it prints the number of books and the time taken.

if [ -z "$RUNNER" ]; then
    RUNNER=build/runner/boymoo-run
    make -s -f runner/Makefile > /dev/null || exit 2
fi
sh checker/build.sh || exit 2
. checker/quote.sh

library=build/export/library.statements
q=build/checker/quoted
mkdir -p "$q" build/checker/skips
quote spec/ground.txt > "$q/ground"
quote "$library" > "$q/library"

sed 's/#.*//; s/[[:space:]]*$//; /^$/d' export/books.txt > build/checker/books.names
if [ $# -gt 0 ]; then
    head -n "$1" build/checker/books.names > build/checker/books.names.tmp
    mv build/checker/books.names.tmp build/checker/books.names
fi

: > build/checker/books.txt
: > build/checker/books-list.txt
start=$(date +%s)
n=0
tab=$(printf '\t')
while read -r book; do
    statements=build/export/books/$book.statements
    proofs=build/checker/skips/$book.proofs
    mkdir -p "$(dirname "$proofs")"
    if [ ! -f "$statements" ]; then
        echo "$book${tab}not exported" >> build/checker/books.txt
        continue
    fi
    python3 checker/skips.py "$library" "$statements" > "$proofs"
    quote "$statements" > "$q/statements"
    quote "$proofs" > "$q/proofs"
    verdict=$(run_check "$q/ground" "$q/library" "$q/statements" "$q/proofs" | sed -n 1p)
    echo "$book$tab$verdict" >> build/checker/books.txt
    echo "$book $library $statements $proofs" >> build/checker/books-list.txt
    n=$((n + 1))
done < build/checker/books.names
end=$(date +%s)
rm -f "$q/statements" "$q/proofs"
echo "$n books in $((end - start)) seconds"
