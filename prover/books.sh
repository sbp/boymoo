#!/bin/sh
# Prove books with the prover, and have both checkers judge each with the
# library's proofs as the fourth input (PLAN.md, step 6).  From the root of
# the repository, after sh prover/build-all.sh, make -f runner-fast/Makefile
# and sh review/termination/run.sh:
#
#     sh prover/books.sh [-f | -l LIBRARY-PROOFS] BOOK ...
#
# Without -l it first proves the library: sh prover/library.sh, with its
# defaults, and with -f if -f is given, writes build/prover/library.proofs,
# which are then LIBRARY-PROOFS; and if it leaves an obligation of the
# library unproved, the script stops there, since no book can then be
# accepted. With -l the library's proofs are the file LIBRARY-PROOFS.
#
# Each BOOK is a book of export/books.txt, whose statements and aids are
# build/export/books/BOOK.statements and build/export/books/BOOK.aids.
# The driver writes the book's proofs to build/prover/books/BOOK.proofs,
# with build/export/library.statements as the library, less each helper
# entry whose head line LIBRARY-PROOFS already states (prover/tools/repeats.awk):
# a helper is named by its content, and the checker, which reads the
# library's proofs first, has admitted it under that name. Then the checker in
# ACL2 Core, on the fast runner, and the second checker, on Node, judge the
# library, the book's statements, its proofs and LIBRARY-PROOFS. It prints
# the two verdicts of each book, and ends with "All N books accepted by both
# checkers." when every verdict is accepted, and otherwise with "Some books
# are not accepted by both checkers." and status 1.
set -u
export LC_ALL=C

usage() {
    echo 'usage: sh prover/books.sh [-f | -l LIBRARY-PROOFS] BOOK ...' >&2
    exit 2
}
fresh=
library_proofs=
while [ "$#" -gt 0 ]; do
    case $1 in
        -f) fresh=-f; shift ;;
        -l) [ "$#" -ge 2 ] || usage; library_proofs=$2; shift 2 ;;
        -*) usage ;;
        *) break ;;
    esac
done
[ "$#" -ge 1 ] || usage
[ -n "$fresh" ] && [ -n "$library_proofs" ] && usage
library=build/export/library.statements
work=build/prover/books
mkdir -p "$work" || exit 2
if [ -z "$library_proofs" ]; then
    library_proofs=build/prover/library.proofs
    sh prover/library.sh $fresh "$library_proofs" > "$work/library.out" || {
        cat "$work/library.out"
        echo 'prover/books.sh: prover/library.sh failed' >&2
        exit 1
    }
    cat "$work/library.out"
    grep -q '; 0 left as skips;' "$work/library.out" || {
        echo 'prover/books.sh: the library is not proved in full' >&2
        exit 1
    }
fi
[ -s "$library_proofs" ] || { echo "prover/books.sh: no file $library_proofs" >&2; exit 2; }

count=0
failed=0
for book do
    count=$((count + 1))
    statements=build/export/books/$book.statements
    aids=build/export/books/$book.aids
    proofs=$work/$book.proofs
    if [ ! -s "$statements" ]; then
        echo "$book: no file $statements"
        failed=1
        continue
    fi
    mkdir -p "$(dirname "$proofs")" || exit 2
    [ -f "$aids" ] || aids=
    if ! sh prover/driver/prove.sh "$library" "$statements" $aids > "$proofs.tmp"; then
        echo "$book: the driver failed"
        rm -f "$proofs.tmp"
        failed=1
        continue
    fi
    awk -v known="$library_proofs" -f prover/tools/repeats.awk "$proofs.tmp" > "$proofs" || exit 2
    rm -f "$proofs.tmp"
    core=$(RUNNER=build/runner-fast/boymoo-run-fast sh checker/check.sh \
        "$library" "$statements" "$proofs" "$library_proofs" | head -1)
    second=$(sh checker-js/check.sh "$library" "$statements" "$proofs" \
        "$library_proofs" node | head -1)
    echo "$book: checker: $core; second checker: $second"
    [ "$core" = accepted ] && [ "$second" = accepted ] || failed=1
done
if [ "$failed" -eq 0 ]; then
    echo "All $count books accepted by both checkers."
else
    echo 'Some books are not accepted by both checkers.'
    exit 1
fi
