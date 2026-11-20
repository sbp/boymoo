#!/bin/sh
# The exporter of PLAN.md, step 2.  Run from the root of the repository:
#
#     sh export/run.sh            the library and every book of export/books.txt
#     sh export/run.sh BOOK ...   the library and the books named
#
# It needs acl2 (ACL2 8.7 with its distributed books), python3, timeout,
# xargs and the usual POSIX tools on the PATH.  For ACL2's built-in
# library and for each book it writes, under build/export/, the
# statements, the program text, the prover's aids and the notes, has ACL2
# read each file back (export/readback.lsp), has checks/reader.py read
# every file, and writes build/export/summary.txt: the number of
# statements of each kind, the size in bytes of each file, which books
# were exported and confirmed, and why each of the others was not.  It
# runs two ACL2 processes at a time.

mkdir -p build/export/books

# The functions that the ground theory defines, which the library leaves
# out.  They are read from spec/ground.txt.
names=$(sed -n 's/^(define [^ (][^ ]* (\([^ ]*\) .*/\1/p; s/^(define ([^()]*) (\([^ ]*\) .*/\1/p' spec/ground.txt |
            tr '\n' ' ')
echo "(assign bx-ground-fns '($names))" > build/export/ground-fns.lsp

if [ $# -gt 0 ]; then
    printf '%s\n' "$@" > build/export/books.list
else
    sed 's/#.*//; s/[[:space:]]*$//; /^$/d' export/books.txt > build/export/books.list
fi

# The book build/outer, of checks/run.sh, includes a book locally and so
# holds a package that ACL2 keeps hidden.  It is certified here as there.
if grep -q '^build/outer$' build/export/books.list; then
    rm -f build/hidden.* build/outer.*
    cp checks/hidden.lisp build/hidden.lisp
    cp checks/outer.lisp build/outer.lisp
    timeout 600 acl2 < checks/hidden.lsp > build/hidden.log 2>&1
    timeout 600 acl2 < checks/outer.lsp > build/outer.log 2>&1
fi

# The book export/choice.lisp holds two cases that no certified book of
# ACL2's distribution keeps in its world.
if grep -q '^build/choice$' build/export/books.list; then
    rm -f build/choice.*
    cp export/choice.lisp build/choice.lisp
    echo '(certify-book "build/choice" 0 nil)' |
        timeout 600 acl2 > build/choice.log 2>&1
fi

start=$(date +%s)
sh export/book.sh :library
xargs -n 1 -P 2 sh export/book.sh < build/export/books.list
end=$(date +%s)

# Every file in the formats, read by the reader of checks/reader.py.
files="build/export/library.statements build/export/library.program build/export/library.notes build/export/library.readback"
while read -r book; do
    for kind in statements program aids notes readback; do
        f=build/export/books/$book.$kind
        [ -f "$f" ] && files="$files $f"
    done
done < build/export/books.list
python3 checks/reader.py $files > build/export/reader.txt
reader=$?

{
    version=$(grep -a -m 1 -o 'ACL2 Version [0-9.]*' build/export/library.log)
    echo "sh export/run.sh, run on $(date +%Y-%m-%d) in $((end - start)) seconds with $version"
    echo
    python3 export/measure.py $(cat build/export/books.list)
    echo
    if [ $reader -eq 0 ]; then
        echo "checks/reader.py read every file"
    else
        echo "checks/reader.py refused:"
        grep '^FAIL' build/export/reader.txt
    fi
} > build/export/summary.txt
cat build/export/summary.txt
