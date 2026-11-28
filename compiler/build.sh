#!/bin/sh
# Certifies the books of the compiler and, with -x, exports the
# last one named. From the root of the repository:
#
#     sh compiler/build.sh [-d DIR] [-x] BOOK ...
#
# DIR is the build directory, build/compiler by default; the books are
# certified in DIR/acl2 in the order given, each after copying
# compiler/BOOK.lisp there. A BOOK may name a book in a subdirectory of
# compiler/, such as proofs/rega-check. A book is certified again when its
# text differs from the copy, when it has no certificate, or when a book
# before it in the list was certified again. Name every book that a book
# includes before it. With -x, the exporter exports the last book, and DIR
# receives compiler.statements, compiler.program, ground.program and
# library.statements. With no BOOK, every book of the compiler is built
# in order.
#
# Several builds can run at once when each has its own DIR.
set -eu

dir=build/compiler
export_it=0
while [ $# -gt 0 ]; do
    case $1 in
        -d) dir=$2; shift 2 ;;
        -x) export_it=1; shift ;;
        -*) echo 'Usage: sh compiler/build.sh [-d DIR] [-x] BOOK ...' >&2; exit 2 ;;
        *) break ;;
    esac
done
if [ $# -eq 0 ]; then
    set -- a64 read index data sha256 macos linux runtime qir rt-qir resolve \
        simplify lower expand opt abi isel rega \
        proofs/rega-check emit compile
    export_it=1
fi

acl=$dir/acl2
mkdir -p "$acl" "$dir/tmp"
export TMPDIR="$PWD/$dir/tmp"

stale=0
if ! cmp -s compiler/package.lsp "$acl/package.lsp"; then
    cp compiler/package.lsp "$acl/package.lsp"
    stale=1
fi
cp checks/version.lsp "$acl/version.lsp"
top=
for b in "$@"; do
    if [ ! -f "compiler/$b.lisp" ]; then
        echo "compiler/build.sh: there is no compiler/$b.lisp" >&2
        exit 2
    fi
    if ! cmp -s "compiler/$b.lisp" "$acl/$b.lisp"; then
        mkdir -p "$(dirname "$acl/$b.lisp")"
        cp "compiler/$b.lisp" "$acl/$b.lisp"
        stale=1
    fi
    if [ "$stale" -eq 1 ] || [ ! -f "$acl/$b.cert" ]; then
        stale=1
        rm -f "$acl/$b.cert"
        (cd "$acl" &&
         printf '(ld "version.lsp")\n(ld "package.lsp")\n(certify-book "%s" 1)\n(good-bye)\n' "$b" |
             acl2 > "$b.out" 2>&1) || true
        if [ ! -f "$acl/$b.cert" ]; then
            echo "compiler/build.sh: ACL2 did not certify compiler/$b.lisp; see $acl/$b.out" >&2
            exit 1
        fi
    fi
    top=$b
done

[ "$export_it" -eq 1 ] || exit 0

out=build/export/books/$acl/$top
if [ "$stale" -eq 1 ] || [ ! -s "$out.program" ] || [ "$acl/$top.cert" -nt "$out.program" ]; then
    sh export/book.sh "$acl/$top"
fi
if [ ! -s "$out.program" ] || [ ! -s "$out.readback" ] ||
   ! awk '{ m = $NF; sub(/\)$/, "", m); if ($(NF - 1) != m) bad = 1 }
          END { exit bad }' "$out.readback"; then
    echo "compiler/build.sh: the export failed; see $out.log" >&2
    exit 1
fi
cp "$out.statements" "$dir/compiler.statements"
cp "$out.program" "$dir/compiler.program"
grep '^(define ' spec/ground.txt > "$dir/ground.program"
lib=$dir/library.statements
awk -f checker/library.awk spec/ground.txt "$out.statements" \
    build/export/library.statements > "$lib.all"
# With no definition, a call of hard-error
# or throw-nonexec-error stops, as in ACL2.
awk '! /^\(define COMMON-LISP::NIL \(ACL2::(HARD-ERROR|THROW-NONEXEC-ERROR) /' "$lib.all" > "$lib.tmp"
rm -f "$lib.all"
mv "$lib.tmp" "$lib"
