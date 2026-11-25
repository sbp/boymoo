#!/bin/sh
# Builds the checker, from the root of the repository:
#
#     sh checker/build.sh
#
# It copies the books of checker/ into build/checker/acl2/, has ACL2
# certify each that changed and every book after it, in logic mode, so that
# ACL2 proves the termination of every function; exports the checker with
# export/book.sh, which writes its statements and its program text; writes
# build/checker/ground.program, the definitions of the ground theory as
# program text; and writes build/checker/library.statements, the checker's
# library: the lines of ACL2's library that define what the checker calls
# beyond the ground theory and itself, with what those lines call
# (checker/library.awk), which serve both as statements and as program
# text.  For that it exports ACL2's library with export/book.sh if
# build/export/library.statements is missing.  It does nothing that is
# already done.  It needs acl2, ACL2 8.7, on the PATH; export/book.sh stops
# under any other version.  It prints nothing unless something fails, and
# then it exits with status 1.

books="base read terms rules admit check"
dir=build/checker/acl2
mkdir -p "$dir"

# A book is certified again when it or a book before it changed.
stale=0
if ! cmp -s checker/package.lsp "$dir/package.lsp"; then
    cp checker/package.lsp "$dir/package.lsp"
    stale=1
fi
for b in $books; do
    if ! cmp -s "checker/$b.lisp" "$dir/$b.lisp"; then
        cp "checker/$b.lisp" "$dir/$b.lisp"
        stale=1
    fi
    if [ $stale -eq 1 ] || [ ! -f "$dir/$b.cert" ]; then
        stale=1
        rm -f "$dir/$b.cert"
        (cd "$dir" &&
         printf '(ld "package.lsp")\n(certify-book "%s" 1)\n' "$b" |
             acl2 > "$b.out" 2>&1)
        if [ ! -f "$dir/$b.cert" ]; then
            echo "checker/build.sh: ACL2 did not certify checker/$b.lisp; see $dir/$b.out" >&2
            exit 1
        fi
    fi
done

# The exported statements and program text of the checker.
out=build/export/books/$dir/check
if [ $stale -eq 1 ] || [ ! -s "$out.program" ] || [ "$dir/check.cert" -nt "$out.program" ]; then
    sh export/book.sh "$dir/check" || exit 1
    # Each line of the readback ends with two counts, which must agree.
    if [ ! -s "$out.program" ] || [ ! -s "$out.readback" ] ||
       ! awk '{ m = $NF; sub(/\)$/, "", m); if ($(NF - 1) != m) bad = 1 }
              END { exit bad }' "$out.readback"; then
        echo "checker/build.sh: the export of the checker failed; see $out.log" >&2
        exit 1
    fi
fi
cp "$out.statements" build/checker/checker.statements
cp "$out.program" build/checker/checker.program

grep '^(define ' spec/ground.txt > build/checker/ground.program

if [ ! -s build/export/library.statements ]; then
    sh export/book.sh :library > /dev/null || exit 1
fi
lib=build/checker/library.statements
if [ ! -f "$lib" ] || [ "$out.statements" -nt "$lib" ] ||
   [ build/export/library.statements -nt "$lib" ] || [ checker/library.awk -nt "$lib" ]; then
    awk -f checker/library.awk spec/ground.txt "$out.statements" \
        build/export/library.statements > "$lib.tmp" || exit 1
    mv "$lib.tmp" "$lib" || exit 1
fi
exit 0
