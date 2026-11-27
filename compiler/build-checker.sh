#!/bin/sh
# Builds the compiled checker, build/compiler/checker.  From the root of the
# repository:
#
#     sh compiler/build-checker.sh
#     COMPILER=EXECUTABLE sh compiler/build-checker.sh
#
# It has checker/build.sh build the checker; has ACL2 certify
# compiler/checker-entry.lisp beside the checker's books, and the exporter
# export it; writes the compiler's input, the program text of the checker
# and of its entry, to build/compiler/checker-test/checker.input; and
# compiles that input, printing the time of the compilation.
#
# COMPILER chooses the compiler. With COMPILER unset or empty, the
# many-pass compiler, build/compiler/compiler-2, compiles the input, and
# the script first runs sh compiler/bootstrap.sh when that executable is
# missing or older than a book of the compiler. With COMPILER set to a
# compiled compiler, such as the single-pass compiler
# build/compiler/single/compiler-2, which sh compiler/single/bootstrap.sh
# writes, that executable compiles the input as it stands.
set -eu

compiler=${COMPILER-}
if [ -n "$compiler" ]; then
    if [ ! -x "$compiler" ]; then
        echo "compiler/build-checker.sh: COMPILER names no executable: $compiler" >&2
        exit 2
    fi
    case $compiler in */*) ;; *) compiler=./$compiler ;; esac
fi

export LC_ALL=C
work=build/compiler/checker-test
acl=build/checker/acl2
book=$acl/checker-entry
exported=build/export/books/$book
mkdir -p "$work/tmp"
export TMPDIR="$PWD/$work/tmp"

sh checker/build.sh
if [ -z "$compiler" ]; then
    compiler=build/compiler/compiler-2
    stale=
    [ -x "$compiler" ] || stale=1
    for source in compiler/*.lisp compiler/proofs/rega-check.lisp compiler/package.lsp; do
        case $source in *checker-entry.lisp|*prover-entry.lisp) continue ;; esac
        [ ! "$source" -nt "$compiler" ] || stale=1
    done
    [ -z "$stale" ] || sh compiler/bootstrap.sh
fi
if ! cmp -s compiler/checker-entry.lisp "$book.lisp" ||
   [ ! -f "$book.cert" ] || [ "$acl/check.cert" -nt "$book.cert" ]; then
    cp compiler/checker-entry.lisp "$book.lisp"
    rm -f "$book.cert"
    (cd "$acl" &&
        printf '(ld "package.lsp")\n(certify-book "checker-entry" 1)\n(good-bye)\n' |
            acl2 > checker-entry.out 2>&1)
fi
if [ ! -f "$book.cert" ]; then
    echo "ACL2 did not certify the entry book. See $book.out" >&2
    exit 2
fi

if [ ! -s "$exported.program" ] || [ "$book.cert" -nt "$exported.program" ]; then
    sh export/book.sh "$book"
fi
if [ ! -s "$exported.program" ] || [ ! -s "$exported.readback" ] ||
   ! awk '{ n = $NF; sub(/\)$/, "", n); if ($(NF - 1) != n) bad = 1 }
          END { exit bad }' "$exported.readback"; then
    echo "The export of the entry book failed. See $exported.log" >&2
    exit 2
fi

# The export includes the definitions of the checker and the entry book.
awk -f checker/library.awk spec/ground.txt "$exported.statements" \
    build/export/library.statements > "$work/library.statements"
{
    awk '/^\((package|hidden-package) /' spec/ground.txt "$exported.statements"
    cat build/checker/ground.program "$work/library.statements" "$exported.program"
    printf '(entry BOYMOO::CHECKER-ENTRY)\n'
} > "$work/checker.input"

time -p "$compiler" < "$work/checker.input" > "$work/checker"
chmod +x "$work/checker"
mv "$work/checker" build/compiler/checker
