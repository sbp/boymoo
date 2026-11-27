#!/bin/sh
# Has ACL2 certify the books of the single-pass compiler and the exporter
# export them. From the root of the repository:
#
#     sh compiler/single/build.sh [--a64]
#
# The books that both compilers share are copied from compiler/, and
# gen.lisp, runtime.lisp and compile.lisp from compiler/single/, into
# build/compiler/single/acl2, where ACL2 certifies them in order. The
# statements and program text of the compiler, ground.program and
# library.statements are written to build/compiler/single. With --a64 only
# the assembler, compiler/a64.lisp, is certified and exported, and the
# files are written to build/compiler/a64, for compiler/test-a64.sh.
set -eu

case ${1-} in
    --a64) books=a64; top=a64; export_dir=build/compiler/a64 ;;
    '') books='a64 read index data gen sha256 macos linux runtime compile'
        top=compile; export_dir=build/compiler/single ;;
    *) echo 'Usage: sh compiler/single/build.sh [--a64]' >&2; exit 2 ;;
esac
dir=build/compiler/single/acl2
mkdir -p "$dir" build/compiler/single/tmp
export TMPDIR="$PWD/build/compiler/single/tmp"

# The file that holds book $1.
source_of() {
    case $1 in
        gen|runtime|compile) printf 'compiler/single/%s.lisp\n' "$1" ;;
        *) printf 'compiler/%s.lisp\n' "$1" ;;
    esac
}

stale=0
if ! cmp -s compiler/package.lsp "$dir/package.lsp"; then
    cp compiler/package.lsp "$dir/package.lsp"
    stale=1
fi
cp checks/version.lsp "$dir/version.lsp"
previous=
for b in $books; do
    source=$(source_of "$b")
    if ! cmp -s "$source" "$dir/$b.lisp"; then
        cp "$source" "$dir/$b.lisp"
        stale=1
    fi
    if [ "$stale" -eq 1 ] || [ ! -f "$dir/$b.cert" ] ||
       { [ -n "$previous" ] && [ "$previous" -nt "$dir/$b.cert" ]; }; then
        stale=1
        rm -f "$dir/$b.cert"
        (cd "$dir" &&
         printf '(ld "version.lsp")\n(ld "package.lsp")\n(certify-book "%s" 1)\n(good-bye)\n' "$b" |
             acl2 > "$b.out" 2>&1)
        if [ ! -f "$dir/$b.cert" ]; then
            echo "compiler/single/build.sh: ACL2 did not certify $source; see $dir/$b.out" >&2
            exit 1
        fi
    fi
    previous=$dir/$b.cert
done

mkdir -p "$export_dir"
out=build/export/books/$dir/$top
if [ "$stale" -eq 1 ] || [ ! -s "$out.program" ] || [ "$dir/$top.cert" -nt "$out.program" ]; then
    sh export/book.sh "$dir/$top"
fi
if [ ! -s "$out.program" ] || [ ! -s "$out.readback" ] ||
   ! awk '{ m = $NF; sub(/\)$/, "", m); if ($(NF - 1) != m) bad = 1 }
          END { exit bad }' "$out.readback"; then
    echo "compiler/single/build.sh: the export failed; see $out.log" >&2
    exit 1
fi
cp "$out.statements" "$export_dir/compiler.statements"
cp "$out.program" "$export_dir/compiler.program"

grep '^(define ' spec/ground.txt > "$export_dir/ground.program"

if [ ! -s build/export/library.statements ]; then
    sh export/book.sh :library
fi
lib=$export_dir/library.statements
if [ ! -f "$lib" ] || [ "$out.statements" -nt "$lib" ] ||
   [ build/export/library.statements -nt "$lib" ] ||
   [ spec/ground.txt -nt "$lib" ] || [ checker/library.awk -nt "$lib" ] ||
   [ compiler/single/build.sh -nt "$lib" ]; then
    awk -f checker/library.awk spec/ground.txt "$out.statements" \
        build/export/library.statements > "$lib.all"
    # ACL2 defines hard-error and throw-nonexec-error to return NIL, but
    # runs each as an error that ends the computation. With no definition,
    # a call of either stops, as in ACL2, so the compiler stops on an error
    # instead of going on with NIL.
    awk '! /^\(define COMMON-LISP::NIL \(ACL2::(HARD-ERROR|THROW-NONEXEC-ERROR) /' "$lib.all" > "$lib.tmp"
    rm -f "$lib.all"
    mv "$lib.tmp" "$lib"
fi
