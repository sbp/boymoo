#!/bin/sh
# The comparison of review/termination/README.md for one target, from the
# root of the repository:
#
#     sh review/termination/one.sh NAME
#
# NAME is :library, for the ground theory and ACL2's built-in library, or
# the name of a book as export/books.txt gives it: one of ACL2's
# distributed books, or a book of this repository certified into build/
# (a name that begins with build/), whose statements export/book.sh wrote.  It writes, under
# build/termination/, NAME.txt, a line for each definition, NAME.measures,
# the measure and relation of each function from ACL2's world, and
# NAME.log, what ACL2 printed.  review/termination/run.sh calls it.

name=$1
case $name in
    :library) out=build/termination/library ;;
    *) out=build/termination/books/$name ;;
esac
mkdir -p "$(dirname "$out")"
rm -f "$out.txt" "$out.measures" "$out.log"

case $name in
    :library) include=''; statements=nil ;;
    build/*) include="(include-book \"$name\" :uncertified-okp nil :ttags :all)"
             statements="\"build/export/books/$name.statements\"" ;;
    *) include="(include-book \"$name\" :dir :system :uncertified-okp nil :ttags :all)"
       statements="\"build/export/books/$name.statements\"" ;;
esac

{
    echo '(in-package "ACL2")'
    echo '(ld "checks/version.lsp")'
    echo "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
    echo '(f-put-global (quote tt-old) (w state) state)'
    echo "$include"
    echo '(f-put-global (quote tt-hi) (w state) state)'
    echo '(include-book "build/checker/acl2/check")'
    echo '(include-book "build/export/acl2/canon")'
    echo '(ld "review/termination/obligations.lisp")'
    echo '(ld "review/termination/compare.lsp")'
    echo '(set-guard-checking :none)'
    case $name in
        :library) echo "(tt-run (@ tt-hi) nil nil \"$out\" state)" ;;
        *) echo "(tt-run (@ tt-hi) (@ tt-old) $statements \"$out\" state)" ;;
    esac
    echo '(good-bye)'
} | timeout 1800 acl2 > "$out.log" 2>&1
status=$?
# checks/version.lsp ends ACL2 with status 3 under any version but the
# one it names.
if [ $status -eq 3 ]; then
    echo "review/termination/one.sh stopped: $(sed -n 's/^version: //p' "$out.log")" >&2
    exit 3
fi
exit 0
