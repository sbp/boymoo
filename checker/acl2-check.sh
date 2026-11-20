#!/bin/sh
# The checker run inside ACL2, with the same functions that the runner runs
# from their program text.  From the root of the repository:
#
#     sh checker/acl2-check.sh < LIST
#
# Each line of LIST is NAME LIBRARY STATEMENTS PROOFS: a name with no space
# and three files.  For each, in order, it prints the line NAME, a tab and
# the verdict that ACL2 computes.  It builds the checker with
# checker/build.sh, and runs one ACL2 process for all the lines.  The
# names of the files may hold no space and no double quote.

sh checker/build.sh || exit 2

{
    echo '(include-book "build/checker/acl2/check")'
    echo '(ld "checker/acl2-run.lsp")'
    while read -r name library statements proofs; do
        printf '(run-case "%s" "%s" "%s" "%s" state)\n' \
            "$name" "$library" "$statements" "$proofs"
    done
    echo '(good-bye)'
} | acl2 2>&1 | sed -n 's/^verdict //p'
