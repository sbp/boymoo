#!/bin/sh
# The checker run inside ACL2, with the same functions that the runner runs
# from their program text.  From the root of the repository:
#
#     sh checker/acl2-check.sh LIBRARY STATEMENTS PROOFS [LIBRARY-PROOFS]
#     sh checker/acl2-check.sh < LIST
#
# With arguments, it prints the verdict. Each line of LIST has a case
# name followed by the same arguments, without spaces in the names. For
# each line it prints the case name, a tab and the verdict. An omitted
# fourth input is empty. It builds the checker with checker/build.sh and
# computes the verdicts in one ACL2 process.

case $# in
    0|3|4) ;;
    *) echo 'usage: sh checker/acl2-check.sh LIBRARY STATEMENTS PROOFS [LIBRARY-PROOFS]' >&2
       exit 2 ;;
esac
for f do
    if [ ! -f "$f" ]; then
        echo "checker/acl2-check.sh: no file $f" >&2
        exit 2
    fi
done

sh checker/build.sh || exit 2

write_case() {
    printf '(run-case-four'
    case_escape='s/[\\"]/\\&/g'
    for arg do
        case $arg in
            *\\*|*\"*|*'*'*|*'?'*|*'['*|*']'*)
                arg=$(printf '%s.\n' "$arg" | sed "$case_escape")
                arg=${arg%.} ;;
        esac
        printf ' "%s"' "$arg"
        # File arguments are read as Lisp strings and then as pathnames.
        case_escape='s/[][?*\\]/\\&/g; s/[\\"]/\\&/g'
    done
    printf ' state)\n'
}

{
    echo '(include-book "build/checker/acl2/check")'
    echo '(ld "checker/acl2-run.lsp")'
    if [ $# -gt 0 ]; then
        write_case input "$1" "$2" "$3" "${4-}"
    else
        while read -r name library statements proofs library_proofs; do
            write_case "$name" "$library" "$statements" "$proofs" "$library_proofs"
        done
    fi
    echo '(good-bye)'
} | acl2 2>&1 | awk -v direct="$#" '
    /^verdict / {
        if (direct) sub(/^verdict input\t/, "")
        else sub(/^verdict /, "")
        print
        found = 1
    }
    END { if (direct && !found) exit 2 }'
