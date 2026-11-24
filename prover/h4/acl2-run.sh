#!/bin/sh
# Read one canonical term per input line. Use -v for evaluation CPU time.
# Run from the repository root. BOOK defaults to the last certified prefix.

stats=
if [ "${1-}" = -v ]; then
    stats=yes
    shift
fi
files=
if [ "${1-}" = --files ]; then
    files=yes
    shift
fi
if { [ -z "$files" ] && [ "$#" -gt 1 ]; } ||
   { [ -n "$files" ] && [ "$#" -lt 2 ]; }; then
    echo 'usage: sh prover/h4/acl2-run.sh [-v] [BOOK] or [-v] --files BOOK FILE ...' >&2
    exit 2
fi
. prover/h4/tools/run-book.sh
h4_book "${1-}" certified || exit 2
[ "$#" -eq 0 ] || shift
tmp=build/prover/h4/acl2-run.$$
mkdir "$tmp" || exit 2
write_values() {
    for output in "$tmp"/values.*; do
        [ ! -f "$output" ] || cat "$output" || return 2
    done
    if [ -n "$stats" ] && [ -f "$tmp/log" ]; then
        sed -n '/^h4-run-start /p; /^h4-run-cpu /p' "$tmp/log" >&2
    fi
}
trap 'rm -rf "$tmp"' 0
trap 'write_values; exit 143' 1 2 15
if [ -z "$files" ]; then
    cat > "$tmp/terms" || exit 2
    set -- "$tmp/terms"
fi
for input do
    case $input in
        /*|../*|*/../*|*/..|*[!a-zA-Z0-9_./-]*)
            echo 'prover/h4/acl2-run.sh: use a repository-relative input file.' >&2
            exit 2 ;;
    esac
    test -f "$input" || exit 2
done
{
    echo "(set-ld-error-action '(:exit 1) state)"
    printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$h4_books" "$book"
    if [ -f build/export/acl2/canon.cert ] && cmp -s checks/canon.lisp build/export/acl2/canon.lisp; then
        echo '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
    else
        echo '(ld "checks/canon.lsp" :ld-error-action :error)'
    fi
    echo '(ld "export/readback.lsp" :ld-error-action :error)'
    echo '(ld "prover/tools/acl2-run.lsp" :ld-error-action :error)'
    echo '(ld "prover/h4/tools/acl2-run.lsp" :ld-error-action :error)'
    first=1
    file=1
    for input do
        printf '(h4-prover-run-file "%s" "%s/values.%06d" %d state)\n' "$input" "$tmp" "$file" "$first"
        lines=$(wc -l < "$input") || exit 2
        first=$((first + lines))
        file=$((file + 1))
    done
    echo '(good-bye)'
} > "$tmp/session.lsp" || exit 2
h4_acl2 < "$tmp/session.lsp" > "$tmp/log" 2>&1
status=$?
write_values || exit 2
if [ "$status" -ne 0 ] || [ "$(grep -Fxc 'prover-run-finished 0' "$tmp/log")" -ne "$#" ]; then
    if [ "$status" -ne 0 ]; then
        cat "$tmp/log" >&2
    else
        awk '/ACL2 Error|^prover-run:|^HARD ACL2 ERROR/ { print; show=1; next }
             !NF { show=0 } show' "$tmp/log" >&2
    fi
    echo "prover/h4/acl2-run.sh: ACL2 did not give a value for every term (status $status)." >&2
    exit 1
fi
