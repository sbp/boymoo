# Run from the repository root with sh prover/h3/acl2-run.sh [-v] [BOOK].
# Reads the same terms as prover/h3/run.sh. With -v it reports evaluation
# CPU time on standard error.

stats=
if [ "${1-}" = -v ]; then
    stats=yes
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h3/acl2-run.sh [-v] [BOOK]' >&2
    exit 2
fi
work=build/prover/h3
last=$(if [ -r "$work/certified" ]; then cat "$work/certified"; fi)
book=${1-$last}
base=build/prover/acl2/h3/$book
if ! awk -v book="$book" -v last="$last" '
    $0 == book { wanted = NR }
    $0 == last { certified = NR }
    END { exit !(wanted && certified && wanted <= certified) }
' prover/h3/ORDER || [ ! -f "$base.cert" ]; then
    echo 'prover/h3/acl2-run.sh: run sh prover/h3/build.sh to certify a book' >&2
    exit 2
fi

tmp=$work/acl2-run.$$
mkdir "$tmp" || exit 2
values() {
    for file in "$tmp"/values.*; do
        if [ -f "$file" ]; then
            cat "$file" || return 2
        fi
    done
}
timings() {
    if [ -n "$stats" ] && [ -f "$tmp/log" ]; then
        sed -n 's/^prover-run-cpu /prover\/h3\/acl2-run.sh: evaluation CPU seconds /p' "$tmp/log" >&2
    fi
}
trap 'rm -rf "$tmp"' 0
trap 'values; timings; exit 143' 1 2 15

# Use a single ACL2 session and close each call's output as soon as it returns.
awk -v dir="$tmp" '
    {
        file = sprintf("%s/terms.%08d", dir, NR)
        print > file
        close(file)
    }
    END { if (!NR) printf "" > (dir "/terms.00000001") }
' || exit 2
set -- "$tmp"/terms.*
{
    echo "(set-ld-error-action '(:exit 1) state)"
    printf '(include-book "%s" :uncertified-okp nil)\n' "$base"
    if [ -f build/export/acl2/canon.cert ] &&
       cmp -s checks/canon.lisp build/export/acl2/canon.lisp; then
        echo '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
    else
        echo '(ld "checks/canon.lsp" :ld-error-action :error)'
    fi
    echo '(ld "export/readback.lsp" :ld-error-action :error)'
    echo '(ld "prover/tools/acl2-run.lsp" :ld-error-action :error)'
    for input do
        printf '(prover-run-file "%s" "%s/values.%s" state)\n' "$input" "$tmp" "${input##*.}"
    done
    echo '(good-bye)'
} > "$tmp/session.lsp" || exit 2
SBCL_USER_ARGS=${SBCL_USER_ARGS-'--dynamic-space-size 1500'} \
    sh prover/tools/acl2.sh < "$tmp/session.lsp" > "$tmp/log" 2>&1
status=$?
values || exit 2
timings
if [ "$status" -ne 0 ] || [ "$(grep -Fxc 'prover-run-finished 0' "$tmp/log")" -ne "$#" ]; then
    awk '/ACL2 Error|^prover-run:|HARD ACL2 ERROR|fatal error|^Error: / { show=1 }
         !NF { show=0 } show' "$tmp/log" >&2
    echo "prover/h3/acl2-run.sh: ACL2 did not give a value for every term (status $status)" >&2
    exit 1
fi
