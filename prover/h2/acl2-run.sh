# From the repository root, use sh prover/h2/acl2-run.sh [-v] [BOOK].
# Reads the same terms as run.sh. BOOK defaults to the last certified prefix.
# With -v, writes evaluation CPU seconds to standard error.

. prover/h2/tools/artifacts.sh || exit 2
stats=
if [ "${1-}" = -v ]; then
    stats=yes
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h2/acl2-run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-$(cat "$h2_work/certified" 2>/dev/null)}
if ! grep -Fxq -- "$book" "$h2_order" || ! h2_certified "$book"; then
    echo 'prover/h2/acl2-run.sh: select a book certified by sh prover/h2/build.sh' >&2
    exit 2
fi

tmp=$h2_work/acl2-run.$$
mkdir -p "$h2_work/tmp" && mkdir "$tmp" || exit 2
values() {
    for file in "$tmp"/values.*; do
        if [ -f "$file" ]; then
            cat "$file" || return 2
        fi
    done
}
timings() {
    if [ -n "$stats" ] && [ -f "$tmp/log" ]; then
        sed -n 's/^prover-run-cpu /prover\/h2\/acl2-run.sh: evaluation CPU seconds /p' "$tmp/log" >&2
    fi
}
trap 'rm -rf "$tmp"' 0
trap 'values; timings; exit 143' 1 2 15
TMPDIR=$PWD/$h2_work/tmp
export TMPDIR
# Close each value file when the call returns, even within a shared session.
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
    printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$h2_acl2" "$book"
    if [ -s build/export/acl2/canon.cert ] && cmp -s checks/canon.lisp build/export/acl2/canon.lisp; then
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
sh prover/tools/acl2.sh < "$tmp/session.lsp" > "$tmp/log" 2>&1
status=$?
values || exit 2
timings
if [ "$status" -ne 0 ] || [ "$(grep -Fxc 'prover-run-finished 0' "$tmp/log")" -ne "$#" ]; then
    awk '/ACL2 Error|^prover-run:|HARD ACL2 ERROR|^Error: |fatal error/ { show=1 }
         !NF { show=0 } show' "$tmp/log" >&2
    echo "prover/h2/acl2-run.sh: ACL2 did not give a value for every term (status $status)" >&2
    exit 1
fi
