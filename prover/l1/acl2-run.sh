#!/bin/sh
# From the repository root, run sh prover/l1/acl2-run.sh [-v] [BOOK].
# Reads the same terms as run.sh. With -v, evaluation CPU time goes to standard error.

. prover/l1/tools/artifacts.sh || exit 2
stats=
if [ "${1-}" = -v ]; then
    stats=yes
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/l1/acl2-run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-$(cat "$l1_work/certified" 2>/dev/null)}
if ! l1_certified "$book"; then
    echo 'prover/l1/acl2-run.sh: name a book certified by sh prover/l1/build.sh' >&2
    exit 2
fi

tmp=$l1_work/acl2-run.$$
mkdir "$tmp" || exit 2
trap 'rm -f "$tmp/terms" "$tmp/session" "$tmp/log" "$tmp/values"; rmdir "$tmp"' 0
trap '[ ! -f "$tmp/values" ] || cat "$tmp/values"; exit 143' HUP INT TERM
cat > "$tmp/terms" || exit 2
{
    printf "(set-ld-error-action '(:exit 1) state)\n"
    printf '(ld "%s" :ld-error-action :error)\n' "$l1_package"
    printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$l1_acl2" "$book"
    if [ -s build/export/acl2/canon.cert ] && cmp -s checks/canon.lisp build/export/acl2/canon.lisp; then
        printf '%s\n' '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
    else
        printf '%s\n' '(ld "checks/canon.lsp" :ld-error-action :error)'
    fi
    printf '%s\n' '(ld "export/readback.lsp" :ld-error-action :error)' \
        '(ld "prover/tools/acl2-run.lsp" :ld-error-action :error)'
    printf '(prover-run-file "%s/terms" "%s/values" state)\n' "$tmp" "$tmp"
    printf '%s\n' '(good-bye)'
} > "$tmp/session" || exit 2
sh prover/tools/acl2.sh < "$tmp/session" > "$tmp/log" 2>&1
status=$?
[ ! -f "$tmp/values" ] || cat "$tmp/values" || exit 2
if [ -n "$stats" ]; then
    sed -n 's/^prover-run-cpu /prover\/l1\/acl2-run.sh: evaluation CPU seconds /p' "$tmp/log" >&2
fi
if [ "$status" -ne 0 ] || ! grep -Fxq 'prover-run-finished 0' "$tmp/log"; then
    if [ "$status" -ne 0 ]; then
        cat "$tmp/log" >&2
    else
        awk '/ACL2 Error|^prover-run:|^HARD ACL2 ERROR/ { print; show=1; next }
             !NF { show=0 } show' "$tmp/log" >&2
    fi
    echo "prover/l1/acl2-run.sh: ACL2 did not give a value for every term (status $status)" >&2
    exit 1
fi
