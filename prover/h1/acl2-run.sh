# Run the canonical terms accepted by prover/h1/run.sh inside ACL2.
# Use sh prover/h1/acl2-run.sh [-v] [BOOK]. With -v, report evaluation CPU seconds.
# BOOK defaults to the last certified prefix. A failed term prints "no value".

. prover/h1/tools/artifacts.sh || exit 2
stats=
if [ "${1-}" = -v ]; then
    stats=yes
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h1/acl2-run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-}
if [ "$#" -eq 0 ] && [ -s "$h1_work/certified" ]; then
    book=$(cat "$h1_work/certified") || exit 2
fi
if ! h1_has_book "$book" || ! h1_certified "$book"; then
    echo 'prover/h1/acl2-run.sh: name a book certified by sh prover/h1/build.sh' >&2
    exit 2
fi

mkdir -p "$h1_work/tmp" || exit 2
tmp=$h1_work/tmp/acl2-run.$$
mkdir "$tmp" || exit 2
trap 'rm -rf "$tmp"' 0
trap '[ ! -f "$tmp/values" ] || cat "$tmp/values"; exit 143' 1 2 15
TMPDIR=$PWD/$h1_work/tmp
export TMPDIR
cat > "$tmp/terms" || exit 2
{
    echo "(set-ld-error-action '(:exit 1) state)"
    printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$h1_acl2" "$book"
    if [ -s build/export/acl2/canon.cert ] && cmp -s checks/canon.lisp build/export/acl2/canon.lisp; then
        echo '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
    else
        echo '(ld "checks/canon.lsp" :ld-error-action :error)'
    fi
    echo '(ld "export/readback.lsp" :ld-error-action :error)'
    echo '(ld "prover/tools/acl2-run.lsp" :ld-error-action :error)'
    printf '(prover-run-file "%s/terms" "%s/values" state)\n' "$tmp" "$tmp"
    echo '(good-bye)'
} > "$tmp/session.lsp" || exit 2
sh prover/tools/acl2.sh < "$tmp/session.lsp" > "$tmp/log" 2>&1
status=$?
[ ! -f "$tmp/values" ] || cat "$tmp/values" || exit 2
if [ -n "$stats" ]; then
    sed -n 's/^prover-run-cpu /evaluation CPU seconds /p' "$tmp/log" >&2
fi
if [ "$status" -ne 0 ] || ! grep -Fxq 'prover-run-finished 0' "$tmp/log"; then
    if [ "$status" -ne 0 ]; then
        cat "$tmp/log" >&2
    else
        awk '/ACL2 Error|^prover-run:|^HARD ACL2 ERROR/ { print; show=1; next }
             !NF { show=0 } show' "$tmp/log" >&2
    fi
    echo "prover/h1/acl2-run.sh: ACL2 did not give a value for every term (status $status)" >&2
    exit 1
fi
