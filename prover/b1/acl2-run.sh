# Evaluate the canonical terms accepted by prover/b1/run.sh in ACL2.
# From the repository root, run sh prover/b1/acl2-run.sh [-v] [BOOK].
# BOOK defaults to the last certificate. With -v print evaluation CPU time.

. prover/b1/tools/artifacts.sh

stats=
if [ "${1-}" = -v ]; then
    stats=yes
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/b1/acl2-run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-}
if [ "$#" -eq 0 ] && [ -f "$b1_work/certified" ]; then
    read -r book < "$b1_work/certified"
fi
if ! b1_certified "$book"; then
    echo 'prover/b1/acl2-run.sh: name a book certified by sh prover/b1/build.sh' >&2
    exit 2
fi
b1_tempdir || exit 2

tmp=$b1_work/acl2-run.$$
mkdir "$tmp" || exit 2
trap 'rm -rf "$tmp"' 0
trap '[ ! -f "$tmp/values" ] || cat "$tmp/values"; exit 143' 1 2 15
cat > "$tmp/terms" || exit 2
{
    echo "(set-ld-error-action '(:exit 1) state)"
    printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$b1_books" "$book"
    if [ -s build/export/acl2/canon.cert ] &&
       cmp -s checks/canon.lisp build/export/acl2/canon.lisp; then
        echo '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
    else
        echo '(ld "checks/canon.lsp" :ld-error-action :error)'
    fi
    echo '(ld "export/readback.lsp" :ld-error-action :error)'
    echo '(ld "prover/tools/acl2-run.lsp" :ld-error-action :error)'
    printf '(prover-run-file "%s/terms" "%s/values" state)\n' "$tmp" "$tmp"
    echo '(good-bye)'
} > "$tmp/session.lsp" || exit 2

timeout --foreground -k 15 1800 sh prover/tools/acl2.sh < "$tmp/session.lsp" > "$tmp/log" 2>&1
status=$?
[ ! -f "$tmp/values" ] || cat "$tmp/values" || exit 2
if [ -n "$stats" ]; then
    sed -n 's/^prover-run-cpu /prover\/b1\/acl2-run.sh: evaluation CPU seconds /p' "$tmp/log" >&2
fi
if [ "$status" -ne 0 ] || ! grep -Fxq 'prover-run-finished 0' "$tmp/log"; then
    awk '{ lines[NR % 80] = $0 }
         END {
             first = (NR > 80) ? NR - 79 : 1
             for (line = first; line <= NR; line++) print lines[line % 80]
         }' "$tmp/log" >&2
    echo "prover/b1/acl2-run.sh: ACL2 did not give a value for every term (status $status)" >&2
    exit 1
fi
