# Evaluate the canonical terms accepted by prover/t2/run.sh inside ACL2.
# From the repository root, run sh prover/t2/acl2-run.sh [-v] [BOOK] after the build.
# BOOK defaults to the last certified book. The -v flag prints evaluation CPU time.

. prover/t2/tools/artifacts.sh

stats=
if [ "${1-}" = -v ]; then
    stats=yes
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/t2/acl2-run.sh [-v] [BOOK]' >&2
    exit 2
fi

book=${1-}
if [ "$#" -eq 0 ] && [ -s "$t2_work/certified" ]; then
    IFS= read -r book < "$t2_work/certified"
fi
if ! t2_certified "$book" snapshot; then
    echo 'prover/t2/acl2-run.sh: name a book certified by sh prover/t2/build.sh' >&2
    exit 2
fi

scratch=$t2_work/acl2-run.$$
mkdir "$scratch" || exit 2
trap 'rm -rf "$scratch"' 0
trap 'exit 143' 1 2 15
cat > "$scratch/terms" || exit 2
{
    echo "(set-ld-error-action '(:exit 1) state)"
    printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$t2_acl2" "$book"
    if [ -s build/export/acl2/canon.cert ] && cmp -s checks/canon.lisp build/export/acl2/canon.lisp; then
        echo '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
    else
        echo '(ld "checks/canon.lsp" :ld-error-action :error)'
    fi
    echo '(ld "export/readback.lsp" :ld-error-action :error)'
    echo '(ld "prover/tools/acl2-run.lsp" :ld-error-action :error)'
    printf '(prover-run-file "%s/terms" "%s/values" state)\n' "$scratch" "$scratch"
    echo '(good-bye)'
} > "$scratch/session.in" || exit 2

sh prover/t2/build.sh --run-acl2 "${T2_CALL_SECONDS:-1800}" \
    < "$scratch/session.in" > "$scratch/session.out" 2>&1
status=$?
[ ! -f "$scratch/values" ] || cat "$scratch/values" || exit 2
if [ -n "$stats" ]; then
    sed -n 's/^prover-run-cpu /prover\/t2\/acl2-run.sh: evaluation CPU seconds /p' "$scratch/session.out" >&2
fi
if [ "$status" -ne 0 ] || ! grep -Fxq 'prover-run-finished 0' "$scratch/session.out"; then
    awk '{ lines[NR % 80] = $0 }
         END { for (i = (NR > 80 ? NR - 79 : 1); i <= NR; i++) print lines[i % 80] }' \
        "$scratch/session.out" >&2
    echo "prover/t2/acl2-run.sh: ACL2 did not give a value for every term (status $status)" >&2
    [ "$status" -eq 0 ] || exit "$status"
    exit 1
fi
