# Evaluate the canonical terms accepted by prover/t3/run.sh in ACL2.
# Run from the repository root with sh prover/t3/acl2-run.sh [-v] [BOOK].

. prover/t3/tools/artifacts.sh

stats=
if [ "${1-}" = -v ]; then
    stats=yes
    shift
fi
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/t3/acl2-run.sh [-v] [BOOK]' >&2
    exit 2
fi
book=${1-}
if [ "$#" -eq 0 ] && [ -f "$t3_work/certified" ]; then
    IFS= read -r book < "$t3_work/certified"
fi
if ! t3_certified "$book"; then
    echo 'prover/t3/acl2-run.sh: name a book certified by sh prover/t3/build.sh' >&2
    exit 2
fi

tmp=$t3_work/acl2-run.$$
mkdir "$tmp" || exit 2
print_values() {
    for values in "$tmp"/values.*; do
        [ ! -f "$values" ] || cat "$values" || return 1
    done
}
print_cpu() {
    if [ -n "$stats" ] && [ -f "$tmp/log" ]; then
        awk '/^prover-run-cpu / { print "prover/t3/acl2-run.sh: evaluation CPU seconds", $2 }' "$tmp/log" >&2
    fi
}
trap 'rm -rf "$tmp"' 0
trap 'print_values; print_cpu; exit 143' 1 2 15
ulimit -f 48000 || exit 2
# Small input files share one ACL2 session and one set of loaded books.
awk -v directory="$tmp" '
    { file = sprintf("%s/terms.%08d", directory, int((NR - 1) / 5)) }
    file != previous { if (previous != "") close(previous); previous = file }
    { print > file }
' || exit 2
[ -f "$tmp/terms.00000000" ] || exit 0
chunks=0
{
    printf "(set-ld-error-action '(:exit 1) state)\n"
    printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$t3_acl2" "$book"
    if [ -s build/export/acl2/canon.cert ] && cmp -s checks/canon.lisp build/export/acl2/canon.lisp; then
        printf '(include-book "build/export/acl2/canon" :uncertified-okp nil)\n'
    else
        printf '(ld "checks/canon.lsp" :ld-error-action :error)\n'
    fi
    printf '(ld "export/readback.lsp" :ld-error-action :error)\n'
    printf '(ld "prover/tools/acl2-run.lsp" :ld-error-action :error)\n'
    for terms in "$tmp"/terms.*; do
        chunks=$((chunks + 1))
        printf '(prover-run-file "%s" "%s/values.%s" state)\n' "$terms" "$tmp" "${terms##*.}"
    done
    printf '(good-bye)\n'
} > "$tmp/session.lsp" || exit 2
timeout --foreground -k 15 "$t3_limit" sh prover/tools/acl2.sh \
    < "$tmp/session.lsp" > "$tmp/log" 2>&1
status=$?
print_values || exit 2
print_cpu
finished=$(awk '/^prover-run-finished 0$/ { count++ } END { print count + 0 }' "$tmp/log")
if [ "$status" -ne 0 ] || [ "$finished" -ne "$chunks" ]; then
    cat "$tmp/log" >&2
    echo "prover/t3/acl2-run.sh: ACL2 did not give a value for every term (status $status)" >&2
    exit 1
fi
