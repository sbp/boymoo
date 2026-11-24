# Export a certified H2 book into its build directory.

. prover/h2/tools/artifacts.sh || exit 2
book=$1
staged=$2/$book
out=$h2_exports/$book
if [ ! -s build/export/acl2/guards.cert ] || [ ! -s build/export/ground-fns.lsp ]; then
    echo 'prover/h2/tools/export.sh: the certified exporter and ground functions are required' >&2
    exit 2
fi

{
    printf '%s\n' '(in-package "ACL2")' '(ld "checks/version.lsp")' \
        "(set-ld-error-action '(:exit 1) state)" \
        "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))" \
        '(assign bx-boot-hi (max-absolute-event-number (w state)))'
    printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$h2_acl2" "$book"
    printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))' \
        '(ld "build/export/ground-fns.lsp")' \
        '(include-book "build/export/acl2/canon")' \
        '(include-book "build/export/acl2/guards")' \
        '(ld "export/export.lsp")' '(set-inhibit-output-lst nil)' '(set-guard-checking t)'
    printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi) (@ bx-hi) "%s" state)\n' "$staged"
    printf '%s\n' '(ld "export/readback.lsp")'
    printf '(rb-readback "%s" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)\n' "$staged"
    printf '%s\n' '(good-bye)'
} > "$2/export.in" || exit 2
timeout --foreground -k 15 1800 sh prover/tools/acl2.sh < "$2/export.in" > "$out.log" 2>&1 || exit $?
for suffix in statements program aids notes readback; do
    [ -f "$staged.$suffix" ] || exit 1
done
for suffix in statements program aids notes readback; do
    mv "$staged.$suffix" "$out.$suffix" || exit 1
done
