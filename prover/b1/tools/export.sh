# Export one certified B1 book and check its readback counts.
set -eu
. prover/b1/tools/artifacts.sh

book=$1
work=$2
output=$work/export
for dependency in ground-fns.lsp acl2/canon.cert acl2/guards.cert; do
    if [ ! -s "build/export/$dependency" ]; then
        printf 'prover/b1/tools/export.sh: missing build/export/%s\n' "$dependency" >&2
        exit 1
    fi
done

{
    printf '%s\n' '(ld "checks/version.lsp")'
    printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
    printf '%s\n' "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
    printf '%s\n' '(assign bx-boot-hi (max-absolute-event-number (w state)))'
    printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$b1_books" "$book"
    printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))'
    printf '%s\n' '(ld "build/export/ground-fns.lsp")'
    printf '%s\n' '(include-book "build/export/acl2/canon")' '(include-book "build/export/acl2/guards")'
    printf '%s\n' '(ld "export/export.lsp")' '(set-guard-checking t)'
    printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi) (@ bx-hi) "%s" state)\n' "$output"
    printf '%s\n' '(ld "export/readback.lsp")'
    printf '%s\n' '(value-triple #+sbcl (gc$ :full t) #-sbcl (gc$))'
    printf '(rb-readback "%s" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)\n' "$output"
    printf '%s\n' '(good-bye)'
} > "$work/export.in"

log=$b1_exports/$book.log
if ! timeout --foreground -k 15 1800 sh prover/tools/acl2.sh < "$work/export.in" > "$log" 2>&1 ||
   [ ! -s "$output.statements" ] || [ ! -f "$output.program" ] ||
   [ ! -s "$output.readback" ] || ! b1_readback_ok "$output.readback"; then
    exit 1
fi
for suffix in aids notes statements program readback; do
    mv "$output.$suffix" "$b1_exports/$book.$suffix"
done
