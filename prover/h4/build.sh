#!/bin/sh
# Certify an H4 book and its dependencies, then export it for the runner.
set -eu
. prover/h4/tools/run-book.sh

fail() {
    printf 'prover/h4/build.sh: %s\n' "$*" >&2
    exit 1
}

if [ "${1-}" = -- ]; then shift; fi
[ "$#" -le 1 ] || fail 'usage: sh prover/h4/build.sh [BOOK]'
last=${1:-$(tail -n 1 "$h4_source/ORDER")}
grep -Fxq -- "$last" "$h4_source/ORDER" || fail "unknown book $last"
for dependency in "$h4_shared/descent.cert" prover/package.lsp \
                  build/export/ground-fns.lsp build/export/acl2/canon.cert \
                  build/export/acl2/guards.cert; do
    [ -s "$dependency" ] || fail "missing $dependency"
done

mkdir -p "$h4_books" "$h4_exports"
lock=$h4_work/building
mkdir "$lock" || fail 'an H4 build is already in progress'
trap 'rm -rf "$lock"' 0
trap 'exit 1' HUP INT TERM

pending=$lock/pending
forms=$lock/certify.lsp
: > "$pending"
{
    printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
    printf '%s\n' "(set-inhibit-output-lst '(proof-tree prove observation event history warning warning!))"
    printf '%s\n' '(ld "prover/package.lsp" :ld-error-action :error)'
} > "$forms"
previous=$h4_shared/descent
while IFS= read -r book; do
    source=$h4_source/$book.lisp
    staged=$h4_books/$book
    [ -s "$source" ] || fail "missing $source"
    if [ -s "$pending" ] || [ ! -s "$staged.cert" ] ||
       [ "$previous.cert" -nt "$staged.cert" ] || [ prover/package.lsp -nt "$staged.cert" ] ||
       [ "$staged.lisp" -nt "$staged.cert" ] || ! cmp -s "$source" "$staged.lisp"; then
        rm -f "$staged.cert"
        if ! cmp -s "$source" "$staged.lisp"; then
            cp "$source" "$staged.lisp"
        fi
        {
            printf '(cw "~%%h4-certification-start %s~%%")\n' "$book"
            if [ -s "$pending" ]; then printf '%s\n' '(ubt! 2)'; fi
            printf '(include-book "%s" :uncertified-okp nil)\n' "$previous"
            printf '(certify-book "%s" 2 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$staged"
            printf '(cw "~%%h4-certification-done %s~%%")\n' "$book"
        } >> "$forms"
        printf '%s\n' "$book" >> "$pending"
    fi
    [ "$book" != "$last" ] || break
    previous=$staged
done < "$h4_source/ORDER"
if [ -s "$pending" ]; then
    printf '%s\n' '(good-bye)' >> "$forms"
    log=$h4_work/certify.log
    if ! h4_acl2 < "$forms" > "$log" 2>&1; then
        fail "certification failed. See $log."
    fi
    while IFS= read -r book; do
        if [ ! -s "$h4_books/$book.cert" ] || ! grep -Fxq "h4-certification-done $book" "$log"; then
            fail "certification stopped at $book. See $log."
        fi
    done < "$pending"
fi
printf '%s\n' "$last" > "$lock/certified"
mv "$lock/certified" "$h4_work/certified"

out=$h4_exports/$last
cert=$h4_books/$last.cert
if ! h4_export_current "$out" "$cert"; then
    prefix=$lock/program
    forms=$lock/export.lsp
    log=$h4_work/export.log
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
        printf '%s\n' "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
        printf '%s\n' '(assign bx-boot-hi (max-absolute-event-number (w state)))'
        printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$h4_books" "$last"
        printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))'
        printf '%s\n' '(ld "build/export/ground-fns.lsp")'
        printf '%s\n' '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
        printf '%s\n' '(include-book "build/export/acl2/guards" :uncertified-okp nil)'
        printf '%s\n' '(ld "export/export.lsp")' '(set-guard-checking t)'
        printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi) (@ bx-hi) "%s" state)\n' "$prefix"
        printf '%s\n' '(ld "export/readback.lsp")'
        printf '(rb-readback "%s" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)\n' "$prefix"
        printf '%s\n' '(good-bye)'
    } > "$forms"
    if ! h4_acl2 < "$forms" > "$log" 2>&1 || ! h4_export_current "$prefix" "$cert"; then
        fail "export failed. See $log."
    fi
    for suffix in statements aids notes readback program; do
        mv "$prefix.$suffix" "$out.$suffix"
    done
fi
printf '%s\n' "$last" > "$lock/exported"
mv "$lock/exported" "$h4_work/exported"
printf 'Certified and exported through %s.\n' "$last"
