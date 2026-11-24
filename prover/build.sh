# Certifies the books through LAST-BOOK in prover/ORDER and exports that prefix.
# Run from the root of the repository with sh prover/build.sh [LAST-BOOK].
# The default is the whole order. A missing source or a failed certification
# stops the build and gives status 1 after exporting the last certified book.

if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/build.sh [LAST-BOOK]' >&2
    exit 2
fi
books=$(cat prover/ORDER) || exit 2
target=${1-$(printf '%s\n' "$books" | awk 'END { print }')}
if ! grep -Fxq -- "$target" prover/ORDER; then
    echo "prover/build.sh: $target is not a book in prover/ORDER" >&2
    exit 2
fi

work=build/prover
dir=$work/acl2
mkdir -p "$dir" || exit 2
stale=0
if ! cmp -s prover/package.lsp "$dir/package.lsp"; then
    cp prover/package.lsp "$dir/package.lsp" || exit 2
    stale=1
fi

previous=
stopped=
for book in $books; do
    source=prover/$book.lisp
    copy=$dir/$book.lisp
    cert=$dir/$book.cert
    if [ ! -f "$source" ]; then
        stopped="missing $source"
        break
    fi
    if ! cmp -s "$source" "$copy"; then
        rm -f "$cert" || exit 2
        cp "$source" "$copy" || exit 2
        stale=1
    fi
    if [ "$stale" -eq 1 ] || [ ! -f "$cert" ] ||
       [ "$copy" -nt "$cert" ] || [ "$dir/package.lsp" -nt "$cert" ] ||
       { [ -n "$previous" ] && [ "$dir/$previous.cert" -nt "$cert" ]; }; then
        stale=1
        rm -f "$cert" || exit 2
        {
            printf "(set-ld-error-action '(:exit 1) state)\n"
            printf "(set-inhibit-output-lst '(proof-tree prove observation event history))\n"
            printf '(ld "%s/package.lsp" :ld-error-action :error)\n' "$dir"
            commands=1
            if [ -n "$previous" ]; then
                printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$dir" "$previous"
                commands=2
            fi
            printf '(certify-book "%s/%s" %d :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' \
                "$dir" "$book" "$commands"
            printf '(good-bye)\n'
        } > "$dir/certify.in" || exit 2
        if [ -n "${PROVER_CERT_SECONDS-}" ]; then
            timeout -k 5 "$PROVER_CERT_SECONDS" sh prover/tools/acl2.sh \
                < "$dir/certify.in" > "$dir/$book.out" 2>&1
        else
            sh prover/tools/acl2.sh < "$dir/certify.in" > "$dir/$book.out" 2>&1
        fi
        status=$?
        if [ "$status" -ne 0 ] || [ ! -f "$cert" ]; then
            rm -f "$cert" || exit 2
            printf '%s\n' "$status" > "$dir/$book.failed"
            stopped="ACL2 could not certify $source (see $dir/$book.out)"
            break
        fi
        rm -f "$dir/$book.failed" "$dir/$book.failure"
    fi
    previous=$book
    [ "$book" != "$target" ] || break
done

printf '%s\n' "$previous" > "$work/certified.new" &&
    mv "$work/certified.new" "$work/certified" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    printf '\n' > "$work/exported"
    exit 1
fi

out=build/export/books/$dir/$previous
export_ok() {
    [ -s "$out.statements" ] && [ -f "$out.program" ] && [ -s "$out.readback" ] &&
        awk '/^\(readback / { count++ }
             { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
             END { exit (count != 2 || NR < 6 || bad) }' "$out.readback"
}
if [ "$dir/$previous.cert" -nt "$out.program" ] || ! export_ok; then
    sh export/book.sh "$dir/$previous"
    status=$?
    if [ "$status" -ne 0 ] || ! export_ok; then
        printf '\n' > "$work/exported"
        echo "prover/build.sh: certified through $previous; export failed (see $out.log)" >&2
        exit 1
    fi
fi
printf '%s\n' "$previous" > "$work/exported.new" &&
    mv "$work/exported.new" "$work/exported" || exit 2
echo "prover/build.sh: certified and exported through $previous"
[ -z "$stopped" ]
