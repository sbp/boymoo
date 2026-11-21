#!/bin/sh
# From the repository root, certify the round-trip books and run their
# tests with ACL2 8.7. The logs and certificates are in build/export/acl2.

dir=build/export/acl2
books='base read round-trip-text round-trip-numbers round-trip-symbols round-trip-atoms round-trip round-trip-lexical round-trip-packages round-trip-converse round-trip-native'
tests='certificates printer-guards startup-world line-feed empty-table-keys noncanonical-text acl2-package-imports native-import-conflict world-with-books hidden-reader-package'

fail() {
    printf 'FAIL %s\n' "$1"
    echo 'round-trip checks failed'
    exit 1
}

sh export/certify.sh || fail 'canon or core'
echo 'ok canon'
echo 'ok core'

cp checker/package.lsp checks/version.lsp "$dir/" || fail 'certification inputs'

for book in $books; do
    case $book in
        base|read) source=checker/$book.lisp ;;
        *) source=export/proofs/$book.lisp ;;
    esac
    cp "$source" "$dir/$book.lisp" || fail "$book"
    rm -f "$dir/$book.cert" || fail "$book"
    (
        cd "$dir" || exit 1
        printf '(ld "version.lsp")\n(ld "package.lsp")\n(certify-book "%s" 1 nil :defaxioms-okp nil :skip-proofs-okp nil :ttags nil)\n' "$book" |
            timeout 1800 acl2 > "$book.out" 2>&1
    ) && [ -f "$dir/$book.cert" ] || fail "$book (see $dir/$book.out)"
    seconds=$(awk '/^Time: / { seconds = $2 } END { print seconds }' "$dir/$book.out")
    printf 'ok %s (%s seconds)\n' "$book" "$seconds"
done

log=round-trip-tests.out
cp export/proofs/round-trip-tests.lsp "$dir/" || fail 'test input'
(
    cd "$dir" || exit 1
    printf '(ld "round-trip-tests.lsp" :ld-error-action :error)\n(good-bye)\n' |
        timeout 1800 acl2 > "$log" 2>&1
) || fail "ACL2 tests (see $dir/$log)"

for test in $tests; do
    grep -a -x -q "ROUND-TRIP-OK $test" "$dir/$log" || fail "$test (see $dir/$log)"
    printf 'ok %s\n' "$test"
done

echo 'all round-trip checks passed'
