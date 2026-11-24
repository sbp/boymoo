# Certify successive copied H3 books in one ACL2 session.
# The first argument names the certified book before the first source.

dependency=$1
shift
work=build/prover/h3
dir=build/prover/acl2/h3
for last do
    :
done
: > "$work/certify.out" || exit 2
{
    printf "(set-ld-error-action '(:exit 1) state)\n"
    printf "(set-inhibit-output-lst '(proof-tree prove observation event history warning))\n"
    printf '(ld "prover/package.lsp" :ld-error-action :error)\n'
    for book do
        printf '(cw "~%%h3-certify-begin %s~%%")\n' "$book"
        printf '(include-book "%s" :uncertified-okp nil)\n' "$dependency"
        printf '(certify-book "%s/%s" 2 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$dir" "$book"
        printf '(cw "~%%h3-certify-done %s~%%")\n' "$book"
        # Keep the package and restore the two-command world for the next book.
        [ "$book" = "$last" ] || printf '(ubt 2)\n'
        dependency=$dir/$book
    done
    printf '(good-bye)\n'
} > "$work/certify.in" || exit 2

timeout --foreground --verbose -k 10 1800 sh prover/tools/acl2.sh \
    < "$work/certify.in" > "$work/certify.out" 2>&1
status=$?
awk -v dir="$dir" -v first="$1" '
    BEGIN { file = dir "/" first ".out" }
    /^h3-certify-begin / {
        if (file != dir "/" $2 ".out") {
            close(file)
            file = dir "/" $2 ".out"
        }
    }
    { print > file }
' "$work/certify.out" || exit 2
exit "$status"
