#!/bin/sh
# Certify the faithfulness books and run the world and counterexample
# tests from the root of the repository.

dir=build/export/acl2
books='faithful-origin faithful-routing faithful-kinds faithful-definitions
faithful-world faithful-packages faithful-choice faithful-conjuncts
faithful-constraints faithful-candidates faithful-constraint-names
faithful-constraint-outcomes faithful-reserve faithful-label-spelling faithful-generated-names
faithful-program-data faithful-program-items faithful-program faithful-attachments'

failed=0
if ! sh export/certify.sh; then
    echo 'exporter prerequisites failed'
    echo 'some faithfulness checks failed'
    exit 1
fi

# Read the annotation record from the certificate file. The three
# entries must be present, with no skips, axioms, or trust tags.
certificate_check() {
    printf '%s\n' \
        "(mv-let (erp pair state)" \
        "  (cert-annotations-and-checksum-from-cert-file \"$dir/$1.lisp\" state)" \
        "  (if (and (not erp) (equal (car pair) '((:skipped-proofsp) (:axiomsp) (:ttags))))" \
        "      (prog2$ (cw \"~%faithful certificate ok~%\") (value :ok))" \
        "    (prog2$ (cw \"~%faithful certificate failed~%\") (value :failed))))"
}

for book in $books; do
    if ! cp "export/proofs/$book.lisp" "$dir/$book.lisp" ||
       ! rm -f "$dir/$book.cert"; then
        echo "$book failed to prepare"
        failed=1
        continue
    fi
    {
        echo '(ld "checks/version.lsp")'
        portcullis=0
        if [ "$book" = faithful-label-spelling ]; then
            # ACL2 reads the packages in the string lemmas and their certificates.
            for packages in std/portcullis data-structures/portcullis; do
                printf '(include-book "%s" :dir :system :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$packages"
            done
            portcullis=2
        fi
        printf '(certify-book "%s/%s" %s :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' "$dir" "$book" "$portcullis"
        certificate_check "$book"
        echo '(good-bye)'
    } | timeout -k 5 1800 acl2 > "$dir/$book.out" 2>&1
    if [ "$?" -eq 0 ] && [ -f "$dir/$book.cert" ] &&
       grep -Fxq 'faithful certificate ok' "$dir/$book.out"; then
        seconds=$(awk '/^Time:/ {seconds=$2} END {print seconds}' "$dir/$book.out")
        echo "$book ok ($seconds s)"
    else
        echo "$book failed (see $dir/$book.out)"
        failed=1
    fi
done

log=$dir/faithful-tests.out
if [ "$failed" -eq 0 ]; then
    names=$(sed -n 's/^(define [^ (][^ ]* (\([^ ]*\) .*/\1/p; s/^(define ([^()]*) (\([^ ]*\) .*/\1/p' spec/ground.txt |
                tr '\n' ' ')
    {
        echo '(ld "checks/version.lsp")'
        printf "(assign faithful-ground-fns '(%s))\n" "$names"
        cat export/proofs/faithful-tests.lsp export/proofs/faithful-outcome-tests.lsp \
            export/proofs/faithful-counterexamples.lsp
        echo '(good-bye)'
    } | timeout -k 5 1800 acl2 > "$log" 2>&1
    tested=$?
    if grep -q '^ACL2 Error' "$log"; then
        tested=1
    fi
else
    tested=1
fi

while IFS= read -r test; do
    if [ "$tested" -eq 0 ] && grep -Fxq "faithful-test: $test ok" "$log"; then
        echo "$test ok"
    else
        echo "$test failed (see $log)"
        failed=1
    fi
done <<'TESTS'
initial world
world with hidden packages
world with defpun
world with alist-equiv
world with abstract stobjs
world with dft-ex
world with statement and program examples
library statement data
library constraint outcomes
library program data
book statement data
book constraint outcomes
book program data
constraint with guard holders
strengthened nullary choice
constraint label exhaustion
library constraint label exhaustion
constraint labels and deferred definitions
definition equation of a constraint sibling
unlisted constrained functions
library axiom outside the ground theory
imported constraint label passed over
different ruler-extenders
nested constraint shares a generated label
TESTS

if [ "$failed" -eq 0 ]; then
    echo 'all faithfulness checks passed'
else
    echo 'some faithfulness checks failed'
fi
exit "$failed"
