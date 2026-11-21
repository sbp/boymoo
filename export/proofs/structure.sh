#!/bin/sh
# Run from the repository root with ACL2 8.7 and the tools in DETAILS.md.
# Certify the proof books and test their hypotheses with actual worlds.

dir=build/export/acl2
proofs=export/proofs
books='structure-spec structure-events structure-enclosure structure-walk structure-items
structure-held-items structure-order structure-counts structure-coverage structure-ground-filter
structure-entry-order structure-entry-coverage structure-name-spelling
structure-name-routing structure-generated-names'
samples='std/lists/append misc/defpun std/stobjs/absstobjs
misc/hidden-defpkg-checks/top ordinals/e0-ordinal'
examples='repeat-cases cross-file-repeat named-conversion-note choice-self-call
import-shadowing invalid-library library-name-conflict reservation-note
unlisted-sibling-note nonground-axiom encapsulate-order constraint-name-exhaustion
shared-import-formula-names nested-constraint-name-reuse'

fail() {
    printf 'FAIL %s\n' "$1"
    printf '%s\n' 'some structure checks failed'
    exit 1
}

sh export/certify.sh || fail 'exporter prerequisites'
for book in $books; do
    cp "$proofs/$book.lisp" "$dir/$book.lisp" || fail "$book copy"
    if [ -f "$dir/$book.cert" ]; then
        rm "$dir/$book.cert" || fail "$book remove certificate"
    fi
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '(certify-book "%s/%s" 0 :default :defaxioms-okp nil :skip-proofs-okp nil :ttags nil)\n' "$dir" "$book"
        printf '%s\n' '(good-bye)'
    } | timeout 1800 acl2 > "$dir/$book.out" 2>&1
    if [ "$?" -ne 0 ] || [ ! -s "$dir/$book.cert" ]; then
        fail "$book certification (see $dir/$book.out)"
    fi
    seconds=$(awk '/^Time:/ {seconds = $2} END {print seconds}' "$dir/$book.out")
    printf 'ok %s (%s s)\n' "$book" "$seconds"
done

# Read only the fields of ground.txt used for order.  A ground definition
# has one function.  Its formals follow the name and are a list or NIL.
{
    printf "%s\n" "(er-progn (assign structure-ground-spec '("
    awk '
        /^\(package / {
            sub(/^\(package /, "(:package ")
            print
        }
        /^\(primitive / {
            sub(/^\(primitive /, "(:primitive ")
            print
        }
        /^\(define / {
            sub(/^\(define /, "")
            if (substr($0, 1, 1) == "(") sub(/^\([^()]*\) /, "")
            else sub(/^[^ ]+ /, "")
            sub(/^\(/, "")
            name = $1
            sub(/^[^ ]+ /, "")
            arity = 0
            if (match($0, /^\([^()]*\)/)) {
                formals = substr($0, 2, RLENGTH - 2)
                if (formals != "") arity = split(formals, fields, " ")
            }
            printf "(:define %s %d)\n", name, arity
        }
        /^\(clause [^"]/ {print "(:axiom " $2 ")"}
    ' spec/ground.txt
    printf '%s\n' ')) (value :structure-ground-ready))'
} > "$dir/structure-ground.lsp"

session_start() {
    printf '%s\n' '(ld "checks/version.lsp")'
    printf '%s\n' '(set-inhibit-output-lst (quote (warning observation prove proof-tree event summary history)))'
    printf '%s\n' '(assign structure-boot-hi (max-absolute-event-number (w state)))'
}

load_tests() {
    printf '%s\n' '(set-guard-checking :none)'
    printf '(ld "%s/structure-tests.lsp" :ld-error-action :error)\n' "$proofs"
    printf '(ld "%s/structure-ground.lsp" :ld-error-action :error)\n' "$dir"
}

check_log() {
    if grep -aq -E '^structure fail |^ACL2 Error|^[*]+ FAILED|ABORTING from raw Lisp' "$1"; then
        fail "ACL2 tests (see $1)"
    fi
}

check_test() {
    grep -aq -F -x "structure ok $1" "$2" || fail "$1 (see $2)"
    printf 'ok %s\n' "$1"
}

# Reload each certificate while ACL2 rejects trust tags, skipped proofs
# and added axioms, including in certified dependencies.
testlog=$dir/structure-tests.out
library=$dir/structure-library.object
{
    session_start
    printf '%s\n' '(assign structure-startup-world (w state))' '(progn'
    for book in canon core $books; do
        printf '(include-book "%s/%s" :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$dir" "$book"
    done
    printf '%s\n' '(value-triple :structure-certificates-ok))'
    load_tests
    printf '%s\n' '(ld "export/export.lsp" :ld-error-action :error)' '(logic)'
    cat <<'ACL2'
(structure-test-examples)
(structure-test-result "startup-world"
  (or (structure-test-range (@ structure-startup-world) 0 (@ structure-boot-hi))
      (and (not (structure-test-groundp (@ structure-ground-spec)
                                        (@ structure-startup-world)))
           :ground)))
(er-progn
 (assign structure-library-result
   (let* ((world (w state))
          (hi (@ structure-boot-hi))
          (translations (bx-translations (bx-translation-requests 0 hi world) world)))
     (mv-let (statements program notes)
       (bx-library-lines (structure-test-ground-definitions (@ structure-ground-spec))
                         hi translations world)
       (declare (ignore program))
       (list statements notes))))
 (value :structure-library-ready))
(structure-test-result "library-output"
  (structure-test-file (car (@ structure-library-result))
                       (cadr (@ structure-library-result))
                       (@ structure-ground-spec) (@ structure-boot-hi)
                       0 (@ structure-boot-hi) t (w state)))
ACL2
    printf '(structure-test-write-library (car (@ structure-library-result)) "%s" state)\n' "$library"
    printf '(ld "%s/structure-exhaustion.lsp" :ld-error-action :error)\n' "$proofs"
    printf '(ld "%s/structure-generated-tests.lsp" :ld-error-action :error)\n' "$proofs"
    printf '%s\n' '(good-bye)'
} | timeout 1800 acl2 > "$testlog" 2>&1
[ "$?" -eq 0 ] || fail "startup tests (see $testlog)"
check_log "$testlog"
grep -aq -E '^(ACL2 [!]*>[[:space:]]*)?:STRUCTURE-CERTIFICATES-OK$' "$testlog" ||
    fail "certificate reload (see $testlog)"
printf '%s\n' 'ok certificates'
for testcase in startup-world library-output $examples; do
    check_test "$testcase" "$testlog"
done
grep -aq ':STRUCTURE-LIBRARY-WRITTEN$' "$testlog" || fail "library data (see $testlog)"

# As in export/book.sh, include the specimens and save their range before
# installing the exporter or proof support.  Earlier portcullis events
# are part of that range.  Each test starts in a fresh ACL2 session.
check_books() {
    testcase=$1
    shift
    logname=$(printf '%s' "$testcase" | tr '/' '-')
    testlog=$dir/structure-$logname.out
    {
        session_start
        for specimen in "$@"; do
            printf '(include-book "%s" :dir :system :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$specimen"
        done
        printf '%s\n' '(assign structure-book-hi (max-absolute-event-number (w state)))' \
            '(assign structure-book-world (w state))'
        printf '(include-book "%s/canon" :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$dir"
        printf '(include-book "%s/structure-generated-names" :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$dir"
        load_tests
        printf '(er-let* ((library (structure-test-read-library "%s" state)))\n' "$library"
        printf '  (value (structure-test-result "%s" (structure-test-specimen library (@ structure-ground-spec) (@ structure-boot-hi) (@ structure-book-hi) (@ structure-book-world) (w state)))))\n' "$testcase"
        printf '%s\n' '(good-bye)'
    } | timeout 1800 acl2 > "$testlog" 2>&1
    [ "$?" -eq 0 ] || fail "$testcase (see $testlog)"
    check_log "$testlog"
    check_test "$testcase" "$testlog"
}

for book in $samples; do
    check_books "$book" "$book"
done
check_books combined-books $samples
printf '%s\n' 'all structure checks passed'
