#!/bin/sh
# Certify the exporter well-formedness proofs and run their ACL2 tests.
# Run from the root of the repository.

dir=build/export/acl2
books='well-formed-syntax well-formed-terms well-formed-world well-formed-items well-formed-names well-formed'

fail() {
    printf '%s\n' "$1" 'well-formedness checks failed'
    exit 1
}

sh export/certify.sh || fail 'exporter books: failed'

for book in $books; do
    log=$dir/$book.out
    cp "export/proofs/$book.lisp" "$dir/$book.lisp" || fail "$book: copy failed"
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '(certify-book "%s/%s" 0 nil :pcert nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$dir" "$book"
        printf '%s\n' '(good-bye)'
    } | timeout -k 5 300 acl2 > "$log" 2>&1
    if [ "$?" -ne 0 ] || [ ! -f "$dir/$book.cert" ] ||
        ! grep -q '^\* Step 4:  Write the certificate' "$log" ||
        grep -q '^ACL2 Error' "$log"; then
        fail "$book: certification failed ($log)"
    fi
    seconds=$(awk '/^Form:  [(]CERTIFY-BOOK/ { cert = 1 }
                   cert && /^Time:/ { print $2; exit }' "$log")
    printf '%s: ok (%s s)\n' "$book" "$seconds"
done

# Read the function names from the define lines of the ground theory.
ground=$(sed -n 's/^(define [^ (][^ ]* (\([^ ]*\) .*/\1/p; s/^(define ([^()]*) (\([^ ]*\) .*/\1/p' spec/ground.txt |
    tr '\n' ' ')

log=$dir/well-formed-tests.out
{
    cat <<'EOF'
(ld "checks/version.lsp")
(assign wf-initial-world (w state))
(assign wf-initial-hi (max-absolute-event-number (w state)))
(include-book "build/export/acl2/canon" :uncertified-okp nil
              :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)
(include-book "build/export/acl2/core" :uncertified-okp nil
              :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)
(ld "export/export.lsp")
(set-guard-checking :none)
EOF
    printf "(assign wf-ground-fns '(%s))\n" "$ground"
    cat <<'EOF'
(er-progn
 (assign wf-initial-translations
         (bx-translations
          (bx-translation-requests 0 (@ wf-initial-hi) (w state)) (w state)))
 (value :invisible))
(er-progn
 (assign wf-initial-output
         (mv-let (statements program notes)
           (bx-library-lines (@ wf-ground-fns) (@ wf-initial-hi)
                             (@ wf-initial-translations) (w state))
           (declare (ignore notes))
           (list statements program)))
 (value :invisible))
EOF
    printf '%s\n' '(er-progn'
    for book in $books; do
        printf ' (include-book "%s/%s" :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$dir" "$book"
    done
    cat <<'EOF'
 (value :WF-CERTIFICATES-OK))

(value-triple (if (plist-worldp (@ wf-initial-world))
                  :WF-INITIAL-TRIPLES-OK :failed))
(value-triple (if (wf-world-property-shapes-p (@ wf-initial-world))
                  :WF-INITIAL-PROPERTY-SHAPES-OK :failed))
(value-triple (if (wf-world-properties-p (@ wf-initial-world))
                  :WF-INITIAL-PROPERTY-DETAILS-OK :failed))
(value-triple (if (wf-world-attachment-targets-p (@ wf-initial-world))
                  :WF-INITIAL-ATTACHMENT-TARGETS-OK :failed))
(value-triple (if (wf-world-event-data-p (@ wf-initial-world) (@ wf-initial-world)
                                         0 (@ wf-initial-hi))
                  :WF-INITIAL-EVENT-DATA-OK :failed))
(value-triple (if (and (consp (@ wf-ground-fns))
                       (wf-ground-functions-p (@ wf-ground-fns) (@ wf-initial-world)))
                  :WF-INITIAL-GROUND-FUNCTIONS-OK :failed))
(value-triple (if (and (consp (@ wf-initial-translations))
                       (wf-translations-p (@ wf-initial-translations)))
                  :WF-INITIAL-TRANSLATIONS-OK :failed))
(value-triple (if (and (consp (car (@ wf-initial-output)))
                       (wf-statement-lines-p (car (@ wf-initial-output))))
                  :WF-LIBRARY-STATEMENTS-OK :failed))
(value-triple (if (and (consp (cadr (@ wf-initial-output)))
                       (wf-program-lines-p (cadr (@ wf-initial-output))))
                  :WF-LIBRARY-PROGRAM-OK :failed))

(logic)
(set-guard-checking t)
(assign wf-sample-lo (max-absolute-event-number (w state)))
EOF
    for book in std/lists/append misc/defattach-example std/system/defchoose-queries \
        std/stobjs/1d-arr misc/hidden-defpkg-checks/top misc/defpun std/strings/pretty; do
        printf '(include-book "%s" :dir :system :uncertified-okp nil :skip-proofs-okp nil :ttags nil)\n' "$book"
    done
    cat <<'EOF'
(assign wf-sample-hi (max-absolute-event-number (w state)))
(set-guard-checking :none)
(value-triple (if (plist-worldp (w state)) :WF-SAMPLE-TRIPLES-OK :failed))
(value-triple (if (wf-world-property-shapes-p (w state))
                  :WF-SAMPLE-PROPERTY-SHAPES-OK :failed))
(value-triple (if (wf-world-properties-p (w state))
                  :WF-SAMPLE-PROPERTY-DETAILS-OK :failed))
(value-triple (if (wf-world-attachment-targets-p (w state))
                  :WF-SAMPLE-ATTACHMENT-TARGETS-OK :failed))
(value-triple (if (and (< (@ wf-sample-lo) (@ wf-sample-hi))
                       (wf-world-event-data-p (w state) (w state)
                                              (@ wf-sample-lo) (@ wf-sample-hi)))
                  :WF-SAMPLE-EVENT-DATA-OK :failed))
(value-triple (if (wf-ground-functions-p (@ wf-ground-fns) (w state))
                  :WF-SAMPLE-GROUND-FUNCTIONS-OK :failed))
(er-progn
 (assign wf-sample-translations
         (bx-translations
          (bx-translation-requests (@ wf-sample-lo) (@ wf-sample-hi) (w state))
          (w state)))
 (value :invisible))
(value-triple (if (wf-translations-p (@ wf-sample-translations))
                  :WF-SAMPLE-TRANSLATIONS-OK :failed))
(er-progn
 (assign wf-sample-output
         (mv-let (statements program notes aids)
           (bx-book-lines (@ wf-ground-fns) (@ wf-initial-hi)
                          (@ wf-sample-lo) (@ wf-sample-hi) (@ wf-sample-translations)
                          "" "" (w state))
           (declare (ignore notes aids))
           (list statements program)))
 (value :invisible))
(value-triple (if (and (consp (car (@ wf-sample-output)))
                       (wf-statement-lines-p (car (@ wf-sample-output))))
                  :WF-BOOK-STATEMENTS-OK :failed))
(value-triple (if (and (consp (cadr (@ wf-sample-output)))
                       (wf-program-lines-p (cadr (@ wf-sample-output))))
                  :WF-BOOK-PROGRAM-OK :failed))

; A package import occupies the first candidate for the corollary's
; name. The definition of G needs F from the constraint.
(set-guard-checking t)
(assign wf-example-start (max-absolute-event-number (w state)))
(defpkg "WF-EXAMPLE" '(:|F constraint 1|))
(encapsulate (((wf-example::f *) => *))
  (local (defun wf-example::f (x) x))
  (defun wf-example::g (x) (wf-example::f x))
  (defthm wf-example::identity
    (equal (wf-example::f x) x)
    :rule-classes ((:rewrite :corollary (equal (wf-example::f x) x))
                   (:rewrite :corollary (equal (wf-example::f (cons x y)) (cons x y))))))
(set-guard-checking :none)
(value-triple
 (let ((hi (max-absolute-event-number (w state))))
   (mv-let (statements program notes aids)
     (bx-book-lines nil 0 (@ wf-example-start) hi nil "" "" (w state))
     (declare (ignore program aids))
     (if (and (wf-world-property-shapes-p (w state))
              (wf-world-properties-p (w state))
              (wf-world-event-data-p (w state) (w state) (@ wf-example-start) hi)
              (equal (strip-cars statements) '("package" "constrain" "define"))
              (wf-statement-lines-p statements)
              (member-equal '(wf-example::|F constraint 1 1|
                              (equal (wf-example::f (cons x y)) (cons x y)))
                            (cadr (cadr (cadr statements))))
              (equal (caddr statements)
                     '("define" (nil (wf-example::g (x) (wf-example::f x)))))
              (equal (bx-words '("note") notes)
                     '(("note" ("formula of a constraint that no event of the encapsulate states"
                                (wf-example::f wf-example::|F constraint 1 1|))))))
         :WF-CONSTRAINT-IMPORTED-NAME-OK
       :failed))))

; The constraint has a named formula and an unnamed formula whose
; candidate names all belong to existing theorems.
(defun wf-test-occupy-constraint-names (i wrld)
  (declare (xargs :mode :program))
  (let* ((base "WF-EXHAUSTED constraint 1")
         (name (if (zp i)
                   base
                 (concatenate 'string base " "
                              (coerce (explode-nonnegative-integer i 10 nil) 'string))))
         (rule (intern-in-package-of-symbol name 'wf-exhausted))
         (wrld (cons (list* rule 'theorem ''t) wrld)))
    (if (zp i)
        wrld
      (wf-test-occupy-constraint-names (- i 1) wrld))))
(value-triple
 (let* ((lo (@ wf-initial-hi))
        (hi (+ lo 2))
        (wrld (wf-test-occupy-constraint-names
               *bx-name-tries*
               (append `((event-landmark global-value ,hi encapsulate ((wf-exhausted)))
                         (event-landmark global-value (,(1+ lo) . 1) defthm wf-exhausted-law)
                         (wf-exhausted constraint-lst-etc
                          ((quote t) (equal (wf-exhausted) (quote t))))
                         (wf-exhausted-law theorem . (equal (wf-exhausted) (quote t)))
                         (wf-exhausted formals)
                         (wf-exhausted-companion formals)
                         (wf-exhausted siblings wf-exhausted wf-exhausted-companion))
                       (@ wf-initial-world))))
        (items (bx-range-items lo hi nil wrld))
        (notes-to-write
         '(("formula of a constraint that no event of the encapsulate states" (wf-exhausted nil))
           ("constraint with a formula for which no unused name was found"
            (wf-exhausted wf-exhausted-companion wf-exhausted-law)))))
   (mv-let (statements program notes aids)
     (bx-book-lines nil 0 lo hi nil "" "" wrld)
     (declare (ignore program aids))
     (if (and (wf-world-property-shapes-p wrld)
              (wf-world-properties-p wrld)
              (wf-world-event-data-p wrld wrld lo hi)
              (equal (strip-cars items) '(:note :note))
              (equal (bx-select :note items) notes-to-write)
              (null statements)
              (equal (strip-cadrs (bx-words '("note") notes)) notes-to-write))
         :WF-CONSTRAINT-NAMES-EXHAUSTED-OK
       :failed))))

; Both packages import the same candidate for an unnamed formula.
(set-guard-checking t)
(assign wf-shared-import-lo (max-absolute-event-number (w state)))
(defpkg "WF-IMPORT-A" '(acl2::|F constraint 1|))
(defpkg "WF-IMPORT-B" '(acl2::|F constraint 1|))
(encapsulate (((wf-import-a::f *) => *))
  (local (defun wf-import-a::f (x) x))
  (defthm wf-import-a::law
    (equal (wf-import-a::f x) x)
    :rule-classes ((:rewrite :corollary (equal (wf-import-a::f x) x))
                   (:rewrite :corollary (equal (wf-import-a::f (cons x y)) (cons x y))))))
(encapsulate (((wf-import-b::f *) => *))
  (local (defun wf-import-b::f (x) x))
  (defthm wf-import-b::law
    (equal (wf-import-b::f x) x)
    :rule-classes ((:rewrite :corollary (equal (wf-import-b::f x) x))
                   (:rewrite :corollary (equal (wf-import-b::f (cons x y)) (cons x y))))))
(set-guard-checking :none)
(value-triple
 (mv-let (statements program notes aids)
   (bx-book-lines nil 0 (@ wf-shared-import-lo)
                  (max-absolute-event-number (w state)) nil "" "" (w state))
   (declare (ignore program aids))
   (let* ((constraints (bx-words '("constrain") statements))
          (a (cadr (cadar constraints)))
          (b (cadr (cadadr constraints))))
     (if (and (equal (strip-cars statements) '("package" "package" "constrain" "constrain"))
              (wf-statement-lines-p statements)
              (equal (strip-cars a) '(wf-import-a::law wf-import-a::|F constraint 1 1|))
              (equal (strip-cars b) '(wf-import-b::law wf-import-b::|F constraint 1 1|))
              (equal (bx-words '("note") notes)
                     '(("note" ("formula of a constraint that no event of the encapsulate states"
                                (wf-import-a::f wf-import-a::|F constraint 1 1|)))
                       ("note" ("formula of a constraint that no event of the encapsulate states"
                                (wf-import-b::f wf-import-b::|F constraint 1 1|))))))
         :WF-CONSTRAINT-SHARED-IMPORT-OK
       :failed))))

; ACL2 associates both signatures with the same constraint owner.
(set-guard-checking t)
(assign wf-nested-lo (max-absolute-event-number (w state)))
(encapsulate (((wf-outer *) => *))
  (local (defun wf-outer (x) x))
  (defthm wf-outer-law
    (equal (wf-outer x) x)
    :rule-classes ((:rewrite :corollary (equal (wf-outer x) x))
                   (:rewrite :corollary (equal (wf-outer (cons x y)) (cons x y)))))
  (encapsulate (((wf-inner *) => *))
    (local (defun wf-inner (x) (wf-outer x)))
    (defthm wf-inner-law
      (equal (wf-inner x) (wf-outer x))
      :rule-classes nil)))
(set-guard-checking :none)
(value-triple
 (let* ((hi (max-absolute-event-number (w state)))
        (named-formula '(|WF-OUTER constraint 1| (equal (wf-outer (cons x y)) (cons x y)))))
   (mv-let (statements program notes aids)
     (bx-book-lines nil 0 (@ wf-nested-lo) hi nil "" "" (w state))
     (declare (ignore program aids))
     (if (and (wf-world-property-shapes-p (w state))
              (wf-world-properties-p (w state))
              (wf-world-event-data-p (w state) (w state) (@ wf-nested-lo) hi)
              (equal (car (getpropc 'wf-inner 'constraint-lst-etc nil (w state))) 'wf-outer)
              (equal (strip-cars statements) '("constrain" "constrain"))
              (wf-statement-lines-p statements)
              (not (equal (car statements) (cadr statements)))
              (member-equal named-formula (cadr (cadar statements)))
              (member-equal named-formula (cadr (cadadr statements)))
              (member-equal
               '("note" ("line that could not be admitted in order"
                         ((wf-outer wf-inner) nil
                          ((:name-in-use (wf-outer wf-inner wf-outer-law wf-inner-law
                                                                    |WF-OUTER constraint 1|))))))
               notes))
         :WF-CONSTRAINT-SHARED-OWNER-EXAMPLE-OK
       :failed))))
(good-bye)
EOF
} | timeout -k 5 300 acl2 > "$log" 2>&1
status=$?

for test in CERTIFICATES \
    INITIAL-TRIPLES INITIAL-PROPERTY-SHAPES INITIAL-PROPERTY-DETAILS \
    INITIAL-ATTACHMENT-TARGETS \
    INITIAL-EVENT-DATA INITIAL-GROUND-FUNCTIONS INITIAL-TRANSLATIONS \
    LIBRARY-STATEMENTS LIBRARY-PROGRAM \
    SAMPLE-TRIPLES SAMPLE-PROPERTY-SHAPES SAMPLE-PROPERTY-DETAILS \
    SAMPLE-ATTACHMENT-TARGETS \
    SAMPLE-EVENT-DATA SAMPLE-GROUND-FUNCTIONS SAMPLE-TRANSLATIONS \
    BOOK-STATEMENTS BOOK-PROGRAM CONSTRAINT-IMPORTED-NAME CONSTRAINT-NAMES-EXHAUSTED \
    CONSTRAINT-SHARED-IMPORT CONSTRAINT-SHARED-OWNER-EXAMPLE; do
    if grep -Eq "(^|[[:space:]]):WF-$test-OK([[:space:]]|$)" "$log"; then
        printf '%s: ok\n' "$test"
    else
        printf '%s: failed\n' "$test"
        status=1
    fi
done
if [ "$status" -ne 0 ] || grep -Eq '^ACL2 Error|^HARD ACL2 ERROR' "$log"; then
    fail "ACL2 tests: see $log"
fi
printf '%s\n' 'all well-formedness checks passed'
