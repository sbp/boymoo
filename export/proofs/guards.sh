#!/bin/sh
# Certify the guard books and check their entry guards on ACL2 worlds.
# Run from the root of the repository.

dir=build/export/acl2
books='guards-events guards-data guards-terms guards-items guards-report guards-lines guards'
tests='certificates core-guards startup hidden-packages choice alist-equivalence abstract-stobjs axiom'
log=$dir/guards-tests.out
failed=0

if ! sh export/certify.sh --fresh-guards; then
    failed=1
fi
for book in $books; do
    if [ -f "$dir/$book.cert" ]; then
        seconds=$(awk '/^Time:/ {seconds=$2} END {print seconds}' "$dir/$book.out")
        echo "$book ok ($seconds s)"
    else
        echo "$book failed (see $dir/$book.out)"
        failed=1
    fi
done

if [ "$failed" -eq 0 ]; then
    names=$(sed -n 's/^(define [^ (][^ ]* (\([^ ]*\) .*/\1/p; s/^(define ([^()]*) (\([^ ]*\) .*/\1/p' spec/ground.txt |
                tr '\n' ' ')
    functions=$(sed -n 's/^[[:space:]]*(defun \(bx-[a-z0-9-]*\) .*/\1/p' export/core.lisp |
                    tr '\n' ' ')
    {
        echo '(ld "checks/version.lsp")'
        echo "(set-ld-error-action '(:exit 1) state)"
        echo "(set-inhibit-output-lst '(proof-tree prove event summary history))"
        echo '(assign guards-startup-world (w state))'
        echo '(assign guards-startup-hi (max-absolute-event-number (w state)))'
        for specimen in \
            hidden-packages:misc/hidden-defpkg-checks/top \
            choice:misc/defpun \
            alist-equivalence:std/alists/alist-equiv \
            abstract-stobjs:std/stobjs/absstobjs \
            axiom:misc/dft-ex; do
            label=${specimen%%:*}
            source=${specimen#*:}
            printf '(include-book "%s" :dir :system :uncertified-okp nil :ttags :all)\n' "$source"
            printf '(assign guards-%s-world (w state))\n' "$label"
            printf '(assign guards-%s-hi (max-absolute-event-number (w state)))\n' "$label"
        done
        for book in canon guards; do
            printf '(include-book "%s/%s" :uncertified-okp nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$dir" "$book"
        done
        echo '(ld "export/export.lsp" :ld-error-action :error)'
        echo '(set-guard-checking t)'
        cat <<'LISP'
(defun guards-check-certificate (file state)
  (declare (xargs :stobjs state))
  (mv-let (erp data state)
    (cert-annotations-and-checksum-from-cert-file file state)
    (if (and (not erp)
             (equal (car data) '((:skipped-proofsp) (:axiomsp) (:ttags))))
        (value t)
      (er soft 'guards-check-certificate "Unexpected annotations in ~x0." file))))

(defmacro guards-test-result (label test)
  `(if ,test
       (value (cw "~%guards-test: ~s0 ok~%" ,label))
     (er soft 'guards-test-result "The ~s0 test failed." ,label)))

(defun guards-unverified-functions (names wrld)
  (cond ((endp names) nil)
        ((eq (getpropc (car names) 'symbol-class nil wrld) :common-lisp-compliant)
         (guards-unverified-functions (cdr names) wrld))
        (t (cons (car names) (guards-unverified-functions (cdr names) wrld)))))

(defun guards-test-definition (test entry wrld)
  (list 'defun test (formals entry wrld)
        (untranslate (guard entry nil wrld) nil wrld)))

; Evaluate the declared entry guards on each saved ACL2 world.
(make-event
 (let ((wrld (w state)))
   (value
    (list 'progn
          (guards-test-definition 'guards-request-inputs-p
                                  'bx-translation-requests wrld)
          (guards-test-definition 'guards-library-inputs-p
                                  'bx-library-lines wrld)
          (guards-test-definition 'guards-book-inputs-p
                                  'bx-book-lines wrld)))))

(defun guards-check-entries (label ground boot-hi hi library-translations wrld state)
  (declare (xargs :stobjs state))
  (let* ((live-world (w state))
         (book-requests (ec-call (bx-translation-requests boot-hi hi live-world)))
         (book-translations (bx-translations book-requests live-world)))
    (guards-test-result
     label
     (and (guards-request-inputs-p 0 boot-hi wrld)
          (guards-request-inputs-p boot-hi hi wrld)
          (guards-library-inputs-p ground boot-hi library-translations wrld)
          (guards-book-inputs-p ground boot-hi boot-hi hi book-translations
                                (system-books-dir state) (cbd) wrld)))))
LISP
        echo '(er-progn'
        for book in canon core $books; do
            printf '  (guards-check-certificate "%s/%s.lisp" state)\n' "$dir" "$book"
        done
        echo '  (guards-test-result "certificates" t))'
        printf '(let ((missing (guards-unverified-functions (quote (%s bm-line)) (w state))))\n' "$functions"
        echo '  (if missing'
        echo '      (er soft (quote guards) "Unverified functions ~x0." missing)'
        echo '    (guards-test-result "core-guards" t)))'
        printf "(assign guards-ground-fns '(%s))\n" "$names"
        # Translation uses the live world. The predicates take each
        # saved world as data, including the world before any book.
        cat <<'LISP'
(let* ((live-world (w state))
       (requests (ec-call (bx-translation-requests 0 (@ guards-startup-hi) live-world)))
       (library-translations (bx-translations requests live-world)))
  (er-progn
LISP
        for label in startup hidden-packages choice alist-equivalence abstract-stobjs axiom; do
            printf '    (guards-check-entries "%s" (@ guards-ground-fns) (@ guards-startup-hi) (@ guards-%s-hi) library-translations (@ guards-%s-world) state)\n' "$label" "$label" "$label"
        done
        echo '    (value :guard-tests-ok)))'
        echo '(good-bye)'
    } | timeout -k 5 300 acl2 > "$log" 2>&1
    if [ "$?" -ne 0 ] || grep -Eq 'ACL2 Error|HARD ACL2 ERROR|ABORTING from raw Lisp' "$log"; then
        failed=1
    fi
else
    : > "$log"
fi

for test in $tests; do
    if grep -Fxq "guards-test: $test ok" "$log"; then
        echo "$test ok"
    else
        echo "$test failed (see $log)"
        failed=1
    fi
done
if [ "$failed" -eq 0 ]; then
    echo 'all guard checks passed'
else
    echo 'some guard checks failed'
fi
exit "$failed"
