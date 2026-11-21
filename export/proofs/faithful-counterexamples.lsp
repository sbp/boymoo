(in-package "ACL2")

; A clique may have more than one set of stored ruler-extenders.

(assign faithful-rulers-lo (max-absolute-event-number (w state)))

(mutual-recursion
 (defun faithful-even (x)
   (declare (xargs :ruler-extenders :all :verify-guards nil))
   (if (zp x) t (faithful-odd (1- x))))
 (defun faithful-odd (x)
   (declare (xargs :ruler-extenders (cons) :verify-guards nil))
   (if (zp x) nil (faithful-even (1- x)))))

(mv-let (statements program notes aids)
  (bx-book-lines (@ faithful-ground-fns) (@ faithful-boot-hi) (@ faithful-rulers-lo)
                 (max-absolute-event-number (w state)) nil "" "" (w state))
  (declare (ignore program aids))
  (let* ((line (car statements))
         (args (cadr line))
         (even-rulers (faithful-ruler-extenders 'faithful-even (w state)))
         (odd-rulers (faithful-ruler-extenders 'faithful-odd (w state))))
    (faithful-test "different ruler-extenders"
                   (and (equal (car line) "define")
                        (equal (strip-cars (cdr args)) '(faithful-even faithful-odd))
                        (eq even-rulers :all)
                        (equal odd-rulers '(cons))
                        (equal (car args) even-rulers)
                        (not (equal (car args) odd-rulers))
                        (member-equal
                         '("note" ("clique whose functions differ in ruler-extenders"
                                    (faithful-even faithful-odd)))
                         notes)))))

; When an inner signature depends on an outer signature, ACL2 can
; record a single constraint for both events. Both lines use the same
; owner and conjunct position to make the label.

(assign faithful-nested-lo (max-absolute-event-number (w state)))

(encapsulate
  (((faithful-nested-outer *) => *))
  (local (defun faithful-nested-outer (x) x))
  (encapsulate
    (((faithful-nested-inner *) => *))
    (local (defun faithful-nested-inner (x) (faithful-nested-outer x)))
    (defthm faithful-nested-link
      (equal (faithful-nested-inner x) (faithful-nested-outer x))
      :rule-classes
      ((:rewrite :corollary
                 (equal (faithful-nested-inner (cons x y))
                        (faithful-nested-outer (cons x y)))))))
  (defthm faithful-nested-law
    (equal (faithful-nested-outer x) x)
    :rule-classes nil))

(mv-let (statements program notes aids)
  (bx-book-lines (@ faithful-ground-fns) (@ faithful-boot-hi) (@ faithful-nested-lo)
                 (max-absolute-event-number (w state)) nil "" "" (w state))
  (declare (ignore program aids))
  (let ((label '|FAITHFUL-NESTED-OUTER constraint 2|)
        (formula '(equal (faithful-nested-inner (cons x y))
                         (faithful-nested-outer (cons x y))))
        (first (car statements))
        (second (cadr statements))
        (wrld (w state)))
    (faithful-test "nested constraint shares a generated label"
                   (and (equal (strip-cars statements) '("constrain" "constrain"))
                        (not (equal first second))
                        (eq (faithful-constraint-owner 'faithful-nested-inner wrld)
                            'faithful-nested-outer)
                        (eq (faithful-constraint-owner 'faithful-nested-outer wrld)
                            'faithful-nested-outer)
                        (faithful-unused-formula-name-p label wrld)
                        (eq (faithful-label-anchor label) 'faithful-nested-outer)
                        (equal (faithful-world-formula-for-generated-label label wrld)
                               formula)
                        (faithful-statement-introduces-name-p label first)
                        (faithful-statement-introduces-name-p label second)
                        (equal (assoc-equal label (cadr (cadr first)))
                               (list label formula))
                        (equal (assoc-equal label (cadr (cadr second)))
                               (list label formula))
                        (not (faithful-first-statement-problem statements wrld))
                        (faithful-note-of-kind-p
                         "line that could not be admitted in order" notes)))))
