(in-package "ACL2")

; ACL2 puts G's defining equation and the named theorem in the same
; constraint.  Capture just the encapsulate and its enclosed events.

(assign structure-exhaustion-lo (max-absolute-event-number (w state)))

(encapsulate (((structure-exhausted-f *) => *))
  (local (defun structure-exhausted-f (x) x))
  (defun structure-exhausted-g (x) (structure-exhausted-f x))
  (defthm structure-exhausted-theorem
    (equal (structure-exhausted-g x) x)
    :rule-classes nil))

(assign structure-exhaustion-hi (max-absolute-event-number (w state)))

(assign structure-exhaustion-control
  (mv-let (statements program notes aids)
    (bx-book-lines (structure-test-ground-definitions (@ structure-ground-spec))
                   (@ structure-boot-hi) (@ structure-exhaustion-lo)
                   (@ structure-exhaustion-hi) nil "" "" (w state))
    (declare (ignore program notes aids))
    (equal statements
           '(("constrain"
              (((structure-exhausted-f 1) (structure-exhausted-g 1))
               ((|STRUCTURE-EXHAUSTED-G definition|
                 (equal (structure-exhausted-g x) (structure-exhausted-f x)))
                (structure-exhausted-theorem (equal (structure-exhausted-g x) x)))))))))

; Each label takes one of the 1,001 candidate names of G's equation.
; The labels are in the world that the exporter consults for name use.

(defun structure-test-equation-labels (n acc)
  (declare (xargs :measure (nfix n)))
  (let* ((base "STRUCTURE-EXHAUSTED-G definition")
         (spelling (if (zp n)
                       base
                     (concatenate 'string base " "
                                  (coerce (explode-nonnegative-integer n 10 nil) 'string))))
         (name (intern-in-package-of-symbol spelling 'structure-exhausted-g))
         (acc (cons (list 'deflabel name) acc)))
    (if (zp n) acc (structure-test-equation-labels (- n 1) acc))))

(make-event (value (cons 'progn (structure-test-equation-labels 1000 nil))))

(defun structure-test-find-exhausted-theorem (records)
  (cond ((endp records) nil)
        ((equal (structure-event-namex (car records)) 'structure-exhausted-theorem)
         (car records))
        (t (structure-test-find-exhausted-theorem (cdr records)))))

(defun structure-test-exhausted-output-p (record lo hi wrld statements notes)
  (let ((name 'structure-exhausted-theorem))
    (and (structure-range-recordsp wrld lo hi)
         (structure-range-namep name record lo hi wrld)
         (structure-namex-shapep record)
         (not (structure-no-statement-due-p name record wrld))
         (equal (structure-introduction-count name statements nil) 0)
         (structure-notes-report-p name notes)
         (member-equal '("note" ("constraint with a formula for which no unused name was found"
                                (structure-exhausted-f structure-exhausted-g
                                 structure-exhausted-theorem)))
                       notes))))

(defun structure-test-real-exhaustion (actual-prefix ground boot-hi lo hi wrld)
  (let ((record (structure-test-find-exhausted-theorem (structure-range-events wrld lo hi nil))))
    (mv-let (library lib-program lib-notes)
      (bx-library-lines ground hi nil wrld)
      (declare (ignore lib-program))
      (mv-let (book program notes aids)
        (bx-book-lines ground boot-hi lo hi nil "" "" wrld)
        (declare (ignore program aids))
        (and (plist-worldp wrld)
             (structure-library-prefix-matches-p actual-prefix ground boot-hi wrld)
             (not (structure-library-ground-supplies-p 'structure-exhausted-theorem ground))
             (structure-test-exhausted-output-p record 0 hi wrld library lib-notes)
             (structure-test-exhausted-output-p record lo hi wrld (append actual-prefix book)
                                                notes))))))

(structure-test-result
 "constraint-name-exhaustion"
 (cond ((not (@ structure-exhaustion-control)) :control)
       ((not (structure-test-real-exhaustion
              (car (@ structure-library-result))
              (structure-test-ground-definitions (@ structure-ground-spec))
              (@ structure-boot-hi) (@ structure-exhaustion-lo) (@ structure-exhaustion-hi)
              (w state)))
        :named-exhaustion)))
