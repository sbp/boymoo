(in-package "ACL2")

(include-book "core")
(include-book "structure-spec")

; The section 8 term traversal rejects exactly the calls whose signatures
; fail the specification's test.  The induction visits lambda bodies as
; well as argument lists, and stops at variables and quotes.

(defun structure-call-induction (x termp)
  (declare (xargs :measure (+ (* 2 (acl2-count x)) (if termp 0 1))))
  (if termp
      (cond ((atom x) nil)
            ((eq (car x) 'quote) nil)
            ((consp (car x))
             (list (structure-call-induction (caddar x) t)
                   (structure-call-induction (cdr x) nil)))
            (t (structure-call-induction (cdr x) nil)))
    (if (endp x)
        nil
      (list (structure-call-induction (car x) t)
            (structure-call-induction (cdr x) nil)))))

(defthm structure-calls-in-scopep-of-append
  (equal (structure-calls-in-scopep (append x y) signatures own)
         (and (structure-calls-in-scopep x signatures own)
              (structure-calls-in-scopep y signatures own))))

(defthm structure-check-call-walk
  (if termp
      (equal (not (bx-bad-calls x signatures own))
             (structure-calls-in-scopep (structure-calls x) signatures own))
    (equal (not (bx-bad-calls-lst x signatures own))
           (structure-calls-in-scopep (structure-calls-in-list x)
                                      signatures own)))
  :hints (("Goal" :induct (structure-call-induction x termp)))
  :rule-classes nil)

(defthm structure-check-calls-in-list
  (iff (bx-bad-calls-lst terms signatures own)
       (not (structure-calls-in-scopep (structure-calls-in-list terms)
                                      signatures own)))
  :hints (("Goal" :use ((:instance structure-check-call-walk
                                   (x terms) (termp nil))))))

; The package and name traversals and the tables installed at one line
; implement the corresponding prefix operations.

(defthm structure-check-packages-of
  (equal (not (bx-packages-of datum packages acc))
         (and (not acc) (structure-declared-packages-p datum packages)))
  :hints (("Goal" :induct (bx-packages-of datum packages acc))))

(defthm structure-check-missing-packages
  (iff (bx-packages-of datum packages nil)
       (not (structure-declared-packages-p datum packages)))
  :hints (("Goal" :use ((:instance structure-check-packages-of (acc nil)))
                  :in-theory (disable bx-packages-of structure-declared-packages-p
                                      structure-check-packages-of))))

(defthm structure-check-imported-names
  (equal (not (bx-imported-names datum packages acc))
         (and (not acc) (structure-unshadowed-symbols-p datum packages)))
  :hints (("Goal" :induct (bx-imported-names datum packages acc))))

(defthm structure-check-shadowed-symbols
  (iff (bx-imported-names datum packages nil)
       (not (structure-unshadowed-symbols-p datum packages)))
  :hints (("Goal" :use ((:instance structure-check-imported-names (acc nil)))
                  :in-theory (disable bx-imported-names structure-unshadowed-symbols-p
                                      structure-check-imported-names))))

(defthm structure-check-record-imports
  (equal (bx-add-imports package imports packages)
         (structure-record-imports package imports packages))
  :hints (("Goal" :induct (bx-add-imports package imports packages))))

(defthm structure-check-new-names
  (iff (bx-new-names new names)
       (not (structure-fresh-names-p new names)))
  :hints (("Goal" :induct (bx-new-names new names))))

(defthm structure-check-definition-signatures
  (equal (bx-alist (bx-def-arities definitions))
         (structure-definition-signatures definitions)))

(defthm structure-check-declared-signatures
  (equal (bx-alist declarations)
         (structure-declared-signatures declarations)))

(defthm structure-check-record-signatures
  (equal (bx-add-arities declarations signatures)
         (structure-record-signatures
          (structure-declared-signatures declarations) signatures))
  :hints (("Goal" :induct (bx-add-arities declarations signatures))))

(defthm structure-declared-signatures-of-def-arities
  (equal (structure-declared-signatures (bx-def-arities definitions))
         (structure-definition-signatures definitions)))

(defthm structure-strip-cars-of-def-arities
  (equal (strip-cars (bx-def-arities definitions))
         (strip-cars definitions)))

(defthm structure-check-record-names
  (equal (bx-add-names new names)
         (structure-record-names new names))
  :hints (("Goal" :induct (bx-add-names new names))))

(defthm structure-check-bodies
  (equal (bx-bodies definitions) (structure-definition-bodies definitions)))

(defthm structure-check-package-rule
  (equal (bx-package-rule package) (structure-package-rule package)))

(defthm structure-one-declared-signature
  (equal (structure-declared-signatures (list (list function arity)))
         (list (cons function arity))))

(defthm structure-empty-calls-in-scope
  (structure-calls-in-scopep nil signatures own))

(defthm structure-no-calls-in-empty-terms
  (equal (structure-calls-in-list nil) nil))

(defthm structure-empty-names-are-fresh
  (structure-fresh-names-p nil names))

(defthm structure-one-name-is-fresh
  (equal (structure-fresh-names-p (list name) names)
         (not (hons-get name names))))

(local (in-theory (disable bx-bad-calls bx-bad-calls-lst bx-packages-of bx-new-names
                    bx-imported-names structure-unshadowed-symbols-p
                    bx-add-arities bx-add-imports bx-add-names bx-bodies bx-package-rule
                    structure-record-imports
                    bx-def-arities bx-alist structure-package-rule
                    structure-definition-bodies structure-definition-signatures
                    structure-declared-signatures structure-calls-in-list
                    structure-calls-in-scopep structure-declared-packages-p
                    structure-fresh-names-p)))

(defthm structure-check-one-line-order
  (iff (car (bx-check-stmt line signatures names packages))
       (not (structure-line-orderp line signatures names packages)))
  :hints (("Goal" :in-theory (enable structure-line-orderp
                                     structure-package-newp))))

(defthm structure-check-one-line-context
  (let ((result (bx-check-stmt line signatures names packages)))
    (and (equal (mv-nth 1 result)
                (structure-record-signatures (structure-signatures line) signatures))
         (equal (mv-nth 2 result)
                (structure-record-names (structure-names line) names))
         (equal (mv-nth 3 result)
                (structure-record-package line packages))))
  :hints (("Goal" :in-theory (enable structure-record-signatures
                                     structure-record-names
                                     structure-declared-signatures))))

; The index used by section 8 answers membership in the preceding lines.
; Equal data are one line in the canonical format.  Ground data are never
; entered in this index.

(defun structure-seen-index (earlier)
  (if (endp earlier)
      nil
    (let* ((index (structure-seen-index (cdr earlier)))
           (line (car earlier))
           (key (bx-stmt-key line)))
      (hons-acons key (cons line (cdr (hons-get key index))) index))))

(defthm structure-seen-index-correct
  (iff (member-equal line
                     (cdr (hons-get (bx-stmt-key line)
                                    (structure-seen-index earlier))))
       (member-equal line earlier))
  :hints (("Goal" :induct (structure-seen-index earlier)
                  :in-theory (disable bx-stmt-key))))

(defthm structure-push-seen-index
  (equal (hons-acons (bx-stmt-key line)
                    (cons line (cdr (hons-get (bx-stmt-key line)
                                              (structure-seen-index earlier))))
                    (structure-seen-index earlier))
         (structure-seen-index (cons line earlier)))
  :hints (("Goal" :in-theory (disable bx-stmt-key hons-acons hons-get))))

(defthm structure-empty-seen-index
  (equal (structure-seen-index nil) nil))

(local (in-theory (disable structure-seen-index hons-acons hons-get)))

; The audit records one order note per first occurrence that fails.  Its
; name, signature, package and repeat tables match the specification scan.

(defun structure-order-item-count (items)
  (if (endp items)
      0
    (+ (if (and (eq (caar items) :note)
                (equal (cadar items) "line that could not be admitted in order"))
           1
         0)
       (structure-order-item-count (cdr items)))))

(defthm structure-order-item-count-of-nil
  (equal (structure-order-item-count nil) 0))

(defthm structure-order-item-count-of-append
  (equal (structure-order-item-count (append a b))
         (+ (structure-order-item-count a) (structure-order-item-count b))))

(defthm structure-order-item-count-of-revappend
  (equal (structure-order-item-count (revappend a b))
         (+ (structure-order-item-count a) (structure-order-item-count b))))

(defthm structure-order-item-count-of-reverse
  (equal (structure-order-item-count (reverse notes))
         (structure-order-item-count notes)))

(defun structure-order-item (line problems)
  (bx-note "line that could not be admitted in order"
           (list (bx-introduced line)
                 (if (member-equal (car line) '("theorem" "axiom" "reserve"))
                     (caadr line)
                   nil)
                 problems)))

(defthm structure-check-first-line
  (implies
   (consp lines)
   (equal
    (bx-check-stmts lines signatures names packages
                   (structure-seen-index earlier) notes)
    (if (member-equal (car lines) earlier)
        (bx-check-stmts (cdr lines) signatures names packages
                       (structure-seen-index earlier) notes)
      (let* ((line (car lines))
             (problems (car (bx-check-stmt line signatures names packages))))
        (bx-check-stmts
         (cdr lines)
         (structure-record-signatures (structure-signatures line) signatures)
         (structure-record-names (structure-names line) names)
         (structure-record-package line packages)
         (structure-seen-index (cons line earlier))
         (if (structure-line-orderp line signatures names packages)
             notes
           (cons (structure-order-item line problems) notes)))))))
  :hints (("Goal" :expand ((bx-check-stmts lines signatures names packages
                                          (structure-seen-index earlier) notes))
                  :in-theory (disable bx-check-stmts bx-check-stmt bx-stmt-key
                                      bx-introduced structure-record-signatures
                                      structure-record-names structure-record-package
                                      structure-signatures structure-line-orderp
                                      structure-names))))

(defthm structure-check-empty-tail
  (implies (not (consp lines))
           (equal (bx-check-stmts lines signatures names packages seen notes)
                  (list (reverse notes) signatures names packages seen))))

(defthm structure-count-one-order-item
  (equal (structure-order-item-count (cons (structure-order-item line problems) notes))
         (+ 1 (structure-order-item-count notes)))
  :hints (("Goal" :in-theory (disable bx-introduced))))

(defun structure-order-induction (lines signatures names packages earlier notes)
  (declare (xargs :measure (acl2-count lines)))
  (cond
   ((endp lines) (list signatures names packages earlier notes))
   ((member-equal (car lines) earlier)
    (structure-order-induction (cdr lines) signatures names packages earlier notes))
   (t
    (let ((line (car lines)))
      (mv-let (problems ignored-signatures ignored-names ignored-packages)
        (bx-check-stmt line signatures names packages)
        (declare (ignore ignored-signatures ignored-names ignored-packages))
        (structure-order-induction
       (cdr lines)
       (structure-record-signatures (structure-signatures line) signatures)
       (structure-record-names (structure-names line) names)
       (structure-record-package line packages)
       (cons line earlier)
       (if (structure-line-orderp line signatures names packages)
           notes
         (cons (structure-order-item line problems) notes))))))))


(local (set-induction-depth-limit 1))

(defthm structure-check-statements-order
  (let ((result (bx-check-stmts lines signatures names packages
                               (structure-seen-index earlier) notes))
        (model (structure-order-scan lines signatures names packages earlier)))
    (and (equal (structure-order-item-count (car result))
                (+ (len (car model)) (structure-order-item-count notes)))
         (equal (mv-nth 1 result) (mv-nth 1 model))
         (equal (mv-nth 2 result) (mv-nth 2 model))
         (equal (mv-nth 3 result) (mv-nth 3 model))
         (equal (mv-nth 4 result) (structure-seen-index (mv-nth 4 model)))))
  :hints (("Goal" :induct (structure-order-induction lines signatures names packages
                                                     earlier notes)
                  :in-theory (disable bx-check-stmts bx-check-stmt bx-stmt-key bx-introduced
                                      structure-record-signatures structure-record-names
                                      structure-record-package structure-signatures
                                      structure-line-orderp structure-names
                                      structure-order-item structure-order-item-count reverse)))
  :rule-classes nil)

; The context of a whole input is obtained by scanning its library prefix
; first.  The checker stops at the first violation; collecting violations
; preserves the test for a violation anywhere.

(defthm structure-order-scan-components
  (let ((scan (structure-order-scan lines signatures names packages earlier)))
    (equal (list (car scan) (mv-nth 1 scan) (mv-nth 2 scan)
                 (mv-nth 3 scan) (mv-nth 4 scan))
           scan))
  :hints (("Goal" :induct (structure-order-scan lines signatures names packages
                                               earlier)
                  :in-theory (disable structure-line-orderp structure-terms
                                      structure-signatures structure-names
                                      structure-record-signatures structure-record-names
                                      structure-record-package))))

(defthm structure-order-scan-of-append
  (equal (structure-order-scan (append prefix lines)
                               signatures names packages earlier)
         (mv-let (faults signatures1 names1 packages1 earlier1)
           (structure-order-scan prefix signatures names packages earlier)
           (mv-let (faults1 signatures2 names2 packages2 earlier2)
             (structure-order-scan lines signatures1 names1 packages1 earlier1)
             (mv (append faults faults1) signatures2 names2 packages2 earlier2))))
  :hints (("Goal" :induct (structure-order-scan prefix signatures names packages
                                               earlier)
                  :in-theory (disable structure-line-orderp structure-terms
                                      structure-signatures structure-names
                                      structure-record-signatures structure-record-names
                                      structure-record-package))))
