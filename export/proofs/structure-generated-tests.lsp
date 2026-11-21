(in-package "ACL2")

; Two packages import the same symbol of a spelling the exporter tries.

(assign structure-imported-labels-lo (max-absolute-event-number (w state)))

(defpkg "STRUCTURE-LABEL-A" '(acl2::|F constraint 1|))
(defpkg "STRUCTURE-LABEL-B" '(acl2::|F constraint 1|))

(encapsulate (((structure-label-a::f *) => *))
  (local (defun structure-label-a::f (x) x))
  (defthm structure-label-a::law (equal x x)
    :rule-classes ((:rewrite :corollary (equal (structure-label-a::f 0) 0)))))

(encapsulate (((structure-label-b::f *) => *))
  (local (defun structure-label-b::f (x) x))
  (defthm structure-label-b::law (equal x x)
    :rule-classes ((:rewrite :corollary (equal (structure-label-b::f 0) 0)))))

(assign structure-imported-labels-hi (max-absolute-event-number (w state)))

(defun structure-test-imported-labels-in-lines (lines)
  (and (equal (structure-introduction-count 'structure-label-a::|F constraint 1 1| lines nil) 1)
       (equal (structure-introduction-count 'structure-label-b::|F constraint 1 1| lines nil) 1)
       (equal (structure-introduction-count 'acl2::|F constraint 1| lines nil) 0)))

(structure-test-result
 "shared-import-formula-names"
 (let ((ground (structure-test-ground-definitions (@ structure-ground-spec))))
   (mv-let (library lib-program lib-notes)
     (bx-library-lines ground (@ structure-imported-labels-hi) nil (w state))
     (declare (ignore lib-program lib-notes))
     (mv-let (book program notes aids)
       (bx-book-lines ground (@ structure-boot-hi) (@ structure-imported-labels-lo)
                      (@ structure-imported-labels-hi) nil "" "" (w state))
       (declare (ignore program aids))
       (not (and (structure-test-imported-labels-in-lines library)
                 (structure-test-imported-labels-in-lines book)
                 (equal (structure-order-note-count notes) 0)))))))

; Both closing records resolve to F's constraint.  The corollary stays
; unnamed at both records, and their signatures put different functions
; first.

(assign structure-nested-labels-lo (max-absolute-event-number (w state)))

(encapsulate (((structure-nested-f *) => *))
  (local (defun structure-nested-f (x) x))
  (encapsulate (((structure-nested-g *) => *))
    (local (defun structure-nested-g (x) (structure-nested-f x)))
    (defthm structure-nested-g-law (equal (structure-nested-g x) (structure-nested-f x))
      :rule-classes ((:rewrite :corollary
                      (equal (structure-nested-g 0) (structure-nested-f 0))))))
  (defthm structure-nested-f-law (equal (structure-nested-f x) (structure-nested-g x))
    :hints (("Goal" :use structure-nested-g-law))
    :rule-classes nil))

(assign structure-nested-labels-hi (max-absolute-event-number (w state)))

(defun structure-test-nested-reuse-in-lines (name lines notes)
  (and (equal (structure-introduction-count name lines nil) 2)
       (structure-order-notes-report-conflict-p name notes)))

(defun structure-test-nested-labels (ground boot-hi lo hi wrld)
  (let* ((name '|STRUCTURE-NESTED-F constraint 2|)
         (records (structure-range-events wrld lo hi nil)))
    (mv-let (library lib-program lib-notes)
      (bx-library-lines ground hi nil wrld)
      (declare (ignore lib-program))
      (mv-let (book program notes aids)
        (bx-book-lines ground boot-hi lo hi nil "" "" wrld)
        (declare (ignore program aids))
        (and (structure-unregistered-symbol-p name wrld)
             (equal (structure-name-source name)
                    (structure-symbol-spelling 'structure-nested-f))
             (structure-range-recordsp wrld lo hi)
             (structure-naming-recordsp records)
             (equal (structure-name-opportunities name records wrld) 2)
             (structure-test-nested-reuse-in-lines name library lib-notes)
             (structure-test-nested-reuse-in-lines name book notes))))))

(structure-test-result
 "nested-constraint-name-reuse"
 (not (structure-test-nested-labels
       (structure-test-ground-definitions (@ structure-ground-spec))
       (@ structure-boot-hi) (@ structure-nested-labels-lo) (@ structure-nested-labels-hi)
       (w state))))
