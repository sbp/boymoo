(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h4-book-state-known-evidence (evidence known)
  (if (endp evidence)
      known
    (proof-with-checked-results
        ((literal (proof-step-first (car evidence))))
      (h4-book-state-known-evidence
       (cdr evidence) (table-put known literal (car evidence))))))

(defun h4-book-state-evidence-at (known term)
  (let ((entry (assoc-equal term known)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h4-book-state-equation-premise (proof test known)
  (if (proof-is-call test *proof-equal*)
      (proof-with-checked-results
          ((left (proof-term-at test 1))
           (right (proof-term-at test 2)))
        (if (equal left right)
            (proof-proof-reflexive proof left)
          (h4-book-state-evidence-at known test)))
    (h4-book-state-evidence-at known test)))

(defun h4-book-state-equation-premises (proof test known premises)
  (declare (xargs :measure (acl2-count test)))
  (cond
   ((failure-p premises) premises)
   ((and (proof-is-call test *proof-if*)
         (equal (cadddr test) *proof-false*))
    (h4-book-state-equation-premises
     proof (caddr test) known
     (h4-book-state-equation-premises proof (cadr test) known premises)))
   ((and (proof-is-call test *proof-if*) (endp (cdddr test)))
    '(:failure "failure" ""))
   (t (proof-with-checked-results
          ((premise (h4-book-state-equation-premise proof test known)))
        (cons premise premises)))))

(defun h4-book-state-equation-instance (p name term evidence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((rule (proof-proof-fact proof name nil))
         (literal (proof-step-first rule))
         (guarded (proof-is-call literal *library-implies*))
         (equation (if guarded (proof-term-at literal 2) literal)))
      (if (not (proof-is-call equation *proof-equal*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((left (proof-term-at equation 1))
             (match (h4-tactics-match-term left term nil)))
          (if (not (car match))
              '(:failure "failure" "")
            (proof-with-checked-results
                ((instance (proof-proof-instantiate proof rule
                                                    (table-items (cdr match)))))
              (if (not guarded)
                  instance
                (proof-with-checked-results
                    ((known (h4-book-state-known-evidence evidence nil))
                     (literal (proof-step-first instance))
                     (guard (proof-term-at literal 1))
                     (premises (h4-book-state-equation-premises proof guard known nil))
                     (conjoined (h4-book-division-conjunction p (reverse premises))))
                  (h4-tactics-tactics-modus-ponens p instance conjoined))))))))))

(defun h4-book-state-indexed-state-init (p read write laws evidence)
  (proof-with-checked-results ((laws (proof-list-of-length laws 4)))
    (cons :h4-indexed-state (list* p read write (append laws (list evidence))))))

(defun h4-book-state-indexed-state-p (indexed)
  (nth 1 indexed))

(defun h4-book-state-indexed-state-read (indexed)
  (nth 2 indexed))

(defun h4-book-state-indexed-state-write (indexed)
  (nth 3 indexed))

(defun h4-book-state-indexed-state-lookup (indexed)
  (nth 4 indexed))

(defun h4-book-state-indexed-state-overwrite (indexed)
  (nth 5 indexed))

(defun h4-book-state-indexed-state-commute (indexed)
  (nth 6 indexed))

(defun h4-book-state-indexed-state-identity (indexed)
  (nth 7 indexed))

(defun h4-book-state-indexed-state-evidence (indexed)
  (nth 8 indexed))

(defun h4-book-state-indexed-state-on-write (indexed law term)
  (h4-book-state-equation-instance
   (h4-book-state-indexed-state-p indexed) law term
   (table-values (h4-book-state-indexed-state-evidence indexed))))

(defun h4-book-state-indexed-state-reduce-lookup (indexed term write-call)
  (let ((proof (library-library-proof (h4-book-state-indexed-state-p indexed))))
    (proof-with-checked-results
        ((result (h4-book-state-indexed-state-on-write
                  indexed (h4-book-state-indexed-state-lookup indexed) term))
         (index (proof-term-at term 1))
         (written (proof-term-at write-call 2))
         (test (if (equal index written)
                   (proof-proof-reflexive proof index)
                 (h4-book-state-evidence-at
                  (h4-book-state-indexed-state-evidence indexed)
                  (proof-neg (proof-eq index written)))))
         (literal (proof-step-first result))
         (conditional (proof-term-at literal 2))
         (selected (proof-proof-select proof conditional test)))
      (proof-proof-chain proof result (list selected)))))

(defun h4-book-state-indexed-state-reduce-overwrite (indexed term)
  (let ((write (h4-book-state-indexed-state-write indexed)))
    (and (proof-is-call term write)
      (proof-with-checked-results ((inner (proof-term-at term 3)))
        (and (proof-is-call inner write)
          (proof-with-checked-results
              ((index (proof-term-at term 2))
               (other (proof-term-at inner 2)))
            (and (equal index other)
              (h4-book-state-indexed-state-on-write
               indexed (h4-book-state-indexed-state-overwrite indexed) term))))))))

(defun h4-book-state-indexed-state-reduce (indexed term)
  (if (proof-is-call term (h4-book-state-indexed-state-read indexed))
      (proof-with-checked-results ((written (proof-term-at term 2)))
        (if (proof-is-call written (h4-book-state-indexed-state-write indexed))
            (h4-book-state-indexed-state-reduce-lookup indexed term written)
          (h4-book-state-indexed-state-reduce-overwrite indexed term)))
    (h4-book-state-indexed-state-reduce-overwrite indexed term)))

(defun h4-book-state-indexed-state-restore (n indexed term original)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h4-book-state-indexed-state-restore")
    (proof-with-checked-results ((parts (proof-list-of-length term 4)))
      (let* ((p (h4-book-state-indexed-state-p indexed))
             (proof (library-library-proof p))
             (value (cadr parts))
             (slot (caddr parts))
             (written (cadddr parts)))
        (cond
         ((not (equal value (list (h4-book-state-indexed-state-read indexed)
                                  slot original)))
          '(:failure "failure" ""))
         ((equal written original)
          (h4-book-state-indexed-state-on-write
           indexed (h4-book-state-indexed-state-identity indexed) term))
         ((not (proof-is-call written (h4-book-state-indexed-state-write indexed)))
          '(:failure "failure" ""))
         (t
          (proof-with-checked-results ((other (proof-term-at written 2)))
            (if (equal other slot)
                (proof-with-checked-results
                    ((overwrite (h4-book-state-indexed-state-on-write
                                 indexed (h4-book-state-indexed-state-overwrite indexed)
                                 term))
                     (literal (proof-step-first overwrite))
                     (next (proof-term-at literal 2))
                     (rest (h4-book-state-indexed-state-restore
                            (1- n) indexed next original)))
                  (proof-proof-chain proof overwrite (list rest)))
              (proof-with-checked-results
                  ((commute (h4-book-state-indexed-state-on-write
                             indexed (h4-book-state-indexed-state-commute indexed)
                             term))
                   (literal (proof-step-first commute))
                   (outer (proof-term-at literal 2))
                   (inner (proof-term-at outer 3))
                   (rest (h4-book-state-indexed-state-restore
                          (1- n) indexed inner original))
                   (rewritten (h4-book-flatten-rewrite-argument p outer 3 rest)))
                (proof-proof-chain proof commute (list rewritten)))))))))))

(defun h4-book-state-indexed-state-invariant-equation (indexed law view written)
  (h4-book-state-indexed-state-on-write indexed law (list view written)))
