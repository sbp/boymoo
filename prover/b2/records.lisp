(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defmacro b2-records-declare-events ()
  '(progn

(defconst *b2-records-get* (proof-sym "G" "ACL2"))
(defconst *b2-records-set* (proof-sym "S" "ACL2"))
(defconst *b2-records-get-nil* (proof-sym "G-OF-NIL-IS-NIL" "ACL2"))
(defconst *b2-records-set-same* (proof-sym "G-SAME-S" "ACL2"))
(defconst *b2-records-set-different* (proof-sym "G-DIFF-S" "ACL2"))

(defconst *b2-records-record-corollaries*
  (list *b2-records-get-nil*
        (proof-sym "G-OF-S-REDUX" "ACL2")
        (proof-sym "NON-NIL-IF-G-NON-NIL" "ACL2")
        (proof-sym "S-NON-NIL-CANNOT-BE-NIL" "ACL2")))

(defun b2-records-get-nil (lib key)
  (let* ((proof (library-library-proof lib))
         (lookup (list *b2-records-get* key *proof-false*))
         (fact (assoc-equal *b2-records-get-nil* (proof-proof-facts proof))))
    (if (not fact)
        '(:failure "tactic-rejected" "")
      (proof-with-checked-results
       ((pattern (proof-term-at (cdr fact) 0))
        (premise (b2-tactics-tactics-exact lib *b2-records-get-nil* pattern (proof-neg lookup))))
       (b2-tactics-tactics-close-false lib lookup premise)))))

(defun b2-records-set-same-pattern (lib)
  (proof-with-checked-results
   ((clause (b2-arithmetic-require *b2-records-set-same*
                                   (proof-proof-facts (library-library-proof lib)))))
   (proof-term-at clause 0)))

(defun b2-records-record-corollary-consequent (premise lib goal key value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((impossible (proof-proof-assume proof goal nil))
      (lookup (proof-eq (list *b2-records-get* key goal) value))
      (pattern (b2-records-set-same-pattern lib))
      (identity (b2-tactics-tactics-exact lib *b2-records-set-same* pattern lookup))
      (closed (b2-tactics-tactics-close-false lib goal impossible))
      (empty (proof-proof-rewrite proof identity closed '(1 1 2)))
      (nil-lookup (b2-records-get-nil lib key))
      (nil-result (proof-proof-rewrite proof empty nil-lookup '(1 1)))
      (nil-result (proof-proof-tidy proof nil-result))
      (value-nil (proof-proof-symmetric proof nil-result))
      (contradiction (proof-proof-rewrite proof premise value-nil '(1)))
      (contradiction (proof-proof-tidy proof contradiction)))
     (proof-proof-front proof contradiction goal))))

(defun b2-records-get-of-set (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((fields (proof-list-of-length formula 3))
      (call (cadr fields))
      (rhs (proof-list-of-length (caddr fields) 4))
      (terms (proof-list-of-length call 3))
      (set-call (proof-list-of-length (caddr terms) 4))
      (test (cadr rhs))
      (value (caddr rhs))
      (unchanged (cadddr rhs))
      (a (cadr terms))
      (record (cadddr set-call))
      (yes (proof-proof-assume proof test t))
      (no (proof-proof-assume proof test nil))
      (target (proof-eq (list *b2-records-get* a (list *b2-records-set* a value record)) value))
      (pattern (b2-records-set-same-pattern lib))
      (same (b2-tactics-tactics-exact lib *b2-records-set-same* pattern target))
      (same (proof-proof-rewrite proof same yes '(1 1 2 1)))
      (same (proof-proof-tidy proof same))
      (different (b2-tactics-tactics-use-fact
                  lib *b2-records-set-different* (proof-eq call unchanged) (list no) nil nil 0 nil))
      (yes (b2-tactics-tactics-solve lib formula (list yes) nil (list same) 0 nil))
      (no (b2-tactics-tactics-solve lib formula (list no) nil (list different) 0 nil)))
     (proof-proof-cases proof test yes no))))

(defun b2-records-record-corollary (lib name formula)
  (cond
   ((equal name *b2-records-get-nil*)
    (b2-tactics-tactics-solve lib formula nil
                             (list *b2-records-get* (proof-sym "G-AUX" "ACL2")
                                   (proof-sym "ACL2->RCD" "ACL2") (proof-sym "IFRP" "ACL2")
                                   (proof-sym "RCDP" "ACL2"))
                             nil 0 nil))
   ((equal name (proof-sym "G-OF-S-REDUX" "ACL2"))
    (b2-records-get-of-set lib formula))
   (t
    (proof-with-checked-results
     ((fields (proof-list-of-length formula 3))
      (antecedent (cadr fields))
      (goal (caddr fields)))
     (if (equal name (proof-sym "NON-NIL-IF-G-NON-NIL" "ACL2"))
         (proof-with-checked-results
          ((call (b2-tactics-tactics-implication lib antecedent goal nil))
           (premise (cadddr (car call)))
           (key (proof-term-at antecedent 1))
           (nil-lookup (b2-records-get-nil lib key))
           (outcome (b2-tactics-tactics-from-impossible
                     lib goal premise nil nil (list nil-lookup) 1500 nil))
           (result (b2-tactics-tactics-implication lib antecedent goal (cons outcome lib))))
          (car result))
       (proof-with-checked-results
        ((terms (proof-list-of-length goal 4))
         (call (b2-tactics-tactics-implication lib antecedent goal nil))
         (outcome (b2-records-record-corollary-consequent
                   (cadddr (car call)) (cdr call) goal (cadr terms) (caddr terms)))
         (result (b2-tactics-tactics-implication lib antecedent goal (cons outcome (cdr call)))))
        (car result)))))))
))
