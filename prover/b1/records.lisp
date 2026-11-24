(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-records-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *b1-records-v* (proof-sym "V" "ACL2"))

(defun b1-records-install-association (lib name label same unfold)
  (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
      lib
    (let* ((marker (if same *library-x* *library-y*))
           (pair (list *proof-cons* marker *b1-records-v*))
           (lookup (list *b1-records-assoc* *library-x* (list *proof-cons* pair *library-z*))))
      (proof-with-checked-results
       ((guard (if same nil (proof-eq *library-x* *library-y*)))
        (different (if same nil (proof-proof-assume (library-library-proof lib) guard nil)))
        (step (b1-logic-bookproof-normalize lib lookup (and different (list different))
                                            unfold nil nil nil nil))
        (claim (proof-step-first step)))
       (library-library-lemma lib label claim step (and guard (list guard)))))))

(defun b1-records-association-pair (lib key field value rest)
  (let* ((same (equal key field))
         (label (if same "ASSOC-KEY-HERE" "ASSOC-KEY-TAIL"))
         (name (proof-sym (concatenate 'string "SELF-" label) "ACL2"))
         (unfold (list *b1-records-assoc* *b1-logic-atom* *b1-logic-endp* *proof-not*)))
    (proof-with-checked-results
     ((lib (b1-records-install-association lib name label same unfold)))
     (let* ((proof (library-library-proof lib))
            (bindings (list (list *library-x* key) (list *library-y* field)
                            (list *library-z* rest) (list *b1-records-v* value))))
       (proof-with-checked-results
        ((step (if same
                   (proof-proof-fact proof name bindings)
                 (proof-with-checked-results
                  ((different (b1-logic-bookproof-normalize-proof
                               lib (proof-neg (proof-eq key field)) nil (list *proof-not*) nil nil)))
                  (proof-proof-use proof name bindings (list different))))))
        (cons step lib))))))

(defun b1-records-association-step (lib term)
  (if (not (proof-is-call term *b1-records-assoc*))
      (cons nil lib)
    (proof-with-checked-results ((key (proof-term-at term 1)))
      (if (not (proof-is-call key *proof-quote*))
          (cons nil lib)
        (proof-with-checked-results ((items (proof-term-at term 2)))
          (if (not (proof-is-call items *proof-cons*))
              (cons nil lib)
            (proof-with-checked-results
             ((actuals (proof-list-of-length (cdr term) 2))
              (items (proof-list-of-length (cdr (cadr actuals)) 2)))
             (let ((pair (car items)) (rest (cadr items)))
               (if (not (proof-is-call pair *proof-cons*))
                   (cons nil lib)
                 (proof-with-checked-results ((field (proof-term-at pair 1)))
                   (if (not (proof-is-call field *proof-quote*))
                       (cons nil lib)
                     (proof-with-checked-results ((pair (proof-list-of-length (cdr pair) 2)))
                       (b1-records-association-pair lib key (car pair) (cadr pair) rest)))))))))))))
