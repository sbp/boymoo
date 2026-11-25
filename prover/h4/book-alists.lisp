(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-alists-lookup* (proof-sym "HONS-ASSOC-EQUAL" "ACL2"))
(defconst *h4-book-alists-key-equal* (proof-sym "HONS-EQUAL" "ACL2"))
(defconst *h4-book-alists-remove* (proof-sym "HONS-REMOVE-ASSOC" "ACL2"))
(defconst *h4-book-alists-fork* (proof-sym "FAST-ALIST-FORK" "ACL2"))
(defconst *h4-book-alists-lookup-after-removal*
  (proof-sym "HONS-ASSOC-EQUAL-REMOVE-ASSOC" "ACL2"))

(defun h4-book-alists-heads (terms)
  (cond ((endp terms) nil)
        ((proof-compound (car terms))
         (proof-with-checked-results
             ((head (proof-term-at (car terms) 0))
              (rest (h4-book-alists-heads (cdr terms))))
           (cons head rest)))
        (t (h4-book-alists-heads (cdr terms)))))

(defun h4-book-alists-keyed-removal (formula)
  (proof-with-checked-results
      ((terms (h4-book-tactics-terms formula))
       (heads (h4-book-alists-heads terms)))
    (and (member-equal *h4-book-alists-remove* heads)
         (or (member-equal *h4-book-alists-lookup* heads)
             (member-equal *h4-book-alists-fork* heads))
         t)))

(defun h4-book-alists-key-call-p (term)
  (or (proof-is-call term *h4-book-alists-lookup*)
      (proof-is-call term *h4-book-alists-remove*)
      (proof-is-call term *h4-book-alists-fork*)
      (proof-is-call term *proof-if*)))

(defun h4-book-alists-key-alias (proof step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (and (proof-is-call literal *proof-equal*)
         (proof-with-checked-results
             ((left (proof-term-at literal 1))
              (right (proof-term-at literal 2)))
           (and (not (equal left right))
                (proof-with-checked-results
                    ((sides (proof-list-of-length (cdr literal) 2)))
                  (and (not (h4-book-alists-key-call-p (car sides)))
                       (not (h4-book-alists-key-call-p (cadr sides)))
                       (proof-with-checked-results
                           ((smaller (h4-book-tactics-smaller right left)))
                         (if smaller step (proof-proof-symmetric proof step))))))))))

(defun h4-book-alists-key-alias-list (proof entries)
  (if (endp entries)
      nil
    (proof-with-checked-results
        ((alias (h4-book-alists-key-alias proof (cdar entries)))
         (rest (h4-book-alists-key-alias-list proof (cdr entries))))
      (if alias (cons alias rest) rest))))

(defun h4-book-alists-key-search-key-aliases (search evidence)
  (h4-book-alists-key-alias-list
   (library-library-proof (h4-book-tactics-book-search-p search)) evidence))

(defun h4-book-alists-put-new (dict key value)
  (if (assoc-equal key dict) dict (table-put dict key value)))

(defun h4-book-alists-index-steps (steps evidence)
  (if (endp steps)
      evidence
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (h4-book-alists-index-steps (cdr steps)
                                 (table-put evidence literal (car steps))))))

(defun h4-book-alists-substitute-positions (proof step equality positions)
  (if (endp positions)
      step
    (let ((term (caar positions))
          (path (cadar positions)))
      (proof-with-checked-results
          ((changed (if path
                        (proof-with-checked-results
                            ((literal (proof-step-first equality))
                             (left (proof-term-at literal 1)))
                          (if (equal term left)
                              (proof-proof-rewrite proof step equality (cons 1 path))
                            step))
                      step)))
        (h4-book-alists-substitute-positions proof changed equality (cdr positions))))))

(defun h4-book-alists-substitute-steps (proof equality entries evidence)
  (if (endp entries)
      evidence
    (proof-with-checked-results
        ((literal (proof-step-first (cdar entries)))
         (positions (h4-book-equivalence-positions literal nil))
         (changed (h4-book-alists-substitute-positions proof (cdar entries)
                                                      equality positions))
         (key (proof-step-first changed)))
      (h4-book-alists-substitute-steps
       proof equality (cdr entries) (h4-book-alists-put-new evidence key changed)))))

(defun h4-book-alists-substitute-aliases (proof aliases evidence)
  (if (endp aliases)
      evidence
    (proof-with-checked-results
        ((updated (h4-book-alists-substitute-steps proof (cdar aliases) evidence evidence)))
      (h4-book-alists-substitute-aliases proof (cdr aliases) updated))))

(defun h4-book-alists-key-search-substitute-keys (search evidence)
  (proof-with-checked-results
      ((aliases (h4-book-alists-key-search-key-aliases search evidence))
       (indexed (h4-book-alists-index-steps aliases nil)))
    (h4-book-alists-substitute-aliases
     (library-library-proof (h4-book-tactics-book-search-p search)) indexed evidence)))

(defun h4-book-alists-key-search-expose-removal (search term)
  (let* ((p (h4-book-tactics-book-search-p search))
         (proof (library-library-proof p)))
    (proof-with-checked-results ((head (proof-term-at term 0)))
      (cond ((or (equal head *library-car*) (equal head *library-cdr*))
             (proof-with-checked-results ((argument (proof-term-at term 1)))
               (and (proof-is-call argument *proof-cons*)
                    (library-library-axiom
                     p (if (equal head *library-car*) "CAR-CONS" "CDR-CONS")
                     (cdr argument)))))
            ((proof-is-call term *h4-book-alists-remove*)
             (proof-with-checked-results ((sequence (proof-term-at term 2)))
               (and (proof-is-call sequence *proof-cons*)
                    (proof-proof-unfold proof term))))))))

(defun h4-book-alists-normalize-with-replies (search literal others expand replies)
  (h4-tactics-tactics-normalize (h4-book-tactics-book-search-p search) literal others expand
                                nil (cons :h4-tactics-provider replies)))

(defun h4-book-alists-normalize-removal (n search literal others expand replies result)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "h4-book-alists-normalize-removal"))
        ((h4-tactics-request-p result)
         (let* ((term (h4-tactics-request-term result))
                (reply (h4-book-alists-key-search-expose-removal search term))
                (replies (table-put replies term reply))
                (next (and (< 1 n) (h4-book-alists-normalize-with-replies
                                    search literal others expand replies))))
           (h4-book-alists-normalize-removal (1- n) search literal others expand replies next)))
        (t result)))

(defun h4-book-alists-conditional-or-cons-p (terms)
  (and (consp terms)
       (or (proof-is-call (car terms) *proof-if*)
           (proof-is-call (car terms) *proof-cons*)
           (h4-book-alists-conditional-or-cons-p (cdr terms)))))

(defun h4-book-alists-other-evidence (entries literal)
  (if (endp entries)
      nil
    (proof-with-checked-results
        ((key (proof-step-first (cdar entries)))
         (rest (h4-book-alists-other-evidence (cdr entries) literal)))
      (if (equal key literal) rest (cons (cdar entries) rest)))))

(defun h4-book-alists-selected-equation (search step evidence)
  (let* ((p (h4-book-tactics-book-search-p search))
         (proof (library-library-proof p))
         (expand (append *h4-book-tactics-logic* (list *h4-book-alists-key-equal*))))
    (proof-with-checked-results ((literal (proof-step-first step)))
      (cond
       ((proof-is-call literal *proof-not*)
        (proof-with-checked-results ((term (proof-term-at literal 1)))
          (and (proof-is-call term *h4-book-alists-lookup*)
               (proof-with-checked-results
                   ((expandable (h4-book-tactics-book-search-expandable search term evidence)))
                 (and expandable
                      (proof-with-checked-results
                          ((opened (proof-proof-unfold proof term))
                           (equation (proof-step-first opened))
                           (right (proof-term-at equation 2))
                           (value (h4-tactics-tactics-normalize
                                   p right (table-values evidence) expand nil nil))
                           (chain (proof-proof-chain proof opened (list value))))
                        (proof-proof-rewrite proof step chain '(1 1))))))))
       ((proof-is-call literal *proof-equal*)
        (proof-with-checked-results ((terms (h4-book-tactics-terms literal)))
          (and (h4-book-alists-conditional-or-cons-p terms)
               (proof-with-checked-results
                   ((others (h4-book-alists-other-evidence evidence literal))
                    (initial (h4-book-alists-normalize-with-replies search literal others expand nil))
                    (value (h4-book-alists-normalize-removal 1000000 search literal
                                                            others expand nil initial))
                    (equation (proof-step-first value))
                    (right (proof-term-at equation 2)))
                 (and (not (equal right literal))
                      (proof-proof-rewrite proof step value '(1)))))))))))

(defun h4-book-alists-selected-equation-list (search entries evidence)
  (if (endp entries)
      nil
    (proof-with-checked-results
        ((step (h4-book-alists-selected-equation search (cdar entries) evidence))
         (rest (h4-book-alists-selected-equation-list search (cdr entries) evidence)))
      (if step (cons step rest) rest))))

(defun h4-book-alists-key-search-selected-equations (search evidence)
  (h4-book-alists-selected-equation-list search evidence evidence))

(defun h4-book-alists-join-ends (proof ends direction right evidence)
  (if (endp ends)
      evidence
    (let ((previous (cdar ends)))
      (proof-with-checked-results
          ((literal (proof-step-first previous))
           (limit (proof-term-at literal 2)))
        (if (equal limit right)
            (h4-book-alists-join-ends proof (cdr ends) direction right evidence)
          (proof-with-checked-results
              ((reverse (proof-proof-symmetric proof previous))
               (joined (proof-proof-chain proof reverse (list direction)))
               (key (proof-step-first joined)))
            (h4-book-alists-join-ends
             proof (cdr ends) direction right (h4-book-alists-put-new evidence key joined))))))))

(defun h4-book-alists-join-directions (proof directions visited evidence)
  (if (endp directions)
      (cons visited evidence)
    (let ((direction (car directions)))
      (proof-with-checked-results
          ((literal (proof-step-first direction))
           (parts (proof-list-of-length literal 3)))
        (let* ((left (cadr parts))
               (right (caddr parts))
               (ends (table-get visited left nil)))
          (proof-with-checked-results
              ((updated (h4-book-alists-join-ends proof ends direction right evidence)))
            (h4-book-alists-join-directions
             proof (cdr directions)
             (table-put visited left (h4-book-alists-put-new ends right direction))
             updated)))))))

(defun h4-book-alists-join-entries (proof entries visited evidence)
  (if (endp entries)
      evidence
    (let ((step (cdar entries)))
      (proof-with-checked-results ((literal (proof-step-first step)))
        (if (proof-is-call literal *proof-equal*)
            (proof-with-checked-results
                ((reverse (proof-proof-symmetric proof step))
                 (updated (h4-book-alists-join-directions
                           proof (list step reverse) visited evidence)))
              (h4-book-alists-join-entries proof (cdr entries) (car updated) (cdr updated)))
          (h4-book-alists-join-entries proof (cdr entries) visited evidence))))))

(defun h4-book-alists-key-search-join-equalities (search evidence)
  (h4-book-alists-join-entries
   (library-library-proof (h4-book-tactics-book-search-p search)) evidence nil evidence))

(defun h4-book-alists-constructor-terms (proof terms evidence)
  (if (endp terms)
      evidence
    (if (proof-is-call (car terms) *proof-cons*)
        (proof-with-checked-results
            ((shape (proof-proof-fact proof "consp-cons"
                                      (seq-zip (list *library-x* *library-y*) (cdar terms))))
             (literal (proof-step-first shape)))
          (h4-book-alists-constructor-terms
           proof (cdr terms) (h4-book-alists-put-new evidence literal shape)))
      (h4-book-alists-constructor-terms proof (cdr terms) evidence))))

(defun h4-book-alists-constructor-evidence (proof entries evidence)
  (if (endp entries)
      evidence
    (proof-with-checked-results
        ((literal (proof-step-first (cdar entries)))
         (terms (h4-book-tactics-terms literal))
         (updated (h4-book-alists-constructor-terms proof terms evidence)))
      (h4-book-alists-constructor-evidence proof (cdr entries) updated))))

(defun h4-book-alists-key-search-hypotheses (search premises)
  (let* ((p (h4-book-tactics-book-search-p search))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((evidence (h4-book-tactics-book-search-hypotheses search premises))
         (substituted (h4-book-alists-key-search-substitute-keys search evidence))
         (shaped (h4-book-alists-constructor-evidence proof substituted substituted))
         (selected (h4-book-alists-key-search-selected-equations search shaped))
         (additional (h4-book-measures-expand-evidence p selected))
         (updated (h4-book-alists-index-steps additional shaped)))
      (h4-book-alists-key-search-join-equalities search updated))))

(defun h4-book-alists-induction-attempt (search formula plan replies)
  (let ((hooked (h4-book-tactics-book-search-with-hooks
                 search replies *h4-book-alists-lookup-after-removal*)))
    (h4-book-tactics-book-search-induction
     hooked formula (car plan) (cadr plan) (caddr plan) (cadddr plan) 5)))

(defun h4-book-alists-induction (n search formula plan replies attempt)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "fuel" "h4-book-alists-induction") search)
    (let ((result (car attempt)))
      (if (h4-book-tactics-hypotheses-request-p result)
          (let* ((premises (h4-book-tactics-hypotheses-request-premises result))
                 (evidence (h4-book-alists-key-search-hypotheses search premises))
                 (replies (table-put replies premises evidence))
                 (next (and (< 1 n) (h4-book-alists-induction-attempt search formula plan replies))))
            (h4-book-alists-induction (1- n) search formula plan replies next))
        (cons result (h4-book-tactics-book-search-with-hooks (cdr attempt) :default nil))))))

(defun h4-book-alists-try-plan (search formula plan)
  (let* ((ready (h4-book-tactics-book-search-with-budgets search 80 10000))
         (initial (h4-book-alists-induction-attempt ready formula plan nil)))
    (h4-book-alists-induction 1000000 ready formula plan nil initial)))

(defun h4-book-alists-try-plans (formula plans left attempt)
  (declare (xargs :measure (acl2-count plans)))
  (let ((result (car attempt)))
    (if (and (failure-p result)
             (member-equal (cadr result) '("unproved" "inapplicable-step" "assertion" "recursion")))
        (if (or (endp plans) (zp left))
            nil
          (h4-book-alists-try-plans formula (cdr plans) (1- left)
                                  (h4-book-alists-try-plan (cdr attempt) formula (car plans))))
      result)))

(defun h4-book-alists-keyed-removal-proof-with-templates (p formula tables)
  (proof-with-checked-results ((keyed (h4-book-alists-keyed-removal formula)))
    (and keyed
         (proof-with-checked-results
             ((search (h4-book-tactics-book-search-init-with-templates p tables))
              (plans (h4-book-tactics-book-search-induction-options search formula)))
           (and (consp plans)
                (h4-book-alists-try-plans formula (cdr plans) 2
                                        (h4-book-alists-try-plan search formula (car plans))))))))

