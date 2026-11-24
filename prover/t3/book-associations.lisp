(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t3-book-associations-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *t3-book-associations-by-cdr* (proof-sym "ASSOC-EQUAL-CDR" "ACL2"))
(defconst *t3-book-associations-strip-cdrs* (proof-sym "STRIP-CDRS" "ACL2"))
(defconst *t3-book-associations-natp* (proof-sym "NATP" "ACL2"))
(defconst *t3-book-associations-nat-table* (proof-sym "NAT-ALISTP" "ACL2"))
(defconst *t3-book-associations-fixnat-table* (proof-sym "FIXNAT-ALISTP" "ACL2"))
(defconst *t3-book-associations-symbol-table* (proof-sym "R-SYMBOL-ALISTP" "ACL2"))
(defconst *t3-book-associations-term-list* (proof-sym "PSEUDO-TERM-LISTP" "ACL2"))
(defconst *t3-book-associations-termp* (proof-sym "PSEUDO-TERMP" "ACL2"))
(defconst *t3-book-associations-symbolp* (proof-cl "SYMBOLP"))

(defun t3-book-associations-components-visit (n proof recognizer)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-book-associations-components")
    (proof-with-checked-results
     ((literal (proof-step-first recognizer))
      (no (if (proof-is-call literal *proof-if*) (proof-term-at literal 3) nil)))
     (if (equal no *proof-false*)
         (proof-with-checked-results
          ((parts (proof-proof-conjunct proof recognizer))
           (rest (t3-book-associations-components-visit (1- n) proof (cadr parts))))
          (cons (car parts) rest))
       (list recognizer)))))

(defun t3-book-associations-components (lib recognizer)
  (t3-book-associations-components-visit 1000000 (library-library-proof lib) recognizer))

(defun t3-book-associations-component-facts (components facts)
  (declare (xargs :measure (acl2-count components)))
  (if (endp components)
      facts
    (proof-with-checked-results ((literal (proof-step-first (car components))))
      (t3-book-associations-component-facts
       (cdr components) (table-put facts literal (car components))))))

(defun t3-book-associations-invariant-guarded (lib table allowed present)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((subject (proof-term-at table 1)))
      (if (equal subject (list *t3-book-associations-strip-cdrs* *library-y*))
          (proof-with-checked-results
           ((opened (t3-book-spines-shallow lib subject (list present)))
            (changed (proof-proof-rewrite proof allowed opened '(1 1))))
           (proof-proof-tidy proof changed))
        allowed))))

(defun t3-book-associations-normalize (lib term evidence definitions)
  (if (eq (proof-proof-kind (library-library-proof lib)) :t3-book)
      (t3-book-values-book-proofs-normalize
       (t3-book-values-make-book-proofs lib nil nil) term evidence definitions)
    (t3-logic-libraryproofs-normalize lib term evidence definitions)))

(defund t3-book-associations-formula-plan (lib term definitions evidence)
  (proof-with-checked-results ((premise (proof-find-evidence evidence (list term))))
    (cond
     (premise premise)
     ((equal term *proof-true*) (t3-logic-libraryproofs-prove lib term nil nil))
     (t
      (proof-with-checked-results
       ((opened (t3-book-associations-normalize lib term evidence definitions)))
       (let ((value (and opened (caddr (proof-step-first opened)))))
         (cond
          ((and opened (not (equal value term))) (list :transport value opened))
          ((proof-is-call term *proof-if*)
           (proof-with-checked-results ((branches (proof-list-of-length (cdr term) 3)))
             (cons :split branches)))
          (t
           (proof-with-checked-results ((written (proof-write term)))
             '(:failure "Unsupported" ""))))))))))

(defun t3-book-associations-formula-evidence (proof test holds evidence)
  (proof-with-checked-results ((premise (proof-proof-assume proof test holds)))
    (append evidence (list premise))))

(defun t3-book-associations-formula-cases (proof term test yes no)
  (proof-with-checked-results
   ((take-yes (proof-proof-if-true proof term))
    (yes (proof-proof-transport proof yes take-yes))
    (take-no (proof-proof-if-false proof term))
    (no (proof-proof-transport proof no take-no)))
   (proof-proof-cases proof test yes no)))

(defun t3-book-associations-prove-formula (n lib term definitions evidence)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "t3-book-associations-prove-formula"))
   ((failure-p evidence) evidence)
   (t
    (let ((proof (library-library-proof lib))
          (plan (t3-book-associations-formula-plan lib term definitions evidence)))
      (case (car plan)
        (:transport
         (proof-with-checked-results
          ((step (t3-book-associations-prove-formula (1- n) lib (cadr plan) definitions evidence)))
          (proof-proof-transport proof step (caddr plan))))
        (:split
         (let ((test (cadr plan)))
           (proof-with-checked-results
            ((yes (t3-book-associations-prove-formula
                   (1- n) lib (caddr plan) definitions
                   (t3-book-associations-formula-evidence proof test t evidence)))
             (no (t3-book-associations-prove-formula
                  (1- n) lib (cadddr plan) definitions
                  (t3-book-associations-formula-evidence proof test nil evidence))))
            (t3-book-associations-formula-cases proof term test yes no))))
        (otherwise plan))))))

(defun t3-book-associations-invariant-recognize (lib head-type facts)
  (let ((recognized (table-get facts head-type nil)))
    (if recognized
        recognized
      (proof-with-checked-results
       ((normal (t3-book-associations-normalize lib head-type nil (list *proof-not*))))
       (let ((known (and normal (assoc-equal (caddr (proof-step-first normal)) facts))))
         (if known
             (proof-proof-transport (library-library-proof lib) (cdr known) normal)
           '(:failure "Unsupported" "")))))))

(defun t3-book-associations-invariant (lib label lookup table result)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (cons-test (list *proof-consp* y))
         (head (list *library-car* y))
         (tail (list *library-cdr* y))
         (finder (list lookup x y))
         (bindings (list (cons y tail)))
         (pairs (list (list y tail))))
    (proof-with-checked-results
     ((present (proof-proof-assume proof cons-test t))
      (template (proof-subst result (list (cons *proof-result* finder))))
      (theorem (proof-ite table template *proof-true*))
      (allowed (proof-proof-assume proof table t))
      (guarded (t3-book-associations-invariant-guarded lib table allowed present))
      (guarded-first (proof-step-first guarded))
      (guarded-opened (t3-book-spines-shallow lib guarded-first (list present)))
      (unfolded (proof-proof-rewrite proof guarded guarded-opened '(1)))
      (unfolded (proof-proof-tidy proof unfolded))
      (components (t3-book-associations-components lib unfolded))
      (facts (t3-book-associations-component-facts components nil))
      (child (proof-subst table bindings))
      (smaller (library-library-builtin lib 3 y))
      (smaller (proof-proof-discharge proof smaller present))
      (substituted (proof-subst theorem bindings))
      (assumption (proof-ite (proof-step-first smaller) substituted *proof-true*))
      (assumption (proof-proof-assume proof assumption t))
      (use-child (proof-proof-prove-if proof assumption smaller))
      (known-child (if (assoc-equal child facts)
                       (table-get facts child nil)
                     '(:failure "MissingProofInput" "")))
      (tail-result (proof-proof-prove-if proof use-child known-child))
      (inspected (t3-book-spines-shallow lib finder (list present)))
      (test (proof-term-at (caddr (proof-step-first inspected)) 1))
      (matches (proof-proof-assume proof test t))
      (contained (t3-book-spines-shallow lib finder (list present matches)))
      (misses (proof-proof-assume proof test nil))
      (next-entry (t3-book-spines-shallow lib finder (list present misses)))
      (head-result (proof-subst result (list (cons *proof-result* head))))
      (no (if (proof-is-call head-result *proof-if*) (proof-term-at head-result 3) nil))
      (conditional (equal no *proof-true*))
      (head-type (if conditional (caddr head-result) head-result))
      (recognized (t3-book-associations-invariant-recognize lib head-type facts))
      (recognized (if conditional (t3-scan-conclusion lib head-result recognized) recognized))
      (contained (proof-proof-symmetric proof contained))
      (yes (proof-proof-rewrite-result proof recognized contained result *proof-result*))
      (next-entry (proof-proof-symmetric proof next-entry))
      (no (proof-proof-rewrite-result proof tail-result next-entry result *proof-result*))
      (step (proof-proof-cases proof test yes no))
      (atom-proof (proof-proof-assume proof cons-test nil))
      (empty (t3-book-spines-shallow lib finder (list atom-proof)))
      (empty-result (proof-subst result (list (cons *proof-result* *proof-false*))))
      (zero (t3-book-associations-prove-formula
             1000000 lib empty-result (list *t3-book-associations-termp* *t3-logic-atom* *proof-not*)
             nil))
      (empty (proof-proof-symmetric proof empty))
      (base (proof-proof-rewrite-result proof zero empty result *proof-result*))
      (yes (t3-scan-conclusion lib theorem step))
      (no (t3-scan-conclusion lib theorem base))
      (test-cases (proof-proof-cases proof cons-test yes no))
      (ordinal (library-library-builtin lib 1 y))
      (step (proof-proof-induct proof ordinal test-cases theorem
                                (list *library-count* y) (list pairs))))
     (library-library-lemma lib label theorem step nil))))

(defun t3-book-associations-associate-natural (lib goal given)
  (let ((label "T3-LOOKUP-NATURAL")
        (result (proof-ite *proof-result*
                           (list *t3-book-associations-natp* (list *library-car* *proof-result*))
                           *proof-true*)))
    (proof-with-checked-results
     ((lib (t3-book-associations-invariant
            lib label *t3-book-associations-by-cdr*
            (list *t3-book-associations-nat-table* *library-y*) result))
      (proof (library-library-proof lib))
      (parts (proof-proof-conjunct proof given))
      (found (car parts))
      (typed (cadr parts))
      (rule (library-library-cite lib label (cdr (proof-step-first found)) nil))
      (natural (proof-proof-prove-if proof rule typed))
      (natural (proof-proof-prove-if proof natural found))
      (selected (proof-proof-select proof goal natural))
      (step (proof-proof-transport proof natural selected)))
     (cons step lib))))

(defun t3-book-associations-associate-fixnat (lib given)
  (let* ((label "T3-LOOKUP-FIXNAT-BOUND")
         (limit (proof-quote 1152921504606846975))
         (first (list *library-car* *proof-result*))
         (result (proof-ite first (proof-neg (list *proof-less* limit first)) *proof-true*)))
    (proof-with-checked-results
     ((lib (t3-book-associations-invariant
            lib label *t3-book-associations-by-cdr*
            (list *t3-book-associations-fixnat-table* *library-y*) result))
      (proof (library-library-proof lib))
      (parts (proof-proof-conjunct proof given))
      (number (car parts))
      (typed (cadr parts))
      (lookup (proof-term-at (proof-step-first number) 1))
      (rule (library-library-cite lib label (cdr lookup) nil))
      (step (proof-proof-prove-if proof rule typed))
      (step (proof-proof-prove-if proof step number)))
     (cons step lib))))

(defun t3-book-associations-associate-symbol (lib goal given)
  (let* ((label "T3-LOOKUP-SYMBOL")
         (result (proof-ite *proof-result*
                            (list *t3-book-associations-symbolp* (list *library-cdr* *proof-result*))
                            *proof-true*)))
    (proof-with-checked-results
     ((lib (t3-book-associations-invariant
            lib label *t3-book-associations-assoc*
            (list *t3-book-associations-symbol-table* *library-y*) result))
      (proof (library-library-proof lib))
      (parts (proof-proof-conjunct proof given))
      (original (car parts))
      (other (proof-proof-conjunct proof (cadr parts)))
      (typed (cadr other))
      (term (proof-term-at goal 1))
      (opened (t3-book-spines-shallow lib term nil))
      (selected (caddr (proof-step-first opened)))
      (lookup (proof-term-at selected 1))
      (rule (library-library-cite lib label (cdr lookup) nil))
      (found (proof-proof-assume proof lookup t))
      (symbol (proof-proof-prove-if proof rule typed))
      (symbol (proof-proof-prove-if proof symbol found))
      (yes (proof-proof-if-true proof selected))
      (yes (library-library-transport-argument lib symbol yes 1))
      (no (proof-proof-if-false proof selected))
      (no (library-library-transport-argument lib original no 1))
      (step (proof-proof-cases proof lookup yes no))
      (step (library-library-transport-argument lib step opened 1)))
     (cons step lib))))

(defun t3-book-associations-associate-term (lib goal given)
  (let ((label "T3-LOOKUP-TERM")
        (result (list *t3-book-associations-termp* (list *library-cdr* *proof-result*))))
    (proof-with-checked-results
     ((lib (t3-book-associations-invariant
            lib label *t3-book-associations-assoc*
            (list *t3-book-associations-term-list*
                  (list *t3-book-associations-strip-cdrs* *library-y*)) result))
      (receiver (proof-term-at goal 1))
      (lookup (proof-term-at receiver 1))
      (rule (library-library-cite lib label (cdr lookup) nil))
      (step (proof-proof-prove-if (library-library-proof lib) rule given)))
     (cons step lib))))

(defun t3-book-associations-associate (lib name formula table)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((goal (proof-term-at formula 2))
      (guard (proof-term-at formula 1))
      (given (proof-proof-assume proof guard t))
      (result (cond
               ((equal table *t3-book-associations-nat-table*)
                (t3-book-associations-associate-natural lib goal given))
               ((equal table *t3-book-associations-fixnat-table*)
                (t3-book-associations-associate-fixnat lib given))
               ((equal table *t3-book-associations-symbol-table*)
                (t3-book-associations-associate-symbol lib goal given))
               (t (t3-book-associations-associate-term lib goal given))))
      (step (t3-book-lemmas-implication (cdr result) formula (car result)))
      (entry (proof-proof-entry "theorem" name (list name) (list step))))
     (cons entry (cdr result)))))
