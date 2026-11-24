(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *lemmas-reflexive* (proof-sym "SELF-EQUALITY-REFLEXIVE" "ACL2"))
(defconst *lemmas-len-number* (proof-sym "SELF-LEN-NUMBER" "ACL2"))
(defconst *lemmas-number-if* (proof-sym "SELF-NUMBER-IF" "ACL2"))
(defconst *lemmas-length* (proof-cl "LENGTH"))
(defconst *lemmas-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *lemmas-min* (proof-cl "MIN"))
(defconst *lemmas-characterp* (proof-cl "CHARACTERP"))
(defconst *lemmas-symbolp* (proof-cl "SYMBOLP"))

(defun lemmas-slice-library-init (proof)
  (library-library-init (proof-proof-with-kind proof :slice)))

(defun lemmas-slice-proof (lib)
  (let ((proof (library-library-proof lib)))
    (if (eq (proof-proof-kind proof) :book)
        proof
      (proof-proof-with-kind proof :slice))))

(defun lemmas-has-fact (lib name)
  (if (assoc-equal name (proof-proof-facts (library-library-proof lib))) t nil))

(defun lemmas-has-definition (lib name)
  (if (assoc-equal name (proof-proof-definitions (library-library-proof lib))) t nil))

(defun lemmas-self-name (name)
  (proof-sym (concatenate 'string "SELF-" name) "ACL2"))

(defun lemmas-slice-library-reflexive (lib term)
  (proof-proof-reflexive (lemmas-slice-proof lib) term))

(defun lemmas-slice-library-constant (lib term)
  (proof-proof-constant (proof-proof-with-kind (library-library-proof lib) :slice) term))

(defun lemmas-nfix-equation (lib value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((lib (if (lemmas-has-fact lib (lemmas-self-name "LIBRARY-NFIX"))
               lib
             (proof-with-checked-results
              ((library (proof-proof-unfold proof (list *lemmas-nfix* *library-x*)))
               (helper (proof-proof-simplify proof (list *library-nfix* *library-x*)
                                            nil (list *library-nfix* *library-natp*)))
               (reverse-helper (proof-proof-symmetric proof helper))
               (identity (proof-proof-chain proof library (list reverse-helper)))
               (claim (proof-step-first identity)))
              (library-library-lemma lib "LIBRARY-NFIX" claim identity nil))))
      (step (library-library-cite lib "LIBRARY-NFIX" (list value) nil)))
     (cons step lib))))

(defun lemmas-slice-library-by-value (lib value template leaf tests)
  (proof-proof-by-value (lemmas-slice-proof lib) value template leaf tests))

(defun lemmas-type-evidence (literal evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results ((first (proof-step-first (car evidence))))
     (if (equal first literal)
         (car evidence)
       (lemmas-type-evidence literal (cdr evidence))))))

(defun lemmas-minimum-leaves (requests bounds)
  (if (endp requests)
      nil
    (let* ((request (car requests))
           (match (assoc-equal (car request) bounds))
           (result (if match (cdr match) '(:failure "failure" ""))))
      (cons (cons request result) (lemmas-minimum-leaves (cdr requests) bounds)))))

(defun lemmas-minimum-natural-lemma (lib)
  (let* ((proof (library-library-proof lib))
         (template (list *library-natp* *proof-result*))
         (nx (list *library-natp* *library-x*))
         (ny (list *library-natp* *library-y*)))
    (proof-with-checked-results
     ((equation (proof-proof-unfold proof (list *lemmas-min* *library-x* *library-y*)))
      (x-bound (proof-proof-assume proof nx t))
      (y-bound (proof-proof-assume proof ny t))
      (first (proof-step-first equation))
      (value (caddr first))
      (requests (proof-proof-by-value-leaves proof value nil))
      (leaf (lemmas-minimum-leaves requests
                                  (list (cons *library-x* x-bound) (cons *library-y* y-bound))))
      (step (lemmas-slice-library-by-value lib value template leaf nil))
      (step (library-library-transport-argument lib step equation 1))
      (claim (proof-step-first step)))
     (library-library-lemma lib "MINIMUM-NATURAL" claim step
                            (list (proof-neg nx) (proof-neg ny))))))

(defun lemmas-natural-nfix (lib term)
  (proof-with-checked-results
   ((natural (library-library-cite lib "NFIX-NATURAL" (cdr term) nil))
    (argument (proof-term-at term 1))
    (equation (lemmas-nfix-equation lib argument))
    (step (library-library-transport-argument (cdr equation) natural (car equation) 1)))
   (cons step (cdr equation))))

(defun lemmas-natural-length-task (lib term)
  (let ((length-term (list *lemmas-length* *library-x*))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof length-term))
      (first (proof-step-first opened))
      (value (proof-term-at first 2))
      (requests (proof-proof-by-value-leaves proof value nil)))
     (list :length lib (cdr term) length-term opened value requests))))

(defun lemmas-natural-prepare (lib term)
  (cond
   ((and (proof-is-call term *lemmas-nfix*) (lemmas-has-definition lib *lemmas-nfix*))
    (proof-with-checked-results ((value (lemmas-natural-nfix lib term)))
     (list :return value)))
   ((and (proof-is-call term *lemmas-min*) (lemmas-has-definition lib *lemmas-min*))
    (let ((name "MINIMUM-NATURAL"))
      (proof-with-checked-results
       ((lib (if (lemmas-has-fact lib (lemmas-self-name name))
                 lib
               (lemmas-minimum-natural-lemma lib))))
       (list :arguments lib name (cdr term)))))
   ((proof-is-call term *lemmas-length*)
    (if (lemmas-has-fact lib (lemmas-self-name "LENGTH-NATURAL"))
        (proof-with-checked-results
         ((step (library-library-cite lib "LENGTH-NATURAL" (cdr term) nil)))
         (list :return (cons step lib)))
      (lemmas-natural-length-task lib term)))
   ((proof-is-call term *proof-plus*)
    (list :arguments lib "NATURAL-SUM" (cdr term)))
   (t
    (proof-with-checked-results ((step (library-library-natural lib term)))
     (list :return (cons step lib))))))

(defun lemmas-natural-finish-length (task leaves)
  (let* ((lib (cdr leaves))
         (proof (library-library-proof lib))
         (args (caddr task))
         (length-term (cadddr task))
         (opened (car (cddddr task)))
         (value (cadr (cddddr task)))
         (template (list *library-natp* *proof-result*)))
    (proof-with-checked-results
     ((step (lemmas-slice-library-by-value lib value template (car leaves) nil))
      (symmetric (proof-proof-symmetric proof opened))
      (step (proof-proof-rewrite-result proof step symmetric template *proof-result*))
      (lib (library-library-lemma lib "LENGTH-NATURAL" (list *library-natp* length-term) step nil))
      (step (library-library-cite lib "LENGTH-NATURAL" args nil)))
     (cons step lib))))

; A natural-number proof can require proofs for arguments or for result branches.
(mutual-recursion
 (defun lemmas-slice-library-natural-loop (n lib term)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "lemmas-slice-library-natural-loop")
     (lemmas-natural-run (1- n) (lemmas-natural-prepare lib term))))

 (defun lemmas-natural-run (n task)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "lemmas-natural-run"))
    ((failure-p task) task)
    ((eq (car task) :return) (cadr task))
    ((eq (car task) :length)
     (proof-with-checked-results
      ((leaves (lemmas-length-natural-leaves (1- n) (cadr task) (caddr (cddddr task)))))
      (lemmas-natural-finish-length task leaves)))
    (t
     (let ((lib (cadr task))
           (name (caddr task))
           (arguments (cadddr task)))
       (proof-with-checked-results
        ((naturals (lemmas-slice-library-naturals (1- n) lib arguments))
         (step (library-library-cite (cdr naturals) name arguments (car naturals))))
        (cons step (cdr naturals)))))))

 (defun lemmas-slice-library-naturals (n lib terms)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "lemmas-slice-library-naturals"))
         ((endp terms) (cons nil lib))
         (t
          (proof-with-checked-results
           ((first (lemmas-slice-library-natural-loop (1- n) lib (car terms)))
            (rest (lemmas-slice-library-naturals (1- n) (cdr first) (cdr terms))))
           (cons (cons (car first) (car rest)) (cdr rest))))))

 (defun lemmas-length-natural-leaves (n lib requests)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "lemmas-length-natural-leaves"))
         ((endp requests) (cons nil lib))
         (t
          (proof-with-checked-results
           ((value (lemmas-slice-library-natural-loop (1- n) lib (caar requests)))
            (rest (lemmas-length-natural-leaves (1- n) (cdr value) (cdr requests))))
           (cons (cons (cons (car requests) (car value)) (car rest)) (cdr rest)))))))

(defun lemmas-slice-library-natural (lib term)
  (lemmas-slice-library-natural-loop 1000000 lib term))

(mutual-recursion
 (defun lemmas-slice-library-type-of-loop (n lib term evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "lemmas-slice-library-type-of-loop")
     (cond
      ((or (proof-is-call term *lemmas-length*)
           (and (member-equal (car term) (list *lemmas-nfix* *lemmas-min*))
                (proof-compound term)
                (lemmas-has-definition lib (car term))))
       (proof-with-checked-results ((existing (lemmas-type-evidence (library-integer term) evidence)))
        (if existing
            (cons existing lib)
          (proof-with-checked-results
           ((natural (lemmas-slice-library-natural lib term))
            (step (library-library-cite (cdr natural) "NATURAL-INTEGER" (list term) (list (car natural)))))
           (cons step (cdr natural))))))
      ((and (proof-compound term) (member-equal (car term) (list *proof-plus* *proof-times* *proof-minus*)))
       (proof-with-checked-results ((existing (lemmas-type-evidence (library-integer term) evidence)))
        (cond
         (existing (cons existing lib))
         ((and (equal (car term) *proof-minus*) (endp (cdr term)))
          '(:failure "failure" ""))
         (t
          (let ((name (cond ((equal (car term) *proof-plus*) "INTEGER-SUM")
                            ((equal (car term) *proof-times*) "INTEGER-PRODUCT")
                            (t "INTEGER-NEGATION")))
                (arguments (if (equal (car term) *proof-minus*) (list (cadr term)) (cdr term))))
            (proof-with-checked-results
             ((types (lemmas-slice-library-types-loop (1- n) lib arguments evidence))
              (step (library-library-cite (cdr types) name (cdr term) (car types))))
             (cons step (cdr types))))))))
      (t
       (proof-with-checked-results ((step (library-library-type-of lib term evidence)))
        (cons step lib))))))

 (defun lemmas-slice-library-types-loop (n lib terms evidence)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "lemmas-slice-library-types-loop"))
         ((endp terms) (cons nil lib))
         (t
          (proof-with-checked-results
           ((first (lemmas-slice-library-type-of-loop (1- n) lib (car terms) evidence))
            (rest (lemmas-slice-library-types-loop (1- n) (cdr first) (cdr terms) evidence)))
           (cons (cons (car first) (car rest)) (cdr rest)))))))

(defun lemmas-slice-library-type-of (lib term evidence)
  (lemmas-slice-library-type-of-loop 1000000 lib term evidence))

(defun lemmas-slice-library-types (lib terms evidence)
  (lemmas-slice-library-types-loop 1000000 lib terms evidence))

(defun lemmas-slice-library-rational (lib term evidence)
  (proof-with-checked-results
   ((axiom (library-library-axiom lib "INTEGER-IMPLIES-RATIONAL" (list term)))
    (integer (lemmas-slice-library-type-of lib term evidence))
    (step (proof-proof-modus-ponens (library-library-proof (cdr integer)) axiom (car integer))))
   (cons step (cdr integer))))

(defun lemmas-slice-library-number (lib term evidence)
  (let ((proof (library-library-proof lib)))
    (cond
     ((and (proof-is-call term *library-len*) (lemmas-has-fact lib *lemmas-len-number*))
      (if (endp (cdr term))
          '(:failure "failure" "")
        (proof-with-checked-results
         ((step (proof-proof-fact proof *lemmas-len-number* (list (list *library-x* (cadr term))))))
         (cons step lib))))
     ((proof-is-call term *proof-quote*)
      (proof-with-checked-results ((step (proof-proof-prove proof (list *library-numberp* term) nil nil)))
       (cons step lib)))
     (t
      (proof-with-checked-results
       ((fact (proof-proof-fact proof "rationalp-acl2-numberp" (list (list *library-x* term))))
        (rational (lemmas-slice-library-rational lib term evidence))
        (step (proof-proof-modus-ponens (library-library-proof (cdr rational)) fact (car rational))))
       (cons step (cdr rational)))))))

(defun lemmas-positive-nonzero-atom (lib value integrality nonzero bound)
  (let* ((proof (library-library-proof lib))
         (goal (library-positive value)))
    (proof-with-checked-results
     ((axiom (library-library-axiom lib "TRICHOTOMY" (list value)))
      (trichotomy (proof-proof-conjunct proof axiom))
      (numeric (lemmas-slice-library-number lib value (list integrality)))
      (lib (cdr numeric))
      (proof (library-library-proof lib))
      (signs (proof-proof-modus-ponens proof (car trichotomy) (car numeric)))
      (not-positive (proof-proof-assume proof goal nil))
      (negative (proof-proof-simplify-first proof signs (list not-positive nonzero) nil))
      (shift (library-library-axiom lib "<-ON-OTHERS" (list *proof-zero* (library-minus value))))
      (shifted (proof-proof-rewrite proof negative shift '(1)))
      (difference (library-library-linear-equal lib (library-diff *proof-zero* (library-minus value))
                                                value (list integrality)))
      (negative (proof-proof-rewrite proof shifted difference '(1 1)))
      (negative (proof-proof-tidy proof negative))
      (first (proof-step-first negative)))
     (if (equal first (library-lt value *proof-zero*))
         (proof-with-checked-results ((cut (proof-proof-cut proof negative bound))
                       (step (proof-proof-front proof cut goal)))
          (cons step lib))
       '(:failure "failure" "")))))

(defun lemmas-positive-nonzero-integer (lib value integrality nonzero bound)
  (if (not (proof-compound value))
      (lemmas-positive-nonzero-atom lib value integrality nonzero bound)
    (let* ((name "POSITIVE-NONZERO-INTEGER")
           (proof (library-library-proof lib))
           (integer (library-integer *library-x*))
           (zero (proof-eq *library-x* *proof-zero*))
           (below (library-lt *library-x* *proof-zero*)))
      (proof-with-checked-results
       ((lib (if (lemmas-has-fact lib (lemmas-self-name name))
                 lib
               (proof-with-checked-results
                ((typed (proof-proof-assume proof integer t))
                 (nz (proof-proof-assume proof zero nil))
                 (lower (proof-proof-assume proof below nil))
                 (positive (lemmas-positive-nonzero-atom lib *library-x* typed nz lower))
                 (claim (proof-step-first (car positive))))
                (library-library-lemma (cdr positive) name claim (car positive)
                                       (list (proof-neg integer) zero below)))))
        (step (library-library-cite lib name (list value) (list integrality nonzero bound))))
       (cons step lib)))))

(defun lemmas-written-terms (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results ((first (proof-write (car terms)))
                  (rest (lemmas-written-terms (cdr terms))))
     (cons first rest))))

(defun lemmas-obligation-counts (obligations counts)
  (if (endp obligations)
      counts
    (proof-with-checked-results ((obligation (proof-list-of-length (car obligations) 2)))
     (let* ((step (cadr obligation))
            (copies (table-get counts step 0)))
       (lemmas-obligation-counts (cdr obligations) (table-put counts step (1+ copies)))))))

(defun lemmas-blocked-proof-p (blocked header source)
  (and (consp blocked)
       (or (<= 0 (text-find header (car blocked)))
           (<= 0 (text-find source (car blocked)))
           (lemmas-blocked-proof-p (cdr blocked) header source))))

(defun lemmas-propose-shared (lib step copies blocked)
  (let ((clause (proof-step-clause step)))
    (proof-with-checked-results
     ((lines (proof-serialize step))
      (source (text-join "" lines))
      (prefix (proof-line "lemma" clause))
      (digest (siphash-hexdigest (concatenate 'string prefix source)))
      (label (concatenate 'string "SHARED-PROOF-" (text-upper (seq-slice digest 0 20))))
      (name (lemmas-self-name label))
      (header (proof-line "lemma" (cons name clause))))
     (if (lemmas-blocked-proof-p blocked header source)
         (cons nil lib)
       (proof-with-checked-results
        ((qed (proof-line "qed" nil))
         (fact (proof-line "fact" (list name))))
        (if (<= (* (1- copies) (length source))
                (+ (length header) (length qed) (* copies (length fact))))
            (cons nil lib)
          (proof-with-checked-results
           ((lib (if (lemmas-has-fact lib name)
                     lib
                   (proof-with-checked-results ((claim (proof-step-first step)))
                    (library-library-lemma lib label claim step (cdr clause)))))
            (shared (proof-proof-fact (library-library-proof lib) name nil)))
           (cons shared lib))))))))

(defun lemmas-share-repeated (lib counts blocked shared)
  (if (endp counts)
      (cons shared lib)
    (let ((step (caar counts))
          (copies (cdar counts)))
      (if (< copies 2)
          (lemmas-share-repeated lib (cdr counts) blocked shared)
        (proof-with-checked-results ((result (lemmas-propose-shared lib step copies blocked)))
         (lemmas-share-repeated (cdr result) (cdr counts) blocked
                               (if (car result) (table-put shared step (car result)) shared)))))))

(defun lemmas-subsume-obligations (proof obligations shared)
  (if (endp obligations)
      nil
    (let* ((clause (caar obligations))
           (step (cadar obligations))
           (source (table-get shared step step)))
      (proof-with-checked-results ((first (proof-proof-subsume proof source clause))
                    (rest (lemmas-subsume-obligations proof (cdr obligations) shared)))
       (cons first rest)))))

(defun lemmas-slice-library-share-proofs (lib obligations forbidden)
  (proof-with-checked-results
   ((blocked (lemmas-written-terms forbidden))
    (counts (lemmas-obligation-counts obligations nil))
    (shared (lemmas-share-repeated lib counts blocked nil))
    (steps (lemmas-subsume-obligations (library-library-proof (cdr shared)) obligations (car shared))))
   (cons steps (cdr shared))))

(defun lemmas-slice-library-count-lemmas-numeric-branch (value tests lib summation)
  (declare (ignore tests))
  (if (proof-is-call value *proof-plus*)
      summation
    (proof-proof-prove (library-library-proof lib) (list *library-numberp* value) nil nil)))

(defun lemmas-count-number-leaves (requests lib summation)
  (if (endp requests)
      nil
    (cons (cons (car requests)
                (lemmas-slice-library-count-lemmas-numeric-branch
                 (caar requests) (cadar requests) lib summation))
          (lemmas-count-number-leaves (cdr requests) lib summation))))

(defun lemmas-count-number-if (lib)
  (let* ((proof (library-library-proof lib))
         (conditional (proof-ite *library-x* *library-y* *library-z*))
         (y-number (list *library-numberp* *library-y*))
         (z-number (list *library-numberp* *library-z*)))
    (proof-with-checked-results
     ((yes (proof-proof-assume proof y-number t))
      (no (proof-proof-assume proof z-number t))
      (true (proof-proof-if-true proof conditional))
      (yes-proof (library-library-transport-argument lib yes true 1))
      (false (proof-proof-if-false proof conditional))
      (no-proof (library-library-transport-argument lib no false 1))
      (cases (proof-proof-cases proof *library-x* yes-proof no-proof)))
     (library-library-lemma lib "NUMBER-IF" (list *library-numberp* conditional)
                            cases (list (proof-neg y-number) (proof-neg z-number))))))

(defun lemmas-slice-library-count-lemmas (lib)
  (let* ((length-term (list *library-len* *library-x*))
         (template (list *library-numberp* *proof-result*))
         (tail (list *library-len* (list *library-cdr* *library-x*))))
    (proof-with-checked-results
     ((lib (lemmas-count-number-if lib))
      (proof (library-library-proof lib))
      (opened (proof-proof-unfold proof length-term))
      (closure (library-library-axiom lib "CLOSURE" (list *proof-one* tail)))
      (conjuncts (proof-proof-conjunct proof closure))
      (first (proof-step-first opened))
      (value (caddr first))
      (requests (proof-proof-by-value-leaves proof value nil))
      (leaf (lemmas-count-number-leaves requests lib (car conjuncts)))
      (step (lemmas-slice-library-by-value lib value template leaf nil))
      (symmetric (proof-proof-symmetric proof opened))
      (step (proof-proof-rewrite-result proof step symmetric template *proof-result*))
      (lib (library-library-lemma lib "LEN-NUMBER" (list *library-numberp* length-term) step nil)))
     (library-library-count-lemmas-for-slice lib))))

(defun lemmas-slice-library-build (lib)
  (let ((x *library-x*)
        (term (proof-ite *library-x* *library-x* *library-y*)))
    (proof-with-checked-results
     ((lib (library-library-with-proof lib (lemmas-slice-proof lib)))
      (reflexive (proof-proof-reflexive-base (library-library-proof lib) x))
      (lib (library-library-lemma lib "EQUALITY-REFLEXIVE" (proof-eq x x) reflexive nil))
      (lib (library-library-build-before-count lib))
      (lib (lemmas-slice-library-count-lemmas lib))
      (lib (library-library-build-after-count lib))
      (proof (library-library-proof lib))
      (assumed (proof-proof-assume proof x t))
      (true (proof-proof-if-true proof term))
      (selected (proof-proof-transport proof assumed true))
      (negative (proof-neg x))
      (step (proof-proof-front proof selected negative)))
     (library-library-lemma lib "IF-RETURNS-TRUE-TEST" negative step (list term)))))
