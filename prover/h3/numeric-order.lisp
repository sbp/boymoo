(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-numeric-order-prefix* "H3-NUMERIC-")

(defund h3-numeric-order-numeric-evidence (proof step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (if (proof-is-call literal *library-rationalp*)
        (proof-with-checked-results
         ((term (proof-term-at literal 1))
          (conversion (proof-proof-fact
                       proof "rationalp-acl2-numberp" (list (list *library-x* term)))))
         (proof-proof-modus-ponens proof conversion step))
      step)))

(defun h3-numeric-order-cite-evidence (proof evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results
     ((numeric (h3-numeric-order-numeric-evidence proof (car evidence)))
      (rest (h3-numeric-order-cite-evidence proof (cdr evidence))))
     (cons numeric rest))))

(defun h3-numeric-order-cite (lib name values evidence)
  (proof-with-checked-results
   ((types (h3-numeric-order-cite-evidence (library-library-proof lib) evidence)))
    (library-library-cite lib (concatenate 'string *h3-numeric-order-prefix* name) values types)))

(defun h3-numeric-order-save-conditions (hypotheses)
  (if (endp hypotheses)
      nil
    (let ((term (car hypotheses)))
      (proof-with-checked-results
       ((condition (if (proof-is-call term *proof-not*) (proof-term-at term 1) (proof-neg term)))
        (rest (h3-numeric-order-save-conditions (cdr hypotheses))))
       (cons condition rest)))))

(defun h3-numeric-order-save (lib name step hypotheses)
  (proof-with-checked-results
   ((conditions (h3-numeric-order-save-conditions hypotheses))
    (literal (proof-step-first step)))
   (library-library-lemma lib (concatenate 'string *h3-numeric-order-prefix* name)
                          literal step conditions)))

(defun h3-numeric-order-numeric-sums-init (lib)
  (proof-with-checked-results
   ((rules (h3-rewrite-rules-init
            lib (list (proof-sym "SELF-SUM-NUMBER" "ACL2")
                      (proof-sym "SELF-NEGATION-NUMBER" "ACL2"))
            nil)))
   (list :numeric-sums lib (h3-rewrite-search-init lib nil nil rules 150 nil))))

(defun h3-numeric-order-numeric-sums-lib (sums)
  (cadr sums))

(defun h3-numeric-order-numeric-sums-types (sums)
  (caddr sums))

(defun h3-numeric-order-numeric-sums-with-lib (sums lib)
  (list :numeric-sums lib
        (h3-rewrite-search-with-lib (h3-numeric-order-numeric-sums-types sums) lib)))

(defun h3-numeric-order-numeric-sums-cite (sums name args evidence)
  (let ((lib (h3-numeric-order-numeric-sums-lib sums)))
    (if (member-equal name '("ADD-ZERO-LEFT" "ADD-ZERO-RIGHT"))
        (h3-numeric-order-cite lib name args evidence)
      (library-library-cite lib name args evidence))))

(defun h3-numeric-order-numeric-sums-type-of (sums term evidence)
  (let ((search (h3-numeric-order-numeric-sums-types sums)))
    (proof-with-checked-results ((context (h3-rewrite-search-context search evidence)))
      (car (h3-rewrite-search-derive search (list *library-numberp* term) context nil nil)))))

(defun h3-numeric-order-numeric-sums-push-minus (sums term evidence)
  (declare (ignore sums term evidence))
  nil)

(defun h3-numeric-order-linear-remove-zero (sums step name term place evidence)
  (proof-with-checked-results
   ((type-step (h3-numeric-order-numeric-sums-type-of sums term evidence))
    (zero-step (h3-numeric-order-numeric-sums-cite sums name (list term) (list type-step))))
   (proof-proof-rewrite
    (library-library-proof (h3-numeric-order-numeric-sums-lib sums)) step zero-step place)))

(defund h3-numeric-order-linear-combination (sums step place evidence)
  (let* ((lib (h3-numeric-order-numeric-sums-lib sums))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first step))
      (node (library-linear-form-get literal (cdr place))))
     (if (not (proof-is-call node *proof-plus*))
         (proof-with-checked-results ((step (proof-proof-tidy proof step)))
           (cons step nil))
       (proof-with-checked-results
        ((pair (proof-list-of-length (cdr node) 2))
         (a (car pair))
         (rest (cadr pair))
         (suffix (proof-is-call rest *proof-plus*))
         (b (if suffix (proof-term-at rest 1) rest)))
        (cond
         ((equal a *proof-zero*)
          (proof-with-checked-results
           ((step (h3-numeric-order-linear-remove-zero sums step "ADD-ZERO-LEFT"
                                                      rest place evidence)))
           (cons step place)))
         ((and (equal b *proof-zero*) (not suffix))
          (proof-with-checked-results
           ((step (h3-numeric-order-linear-remove-zero sums step "ADD-ZERO-RIGHT"
                                                      a place evidence)))
           (cons step place)))
         (t
          (proof-with-checked-results ((combine (library-linear-combine-pair lib a b)))
            (if (not combine)
                (cons step (append place '(2)))
              (proof-with-checked-results
               ((step (if suffix
                          (proof-with-checked-results
                           ((tail (proof-term-at rest 2))
                            (associate (library-library-axiom lib "ASSOCIATIVITY-OF-+"
                                                              (list a b tail)))
                            (symmetric (proof-proof-symmetric proof associate)))
                           (proof-proof-rewrite proof step symmetric place))
                        step))
                (step (proof-proof-rewrite proof step combine
                                           (if suffix (append place '(1)) place))))
               (cons step '(1 2))))))))))))

(defun h3-numeric-order-linear-combine (n sums step place evidence)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h3-numeric-order-linear-combine")
    (proof-with-checked-results ((result (h3-numeric-order-linear-combination sums step place evidence)))
      (if (cdr result)
          (h3-numeric-order-linear-combine (1- n) sums (car result) (cdr result) evidence)
        (car result)))))

(defun h3-numeric-order-numeric-sums-linear-form (sums term evidence)
  (let* ((lib (h3-numeric-order-numeric-sums-lib sums))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((step (h3-numeric-order-numeric-sums-push-minus sums term evidence))
      (step (or step (proof-proof-reflexive proof term)))
      (step (library-linear-reassociate 1000000 lib step '(1 2)))
      (step (library-linear-sort 1000000 lib step '(1 2) nil)))
     (h3-numeric-order-linear-combine 1000000 sums step '(1 2) evidence))))

(defun h3-numeric-order-numeric-sums-linear-equal (sums left right evidence)
  (let ((proof (library-library-proof (h3-numeric-order-numeric-sums-lib sums))))
    (proof-with-checked-results
     ((a (h3-numeric-order-numeric-sums-linear-form sums left evidence))
      (b (h3-numeric-order-numeric-sums-linear-form sums right evidence))
      (a-normal (proof-rewritten-term a))
      (b-normal (proof-rewritten-term b)))
     (if (equal a-normal b-normal)
         (proof-with-checked-results ((symmetric (proof-proof-symmetric proof b)))
           (proof-proof-chain proof a (list symmetric)))
       '(:failure "different-normal-forms" "")))))

(defun h3-numeric-order-add-zero (lib number)
  (let ((proof (library-library-proof lib)))
    (if (assoc-equal (proof-sym "SELF-H3-NUMERIC-ADD-ZERO-LEFT" "ACL2")
                     (proof-proof-facts proof))
        lib
      (proof-with-checked-results
       ((literal (proof-step-first number))
        (value (proof-term-at literal 1))
        (left (library-library-axiom lib "UNICITY-OF-0" (list value)))
        (fix-term (proof-rewritten-term left))
        (fix (proof-proof-unfold proof fix-term))
        (if-term (proof-rewritten-term fix))
        (selected (proof-proof-select proof if-term number))
        (left (proof-proof-chain proof left (list fix selected)))
        (lib (h3-numeric-order-save lib "ADD-ZERO-LEFT" left (list literal)))
        (proof (library-library-proof lib))
        (commute (library-library-axiom lib "COMMUTATIVITY-OF-+" (list value *proof-zero*)))
        (right (proof-proof-chain proof commute (list left))))
       (h3-numeric-order-save lib "ADD-ZERO-RIGHT" right (list literal))))))

(defun h3-numeric-order-additive-inverse (lib sums a b numbers)
  (let* ((proof (library-library-proof lib))
         (opposite-a (library-minus a)))
    (proof-with-checked-results
     ((sum-zero (h3-numeric-order-numeric-sums-linear-equal
                 sums (library-plus a b) *proof-zero* numbers))
      (commute (library-library-axiom lib "COMMUTATIVITY-OF-+" (list opposite-a a)))
      (inverse (library-library-axiom lib "INVERSE-OF-+" (list a)))
      (cancel (proof-proof-chain proof commute (list inverse)))
      (associate (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list opposite-a a b)))
      (equation (proof-proof-symmetric proof associate))
      (equation (proof-proof-rewrite proof equation sum-zero '(1 1 2)))
      (equation (proof-proof-rewrite proof equation cancel '(1 2 1)))
      (opposite-type (h3-numeric-order-numeric-sums-type-of sums opposite-a numbers))
      (zero-right (h3-numeric-order-cite lib "ADD-ZERO-RIGHT" (list opposite-a)
                                        (list opposite-type)))
      (equation (proof-proof-rewrite proof equation zero-right '(1 1)))
      (b-type (h3-numeric-order-numeric-sums-type-of sums b numbers))
      (zero-left (h3-numeric-order-cite lib "ADD-ZERO-LEFT" (list b) (list b-type))))
     (proof-proof-chain proof equation (list zero-left)))))

(defun h3-numeric-order-positive-difference (lib sums numbers opposite)
  (let* ((proof (library-library-proof lib))
         (delta (library-diff *library-y* *library-x*))
         (minus-delta (library-minus delta)))
    (proof-with-checked-results
     ((positive-delta (library-library-axiom lib "<-ON-OTHERS" (list *proof-zero* delta)))
      (number (h3-numeric-order-numeric-sums-type-of sums minus-delta numbers))
      (zero (h3-numeric-order-cite lib "ADD-ZERO-LEFT" (list minus-delta) (list number)))
      (positive-delta (proof-proof-rewrite proof positive-delta zero '(1 2 1)))
      (positive-delta (proof-proof-rewrite proof positive-delta opposite '(1 2 1)))
      (comparison (library-library-axiom lib "<-ON-OTHERS" (list *library-x* *library-y*)))
      (symmetric (proof-proof-symmetric proof positive-delta)))
     (proof-proof-chain proof comparison (list symmetric)))))

(defun h3-numeric-order-asymmetric (lib numbers comparison opposite)
  (let ((proof (library-library-proof lib))
        (delta (library-diff *library-y* *library-x*)))
    (proof-with-checked-results
     ((xy (proof-proof-assume proof (library-lt *library-x* *library-y*) t))
      (pos-delta (proof-proof-rewrite proof xy comparison '(1)))
      (trichotomy (library-library-axiom lib "TRICHOTOMY" (list delta)))
      (parts (proof-proof-conjunct proof trichotomy))
      (positive (h3-rewrite-introduce-double-negation lib pos-delta))
      (other-sign (proof-proof-prove-if proof (cadr parts) positive))
      (other-sign (proof-proof-rewrite proof other-sign opposite '(1 1 2)))
      (reverse (h3-numeric-order-cite lib "LESS-DIFFERENCE" (list *library-y* *library-x*)
                                     (reverse numbers))))
     (library-library-transport-argument lib other-sign reverse 1))))

(defun h3-numeric-order-antisymmetric (lib sums numbers comparison opposite)
  (let* ((proof (library-library-proof lib))
         (delta (library-diff *library-y* *library-x*))
         (zero (proof-eq delta *proof-zero*)))
    (proof-with-checked-results
     ((numbers (proof-list-of-length numbers 2))
      (rx (car numbers))
      (ry (cadr numbers))
      (xy (proof-proof-assume proof (library-lt *library-x* *library-y*) nil))
      (yx (proof-proof-assume proof (library-lt *library-y* *library-x*) nil))
      (not-positive (proof-proof-rewrite proof xy comparison '(1 1)))
      (reverse (h3-numeric-order-cite lib "LESS-DIFFERENCE" (list *library-y* *library-x*)
                                     (list ry rx)))
      (other (proof-proof-rewrite proof yx reverse '(1 1)))
      (inverse (proof-proof-symmetric proof opposite))
      (other (proof-proof-rewrite proof other inverse '(1 1 2)))
      (numeric (h3-numeric-order-numeric-sums-type-of sums delta numbers))
      (tri (library-library-axiom lib "TRICHOTOMY" (list delta)))
      (parts (proof-proof-conjunct proof tri))
      (tri (proof-proof-modus-ponens proof (car parts) numeric))
      (tri (proof-proof-prove-if proof tri not-positive))
      (not-zero (proof-proof-assume proof zero nil))
      (sign (proof-proof-prove-if proof tri not-zero))
      (cut (proof-proof-cut proof sign other))
      (zero-proof (proof-proof-front proof cut zero))
      (equation (h3-numeric-order-numeric-sums-linear-equal
                 sums (library-plus *library-x* delta) *library-y* numbers))
      (equation (proof-proof-rewrite proof equation zero-proof '(1 1 2)))
      (zero-right (h3-numeric-order-cite lib "ADD-ZERO-RIGHT" (list *library-x*) (list rx)))
      (equation (proof-proof-rewrite proof equation zero-right '(1 1))))
     (proof-proof-tidy proof equation))))

(defun h3-numeric-order-strict-transitive (lib sums numbers)
  (let* ((proof (library-library-proof lib))
         (a (library-diff *library-y* *library-x*))
         (b (library-diff *library-z* *library-y*)))
    (proof-with-checked-results
     ((numbers (proof-list-of-length numbers 3))
      (rx (car numbers))
      (ry (cadr numbers))
      (rz (caddr numbers))
      (xy (proof-proof-assume proof (library-lt *library-x* *library-y*) t))
      (difference (h3-numeric-order-cite lib "LESS-DIFFERENCE" (list *library-x* *library-y*)
                                         (list rx ry)))
      (first (proof-proof-rewrite proof xy difference '(1)))
      (yz (proof-proof-assume proof (library-lt *library-y* *library-z*) t))
      (difference (h3-numeric-order-cite lib "LESS-DIFFERENCE" (list *library-y* *library-z*)
                                         (list ry rz)))
      (second (proof-proof-rewrite proof yz difference '(1)))
      (total (library-library-cite lib "POSITIVE-SUM" (list a b) (list first second)))
      (sum (h3-numeric-order-numeric-sums-linear-equal
            sums (library-plus a b) (library-diff *library-z* *library-x*) numbers))
      (total (proof-proof-rewrite proof total sum '(1 2)))
      (target (h3-numeric-order-cite lib "LESS-DIFFERENCE" (list *library-x* *library-z*)
                                     (list rx rz))))
     (proof-proof-transport proof total target))))

(defun h3-numeric-order-ordered-composition-finish
    (left lib rx ry rz first-strict second-strict first second q)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((right (if second-strict second (proof-proof-assume proof q t)))
      (strict (h3-numeric-order-cite
               lib "LESS-TRANSITIVE" (list *library-x* *library-y* *library-z*)
               (list rx ry rz left right)))
      (joined (if (or first-strict second-strict)
                  strict
                (h3-numeric-order-cite lib "LESS-ASYMMETRIC" (list *library-x* *library-z*)
                                       (list rx rz strict)))))
     (if second-strict
         joined
       (proof-with-checked-results
        ((not-q (proof-proof-assume proof q nil))
         (same (h3-numeric-order-cite lib "WEAK-ANTISYMMETRIC" (list *library-y* *library-z*)
                                     (list ry rz second not-q)))
         (no (proof-proof-rewrite-first proof first same)))
        (proof-proof-cases proof q joined no))))))

(defun h3-numeric-order-ordered-composition (lib numbers first-strict second-strict)
  (let* ((proof (library-library-proof lib))
         (p (library-lt *library-x* *library-y*))
         (q (library-lt *library-y* *library-z*)))
    (proof-with-checked-results
     ((numbers (proof-list-of-length numbers 3))
      (first (proof-proof-assume proof
                                 (if first-strict p (library-lt *library-y* *library-x*))
                                 first-strict))
      (second (proof-proof-assume proof
                                  (if second-strict q (library-lt *library-z* *library-y*))
                                  second-strict)))
     (if first-strict
         (h3-numeric-order-ordered-composition-finish
          first lib (car numbers) (cadr numbers) (caddr numbers)
          first-strict second-strict first second q)
       (proof-with-checked-results
        ((not-p (proof-proof-assume proof p nil))
         (same (h3-numeric-order-cite lib "WEAK-ANTISYMMETRIC" (list *library-x* *library-y*)
                                     (list (car numbers) (cadr numbers) first not-p)))
         (symmetric (proof-proof-symmetric proof same))
         (no (proof-proof-rewrite-first proof second symmetric))
         (yes (proof-proof-assume proof p t))
         (yes (h3-numeric-order-ordered-composition-finish
               yes lib (car numbers) (cadr numbers) (caddr numbers)
               first-strict second-strict first second q)))
        (proof-proof-cases proof p yes no))))))

(defun h3-numeric-order-register-shift (lib sums predicates rx ry rz)
  (let* ((proof (library-library-proof lib))
         (left (library-plus *library-z* *library-x*))
         (right (library-plus *library-z* *library-y*))
         (test (library-lt *library-x* *library-y*))
         (numbers (list rx ry rz)))
    (proof-with-checked-results
     ((less (proof-proof-assume proof test t))
      (difference (h3-numeric-order-cite lib "LESS-DIFFERENCE" (list *library-x* *library-y*)
                                         (list rx ry)))
      (source (proof-proof-rewrite proof less difference '(1)))
      (inverse-left (h3-numeric-order-additive-inverse
                     lib sums left (library-plus (library-minus *library-z*)
                                                 (library-minus *library-x*))
                     (list rx rz)))
      (shifted (proof-proof-reflexive proof (library-diff right left)))
      (shifted (proof-proof-rewrite proof shifted inverse-left '(1 2 2)))
      (value (proof-rewritten-term shifted))
      (sum (h3-numeric-order-numeric-sums-linear-equal
            sums value (library-diff *library-y* *library-x*) numbers))
      (shifted (proof-proof-chain proof shifted (list sum)))
      (left-type (h3-numeric-order-numeric-sums-type-of sums left numbers))
      (right-type (h3-numeric-order-numeric-sums-type-of sums right numbers))
      (target (h3-numeric-order-cite lib "LESS-DIFFERENCE" (list left right) (list left-type right-type)))
      (target (proof-proof-rewrite proof target shifted '(1 2 2)))
      (step (proof-proof-transport proof source target)))
     (h3-numeric-order-save lib "LESS-SHIFT-LEFT" step (append predicates (list test))))))

(defund h3-numeric-order-register-composition (lib numbers predicates recipe)
  (let ((first (cadr recipe))
        (second (caddr recipe)))
    (proof-with-checked-results
     ((step (h3-numeric-order-ordered-composition lib numbers first second))
      (left (if first (library-lt *library-x* *library-y*) (library-le *library-x* *library-y*)))
      (right (if second (library-lt *library-y* *library-z*) (library-le *library-y* *library-z*))))
     (h3-numeric-order-save lib (car recipe) step (append predicates (list left right))))))

(defun h3-numeric-order-register-compositions (lib numbers predicates recipes)
  (declare (xargs :measure (acl2-count recipes)))
  (if (endp recipes)
      lib
    (proof-with-checked-results
     ((lib (h3-numeric-order-register-composition lib numbers predicates (car recipes))))
     (h3-numeric-order-register-compositions lib numbers predicates (cdr recipes)))))

(defun h3-numeric-order-numeric-order (lib)
  (if (assoc-equal (proof-sym "SELF-H3-NUMERIC-WEAK-THEN-LESS" "ACL2")
                   (proof-proof-facts (library-library-proof lib)))
      lib
    (proof-with-checked-results
     ((lib (h3-merges-arithmetic lib))
      (sums (h3-numeric-order-numeric-sums-init lib))
      (proof (library-library-proof lib))
      (nx (list *library-numberp* *library-x*))
      (ny (list *library-numberp* *library-y*))
      (nz (list *library-numberp* *library-z*))
      (rx (proof-proof-assume proof nx t))
      (ry (proof-proof-assume proof ny t))
      (rz (proof-proof-assume proof nz t))
      (predicates (list nx ny nz))
      (pair (list nx ny))
      (lib (h3-numeric-order-add-zero lib rx))
      (sums (h3-numeric-order-numeric-sums-with-lib sums lib))
      (opposite (h3-numeric-order-additive-inverse
                 lib sums (library-diff *library-y* *library-x*)
                 (library-diff *library-x* *library-y*) (list rx ry)))
      (lib (h3-numeric-order-save lib "OPPOSITE-DIFFERENCES" opposite pair))
      (sums (h3-numeric-order-numeric-sums-with-lib sums lib))
      (comparison (h3-numeric-order-positive-difference lib sums (list rx ry) opposite))
      (lib (h3-numeric-order-save lib "LESS-DIFFERENCE" comparison pair))
      (xy (library-lt *library-x* *library-y*))
      (yz (library-lt *library-y* *library-z*))
      (step (h3-numeric-order-asymmetric lib (list rx ry) comparison opposite))
      (lib (h3-numeric-order-save lib "LESS-ASYMMETRIC" step (append pair (list xy))))
      (sums (h3-numeric-order-numeric-sums-with-lib sums lib))
      (step (h3-numeric-order-antisymmetric lib sums (list rx ry) comparison opposite))
      (lib (h3-numeric-order-save lib "WEAK-ANTISYMMETRIC" step
                                 (append pair (list (library-le *library-x* *library-y*)
                                                    (library-le *library-y* *library-x*)))))
      (sums (h3-numeric-order-numeric-sums-with-lib sums lib))
      (numbers (list rx ry rz))
      (step (h3-numeric-order-strict-transitive lib sums numbers))
      (lib (h3-numeric-order-save lib "LESS-TRANSITIVE" step (append predicates (list xy yz))))
      (sums (h3-numeric-order-numeric-sums-with-lib sums lib))
      (lib (h3-numeric-order-register-shift lib sums predicates rx ry rz)))
     (h3-numeric-order-register-compositions
      lib numbers predicates '(("WEAK-THEN-LESS" nil t)
                                ("LESS-THEN-WEAK" t nil)
                                ("WEAK-TRANSITIVE" nil nil))))))
