(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defun t4-field-side (step index)
  (if (null step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun t4-field-inverse-from-product-typed
    (obj index lib product factor candidate replies)
  (let ((typed (list *library-numberp* obj))
        (other (if (equal index 1) candidate factor)))
    (t4-algebra-with-library lib
        ((notnum (proof-proof-assume (library-library-proof lib) typed nil))
         (completion (library-library-axiom lib "COMPLETION-OF-*" (list obj other)))
         (zero (t4-algebra-choose lib completion notnum))
         (zero (if (equal index 2)
                   (proof-with-checked-results
                    ((moved (t4-algebra-commuted lib *proof-times* other obj)))
                    (proof-proof-chain (library-library-proof lib) moved (list zero)))
                 zero))
         (contradiction (proof-proof-rewrite (library-library-proof lib) product zero '(1 1)))
         (literal (proof-step-first contradiction))
         (answer (t4-algebra-constant lib literal replies) :library)
         (contradiction (proof-proof-rewrite
                         (library-library-proof lib) contradiction answer '(1))))
      (cons (proof-proof-front (library-library-proof lib) contradiction typed) lib))))

(defun t4-field-unit-product (product)
  (proof-with-checked-results
   ((left (t4-field-side product 1))
    (factors (proof-list-of-length left 3)))
   (if (not (equal (car factors) *proof-times*))
       '(:failure "inference-mismatch" "")
     (proof-with-checked-results ((right (t4-field-side product 2)))
       (if (equal right *proof-one*) factors '(:failure "inference-mismatch" ""))))))

(defun t4-field-inverse-from-product-with-replies (lib product replies)
  (t4-algebra-with-library lib ((factors (t4-field-unit-product product)))
    (let* ((factor (cadr factors))
           (candidate (caddr factors))
           (test (proof-eq factor *proof-zero*))
           (recip (list *t4-algebra-reciprocal* factor)))
      (t4-algebra-with-library lib
          ((is-zero (proof-proof-assume (library-library-proof lib) test t))
           (evaluated (proof-proof-rewrite (library-library-proof lib)
                                           product is-zero '(1 1 1)))
           (zero (t4-algebra-multiply-zero-with-replies lib candidate replies) :library)
           (evaluated (proof-proof-rewrite (library-library-proof lib) evaluated zero '(1 1)))
           (literal (proof-step-first evaluated))
           (answer (t4-algebra-constant lib literal replies) :library)
           (impossible (proof-proof-rewrite (library-library-proof lib) evaluated answer '(1)))
           (nonzero (proof-proof-front (library-library-proof lib) impossible (proof-neg test)))
           (proved-factor (t4-field-inverse-from-product-typed
                           factor 1 lib product factor candidate replies) :library)
           (proved-candidate (t4-field-inverse-from-product-typed
                              candidate 2 lib product factor candidate replies) :library)
           (inverse (t4-algebra-product-inverse-with-replies
                     lib factor (list proved-factor nonzero) replies) :library)
           (commuted (t4-algebra-commuted lib *proof-times* recip factor))
           (inverse (proof-proof-chain (library-library-proof lib) commuted (list inverse)))
           (joined (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list recip factor candidate)))
           (joined (proof-proof-rewrite (library-library-proof lib) joined inverse '(1 1 1)))
           (joined (proof-proof-rewrite (library-library-proof lib) joined product '(1 2 2)))
           (left-unit (library-library-axiom lib "UNICITY-OF-1" (list candidate)))
           (left-fixed (t4-algebra-fixed lib candidate proved-candidate))
           (left (proof-proof-chain (library-library-proof lib) left-unit (list left-fixed)))
           (right-commuted (t4-algebra-commuted lib *proof-times* recip *proof-one*))
           (right-unit (library-library-axiom lib "UNICITY-OF-1" (list recip)))
           (right-type (t4-algebra-number-with-replies lib recip nil replies) :library)
           (right-fixed (t4-algebra-fixed lib recip right-type))
           (right (proof-proof-chain (library-library-proof lib)
                                     right-commuted (list right-unit right-fixed)))
           (left (proof-proof-symmetric (library-library-proof lib) left)))
        (cons (proof-proof-chain (library-library-proof lib) left (list joined right)) lib)))))

(defun t4-field-simplified-with-replies (lib proof premises replies)
  (t4-algebra-with-library lib
      ((right (t4-field-side proof 2))
       (normalized (t4-algebra-normal-with-replies lib right premises replies) :library))
    (cons (proof-proof-chain (library-library-proof lib) proof (list normalized)) lib)))

(defun t4-field-reciprocal-terms (terms)
  (if (endp terms)
      nil
    (cons (list *t4-algebra-reciprocal* (car terms))
          (t4-field-reciprocal-terms (cdr terms)))))

(defund t4-field-reciprocal-of-operation-branch (lib goal obj replies)
  (let ((test (proof-eq (list *t4-algebra-fix* obj) *proof-zero*)))
    (t4-algebra-with-library lib
        ((is-zero (proof-proof-assume (library-library-proof lib) test t))
         (a (t4-algebra-replace-fixed-with-replies lib (cadr goal) is-zero replies) :library)
         (a (t4-field-simplified-with-replies lib a nil replies) :library)
         (b (t4-algebra-replace-fixed-with-replies lib (caddr goal) is-zero replies) :library)
         (b (t4-field-simplified-with-replies lib b nil replies) :library)
         (b (proof-proof-symmetric (library-library-proof lib) b))
         (zero (proof-proof-chain (library-library-proof lib) a (list b)))
         (rejected (proof-proof-assume (library-library-proof lib) test nil))
         (nonzero (t4-algebra-nonzero-fix lib obj rejected)))
      (cons (list test zero nonzero) lib))))

(defun t4-field-reciprocal-of-operation-recurse (values premises lib goal body right replies)
  (declare (xargs :measure (acl2-count values)))
  (if (endp values)
      (t4-algebra-with-library lib
          ((product (list *proof-times* body right))
           (normalized (t4-algebra-normal-with-replies lib product premises replies) :library)
           (answer (t4-field-side normalized 2)))
        (if (not (equal answer *proof-one*))
            (cons '(:failure "search-miss" "") lib)
          (t4-algebra-with-library lib
              ((inverse (t4-field-inverse-from-product-with-replies lib normalized replies) :library))
            (cons (proof-proof-symmetric (library-library-proof lib) inverse) lib))))
    (t4-algebra-with-library lib
        ((branch (t4-field-reciprocal-of-operation-branch lib goal (car values) replies) :library)
         (not-zero (t4-field-reciprocal-of-operation-recurse
                    (cdr values) (append premises (caddr branch)) lib goal body right replies)
                   :library))
      (cons (proof-proof-cases (library-library-proof lib) (car branch) (cadr branch) not-zero)
            lib))))

(defun t4-field-reciprocal-of-operation-with-replies (lib goal replies)
  (if (not (proof-is-call goal *proof-equal*))
      (cons nil lib)
    (t4-algebra-with-library lib ((left (proof-term-at goal 1)))
      (if (not (proof-is-call left *t4-algebra-reciprocal*))
          (cons nil lib)
        (t4-algebra-with-library lib
            ((sides (proof-list-of-length (cdr goal) 2))
             (right (cadr sides))
             (body (proof-term-at left 1)))
          (cond
           ((proof-is-call body *proof-times*)
            (if (equal right (cons *proof-times* (t4-field-reciprocal-terms (cdr body))))
                (t4-field-reciprocal-of-operation-recurse (cdr body) nil lib goal body right replies)
              (cons nil lib)))
           ((proof-is-call body *proof-minus*)
            (t4-algebra-with-library lib ((value (proof-term-at body 1)))
              (if (equal right (list *proof-minus* (list *t4-algebra-reciprocal* value)))
                  (t4-field-reciprocal-of-operation-recurse (cdr body) nil lib goal body right replies)
                (cons nil lib))))
           (t (cons nil lib))))))))

(defun t4-field-first-reciprocal (terms)
  (cond ((endp terms) nil)
        ((proof-is-call (car terms) *t4-algebra-reciprocal*) (car terms))
        (t (t4-field-first-reciprocal (cdr terms)))))

(defun t4-field-compare-inverse-with-replies (lib relation products premises replies)
  (if (not (and (proof-is-call relation *proof-equal*)
                (proof-is-call products *proof-equal*)
                (member-equal *proof-one* (cdr products))))
      (cons nil lib)
    (let ((reciprocal (t4-field-first-reciprocal (cdr relation))))
      (if (not reciprocal)
          (cons nil lib)
        (t4-algebra-with-library lib
            ((left (proof-term-at relation 1))
             (candidate (if (equal left reciprocal) (proof-term-at relation 2) left))
             (factor (proof-term-at reciprocal 1))
             (product (if (equal (cadr products) *proof-one*)
                          (proof-term-at products 2)
                        (cadr products))))
          (let ((ordered (list *proof-times* factor candidate))
                (reversed (list *proof-times* candidate factor)))
            (if (not (or (equal product ordered) (equal product reversed)))
                (cons nil lib)
              (t4-algebra-with-library lib
                  ((expected (t4-algebra-product-inverse-with-replies
                              lib factor premises replies) :library))
                (if (not expected)
                    (cons nil lib)
                  (t4-algebra-with-library lib
                      ((swapped (proof-proof-assume (library-library-proof lib) relation t))
                       (assumed (if (equal left reciprocal) swapped
                                  (proof-proof-symmetric (library-library-proof lib) swapped)))
                       (forward (proof-proof-rewrite (library-library-proof lib)
                                                     expected assumed '(1 1 2)))
                       (forward (t4-algebra-orient-normalized-with-replies
                                 lib forward products premises replies) :library)
                       (assumed (proof-proof-assume (library-library-proof lib) products t))
                       (product-rhs (proof-term-at products 2))
                       (known (if (equal product-rhs *proof-one*) assumed
                                (proof-proof-symmetric (library-library-proof lib) assumed)))
                       (known-left (t4-field-side known 1))
                       (known
                        (if (equal known-left ordered)
                            known
                          (proof-with-checked-results
                           ((moved (t4-algebra-commuted lib *proof-times* candidate factor)))
                           (proof-proof-rewrite (library-library-proof lib) known moved '(1 1)))))
                       (backward (t4-field-inverse-from-product-with-replies lib known replies)
                                 :library)
                       (backward (t4-algebra-orient-normalized-with-replies
                                  lib backward relation premises replies) :library))
                    (cons (t4-algebra-equality-tests lib relation products forward backward)
                          lib)))))))))))

(defun t4-field-inverse-zero-test (test)
  (and (proof-is-call test *proof-not*)
    (proof-with-checked-results ((zero (proof-term-at test 1)))
      (and (proof-is-call zero *proof-equal*)
        (proof-with-checked-results ((right (proof-term-at zero 2)))
          (and (equal right *proof-zero*)
            (proof-with-checked-results ((left (proof-term-at zero 1)))
              (and (proof-is-call left *t4-algebra-fix*) zero))))))))

(defun t4-field-factor-in-product-p (terms factor)
  (and (consp terms)
       (or (and (proof-is-call (car terms) *proof-times*)
                (member-equal factor (cdar terms)))
           (t4-field-factor-in-product-p (cdr terms) factor))))

(defun t4-field-inverse-with-zero-case-prove (lib products branch test zero relation factor replies)
  (t4-algebra-with-library lib
      ((nonzero (proof-proof-assume (library-library-proof lib) test t))
       (premises (t4-algebra-nonzero-fix lib factor nonzero))
       (derived (t4-field-compare-inverse-with-replies lib relation products premises replies)
                :library))
    (if (not derived)
        (cons nil lib)
      (t4-algebra-with-library lib
          ((derived (proof-proof-symmetric (library-library-proof lib) derived))
           (selected (proof-proof-select (library-library-proof lib) branch nonzero))
           (selected (proof-proof-symmetric (library-library-proof lib) selected))
           (yes (proof-proof-rewrite (library-library-proof lib) derived selected '(1 2)))
           (not-zero (proof-proof-assume (library-library-proof lib) zero nil))
           (not-test (proof-proof-assume (library-library-proof lib) test nil))
           (accepted (proof-proof-cut (library-library-proof lib) not-zero not-test))
           (accepted (proof-proof-front (library-library-proof lib) accepted zero))
           (replaced (t4-algebra-replace-fixed-with-replies lib products accepted replies) :library)
           (reduced (t4-field-simplified-with-replies lib replaced nil replies) :library)
           (value (t4-field-side reduced 2)))
        (if (not (equal value *proof-false*))
            (cons nil lib)
          (t4-algebra-with-library lib
              ((fallback (proof-proof-if-false (library-library-proof lib) branch))
               (fallback (proof-proof-symmetric (library-library-proof lib) fallback))
               (no (proof-proof-chain (library-library-proof lib) reduced (list fallback))))
            (cons (proof-proof-cases (library-library-proof lib) test yes no) lib)))))))

(defun t4-field-inverse-with-zero-case-with-replies (lib goal replies)
  (t4-algebra-with-library lib
      ((parts (proof-list-of-length (cdr goal) 2)))
    (let ((products (car parts))
          (branch (cadr parts)))
      (if (not (and (proof-is-call products *proof-equal*)
                    (proof-is-call branch *proof-if*)))
          (cons nil lib)
        (t4-algebra-with-library lib ((otherwise (proof-term-at branch 3)))
          (if (not (equal otherwise *proof-false*))
              (cons nil lib)
            (let ((test (cadr branch)) (relation (caddr branch)))
              (t4-algebra-with-library lib
                  ((zero (t4-field-inverse-zero-test test)))
                (if (not zero)
                    (cons nil lib)
                  (t4-algebra-with-library lib ((factor (proof-term-at (cadr zero) 1)))
                    (if (and (t4-field-factor-in-product-p (cdr products) factor)
                             (member-equal *proof-one* (cdr products)))
                        (t4-field-inverse-with-zero-case-prove
                         lib products branch test zero relation factor replies)
                      (cons nil lib))))))))))))

(defun t4-field-scaled-right-prove (lib original conditional parts reciprocal premises replies)
  (t4-algebra-with-library lib
      ((arguments (proof-list-of-length (cdr reciprocal) 1))
       (typed (proof-proof-assume (library-library-proof lib) (car parts) t)))
    (let* ((test (car parts))
           (target (cadr parts))
           (base (car arguments))
           (extra (append premises (list typed)))
           (product (cadr original)))
      (t4-algebra-with-library lib
          ((assumed (proof-proof-assume (library-library-proof lib) original t))
           (forward (t4-algebra-under-operation
                     lib assumed (list *proof-times* base *proof-result*)))
           (forward (t4-algebra-orient-normalized-with-replies
                     lib forward target extra replies) :library)
           (assumed (proof-proof-assume (library-library-proof lib) target t))
           (back (t4-algebra-under-operation
                  lib assumed (list *proof-times* reciprocal *proof-result*)))
           (back (t4-algebra-orient-normalized-with-replies
                  lib back original extra replies) :library)
           (yes (t4-algebra-equality-tests lib original target forward back))
           (selected (proof-proof-select (library-library-proof lib) conditional typed))
           (selected (proof-proof-symmetric (library-library-proof lib) selected))
           (yes (proof-proof-rewrite (library-library-proof lib) yes selected '(1 2)))
           (number (t4-algebra-number-with-replies lib product nil replies) :library)
           (assumed (proof-proof-assume (library-library-proof lib) original t))
           (derived (proof-proof-rewrite (library-library-proof lib) number assumed '(1 1)))
           (denied-num (proof-proof-assume (library-library-proof lib) test nil))
           (cut (proof-proof-cut (library-library-proof lib) derived denied-num))
           (denied-product (proof-proof-front (library-library-proof lib) cut (proof-neg original)))
           (false (t4-algebra-value-of original lib denied-product))
           (fallback (proof-proof-if-false (library-library-proof lib) conditional))
           (fallback (proof-proof-symmetric (library-library-proof lib) fallback))
           (no (proof-proof-chain (library-library-proof lib) false (list fallback))))
        (cons (proof-proof-cases (library-library-proof lib) test yes no) lib)))))

(defun t4-field-scaled-right-with-replies (lib goal premises replies)
  (t4-algebra-with-library lib
      ((sides (proof-list-of-length (cdr goal) 2)))
    (let ((original (car sides)) (conditional (cadr sides)))
      (if (not (proof-is-call original *proof-equal*))
          (cons nil lib)
        (t4-algebra-with-library lib ((product (proof-term-at original 1)))
          (if (not (and (proof-is-call product *proof-times*)
                        (proof-is-call conditional *proof-if*)))
              (cons nil lib)
            (t4-algebra-with-library lib
                ((parts (proof-list-of-length (cdr conditional) 3))
                 (value (proof-term-at original 2)))
              (if (not (and (equal (car parts) (list *library-numberp* value))
                            (proof-is-call (cadr parts) *proof-equal*)
                            (equal (caddr parts) *proof-false*)))
                  (cons nil lib)
                (let ((reciprocal (t4-field-first-reciprocal (cdr product))))
                  (if (not reciprocal)
                      (cons nil lib)
                    (t4-algebra-with-library lib
                        ((base (proof-term-at reciprocal 1))
                         (expected (t4-algebra-product-inverse-with-replies
                                    lib base premises replies) :library))
                      (if (not expected)
                          (cons nil lib)
                        (t4-field-scaled-right-prove
                         lib original conditional parts reciprocal premises replies)))))))))))))

(defun t4-field-formula-parts (formula)
  (if (proof-is-call formula *library-implies*)
      (proof-list-of-length (cdr formula) 2)
    (list :none formula)))

(defun t4-field-identity-prove (lib parts replies)
  (let ((guard (car parts)) (goal (cadr parts)))
    (if (eq guard :none)
        (t4-algebra-with-library lib
            ((step (t4-field-reciprocal-of-operation-with-replies lib goal replies) :library))
          (if step (cons step lib)
            (t4-field-inverse-with-zero-case-with-replies lib goal replies)))
      (t4-algebra-with-library lib
          ((assumed (proof-proof-assume (library-library-proof lib) guard t))
           (premises (t4-division-pieces lib assumed))
           (sides (proof-list-of-length (cdr goal) 2))
           (step (t4-field-compare-inverse-with-replies
                  lib (car sides) (cadr sides) premises replies) :library)
           (step (if step (cons step lib)
                   (t4-field-scaled-right-with-replies lib goal premises replies)) :library))
        (cons (and step (t4-ordinals-ordinals-imply lib guard step)) lib)))))

(defun t4-field-field-identity-with-replies (lib formula replies)
  (t4-algebra-with-library lib ((parts (t4-field-formula-parts formula)))
    (if (not (proof-is-call (cadr parts) *proof-equal*))
        (cons nil lib)
      (let ((arithmetic (t4-algebra-query :arithmetic lib nil replies)))
        (if (t4-algebra-interrupted-p (car arithmetic))
            arithmetic
          (t4-field-identity-prove (cdr arithmetic) parts replies))))))

