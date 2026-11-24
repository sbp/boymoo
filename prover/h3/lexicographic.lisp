(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-lexicographic-lex* (proof-sym "LEXORDER" "ACL2"))

(defun h3-lexicographic-reconstruct-cons (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (heads (proof-eq (list *library-car* x) (list *library-car* y)))
         (tails (proof-eq (list *library-cdr* x) (list *library-cdr* y)))
         (cons-x (list *proof-consp* x))
         (cons-y (list *proof-consp* y)))
    (proof-with-checked-results
        ((elimination (library-library-axiom lib "CAR-CDR-ELIM" (list x)))
         (x-cons (proof-proof-assume proof cons-x t))
         (x-reconstructed (proof-proof-modus-ponens proof elimination x-cons))
         (replacement (proof-proof-symmetric proof x-reconstructed))
         (equal-heads (proof-proof-assume proof heads t))
         (replacement (proof-proof-rewrite proof replacement equal-heads '(1 2 1)))
         (equal-tails (proof-proof-assume proof tails t))
         (replacement (proof-proof-rewrite proof replacement equal-tails '(1 2 2)))
         (elimination (library-library-axiom lib "CAR-CDR-ELIM" (list y)))
         (y-cons (proof-proof-assume proof cons-y t))
         (reconstruct-y (proof-proof-modus-ponens proof elimination y-cons))
         (conclusion (proof-proof-chain proof replacement (list reconstruct-y)))
         (lib (library-library-lemma
                lib "H3-CONS-EQUALITY" (proof-eq x y) conclusion
                (list (proof-neg cons-x) (proof-neg cons-y)
                      (proof-neg heads) (proof-neg tails)))))
      (cons (proof-sym "SELF-H3-CONS-EQUALITY" "ACL2") lib))))

(defun h3-lexicographic-lexorder-prove-case
    (evidence lib names calls property-name formula)
  (proof-with-checked-results ((rules (h3-rewrite-rules-init lib names nil)))
    (let ((search (h3-rewrite-search-init
                   lib (list (proof-cl "ATOM")) calls rules 400
                   (equal property-name "TOTAL"))))
      (car (h3-rewrite-search-prove search formula evidence)))))

(defun h3-lexicographic-selector-mapping (variables selector)
  (if (endp variables)
      nil
    (let ((variable (car variables)))
      (cons (cons variable (list selector variable))
            (h3-lexicographic-selector-mapping (cdr variables) selector)))))

(defun h3-lexicographic-induction
    (n lib formula replacements names calls property-name result-and-replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h3-lexicographic-induction")
    (let ((result (car result-and-replies)))
      (if (h3-induction-request-p result)
          (h3-lexicographic-induction
           (1- n) lib formula replacements names calls property-name
           (let ((reply (h3-lexicographic-lexorder-prove-case
                         (h3-induction-request-evidence result)
                         lib names calls property-name formula)))
             (if (failure-p reply)
                 (list reply)
               (let ((replies (append (cdr result-and-replies) (list reply))))
                 (cons (h3-induction-structural-induction
                        lib formula *library-x* replacements replies)
                       replies)))))
        result))))

(defun h3-lexicographic-lexorder (lib name formula)
  (let* ((property-name (if (text-starts-with name "LEXORDER-")
                            (seq-slice name 9 :none)
                          name))
         (x *library-x*)
         (y *library-y*)
         (z *library-z*)
         (lex *h3-lexicographic-lex*)
         (variables (cond ((equal property-name "REFLEXIVE") (list x))
                          ((equal property-name "TRANSITIVE") (list x y z))
                          ((member-equal property-name '("ANTI-SYMMETRIC" "TOTAL"))
                           (list x y))
                          (t nil)))
         (calls (cond ((equal property-name "REFLEXIVE") (list (list lex x x)))
                      ((equal property-name "TRANSITIVE")
                       (list (list lex x y) (list lex y z) (list lex x z)))
                      (t (list (list lex x y) (list lex y x)))))
         (names (list (proof-sym (concatenate 'string "ALPHORDER-" property-name)
                                 "ACL2")))
         (tail (list (h3-lexicographic-selector-mapping variables *library-cdr*) 3))
         (replacements
          (if (equal (len variables) 1)
              (list tail)
            (list (list (h3-lexicographic-selector-mapping variables *library-car*) 2)
                  tail))))
    (if (not variables)
        '(:failure "MissingProofData" "")
      (proof-with-checked-results
          ((addition (if (equal property-name "ANTI-SYMMETRIC")
                         (h3-lexicographic-reconstruct-cons lib)
                       (cons (and (equal property-name "TRANSITIVE")
                                  (proof-sym "LEXORDER-ANTI-SYMMETRIC" "ACL2"))
                             lib)))
           (lib (cdr addition))
           (result (h3-induction-structural-induction
                    lib formula *library-x* replacements nil))
           (step (h3-lexicographic-induction
                  1000000 lib formula replacements
                  (if (car addition) (append names (list (car addition))) names)
                  calls property-name (list result))))
        (cons step lib)))))
