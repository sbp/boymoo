(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-folds-abst* (proof-sym "ABST" "ACL2"))
(defconst *b2-folds-mult* (proof-sym "MULT" "ACL2"))
(defconst *b2-folds-reverse* (proof-cl "REVERSE"))
(defconst *b2-folds-revappend* (proof-cl "REVAPPEND"))
(defconst *b2-folds-stringp* (proof-cl "STRINGP"))
(defconst *b2-folds-item* (proof-sym "ITEM" "ACL2"))
(defconst *b2-folds-root* (proof-sym "ROOT" "ACL2"))

(defun b2-folds-multiplication (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*) (y *library-y*)
         (left (list *b2-folds-mult* x y))
         (formula (proof-eq left (b2-products-product x y)))
         (nx (list *library-numberp* x))
         (ny (list *library-numberp* y))
         (xfix (list *b2-products-fix* x))
         (yfix (list *b2-products-fix* y)))
    (proof-with-checked-results
        ((x-yes (proof-proof-assume proof nx t))
         (x-no (proof-proof-assume proof nx nil))
         (y-yes (proof-proof-assume proof ny t))
         (y-no (proof-proof-assume proof ny nil))
         (both (b2-tactics-tactics-solve lib formula (list x-yes y-yes)
                                        (list left xfix yfix) nil 0 nil))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list *proof-zero* yfix)))
         (zero-pair (b2-products-zero-product lib yfix))
         (lib (cdr zero-pair))
         (proof (library-library-proof lib))
         (left-zero (proof-proof-chain proof commute (list (car zero-pair))))
         (completion (b2-products-product-completion lib x y (list x-no)))
         (missing-x (b2-tactics-tactics-solve lib formula (list x-no) (list left xfix)
                                             (list left-zero completion) 0 nil))
         (zero-pair (b2-products-zero-product lib x))
         (lib (cdr zero-pair))
         (proof (library-library-proof lib))
         (completion (b2-products-product-completion lib x y (list x-yes y-no)))
         (missing-y (b2-tactics-tactics-solve lib formula (list x-yes y-no) (list left xfix yfix)
                                             (list (car zero-pair) completion) 0 nil))
         (has-x (proof-proof-cases proof ny both missing-y))
         (step (proof-proof-cases proof nx has-x missing-x)))
      (b2-tactics-tactics-add-lemma lib "MULT-EQUALS-PRODUCT" step :none))))

(defun b2-folds-operator-laws (lib name)
  (if (equal name *b2-folds-abst*)
      (cons :abst lib)
    (b2-folds-multiplication lib)))

(defun b2-folds-operator-laws-abst-law (kind args lib)
  (let ((fact (proof-sym (if (equal kind "ASSOCIATIVITY") "ABST-ASSOC" "ABST-COMM") "ACL2")))
    (proof-proof-fact (library-library-proof lib) fact
                      (seq-zip (list *library-x* *library-y* *library-z*) args))))

(mutual-recursion
 (defun b2-folds-operator-laws-law-mult-rules (term lib mult)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond ((not (proof-compound term)) nil)
         ((endp term) '(:failure "tactic-rejected" ""))
         ((equal (car term) *proof-quote*) nil)
         (t (proof-with-checked-results
                ((fact (and (proof-is-call term *b2-folds-mult*)
                            (proof-proof-fact (library-library-proof lib) mult
                                              (seq-zip (list *library-x* *library-y*) (cdr term)))))
                 (rest (b2-folds-operator-laws-mult-argument-rules (cdr term) lib mult)))
              (if fact (cons fact rest) rest)))))
 (defun b2-folds-operator-laws-mult-argument-rules (args lib mult)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((first (b2-folds-operator-laws-law-mult-rules (car args) lib mult))
          (rest (b2-folds-operator-laws-mult-argument-rules (cdr args) lib mult)))
       (append first rest)))))

(defun b2-folds-operator-laws-mult-sides (args)
  (cond ((integerp args) '(:failure "tactic-rejected" ""))
        ((< (len args) 2)
         '(:failure "inapplicable" ""))
        ((endp (cddr args))
         (list (list *b2-folds-mult* (car args) (cadr args))
               (list *b2-folds-mult* (cadr args) (car args))))
        (t (proof-with-checked-results ((rest (proof-list-of-length (cddr args) 1)))
             (let ((a (car args)) (b (cadr args)) (c (car rest)))
               (list (list *b2-folds-mult* (list *b2-folds-mult* a b) c)
                     (list *b2-folds-mult* a (list *b2-folds-mult* b c))))))))

(defun b2-folds-operator-laws-mult-law (kind args lib mult)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((sides (b2-folds-operator-laws-mult-sides args))
         (left (car sides))
         (right (cadr sides))
         (rules (b2-folds-operator-laws-law-mult-rules left lib mult))
         (first (b2-tactics-tactics-normalize lib left nil nil rules 1500 nil))
         (rules (b2-folds-operator-laws-law-mult-rules right lib mult))
         (last (b2-tactics-tactics-normalize lib right nil nil rules 1500 nil))
         (operator (library-library-axiom lib (string-append kind "-OF-*") args))
         (symmetric (if last
                        (proof-proof-symmetric proof last)
                      '(:failure "failure" ""))))
      (if first
          (proof-proof-chain proof first (list operator symmetric))
        '(:failure "failure" "")))))

(defun b2-folds-operator-laws-law (lib kind args law)
  (if (eq law :abst)
      (b2-folds-operator-laws-abst-law kind args lib)
    (b2-folds-operator-laws-mult-law kind args lib law)))

(defun b2-folds-noncons-string (lib term string)
  (let ((proof (library-library-proof lib)) (test (list *proof-consp* term)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof "consp-not-stringp" (list (list *library-x* term))))
         (cons-step (proof-proof-assume proof test t))
         (disjoint (proof-proof-modus-ponens proof fact cons-step))
         (cut (proof-proof-cut proof string disjoint)))
      (proof-proof-front proof cut (proof-neg test)))))

(defun b2-folds-fold-reverse-f (lst accumulator fold)
  (list fold lst accumulator))

(defmacro b2-folds-prove-on-list (lib formula variable extra signed hypothesis advance base)
  `(proof-with-checked-results
       ((b2-folds-request (b2-tactics-tactics-on-list ,lib ,formula ,variable nil nil ,extra))
        (,signed (cadddr (car b2-folds-request)))
        (,hypothesis (car (cddddr (car b2-folds-request))))
        (b2-folds-advance ,advance)
        (b2-folds-request (b2-tactics-tactics-on-list
                           ,lib ,formula ,variable nil (cons b2-folds-advance ,lib) ,extra))
        (,signed (cadddr (car b2-folds-request)))
        (b2-folds-base ,base)
        (b2-folds-result (b2-tactics-tactics-on-list
                          ,lib ,formula ,variable (cons b2-folds-base ,lib)
                          (cons b2-folds-advance ,lib) ,extra)))
     (car b2-folds-result)))

(defun b2-folds-fold-reverse-swap-base (atom lib swap-formula left-swap fold-x)
  (b2-tactics-tactics-solve lib swap-formula (list atom) (list left-swap fold-x) nil 0 nil))

(defun b2-folds-fold-reverse-swap-advance
    (cons-step hypothesis lib law left-swap right-swap item tail root fold fold-x)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (b2-tactics-tactics-normalize lib left-swap (list cons-step)
                                             (list left-swap) (list hypothesis) 1500 nil))
         (v (b2-folds-fold-reverse-f tail root fold))
         (assoc-step (b2-folds-operator-laws-law lib "ASSOCIATIVITY" (list item *b2-folds-item* v) law))
         (swap (proof-proof-symmetric proof assoc-step))
         (commute (b2-folds-operator-laws-law lib "COMMUTATIVITY" (list item *b2-folds-item*) law))
         (swap (proof-proof-rewrite proof swap commute '(1 2 1)))
         (assoc-step (b2-folds-operator-laws-law lib "ASSOCIATIVITY" (list *b2-folds-item* item v) law))
         (swap (proof-proof-chain proof swap (list assoc-step)))
         (last (b2-tactics-tactics-normalize lib right-swap (list cons-step) (list fold-x) nil 1500 nil))
         (symmetric (if last
                        (proof-proof-symmetric proof last)
                      '(:failure "failure" ""))))
      (if first
          (proof-proof-chain proof first (list swap symmetric))
        '(:failure "failure" "")))))

(defun b2-folds-fold-reverse-append-base (atom lib append-formula reverse composed)
  (b2-tactics-tactics-solve lib append-formula (list atom) (list reverse composed) nil 0 nil))

(defun b2-folds-fold-reverse-append-advance
    (cons-step hypothesis lib append-formula reverse composed extended root fold swap x tail item fold-y)
  (let ((inner (b2-folds-fold-reverse-f extended root fold)))
    (proof-with-checked-results
        ((inner (b2-tactics-tactics-normalize lib inner nil (list inner) nil 1500 nil))
         (moved (proof-proof-fact (library-library-proof lib) swap
                                 (list (list x tail) (list *b2-folds-item* item) (list root fold-y)))))
      (b2-tactics-tactics-solve lib append-formula (list cons-step) (list reverse composed)
                               (list hypothesis inner moved) 0 nil))))

(defun b2-folds-reverse-branches (lib formula left right x root fold append-fold)
  (let ((proof (library-library-proof lib))
        (test (list *b2-folds-stringp* x))
        (value (b2-folds-fold-reverse-f *proof-false* root fold)))
    (proof-with-checked-results
        ((string (proof-proof-assume proof test t))
         (other (proof-proof-assume proof test nil))
         (nil-fold (b2-tactics-tactics-normalize lib value nil (list value) nil 1500 nil))
         (use-append-fold (proof-proof-instantiate proof append-fold (list (list *library-y* *proof-false*))))
         (reversed (proof-term-at left 1))
         (no (b2-tactics-tactics-solve lib formula (list other) (list reversed)
                                      (list use-append-fold nil-fold) 0 nil))
         (equation (b2-tactics-tactics-normalize lib reversed (list string) (list reversed) nil 1500 nil))
         (literal (if equation
                      (proof-step-first equation)
                    '(:failure "failure" "")))
         (result (proof-term-at literal 2))
         (result-string (b2-tactics-tactics-use-fact lib '("str" "stringp-coerce")
                                                    (list *b2-folds-stringp* result) nil nil nil 0 nil))
         (result-atom (b2-folds-noncons-string lib result result-string))
         (symmetric (proof-proof-symmetric proof equation))
         (result-atom (proof-proof-rewrite proof result-atom symmetric '(1 1 1)))
         (result-atom (proof-proof-tidy proof result-atom))
         (input-atom (b2-folds-noncons-string lib x string))
         (yes (b2-tactics-tactics-solve lib formula (list input-atom result-atom)
                                       (list left right) nil 0 nil))
         (step (proof-proof-cases proof test yes no)))
      (cons step lib))))

(defun b2-folds-reverse-append (lib formula left right x root fold item tail swap)
  (let* ((fold-y (b2-folds-fold-reverse-f *library-y* root fold))
         (reverse (list *b2-folds-revappend* x *library-y*))
         (composed (b2-folds-fold-reverse-f x fold-y fold))
         (append-formula (proof-eq (b2-folds-fold-reverse-f reverse root fold) composed))
         (extended (list *proof-cons* item *library-y*))
         (extra (list (list *library-y* extended))))
    (proof-with-checked-results
        ((append-fold
          (b2-folds-prove-on-list lib append-formula x extra signed hypothesis
            (b2-folds-fold-reverse-append-advance signed hypothesis lib append-formula
                                                 reverse composed extended root fold swap x tail item fold-y)
            (b2-folds-fold-reverse-append-base signed lib append-formula reverse composed))))
      (b2-folds-reverse-branches lib formula left right x root fold append-fold))))

(defun b2-folds-reverse-operator (lib fold)
  (let ((definition (assoc-equal fold (proof-proof-definitions (library-library-proof lib)))))
    (if (not definition)
        '(:failure "tactic-rejected" "")
      (proof-with-checked-results
          ((body (proof-term-at (cdr definition) 1))
           (branch (proof-term-at body 2)))
        (proof-term-at branch 0)))))

(defun b2-folds-fold-reverse (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (left (cadr parts))
       (right (caddr parts))
       (args (proof-list-of-length right 3))
       (fold (car args))
       (op (b2-folds-reverse-operator lib fold))
       (law-pair (b2-folds-operator-laws lib op))
       (law (car law-pair))
       (lib (cdr law-pair))
       (name (proof-term-at fold 2)))
    (if (not (stringp name))
        '(:failure "failure" "")
      (let* ((x (cadr args)) (root (caddr args))
             (item (list *library-car* x)) (tail (list *library-cdr* x))
             (fold-x (b2-folds-fold-reverse-f x root fold))
             (left-swap (b2-folds-fold-reverse-f x (list op *b2-folds-item* root) fold))
             (right-swap (list op *b2-folds-item* fold-x))
             (swap-formula (proof-eq left-swap right-swap)))
        (proof-with-checked-results
            ((swap
              (b2-folds-prove-on-list lib swap-formula x nil signed hypothesis
                (b2-folds-fold-reverse-swap-advance signed hypothesis lib law left-swap right-swap
                                                   item tail root fold fold-x)
                (b2-folds-fold-reverse-swap-base signed lib swap-formula left-swap fold-x)))
             (swap (b2-tactics-tactics-add-lemma lib (string-append name "-ACCUMULATOR") swap :none)))
          (b2-folds-reverse-append (cdr swap) formula left right x root fold item tail (car swap)))))))
