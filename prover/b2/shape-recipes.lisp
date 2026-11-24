(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-shape-recipes-a* '("sym" "ACL2" "A"))
(defconst *b2-shape-recipes-b* '("sym" "ACL2" "B"))
(defconst *b2-shape-recipes-r* '("sym" "ACL2" "R"))
(defconst *b2-shape-recipes-i* '("sym" "ACL2" "I"))
(defconst *b2-shape-recipes-j* '("sym" "ACL2" "J"))
(defconst *b2-shape-recipes-v* '("sym" "ACL2" "V"))
(defconst *b2-shape-recipes-force* '("sym" "ACL2" "FORCE"))
(defconst *b2-shape-recipes-expt* '("sym" "COMMON-LISP" "EXPT"))
(defconst *b2-shape-recipes-floor* '("sym" "COMMON-LISP" "FLOOR"))
(defconst *b2-shape-recipes-truncate* '("sym" "COMMON-LISP" "TRUNCATE"))
(defconst *b2-shape-recipes-mod* '("sym" "COMMON-LISP" "MOD"))
(defconst *b2-shape-recipes-rem* '("sym" "COMMON-LISP" "REM"))

(defun b2-shape-recipes-bag-patterns (formulas)
  (if (endp formulas)
      nil
    (cons (list (cdar formulas) :bag (caar formulas) (cdar formulas))
          (b2-shape-recipes-bag-patterns (cdr formulas)))))

(defun b2-shape-recipes-list-patterns ()
  (let* ((x *library-x*) (y *library-y*)
         (map-names *b2-lists-map-names*)
         (sum-list (proof-sym "SUMLIST" "ACL2"))
         (append-symbol (proof-sym "BINARY-APPEND" "ACL2"))
         (rationals (proof-sym "RATIONAL-LISTP" "ACL2"))
         (strings (proof-sym "STRING-LISTP" "ACL2"))
         (rational-sum (list *library-implies* (list rationals x)
                             (list *library-rationalp* (list sum-list x))))
         (sum-append (proof-eq (list sum-list (list append-symbol x y))
                              (library-plus (list sum-list x) (list sum-list y))))
         (string-list (list strings (list map-names x)))
         (character-list (list *b2-lists-char-list* (list *b2-lists-make-chars* x)))
         (name-cons (proof-eq (list map-names (list *proof-cons* x y))
                              (list *proof-cons* (list (proof-cl "SYMBOL-NAME") x)
                                    (list map-names y))))
         (pack-list (list *b2-character-lists-character-list*
                          (list *b2-character-lists-pack-list* x)))
         (pack-tree (list *b2-character-lists-character-list*
                          (list *b2-character-lists-pack-tree* x)))
         (symbol-list (list *b2-sort-order-symbol-list* x))
         (merge-order (list *library-implies* symbol-list
                             (list *b2-sort-order-sorted* (list *b2-sorting-merge-sort* x))))
         (sort-order (list *library-implies* symbol-list
                            (list *b2-sort-order-sorted* (list *b2-sorting-sort* x)))))
    (list (list rational-sum :rational-sum rational-sum)
          (list sum-append :sum-append sum-append)
          (list string-list :mapped-recognizer string-list)
          (list character-list :mapped-recognizer character-list)
          (list name-cons :map-names name-cons)
          (list pack-list :pack-characters nil pack-list)
          (list pack-tree :pack-characters nil pack-tree)
          (list merge-order :sort-order merge-order)
          (list sort-order :sort-wrapper
                (proof-sym "STRICT-SYMBOL<-SORTEDP-SORT-SYMBOL-LISTP" "ACL2")
                sort-order))))

(defun b2-shape-recipes-operand-patterns (operation residual)
  (let* ((x *library-x*) (y *library-y*) (z *library-z*)
         (right (proof-eq (proof-eq (list operation x z) (list operation y z)) residual))
         (left (proof-eq (proof-eq (list operation z x) (list operation z y)) residual)))
    (list (list right :common-operand right)
          (list left :common-operand left))))

(defun b2-shape-recipes-arithmetic-patterns ()
  (let* ((x *library-x*) (y *library-y*) (z *library-z*)
         (zero *proof-zero*)
         (fix *b2-products-fix*)
         (fixed (proof-eq (list fix x) (list fix y)))
         (cancel-zero (proof-eq zero (list fix z)))
         (times *proof-times*)
         (left-distributes
          (proof-eq (list times (library-plus x y) z)
                    (library-plus (list times x z) (list times y z))))
         (right-distributes
          (proof-eq (list times x (library-plus y z))
                    (library-plus (list times x y) (list times x z))))
         (self-inversion (proof-eq (library-minus (library-minus x)) (list fix x)))
         (minus-minus (proof-eq (proof-eq (library-minus x) (library-minus y)) fixed))
         (inverse-zero (proof-eq (proof-eq (library-diff x y) zero) fixed))
         (commutes (proof-eq (list times x (list times y z)) (list times y (list times x z))))
         (multiply-minus-left
          (proof-eq (list times (library-minus x) y) (library-minus (list times x y))))
         (multiply-minus-right
          (proof-eq (list times x (library-minus y)) (library-minus (list times x y)))))
    (append
     (list (list (proof-eq (list times x zero) zero) :zero-product x)
           (list (proof-eq (list times zero x) zero) :zero-left-product x)
           (list left-distributes :distributivity left-distributes)
           (list right-distributes :axiom "DISTRIBUTIVITY" (list x y z)))
     (b2-shape-recipes-operand-patterns *proof-plus* fixed)
     (b2-shape-recipes-operand-patterns times (proof-ite cancel-zero cancel-zero fixed))
     (list (list self-inversion :arithmetic-identity
                 (proof-sym "FUNCTIONAL-SELF-INVERSION-OF-MINUS" "ACL2") self-inversion)
           (list minus-minus :arithmetic-identity
                 (proof-sym "EQUAL-MINUS-MINUS" "ACL2") minus-minus)
           (list inverse-zero :arithmetic-identity
                 (proof-sym "INVERSE-OF-+-AS=0" "ACL2") inverse-zero)
           (list commutes :arithmetic-identity
                 (proof-sym "COMMUTATIVITY-2-OF-*" "ACL2") commutes)
           (list multiply-minus-left :arithmetic-identity
                 (proof-sym "FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT" "ACL2")
                 multiply-minus-left)
           (list multiply-minus-right :arithmetic-identity
                 (proof-sym "FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT" "ACL2")
                 multiply-minus-right)))))

(defun b2-shape-recipes-reciprocal-patterns ()
  (let* ((x *library-x*) (y *library-y*)
         (zero *proof-zero*)
         (fix *b2-products-fix*)
         (recip *b2-products-recip*)
         (times *proof-times*)
         (fixed-x (list fix x))
         (fixed-y (list fix y))
         (zero-x (proof-eq fixed-x zero))
         (zero-y (proof-eq fixed-y zero))
         (rx (list recip x))
         (ry (list recip y))
         (minus-zero (proof-eq (proof-eq zero (library-minus x)) (proof-eq zero fixed-x)))
         (invert-twice (proof-eq (list recip rx) fixed-x))
         (invert-product (proof-eq (list recip (list times x y)) (list times rx ry)))
         (invert-minus (proof-eq (list recip (library-minus x)) (library-minus rx)))
         (injective (proof-eq (proof-eq rx ry) (proof-eq fixed-x fixed-y)))
         (zero-product (proof-eq (proof-eq (list times x y) zero)
                                 (proof-ite zero-x zero-x zero-y))))
    (list (list minus-zero :reciprocal *b2-reciprocal-minus-zero* minus-zero)
          (list invert-twice :reciprocal *b2-reciprocal-invert-twice* invert-twice)
          (list invert-product :reciprocal *b2-reciprocal-invert-product* invert-product)
          (list invert-minus :reciprocal *b2-reciprocal-invert-minus* invert-minus)
          (list injective :reciprocal *b2-reciprocal-injective* injective)
          (list zero-product :reciprocal *b2-reciprocal-zero-product* zero-product))))

(defun b2-shape-recipes-power-patterns ()
  (let* ((x *library-x*) (r *b2-shape-recipes-r*)
         (i *b2-shape-recipes-i*) (j *b2-shape-recipes-j*)
         (zero *proof-zero*) (one *proof-one*)
         (implies *library-implies*) (expt *b2-shape-recipes-expt*)
         (power (list expt r i))
         (unit (proof-eq (list expt one x) one))
         (integer-result
          (list implies (b2-powers-and-terms (list (proof-neg (library-lt i zero))
                                                   (library-integer r)))
                (library-integer power)))
         (nonzero
          (list implies (b2-powers-and-terms (list (list *library-numberp* r)
                                                   (proof-neg (proof-eq r zero))))
                (proof-neg (proof-eq zero power))))
         (positive
          (list implies (b2-powers-and-terms (list (library-lt zero r) (list *library-rationalp* r)))
                (library-lt zero power)))
         (sum (library-plus i j))
         (combined (list expt x sum))
         (multiplied (list *proof-times* (list expt x i) (list expt x j)))
         (typed (b2-powers-and-terms (list (library-integer i) (library-integer j))))
         (zero-base (proof-eq (list *b2-products-fix* x) zero))
         (aggressive
          (list implies typed
                (proof-eq combined (proof-ite (proof-eq sum zero) one
                                              (proof-ite zero-base zero multiplied)))))
         (inverse
          (list implies typed
                (proof-eq multiplied
                          (proof-ite (b2-powers-and-terms
                                      (list (proof-eq i zero) (proof-eq j zero)))
                                     one (proof-ite zero-base zero combined))))))
    (list (list unit :exponent-type *b2-exponent-types-unit* unit)
          (list integer-result :exponent-type *b2-exponent-types-integer* integer-result)
          (list nonzero :exponent-type *b2-exponent-types-nonzero* nonzero)
          (list positive :exponent-type *b2-exponent-types-positive* positive)
          (list aggressive :expt-add (proof-sym "EXPTS-ADD-AGGRESSIVE" "ACL2") aggressive)
          (list inverse :expt-add (proof-sym "EXPTS-ADD-INVERSE" "ACL2") inverse))))

(defun b2-shape-recipes-factorial-patterns ()
  (let* ((factorial (list *b2-arithmetic-factorial* *library-x*))
         (positive (b2-powers-and-terms
                    (list (library-integer factorial) (library-lt *proof-zero* factorial))))
         (nonnegative (proof-neg (library-lt factorial *proof-one*)))
         (magnitude (proof-eq (list (proof-cl "ABS") factorial) factorial)))
    (list (list positive :factorial-positive positive)
          (list nonnegative :factorial-properties
                (proof-sym "FACTORIAL-NON-NEGATIVE" "ACL2") nonnegative)
          (list magnitude :factorial-properties (proof-sym "ABS-FACTORIAL" "ACL2") magnitude))))

(defun b2-shape-recipes-quotient-pattern (name operation condition ratio)
  (let* ((value (if (member-equal operation (list *b2-shape-recipes-mod* *b2-shape-recipes-rem*))
                    *proof-zero*
                  ratio))
         (result (proof-eq (proof-eq (list operation *library-x* *library-y*) value)
                           (library-integer ratio)))
         (formula (if (equal operation *b2-shape-recipes-floor*)
                      result
                    (list *library-implies* condition result))))
    (list formula :quotient-identity name formula)))

(defun b2-shape-recipes-quotient-patterns ()
  (let* ((x *library-x*) (y *library-y*)
         (ratio (list *proof-times* x (list *b2-products-recip* y)))
         (force *b2-shape-recipes-force*)
         (condition (b2-powers-and-terms
                     (list (list force (list *library-rationalp* x))
                           (list force (list *library-rationalp* y))
                           (list force (proof-neg (proof-eq *proof-zero* y)))))))
    (list (b2-shape-recipes-quotient-pattern
           *b2-quotient-algebra-exact-floor* *b2-shape-recipes-floor* condition ratio)
          (b2-shape-recipes-quotient-pattern
           *b2-quotient-algebra-exact-truncate* *b2-shape-recipes-truncate* condition ratio)
          (b2-shape-recipes-quotient-pattern
           *b2-quotient-algebra-zero-mod* *b2-shape-recipes-mod* condition ratio)
          (b2-shape-recipes-quotient-pattern
           *b2-quotient-algebra-zero-rem* *b2-shape-recipes-rem* condition ratio))))

(defun b2-shape-recipes-pair-patterns ()
  (let* ((x *library-x*) (a *b2-shape-recipes-a*) (b *b2-shape-recipes-b*)
         (head *library-car*) (tail *library-cdr*) (size *library-count*)
         (implies *library-implies*)
         (pair (list *b2-pair-products-pair* a b))
         (typed (list *b2-pair-products-pairp* x))
         (first (proof-eq (list head pair) a))
         (last (proof-eq (list tail pair) b))
         (rebuild (list implies typed
                        (proof-eq (list *b2-pair-products-pair* (list head x) (list tail x)) x)))
         (same (list implies typed
                     (proof-eq (proof-eq x pair)
                               (b2-powers-and-terms (list (proof-eq (list head x) a)
                                                         (proof-eq (list tail x) b))))))
         (bound (b2-powers-and-terms
                 (list (proof-neg (library-lt (list size pair) (list size a)))
                       (proof-neg (library-lt (list size pair) (list size b))))))
         (tag (list implies (list *b2-pair-products-tag* x) (list *proof-consp* x))))
    (list (list first :pair (cdr (assoc-equal head *b2-pair-products-selectors*)) first)
          (list last :pair (cdr (assoc-equal tail *b2-pair-products-selectors*)) last)
          (list rebuild :pair *b2-pair-products-rebuild* rebuild)
          (list same :pair *b2-pair-products-equality* same)
          (list bound :pair *b2-pair-products-size* bound)
          (list tag :pair *b2-pair-products-tag-cons* tag))))

(defun b2-shape-recipes-fixed-patterns (fixes)
  (if (endp fixes)
      nil
    (let* ((fixer (cadr (cdar fixes)))
           (formula (list (caar fixes) (list fixer *library-x*) *library-x*)))
      (cons (list formula :completed-equivalence formula)
            (b2-shape-recipes-fixed-patterns (cdr fixes))))))

(defun b2-shape-recipes-record-patterns ()
  (let* ((a *b2-shape-recipes-a*) (b *b2-shape-recipes-b*)
         (v *b2-shape-recipes-v*) (r *b2-shape-recipes-r*)
         (x *library-x*) (y *library-y*)
         (get *b2-records-get*) (set *b2-records-set*)
         (implies *library-implies*)
         (same (proof-eq a b))
         (different (proof-neg same))
         (read-update (list get a (list set b v r)))
         (read-original (list get a r))
         (set-same (proof-eq (list get a (list set a v r)) v))
         (set-different (list implies different (proof-eq read-update read-original)))
         (set-read (proof-eq (list set a read-original r) r))
         (redux (proof-eq read-update (proof-ite same v read-original)))
         (get-nil (proof-neg (list get a *proof-false*)))
         (non-nil (list implies read-original r))
         (set-non-nil (list implies v (list set a v r)))
         (set-same-twice (proof-eq (list set a y (list set a x r)) (list set a y r)))
         (set-different-twice
          (list implies different
                (proof-eq (list set b y (list set a x r)) (list set a x (list set b y r))))))
    (list (list set-same :record-law *b2-records-set-same* set-same)
          (list set-different :record-law *b2-records-set-different* set-different)
          (list set-read :record-law (proof-sym "S-SAME-G" "ACL2") set-read)
          (list redux :record-corollary (proof-sym "G-OF-S-REDUX" "ACL2") redux)
          (list get-nil :record-corollary *b2-records-get-nil* get-nil)
          (list non-nil :record-corollary (proof-sym "NON-NIL-IF-G-NON-NIL" "ACL2") non-nil)
          (list set-non-nil :record-corollary (proof-sym "S-NON-NIL-CANNOT-BE-NIL" "ACL2")
                set-non-nil)
          (list set-same-twice :record-extensionality (proof-sym "S-SAME-S" "ACL2") set-same-twice)
          (list set-different-twice :record-extensionality (proof-sym "S-DIFF-S" "ACL2")
                set-different-twice))))

(defun b2-shape-recipes-patterns ()
  (let* ((x *library-x*)
         (bit (list *library-implies* (list *b2-completions-bitp* x)
                    (proof-eq (list *b2-completions-bfix* x) x))))
    (append (b2-shape-recipes-bag-patterns *b2-bags-formulas*)
            (b2-shape-recipes-list-patterns)
            (b2-shape-recipes-arithmetic-patterns)
            (b2-shape-recipes-reciprocal-patterns)
            (b2-shape-recipes-power-patterns)
            (b2-shape-recipes-factorial-patterns)
            (b2-shape-recipes-quotient-patterns)
            (b2-shape-recipes-pair-patterns)
            (b2-shape-recipes-fixed-patterns *b2-completions-fixes*)
            (list (list bit :completion *b2-completions-bit-identity* bit))
            (b2-shape-recipes-record-patterns))))

(defun b2-shape-recipes-build-routes (patterns routes)
  (if (endp patterns)
      routes
    (let* ((pattern (car patterns))
           (head (caar pattern))
           (bucket (table-get routes head nil)))
      (b2-shape-recipes-build-routes
       (cdr patterns) (table-put routes head (append bucket (list pattern)))))))

(defconst *b2-shape-recipes-routes*
  (b2-shape-recipes-build-routes (b2-shape-recipes-patterns) nil))

(defun b2-shape-recipes-with-library (step lib)
  (if (failure-p step) step (cons step lib)))

(defun b2-shape-recipes-apply (lib recipe args)
  (let ((first (car args))
        (second (cadr args)))
    (case recipe
      (:bag (b2-bags-prove-bag lib first second))
      (:rational-sum (b2-shape-recipes-with-library (b2-lists-rational-sum lib first) lib))
      (:sum-append (b2-shape-recipes-with-library (b2-lists-sum-append lib first) lib))
      (:mapped-recognizer
       (b2-shape-recipes-with-library (b2-lists-mapped-recognizer lib first) lib))
      (:map-names
       (b2-shape-recipes-with-library
        (b2-tactics-tactics-solve lib first nil (list *b2-lists-map-names*) nil 0 nil) lib))
      (:pack-characters (b2-character-lists-pack-characters lib first second))
      (:sort-order (b2-sort-order-sort-order lib first))
      (:sort-wrapper (b2-shape-recipes-with-library (b2-sorting-sort-wrapper lib first second) lib))
      (:zero-product (b2-products-zero-product lib first))
      (:zero-left-product (b2-products-zero-left-product lib first))
      (:distributivity (b2-shape-recipes-with-library (b2-recipes-distributivity lib first) lib))
      (:axiom (b2-shape-recipes-with-library (library-library-axiom lib first second) lib))
      (:common-operand (b2-algebra-common-operand lib first))
      (:arithmetic-identity (b2-algebra-arithmetic-identity lib first second))
      (:reciprocal (b2-reciprocal-reciprocal-theorem lib first second))
      (:exponent-type (b2-exponent-types-exponent-type lib first second))
      (:expt-add (b2-powers-expt-add lib first second))
      (:factorial-positive
       (b2-shape-recipes-with-library (b2-arithmetic-factorial-positive lib first) lib))
      (:factorial-properties
       (b2-shape-recipes-with-library (b2-arithmetic-factorial-properties lib first second) lib))
      (:quotient-identity (b2-quotient-algebra-quotient-identity lib first second))
      (:pair (b2-shape-recipes-with-library (b2-pair-products-pair-theorem lib first second) lib))
      (:completed-equivalence
       (b2-shape-recipes-with-library (b2-completions-completed-equivalence lib first) lib))
      (:completion (b2-completions-completion-theorem lib first second))
      (:record-law (b2-record-update-record-law lib first second))
      (:record-corollary
       (b2-shape-recipes-with-library (b2-records-record-corollary lib first second) lib))
      (:record-extensionality (b2-record-extensionality-record-extensionality lib first second))
      (otherwise (b2-tactics-unproved)))))

(defun b2-shape-recipes-try-routes (lib formula routes)
  (if (endp routes)
      (b2-tactics-unproved)
    (let* ((route (car routes))
           (schematic (car route))
           (matched (b2-tactics-match schematic formula nil)))
      (if (car matched)
          (proof-with-checked-results
              ((result (b2-shape-recipes-apply lib (cadr route) (cddr route)))
               (proof (library-library-proof (cdr result)))
               (step (proof-proof-subsume proof (car result) (list schematic)))
               (instance (proof-proof-instantiate proof step (table-items (cdr matched)))))
            (cons instance (cdr result)))
        (b2-shape-recipes-try-routes lib formula (cdr routes))))))

(defun b2-shape-recipes-prove-shape (lib formula)
  (if (proof-compound formula)
      (proof-with-checked-results ((head (proof-term-at formula 0)))
        (b2-shape-recipes-try-routes lib formula (table-get *b2-shape-recipes-routes* head nil)))
    (b2-tactics-unproved)))
