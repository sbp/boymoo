(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t3-book-counterexamples-count* (proof-sym "HOW-MANY" "ACL2"))
(defconst *t3-book-counterexamples-find* (proof-sym "PERM-COUNTER-EXAMPLE" "ACL2"))
(defconst *t3-book-counterexamples-fix* (proof-sym "TLFIX" "ACL2"))
(defconst *t3-book-counterexamples-checked-count*
  (proof-sym "PERM-COUNTER-EXAMPLE-IS-COUNTEREXAMPLE-FOR-TRUE-LISTS" "ACL2"))

(defun t3-book-counterexamples-occurrence-comparison (x y)
  (let ((key (list *t3-book-counterexamples-find* x y)))
    (proof-eq (list *t3-book-counterexamples-count* key x)
              (list *t3-book-counterexamples-count* key y))))

(defun t3-book-counterexamples-statement (x y)
  (proof-eq (list *t3-book-permutations-perm* x y)
            (t3-book-counterexamples-occurrence-comparison x y)))

(defun t3-book-counterexamples-list-statement (x y)
  (list *library-implies*
        (proof-ite (list *t3-book-lemmas-true-listp* x)
                   (list *t3-book-lemmas-true-listp* y)
                   *proof-false*)
        (t3-book-counterexamples-statement x y)))

(defun t3-book-counterexamples-equal-successors (lib a b integers)
  (let* ((proof (library-library-proof lib))
         (left (library-plus *proof-one* a))
         (right (library-plus *proof-one* b))
         (raw (proof-eq a b))
         (shifted (proof-eq left right))
         (inverse-left (library-plus *proof-neg-one* left))
         (inverse-right (library-plus *proof-neg-one* right)))
    (proof-with-checked-results
     ((yes (proof-proof-assume proof raw t))
      (same (proof-proof-reflexive proof left))
      (same (t3-book-spines-replace-value lib same (list yes)))
      (true-same (t3-book-lemmas-true-equality lib same))
      (true-yes (t3-book-lemmas-true-equality lib yes))
      (reverse (proof-proof-symmetric proof true-yes))
      (affirmed (proof-proof-chain proof true-same (list reverse)))
      (premise (proof-proof-reflexive proof inverse-left))
      (shifted-proof (proof-proof-assume proof shifted t))
      (premise (t3-book-spines-replace-value lib premise (list shifted-proof)))
      (first (library-library-linear-equal lib inverse-left a integers))
      (second (library-library-linear-equal lib inverse-right b integers))
      (first (proof-proof-symmetric proof first))
      (derived (proof-proof-chain proof first (list premise second)))
      (denied (proof-proof-assume proof raw nil))
      (impossible (proof-proof-cut proof derived denied))
      (negated (proof-proof-front proof impossible (proof-neg shifted)))
      (nil-negated (t3-book-lemmas-nil-value lib negated))
      (nil-denied (t3-book-lemmas-nil-value lib denied))
      (reverse (proof-proof-symmetric proof nil-denied))
      (rejected (proof-proof-chain proof nil-negated (list reverse))))
     (proof-proof-cases proof raw affirmed rejected))))

(defun t3-book-counterexamples-multiplicities-init (lib)
  (let ((count (list *t3-book-counterexamples-count* *t3-book-permutations-a* *library-x*)))
    (proof-with-checked-results
     ((natural (t3-book-occurrences-natural-count lib count *library-x*)))
     (list :t3-multiplicities lib natural))))

(defun t3-book-counterexamples-multiplicities-lib (counts)
  (cadr counts))

(defun t3-book-counterexamples-multiplicities-natural (counts)
  (caddr counts))

(defun t3-book-counterexamples-multiplicities-natural-at (counts term)
  (proof-with-checked-results
   ((key (proof-term-at term 1))
    (items (proof-term-at term 2)))
   (proof-proof-instantiate
    (library-library-proof (t3-book-counterexamples-multiplicities-lib counts))
    (t3-book-counterexamples-multiplicities-natural counts)
    (list (list *t3-book-permutations-a* key) (list *library-x* items)))))

(defun t3-book-counterexamples-multiplicities-integer-at (counts term)
  (proof-with-checked-results ((natural (t3-book-counterexamples-multiplicities-natural-at counts term)))
    (library-library-cite (t3-book-counterexamples-multiplicities-lib counts)
                          "NATURAL-INTEGER" (list term) (list natural))))

(defun t3-book-counterexamples-multiplicities-zero-inequality (counts comparison)
  (let* ((lib (t3-book-counterexamples-multiplicities-lib counts))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length comparison 3))
      (assume-equal (proof-proof-assume proof comparison t)))
     (let* ((a (cadr parts))
            (b (caddr parts))
            (zero-on-right (equal b *proof-zero*))
            (positive (if zero-on-right a b)))
       (proof-with-checked-results
        ((zeroize (if zero-on-right assume-equal (proof-proof-symmetric proof assume-equal)))
         (term (proof-term-at positive 2))
         (natural (t3-book-counterexamples-multiplicities-natural-at counts term))
         (evidence (t3-logic-evidence-init lib nil (list natural) nil))
         (above-zero (t3-arithmetic-integer-comparison lib *proof-zero* positive evidence))
         (impossible (proof-proof-rewrite proof (car above-zero) zeroize '(1 2)))
         (impossible (t3-logic-libraryproofs-simplify-first lib impossible nil nil))
         (denied (proof-proof-front proof impossible (proof-neg comparison))))
        (t3-book-lemmas-nil-value lib denied))))))

(defun t3-book-counterexamples-counterexample-count-equation (witness equations lib right)
  (proof-with-checked-results
   ((equation (proof-proof-reflexive (library-library-proof lib) right))
    (equation (t3-book-spines-replace-value lib equation (list witness))))
   (t3-book-spines-replace-value lib equation equations)))

(defun t3-book-counterexamples-counterexample-base (holds lib perm left search right counts)
  (let* ((proof (library-library-proof lib))
         (atom-proof (t3-book-permutations-permutations-atom perm))
         (key (list *library-car* *library-y*)))
    (proof-with-checked-results
     ((y-kind (proof-proof-assume proof (list *proof-consp* *library-y*) holds))
      (p (t3-book-permutations-permutations-open-perm perm left atom-proof))
      (form (t3-book-spines-constructor-form lib (caddr (proof-step-first p))
                                             (list y-kind) *t3-book-spines-guards*))
      (p (proof-proof-chain proof p (list form)))
      (witness (t3-book-spines-shallow lib search (list atom-proof)))
      (x-count (t3-book-spines-shallow lib
                                       (list *t3-book-counterexamples-count* key *library-x*)
                                       (list atom-proof)))
      (y-count (t3-book-spines-shallow lib
                                       (list *t3-book-counterexamples-count* key *library-y*)
                                       (list y-kind)))
      (compared (t3-book-counterexamples-counterexample-count-equation
                  witness (list x-count y-count) lib right))
      (value (if holds
                 (t3-book-counterexamples-multiplicities-zero-inequality
                  counts (caddr (proof-step-first compared)))
               (t3-logic-libraryproofs-constant lib (caddr (proof-step-first compared)))))
      (equality (proof-proof-chain proof compared (list value)))
      (reverse (proof-proof-symmetric proof equality)))
     (proof-proof-chain proof p (list reverse)))))

(defun t3-book-counterexamples-counterexample-selection (branch lib opened)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((selected (proof-proof-select proof (caddr (proof-step-first opened)) branch)))
     (proof-proof-chain proof opened (list selected)))))

(defun t3-book-counterexamples-counterexample-missing
    (lib counts head search right cons-proof missing opened)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((witness (t3-book-spines-shallow lib search (list cons-proof missing)))
      (absent (proof-proof-fact
               proof (proof-sym "NOT-MEMB-IMPLIES-HOW-MANY-IS-0" "ACL2")
               (list (list *t3-book-permutations-a* head) (list *library-x* *library-y*))))
      (zero (proof-proof-modus-ponens proof absent missing))
      (x-count (t3-book-spines-shallow lib
                                       (list *t3-book-counterexamples-count* head *library-x*)
                                       (list cons-proof)))
      (compared (t3-book-counterexamples-counterexample-count-equation
                  witness (list x-count zero) lib right))
      (different (t3-book-counterexamples-multiplicities-zero-inequality
                  counts (caddr (proof-step-first compared))))
      (unequal (proof-proof-chain proof compared (list different)))
      (selected (t3-book-counterexamples-counterexample-selection missing lib opened))
      (reverse (proof-proof-symmetric proof unequal)))
     (proof-proof-chain proof selected (list reverse)))))

(defun t3-book-counterexamples-counterexample-advance-count
    (lib actual match eq-y smaller-y original-y counts)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((reverse (proof-proof-symmetric proof match))
      (occurs (proof-proof-rewrite proof actual reverse '(1 1)))
      (occurs (proof-proof-tidy proof occurs))
      (form (t3-book-spines-constructor-form
             lib (caddr (proof-step-first eq-y)) (list match occurs) *t3-book-spines-guards*))
      (eq-y (proof-proof-chain proof eq-y (list form)))
      (advanced (proof-proof-reflexive proof (library-plus *proof-one* smaller-y)))
      (eq-y (t3-book-spines-replace-value lib advanced (list eq-y)))
      (typed (t3-book-counterexamples-multiplicities-integer-at counts original-y))
      (cancel (library-library-linear-equal lib (caddr (proof-step-first eq-y))
                                             original-y (list typed))))
     (proof-proof-chain proof eq-y (list cancel)))))

(defun t3-book-counterexamples-counterexample-advance
    (holds lib same key head cons-proof actual counts witness right smaller-x smaller-y opened smaller)
  (let* ((proof (library-library-proof lib))
         (original-y (list *t3-book-counterexamples-count* key *library-y*)))
    (proof-with-checked-results
     ((match (proof-proof-assume proof same holds))
      (eq-x (t3-book-spines-shallow lib (list *t3-book-counterexamples-count* key *library-x*)
                                    (list cons-proof match)))
      (law (if holds "HOW-MANY-RM-GENERAL" "HOW-MANY-RM"))
      (eq-y (proof-proof-fact
             proof (proof-sym law "ACL2")
             (list (list *t3-book-permutations-a* key) (list *t3-book-permutations-b* head)
                   (list *library-x* *library-y*))))
      (eq-y (if holds
                (t3-book-counterexamples-counterexample-advance-count
                 lib actual match eq-y smaller-y original-y counts)
              (proof-proof-modus-ponens proof eq-y match)))
      (reverse (proof-proof-symmetric proof eq-y))
      (rhs (t3-book-counterexamples-counterexample-count-equation
             witness (list eq-x reverse) lib right))
      (rhs
       (if holds
           (proof-with-checked-results
            ((x-type (t3-book-counterexamples-multiplicities-integer-at counts smaller-x))
             (y-type (t3-book-counterexamples-multiplicities-integer-at counts smaller-y))
             (shifted (t3-book-counterexamples-equal-successors
                       lib smaller-x smaller-y (list x-type y-type))))
            (proof-proof-chain proof rhs (list shifted)))
         rhs))
      (selected (t3-book-counterexamples-counterexample-selection actual lib opened))
      (reverse (proof-proof-symmetric proof rhs)))
     (proof-proof-chain proof selected (list smaller reverse)))))

(defun t3-book-counterexamples-counterexample (lib name formula)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (search (list *t3-book-counterexamples-find* x y))
         (cons-test (list *proof-consp* y)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (perm (t3-book-permutations-permutations-init lib))
      (counts (t3-book-counterexamples-multiplicities-init lib))
      (sides (proof-list-of-length (cdr (caddr parts)) 2))
      (left (car sides))
      (right (cadr sides))
      (assumption (proof-proof-assume proof (cadr parts) t))
      (proper-types (proof-proof-conjunct proof assumption))
      (proper-x (car proper-types))
      (proper-y (cadr proper-types))
      (head (t3-book-permutations-permutations-head perm))
      (tail (t3-book-permutations-permutations-tail perm))
      (rest (t3-book-permutations-permutations-after-y perm))
      (yes (t3-book-counterexamples-counterexample-base t lib perm left search right counts))
      (no (t3-book-counterexamples-counterexample-base nil lib perm left search right counts))
      (empty-x (proof-proof-cases proof cons-test yes no))
      (present (list *t3-book-permutations-member* head y))
      (actual (proof-proof-assume proof present t))
      (missing (proof-proof-assume proof present nil))
      (cons-proof (t3-book-permutations-permutations-cons perm))
      (opened (t3-book-permutations-permutations-open-perm perm left cons-proof))
      (no-head (t3-book-counterexamples-counterexample-missing
                lib counts head search right cons-proof missing opened))
      (pairs (list (list x tail) (list y rest)))
      (hypothesis (t3-book-permutations-permutations-hypothesis perm formula pairs))
      (tail-type (t3-book-spines-shallow lib (proof-step-first proper-x) (list cons-proof)))
      (tail-proper (proof-proof-rewrite proof proper-x tail-type '(1)))
      (tail-proper (proof-proof-tidy proof tail-proper))
      (remove-proper (proof-proof-fact proof (proof-sym "TRUE-LISTP-RM" "ACL2")
                                       (list (list *t3-book-permutations-a* head) (list x y))))
      (rest-proper (proof-proof-modus-ponens proof remove-proper proper-y))
      (both (t3-book-permutations-conjunction lib tail-proper rest-proper))
      (smaller (proof-proof-modus-ponens proof hypothesis both))
      (witness (t3-book-spines-shallow lib search (list cons-proof actual)))
      (key (list *t3-book-counterexamples-find* tail rest))
      (same (proof-eq key head))
      (smaller-x (list *t3-book-counterexamples-count* key tail))
      (smaller-y (list *t3-book-counterexamples-count* key rest))
      (yes (t3-book-counterexamples-counterexample-advance
            t lib same key head cons-proof actual counts witness right
            smaller-x smaller-y opened smaller))
      (no (t3-book-counterexamples-counterexample-advance
           nil lib same key head cons-proof actual counts witness right
           smaller-x smaller-y opened smaller))
      (present-head (proof-proof-cases proof same yes no))
      (step (proof-proof-cases proof present present-head no-head))
      (step (t3-book-permutations-permutations-induct perm formula pairs step empty-x)))
     (proof-proof-entry "theorem" name (list name) (list step)))))

(defun t3-book-counterexamples-perm-fixed-facts (x y z lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((equivalence (proof-proof-fact proof *t3-book-permutations-theorem*
                                      (list (list *library-x* x) (list *library-y* y)
                                            (list *library-z* z))))
      (typed (proof-proof-conjunct proof equivalence))
      (other (proof-proof-conjunct proof (cadr typed)))
      (other (proof-proof-conjunct proof (cadr other))))
     (list (car typed) (car other) (cadr other)))))

(defun t3-book-counterexamples-perm-fixed-symmetry (premise lib)
  (proof-with-checked-results
   ((term (proof-step-first premise))
    (parts (proof-list-of-length term 3))
    (facts (t3-book-counterexamples-perm-fixed-facts (cadr parts) (caddr parts) *library-z* lib)))
   (proof-proof-modus-ponens (library-library-proof lib) (cadr facts) premise)))

(defun t3-book-counterexamples-perm-fixed-transitive (before after lib)
  (proof-with-checked-results
   ((before-first (proof-step-first before))
    (before-parts (proof-list-of-length before-first 3))
    (after-first (proof-step-first after))
    (after-parts (proof-list-of-length after-first 3))
    (facts (t3-book-counterexamples-perm-fixed-facts
            (cadr before-parts) (caddr before-parts) (caddr after-parts) lib))
    (both (t3-book-permutations-conjunction lib before after)))
   (proof-proof-modus-ponens (library-library-proof lib) (caddr facts) both)))

(defun t3-book-counterexamples-perm-fixed (lib fixed-x fixed-y)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (z *library-z*)
         (low (list *t3-book-permutations-perm* fixed-x fixed-y))
         (high (list *t3-book-permutations-perm* x y))
         (fix-law (proof-sym "PERM-TLFIX" "ACL2")))
    (proof-with-checked-results
     ((xfix (proof-proof-fact proof fix-law (list (list x x))))
      (yfix (proof-proof-fact proof fix-law (list (list x y))))
      (given (proof-proof-assume proof low t))
      (reverse (t3-book-counterexamples-perm-fixed-symmetry xfix lib))
      (actual (t3-book-counterexamples-perm-fixed-transitive reverse given lib))
      (actual (t3-book-counterexamples-perm-fixed-transitive actual yfix lib))
      (facts (t3-book-counterexamples-perm-fixed-facts fixed-x fixed-y z lib))
      (a (library-library-cite lib "T3-BOOLEAN-TRUE" (list low) (list (car facts) given)))
      (facts (t3-book-counterexamples-perm-fixed-facts x y z lib))
      (b (library-library-cite lib "T3-BOOLEAN-TRUE" (list high) (list (car facts) actual)))
      (b (proof-proof-symmetric proof b))
      (yes (proof-proof-chain proof a (list b)))
      (denied (proof-proof-assume proof low nil))
      (other (proof-proof-assume proof high t))
      (converse (t3-book-counterexamples-perm-fixed-transitive xfix other lib))
      (reverse (t3-book-counterexamples-perm-fixed-symmetry yfix lib))
      (converse (t3-book-counterexamples-perm-fixed-transitive converse reverse lib))
      (cut (proof-proof-cut proof converse denied))
      (negative (proof-proof-front proof cut (proof-neg high)))
      (nil-denied (t3-book-lemmas-nil-value lib denied))
      (nil-negative (t3-book-lemmas-nil-value lib negative))
      (reverse (proof-proof-symmetric proof nil-negative))
      (no (proof-proof-chain proof nil-denied (list reverse))))
     (proof-proof-cases proof low yes no))))

(defun t3-book-counterexamples-convert-proper-replies (n lib formula replies result)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (t3-book-spines-callback-p result)) result)
   ((zp n) '(:failure "Fuel" "t3-book-counterexamples-convert-proper-replies"))
   (t
    (let* ((args (t3-book-spines-callback-args result))
           (answer (if (eq (proof-proof-kind (library-library-proof lib)) :t3-book)
                       (t3-book-values-book-proofs-prove
                        (t3-book-values-make-book-proofs lib nil nil) (car args) (cadr args) nil)
                     (t3-logic-libraryproofs-prove lib (car args) (cadr args) nil)))
           (replies (append replies (list answer))))
      (t3-book-counterexamples-convert-proper-replies
       (1- n) lib formula replies (t3-book-spines-mapped-list lib formula replies))))))

(defun t3-book-counterexamples-convert-proper (fixed lib)
  (let ((formula (list *t3-book-lemmas-true-listp* fixed)))
    (t3-book-counterexamples-convert-proper-replies
     1000000 lib formula nil (t3-book-spines-mapped-list lib formula nil))))

(defun t3-book-counterexamples-convert-count (proof step variable)
  (proof-with-checked-results
   ((count (proof-proof-fact
            proof (proof-sym "HOW-MANY-TLFIX" "ACL2")
            (list (list *t3-book-permutations-a*
                        (list *t3-book-counterexamples-find* *library-x* *library-y*))
                  (list *library-x* variable)))))
   (proof-proof-rewrite-first proof step count)))

(defun t3-book-counterexamples-convert (lib name formula)
  (declare (ignore formula))
  (let* ((proof (library-library-proof lib))
         (fixed-x (list *t3-book-counterexamples-fix* *library-x*))
         (fixed-y (list *t3-book-counterexamples-fix* *library-y*)))
    (proof-with-checked-results
     ((earlier (proof-proof-fact proof *t3-book-counterexamples-checked-count*
                                 (list (list *library-x* fixed-x) (list *library-y* fixed-y))))
      (proper-x (t3-book-counterexamples-convert-proper fixed-x lib))
      (proper-y (t3-book-counterexamples-convert-proper fixed-y lib))
      (proper (t3-book-permutations-conjunction lib proper-x proper-y))
      (step (proof-proof-modus-ponens proof earlier proper))
      (key-x (proof-proof-fact proof (proof-sym "PERM-COUNTER-EXAMPLE-TLFIX-1" "ACL2")
                                (list (list *library-y* fixed-y))))
      (key-y (proof-proof-fact proof (proof-sym "PERM-COUNTER-EXAMPLE-TLFIX-2" "ACL2") nil))
      (key (proof-proof-chain proof key-x (list key-y)))
      (step (proof-proof-rewrite-first proof step key))
      (step (t3-book-counterexamples-convert-count proof step *library-x*))
      (step (t3-book-counterexamples-convert-count proof step *library-y*))
      (fixed (t3-book-counterexamples-perm-fixed lib fixed-x fixed-y))
      (step (proof-proof-rewrite-first proof step fixed)))
     (proof-proof-entry "theorem" name (list name) (list step)))))
