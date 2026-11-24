(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h4-book-hanoi-hanoi (name)
  (proof-sym name "HANOI"))

(defconst *h4-book-hanoi-app* (h4-book-hanoi-hanoi "APP"))
(defconst *h4-book-hanoi-get* (h4-book-hanoi-hanoi "GET"))
(defconst *h4-book-hanoi-put* (h4-book-hanoi-hanoi "PUT"))
(defconst *h4-book-hanoi-tower* (h4-book-hanoi-hanoi "TOWER"))
(defconst *h4-book-hanoi-h* (h4-book-hanoi-hanoi "H"))
(defconst *h4-book-hanoi-play* (h4-book-hanoi-hanoi "PLAY"))
(defconst *h4-book-hanoi-perm* (h4-book-hanoi-hanoi "PERM"))
(defconst *h4-book-hanoi-mem* (h4-book-hanoi-hanoi "MEM"))
(defconst *h4-book-hanoi-big-tops* (h4-book-hanoi-hanoi "BIG-TOPS"))
(defconst *h4-book-hanoi-legal* (h4-book-hanoi-hanoi "LEGAL-MOVEP"))
(defconst *h4-book-hanoi-syntax* (h4-book-hanoi-hanoi "LEGAL-SYNTAXP"))
(defconst *h4-book-hanoi-move* (h4-book-hanoi-hanoi "DO-MOVE"))
(defconst *h4-book-hanoi-endp* (proof-cl "ENDP"))
(defconst *h4-book-hanoi-last-slot* (proof-quote 2))
(defconst *h4-book-hanoi-slot-count* (proof-quote 3))
(defconst *h4-book-hanoi-slots* (proof-quote '(0 1 2)))

(defun h4-book-hanoi-cons-list (items)
  (if (endp items)
      *proof-false*
    (list *proof-cons* (car items) (h4-book-hanoi-cons-list (cdr items)))))

(defun h4-book-hanoi-first-at (step index)
  (if (null step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun h4-book-hanoi-evidence-get (evidence key)
  (let ((entry (assoc-equal key evidence)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h4-book-hanoi-evidence-steps (evidence tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
     ((step (h4-book-hanoi-evidence-get evidence (car tests)))
      (rest (h4-book-hanoi-evidence-steps evidence (cdr tests))))
     (cons step rest))))

(defun h4-book-hanoi-step-evidence (steps evidence)
  (if (endp steps)
      evidence
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (h4-book-hanoi-step-evidence (cdr steps) (table-put evidence literal (car steps))))))

(defun h4-book-hanoi-index-membership-find-point (points excluded p index evidence goal integral)
  (let ((proof (library-library-proof p)))
    (if (endp points)
        (proof-with-checked-results
         ((lower (h4-book-hanoi-evidence-get evidence (proof-neg (library-lt index *proof-zero*))))
          (upper (h4-book-hanoi-evidence-get evidence (proof-neg (library-lt *h4-book-hanoi-last-slot* index))))
          (impossible (h4-book-finite-proposition-from-interval p index 0 2 integral lower upper excluded)))
         (proof-proof-subsume proof impossible (cons goal (proof-step-clause impossible))))
      (let ((test (proof-eq index (proof-quote (car points)))))
        (proof-with-checked-results
         ((yes (proof-proof-assume proof test t))
          (yes (h4-tactics-tactics-establish p goal nil (list *h4-book-hanoi-mem*) (list yes) nil))
          (no (proof-proof-assume proof test nil))
          (no (h4-book-hanoi-index-membership-find-point
               (cdr points) (append excluded (list no)) p index evidence goal integral)))
         (h4-tactics-tactics-case-of p goal test yes no))))))

(defun h4-book-hanoi-index-membership (p index evidence)
  (let ((goal (list *h4-book-hanoi-mem* index *h4-book-hanoi-slots*)))
    (proof-with-checked-results
     ((integral (h4-book-hanoi-evidence-get evidence (library-integer index))))
     (h4-book-hanoi-index-membership-find-point
      (cadr *h4-book-hanoi-slots*) nil p index evidence goal integral))))

(defun h4-book-hanoi-top-bound (size stack)
  (let ((empty (list *h4-book-hanoi-endp* stack)))
    (proof-ite empty empty (library-lt size (list *library-car* stack)))))

(defun h4-book-hanoi-bound-under-step-branch (shape p bound decrease transitive small large goal)
  (let ((proof (library-library-proof p))
        (logic *h4-book-flatten-logic*))
    (proof-with-checked-results
     ((wanted (h4-tactics-tactics-normalize p goal (list shape) logic nil nil))
      (shape-literal (proof-step-first shape))
      (result
       (if (proof-is-call shape-literal *proof-consp*)
           (proof-with-checked-results
            ((literal (proof-step-first bound))
             (before (h4-tactics-tactics-normalize p literal (list shape) logic nil nil))
             (above (proof-proof-rewrite proof bound before '(1)))
             (rhs (h4-book-hanoi-first-at before 2))
             (operands (proof-list-of-length (cdr rhs) 2))
             (law (proof-proof-instantiate
                   proof transitive (list (list *library-x* small) (list *library-y* large)
                                          (list *library-z* (cadr operands)))))
             (premise (h4-book-division-conjunction p (list decrease above))))
            (h4-tactics-tactics-modus-ponens p law premise))
         (proof-with-checked-results ((rhs (h4-book-hanoi-first-at wanted 2)))
           (h4-tactics-tactics-establish p rhs (list shape) logic nil nil)))))
     (proof-proof-transport proof result wanted))))

(defun h4-book-hanoi-bound-under-step (p bound decrease transitive)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((literal (proof-step-first decrease))
      (operands (proof-list-of-length (cdr literal) 2))
      (small (car operands))
      (large (cadr operands))
      (empty (h4-book-hanoi-first-at bound 1))
      (stack (proof-term-at empty 1))
      (goal (h4-book-hanoi-top-bound small stack))
      (test (list *proof-consp* stack))
      (yes (proof-proof-assume proof test t))
      (yes (h4-book-hanoi-bound-under-step-branch yes p bound decrease transitive small large goal))
      (no (proof-proof-assume proof test nil))
      (no (h4-book-hanoi-bound-under-step-branch no p bound decrease transitive small large goal)))
     (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-hanoi-transfer-state-p (self) (nth 1 self))
(defun h4-book-hanoi-transfer-state-natural (self) (nth 2 self))
(defun h4-book-hanoi-transfer-state-true-list (self) (nth 3 self))
(defun h4-book-hanoi-transfer-state-length (self) (nth 4 self))
(defun h4-book-hanoi-transfer-state-permutation (self) (nth 5 self))
(defun h4-book-hanoi-transfer-state-slots (self) (nth 6 self))
(defun h4-book-hanoi-transfer-state-size (self) (nth 7 self))
(defun h4-book-hanoi-transfer-state-base (self) (nth 8 self))
(defun h4-book-hanoi-transfer-state-top-bounds (self) (nth 9 self))
(defun h4-book-hanoi-transfer-state-evidence (self) (nth 10 self))
(defun h4-book-hanoi-transfer-state-indexed (self) (nth 11 self))
(defun h4-book-hanoi-transfer-state-constructors (self) (nth 12 self))

(defun h4-book-hanoi-slot-bounds (slots bounds result)
  (if (or (endp slots) (endp bounds))
      result
    (h4-book-hanoi-slot-bounds (cdr slots) (cdr bounds)
                              (table-put result (car slots) (car bounds)))))

(defun h4-book-hanoi-reflected-tests (p tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
     ((term (h4-book-hanoi-first-at (car tests) 1))
      (reflection (if (proof-is-call term *proof-equal*)
                      (h4-book-order-reflected-test p (car tests))
                    nil))
      (rest (h4-book-hanoi-reflected-tests p (cdr tests))))
     (if reflection (cons reflection rest) rest))))

(defun h4-book-hanoi-transfer-slot-evidence (p slots length last count below-count evidence)
  (if (endp slots)
      evidence
    (let ((slot (car slots))
          (proof (library-library-proof p)))
      (proof-with-checked-results
       ((integral (h4-book-hanoi-evidence-get evidence (library-integer slot)))
        (lower (h4-book-hanoi-evidence-get evidence (proof-neg (library-lt slot *proof-zero*))))
        (upper (h4-book-hanoi-evidence-get evidence (proof-neg (library-lt *h4-book-hanoi-last-slot* slot))))
        (natural (library-library-cite p "NATURAL-FROM-BOUNDS" (list slot) (list integral lower)))
        (bounded (library-library-cite p "WEAK-THEN-LESS"
                                       (list slot *h4-book-hanoi-last-slot* *h4-book-hanoi-slot-count*)
                                       (list integral last count upper below-count)))
        (reverse-length (proof-proof-symmetric proof length))
        (bounded (proof-proof-rewrite proof bounded reverse-length '(1 2)))
        (evidence (h4-book-hanoi-step-evidence (list natural bounded) evidence)))
       (h4-book-hanoi-transfer-slot-evidence p (cdr slots) length last count below-count evidence)))))

(defun h4-book-hanoi-transfer-state-init (p premise)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((assumption (proof-proof-assume proof premise t))
      (conjuncts (h4-book-list-types-conjunct-proofs p assumption))
      (conjuncts (proof-list-of-length conjuncts 5))
      (natural (car conjuncts))
      (true-list (cadr conjuncts))
      (length (caddr conjuncts))
      (permutation (cadddr conjuncts))
      (big (nth 4 conjuncts))
      (literal (proof-step-first big))
      (slots (seq-slice literal 1 4))
      (size (proof-term-at literal 4))
      (base (proof-term-at literal 5))
      (opened (proof-proof-unfold proof literal))
      (bounds (proof-proof-rewrite proof big opened '(1)))
      (bounds (h4-book-list-types-conjunct-proofs p bounds))
      (top-bounds (h4-book-hanoi-slot-bounds slots bounds nil))
      (permutation-term (proof-step-first permutation))
      (condition (h4-book-state-equation-instance p (h4-book-hanoi-hanoi "PERM-OPENER") permutation-term nil))
      (perm-tests (proof-proof-rewrite proof permutation condition '(1)))
      (perm-tests (h4-book-list-types-conjunct-proofs p perm-tests))
      (reflections (h4-book-hanoi-reflected-tests p perm-tests))
      (evidence (h4-book-hanoi-step-evidence (append perm-tests reflections) nil))
      (last (library-library-type-of p *h4-book-hanoi-last-slot* nil))
      (count (library-library-type-of p *h4-book-hanoi-slot-count* nil))
      (below-count (h4-tactics-tactics-establish
                    p (library-lt *h4-book-hanoi-last-slot* *h4-book-hanoi-slot-count*) nil nil nil nil))
      (evidence (h4-book-hanoi-transfer-slot-evidence p slots length last count below-count evidence))
      (laws (list (h4-book-hanoi-hanoi "GET-PUT") (h4-book-hanoi-hanoi "PUT-PUT-2")
                  (h4-book-hanoi-hanoi "PUT-PUT-1") (h4-book-hanoi-hanoi "PUT-GET")))
      (indexed (h4-book-state-indexed-state-init p *h4-book-hanoi-get* *h4-book-hanoi-put* laws evidence))
      (constructors (h4-book-finite-constructor-test p)))
     (list :h4-transfer-state p natural true-list length permutation slots size base
           top-bounds evidence indexed constructors))))

(defun h4-book-hanoi-transfer-state-reduce (self term)
  (let ((p (h4-book-hanoi-transfer-state-p self)))
    (proof-with-checked-results
     ((equation (h4-book-finite-reduction-provider-provide
                 term p (h4-book-hanoi-transfer-state-constructors self)))
      (equation (or equation (h4-book-state-indexed-state-reduce
                              (h4-book-hanoi-transfer-state-indexed self) term))))
     (if (or equation (not (proof-is-call term *h4-book-hanoi-app*)))
         equation
       (proof-with-checked-results ((sequence (proof-term-at term 1)))
         (and (or (equal sequence *proof-false*) (proof-is-call sequence *proof-cons*))
           (h4-book-flatten-unfold-on-list p term sequence nil)))))))

(defun h4-book-hanoi-transfer-state-normalize-turn (self term evidence expand rewrites replies)
  (let ((result (h4-tactics-tactics-normalize
                 (h4-book-hanoi-transfer-state-p self) term evidence expand rewrites
                 (cons :h4-tactics-provider replies))))
    (if (h4-tactics-request-p result)
        (let ((requested (h4-tactics-request-term result)))
          (proof-with-checked-results
           ((reply (h4-book-hanoi-transfer-state-reduce self requested)))
           (cons :h4-hanoi-normalization-replies (table-put replies requested reply))))
      result)))

(defun h4-book-hanoi-transfer-state-normalize-loop (n result self term evidence expand rewrites)
  (declare (xargs :measure (nfix n)))
  (cond ((not (eq (car result) :h4-hanoi-normalization-replies)) result)
        ((zp n) '(:failure "Fuel" "h4-book-hanoi-transfer-state-normalize-loop"))
        (t (h4-book-hanoi-transfer-state-normalize-loop
            (1- n) (h4-book-hanoi-transfer-state-normalize-turn self term evidence expand rewrites (cdr result))
            self term evidence expand rewrites))))

(defun h4-book-hanoi-transfer-state-normalize (n self term evidence expand rewrites replies)
  (if (zp n)
      '(:failure "Fuel" "h4-book-hanoi-transfer-state-normalize")
    (h4-book-hanoi-transfer-state-normalize-loop
     (1- n) (h4-book-hanoi-transfer-state-normalize-turn self term evidence expand rewrites replies)
     self term evidence expand rewrites)))

(defun h4-book-hanoi-transfer-state-stack (self index)
  (list *h4-book-hanoi-get* index (h4-book-hanoi-transfer-state-base self)))

(defun h4-book-hanoi-transfer-state-permutation-given (self order)
  (let* ((p (h4-book-hanoi-transfer-state-p self))
         (proof (library-library-proof p))
         (term (list *h4-book-hanoi-perm* (h4-book-hanoi-cons-list order) *h4-book-hanoi-slots*)))
    (proof-with-checked-results
     ((equation (h4-book-state-equation-instance p (h4-book-hanoi-hanoi "PERM-OPENER") term nil))
      (body (h4-book-hanoi-first-at equation 2))
      (tests (h4-book-list-types-conjuncts body))
      (evidence (h4-book-hanoi-evidence-steps (h4-book-hanoi-transfer-state-evidence self) tests))
      (premise (h4-book-division-conjunction p evidence)))
     (proof-proof-transport proof premise equation))))

(defun h4-book-hanoi-transfer-state-amended (self slot)
  (list *h4-book-hanoi-put*
        (list *proof-cons* (h4-book-hanoi-transfer-state-size self)
              (h4-book-hanoi-transfer-state-stack self slot))
        slot (h4-book-hanoi-transfer-state-base self)))

(defun h4-book-hanoi-transfer-smaller-bounds (p slots top-bounds decrease transitive result)
  (if (endp slots)
      result
    (let ((slot (car slots)))
      (proof-with-checked-results
       ((bound (h4-book-hanoi-evidence-get top-bounds slot))
        (new-bound (h4-book-hanoi-bound-under-step p bound decrease transitive)))
       (h4-book-hanoi-transfer-smaller-bounds
        p (cdr slots) top-bounds decrease transitive (table-put result slot new-bound))))))

(defun h4-book-hanoi-transfer-state-smaller-tops (self decrease)
  (let* ((p (h4-book-hanoi-transfer-state-p self))
         (proof (library-library-proof p))
         (guard (proof-ite (library-lt *library-x* *library-y*)
                           (library-lt *library-y* *library-z*) *proof-false*))
         (formula (list *library-implies* guard (library-lt *library-x* *library-z*))))
    (proof-with-checked-results
     ((assumption (proof-proof-assume proof guard t))
      (conjuncts (h4-tactics-tactics-conjunct p assumption))
      (strict (h4-book-order-primitive-transitive p (car conjuncts) (cadr conjuncts)))
      (transitive (h4-tactics-tactics-imply p formula strict)))
     (h4-book-hanoi-transfer-smaller-bounds
      p (h4-book-hanoi-transfer-state-slots self) (h4-book-hanoi-transfer-state-top-bounds self)
      decrease transitive nil))))

(defun h4-book-hanoi-transfer-amended-bound (self slot written small decrease smaller-tops)
  (let* ((p (h4-book-hanoi-transfer-state-p self))
         (proof (library-library-proof p))
         (observed-term (list *h4-book-hanoi-get* slot written))
         (bound (h4-book-hanoi-top-bound small observed-term)))
    (proof-with-checked-results
     ((observed (h4-book-state-indexed-state-reduce (h4-book-hanoi-transfer-state-indexed self) observed-term))
      (identity (proof-proof-reflexive proof bound))
      (observed-lhs (h4-book-hanoi-first-at observed 1))
      (simplified (proof-proof-rewrite-result proof identity observed (proof-eq *proof-result* bound) observed-lhs))
      (written-slot (proof-term-at written 2)))
     (if (equal slot written-slot)
         (proof-with-checked-results
          ((rhs (h4-book-hanoi-first-at simplified 2))
           (reduced (h4-tactics-tactics-normalize
                     p rhs nil *h4-book-flatten-logic* nil
                     (h4-tactics-constructor-provider (h4-book-hanoi-transfer-state-constructors self))))
           (equality (proof-proof-chain proof simplified (list reduced))))
          (proof-proof-transport proof decrease equality))
       (proof-with-checked-results ((original (h4-book-hanoi-evidence-get smaller-tops slot)))
         (proof-proof-transport proof original simplified))))))

(defun h4-book-hanoi-transfer-amended-bounds (self order written small decrease smaller-tops)
  (if (endp order)
      nil
    (proof-with-checked-results
     ((bound (h4-book-hanoi-transfer-amended-bound self (car order) written small decrease smaller-tops))
      (rest (h4-book-hanoi-transfer-amended-bounds self (cdr order) written small decrease smaller-tops)))
     (cons bound rest))))

(defun h4-book-hanoi-transfer-state-amended-guards (self order written smaller-nat decrease smaller-tops)
  (let* ((p (h4-book-hanoi-transfer-state-p self))
         (proof (library-library-proof p))
         (indexed (h4-book-hanoi-transfer-state-indexed self)))
    (proof-with-checked-results
     ((true-list (h4-book-state-indexed-state-invariant-equation
                  indexed (h4-book-hanoi-hanoi "TRUE-LISTP-PUT") *h4-book-updates-true-list* written))
      (state-type (proof-proof-transport proof (h4-book-hanoi-transfer-state-true-list self) true-list))
      (length (h4-book-state-indexed-state-invariant-equation
               indexed (h4-book-hanoi-hanoi "LEN-PUT") *library-len* written))
      (state-length (proof-proof-chain proof length (list (h4-book-hanoi-transfer-state-length self))))
      (small (h4-book-hanoi-first-at smaller-nat 1))
      (big (proof-proof-unfold proof (cons *h4-book-hanoi-big-tops* (append order (list small written)))))
      (bounds (h4-book-hanoi-transfer-amended-bounds self order written small decrease smaller-tops))
      (tops (h4-book-division-conjunction p bounds))
      (tops (proof-proof-transport proof tops big))
      (permutation (h4-book-hanoi-transfer-state-permutation-given self order)))
     (h4-book-division-conjunction p (list smaller-nat state-type state-length permutation tops)))))

(defun h4-book-hanoi-transfer-state-move-fields (self move source destination)
  (let* ((p (h4-book-hanoi-transfer-state-p self))
         (a (h4-book-hanoi-hanoi "A"))
         (b (h4-book-hanoi-hanoi "B"))
         (operators (list* a b *h4-book-hanoi-get* *h4-book-arithmetic-zp* *h4-book-flatten-logic*))
         (provider (h4-tactics-constructor-provider (h4-book-hanoi-transfer-state-constructors self))))
    (proof-with-checked-results
     ((a-equation (h4-tactics-tactics-normalize p (list a move) nil operators nil provider))
      (b-equation (h4-tactics-tactics-normalize p (list b move) nil operators nil provider))
      (a-field (h4-book-hanoi-first-at a-equation 2))
      (b-field (h4-book-hanoi-first-at b-equation 2)))
     (if (and (equal a-field source) (equal b-field destination))
         (list a-equation b-equation)
       '(:failure "failure" "")))))

(defun h4-book-hanoi-transfer-state-legal-move-branch (shape self simplified bound access before)
  (let* ((p (h4-book-hanoi-transfer-state-p self))
         (proof (library-library-proof p)))
    (proof-with-checked-results
     ((rhs (h4-book-hanoi-first-at simplified 2))
      (value (h4-book-hanoi-transfer-state-normalize 1000000 self rhs (list shape) nil access nil))
      (literal (proof-step-first bound))
      (normalized (h4-tactics-tactics-normalize p literal (list shape) *h4-book-flatten-logic* nil nil))
      (shape-literal (proof-step-first shape))
      (proved (if (proof-is-call shape-literal *proof-consp*)
                  (proof-proof-rewrite proof bound normalized '(1))
                (proof-proof-prove proof *proof-true* nil nil)))
      (equality (proof-proof-chain proof before (list simplified value))))
     (proof-proof-transport proof proved equality))))

(defun h4-book-hanoi-transfer-state-legal-move (self move written source destination access)
  (let* ((p (h4-book-hanoi-transfer-state-p self))
         (proof (library-library-proof p))
         (evidence (h4-book-hanoi-transfer-state-evidence self))
         (provider (h4-tactics-constructor-provider (h4-book-hanoi-transfer-state-constructors self))))
    (proof-with-checked-results
     ((source-member (h4-book-hanoi-index-membership p source evidence))
      (destination-member (h4-book-hanoi-index-membership p destination evidence))
      (distinct (h4-book-hanoi-evidence-get evidence (proof-neg (proof-eq source destination))))
      (syntax (h4-tactics-tactics-establish
               p (list *h4-book-hanoi-syntax* move) (list source-member destination-member distinct)
               (append *h4-book-flatten-logic*
                       (list *h4-book-hanoi-syntax* *h4-book-updates-true-list* *library-len*))
               access provider))
      (term (list *h4-book-hanoi-legal* move written))
      (before (proof-proof-unfold proof term))
      (rhs (h4-book-hanoi-first-at before 2))
      (simplified (h4-book-hanoi-transfer-state-normalize 1000000 self rhs (list syntax) nil access nil))
      (stack (h4-book-hanoi-transfer-state-stack self destination))
      (bound (h4-book-hanoi-evidence-get (h4-book-hanoi-transfer-state-top-bounds self) destination))
      (test (list *proof-consp* stack))
      (yes (proof-proof-assume proof test t))
      (yes (h4-book-hanoi-transfer-state-legal-move-branch yes self simplified bound access before))
      (no (proof-proof-assume proof test nil))
      (no (h4-book-hanoi-transfer-state-legal-move-branch no self simplified bound access before)))
     (h4-tactics-tactics-case-of p term test yes no))))

(defun h4-book-hanoi-added-tower (p self index tower countdown)
  (let* ((proof (library-library-proof p))
         (stack (h4-book-hanoi-transfer-state-stack self index))
         (term (list *h4-book-hanoi-put* (list *h4-book-hanoi-app* tower stack)
                     index (h4-book-hanoi-transfer-state-base self))))
    (proof-with-checked-results
     ((expanded (h4-tactics-tactics-normalize p term nil nil (list countdown) nil))
      (rhs (h4-book-hanoi-first-at expanded 2))
      (joined (proof-term-at rhs 1))
      (regroup (h4-book-state-equation-instance p (h4-book-hanoi-hanoi "APP-ASSOC") joined nil))
      (reshaped (proof-proof-rewrite proof expanded regroup '(1 2 1)))
      (rhs (h4-book-hanoi-first-at reshaped 2))
      (normalized (h4-book-hanoi-transfer-state-normalize 1000000 self rhs nil nil nil nil)))
     (proof-proof-chain proof reshaped (list normalized)))))

(defun h4-book-hanoi-transfer-substitution (arguments replacements)
  (if (or (endp arguments) (endp replacements))
      nil
    (let ((rest (h4-book-hanoi-transfer-substitution (cdr arguments) (cdr replacements))))
      (if (equal (car arguments) (car replacements))
          rest
        (cons (list (car arguments) (car replacements)) rest)))))

(defun h4-book-hanoi-transfer-bindings (substitution bindings)
  (if (endp substitution)
      bindings
    (h4-book-hanoi-transfer-bindings
     (cdr substitution) (table-put bindings (caar substitution) (cadar substitution)))))

(defun h4-book-hanoi-stack-transfer-empty (test p formula goal self moves full-tower)
  (let ((proof (library-library-proof p))
        (indexed (h4-book-hanoi-transfer-state-indexed self)))
    (proof-with-checked-results
     ((move-result (h4-book-updates-select-result p moves test))
      (tower-result (h4-book-updates-select-result p full-tower test))
      (equality (h4-book-hanoi-transfer-state-normalize
                 1000000 self goal nil (list *h4-book-hanoi-play*) (list move-result tower-result) nil))
      (rhs (h4-book-hanoi-first-at equality 2))
      (sides (proof-list-of-length (cdr rhs) 2))
      (restored-left (h4-book-state-indexed-state-on-write
                      indexed (h4-book-hanoi-hanoi "PUT-GET") (car sides)))
      (restored-right (h4-book-state-indexed-state-on-write
                       indexed (h4-book-hanoi-hanoi "PUT-GET") (cadr sides)))
      (equality (proof-proof-rewrite proof equality restored-left '(1 2 1)))
      (equality (proof-proof-rewrite proof equality restored-right '(1 2 2)))
      (identity (proof-proof-reflexive proof (h4-book-hanoi-transfer-state-base self)))
      (conclusion (proof-proof-transport proof identity equality)))
     (h4-tactics-tactics-imply p formula conclusion))))

(defun h4-book-hanoi-stack-transfer-transfer-recurse
    (order base substitution p formula self decrease smaller-nat bound smaller-tops)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((instance (proof-subst formula (h4-book-hanoi-transfer-bindings substitution nil)))
      (decrease-term (proof-step-first decrease))
      (assumption (proof-proof-assume proof (proof-ite decrease-term instance *proof-true*) t))
      (hypothesis (proof-proof-prove-if proof assumption decrease))
      (guard (h4-book-hanoi-transfer-state-amended-guards self order base smaller-nat bound smaller-tops))
      (equality (h4-tactics-tactics-modus-ponens p hypothesis guard))
      (literal (proof-step-first equality))
      (normalized (h4-book-hanoi-transfer-state-normalize 1000000 self literal nil nil nil nil)))
     (proof-proof-rewrite proof equality normalized '(1)))))

(defun h4-book-hanoi-transfer-finish (p formula goal self move moves full-tower test first second)
  (let* ((proof (library-library-proof p))
         (slots (h4-book-hanoi-transfer-state-slots self))
         (source (car slots))
         (destination (caddr slots))
         (indexed (h4-book-hanoi-transfer-state-indexed self))
         (original (h4-book-hanoi-transfer-state-base self))
         (provider (h4-tactics-constructor-provider (h4-book-hanoi-transfer-state-constructors self))))
    (proof-with-checked-results
     ((opening (h4-book-updates-select-result p moves test))
      (tower (h4-book-updates-select-result p full-tower test))
      (goal-lhs (proof-term-at goal 1))
      (joined (h4-book-flatten-rewrite-argument p goal-lhs 1 opening))
      (joined-rhs (h4-book-hanoi-first-at joined 2))
      (split (h4-book-state-equation-instance p (h4-book-hanoi-hanoi "PLAY-APP") joined-rhs nil))
      (before (proof-proof-chain proof joined (list split)))
      (source-stack (h4-book-hanoi-added-tower p self source full-tower tower))
      (before (proof-proof-rewrite proof before source-stack '(1 2 2 2)))
      (first-transfer (proof-proof-rewrite proof before first '(1 2 2)))
      (intermediate (h4-book-hanoi-first-at first 2))
      (access (h4-book-hanoi-transfer-state-move-fields self move source destination))
      (legal (h4-book-hanoi-transfer-state-legal-move self move intermediate source destination access))
      (first-transfer-rhs (h4-book-hanoi-first-at first-transfer 2))
      (opened (proof-proof-unfold proof first-transfer-rhs))
      (opened-rhs (h4-book-hanoi-first-at opened 2))
      (single (h4-tactics-tactics-normalize p opened-rhs (list legal) nil nil provider))
      (played (proof-proof-chain proof first-transfer (list opened single)))
      (played-rhs (h4-book-hanoi-first-at played 2))
      (updated (proof-term-at played-rhs 2))
      (opened (h4-book-hanoi-transfer-state-normalize
               1000000 self updated nil
               (list *h4-book-hanoi-move* (h4-book-hanoi-hanoi "POP")
                     (h4-book-hanoi-hanoi "PUSH") (h4-book-hanoi-hanoi "TOP"))
               access nil))
      (opened-rhs (h4-book-hanoi-first-at opened 2))
      (pop-source (h4-book-state-indexed-state-restore 1000000 indexed opened-rhs original))
      (pop-rhs (h4-book-hanoi-first-at pop-source 2))
      (reorder (h4-book-state-indexed-state-on-write indexed (h4-book-hanoi-hanoi "PUT-PUT-1") pop-rhs))
      (after-move (proof-proof-chain proof opened (list pop-source reorder)))
      (played (proof-proof-rewrite proof played after-move '(1 2 2)))
      (finished (proof-proof-chain proof played (list second)))
      (destination-stack (h4-book-hanoi-added-tower p self destination full-tower tower))
      (reverse (proof-proof-symmetric proof destination-stack))
      (finished (proof-proof-chain proof finished (list reverse))))
     (h4-tactics-tactics-imply p formula finished))))

(defun h4-book-hanoi-stack-transfer-transfer
    (test p formula goal self smaller move moves full-tower first-order first-base second-order second-base substitutions)
  (let ((proof (library-library-proof p))
        (size (h4-book-hanoi-transfer-state-size self)))
    (proof-with-checked-results
     ((builtin (library-library-builtin p 9 size))
      (decrease (proof-proof-discharge proof builtin test))
      (smaller-nat (proof-proof-use proof *h4-book-updates-predecessor-natural*
                                   (list (list *library-x* size)) (list test)))
      (size-type (library-library-cite p "NATURAL-INTEGER" (list size)
                                       (list (h4-book-hanoi-transfer-state-natural self))))
      (smaller-type (library-library-cite p "NATURAL-INTEGER" (list smaller) (list smaller-nat)))
      (bound (library-library-cite p "SUCCESSOR-LARGER" (list smaller) (list smaller-type)))
      (bound-rhs (h4-book-hanoi-first-at bound 2))
      (size-equality (library-library-linear-equal p bound-rhs size (list size-type smaller-type)))
      (bound (proof-proof-rewrite proof bound size-equality '(1 2)))
      (smaller-tops (h4-book-hanoi-transfer-state-smaller-tops self bound))
      (first (h4-book-hanoi-stack-transfer-transfer-recurse
              first-order first-base (car substitutions) p formula self decrease smaller-nat bound smaller-tops))
      (second (h4-book-hanoi-stack-transfer-transfer-recurse
               second-order second-base (cadr substitutions) p formula self decrease smaller-nat bound smaller-tops)))
     (h4-book-hanoi-transfer-finish p formula goal self move moves full-tower test first second))))

(defun h4-book-hanoi-stack-transfer (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((parts (proof-list-of-length (cdr formula) 2))
      (self (h4-book-hanoi-transfer-state-init p (car parts)))
      (goal (cadr parts))
      (slots (proof-list-of-length (h4-book-hanoi-transfer-state-slots self) 3))
      (source (car slots))
      (spare (cadr slots))
      (destination (caddr slots))
      (size (h4-book-hanoi-transfer-state-size self))
      (sequence (h4-book-hanoi-transfer-state-base self))
      (smaller (h4-book-arithmetic-predecessor size))
      (move (h4-book-hanoi-cons-list (list (proof-quote (h4-book-hanoi-hanoi "MOVE")) source destination)))
      (first-base (h4-book-hanoi-transfer-state-amended self source))
      (second-base (h4-book-hanoi-transfer-state-amended self destination))
      (first-order (list source destination spare))
      (second-order (list spare source destination))
      (arguments (append slots (list size sequence)))
      (substitutions (list (h4-book-hanoi-transfer-substitution arguments (append first-order (list smaller first-base)))
                           (h4-book-hanoi-transfer-substitution arguments (append second-order (list smaller second-base)))))
      (full-tower (list *h4-book-hanoi-tower* size))
      (moves (cons *h4-book-hanoi-h* (append slots (list size))))
      (condition (list *h4-book-arithmetic-zp* size))
      (yes (proof-proof-assume proof condition t))
      (yes (h4-book-hanoi-stack-transfer-empty yes p formula goal self moves full-tower))
      (no (proof-proof-assume proof condition nil))
      (no (h4-book-hanoi-stack-transfer-transfer
           no p formula goal self smaller move moves full-tower first-order first-base second-order second-base substitutions))
      (cases (h4-tactics-tactics-case-of p formula condition yes no))
      (ordinal (library-library-builtin p 1 size)))
     (proof-proof-induct proof ordinal cases formula (list *library-count* size) substitutions))))

(defun h4-book-hanoi-first-implication (instances)
  (and (consp instances)
    (proof-with-checked-results ((literal (proof-step-first (car instances))))
      (if (proof-is-call literal *library-implies*)
          (car instances)
        (h4-book-hanoi-first-implication (cdr instances))))))

(defun h4-book-hanoi-hanoi-corollary-empty (test p formula provider)
  (h4-tactics-tactics-establish
   p formula (list test) (table-keys (proof-proof-definitions (library-library-proof p))) nil provider))

(defun h4-book-hanoi-corollary-guards (guards evaluate size natural)
  (if (endp guards)
      nil
    (proof-with-checked-results
     ((proved (if (equal (car guards) (list *library-natp* size))
                  natural
                (h4-book-evaluation-closed-evaluation-prove evaluate (car guards))))
      (rest (h4-book-hanoi-corollary-guards (cdr guards) evaluate size natural)))
     (cons proved rest))))

(defun h4-book-hanoi-corollary-expansions (names excluded)
  (cond ((endp names) nil)
        ((member-equal (car names) excluded) (h4-book-hanoi-corollary-expansions (cdr names) excluded))
        (t (cons (car names) (h4-book-hanoi-corollary-expansions (cdr names) excluded)))))

(defun h4-book-hanoi-hanoi-corollary-transfer (test p formula size lemma evaluate provider)
  (let ((proof (library-library-proof p))
        (bindings (list (list *library-x* size))))
    (proof-with-checked-results
     ((integer-size (proof-proof-use proof (proof-sym "H4-COUNTDOWN-INTEGER" "ACL2") bindings (list test)))
      (positive (proof-proof-use proof (proof-sym "H4-COUNTDOWN-POSITIVE" "ACL2") bindings (list test)))
      (nonnegative (library-library-cite p "POSITIVE-NONNEGATIVE" (list size) (list integer-size positive)))
      (natural (library-library-cite p "NATURAL-FROM-BOUNDS" (list size) (list integer-size nonnegative)))
      (premise (h4-book-hanoi-first-at lemma 1))
      (guards (h4-book-list-types-conjuncts premise))
      (guards (h4-book-hanoi-corollary-guards guards evaluate size natural))
      (conjoined (h4-book-division-conjunction p guards))
      (result (h4-tactics-tactics-modus-ponens p lemma conjoined))
      (tower (list *h4-book-hanoi-tower* size))
      (proper (proof-proof-fact proof (h4-book-hanoi-hanoi "TRUE-LISTP-TOWER")
                                (list (list (h4-book-hanoi-hanoi "N") size))))
      (right-identity (proof-proof-fact proof (h4-book-hanoi-hanoi "APP-RIGHT-ID")
                                        (list (list (h4-book-hanoi-hanoi "X") tower))))
      (identity (h4-tactics-tactics-modus-ponens p right-identity proper))
      (expand (h4-book-hanoi-corollary-expansions
               (table-keys (proof-proof-definitions proof))
               (list *h4-book-hanoi-app* *h4-book-hanoi-h* *h4-book-hanoi-play* *h4-book-hanoi-tower*)))
      (literal (proof-step-first result))
      (before (h4-tactics-tactics-normalize p literal nil expand (list identity) provider))
      (after (h4-tactics-tactics-normalize p formula nil expand nil provider))
      (rewritten (proof-proof-rewrite proof result before '(1))))
     (proof-proof-transport proof rewritten after))))

(defun h4-book-hanoi-corollary-cases (p formula condition size lemma evaluate provider)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((yes (proof-proof-assume proof condition t))
      (yes (h4-book-hanoi-hanoi-corollary-empty yes p formula provider))
      (no (proof-proof-assume proof condition nil))
      (no (h4-book-hanoi-hanoi-corollary-transfer no p formula size lemma evaluate provider)))
     (h4-tactics-tactics-case-of p formula condition yes no))))

(defun h4-book-hanoi-hanoi-corollary-with-book-functions (p formula uses book-functions)
  (and (proof-is-call formula *proof-equal*)
    (proof-with-checked-results
     ((instances (h4-book-hints-hint-facts p uses book-functions))
      (lemma (h4-book-hanoi-first-implication instances)))
     (and lemma
       (proof-with-checked-results
        ((lhs (proof-term-at formula 1))
         (call (proof-term-at lhs 1))
         (size (proof-term-at call 1))
         (condition (list *h4-book-arithmetic-zp* size))
         (evaluate (h4-book-evaluation-closed-evaluation-init p))
         (provider (h4-book-finite-reduction-provider p)))
        (let ((result (h4-book-hanoi-corollary-cases p formula condition size lemma evaluate provider)))
          (if (and (failure-p result)
                   (member-equal (cadr result)
                                 '("InapplicableStep" "InapplicableTerm" "MissingProofInput"
                                   "assertion" "value" "key" "Unproved")))
              nil
            result)))))))

(defun h4-book-hanoi-hanoi-corollary (p formula uses)
  (h4-book-hanoi-hanoi-corollary-with-book-functions p formula uses nil))

(defun h4-book-hanoi-hanoi-proof-with-book-functions (p formula uses book-functions)
  (cond
   ((proof-is-call formula *library-implies*)
    (proof-with-checked-results ((conclusion (proof-term-at formula 2)))
      (and (proof-is-call conclusion *proof-equal*)
        (proof-with-checked-results ((lhs (proof-term-at conclusion 1)))
          (and (proof-is-call lhs *h4-book-hanoi-play*)
            (proof-with-checked-results
             ((premise (proof-term-at formula 1))
              (tests (h4-book-list-types-conjuncts premise)))
             (and (and (equal (len tests) 5)
                        (proof-is-call (nth 4 tests) *h4-book-hanoi-big-tops*))
               (proof-with-checked-results ((moves (proof-term-at lhs 1)))
                 (and (proof-is-call moves *h4-book-hanoi-h*)
                   (h4-book-hanoi-stack-transfer p formula))))))))))
   ((proof-is-call formula *proof-equal*)
    (proof-with-checked-results ((lhs (proof-term-at formula 1)))
      (and (proof-is-call lhs *h4-book-hanoi-play*)
        (proof-with-checked-results ((moves (proof-term-at lhs 1)))
          (and (proof-is-call moves (h4-book-hanoi-hanoi "HANOI"))
            (h4-book-hanoi-hanoi-corollary-with-book-functions p formula uses book-functions))))))
   (t nil)))

(defun h4-book-hanoi-hanoi-proof (p formula uses)
  (h4-book-hanoi-hanoi-proof-with-book-functions p formula uses nil))
