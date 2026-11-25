(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h1-book-witness-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *h1-book-witness-kwote* (proof-sym "KWOTE" "ACL2"))
(defconst *h1-book-witness-kwote-list* (proof-sym "KWOTE-LST" "ACL2"))
(defconst *h1-book-witness-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *h1-book-witness-pairlis* (proof-sym "PAIRLIS$" "ACL2"))
(defconst *h1-book-witness-char-code* (proof-cl "CHAR-CODE"))
(defconst *h1-book-witness-coerce* (proof-cl "COERCE"))
(defconst *h1-book-witness-symbol-name* (proof-cl "SYMBOL-NAME"))
(defconst *h1-book-witness-package-name* (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2"))
(defconst *h1-book-witness-quote-name* (proof-quote *proof-quote*))
(defconst *h1-book-witness-key* (proof-sym "H1-DISPATCH-KEY" "ACL2"))

(defund h1-book-witness-step-value (step)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((equation (proof-step-first step)))
      (proof-term-at equation 2))))

(defun h1-book-witness-table-from-keys (keys value)
  (if (endp keys)
      nil
    (cons (cons (car keys) value)
          (h1-book-witness-table-from-keys (cdr keys) value))))

(mutual-recursion
 (defun h1-book-witness-rename-calls (term changes)
   (declare (xargs :measure (acl2-count term)))
   (let ((head (h1-tactics-call-head term)))
     (cond
      ((or (atom term) (eq head :none) (equal head *proof-quote*)) term)
      ((proof-compound head)
       (if (and (consp (car term)) (consp (cdar term)) (consp (cddar term)))
           (proof-with-checked-results
            ((body (h1-book-witness-rename-calls (caddar term) changes))
             (head (list (caar term) (cadar term) body))
             (head (table-get changes head head))
             (args (h1-book-witness-rename-arguments (cdr term) changes)))
            (cons head args))
         '(:failure "failure" "")))
      (t
       (let ((head (table-get changes head head)))
         (proof-with-checked-results
          ((args (h1-book-witness-rename-arguments (cdr term) changes)))
          (cons head args)))))))
 (defun h1-book-witness-rename-arguments (args changes)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((arg (h1-book-witness-rename-calls (car args) changes))
       (rest (h1-book-witness-rename-arguments (cdr args) changes)))
      (cons arg rest)))))

(defun h1-book-witness-witness-prefix (raw)
  (concatenate 'string "H1-WITNESS-"
               (text-upper (siphash-hexdigest raw))))

(defun h1-book-witness-projection-choice (result premise name slot)
  (if (and (proof-is-call result name)
           (member-equal premise (cdr result)))
      (list slot (seq-index (cdr result) premise))
    '(:failure "unproved" "")))

(defun h1-book-witness-projection-result (result premise name)
  (if (proof-is-call result *h1-book-witness-mv-nth*)
      (proof-with-checked-results ((selector (proof-term-at result 1)))
        (if (proof-is-call selector *proof-quote*)
            (proof-with-checked-results
             ((slot (proof-term-at selector 1))
              (result (proof-term-at result 2)))
             (if (and (integerp slot) (<= 0 slot) (<= slot 8))
                 (h1-book-witness-projection-choice result premise name slot)
               '(:failure "unproved" "")))
          (h1-book-witness-projection-choice result premise name :none)))
    (h1-book-witness-projection-choice result premise name :none)))

(defund h1-book-witness-projection (formula name)
  (if (not (proof-is-call formula *library-implies*))
      '(:failure "unproved" "")
    (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
      (let* ((premise (cadr parts))
             (conclusion (caddr parts))
             (head (h1-tactics-call-head premise)))
        (cond
         ((or (eq head :none) (not (equal (len premise) 2)))
          '(:failure "unproved" ""))
         ((integerp conclusion)
          '(:failure "failure" ""))
         ((or (not (equal (length conclusion) 2))
              (not (equal head (h1-tactics-call-head conclusion))))
          '(:failure "unproved" ""))
         (t (h1-book-witness-projection-result (cadr conclusion)
                                               (cadr premise) name)))))))

(defun h1-book-witness-projection-results (formulas name results)
  (if (endp formulas)
      results
    (proof-with-checked-results
     ((pair (proof-list-of-length (car formulas) 2))
      (choice (h1-book-witness-projection (cadr pair) name)))
     (let* ((slot (car choice))
            (position (cadr choice))
            (prior (assoc-equal slot results)))
       (cond
        ((not prior)
         (h1-book-witness-projection-results
          (cdr formulas) name (table-put results slot position)))
        ((equal (cdr prior) position)
         (h1-book-witness-projection-results (cdr formulas) name results))
        (t '(:failure "unproved" "")))))))

(defun h1-book-witness-projection-formals (indices)
  (if (endp indices)
      nil
    (cons (proof-sym (concatenate 'string "H1-ARG-" (decimal-text (car indices))) "ACL2")
          (h1-book-witness-projection-formals (cdr indices)))))

(defun h1-book-witness-projection-max-slot (results slot)
  (if (endp results)
      slot
    (h1-book-witness-projection-max-slot (cdr results) (max slot (caar results)))))

(defun h1-book-witness-projection-tuple (slots results formals body)
  (if (endp slots)
      body
    (let ((choice (assoc-equal (car slots) results)))
      (proof-with-checked-results
       ((value (if choice (proof-term-at formals (cdr choice)) *proof-false*)))
       (h1-book-witness-projection-tuple (cdr slots) results formals
                                         (list *proof-cons* value body))))))

(defun h1-book-witness-projection-plan (results formals)
  (let ((direct (assoc-equal :none results)))
    (cond
     (direct
      (if (not (equal (len results) 1))
          '(:failure "unproved" "")
        (proof-with-checked-results ((body (proof-term-at formals (cdr direct))))
          (list body nil))))
     ((endp results) '(:failure "candidate-rejected" ""))
     (t
      (let ((maximum (h1-book-witness-projection-max-slot results 0)))
        (proof-with-checked-results
         ((body (h1-book-witness-projection-tuple
                 (seq-range maximum -1 -1) results formals *proof-false*)))
         (list body (list (cons *h1-book-witness-mv-nth* (1+ maximum))
                          (cons (proof-sym "ZP" "ACL2") 2)))))))))

(defun h1-book-witness-publish-entries (proof entries)
  (let ((lib (h1-tactics-prover-library proof)))
    (h1-tactics-prover-with-library
     proof (library-library-with-entries lib (append (library-library-entries lib) entries)))))

(defun h1-book-witness-definition (proof name formals body)
  (proof-with-checked-results
   ((proof (h1-tactics-prover-add-definition proof name formals body))
    (source (proof-line "define" (list *proof-nil* (list name formals body)))))
   (h1-book-witness-publish-entries proof (list (list "define" name nil source)))))

(defun h1-book-witness-lemma (proof name claim step conditions)
  (proof-with-checked-results
   ((lib (library-library-lemma (h1-tactics-prover-library proof)
                                 name claim step conditions)))
   (h1-tactics-prover-with-library proof lib)))

(defun h1-book-witness-projection-proofs (proof formulas changes openings)
  (if (endp formulas)
      nil
    (let ((lib (h1-tactics-prover-library proof))
          (p (h1-tactics-prover-proof proof)))
      (proof-with-checked-results
       ((obligation (h1-book-witness-rename-calls (cadar formulas) changes))
        (parts (proof-list-of-length obligation 3))
        (preserved (h1-tactics-prover-solve
                    proof (proof-eq (cadr (caddr parts)) (cadadr parts)) openings 160))
        (assumed (proof-proof-assume p (cadr parts) t))
        (step (h1-propositions-library-transport-argument lib assumed preserved 1))
        (step (h1-propositions-propositional-proof-implies-from lib obligation step))
        (step (proof-proof-subsume p step (list obligation)))
        (rest (h1-book-witness-projection-proofs proof (cdr formulas) changes openings)))
       (cons step rest)))))

(defun h1-book-witness-projection-witness (proof raw fields)
  (proof-with-checked-results
   ((fields (proof-list-of-length fields 2))
    (only (proof-list-of-length (car fields) 1))
    (function (proof-list-of-length (car only) 2))
    (results (h1-book-witness-projection-results (cadr fields) (car function) nil))
    (formals (h1-book-witness-projection-formals (seq-range 0 (cadr function) 1)))
    (plan (h1-book-witness-projection-plan results formals)))
   (let* ((name (car function))
          (witness (proof-sym (h1-book-witness-witness-prefix raw) "ACL2")))
     (proof-with-checked-results
      ((proof (h1-book-witness-definition proof witness formals (car plan)))
       (steps (h1-book-witness-projection-proofs proof (cadr fields)
                                                (list (cons name witness))
                                                (table-put (cadr plan) witness 1)))
       (entry (proof-proof-entry "witness" name (list name witness) steps)))
      (cons entry proof)))))

(defun h1-book-witness-tail (term count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      term
    (h1-book-witness-tail (list *library-cdr* term) (1- count))))

(defund h1-book-witness-exclude-predicate (proof context test assumed predicate)
  (let* ((p (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (actual (list predicate (cadr test)))
         (constant (list predicate (caddr test))))
    (proof-with-checked-results
     ((value (h1-tactics-prover-constant proof constant))
      (result (h1-book-witness-step-value value)))
     (let ((positive (equal result *proof-true*)))
       (proof-with-checked-results
        ((found (h1-tactics-context-find context (if positive (proof-neg actual) actual))))
        (if (not (car found))
            found
          (proof-with-checked-results
           ((rewritten (proof-proof-rewrite p (car found) assumed
                                            (if positive '(1 1 1) '(1 1))))
            (replaced (proof-proof-tidy p rewritten))
            (computed (h1-propositions-computed-test lib value))
            (conflict (if positive
                          (proof-proof-cut p computed replaced)
                        (proof-proof-cut p replaced computed)))
            (step (proof-proof-front p conflict (proof-neg test))))
           (cons step (cdr found)))))))))

(defun h1-book-witness-exclude-by-type (proof context test)
  (if (not (proof-is-call test *proof-equal*))
      (cons nil context)
    (proof-with-checked-results ((right (proof-term-at test 2)))
      (if (not (proof-is-call right *proof-quote*))
          (cons nil context)
        (proof-with-checked-results
         ((assumed (proof-proof-assume (h1-tactics-prover-proof proof) test t))
          (found (h1-book-witness-exclude-predicate proof context test assumed *proof-consp*)))
         (if (car found)
             found
           (h1-book-witness-exclude-predicate proof (cdr found) test assumed
                                             *h1-tactics-symbolp*)))))))

(defund h1-book-witness-character-code (name offset)
  (let ((size (length name)))
    (cond
     ((>= offset size) 0)
     ((< offset (- size)) '(:failure "failure" ""))
     (t (char-code (char name (if (< offset 0) (+ size offset) offset)))))))

(defun h1-book-witness-dispatch-key-width (operations component width)
  (if (endp operations)
      width
    (proof-with-checked-results ((name (proof-term-at (caar operations) component)))
      (h1-book-witness-dispatch-key-width
       (cdr operations) component (max width (length name))))))

(defun h1-book-witness-features (component offsets)
  (if (endp offsets)
      nil
    (cons (list component (car offsets))
          (h1-book-witness-features component (cdr offsets)))))

(defun h1-book-witness-extend-keys (keys component offset)
  (if (endp keys)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (caar keys) component))
      (code (h1-book-witness-character-code name offset))
      (rest (h1-book-witness-extend-keys (cdr keys) component offset)))
     (cons (cons (caar keys) (+ (* 256 (cdar keys)) code)) rest))))

(defun h1-book-witness-count-keys (keys counts)
  (if (endp keys)
      counts
    (let* ((key (car keys))
           (count (table-get counts key 0)))
      (h1-book-witness-count-keys (cdr keys) (table-put counts key (1+ count))))))

(defun h1-book-witness-collision-cost (counts)
  (if (endp counts)
      0
    (let ((count (cdar counts)))
      (+ (* count (1- count))
         (h1-book-witness-collision-cost (cdr counts))))))

(defun h1-book-witness-best-feature (choices keys best)
  (if (endp choices)
      best
    (let* ((feature (car choices))
           (component (car feature))
           (offset (cadr feature)))
      (proof-with-checked-results
       ((candidate (h1-book-witness-extend-keys keys component offset)))
       (let* ((counts (h1-book-witness-count-keys (table-values candidate) nil))
              (cost (+ (h1-book-witness-collision-cost counts) (* 8 offset))))
         (h1-book-witness-best-feature
          (cdr choices) keys (if (or (not best) (< cost (car best)))
                                 (list cost feature candidate)
                               best)))))))

(defun h1-book-witness-choose-features (choices keys features count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (list (reverse features) keys)
    (proof-with-checked-results
     ((best (h1-book-witness-best-feature choices keys nil)))
     (h1-book-witness-choose-features
      (remove-equal (cadr best) choices) (caddr best)
      (cons (cadr best) features) (1- count)))))

(defun h1-book-witness-dispatch-keys (operations)
  (if (endp operations)
      '(:failure "candidate-rejected" "")
    (proof-with-checked-results
     ((name-width (h1-book-witness-dispatch-key-width operations 2 0))
      (package-width (h1-book-witness-dispatch-key-width operations 1 0)))
     (let* ((choices (append (h1-book-witness-features 2 (seq-range 0 (min 8 name-width) 1))
                             (h1-book-witness-features 1 (seq-range 0 (min 8 package-width) 1))))
            (keys (h1-book-witness-table-from-keys (table-keys operations) 0)))
       (h1-book-witness-choose-features choices keys nil (min 3 (len choices)))))))

(defun h1-book-witness-code-term (symbol component offset)
  (let* ((text (list (if (equal component 2)
                        *h1-book-witness-symbol-name*
                      *h1-book-witness-package-name*)
                    symbol))
         (chars (list *h1-book-witness-coerce* text (proof-quote (proof-cl "LIST")))))
    (list *h1-book-witness-char-code*
          (list *library-car* (h1-book-witness-tail chars offset)))))

(defun h1-book-witness-evaluator-subcalls (terms application names)
  (if (endp terms)
      t
    (if (not (member-equal (h1-tactics-call-head (car terms)) names))
        (h1-book-witness-evaluator-subcalls (cdr terms) application names)
      (proof-with-checked-results
       ((actual (proof-term-at (car terms) 1))
        (parameter (proof-term-at application 1))
        (path (h1-recursion-selector-path actual parameter)))
       (and path (h1-book-witness-evaluator-subcalls (cdr terms) application names))))))

(defun h1-book-witness-evaluator-equation-list (formulas names)
  (if (endp formulas)
      nil
    (proof-with-checked-results ((pair (proof-list-of-length (car formulas) 2)))
      (let ((formula (cadr pair)))
        (if (not (proof-is-call formula *library-implies*))
            :none
          (proof-with-checked-results ((equation (proof-term-at formula 2)))
            (if (not (proof-is-call equation *proof-equal*))
                :none
              (proof-with-checked-results ((parts (proof-list-of-length equation 3)))
                (let ((application (cadr parts))
                      (result (caddr parts)))
                  (if (not (member-equal (h1-tactics-call-head application) names))
                      :none
                    (proof-with-checked-results
                     ((decreasing (h1-book-witness-evaluator-subcalls
                                   (h1-tactics-subterms result) application names))
                      (rest (h1-book-witness-evaluator-equation-list (cdr formulas) names)))
                     (if (or (eq rest :none) (not decreasing))
                         rest
                       (let ((head (h1-tactics-call-head result)))
                         (cons (list (car pair) (if (eq head :none) nil head))
                               rest))))))))))))))

(defun h1-book-witness-evaluator-equations (functions formulas)
  (if (not (equal (len functions) 2))
      nil
    (proof-with-checked-results ((first (proof-list-of-length (car functions) 2)))
      (if (not (equal (cadr first) 2))
          nil
        (proof-with-checked-results ((second (proof-list-of-length (cadr functions) 2)))
          (if (or (not (equal (cadr second) 2)) (> (len formulas) 40))
              nil
            (let ((names (seq-sorted (proof-unique (list (car first) (car second))))))
              (proof-with-checked-results
               ((equations (h1-book-witness-evaluator-equation-list formulas names)))
               (if (eq equations :none)
                   nil
                 (h1-book-witness-table-from-keys names equations))))))))))

(defun h1-book-witness-code-characters (characters)
  (if (endp characters)
      nil
    (cons (list "char" (char-code (car characters)))
          (h1-book-witness-code-characters (cdr characters)))))

(defun h1-book-witness-ones (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 1 (h1-book-witness-ones (1- count)))))

(defund h1-book-witness-compute-code-cdr (p step chars offset position)
  (proof-with-checked-results
   ((cdr-step (proof-proof-compute
               p (list *library-cdr* (proof-quote (or chars *proof-nil*)))
               (or (cdr chars) *proof-nil*))))
   (proof-proof-rewrite p step cdr-step (append position (h1-book-witness-ones offset)))))

(defun h1-book-witness-compute-code-cdrs (p step chars offsets position)
  (declare (xargs :measure (acl2-count offsets)))
  (cond
   ((failure-p step) step)
   ((endp offsets) (cons step chars))
   (t (h1-book-witness-compute-code-cdrs
       p (h1-book-witness-compute-code-cdr p step chars (car offsets) position)
       (cdr chars) (cdr offsets) position))))

(defund h1-book-witness-compute-code (proof operation component offset)
  (let* ((p (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (quoted (proof-quote operation))
         (term (h1-book-witness-code-term quoted component offset))
         (text (if (equal component 2)
                   *h1-book-witness-symbol-name*
                 *h1-book-witness-package-name*))
         (position '(1 2 1 1)))
    (proof-with-checked-results ((name (proof-term-at operation component)))
      (let* ((chars (h1-book-witness-code-characters (coerce name 'list)))
             (string-datum (list "str" name)))
        (proof-with-checked-results
         ((name-value (proof-proof-compute p (list text quoted) string-datum))
          (coerced (proof-proof-compute
                    p (list *h1-book-witness-coerce* (proof-quote string-datum)
                            (proof-quote (proof-cl "LIST"))) (or chars *proof-nil*)))
          (step (h1-propositions-propositional-proof-reflexive lib term))
          (step (proof-proof-rewrite p step name-value
                                     (append position (h1-book-witness-ones (1+ offset)))))
          (step (proof-proof-rewrite p step coerced
                                     (append position (h1-book-witness-ones offset))))
          (cdrs (h1-book-witness-compute-code-cdrs p step chars
                                                  (seq-range (1- offset) -1 -1)
                                                  position)))
         (let ((step (car cdrs))
               (chars (cdr cdrs)))
           (proof-with-checked-results
            ((car-step (proof-proof-compute
                        p (list *library-car* (proof-quote (or chars *proof-nil*)))
                        (if chars (car chars) *proof-nil*)))
             (step (proof-proof-rewrite p step car-step '(1 2 1)))
             (right (h1-book-witness-step-value step))
             (code (h1-book-witness-character-code name offset))
             (computed (proof-proof-compute p right code)))
            (proof-proof-chain p step (list computed)))))))))

(defun h1-book-witness-install-dispatch-test (proof label constant)
  (let* ((name (concatenate 'string "DISPATCH-" label))
         (lib (h1-tactics-prover-library proof))
         (p (h1-tactics-prover-proof proof)))
    (if (assoc-equal (proof-sym (concatenate 'string "SELF-" name) "ACL2")
                     (proof-proof-facts p))
        proof
      (let ((equation (proof-eq *library-x* constant)))
        (proof-with-checked-results
         ((assumed (proof-proof-assume p equation t))
          (evidence (h1-propositions-computed-test lib assumed))
          (oriented (proof-proof-front p evidence (proof-neg equation)))
          (claim (proof-step-first oriented))
          (condition (proof-step-first evidence)))
         (h1-book-witness-lemma proof name claim oriented (list condition)))))))

(defun h1-book-witness-install-dispatch-tests (proof)
  (proof-with-checked-results
   ((proof (h1-book-witness-install-dispatch-test proof "TRUE" *proof-true*)))
   (h1-book-witness-install-dispatch-test proof "FALSE" *proof-false*)))

(defund h1-book-witness-dispatch-test (proof value)
  (proof-with-checked-results ((result (h1-book-witness-step-value value)))
    (if (not (or (equal result *proof-true*) (equal result *proof-false*)))
        '(:failure "failure" "")
      (let ((name (if (equal result *proof-true*) "DISPATCH-TRUE" "DISPATCH-FALSE"))
            (lib (h1-tactics-prover-library proof))
            (p (h1-tactics-prover-proof proof)))
        (proof-with-checked-results
         ((equation (proof-step-first value))
          (actual (proof-term-at equation 1))
          (fact (library-library-cite lib name (list actual) nil)))
         (proof-proof-cut p value fact))))))

(defun h1-book-witness-make-dispatch (proof prefix branches definitions encoder features root)
  (list :h1-dispatch proof prefix branches definitions encoder features root))

(defun h1-book-witness-dispatch-proof (dispatch)
  (nth 1 dispatch))

(defun h1-book-witness-dispatch-prefix (dispatch)
  (nth 2 dispatch))

(defun h1-book-witness-dispatch-branches (dispatch)
  (nth 3 dispatch))

(defun h1-book-witness-dispatch-definitions (dispatch)
  (nth 4 dispatch))

(defun h1-book-witness-dispatch-encoder (dispatch)
  (nth 5 dispatch))

(defun h1-book-witness-dispatch-features (dispatch)
  (nth 6 dispatch))

(defun h1-book-witness-dispatch-root (dispatch)
  (nth 7 dispatch))

(defun h1-book-witness-dispatch-with-proof (dispatch proof)
  (update-nth 1 proof dispatch))

(defun h1-book-witness-operation-keys (operations keys)
  (if (endp operations)
      nil
    (let ((entry (assoc-equal (caar operations) keys)))
      (if (not entry)
          '(:failure "failure" "")
        (proof-with-checked-results
         ((rest (h1-book-witness-operation-keys (cdr operations) keys)))
         (cons (cdr entry) rest))))))

(defun h1-book-witness-dispatch-pivot-choices (counts lower total)
  (if (endp counts)
      nil
    (let* ((pivot (caar counts))
           (count (cadar counts))
           (rest (h1-book-witness-dispatch-pivot-choices
                  (cdr counts) (+ lower count) total)))
      (if (equal lower 0)
          rest
        (cons (list (abs (- total (* 2 lower))) pivot) rest)))))

(defun h1-book-witness-dispatch-min-choice (choices best)
  (if (endp choices)
      best
    (let ((choice (car choices)))
      (h1-book-witness-dispatch-min-choice
       (cdr choices)
       (if (or (not best) (< (car choice) (car best))
               (and (equal (car choice) (car best)) (< (cadr choice) (cadr best))))
           choice
         best)))))

(defund h1-book-witness-dispatch-split (operations keys)
  (if (or (endp keys) (<= (len operations) 4))
      nil
    (proof-with-checked-results ((selected (h1-book-witness-operation-keys operations keys)))
      (let* ((counts (h1-book-witness-count-keys selected nil))
             (choices (h1-book-witness-dispatch-pivot-choices
                       (seq-sorted (table-items counts)) 0 (len operations))))
        (cadr (h1-book-witness-dispatch-min-choice choices nil))))))

(defun h1-book-witness-dispatch-leaf (operations body)
  (if (endp operations)
      body
    (h1-book-witness-dispatch-leaf
     (cdr operations)
     (proof-ite (proof-eq *library-x* (proof-quote (caar operations)))
                (cdar operations) body))))

(defun h1-book-witness-dispatch-groups (operations keys split left right)
  (if (endp operations)
      (list (reverse left) (reverse right))
    (let ((operation (car operations)))
      (if (>= (table-get keys (car operation) 0) split)
          (h1-book-witness-dispatch-groups (cdr operations) keys split
                                           left (cons operation right))
        (h1-book-witness-dispatch-groups (cdr operations) keys split
                                         (cons operation left) right)))))

(defun h1-book-witness-dispatch-branch (proof name formals body identifier side)
  (let* ((p (h1-tactics-prover-proof proof))
         (label (concatenate 'string identifier (if side "-L" "-R")))
         (lemma (seq-slice label 3 :none)))
    (proof-with-checked-results
     ((unfolded (proof-proof-unfold p (cons name formals)))
      (choice (if side (proof-proof-if-true p body) (proof-proof-if-false p body)))
      (branch (proof-proof-chain p unfolded (list choice)))
      (condition (proof-term-at (proof-step-clause branch) 1))
      (branch (proof-proof-front p branch condition))
      (claim (proof-step-first branch))
      (proof (h1-book-witness-lemma proof lemma claim branch (cdr (proof-step-clause branch)))))
     (cons (proof-sym (concatenate 'string "SELF-" lemma) "ACL2") proof))))

(defun h1-book-witness-dispatch-publish (dispatch name formals body identifier split)
  (proof-with-checked-results
   ((proof (h1-book-witness-definition (h1-book-witness-dispatch-proof dispatch)
                                       name formals body)))
   (if (null split)
       (cons name (h1-book-witness-dispatch-with-proof dispatch proof))
     (proof-with-checked-results
      ((left (h1-book-witness-dispatch-branch proof name formals body identifier t))
       (right (h1-book-witness-dispatch-branch (cdr left) name formals body identifier nil)))
      (let ((branches (table-put (h1-book-witness-dispatch-branches dispatch)
                                    name (list split (list (car left) (car right))))))
        (cons name (update-nth 3 branches
                               (h1-book-witness-dispatch-with-proof dispatch (cdr right)))))))))

(defun h1-book-witness-dispatch-define (n dispatch operations keys)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h1-book-witness-dispatch-define")
    (let* ((definitions (h1-book-witness-dispatch-definitions dispatch))
           (identifier (concatenate 'string (h1-book-witness-dispatch-prefix dispatch)
                                    "-D" (decimal-text definitions)))
           (name (proof-sym identifier "ACL2"))
           (dispatch (update-nth 4 (1+ definitions) dispatch)))
      (proof-with-checked-results ((split (h1-book-witness-dispatch-split operations keys)))
        (let ((formals (if keys
                           (list *h1-book-witness-key* *library-x* *library-z*)
                         (list *library-x* *library-z*))))
          (if (null split)
              (h1-book-witness-dispatch-publish
               dispatch name formals
               (h1-book-witness-dispatch-leaf (reverse operations) *proof-false*) identifier nil)
            (let ((groups (h1-book-witness-dispatch-groups operations keys split nil nil)))
              (proof-with-checked-results
               ((left (h1-book-witness-dispatch-define (1- n) dispatch (car groups) keys))
                (right (h1-book-witness-dispatch-define (1- n) (cdr left) (cadr groups) keys)))
               (let* ((actuals (list *h1-book-witness-key* *library-x* *library-z*))
                      (body (proof-ite (library-lt *h1-book-witness-key* (proof-quote split))
                                       (cons (car left) actuals) (cons (car right) actuals))))
                 (h1-book-witness-dispatch-publish
                  (cdr right) name formals body identifier split))))))))))

(defun h1-book-witness-encoder-body (features body)
  (if (endp features)
      body
    (let ((feature (car features)))
      (h1-book-witness-encoder-body
       (cdr features)
       (library-plus (list *proof-times* (proof-quote 256) body)
                     (h1-book-witness-code-term *library-x* (car feature) (cadr feature)))))))

(defun h1-book-witness-dispatch-init (proof prefix operations)
  (proof-with-checked-results
   ((proof (h1-book-witness-install-dispatch-tests proof)))
   (if (<= (len operations) 4)
       (proof-with-checked-results
        ((result (h1-book-witness-dispatch-define
                  1000000 (h1-book-witness-make-dispatch proof prefix nil 0 nil nil nil)
                  operations nil)))
        (update-nth 7 (car result) (cdr result)))
     (proof-with-checked-results
      ((result (h1-book-witness-dispatch-keys operations))
       (first (proof-term-at (car result) 0)))
      (let* ((features (car result))
             (keys (cadr result))
             (body (h1-book-witness-encoder-body
                    (cdr features)
                    (h1-book-witness-code-term *library-x* (car first) (cadr first))))
             (encoder (proof-sym (concatenate 'string prefix "-KEY") "ACL2")))
        (proof-with-checked-results
         ((proof (h1-book-witness-definition proof encoder (list *library-x*) body))
          (result (h1-book-witness-dispatch-define
                   1000000 (h1-book-witness-make-dispatch proof prefix nil 0 encoder features nil)
                   operations keys)))
         (let* ((root (proof-sym (concatenate 'string prefix "-DISPATCH") "ACL2"))
                (body (list (car result) (list encoder *library-x*) *library-x* *library-z*)))
           (proof-with-checked-results
            ((proof (h1-book-witness-definition (h1-book-witness-dispatch-proof (cdr result))
                                                root (list *library-x* *library-z*) body)))
            (update-nth 7 root (h1-book-witness-dispatch-with-proof (cdr result) proof))))))))))

(defund h1-book-witness-dispatch-rewrite-code (proof operation feature key)
  (proof-with-checked-results
   ((code (h1-book-witness-compute-code proof operation (car feature) (cadr feature))))
   (h1-propositions-rewrite-value (h1-tactics-prover-library proof) key code)))

(defun h1-book-witness-dispatch-rewrite-codes (proof operation features key)
  (declare (xargs :measure (acl2-count features)))
  (cond
   ((failure-p key) key)
   ((endp features) key)
   (t (h1-book-witness-dispatch-rewrite-codes
       proof operation (cdr features)
       (h1-book-witness-dispatch-rewrite-code proof operation (car features) key)))))

(defun h1-book-witness-dispatch-encoded (dispatch term operation)
  (let* ((proof (h1-book-witness-dispatch-proof dispatch))
         (p (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
     ((step (proof-proof-unfold p term))
      (key (proof-proof-unfold p (list (h1-book-witness-dispatch-encoder dispatch)
                                       (proof-quote operation))))
      (key (h1-book-witness-dispatch-rewrite-codes
            proof operation (h1-book-witness-dispatch-features dispatch) key))
      (right (h1-book-witness-step-value key))
      (simplified (h1-propositions-proof-simplify p right nil nil))
      (key (proof-proof-chain p key (list simplified)))
      (step (h1-propositions-rewrite-value lib step key)))
     (cons step key))))

(defund h1-book-witness-dispatch-evaluate-branch (dispatch step key operation arguments)
  (proof-with-checked-results
   ((right (h1-book-witness-step-value step))
    (head (proof-term-at right 0)))
   (let* ((proof (h1-book-witness-dispatch-proof dispatch))
          (p (h1-tactics-prover-proof proof))
          (branch (assoc-equal head (h1-book-witness-dispatch-branches dispatch))))
     (if (not branch)
         (proof-with-checked-results
          ((unfolded (proof-proof-unfold p right))
           (step (proof-proof-chain p step (list unfolded))))
          (cons t step))
       (let ((pivot (cadr branch))
             (equations (caddr branch)))
         (proof-with-checked-results
          ((key-value (h1-book-witness-step-value key))
           (value (h1-tactics-prover-constant proof (library-lt key-value (proof-quote pivot))))
           (right (h1-book-witness-step-value value))
           (known (h1-book-witness-dispatch-test proof value)))
          (let* ((rightp (equal right *proof-false*))
                 (bindings (append (list (list *h1-book-witness-key* key-value)
                                         (list *library-x* (proof-quote operation)))
                                   (if (equal arguments *library-z*) nil
                                     (list (list *library-z* arguments))))))
            (proof-with-checked-results
             ((branch (proof-proof-fact p (if rightp (cadr equations) (car equations)) bindings))
              (selected (if rightp (proof-proof-cut p branch known)
                          (proof-proof-cut p known branch)))
              (step (proof-proof-chain p step (list selected))))
             (cons nil step)))))))))

(defun h1-book-witness-dispatch-evaluate-branches (n dispatch step key operation arguments)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h1-book-witness-dispatch-evaluate-branches")
    (proof-with-checked-results
     ((result (h1-book-witness-dispatch-evaluate-branch dispatch step key operation arguments)))
     (if (car result)
         (cdr result)
       (h1-book-witness-dispatch-evaluate-branches
        (1- n) dispatch (cdr result) key operation arguments)))))

(defund h1-book-witness-dispatch-evaluate-leaf-test (proof step)
  (proof-with-checked-results ((right (h1-book-witness-step-value step)))
    (if (not (proof-is-call right *proof-if*))
        '(:failure "unproved" "")
      (proof-with-checked-results
       ((test (proof-term-at right 1))
        (value (h1-tactics-prover-constant proof test))
        (known (h1-book-witness-dispatch-test proof value))
        (step (h1-propositions-select-value (h1-tactics-prover-library proof) step known))
        (literal (proof-step-first known)))
       (cons (equal literal test) step)))))

(defun h1-book-witness-dispatch-evaluate-leaf (n proof step)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h1-book-witness-dispatch-evaluate-leaf")
    (proof-with-checked-results ((result (h1-book-witness-dispatch-evaluate-leaf-test proof step)))
      (if (car result)
          (cdr result)
        (h1-book-witness-dispatch-evaluate-leaf (1- n) proof (cdr result))))))

(defun h1-book-witness-dispatch-evaluate (dispatch operation arguments)
  (let* ((proof (h1-book-witness-dispatch-proof dispatch))
         (term (list (h1-book-witness-dispatch-root dispatch) (proof-quote operation) arguments)))
    (proof-with-checked-results
     ((step (h1-propositions-propositional-proof-reflexive (h1-tactics-prover-library proof) term))
      (encoded (if (h1-book-witness-dispatch-encoder dispatch)
                   (h1-book-witness-dispatch-encoded dispatch term operation)
                 (cons step nil)))
      (step (h1-book-witness-dispatch-evaluate-branches
             1000000 dispatch (car encoded) (cdr encoded) operation arguments)))
     (h1-book-witness-dispatch-evaluate-leaf 1000000 proof step))))

(defun h1-book-witness-extend-bindings (pairs dictionary)
  (if (endp pairs)
      dictionary
    (h1-book-witness-extend-bindings
     (cdr pairs) (table-put dictionary (caar pairs) (cadar pairs)))))

(defun h1-book-witness-make-evaluator-witness (proof prefix value values name cases positions dispatch)
  (list :h1-evaluator-witness proof prefix value values name cases positions dispatch))

(defun h1-book-witness-evaluator-witness-proof (witness)
  (nth 1 witness))

(defun h1-book-witness-evaluator-witness-prefix (witness)
  (nth 2 witness))

(defun h1-book-witness-evaluator-witness-value (witness)
  (nth 3 witness))

(defun h1-book-witness-evaluator-witness-values (witness)
  (nth 4 witness))

(defun h1-book-witness-evaluator-witness-name (witness)
  (nth 5 witness))

(defun h1-book-witness-evaluator-witness-cases (witness)
  (nth 6 witness))

(defun h1-book-witness-evaluator-witness-positions (witness)
  (nth 7 witness))

(defun h1-book-witness-evaluator-witness-dispatch (witness)
  (nth 8 witness))

(defun h1-book-witness-evaluator-witness-with-proof (witness proof)
  (update-nth 1 proof witness))

(defun h1-book-witness-evaluator-witness-operation-equality (equality)
  (if (not (proof-is-call equality *proof-equal*))
      nil
    (proof-with-checked-results ((left (proof-term-at equality 1)))
      (if (not (equal left (list *library-car* *library-x*)))
          nil
        (proof-with-checked-results ((right (proof-term-at equality 2)))
          (if (or (not (proof-is-call right *proof-quote*))
                  (equal right *h1-book-witness-quote-name*))
              nil
            (proof-with-checked-results ((operation (proof-term-at right 1)))
              (cond ((null operation) '(:failure "failure" ""))
                    ((and (consp operation) (equal (car operation) "sym")) operation)
                    (t nil)))))))))

(defun h1-book-witness-evaluator-witness-operation (premise)
  (if (not (proof-is-call premise *proof-if*))
      nil
    (proof-with-checked-results ((test (proof-term-at premise 1)))
      (if (not (equal test (list *proof-consp* *library-x*)))
          nil
        (proof-with-checked-results ((otherwise (proof-term-at premise 3)))
          (if (not (equal otherwise *proof-false*))
              nil
            (h1-book-witness-evaluator-witness-operation-equality (caddr premise))))))))

(defun h1-book-witness-evaluator-position (child position)
  (declare (xargs :measure (acl2-count child)))
  (if (proof-is-call child *library-cdr*)
      (if (and (consp child) (consp (cdr child)))
          (h1-book-witness-evaluator-position (cadr child) (1+ position))
        '(:failure "failure" ""))
    (if (and (equal child *library-x*) (> position 0))
        (1- position)
      nil)))

(defun h1-book-witness-evaluator-argument (term value)
  (if (not (proof-is-call term value))
      nil
    (proof-with-checked-results ((env (proof-term-at term 2)))
      (if (and (equal env *library-y*) (proof-is-call (cadr term) *library-car*))
          (proof-with-checked-results ((child (proof-term-at (cadr term) 1)))
            (h1-book-witness-evaluator-position child 0))
        nil))))

(mutual-recursion
 (defun h1-book-witness-evaluator-witness-on-values (witness term)
   (declare (xargs :measure (acl2-count term)))
   (let* ((head (h1-tactics-call-head term))
          (value (h1-book-witness-evaluator-witness-value witness))
          (values (h1-book-witness-evaluator-witness-values witness)))
     (if (equal head *proof-quote*)
         (cons term witness)
       (proof-with-checked-results
        ((position (h1-book-witness-evaluator-argument term value)))
        (cond
         (position
          (let* ((positions (h1-book-witness-evaluator-witness-positions witness))
                 (positions (if (member-equal position positions)
                                positions
                              (seq-sorted (cons position positions)))))
            (cons (list *library-car* (h1-book-witness-tail *library-z* position))
                  (update-nth 7 positions witness))))
         ((or (atom term) (member-equal head (list value values :none)) (proof-compound head))
          '(:failure "unproved" ""))
         (t
          (proof-with-checked-results
           ((args (h1-book-witness-evaluator-on-arguments witness (cdr term))))
           (cons (cons head (car args)) (cdr args)))))))))
 (defun h1-book-witness-evaluator-on-arguments (witness args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       (cons nil witness)
     (proof-with-checked-results
      ((arg (h1-book-witness-evaluator-witness-on-values witness (car args)))
       (rest (h1-book-witness-evaluator-on-arguments (cdr arg) (cdr args))))
      (cons (cons (car arg) (car rest)) (cdr rest))))))

(defun h1-book-witness-evaluator-parameters-p (arguments)
  (if (endp arguments)
      t
    (let ((arg (car arguments)))
      (cond ((null arg) '(:failure "failure" ""))
            ((and (consp arg) (equal (car arg) "sym"))
             (h1-book-witness-evaluator-parameters-p (cdr arguments)))
            (t nil)))))

(defun h1-book-witness-evaluator-canonical (witness formula equation)
  (proof-with-checked-results
   ((formula (proof-list-of-length formula 3))
    (equation (proof-list-of-length equation 3)))
   (let* ((call (cadr equation))
          (evaluator (h1-tactics-call-head call))
          (value (h1-book-witness-evaluator-witness-value witness))
          (values (h1-book-witness-evaluator-witness-values witness)))
     (proof-with-checked-results
      ((parameters (and (member-equal evaluator (list value values))
                        (h1-book-witness-evaluator-parameters-p (cdr call)))))
      (if (not parameters)
          '(:failure "unproved" "")
        (let ((variables (list *library-x* *library-y*)))
          (proof-with-checked-results
           ((canonical (proof-subst formula (h1-book-witness-extend-bindings
                                             (seq-zip (cdr call) variables) nil)))
            (operation (if (equal evaluator value)
                           (h1-book-witness-evaluator-witness-operation (cadr canonical))
                         nil)))
           (list formula
                 (h1-book-witness-extend-bindings (seq-zip variables (cdr call)) nil)
                 canonical operation))))))))

(defund h1-book-witness-evaluator-case (witness formula renamed)
  (proof-with-checked-results ((formula (h1-book-witness-rename-calls formula renamed)))
    (if (not (proof-is-call formula *library-implies*))
        '(:failure "unproved" "")
      (proof-with-checked-results ((equation (proof-term-at formula 2)))
        (if (not (proof-is-call equation *proof-equal*))
            '(:failure "unproved" "")
          (h1-book-witness-evaluator-canonical witness formula equation))))))

(defund h1-book-witness-evaluator-register-case (witness obligation operations)
  (let ((operation (cadddr obligation)))
    (if (null operation)
        (cons operations witness)
      (let* ((canonical (caddr obligation))
             (result (caddr (caddr canonical))))
        (proof-with-checked-results
         ((branch (h1-book-witness-evaluator-witness-on-values witness result)))
         (let ((previous (assoc-equal operation operations)))
           (cond
            ((not previous)
             (cons (table-put operations operation (car branch)) (cdr branch)))
            ((equal (cdr previous) (car branch)) (cons operations (cdr branch)))
            (t '(:failure "unproved" "")))))))))

(defun h1-book-witness-evaluator-cases (formulas renamed witness operations cases)
  (if (endp formulas)
      (cons operations (update-nth 6 (reverse cases) witness))
    (proof-with-checked-results
     ((pair (proof-list-of-length (car formulas) 2))
      (obligation (h1-book-witness-evaluator-case witness (cadr pair) renamed))
      (registered (h1-book-witness-evaluator-register-case witness obligation operations)))
     (h1-book-witness-evaluator-cases (cdr formulas) renamed (cdr registered)
                                      (car registered) (cons obligation cases)))))

(defun h1-book-witness-add-evaluator-definitions (proof definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (or (failure-p proof) (endp definitions))
      proof
    (let ((definition (car definitions)))
      (h1-book-witness-add-evaluator-definitions
       (h1-tactics-prover-add-definition proof (car definition) (cadr definition) (caddr definition))
       (cdr definitions)))))

(defun h1-book-witness-evaluator-witness-define (witness)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (value (h1-book-witness-evaluator-witness-value witness))
         (values (h1-book-witness-evaluator-witness-values witness))
         (first (list *library-car* *library-x*))
         (rest (list *library-cdr* *library-x*))
         (args (list values rest *library-y*))
         (dispatch (h1-book-witness-evaluator-witness-dispatch witness))
         (application (list (h1-book-witness-dispatch-root dispatch) first args))
         (lambda-body (list value (list *library-car* (h1-book-witness-tail first 2))
                            (list *h1-book-witness-pairlis*
                                  (list *library-car* (list *library-cdr* first))
                                  args)))
         (atom (proof-ite (list *h1-tactics-symbolp* *library-x*)
                          (proof-ite *library-x*
                                     (list *library-cdr* (list *h1-book-witness-assoc*
                                                               *library-x* *library-y*))
                                     *proof-false*)
                          *proof-false*))
         (calls (proof-ite (list *proof-consp* first) lambda-body
                           (proof-ite (list *h1-tactics-symbolp* first)
                                      application *proof-false*)))
         (body (proof-ite (list *proof-consp* *library-x*)
                          (proof-ite (proof-eq first *h1-book-witness-quote-name*)
                                     (list *library-car* rest) calls)
                          atom))
         (list-body (proof-ite (list *proof-consp* *library-x*)
                               (list *proof-cons* (list value first *library-y*) args)
                               *proof-false*))
         (formals (list *library-x* *library-y*))
         (definitions (list (list value formals body) (list values formals list-body))))
    (proof-with-checked-results
     ((calls (termination-recursive-calls *termination-all* definitions))
      (measure (h1-book-termination-termination-entry proof definitions calls nil))
      (proof (h1-book-witness-add-evaluator-definitions proof definitions))
      (source (proof-line "define" (cons *termination-all* definitions))))
     (let ((entry (list "define" value nil source)))
       (h1-book-witness-evaluator-witness-with-proof
        witness (h1-book-witness-publish-entries proof (list entry measure)))))))

(defun h1-book-witness-function-arities (functions)
  (if (endp functions)
      nil
    (proof-with-checked-results
     ((function (proof-list-of-length (car functions) 2))
      (rest (h1-book-witness-function-arities (cdr functions))))
     (cons (cadr function) rest))))

(defun h1-book-witness-evaluator-witness-init (proof raw fields)
  (proof-with-checked-results
   ((fields (proof-list-of-length fields 2))
    (arities (h1-book-witness-function-arities (car fields))))
   (if (not (equal arities '(2 2)))
       '(:failure "unproved" "")
     (let* ((prefix (h1-book-witness-witness-prefix raw))
            (value (proof-sym prefix "ACL2"))
            (values (proof-sym (concatenate 'string prefix "-LIST") "ACL2"))
            (functions (car fields))
            (renamed (h1-book-witness-extend-bindings
                      (seq-zip (list (caar functions) (caadr functions)) (list value values))
                      nil))
            (witness (h1-book-witness-make-evaluator-witness
                      proof prefix value values (caar functions) nil nil nil)))
       (proof-with-checked-results
        ((cases (h1-book-witness-evaluator-cases (cadr fields) renamed witness nil nil))
         (dispatch (h1-book-witness-dispatch-init proof prefix (car cases))))
        (let ((witness (update-nth 8 dispatch (cdr cases))))
          (h1-book-witness-evaluator-witness-define
           (h1-book-witness-evaluator-witness-with-proof
            witness (h1-book-witness-dispatch-proof dispatch)))))))))

(defun h1-book-witness-evaluator-witness-lemma (witness label step)
  (let* ((prefix (h1-book-witness-evaluator-witness-prefix witness))
         (proof (h1-book-witness-evaluator-witness-proof witness))
         (name (concatenate 'string (seq-slice prefix 3 :none) "-" label)))
    (proof-with-checked-results
     ((result (h1-tactics-prover-helper proof name step (cdr (proof-step-clause step)) nil)))
     (cons (proof-sym (concatenate 'string prefix "-" label) "ACL2")
           (h1-book-witness-evaluator-witness-with-proof witness (cdr result))))))

(defun h1-book-witness-list-projection (witness original test at-cons at-atom selector evaluator empty)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (lib (h1-tactics-prover-library proof))
         (p (h1-tactics-prover-proof proof))
         (label (caddr selector))
         (output (list selector original))
         (target (list evaluator (list selector *library-x*) *library-y*)))
    (proof-with-checked-results
     ((value (h1-book-witness-step-value at-cons))
      (allowed (library-library-axiom lib (concatenate 'string label "-CONS") (cdr value)))
      (symmetric (h1-propositions-proof-symmetric p at-cons))
      (yes (proof-proof-rewrite p allowed symmetric '(1 1 1)))
      (yes (proof-proof-tidy p yes))
      (constant (h1-tactics-prover-constant proof (list selector *proof-false*)))
      (symmetric (h1-propositions-proof-symmetric p constant))
      (finished (proof-proof-chain p empty (list symmetric)))
      (completed (library-library-axiom lib (concatenate 'string "COMPLETION-OF-" label)
                                        (list *library-x*)))
      (assumed (proof-proof-assume p test nil))
      (on-atom (h1-propositions-select-value lib completed assumed))
      (symmetric (h1-propositions-proof-symmetric p on-atom))
      (no (proof-proof-rewrite p finished symmetric '(1 1 1)))
      (symmetric (h1-propositions-proof-symmetric p at-atom))
      (no (proof-proof-rewrite p no symmetric '(1 2 1)))
      (no (h1-propositions-proof-symmetric p no))
      (yes-first (proof-step-first yes))
      (no-first (proof-step-first no)))
     (if (not (and (equal yes-first no-first) (equal no-first (proof-eq output target))))
         '(:failure "failure" "")
       (proof-with-checked-results ((step (proof-proof-cases p test yes no)))
         (h1-book-witness-evaluator-witness-lemma witness label step))))))

(defun h1-book-witness-evaluator-witness-list-projections (witness)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (lib (h1-tactics-prover-library proof))
         (p (h1-tactics-prover-proof proof))
         (value (h1-book-witness-evaluator-witness-value witness))
         (values (h1-book-witness-evaluator-witness-values witness))
         (original (list values *library-x* *library-y*))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
     ((equation (proof-proof-unfold p original))
      (assumed (proof-proof-assume p test t))
      (at-cons (h1-propositions-select-value lib equation assumed))
      (assumed (proof-proof-assume p test nil))
      (at-atom (h1-propositions-select-value lib equation assumed))
      (nil-value (h1-tactics-prover-solve
                  proof (proof-eq (list value *proof-false* *library-y*) *proof-false*)
                  (list value) 160))
      (nil-list (h1-tactics-prover-solve
                 proof (proof-eq (list values *proof-false* *library-y*) *proof-false*)
                 (list values) 160))
      (first (h1-book-witness-list-projection witness original test at-cons at-atom
                                              *library-car* value nil-value))
      (rest (h1-book-witness-list-projection (cdr first) original test at-cons at-atom
                                             *library-cdr* values nil-list)))
     (cons (list (car first) (car rest)) (cdr rest)))))

(defund h1-book-witness-project-cdr (p step rest position index)
  (let* ((bindings (list (list *library-x* (h1-book-witness-tail *library-x* index))))
         (place (append '(1 2 1) (h1-book-witness-ones (1- (- position index))))))
    (proof-with-checked-results ((equation (proof-proof-fact p rest bindings)))
      (proof-proof-rewrite p step equation place))))

(defun h1-book-witness-project-cdrs (p step rest position indices)
  (declare (xargs :measure (acl2-count indices)))
  (cond
   ((failure-p step) step)
   ((endp indices) step)
   (t (h1-book-witness-project-cdrs
       p (h1-book-witness-project-cdr p step rest position (car indices))
       rest position (cdr indices)))))

(defund h1-book-witness-project-argument (witness position first rest)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (lib (h1-tactics-prover-library proof))
         (p (h1-tactics-prover-proof proof))
         (values (h1-book-witness-evaluator-witness-values witness))
         (output (list *library-car*
                       (h1-book-witness-tail (list values *library-x* *library-y*) position))))
    (proof-with-checked-results
     ((step (h1-propositions-propositional-proof-reflexive lib output))
      (step (h1-book-witness-project-cdrs p step rest position (seq-range 0 position 1)))
      (head (proof-proof-fact p first (list (list *library-x*
                                                (h1-book-witness-tail *library-x* position)))))
      (step (proof-proof-chain p step (list head))))
     (if (equal position 0)
         (cons first witness)
       (h1-book-witness-evaluator-witness-lemma
        witness (concatenate 'string "ARGUMENT-" (decimal-text position)) step)))))

(defun h1-book-witness-project-arguments (witness positions first rest)
  (declare (xargs :measure (acl2-count positions)))
  (if (endp positions)
      (cons nil witness)
    (proof-with-checked-results
     ((projection (h1-book-witness-project-argument witness (car positions) first rest))
      (following (h1-book-witness-project-arguments (cdr projection) (cdr positions) first rest)))
     (cons (cons (list (car positions) (car projection)) (car following))
           (cdr following)))))

(defun h1-book-witness-evaluator-witness-argument-projections (witness)
  (proof-with-checked-results
   ((result (h1-book-witness-evaluator-witness-list-projections witness)))
   (h1-book-witness-project-arguments (cdr result)
                                      (h1-book-witness-evaluator-witness-positions (cdr result))
                                      (caar result) (cadar result))))

(defun h1-book-witness-requoted-list-cons (lib values)
  (let ((p (library-library-proof lib)))
    (proof-with-checked-results
     ((step (proof-proof-unfold p (list values (list *proof-cons* *library-x* *library-y*)
                                      *library-z*)))
      (test (proof-proof-fact p "consp-cons" nil))
      (step (h1-propositions-select-value lib step test))
      (car-step (library-library-axiom lib "CAR-CONS" (list *library-x* *library-y*)))
      (step (h1-propositions-rewrite-value lib step car-step))
      (cdr-step (library-library-axiom lib "CDR-CONS" (list *library-x* *library-y*))))
     (h1-propositions-rewrite-value lib step cdr-step))))

(defun h1-book-witness-requoted-list-yes
       (lib original claim at-cons cons-test arguments quote-cons quoted-value list-cons)
  (let* ((p (library-library-proof lib))
         (measure (list *library-count* *library-x*))
         (child (list *library-cdr* *library-x*))
         (smaller (list *proof-ordinal-less* (list *library-count* child) measure))
         (pairs (list (list *library-x* child))))
    (proof-with-checked-results
     ((yes (h1-propositions-propositional-proof-reflexive lib original))
      (yes (h1-propositions-rewrite-value lib yes at-cons))
      (quote-cons (proof-proof-instantiate p quote-cons (seq-zip (list *library-x* *library-y*)
                                                               arguments)))
      (yes (h1-propositions-rewrite-value lib yes quote-cons))
      (list-cons (proof-proof-instantiate
                  p list-cons (list (list *library-x* (list *h1-book-witness-kwote* (car arguments)))
                                    (list *library-y* (list *h1-book-witness-kwote-list* (cadr arguments)))
                                    (list *library-z* *proof-false*))))
      (yes (proof-proof-chain p yes (list list-cons)))
      (quoted-value (proof-proof-instantiate
                     p quoted-value (list (list *library-x* (car arguments))
                                          (list *library-y* *proof-false*))))
      (yes (h1-propositions-rewrite-value lib yes quoted-value))
      (builtin (library-library-builtin lib 3 *library-x*))
      (decrease (proof-proof-subsume p builtin (list smaller (proof-neg cons-test))))
      (child-claim (proof-subst claim (h1-book-witness-extend-bindings pairs nil)))
      (hypothesis (proof-proof-assume p (proof-ite smaller child-claim *proof-true*) t))
      (decreased (h1-propositions-proof-prove-if p hypothesis decrease))
      (yes (h1-propositions-rewrite-value lib yes decreased))
      (symmetric (h1-propositions-proof-symmetric p at-cons)))
     (proof-proof-chain p yes (list symmetric)))))

(defun h1-book-witness-evaluator-witness-requoted-list (witness)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (lib (h1-tactics-prover-library proof))
         (p (h1-tactics-prover-proof proof))
         (value (h1-book-witness-evaluator-witness-value witness))
         (values (h1-book-witness-evaluator-witness-values witness))
         (evaluated (list values *library-x* *library-y*))
         (original (list values (list *h1-book-witness-kwote-list* evaluated) *proof-false*))
         (claim (proof-eq original evaluated))
         (cons-test (list *proof-consp* *library-x*))
         (kwote-cons (list *h1-book-witness-kwote-list* (list *proof-cons* *library-x* *library-y*)))
         (quote-head (list *h1-book-witness-kwote* *library-x*))
         (quote-tail (list *h1-book-witness-kwote-list* *library-y*))
         (measure (list *library-count* *library-x*))
         (pairs (list (list *library-x* (list *library-cdr* *library-x*)))))
    (proof-with-checked-results
     ((expansion (proof-proof-unfold p evaluated))
      (assumed (proof-proof-assume p cons-test t))
      (at-cons (h1-propositions-select-value lib expansion assumed))
      (assumed (proof-proof-assume p cons-test nil))
      (at-atom (h1-propositions-select-value lib expansion assumed))
      (arguments (h1-book-witness-step-value at-cons))
      (arguments (proof-list-of-length (cdr arguments) 2))
      (quote-cons (h1-tactics-prover-solve
                   proof (proof-eq kwote-cons (list *proof-cons* quote-head quote-tail))
                   (list *h1-book-witness-kwote-list*) 160))
      (quoted-value (h1-tactics-prover-solve
                     proof (proof-eq (list value quote-head *library-y*) *library-x*)
                     (list value *h1-book-witness-kwote*) 160))
      (list-cons (h1-book-witness-requoted-list-cons lib values))
      (yes (h1-book-witness-requoted-list-yes lib original claim at-cons cons-test
                                              arguments quote-cons quoted-value list-cons))
      (no (h1-propositions-propositional-proof-reflexive lib original))
      (no (h1-propositions-rewrite-value lib no at-atom))
      (closed (h1-tactics-prover-solve
               proof (proof-eq (list values (list *h1-book-witness-kwote-list* *proof-false*)
                                     *proof-false*) *proof-false*)
               (list values *h1-book-witness-kwote-list*) 160))
      (symmetric (h1-propositions-proof-symmetric p at-atom))
      (no (proof-proof-chain p no (list closed symmetric)))
      (ordinal (descent-measure-ordinal lib measure))
      (cases (proof-proof-cases p cons-test yes no))
      (step (proof-proof-induct p ordinal cases claim measure (list pairs))))
     (h1-book-witness-evaluator-witness-lemma witness "REQUOTED-LIST" step))))

(defun h1-book-witness-requoted-value-steps (lib left right cons not-quote list-lemma)
  (let ((p (library-library-proof lib)))
    (proof-with-checked-results
     ((before (proof-proof-unfold p left))
      (before (h1-propositions-select-value lib before cons))
      (before (h1-propositions-select-value lib before not-quote))
      (argument (proof-term-at right 1))
      (parts (proof-list-of-length (cdr argument) 2)))
     (let ((head (car parts))
           (arguments (cadr parts)))
       (proof-with-checked-results
        ((on-cons (proof-proof-fact p "consp-cons"
                                    (list (list *library-x* head) (list *library-y* arguments))))
         (after (proof-proof-unfold p right))
         (after (h1-propositions-select-value lib after on-cons))
         (car-step (library-library-axiom lib "CAR-CONS" (list head arguments)))
         (after (h1-propositions-rewrite-value lib after car-step))
         (after (h1-propositions-select-value lib after not-quote))
         (cdr-step (library-library-axiom lib "CDR-CONS" (list head arguments)))
         (after (h1-propositions-rewrite-value lib after cdr-step))
         (list-step (proof-proof-fact p list-lemma
                                      (list (list *library-x* (list *library-cdr* *library-x*)))))
         (after (h1-propositions-rewrite-value lib after list-step))
         (symmetric (h1-propositions-proof-symmetric p after)))
        (proof-proof-chain p before (list symmetric)))))))

(defun h1-book-witness-evaluator-witness-requoted-value (witness canonical list-lemma)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (lib (h1-tactics-prover-library proof))
         (p (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
     ((premise (proof-term-at canonical 1))
      (equation (proof-term-at canonical 2))
      (sides (proof-list-of-length (cdr equation) 2))
      (assumed (proof-proof-assume p premise t))
      (parts (h1-propositions-propositional-proof-conjunct lib assumed))
      (checks (h1-propositions-propositional-proof-conjunct lib (cadr parts)))
      (cons-literal (proof-step-first (car parts)))
      (quote-literal (proof-step-first (cadr checks))))
     (if (and (equal cons-literal (list *proof-consp* *library-x*))
              (equal quote-literal (proof-neg (proof-eq (list *library-car* *library-x*)
                                                       *h1-book-witness-quote-name*))))
         (h1-book-witness-requoted-value-steps lib (car sides) (cadr sides)
                                               (car parts) (cadr checks) list-lemma)
       '(:failure "unproved" "")))))

(defund h1-book-witness-application-outcome (lib equation holds)
  (proof-with-checked-results
   ((right (h1-book-witness-step-value equation))
    (test (proof-term-at right 1))
    (assumed (proof-proof-assume (library-library-proof lib) test holds)))
   (h1-propositions-select-value lib equation assumed)))

(defun h1-book-witness-select-application (lib equation outcomes)
  (declare (xargs :measure (acl2-count outcomes)))
  (cond
   ((failure-p equation) equation)
   ((endp outcomes) equation)
   (t (h1-book-witness-select-application
       lib (h1-book-witness-application-outcome lib equation (car outcomes)) (cdr outcomes)))))

(defun h1-book-witness-evaluator-witness-application (witness)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (lib (h1-tactics-prover-library proof))
         (p (h1-tactics-prover-proof proof))
         (value (h1-book-witness-evaluator-witness-value witness))
         (premise (proof-ite (list *proof-consp* *library-x*)
                             (proof-eq (list *library-car* *library-x*) *library-z*)
                             *proof-false*))
         (label (concatenate 'string
                             (seq-slice (h1-book-witness-evaluator-witness-prefix witness) 3 :none)
                             "-APPLICATION")))
    (proof-with-checked-results
     ((assumed (proof-proof-assume p premise t))
      (parts (h1-propositions-propositional-proof-conjunct lib assumed))
      (equation (proof-proof-unfold p (list value *library-x* *library-y*)))
      (equation (h1-propositions-select-value lib equation (car parts)))
      (equation (h1-propositions-rewrite-value lib equation (cadr parts)))
      (equation (h1-book-witness-select-application lib equation '(nil nil t)))
      (result (proof-step-first equation))
      (implication (h1-propositions-propositional-proof-implies-from
                    lib (list *library-implies* premise result) equation))
      (literal (proof-step-first implication)))
     (let ((clause (list (proof-eq *library-z* *h1-book-witness-quote-name*)
                         (list *proof-consp* *library-z*)
                         (proof-neg (list *h1-tactics-symbolp* *library-z*))
                         literal)))
       (proof-with-checked-results
        ((step (proof-proof-subsume p implication clause))
         (proof (h1-book-witness-lemma proof label (car clause) step (cdr clause))))
        (cons (proof-sym (concatenate 'string "SELF-" label) "ACL2")
              (h1-book-witness-evaluator-witness-with-proof witness proof)))))))

(defund h1-book-witness-operation-guard (proof step test)
  (proof-with-checked-results
   ((value (h1-tactics-prover-constant proof test))
    (known (h1-book-witness-dispatch-test proof value)))
   (proof-proof-cut (h1-tactics-prover-proof proof) step known)))

(defun h1-book-witness-operation-guards (proof step tests)
  (declare (xargs :measure (acl2-count tests)))
  (cond
   ((failure-p step) step)
   ((endp tests) step)
   (t (h1-book-witness-operation-guards
       proof (h1-book-witness-operation-guard proof step (car tests)) (cdr tests)))))

(defund h1-book-witness-operation-projection (p step projection arguments used)
  (let ((position (car projection))
        (lemma (cadr projection)))
    (if (member-equal (list *library-car* (h1-book-witness-tail arguments position)) used)
        (proof-with-checked-results
         ((equation (proof-proof-fact
                     p lemma (list (list *library-x* (list *library-cdr* *library-x*))))))
         (proof-proof-rewrite-first p step equation))
      step)))

(defun h1-book-witness-operation-projections (p step projections arguments used)
  (declare (xargs :measure (acl2-count projections)))
  (cond
   ((failure-p step) step)
   ((endp projections) step)
   (t (h1-book-witness-operation-projections
       p (h1-book-witness-operation-projection p step (car projections) arguments used)
       (cdr projections) arguments used))))

(defun h1-book-witness-evaluator-witness-operation-case (witness formula operation projections application)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (p (h1-tactics-prover-proof proof))
         (actual (proof-quote operation))
         (tail (list *library-cdr* *library-x*))
         (arguments (list (h1-book-witness-evaluator-witness-values witness) tail *library-y*))
         (dispatch (h1-book-witness-dispatch-with-proof
                    (h1-book-witness-evaluator-witness-dispatch witness) proof)))
    (proof-with-checked-results
     ((step (proof-proof-fact p application (list (list *library-z* actual))))
      (step (h1-book-witness-operation-guards
             proof step (list (proof-eq actual *h1-book-witness-quote-name*)
                              (list *proof-consp* actual))))
      (symbol-step (h1-tactics-prover-constant proof (list *h1-tactics-symbolp* actual)))
      (test (h1-book-witness-dispatch-test proof symbol-step))
      (step (proof-proof-cut p test step))
      (dispatch-step (h1-book-witness-dispatch-evaluate dispatch operation *library-z*))
      (dispatch-step (proof-proof-instantiate p dispatch-step (list (list *library-z* arguments))))
      (step (proof-proof-rewrite p step dispatch-step '(1 2 2)))
      (literal (proof-step-first step))
      (equation (proof-term-at literal 2))
      (result (proof-term-at equation 2))
      (step (h1-book-witness-operation-projections
             p step projections arguments (h1-tactics-subterms result)))
      (literal (proof-step-first step)))
     (if (equal literal formula) step '(:failure "failure" "")))))

(defun h1-book-witness-protected-evaluator-terms (terms value values)
  (if (endp terms)
      nil
    (let ((head (h1-tactics-call-head (car terms))))
      (if (or (equal head value) (equal head values))
          (cons (car terms) (h1-book-witness-protected-evaluator-terms (cdr terms) value values))
        (h1-book-witness-protected-evaluator-terms (cdr terms) value values)))))

(defund h1-book-witness-structural-test (proof context test)
  (proof-with-checked-results ((known (h1-tactics-context-find context test)))
    (if (car known)
        known
      (proof-with-checked-results
       ((known (h1-tactics-context-find (cdr known) (proof-neg test))))
       (if (car known)
           known
         (h1-book-witness-exclude-by-type proof (cdr known) test))))))

(defund h1-book-witness-structural-selection (proof context equation right)
  (proof-with-checked-results ((value (h1-book-witness-step-value equation)))
    (cond
     ((equal value right) (list t equation context))
     ((not (proof-is-call value *proof-if*)) (list t nil context))
     (t
      (proof-with-checked-results
       ((test (proof-term-at value 1))
        (known (h1-book-witness-structural-test proof context test)))
       (if (not (car known))
           (list t nil (cdr known))
         (proof-with-checked-results
          ((equation (h1-propositions-select-value
                      (h1-tactics-prover-library proof) equation (car known))))
          (list nil equation (cdr known)))))))))

(defun h1-book-witness-structural-select (n proof context equation right)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h1-book-witness-structural-select")
    (proof-with-checked-results
     ((result (h1-book-witness-structural-selection proof context equation right)))
     (if (car result)
         (cons (cadr result) (caddr result))
       (h1-book-witness-structural-select (1- n) proof (caddr result) (cadr result) right)))))

(defun h1-book-witness-evaluator-witness-structural-case (witness left right premise)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (p (h1-tactics-prover-proof proof))
         (protected (proof-unique
                     (h1-book-witness-protected-evaluator-terms
                      (h1-tactics-subterms right)
                      (h1-book-witness-evaluator-witness-value witness)
                      (h1-book-witness-evaluator-witness-values witness))))
         (tests (list (list premise t))))
    (proof-with-checked-results
     ((head (proof-term-at left 0))
      (search (h1-tactics-search-init proof (list head) nil nil protected 8 nil))
      (context (h1-tactics-context-init search tests))
      (equation (proof-proof-unfold p left))
      (selected (h1-book-witness-structural-select 1000000 proof context equation right)))
     (if (car selected)
         (car selected)
       (proof-with-checked-results
        ((result (h1-tactics-search-prove (h1-tactics-context-search (cdr selected))
                                         (proof-eq left right) tests t)))
        (car result))))))

(defund h1-book-witness-evaluator-prove-case (witness item projections list-lemma application)
  (let* ((proof (h1-book-witness-evaluator-witness-proof witness))
         (lib (h1-tactics-prover-library proof))
         (p (h1-tactics-prover-proof proof))
         (obligation (car item))
         (bindings (cadr item))
         (canonical (caddr item))
         (operation (cadddr item)))
    (proof-with-checked-results
     ((parts (proof-list-of-length canonical 3))
      (sides (proof-list-of-length (cdr (caddr parts)) 2)))
     (let ((premise (cadr parts))
           (left (car sides))
           (right (cadr sides)))
       (proof-with-checked-results
        ((step
          (if operation
              (h1-book-witness-evaluator-witness-operation-case
               witness canonical operation projections application)
            (proof-with-checked-results
             ((cons-call (if (proof-is-call right (h1-book-witness-evaluator-witness-value witness))
                             (proof-term-at right 1)
                           nil))
              (step
               (if (proof-is-call cons-call *proof-cons*)
                   (h1-book-witness-evaluator-witness-requoted-value witness canonical list-lemma)
                 (h1-book-witness-evaluator-witness-structural-case witness left right premise))))
             (h1-propositions-propositional-proof-implies-from lib canonical step))))
         (step (proof-proof-instantiate p step (table-items bindings))))
        (proof-proof-subsume p step (list obligation)))))))

(defun h1-book-witness-evaluator-prove-cases (witness cases projections list-lemma application)
  (declare (xargs :measure (acl2-count cases)))
  (if (endp cases)
      nil
    (proof-with-checked-results
     ((step (h1-book-witness-evaluator-prove-case witness (car cases) projections list-lemma application))
      (rest (h1-book-witness-evaluator-prove-cases witness (cdr cases) projections list-lemma application)))
     (cons step rest))))

(defun h1-book-witness-evaluator-witness-prove (witness)
  (proof-with-checked-results
   ((projections (h1-book-witness-evaluator-witness-argument-projections witness))
    (list-lemma (h1-book-witness-evaluator-witness-requoted-list (cdr projections)))
    (application (h1-book-witness-evaluator-witness-application (cdr list-lemma))))
   (let* ((witness (cdr application))
          (name (h1-book-witness-evaluator-witness-name witness))
          (value (h1-book-witness-evaluator-witness-value witness))
          (values (h1-book-witness-evaluator-witness-values witness))
          (cases (h1-book-witness-evaluator-witness-cases witness)))
     (proof-with-checked-results
      ((steps (h1-book-witness-evaluator-prove-cases witness cases (car projections)
                                                    (car list-lemma) (car application)))
       (entry (proof-proof-entry "witness" name (list name value values) steps)))
      (cons entry witness)))))

(defun h1-book-witness-witness-entry (proof raw fields)
  (proof-with-checked-results ((functions (proof-term-at fields 0)))
    (if (equal (length functions) 1)
        (h1-book-witness-projection-witness proof raw fields)
      (proof-with-checked-results
       ((witness (h1-book-witness-evaluator-witness-init proof raw fields))
        (result (h1-book-witness-evaluator-witness-prove witness)))
       (cons (car result) (h1-book-witness-evaluator-witness-proof (cdr result)))))))

(defun h1-book-witness-equations-in-terms (terms evaluators equations)
  (if (endp terms)
      equations
    (let* ((head (h1-tactics-call-head (car terms)))
           (registered (table-get evaluators head nil)))
      (h1-book-witness-equations-in-terms (cdr terms) evaluators (append equations registered)))))

(defun h1-book-witness-equation-sort-keys (indexed)
  (if (endp indexed)
      nil
    (let* ((item (car indexed))
           (equation (cadr item)))
      (cons (list (car equation) (car item) equation)
            (h1-book-witness-equation-sort-keys (cdr indexed))))))

(defund h1-book-witness-add-evaluator-rule (p equation plan)
  (proof-with-checked-results
   ((equation (proof-list-of-length equation 2))
    (fact (proof-proof-fact p (car equation) nil))
    (rules (h1-tactics-rules-add-formula (car plan) fact t t)))
   (let ((operation (cadr equation))
         (openings (cdr plan)))
     (cons rules
           (if (assoc-equal operation (proof-proof-definitions p))
               (table-put openings operation 1)
             openings)))))

(defun h1-book-witness-add-evaluator-rules (p equations plan)
  (declare (xargs :measure (acl2-count equations)))
  (cond
   ((failure-p plan) plan)
   ((endp equations) plan)
   (t (h1-book-witness-add-evaluator-rules
       p (cdr equations) (h1-book-witness-add-evaluator-rule p (caddar equations) plan)))))

(defun h1-book-witness-open-short-functions (defs names openings)
  (if (endp names)
      openings
    (let* ((name (car names))
           (definition (assoc-equal name defs))
           (opening (<= (len (h1-tactics-subterms (caddr definition))) 12)))
      (h1-book-witness-open-short-functions
       defs (cdr names) (if opening (table-put openings name 1) openings)))))

(defun h1-book-witness-evaluator-openings (proof definitions names openings)
  (declare (xargs :measure (acl2-count names)))
  (if (endp names)
      openings
    (let* ((definition (assoc-equal (car names) definitions))
           (openings (if definition
                         (h1-book-witness-open-short-functions
                          definitions (h1-tactics-prover-functions-in proof (caddr definition)) openings)
                       openings)))
      (h1-book-witness-evaluator-openings proof definitions (cdr names) openings))))

(defun h1-book-witness-evaluator-proof (proof formula evaluators)
  (let* ((terms (h1-tactics-subterms formula))
         (equations (proof-unique (h1-book-witness-equations-in-terms terms evaluators nil))))
    (if (endp equations)
        '(:failure "unproved" "")
      (let* ((p (h1-tactics-prover-proof proof))
             (definitions (proof-proof-definitions p))
             (rules (h1-tactics-rules-init proof))
             (openings (h1-book-witness-table-from-keys
                        (h1-tactics-prover-functions-in proof formula) 1))
             (openings (table-put openings *proof-equal* 0))
             (equations (seq-sorted
                         (h1-book-witness-equation-sort-keys (seq-numbered equations 0)))))
        (proof-with-checked-results
         ((plan (h1-book-witness-add-evaluator-rules p equations (cons rules openings))))
         (let* ((openings (h1-book-witness-evaluator-openings
                           proof definitions (table-keys (cdr plan)) (cdr plan)))
                (search (h1-tactics-search-init proof openings (car plan) nil nil 18 t))
                (work (h1-tactics-search-work search))
                (search (if (eq work :none)
                            search
                          (h1-tactics-search-with-work search (* 4 work)))))
           (proof-with-checked-results ((result (h1-tactics-search-prove search formula nil t)))
             (car result))))))))
