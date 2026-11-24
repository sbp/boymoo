(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-primitive-apply-prim* (proof-sym "APPLY$-PRIM" "ACL2"))
(defconst *l1-primitive-hons-get* (proof-sym "HONS-GET" "ACL2"))
(defconst *l1-primitive-hons-assoc* (proof-sym "HONS-ASSOC-EQUAL" "ACL2"))
(defconst *l1-primitive-hons-equal* (proof-sym "HONS-EQUAL" "ACL2"))
(defconst *l1-primitive-eql* (proof-cl "EQL"))
(defconst *l1-primitive-key* (proof-sym "L1-LOOKUP-KEY" "ACL2"))
(defconst *l1-primitive-arguments* (proof-sym "L1-PRIMITIVE-ARGUMENTS" "ACL2"))
(defconst *l1-primitive-block-size* 32)
(defconst *l1-primitive-dispatch-block* 256)
(defconst *l1-primitive-alist-entry* (proof-sym "L1-ALIST-ENTRY" "ACL2"))
(defconst *l1-primitive-alist-miss* (proof-sym "L1-ALIST-MISS" "ACL2"))
(defconst *l1-primitive-absence-prefix* "L1-BADGE-ABSENT-")
(defconst *l1-primitive-absence-block-size* 48)
(defconst *l1-primitive-badge-exclusion* (proof-sym "L1-BADGE-EXCLUSION" "ACL2"))

(defun l1-primitive-cons-list (values tail)
  (if (endp values)
      tail
    (list *proof-cons* (car values) (l1-primitive-cons-list (cdr values) tail))))

(defun l1-primitive-arm-variable (index)
  (proof-sym (string-append "L1-ARM-" (decimal-text index)) "ACL2"))

(defun l1-primitive-step-term (step index)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun l1-primitive-require-table-entry (items key)
  (let ((entry (assoc-equal key items)))
    (if entry (cdr entry) '(:failure "MissingWarrantDependency" ""))))

(defun l1-primitive-shifted-arm-bindings (remaining index shift)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons (list (l1-primitive-arm-variable index)
                (l1-primitive-arm-variable (+ index shift)))
          (l1-primitive-shifted-arm-bindings (1- remaining) (1+ index) shift))))

; Each prefix equality leaves the unexamined suffix in Z.
(defun l1-primitive-false-prefix-rec (n proof length cache)
  (declare (xargs :measure (nfix n)))
  (let ((existing (assoc-equal length cache)))
    (cond (existing (cons (cdr existing) cache))
          ((zp n) '(:failure "Fuel" "l1-primitive-false-prefix"))
          ((or (equal length 0) (equal length -1))
           '(:failure "failure" ""))
          ((equal length 1)
           (proof-with-checked-results
               ((step (proof-proof-fact
                       proof "if-nil" (list (list *library-y* (l1-primitive-arm-variable 0))))))
             (cons step (table-put cache length step))))
          (t
           (let* ((middle (floor length 2))
                  (rest (- length middle)))
             (proof-with-checked-results
                 ((prefix (l1-primitive-false-prefix-rec (1- n) proof middle cache))
                  (suffix (l1-primitive-false-prefix-rec (1- n) proof rest (cdr prefix)))
                  (shifted (proof-proof-instantiate
                            proof (car suffix) (l1-primitive-shifted-arm-bindings rest 0 middle)))
                  (left (l1-primitive-step-term shifted 1))
                  (step (proof-proof-instantiate proof (car prefix) (list (list *library-z* left))))
                  (step (proof-proof-rewrite proof step shifted '(1 2))))
               (cons step (table-put (cdr suffix) length step))))))))

(defun l1-primitive-false-prefix (proof length cache)
  (l1-primitive-false-prefix-rec 1000000 proof length cache))

(defun l1-primitive-warrant-constant (proof term)
  (l1-application-proof-constant (proof-proof-with-kind proof :l1-warrant) term))

(defun l1-primitive-proof-simplify (proof term evidence definitions)
  (l1-application-proof-simplify proof term evidence definitions))

; Bind each arm to its placeholder after the tests have selected a branch.
(defun l1-primitive-mask-branches (tests index masked bindings)
  (if (endp tests)
      (list masked (reverse bindings))
    (proof-with-checked-results ((pair (proof-list-of-length (car tests) 2)))
      (let ((variable (l1-primitive-arm-variable index)))
        (l1-primitive-mask-branches
         (cdr tests) (1- index) (proof-ite (car pair) variable masked)
         (cons (list variable (cadr pair)) bindings))))))

(defund l1-primitive-rewrite-branch-test (proof cursor step count definitions)
  (proof-with-checked-results
      ((parts (proof-list-of-length (cdr cursor) 3))
       (result (l1-primitive-proof-simplify proof (car parts) nil definitions))
       (bit (l1-primitive-step-term result 2)))
    (if (not (or (equal bit *proof-false*) (equal bit *proof-true*)))
        '(:failure "failure" "")
      (proof-with-checked-results
          ((step (proof-proof-rewrite
                  proof step result (list* 1 2 (make-list-ac count 3 '(1))))))
        (cons step (equal bit *proof-true*))))))

(defun l1-primitive-collapse-branch-tests (remaining proof cursor step count definitions)
  (declare (xargs :measure (acl2-count remaining)))
  (if (or (endp remaining) (not (proof-is-call cursor *proof-if*)))
      (list step cursor count)
    (proof-with-checked-results
        ((decision (l1-primitive-rewrite-branch-test proof cursor step count definitions)))
      (if (cdr decision)
          (list (car decision) (proof-ite *proof-true* (caddr cursor) (cadddr cursor)) count)
        (l1-primitive-collapse-branch-tests (cdr remaining) proof (cadddr cursor)
                                            (car decision) (1+ count) definitions)))))

(defun l1-primitive-skip-branches-prefix (proof step cursor count)
  (if (zp count)
      step
    (proof-with-checked-results
        ((prefix (l1-primitive-false-prefix proof count nil))
         (law (proof-proof-instantiate proof (car prefix) (list (list *library-z* cursor)))))
      (proof-proof-rewrite proof step law '(1 2)))))

(defun l1-primitive-skip-branches (proof tests tail definitions)
  (proof-with-checked-results
      ((masked (l1-primitive-mask-branches
                (reverse tests) (1- (len tests)) *library-z* (list (list *library-z* tail))))
       (step (proof-proof-reflexive proof (car masked)))
       (collapsed (l1-primitive-collapse-branch-tests tests proof (car masked) step 0 definitions))
       (cursor (cadr collapsed))
       (step (l1-primitive-skip-branches-prefix proof (car collapsed) cursor (caddr collapsed)))
       (simplified (l1-primitive-proof-simplify proof cursor nil nil))
       (step (proof-proof-chain proof step (list simplified))))
    (proof-proof-instantiate proof step (cadr masked))))

(defun l1-primitive-dispatch-variables (remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons (proof-sym (string-append "L1-PRIMITIVE-ARGUMENT-" (decimal-text index)) "ACL2")
          (l1-primitive-dispatch-variables (1- remaining) (1+ index)))))

(defun l1-primitive-dispatch-tests (remaining code tail tests)
  (declare (xargs :measure (nfix remaining)))
  (if (or (zp remaining) (not (proof-is-call tail *proof-if*)))
      (list (reverse tests) tail)
    (proof-with-checked-results ((parts (proof-list-of-length (cdr tail) 3)))
      (let ((test (car parts)))
        (if (not (proof-is-call test *l1-primitive-eql*))
            '(:failure "failure" "")
          (proof-with-checked-results ((left (proof-term-at test 1)))
            (if (not (equal left code))
                '(:failure "failure" "")
              (proof-with-checked-results ((right (proof-term-at test 2)))
                (let ((tests (cons (list test (cadr parts)) tests))
                      (rest (caddr parts)))
                  (if (equal right code)
                      (list (reverse tests) rest)
                    (l1-primitive-dispatch-tests (1- remaining) code rest tests)))))))))))

(defund l1-primitive-dispatch-next (proof code step)
  (proof-with-checked-results ((tail (proof-rewritten-term step)))
    (if (not (proof-is-call tail *proof-if*))
        nil
      (proof-with-checked-results
          ((group (l1-primitive-dispatch-tests *l1-primitive-dispatch-block* code tail nil))
           (selected (l1-primitive-skip-branches proof (car group) (cadr group)
                                                 (list *l1-primitive-eql*))))
        (proof-proof-rewrite proof step selected '(1 2))))))

(defun l1-primitive-dispatch-skip (n proof code step)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "l1-primitive-dispatch")
    (proof-with-checked-results ((next (l1-primitive-dispatch-next proof code step)))
      (if next (l1-primitive-dispatch-skip (1- n) proof code next) step))))

(defun l1-primitive-dispatch-normalize (proof reduction step expected right)
  (if (equal right expected)
      step
    (proof-with-checked-results ((normal (l1-application-application-reduce reduction expected)))
      (if (not normal)
          step
        (proof-with-checked-results ((reversed (proof-proof-symmetric proof normal)))
          (proof-proof-chain proof step (list reversed)))))))

(defun l1-primitive-dispatch (proof function arity)
  (let ((code (proof-quote function))
        (variables (l1-primitive-dispatch-variables arity 0)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (list *l1-primitive-apply-prim* code *l1-primitive-arguments*)))
         (body (proof-rewritten-term opened))
         (definition (proof-proof-unfold proof body))
         (step (proof-proof-rewrite proof opened definition '(1 2)))
         (step (l1-primitive-dispatch-skip 1000000 proof code step))
         (args (l1-primitive-cons-list variables *proof-false*))
         (step (proof-proof-instantiate proof step (list (list *l1-primitive-arguments* args))))
         (reduction (l1-application-application-init proof function nil nil :default))
         (body (proof-rewritten-term step))
         (reduced (l1-application-application-reduce reduction body))
         (step (proof-proof-chain proof step (list reduced)))
         (expected (cons function variables))
         (right (proof-rewritten-term step))
         (step (l1-primitive-dispatch-normalize proof reduction step expected right))
         (right (proof-rewritten-term step)))
      (if (not (equal right expected))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof (list *l1-application-apply-primitive* code) t))
             (applied (l1-primitive-proof-simplify proof (list *l1-application-apply* code args)
                                                  (list assumed) (list *l1-application-apply*)))
             (step (proof-proof-chain proof applied (list step))))
          (list variables step))))))

(defun l1-primitive-make-certificates (proof entries)
  (list :l1-primitive-certificates proof entries))

(defun l1-primitive-certificates-init (proof)
  (l1-primitive-make-certificates proof nil))

(defun l1-primitive-certificates-proof (certificates)
  (cadr certificates))

(defun l1-primitive-certificates-entries (certificates)
  (caddr certificates))

(defun l1-primitive-certificates-with-proof (certificates proof)
  (l1-primitive-make-certificates proof (l1-primitive-certificates-entries certificates)))

(defun l1-primitive-certificates-record-lemma (certificates name clause count source)
  (let* ((proof (l1-primitive-certificates-proof certificates))
         (facts (table-put (proof-proof-facts proof) name clause))
         (proof (proof-proof-with-facts proof facts)))
    (proof-with-checked-results ((fact (proof-proof-fact proof name nil)))
      (cons fact (l1-primitive-make-certificates
                  proof (append (l1-primitive-certificates-entries certificates)
                                (list (list name count source))))))))

(defun l1-primitive-certificates-add (certificates name step)
  (let* ((proof (l1-primitive-certificates-proof certificates))
         (facts (proof-proof-facts proof)))
    (if (assoc-equal name facts)
        '(:failure "failure" "")
      (let ((clause (proof-step-clause step)))
        (proof-with-checked-results ((entry (proof-proof-entry "lemma" name (cons name clause) (list step))))
          (l1-primitive-certificates-record-lemma certificates name clause
                                                  (car (caddr entry)) (cadddr entry)))))))

(defun l1-primitive-certificates-close-facts (entries facts)
  (if (endp entries)
      facts
    (let ((name (caar entries)))
      (if (not (assoc-equal name facts))
          '(:failure "MissingWarrantDependency" "")
        (l1-primitive-certificates-close-facts (cdr entries) (table-delete facts name))))))

(defun l1-primitive-certificates-close (certificates)
  (let ((proof (l1-primitive-certificates-proof certificates)))
    (proof-with-checked-results
        ((facts (l1-primitive-certificates-close-facts
                 (l1-primitive-certificates-entries certificates) (proof-proof-facts proof))))
      (l1-primitive-certificates-with-proof certificates (proof-proof-with-facts proof facts)))))

(defun l1-primitive-table-tail-new (rows text start)
  (list :l1-primitive-table-tail rows text start))

(defun l1-primitive-table-tail-rows (tail)
  (cadr tail))

(defun l1-primitive-table-tail-proof-text (tail)
  (string-append "(" (string-append (seq-slice (caddr tail) (cadddr tail) :none) ")")))

(defun l1-primitive-make-badge-table (certificates rows row-text starts blocks queries)
  (list :l1-primitive-badge-table certificates rows row-text starts blocks queries))

(defun l1-primitive-badge-table-certificates (table)
  (cadr table))

(defun l1-primitive-badge-table-proof (table)
  (l1-primitive-certificates-proof (l1-primitive-badge-table-certificates table)))

(defun l1-primitive-badge-table-rows (table)
  (caddr table))

(defun l1-primitive-badge-table-row-text (table)
  (cadddr table))

(defun l1-primitive-badge-table-starts (table)
  (nth 4 table))

(defun l1-primitive-badge-table-blocks (table)
  (nth 5 table))

(defun l1-primitive-badge-table-queries (table)
  (nth 6 table))

(defun l1-primitive-badge-table-with-certificates (table certificates)
  (update-nth 1 certificates table))

(defun l1-primitive-badge-table-with-blocks (table blocks)
  (update-nth 5 blocks table))

(defun l1-primitive-badge-table-with-queries (table queries)
  (update-nth 6 queries table))

(defun l1-primitive-badge-table-row-starts (rows start)
  (if (endp rows)
      nil
    (cons start (l1-primitive-badge-table-row-starts (cdr rows)
                                                    (+ start (length (car rows)) 1)))))

(defun l1-primitive-badge-table-init (certificates)
  (let* ((proof (l1-primitive-certificates-proof certificates))
         (definitions (proof-proof-definitions proof)))
    (proof-with-checked-results
        ((definition (l1-primitive-require-table-entry definitions *l1-application-badge-primitive*))
         (term (proof-term-at definition 1)))
      (if (not (proof-is-call term *library-cdr*))
          '(:failure "failure" "")
        (proof-with-checked-results ((lookup (proof-term-at term 1)))
          (if (not (proof-is-call lookup *l1-primitive-hons-get*))
              '(:failure "failure" "")
            (proof-with-checked-results
                ((quoted (proof-term-at lookup 2))
                 (rows (proof-term-at quoted 1))
                 (text (proof-write-list rows)))
              (l1-primitive-make-badge-table certificates rows (text-join " " text)
                                             (l1-primitive-badge-table-row-starts text 0)
                                             nil 0))))))))

(defun l1-primitive-badge-table-quoted-tail (table index)
  (let* ((rows (l1-primitive-badge-table-rows table))
         (size (len rows))
         (offset (if (< index 0) (+ size index) index)))
    (cond ((equal index size) *proof-false*)
          ((or (< offset 0) (<= (len (l1-primitive-badge-table-starts table)) offset))
           '(:failure "failure" ""))
          (t (proof-quote
              (l1-primitive-table-tail-rows
               (l1-primitive-table-tail-new
                (nthcdr offset rows) (l1-primitive-badge-table-row-text table)
                (nth offset (l1-primitive-badge-table-starts table)))))))))

(defun l1-primitive-badge-table-entry-equation (table)
  (let* ((certificates (l1-primitive-badge-table-certificates table))
         (proof (l1-primitive-certificates-proof certificates))
         (row (list *proof-cons* *library-x* *library-y*))
         (nested (list *l1-primitive-hons-assoc* *l1-primitive-key*
                       (list *proof-cons* row *library-z*))))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof nested))
         (application (l1-application-application-init proof *l1-primitive-hons-assoc*
                                                        nil nil :default))
         (body (proof-rewritten-term opened))
         (reduced (l1-application-application-reduce application body))
         (step (proof-proof-chain proof opened (list reduced)))
         (right (proof-rewritten-term step)))
      (if (not (equal right (proof-ite (proof-eq *l1-primitive-key* *library-x*) row
                                       (list *l1-primitive-hons-assoc* *l1-primitive-key* *library-z*))))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((added (l1-primitive-certificates-add certificates *l1-primitive-alist-entry* step)))
          (l1-primitive-badge-table-with-certificates table (cdr added)))))))

(defund l1-primitive-badge-table-block-row (proof row step)
  (proof-with-checked-results
      ((key (proof-term-at row 0))
       (key (proof-quote key))
       (payload (proof-quote (cdr row)))
       (left (l1-primitive-step-term step 1))
       (tail (proof-term-at left 2))
       (next-row (proof-proof-fact proof *l1-primitive-alist-entry*
                                  (list (list *library-x* key) (list *library-y* payload)
                                        (list *library-z* tail))))
       (value (proof-proof-compute proof (list *proof-cons* key payload) row))
       (next-row (proof-proof-rewrite proof next-row value '(1 1 2 1)))
       (next-row (proof-proof-rewrite proof next-row value '(1 2 2))))
    (proof-proof-rewrite proof next-row step '(1 2 3))))

(defun l1-primitive-badge-table-block-rows (proof rows step)
  (if (endp rows)
      step
    (proof-with-checked-results
        ((step (l1-primitive-badge-table-block-row proof (car rows) step)))
      (l1-primitive-badge-table-block-rows proof (cdr rows) step))))

(defun l1-primitive-badge-table-indexed-rows (table index)
  (let* ((rows (l1-primitive-badge-table-rows table))
         (size (len rows))
         (offset (if (< index 0) (+ size index) index)))
    (if (or (< offset 0) (<= size offset))
        (proof-term-at rows size)
      (nthcdr offset rows))))

(defund l1-primitive-badge-table-pack-cell (index depth table proof step)
  (proof-with-checked-results
      ((rows (l1-primitive-badge-table-indexed-rows table index))
       (tail (l1-primitive-badge-table-quoted-tail table (1+ index)))
       (value (proof-proof-compute proof (list *proof-cons* (proof-quote (car rows)) tail) rows)))
    (proof-proof-rewrite proof step value (list* 1 1 2 (make-list-ac depth 2 nil)))))

; Evaluate the left side's cons cells from the end of the block to its start.
(defun l1-primitive-badge-table-block-pack (remaining index table proof step)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      step
    (proof-with-checked-results
        ((step (l1-primitive-badge-table-pack-cell index (1- remaining) table proof step)))
      (l1-primitive-badge-table-block-pack (1- remaining) (1- index) table proof step))))

(defun l1-primitive-badge-table-block (table start end)
  (let* ((certificates (l1-primitive-badge-table-certificates table))
         (proof (l1-primitive-certificates-proof certificates))
         (rows (l1-primitive-badge-table-rows table)))
    (proof-with-checked-results
        ((step (proof-proof-reflexive proof (list *l1-primitive-hons-assoc* *l1-primitive-key* *library-z*)))
         (step (l1-primitive-badge-table-block-rows proof (reverse (seq-slice rows start end)) step))
         (tail (l1-primitive-badge-table-quoted-tail table end))
         (step (proof-proof-instantiate proof step (list (list *library-z* tail))))
         (step (l1-primitive-badge-table-block-pack (- end start) (1- end) table proof step))
         (name (proof-sym (string-append "L1-BADGE-TABLE-" (decimal-text start)) "ACL2"))
         (blocks (table-put (l1-primitive-badge-table-blocks table) start (list end name)))
         (table (l1-primitive-badge-table-with-blocks table blocks))
         (added (l1-primitive-certificates-add certificates name step)))
      (l1-primitive-badge-table-with-certificates table (cdr added)))))

(defun l1-primitive-badge-table-tests (rows code)
  (if (endp rows)
      nil
    (proof-with-checked-results
        ((key (proof-term-at (car rows) 0))
         (rest (l1-primitive-badge-table-tests (cdr rows) code)))
      (cons (list (proof-eq code (proof-quote key)) (proof-quote (car rows))) rest))))

(defun l1-primitive-badge-table-lookup-block (table step code suffix)
  (let* ((rows (l1-primitive-badge-table-rows table))
         (size (len rows))
         (start (- size (length suffix))))
    (proof-with-checked-results
        ((table (if (assoc-equal start (l1-primitive-badge-table-blocks table))
                    table
                  (l1-primitive-badge-table-block table start
                                                 (min (+ start *l1-primitive-block-size*) size))))
         (block (l1-primitive-require-table-entry (l1-primitive-badge-table-blocks table) start))
         (end (car block))
         (lemma (cadr block))
         (proof (l1-primitive-badge-table-proof table))
         (equation (proof-proof-fact proof lemma (list (list *l1-primitive-key* code))))
         (tests (l1-primitive-badge-table-tests (seq-slice rows start end) code))
         (tail (l1-primitive-badge-table-quoted-tail table end))
         (selected (l1-primitive-skip-branches proof tests (list *l1-primitive-hons-assoc* code tail) nil))
         (equation (proof-proof-rewrite proof equation selected '(1 2)))
         (step (proof-proof-rewrite proof step equation '(1 2))))
      (cons step table))))

(defund l1-primitive-badge-table-lookup-next (table step code)
  (proof-with-checked-results ((right (proof-rewritten-term step)))
    (if (equal right (list *l1-primitive-hons-assoc* code *proof-false*))
        (let ((proof (l1-primitive-badge-table-proof table)))
          (proof-with-checked-results
              ((simplified (l1-primitive-proof-simplify proof right nil
                                                       (list *l1-primitive-hons-assoc*
                                                             (proof-cl "ATOM") *proof-not*)))
               (step (proof-proof-chain proof step (list simplified))))
            (cons nil (cons step table))))
      (proof-with-checked-results
          ((quoted (proof-term-at right 2))
           (suffix (proof-term-at quoted 1))
           (result (l1-primitive-badge-table-lookup-block table step code suffix))
           (right (proof-rewritten-term (car result))))
        (cons (not (proof-is-call right *proof-quote*)) result)))))

(defun l1-primitive-badge-table-lookup-steps (n table step code)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "l1-primitive-badge-table-lookup-steps")
    (proof-with-checked-results ((next (l1-primitive-badge-table-lookup-next table step code)))
      (if (car next)
          (l1-primitive-badge-table-lookup-steps (1- n) (cddr next) (cadr next) code)
        (cdr next)))))

(defun l1-primitive-badge-table-lookup (table function)
  (let ((proof (l1-primitive-badge-table-proof table))
        (code (proof-quote function)))
    (proof-with-checked-results
        ((tail (l1-primitive-badge-table-quoted-tail table 0))
         (opened (proof-proof-unfold proof (list *l1-primitive-hons-get* code tail))))
      (l1-primitive-badge-table-lookup-steps 1000000 table opened code))))

(defun l1-primitive-badge-table-witnesses-denied (table proof tested)
  (proof-with-checked-results
      ((right (proof-rewritten-term tested))
       (simplified (l1-primitive-proof-simplify proof right nil nil))
       (tested (proof-proof-chain proof tested (list simplified)))
       (not-nil (proof-proof-not-nil proof))
       (left (l1-primitive-step-term tested 1))
       (reflexive (proof-proof-reflexive proof (proof-neg left)))
       (rewritten (proof-proof-rewrite proof reflexive tested '(1 2 1)))
       (denied (proof-proof-transport proof not-nil rewritten)))
    (cons (list denied nil) table)))

(defun l1-primitive-badge-table-witnesses-present (table proof code tested value right)
  (proof-with-checked-results
      ((found (proof-proof-nil-or-true proof right))
       (first (proof-step-first found))
       (computed (proof-proof-compute proof first *proof-nil*))
       (nonnil (proof-proof-rewrite proof found computed '(1)))
       (nonnil (proof-proof-tidy proof nonnil))
       (test (proof-rewritten-term tested))
       (selected (proof-proof-select proof test nonnil))
       (tested (proof-proof-chain proof tested (list selected)))
       (primitive (proof-proof-true-from-eq proof tested))
       (badge (proof-proof-unfold proof (list *l1-application-badge-primitive* code)))
       (badge (proof-proof-rewrite proof badge value '(1 2 1)))
       (right (proof-rewritten-term badge))
       (simplified (l1-primitive-proof-simplify proof right nil nil))
       (badge (proof-proof-chain proof badge (list simplified)))
       (opened (l1-primitive-proof-simplify proof (list *l1-application-badge* code)
                                           (list primitive) (list *l1-application-badge*)))
       (badge (proof-proof-chain proof opened (list badge))))
    (cons (list primitive badge) table)))

(defun l1-primitive-badge-table-witnesses (table function)
  (let* ((code (proof-quote function))
         (queries (l1-primitive-badge-table-queries table))
         (name (proof-sym (string-append "L1-BADGE-LOOKUP-" (decimal-text queries)) "ACL2")))
    (proof-with-checked-results
        ((lookup (l1-primitive-badge-table-lookup table function))
         (table (cdr lookup))
         (added (l1-primitive-certificates-add
                 (l1-primitive-badge-table-certificates table) name (car lookup)))
         (value (car added))
         (table (l1-primitive-badge-table-with-certificates table (cdr added)))
         (table (l1-primitive-badge-table-with-queries table (1+ queries)))
         (proof (l1-primitive-badge-table-proof table))
         (opened (proof-proof-unfold proof (list *l1-application-apply-primitive* code)))
         (tested (proof-proof-rewrite proof opened value '(1 2 1)))
         (right (proof-rewritten-term value)))
      (if (equal right *proof-false*)
          (l1-primitive-badge-table-witnesses-denied table proof tested)
        (l1-primitive-badge-table-witnesses-present table proof code tested value right)))))

(defun l1-primitive-badge-table-miss-equation (table)
  (let ((proof (l1-primitive-badge-table-proof table))
        (certificates (l1-primitive-badge-table-certificates table)))
    (proof-with-checked-results
        ((entry (proof-proof-fact proof *l1-primitive-alist-entry* nil))
         (selection (proof-proof-if-false proof (proof-rewritten-term entry)))
         (miss (proof-proof-rewrite proof entry selection '(1 2)))
         (added (l1-primitive-certificates-add certificates *l1-primitive-alist-miss* miss)))
      (l1-primitive-badge-table-with-certificates table (cdr added)))))

(defun l1-primitive-badge-table-miss-row (proof row)
  (let ((key (proof-quote (car row)))
        (payload (proof-quote (cdr row))))
    (proof-with-checked-results
        ((miss (proof-proof-fact proof *l1-primitive-alist-miss*
                                (list (list *library-x* key) (list *library-y* payload))))
         (entry (proof-proof-compute proof (list *proof-cons* key payload) row)))
      (proof-proof-rewrite proof miss entry '(1 1 2 1)))))

; Each row leaves equality to its key as a side literal.
(defun l1-primitive-badge-table-miss-rows (rows proof step)
  (if (endp rows)
      step
    (let ((cell (list *proof-cons* (proof-quote (car rows)) *library-z*)))
      (proof-with-checked-results
          ((extended (proof-proof-instantiate proof step (list (list *library-z* cell))))
           (miss (l1-primitive-badge-table-miss-row proof (car rows)))
           (step (proof-proof-rewrite proof extended miss '(1 2))))
        (l1-primitive-badge-table-miss-rows (cdr rows) proof step)))))

(defun l1-primitive-badge-table-absence-block (table start end)
  (let ((proof (l1-primitive-badge-table-proof table))
        (certificates (l1-primitive-badge-table-certificates table))
        (name (proof-sym (string-append *l1-primitive-absence-prefix* (decimal-text start)) "ACL2")))
    (proof-with-checked-results
        ((step (proof-proof-reflexive
                proof (list *l1-primitive-hons-assoc* *l1-primitive-key* *library-z*)))
         (rows (seq-slice (l1-primitive-badge-table-rows table) start end))
         (step (l1-primitive-badge-table-miss-rows rows proof step))
         (tail (l1-primitive-badge-table-quoted-tail table end))
         (step (proof-proof-instantiate proof step (list (list *library-z* tail))))
         (step (l1-primitive-badge-table-block-pack (- end start) (1- end) table proof step))
         (added (l1-primitive-certificates-add certificates name step)))
      (cons name (l1-primitive-badge-table-with-certificates table (cdr added))))))

(defun l1-primitive-badge-table-absence-blocks (end table names)
  (declare (xargs :measure (nfix end)))
  (if (zp end)
      (cons names table)
    (let ((start (max 0 (- end *l1-primitive-absence-block-size*))))
      (proof-with-checked-results
          ((block (l1-primitive-badge-table-absence-block table start end)))
        (l1-primitive-badge-table-absence-blocks start (cdr block) (cons (car block) names))))))

(defun l1-primitive-badge-table-apply-absence-blocks (names proof step)
  (if (endp names)
      step
    (proof-with-checked-results
        ((block (proof-proof-fact proof (car names) nil))
         (step (proof-proof-rewrite proof step block '(1 2 1))))
      (l1-primitive-badge-table-apply-absence-blocks (cdr names) proof step))))

(defun l1-primitive-badge-table-exclusion (table)
  (let ((key *l1-primitive-key*))
    (proof-with-checked-results
        ((table (l1-primitive-badge-table-entry-equation table))
         (table (l1-primitive-badge-table-miss-equation table))
         (blocks (l1-primitive-badge-table-absence-blocks
                  (len (l1-primitive-badge-table-rows table)) table nil))
         (table (cdr blocks))
         (proof (l1-primitive-badge-table-proof table))
         (tail (l1-primitive-badge-table-quoted-tail table 0))
         (lookup (proof-proof-unfold proof (list *l1-primitive-hons-get* key tail)))
         (opened (proof-proof-unfold proof (list *l1-application-apply-primitive* key)))
         (tested (proof-proof-rewrite proof opened lookup '(1 2 1)))
         (tested (l1-primitive-badge-table-apply-absence-blocks (car blocks) proof tested))
         (empty (l1-primitive-proof-simplify
                 proof (list *l1-primitive-hons-assoc* key *proof-false*)
                 nil (list *l1-primitive-hons-assoc* (proof-cl "ATOM") *proof-not*)))
         (tested (proof-proof-rewrite proof tested empty '(1 2 1)))
         (denied (l1-primitive-badge-table-witnesses-denied table proof tested))
         (added (l1-primitive-certificates-add (l1-primitive-badge-table-certificates table)
                                               *l1-primitive-badge-exclusion* (caar denied))))
      (l1-primitive-badge-table-with-certificates table (cdr added)))))

; A computation and substitution replace each side literal by quoted NIL.
(defun l1-primitive-badge-table-discharge-keys (tests position previous reversed)
  (if (endp tests)
      (cons previous (reverse reversed))
    (proof-with-checked-results
        ((different (proof-line "compute" (list (car tests))))
         (rewrite-line (proof-line "substitute" (list (1+ previous) previous position))))
      (l1-primitive-badge-table-discharge-keys
       (cdr tests) (1+ position) (+ previous 2) (list* rewrite-line different reversed)))))

(defun l1-primitive-badge-table-use-exclusion (table function name)
  (let ((proof (l1-primitive-badge-table-proof table))
        (certificates (l1-primitive-badge-table-certificates table))
        (binding (list (list *l1-primitive-key* (proof-quote function)))))
    (if (assoc-equal name (proof-proof-facts proof))
        '(:failure "failure" "")
      (proof-with-checked-results
          ((instance (proof-proof-fact proof *l1-primitive-badge-exclusion* binding))
           (claim (proof-step-first instance))
           (head (proof-line "lemma" (list name claim)))
           (fact (proof-line "fact" (list *l1-primitive-badge-exclusion*)))
           (specialize (proof-line "instantiate" (list 1 binding)))
           (body (l1-primitive-badge-table-discharge-keys
                  (cdr (proof-step-clause instance)) 2 2 (list specialize fact)))
           (finish (proof-line "subsume" (list (car body) claim)))
           (source (text-join "" (cons head (append (cdr body) (list finish (proof-line "qed" nil))))))
           (added (l1-primitive-certificates-record-lemma
                   certificates name (list claim) (1+ (car body)) source)))
        (cons (list (car added) nil) (l1-primitive-badge-table-with-certificates table (cdr added)))))))

(defun l1-primitive-badge-table-absence (table function name)
  (let ((rows (l1-primitive-badge-table-rows table)))
    (and (consp rows)
         (not (assoc-equal function rows))
         (proof-with-checked-results
             ((table (l1-primitive-badge-table-exclusion table)))
           (l1-primitive-badge-table-use-exclusion table function name)))))

(defun l1-primitive-discharge-primitives-find-badge (function table members badges)
  (if (assoc-equal function members)
      (list table members badges)
    (let ((index (decimal-text (len members))))
      (proof-with-checked-results
          ((witnesses (l1-primitive-badge-table-witnesses table function))
           (member (caar witnesses))
           (badge (cadar witnesses))
           (table (cdr witnesses))
           (certificates (l1-primitive-badge-table-certificates table))
           (name (proof-sym (string-append "L1-PRIMITIVE-MEMBER-" index) "ACL2"))
           (added (l1-primitive-certificates-add certificates name member))
           (members (table-put members function (car added)))
           (certificates (cdr added))
           (table (l1-primitive-badge-table-with-certificates table certificates)))
        (if (not badge)
            (list table members badges)
          (proof-with-checked-results
              ((name (proof-sym (string-append "L1-PRIMITIVE-BADGE-" index) "ACL2"))
               (added (l1-primitive-certificates-add certificates name badge)))
            (list (l1-primitive-badge-table-with-certificates table (cdr added))
                  members (table-put badges function (car added)))))))))

(defun l1-primitive-discharge-primitives-badge-evidence
    (proof left function members badges user-badge)
  (proof-with-checked-results
      ((user-left (and user-badge (proof-term-at user-badge 1)))
       (user-code (and user-badge (proof-term-at user-left 1))))
    (if (and user-badge (equal user-code (cadr left)))
        (proof-with-checked-results
            ((member (l1-primitive-require-table-entry members function))
             (opened (l1-primitive-proof-simplify proof left (list member)
                                                  (list *l1-application-badge* (proof-cl "EQ")
                                                        *l1-primitive-eql*)))
             (assumed (proof-proof-assume proof user-badge t)))
          (proof-proof-chain proof opened (list assumed)))
      (l1-primitive-require-table-entry badges function))))

(defun l1-primitive-discharge-primitives-dispatch (proof table function right members applications)
  (if (assoc-equal function applications)
      (cons applications table)
    (proof-with-checked-results
        ((dispatched (l1-primitive-dispatch proof function (1- (length right))))
         (member (l1-primitive-require-table-entry members function))
         (branch (proof-proof-discharge proof (cadr dispatched) member))
         (name (proof-sym (string-append "L1-PRIMITIVE-DISPATCH-" (decimal-text (len applications))) "ACL2"))
         (added (l1-primitive-certificates-add
                 (l1-primitive-badge-table-certificates table) name branch))
         (applications (table-put applications function (list (car dispatched) (car added)))))
      (cons applications (l1-primitive-badge-table-with-certificates table (cdr added))))))

(defun l1-primitive-discharge-primitives-application
    (table left right function members badges applications)
  (if (not (proof-is-call left *l1-application-apply*))
      '(:failure "failure" "")
    (proof-with-checked-results ((head (proof-term-at right 0)))
      (if (not (equal head function))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((proof (l1-primitive-badge-table-proof table))
             (dispatched (l1-primitive-discharge-primitives-dispatch
                          proof table function right members applications))
             (applications (car dispatched))
             (table (cdr dispatched))
             (branch (l1-primitive-require-table-entry applications function))
             (proof (l1-primitive-badge-table-proof table))
             (evidence (proof-proof-instantiate proof (cadr branch) (seq-zip (car branch) (cdr right)))))
          (list evidence table members badges applications))))))

(defun l1-primitive-discharge-primitives-equality
    (table side members badges applications user-badge)
  (if (not (proof-is-call side *proof-not*))
      '(:failure "failure" "")
    (proof-with-checked-results ((equality (proof-term-at side 1)))
      (if (not (proof-is-call equality *proof-equal*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((pair (proof-list-of-length (cdr equality) 2))
             (left (car pair))
             (right (cadr pair))
             (code (proof-term-at left 1))
             (function (proof-term-at code 1))
             (found (l1-primitive-discharge-primitives-find-badge function table members badges))
             (table (car found))
             (members (cadr found))
             (badges (caddr found)))
          (if (proof-is-call left *l1-application-badge*)
              (proof-with-checked-results
                  ((evidence (l1-primitive-discharge-primitives-badge-evidence
                              (l1-primitive-badge-table-proof table) left function
                              members badges user-badge)))
                (list evidence table members badges applications))
            (l1-primitive-discharge-primitives-application
             table left right function members badges applications)))))))

(defun l1-primitive-discharge-primitives-side
    (table side members badges applications user-badge)
  (if (proof-is-call side *l1-application-apply-primitive*)
      (proof-with-checked-results
          ((code (proof-term-at side 1))
           (function (proof-term-at code 1))
           (found (l1-primitive-discharge-primitives-find-badge function table members badges))
           (table (car found))
           (members (cadr found))
           (badges (caddr found))
           (evidence (l1-primitive-require-table-entry members function)))
        (list evidence table members badges applications))
    (l1-primitive-discharge-primitives-equality table side members badges applications user-badge)))

(defund l1-primitive-discharge-primitives-advance
    (table step side members badges applications user-badge)
  (proof-with-checked-results
      ((result (l1-primitive-discharge-primitives-side
                table side members badges applications user-badge))
       (proof (l1-primitive-badge-table-proof (cadr result)))
       (step (proof-proof-discharge proof step (car result))))
    (cons step (cdr result))))

(defun l1-primitive-discharge-primitives-sides
    (table step sides members badges applications user-badge)
  (declare (xargs :measure (acl2-count sides)))
  (if (endp sides)
      (proof-with-checked-results
          ((first (proof-step-first step))
           (clause (if user-badge (list first (proof-neg user-badge)) (list first)))
           (proof (l1-primitive-badge-table-proof table))
           (step (proof-proof-subsume proof step clause)))
        (cons step (l1-primitive-badge-table-certificates table)))
    (proof-with-checked-results
        ((result (l1-primitive-discharge-primitives-advance
                  table step (car sides) members badges applications user-badge)))
      (l1-primitive-discharge-primitives-sides
       (cadr result) (car result) (cdr sides)
       (caddr result) (cadddr result) (nth 4 result) user-badge))))

(defun l1-primitive-discharge-primitives (certificates step user-badge)
  (proof-with-checked-results
      ((table (l1-primitive-badge-table-init certificates))
       (table (l1-primitive-badge-table-entry-equation table)))
    (l1-primitive-discharge-primitives-sides
     table step (cdr (proof-step-clause step)) nil nil nil user-badge)))
