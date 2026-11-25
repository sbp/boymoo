(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defun t3-book-measures-exported (definitions stored exported)
  (if (endp definitions)
      exported
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (let ((binding (assoc-equal (car definition) stored)))
        (t3-book-measures-exported (cdr definitions) stored
                                   (if binding
                                       (table-put exported (car binding) (cdr binding))
                                     exported))))))

(defun t3-book-measures-expand-measure (proof measure)
  (proof-with-checked-results ((function (t3-book-theorems-head measure)))
    (if (and (assoc-equal function (proof-proof-definitions proof))
             (not (member-equal function (list *library-count* *library-len* (proof-sym "NFIX" "ACL2")))))
        (proof-with-checked-results
         ((equation (proof-proof-unfold proof measure))
          (right (proof-rewritten-term equation)))
         (if (proof-is-call right *proof-plus*) right measure))
      measure)))

(defun t3-book-measures-expanded (proof exported)
  (if (endp exported)
      nil
    (proof-with-checked-results
     ((measure (t3-book-measures-expand-measure proof (cdar exported)))
      (rest (t3-book-measures-expanded proof (cdr exported))))
     (cons (cons (caar exported) measure) rest))))

(defun t3-book-measures-prepare-plans (lib rulers definitions stored)
  (proof-with-checked-results
   ((calls (termination-recursive-calls rulers definitions))
    (exported (t3-book-measures-exported definitions stored nil))
    (expanded (t3-book-measures-expanded (library-library-proof lib) exported)))
   (list calls exported expanded)))

(defun t3-book-measures-map-included-p (left right)
  (or (endp left)
      (and (equal (car left) (assoc-equal (caar left) right))
           (t3-book-measures-map-included-p (cdr left) right))))

(defun t3-book-measures-seen-plan-p (plan seen)
  (and (consp seen)
       (or (and (equal (len plan) (len (car seen)))
                (t3-book-measures-map-included-p plan (car seen)))
           (t3-book-measures-seen-plan-p plan (cdr seen)))))

(defund t3-book-measures-next-plan (definitions stored setup phase)
  (cond ((eq phase :done) nil)
        ((eq phase :expanded) (cons (caddr setup) :done))
        (t (proof-with-checked-results
            ((next (t3-tactics-measure-plan-next definitions (car setup) stored (cadr phase))))
            (if next
                (cons (car next) (list :inferred (cdr next)))
              (cons (cadr setup) :expanded))))))

(defun t3-book-measures-count-comparison (lib smaller larger evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((value (proof-term-at smaller 1))
      (parent (proof-term-at larger 1))
      (ordinal
       (if (equal value (list *t3-book-lemmas-set-tail* parent))
           (proof-with-checked-results
            ((nonempty (t3-logic-evidence-find evidence (proof-neg (list *t3-book-lemmas-empty* parent)))))
            (if (and (car nonempty) (assoc-equal (proof-sym "SELF-T3-SET-TAIL-COUNT" "ACL2")
                                                 (proof-proof-facts proof)))
                (proof-with-checked-results
                 ((step (library-library-cite lib "T3-SET-TAIL-COUNT" (list parent) (list (car nonempty)))))
                 (cons step (cdr nonempty)))
              '(:failure "unsupported" "")))
         (t3-size-count-descent lib smaller larger evidence)))
      (comparison (t3-size-ordinal-comparison lib smaller larger))
      (step (proof-proof-rewrite proof (car ordinal) comparison '(1)))
      (step (proof-proof-tidy proof step)))
     (cons step (cdr ordinal)))))

(defun t3-book-measures-length-comparison (lib smaller larger evidence)
  (proof-with-checked-results ((parent (proof-term-at larger 1)))
    (if (equal smaller (list *library-len* (list *library-cdr* parent)))
        (t3-size-length-tail lib parent evidence)
      (proof-with-checked-results ((value (proof-term-at smaller 1)))
        (if (not (proof-is-call value *t3-book-halves-mv-nth*))
            '(:failure "unsupported" "")
          (proof-with-checked-results ((parts (proof-list-of-length value 3)))
            (let ((index (cadr parts)))
              (if (and (equal (caddr parts) (list *t3-book-halves-halve* parent))
                       (member-equal index (list *proof-zero* *proof-one*)))
                  (proof-with-checked-results
                   ((cons (t3-logic-evidence-require evidence (list *proof-consp* parent)))
                    (tail (t3-logic-evidence-require (cdr cons) (list *proof-consp* (list *library-cdr* parent))))
                    (step (library-library-cite lib (concatenate 'string "T3-HALVE-LESS-" (decimal-text (cadr index)))
                                                (list parent) (list (car cons) (car tail)))))
                   (cons step (cdr tail)))
                '(:failure "unsupported" "")))))))))

(defun t3-book-measures-count-or-length (lib smaller larger evidence)
  (cond ((and (proof-is-call smaller *library-count*) (proof-is-call larger *library-count*))
         (t3-book-measures-count-comparison lib smaller larger evidence))
        ((and (proof-is-call smaller *library-len*) (proof-is-call larger *library-len*))
         (t3-book-measures-length-comparison lib smaller larger evidence))
        (t '(:failure "unsupported" ""))))

(defund t3-book-measures-shift (lib result offset prefix)
  (proof-with-checked-results ((step (t3-size-shift lib (car result) offset prefix nil)))
    (cons step (cdr result))))

(defun t3-book-measures-sum-decrease (lib smaller larger evidence)
  (declare (xargs :measure (acl2-count smaller)))
  (if (and (consp smaller) (proof-is-call smaller *proof-plus*) (proof-is-call larger *proof-plus*))
      (proof-with-checked-results
       ((parts (proof-list-of-length (cdr smaller) 2))
        (other (proof-list-of-length (cdr larger) 2)))
       (let ((a (car parts)) (b (cadr parts)) (c (car other)) (d (cadr other)))
         (cond
          ((equal a c)
           (proof-with-checked-results
            ((result (t3-book-measures-sum-decrease lib (caddr smaller) d evidence)))
            (t3-book-measures-shift lib result a t)))
          ((equal b d)
           (proof-with-checked-results
            ((result (t3-book-measures-sum-decrease lib (cadr smaller) c evidence)))
            (t3-book-measures-shift lib result b nil)))
          (t
           (proof-with-checked-results
            ((first (t3-book-measures-sum-decrease lib (cadr smaller) c evidence))
             (first (t3-book-measures-shift lib first b nil))
             (second (t3-book-measures-sum-decrease lib (caddr smaller) d (cdr first)))
             (second (t3-book-measures-shift lib second c t))
             (step (t3-size-chain lib (car first) (car second) nil)))
            (cons step (cdr second)))))))
    (t3-book-measures-count-or-length lib smaller larger evidence)))

(defun t3-book-measures-recoverable-failure-p (result)
  (and (failure-p result) (member-equal (cadr result) '("unproved" "unsupported" "value"))))

(defun t3-book-measures-note-facts (context facts)
  (declare (xargs :measure (acl2-count facts)))
  (if (or (endp facts) (failure-p context))
      context
    (t3-book-measures-note-facts (t3-book-theorems-context-note context (cdar facts)) (cdr facts))))

(defun t3-book-measures-ordinal-transport (lib smaller larger evidence quick)
  (proof-with-checked-results
   ((step (if quick quick
            (proof-with-checked-results ((bound (t3-book-measures-sum-decrease lib smaller larger evidence)))
              (car bound))))
    (comparison (t3-size-ordinal-comparison lib smaller larger)))
   (proof-proof-transport (library-library-proof lib) step comparison)))

(defun t3-book-measures-quick-ordinal (lib search a b context evidence)
  (let ((quick (t3-book-theorems-quick-result search (list *proof-less* a b) context 1)))
    (cond ((t3-book-measures-recoverable-failure-p (car quick)) (cons nil (cdr quick)))
          ((failure-p (car quick)) (car quick))
          (t (let ((step (t3-book-measures-ordinal-transport lib a b evidence (car quick))))
               (cond ((t3-book-measures-recoverable-failure-p step) (cons nil (cdr quick)))
                     ((failure-p step) step)
                     (t (cons step (cdr quick)))))))))

(defun t3-book-measures-prove-clause-search (lib search clause call error)
  (proof-with-checked-results
   ((search (t3-book-theorems-with-library search lib))
    (search (t3-book-theorems-theorems-with-fuel search 650))
    (context (t3-book-theorems-context-init lib nil))
    (evidence (t3-logic-evidence-init lib (and call (termination-call-tests call)) nil (list (proof-cl "EQL"))))
    (evidence (t3-logic-evidence-expand evidence))
    (context (t3-book-measures-note-facts context (t3-logic-evidence-facts evidence)))
    (goal (if (consp clause) (car (last clause)) (proof-term-at clause 0)))
    (equality (t3-book-values-book-proofs-normalize
               (t3-book-theorems-theorems-lib search) goal nil nil))
    (normalized (if equality (proof-rewritten-term equality) goal))
    (quick (t3-book-theorems-theorems-quick search normalized context 1))
    (quick
     (if (and (not (car quick)) (proof-is-call normalized *proof-ordinal-less*))
         (proof-with-checked-results ((parts (proof-list-of-length (cdr normalized) 2)))
           (t3-book-measures-quick-ordinal lib (cdr quick) (car parts) (cadr parts) context evidence))
       quick))
    (found
     (if (car quick)
         quick
       (let ((result (t3-book-theorems-theorems-prove (cdr quick) normalized context 12)))
         (cond ((and (failure-p result) (equal (cadr result) "unsupported")) error)
               ((failure-p result) result)
               (t (cons (car result) (cadr result)))))))
    (lib (t3-book-theorems-library (cdr found)))
    (step (if equality (proof-proof-transport (library-library-proof lib) (car found) equality)
            (car found))))
   (list step lib (cdr found))))

(defund t3-book-measures-prove-clause (lib search clause call)
  (let ((result (t3-tactics-descent lib clause call)))
    (cond ((t3-book-measures-recoverable-failure-p result)
           (t3-book-measures-prove-clause-search lib search clause call result))
          ((failure-p result) result)
          (t (list (caar result) (cdr result) (t3-book-theorems-with-library search (cdr result)))))))

(defund t3-book-measures-prove-obligation (lib search clause call)
  (let ((result (t3-book-measures-prove-clause lib search clause call)))
    (if (failure-p result)
        (list result lib search)
      (let* ((lib (cadr result))
             (step (proof-proof-subsume (library-library-proof lib) (car result) clause)))
        (list step lib (caddr result))))))

(defun t3-book-measures-prove-obligations (lib search obligations seen proofs)
  (declare (xargs :measure (acl2-count obligations)))
  (if (endp obligations)
      (list (reverse proofs) lib search)
    (let* ((item (car obligations))
           (clause (car item)))
      (if (member-equal clause seen)
          (t3-book-measures-prove-obligations lib search (cdr obligations) seen proofs)
        (let ((result (t3-book-measures-prove-obligation lib search clause (cadr item))))
          (if (failure-p (car result))
              result
            (t3-book-measures-prove-obligations (cadr result) (caddr result) (cdr obligations)
                                                (cons clause seen) (cons (car result) proofs))))))))

(defun t3-book-measures-entry-fields (definitions plan)
  (if (endp definitions)
      nil
    (let* ((name (caar definitions))
           (entry (assoc-equal name plan)))
      (if (not entry)
          '(:failure "failure" "")
        (proof-with-checked-results ((rest (t3-book-measures-entry-fields (cdr definitions) plan)))
          (cons (cdr entry) rest))))))

(defund t3-book-measures-try-plan (lib search definitions plan calls)
  (let ((cases (termination-obligation-cases definitions plan calls)))
    (if (failure-p cases)
        (list cases lib search)
      (t3-book-measures-prove-obligations lib search cases nil nil))))

(defun t3-book-measures-try-plans (n lib search definitions stored setup phase seen error)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-book-measures-measure-proof")
    (proof-with-checked-results ((next (t3-book-measures-next-plan definitions stored setup phase)))
      (if (not next)
          error
        (let ((plan (car next)))
          (if (or (not (equal (len plan) (len definitions))) (t3-book-measures-seen-plan-p plan seen))
              (t3-book-measures-try-plans (1- n) lib search definitions stored setup (cdr next) seen error)
            (let* ((result (t3-book-measures-try-plan lib search definitions plan (car setup)))
                   (proofs (car result))
                   (lib (cadr result))
                   (search (caddr result)))
              (cond
               ((t3-book-measures-recoverable-failure-p proofs)
                (t3-book-measures-try-plans (1- n) lib search definitions stored setup
                                           (cdr next) (cons plan seen) error))
               ((failure-p proofs) proofs)
               (t (proof-with-checked-results
                   ((fields (t3-book-measures-entry-fields definitions plan))
                    (entry (proof-proof-entry "measure" (caar definitions)
                                              (cons (caar definitions) fields) proofs)))
                   (list entry lib search)))))))))))

(defun t3-book-measures-fallback-library (lib definitions)
  (if (equal (caar definitions) *t3-genvar-genvar*)
      (let ((built (t3-genvar-build lib)))
        (if (failure-p built) lib built))
    lib))

(defun t3-book-measures-measure-proof (lib search rulers definitions stored)
  (let ((result (t3-tactics-termination lib rulers definitions stored)))
    (cond
     ((t3-book-measures-recoverable-failure-p result)
      (let* ((lib (t3-book-measures-fallback-library lib definitions))
             (search (t3-book-theorems-with-library search lib)))
        (proof-with-checked-results ((setup (t3-book-measures-prepare-plans lib rulers definitions stored)))
          (t3-book-measures-try-plans 1000000 lib search definitions stored setup '(:inferred :start) nil result))))
     ((failure-p result) result)
     (t (list (caar result) (cdr result) (t3-book-theorems-with-library search (cdr result)))))))
