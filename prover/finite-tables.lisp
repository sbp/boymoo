(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defmacro finite-tables-let* (bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings)))
      `(let (,binding)
         (if (failure-p ,(car binding))
             ,(car binding)
           (finite-tables-let* ,(cdr bindings) ,body))))))

(mutual-recursion
 (defun finite-tables-table-values (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((proof-is-call term *proof-quote*) (list term))
         ((and (consp term) (proof-is-call term *proof-if*))
          (finite-tables-table-branches (cddr term)))
         (t *terms-unproved*)))
 (defun finite-tables-table-branches (branches)
   (declare (xargs :measure (acl2-count branches)))
   (if (endp branches)
       nil
     (finite-tables-let*
      ((first (finite-tables-table-values (car branches)))
       (rest (finite-tables-table-branches (cdr branches))))
      (append first rest)))))

(defun finite-tables-integerp (value)
  (or (integerp value) (eq value t)))

(defun finite-tables-integer (value)
  (if (eq value t) 1 value))

(defun finite-tables-known-bounds (value known)
  (if (endp known)
      nil
    (let ((term (caar known)))
      (cond ((not (proof-is-call term *proof-less*))
             (finite-tables-known-bounds value (cdr known)))
            ((not (consp (cdr term))) '(:failure "failure" ""))
            ((not (equal (cadr term) value))
             (finite-tables-known-bounds value (cdr known)))
            ((not (consp (cddr term))) '(:failure "failure" ""))
            ((not (proof-is-call (caddr term) *proof-quote*))
             (finite-tables-known-bounds value (cdr known)))
            ((not (consp (cdaddr term))) '(:failure "failure" ""))
            (t (finite-tables-let*
                ((rest (finite-tables-known-bounds value (cdr known))))
                (if (finite-tables-integerp (cadr (caddr term)))
                    (cons (cdar known) rest)
                  rest)))))))

(defun finite-tables-bound-number (step)
  (finite-tables-let* ((literal (proof-step-first step)))
    (if (and (consp (cddr literal)) (consp (cdaddr literal)))
        (finite-tables-integer (cadr (caddr literal)))
      '(:failure "failure" ""))))

(defun finite-tables-tightest-bound (bounds best limit)
  (if (endp bounds)
      best
    (finite-tables-let* ((number (finite-tables-bound-number (car bounds))))
      (if (or (not best) (< number limit))
          (finite-tables-tightest-bound (cdr bounds) (car bounds) number)
        (finite-tables-tightest-bound (cdr bounds) best limit)))))

(defun finite-tables-available-bound (lib value known)
  (let ((bounds (finite-tables-known-bounds value known)))
    (cond ((failure-p bounds) (cons bounds lib))
          (bounds (cons (finite-tables-tightest-bound bounds nil nil) lib))
          ((not (proof-is-call value *remainder-proofs-mod*)) (cons nil lib))
          ((not (consp (cddr value)))
           (cons '(:failure "failure" "") lib))
          (t (let ((result (remainder-proofs-remainder-premise
                            lib (library-lt value (caddr value)) known)))
               (if (failure-p result) (cons result lib) result))))))

(defun finite-tables-impossible-orientation (lib goal upper limit hypothesis
                                               actual constant reverse)
  (cond ((not (and (equal actual *library-x*)
                   (proof-is-call constant *proof-quote*))) nil)
        ((not (consp (cdr constant))) '(:failure "failure" ""))
        ((or (not (finite-tables-integerp (cadr constant)))
             (< (finite-tables-integer (cadr constant)) limit)) nil)
        (t
         (let ((proof (library-library-proof lib)))
           (finite-tables-let*
            ((equality (if reverse (proof-proof-symmetric proof hypothesis) hypothesis))
             (false-step (proof-proof-rewrite proof upper equality '(1 1)))
             (literal (proof-step-first false-step))
             (computed (proof-proof-compute proof literal (cadr *proof-false*)))
             (false-step (proof-proof-rewrite proof false-step computed '(1)))
             (false-step (proof-proof-tidy proof false-step)))
            (proof-proof-subsume proof false-step
                                 (cons goal (proof-step-clause false-step))))))))

(defun finite-tables-impossible-derived (lib goal upper limit derived)
  (if (endp derived)
      *terms-unproved*
    (finite-tables-let* ((term (proof-step-first (cdar derived))))
      (cond ((not (proof-is-call term *proof-equal*))
             (finite-tables-impossible-derived lib goal upper limit (cdr derived)))
            ((not (consp (cddr term))) '(:failure "failure" ""))
            (t (let* ((hypothesis (cdar derived))
                      (left (cadr term))
                      (right (caddr term))
                      (step (finite-tables-impossible-orientation
                             lib goal upper limit hypothesis left right nil)))
                 (if step
                     step
                   (let ((step (finite-tables-impossible-orientation
                                lib goal upper limit hypothesis right left t)))
                     (if step
                         step
                       (finite-tables-impossible-derived
                        lib goal upper limit (cdr derived)))))))))))

(defun finite-tables-impossible-value (lib goal cases upper)
  (finite-tables-let*
   ((limit (finite-tables-bound-number upper))
    (rulers (rulers-rulers-init lib cases nil))
    (derived (rulers-rulers-derived rulers)))
   (finite-tables-impossible-derived lib goal upper limit derived)))

(defun finite-tables-finite-table-predicate-leaf (constant cases lib predicate
                                                          proved boundary)
  (let ((known (assoc-equal constant proved)))
    (if known
        (cdr known)
      (finite-tables-impossible-value lib (list predicate constant) cases boundary))))

(defun finite-tables-prove-values (lib predicate values)
  (if (endp values)
      nil
    (finite-tables-let*
     ((reducer (book-logic-reducer-init lib nil :none t 160 430 nil t)))
     (let* ((result (book-logic-reducer-prove reducer (list predicate (car values))))
            (step (if (failure-p result) result (car result))))
       (cond ((terms-unproved-p step)
              (finite-tables-prove-values lib predicate (cdr values)))
             ((failure-p step) step)
             (t (finite-tables-let*
                 ((rest (finite-tables-prove-values lib predicate (cdr values))))
                 (cons (cons (car values) step) rest))))))))

(defun finite-tables-leaf-proofs (requests lib predicate proved boundary)
  (if (endp requests)
      nil
    (let* ((request (car requests))
           (step (finite-tables-finite-table-predicate-leaf
                  (car request) (cadr request) lib predicate proved boundary)))
      (cons (cons request step)
            (if (failure-p step)
                nil
              (finite-tables-leaf-proofs (cdr requests) lib predicate proved boundary))))))

(defun finite-tables-add-lemma (lib label predicate table limit bounded proved)
  (let ((proof (library-library-proof lib))
        (template (list predicate *proof-result*)))
    (finite-tables-let*
     ((opening (proof-proof-unfold proof (list table *library-x*)))
      (literal (proof-step-first opening))
      (rhs (proof-proof-simplify proof (caddr literal) nil (list *termination-return-last*)))
      (equality (proof-proof-chain proof opening (list rhs)))
      (literal (proof-step-first equality))
      (boundary (and bounded (proof-proof-assume proof (library-lt *library-x* limit) t)))
      (requests (proof-proof-by-value-leaves proof (caddr literal) nil)))
     (let* ((leaves (finite-tables-leaf-proofs requests lib predicate proved boundary))
            (step (lemmas-slice-library-by-value lib (caddr literal) template leaves nil)))
       (if (terms-unproved-p step)
           nil
         (finite-tables-let*
          ((step step)
           (reverse (proof-proof-symmetric proof equality))
           (result (proof-proof-rewrite-result proof step reverse template *proof-result*))
           (claim (proof-step-first result))
           (boundary-term (and boundary (proof-step-first boundary))))
          (library-library-lemma lib label claim result
                                 (if boundary (list (proof-neg boundary-term)) nil))))))))

(defun finite-tables-cite-or-build (lib predicate table value definition proved upper bounded)
  (let* ((literal (and bounded (proof-step-first upper)))
         (limit (if bounded (caddr literal) *proof-false*))
         (source (if (failure-p literal)
                     literal
                   (proof-write (list predicate table definition limit)))))
    (if (failure-p source)
        (cons source lib)
      (let* ((digest (text-upper (seq-slice (siphash-hexdigest source) 0 16)))
             (label (concatenate 'string "FINITE-CASE-" digest))
             (name (proof-sym (concatenate 'string "SELF-" label) "ACL2"))
             (facts (proof-proof-facts (library-library-proof lib)))
             (result (if (assoc-equal name facts)
                         lib
                       (finite-tables-add-lemma lib label predicate table limit bounded proved))))
        (cond ((failure-p result) (cons result lib))
              ((not result) (cons nil lib))
              (t (cons (library-library-cite result label (list value) (and upper (list upper)))
                       result)))))))

(defun finite-tables-prove-body (lib predicate table value definition body known)
  (let ((values (finite-tables-table-values body)))
    (cond
     ((terms-unproved-p values) (cons nil lib))
     ((failure-p values) (cons values lib))
     (t (let* ((values (proof-unique values))
               (proved (finite-tables-prove-values lib predicate values)))
          (cond ((failure-p proved) (cons proved lib))
                ((not proved) (cons nil lib))
                (t (let* ((bounded (not (equal (len proved) (len values))))
                          (result (if bounded
                                      (finite-tables-available-bound lib value known)
                                    (cons nil lib)))
                          (upper (car result))
                          (lib (cdr result)))
                     (cond ((failure-p upper) result)
                           ((and bounded (not upper)) (cons nil lib))
                           (t (finite-tables-cite-or-build
                               lib predicate table value definition proved upper bounded)))))))))))

(defun finite-tables-finite-table-predicate (lib goal known)
  (if (and (proof-compound goal) (equal (len goal) 2)
           (proof-compound (cadr goal)) (equal (len (cadr goal)) 2))
      (let* ((predicate (car goal))
             (table (caadr goal))
             (value (cadadr goal))
             (definitions (proof-proof-definitions (library-library-proof lib)))
             (definition (assoc-equal table definitions)))
        (if (and definition (not (proof-compound predicate))
                 (equal (len (cadr definition)) 1)
                 (book-logic-within-size (caddr definition) 180))
            (let* ((definition (caddr definition))
                   (body (termination-logical-body definition)))
              (cond ((failure-p body) (cons body lib))
                    ((proof-is-call body *proof-if*)
                     (finite-tables-prove-body lib predicate table value definition body known))
                    (t (cons nil lib))))
          (cons nil lib)))
    (cons nil lib)))
