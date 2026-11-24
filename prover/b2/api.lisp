(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-api-prefix* "B2")

(defun b2-api-raw-line (line)
  (let ((size (length line)))
    (if (and (< 0 size) (eql (char line (1- size)) #\Newline))
        (subseq line 0 (1- size))
      line)))

(defun b2-api-parse (raw)
  (b2-reuse-parse raw))

(defun b2-run-admit-definition (proof definition)
  (let ((formals (cadr definition)))
    (if (or (not (equal (len definition) 3))
            (integerp formals) (stringp formals))
        '(:failure "failure" "")
      (proof-proof-add-definition proof (car definition) formals
                                  (caddr definition)))))

(defun b2-run-admit-definitions (proof definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      proof
    (proof-with-checked-results
     ((next (b2-run-admit-definition proof (car definitions))))
     (b2-run-admit-definitions next (cdr definitions)))))

(defun b2-run-admit-constraints (facts formulas)
  (declare (xargs :measure (acl2-count formulas)))
  (cond ((integerp formulas) '(:failure "failure" ""))
        ((endp formulas) facts)
        ((stringp (car formulas))
         ; A string in this position begins a tagged datum, where a constraint pair is required.
         '(:failure "failure" ""))
        (t (proof-with-checked-results
            ((pair (proof-list-of-length (car formulas) 2)))
            (b2-run-admit-constraints
             (table-put facts (car pair) (list (cadr pair)))
             (cdr formulas))))))

(defun b2-run-admit (lib kind data)
  (let* ((proof (library-library-proof lib))
         (facts (proof-proof-facts proof)))
    (cond
     ((equal kind "define")
      (proof-with-checked-results
       ((next (b2-run-admit-definitions proof (cdr data))))
       (library-library-with-proof lib next)))
     ((or (equal kind "theorem") (equal kind "axiom"))
      (proof-with-checked-results ((formula (proof-term-at data 1)))
        (library-library-with-proof
         lib (proof-proof-with-facts
              proof (table-put facts (car data) (list formula))))))
     ((equal kind "constrain")
      (proof-with-checked-results ((formulas (proof-term-at data 1)))
        (if (equal formulas *proof-nil*)
            lib
          (proof-with-checked-results
           ((next (b2-run-admit-constraints facts formulas)))
           (library-library-with-proof lib (proof-proof-with-facts proof next))))))
     (t lib))))

(defun b2-api-fill (lib lines seen)
  (declare (xargs :measure (acl2-count lines)))
  (if (endp lines)
      (list lib seen)
    (let ((raw (b2-api-raw-line (car lines))))
      (if (member-equal raw seen)
          (b2-api-fill lib (cdr lines) seen)
        (proof-with-checked-results
         ((parsed (b2-api-parse raw))
          (next (b2-run-admit lib (car parsed) (cadr parsed))))
         (b2-api-fill next (cdr lines) (cons raw seen)))))))

(defun b2-api-ground ()
  (library-library-init (proof-proof-init)))

(defun b2-api-new-context (source)
  (let ((proof (library-library-proof source)))
    (library-library-init
     (proof-make-proof (proof-proof-facts proof)
                       (proof-proof-definitions proof)
                       (proof-proof-primitives proof)))))

(defun b2-api-library (lines)
  (b2-api-fill (b2-api-new-context (b2-api-ground)) lines nil))

(defun b2-api-prelude ()
  (proof-with-checked-results
   ((lib (library-library-build (library-library-init (proof-proof-init))))
    (groups (b2-api-entries-groups (library-library-entries lib))))
   (list lib groups)))

(defun b2-api-measure-lines (aids measures)
  (if (endp aids)
      measures
    (let ((raw (car aids)))
      (if (text-starts-with raw "(measure ")
          (proof-with-checked-results
           ((parsed (b2-api-parse (b2-api-raw-line raw))))
           (let ((data (cadr parsed)))
             (cond
              ((endp (cddr data))
               '(:failure "failure" ""))
              ((equal (caddr data) *proof-ordinal-less*)
               (b2-api-measure-lines
                (cdr aids) (table-put measures (car data) (cadr data))))
              (t (b2-api-measure-lines (cdr aids) measures)))))
        (b2-api-measure-lines (cdr aids) measures)))))

(defun b2-api-measures (aids)
  (b2-api-measure-lines aids nil))

(defun b2-api-claim-fact (facts formula)
  (cond ((endp facts) nil)
        ((equal (cdar facts) (list formula)) (car facts))
        (t (b2-api-claim-fact (cdr facts) formula))))

(defun b2-api-claim-entry (lib name step)
  (proof-with-checked-results
   ((entry (proof-proof-entry "theorem" name (list name) (list step))))
   (list lib entry)))

(defun b2-api-claim-attempt (recipe lib name formula)
  (let ((trial (b2-api-new-context lib)))
    (proof-with-checked-results
     ((result (case recipe
                (:shape (b2-shape-recipes-prove-shape trial formula))
                (:theorem (b2-recipes-prove-theorem trial name formula))
                (otherwise (b2-next-recipes-prove-new-theorem trial name formula)))))
     (if (null (car result))
         '(:failure "failure" "")
       (proof-with-checked-results
        ((step (proof-proof-subsume (library-library-proof (cdr result))
                                    (car result) (list formula))))
        (b2-api-claim-entry (cdr result) name step))))))

(defun b2-api-claim-attempts (recipes lib name formula)
  (if (endp recipes)
      (b2-tactics-unproved)
    (let ((result (b2-api-claim-attempt (car recipes) lib name formula)))
      (if (and (failure-p result)
               (member-equal (cadr result)
                             '("inapplicable" "tactic-rejected"
                               "value" "Unproved" "coding"
                               "decoding" "encoding"
                               "translating" "lookup" "index"
                               "key" "assertion" "type")))
          (b2-api-claim-attempts (cdr recipes) lib name formula)
        result))))

(defun b2-api-claim (lib name formula)
  (let* ((proof (library-library-proof lib))
         (fact (b2-api-claim-fact (proof-proof-facts proof) formula)))
    (if fact
        (proof-with-checked-results ((step (proof-proof-fact proof (car fact) nil)))
          (b2-api-claim-entry lib name step))
      (b2-api-claim-attempts '(:shape :theorem :new-theorem) lib name formula))))

(defun b2-api-add-support (lib support)
  (let ((proof (library-library-proof lib))
        (support-proof (library-library-proof support)))
    (library-library-with-proof
     lib
     (proof-make-proof
      (table-update (proof-proof-facts proof) (proof-proof-facts support-proof))
      (table-update (proof-proof-definitions proof) (proof-proof-definitions support-proof))
      (proof-proof-primitives proof)))))

(defun b2-api-definition-calls (data)
  (proof-with-checked-results
   ((rulers (proof-term-at data 0)))
   (termination-recursive-calls rulers (cdr data))))

(defun b2-api-compile-measured (lib definitions calls measures)
  (proof-with-checked-results
   ((result (b2-measures-prove-measure lib definitions calls measures)))
   (list (cdr result) (car result))))

(defun b2-api-compile-definition (lib data aids)
  (proof-with-checked-results
   ((calls (b2-api-definition-calls data)))
   (if (endp calls)
       nil
     (proof-with-checked-results
      ((measures (b2-api-measures aids)))
      (b2-api-compile-measured lib (cdr data) calls measures)))))

(defun b2-api-compile-constraint (lib data)
  (proof-with-checked-results ((formulas (proof-term-at data 1)))
    (cond ((equal formulas *proof-nil*) nil)
          ((consp (cddr data))
           '(:failure "failure" ""))
          (t (proof-with-checked-results
              ((result (b2-recipes-prove-witness lib (car data) formulas)))
              (list (cdr result) (car result)))))))

(defun b2-api-compile (lib kind data aids)
  (cond ((equal kind "define") (b2-api-compile-definition lib data aids))
        ((equal kind "constrain") (b2-api-compile-constraint lib data))
        ((not (equal (len data) 2)) '(:failure "failure" ""))
        (t (b2-api-claim lib (car data) (cadr data)))))

(defun b2-api-assemble-compiled (public groups result)
  (cond ((or (null result) (failure-p result)) result)
        (t (let ((proof (library-library-proof public)))
             (b2-api-entries-assemble
              groups (library-library-entries (car result))
              (cadddr (cadr result)) (proof-proof-facts proof)
              (proof-proof-definitions proof))))))

(defun b2-api-prove-internal (statement earlier library aids)
  (let ((raw (b2-api-raw-line statement)))
    (proof-with-checked-results ((parsed (b2-api-parse raw)))
      (let ((kind (car parsed))
            (data (cadr parsed)))
        (if (not (member-equal kind '("theorem" "define" "constrain")))
            nil
          (proof-with-checked-results
           ((given (b2-api-library library))
            (public (b2-api-fill (b2-api-new-context (car given))
                                earlier (cadr given))))
           (if (member-equal raw (cadr public))
               nil
             (let ((lib (b2-api-new-context (car public))))
               (proof-with-checked-results
                ((prelude (b2-api-prelude)))
                (b2-api-assemble-compiled
                 (car public) (cadr prelude)
                 (b2-api-compile (b2-api-add-support lib (car prelude))
                                 kind data aids)))))))))))

(defun b2-api-prove (statement earlier library aids)
  (let ((result (b2-api-prove-internal statement earlier library aids)))
    (if (failure-p result) nil result)))
