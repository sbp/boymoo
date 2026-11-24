(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-book-order-hypothesis-wrappers*
  (list *h3-book-signs-case-split* (proof-sym "FORCE" "ACL2")))

(defun h3-book-order-bound-parts (term)
  (cond
   ((proof-is-call term *proof-less*)
    (proof-with-checked-results
        ((low (proof-term-at term 1))
         (high (proof-term-at term 2)))
      (list low high t)))
   ((proof-is-call term *proof-not*)
    (proof-with-checked-results ((inner (proof-term-at term 1)))
      (if (proof-is-call inner *proof-less*)
          (proof-with-checked-results
              ((low (proof-term-at inner 2))
               (high (proof-term-at inner 1)))
            (list low high nil))
        nil)))
   (t nil)))

(defun h3-book-order-required-parts (term)
  (or (h3-book-order-bound-parts term)
      '(:failure "failure" "")))

(defun h3-book-order-make-bounds (library search evidence)
  (list :h3-bounds library search evidence))

(defun h3-book-order-bounds-lib (bounds)
  (cadr bounds))

(defun h3-book-order-bounds-search (bounds)
  (caddr bounds))

(defun h3-book-order-bounds-evidence (bounds)
  (cadddr bounds))

(defun h3-book-order-bounds-with-library (bounds library)
  (h3-book-order-make-bounds
   library
   (h3-rewrite-search-with-lib (h3-book-order-bounds-search bounds) library)
   (h3-book-order-bounds-evidence bounds)))

(defun h3-book-order-bounds-with-search (bounds search)
  (h3-book-order-make-bounds (h3-rewrite-search-lib search)
                            search (h3-book-order-bounds-evidence bounds)))

(defun h3-book-order-carry-library (bounds result)
  (if (failure-p result)
      (cons result bounds)
    (cons (car result)
          (h3-book-order-bounds-with-library bounds (cdr result)))))

(defun h3-book-order-expose-result (result)
  (if (failure-p (car result)) (car result) result))

(defmacro h3-book-order-with-results (bounds bindings result)
  ;; An optional third binding field identifies a paired result.
  (if (endp bindings)
      result
    (let* ((binding (car bindings))
           (name (car binding))
           (form (cadr binding))
           (kind (caddr binding))
           (next `(if (failure-p ,name)
                      (cons ,name ,bounds)
                    (h3-book-order-with-results ,bounds ,(cdr bindings)
                                               ,result))))
      (if kind
          `(let* ((bounds-reply
                   ,(if (eq kind :library)
                        `(h3-book-order-carry-library ,bounds ,form)
                      form))
                  (,name (car bounds-reply))
                  (,bounds (cdr bounds-reply)))
             ,next)
        `(let ((,name ,form)) ,next)))))

(defun h3-book-order-step-parts (step)
  (proof-with-checked-results ((term (proof-step-first step)))
    (h3-book-order-required-parts term)))

(defun h3-book-order-step-at (step index)
  (proof-with-checked-results ((term (proof-step-first step)))
    (proof-term-at term index)))

(defun h3-book-order-transparency (wrappers definitions)
  (cond ((endp wrappers) nil)
        ((assoc-equal (car wrappers) definitions)
         (cons (car wrappers)
               (h3-book-order-transparency (cdr wrappers) definitions)))
        (t (h3-book-order-transparency (cdr wrappers) definitions))))

(defun h3-book-order-wrapped-p (term wrappers)
  (and (consp wrappers)
       (or (proof-is-call term (car wrappers))
           (h3-book-order-wrapped-p term (cdr wrappers)))))

(defun h3-book-order-expand-evidence (original evidence search expand wrappers)
  (if (endp original)
      evidence
    (let ((term (caar original))
          (proof (library-library-proof (h3-rewrite-search-lib search))))
      (if (h3-book-order-wrapped-p term wrappers)
          (let* ((result (h3-rewrite-search-reduce expand term nil nil nil))
                 (definition (car result)))
            (cond
             ((failure-p definition) definition)
             (definition
              (proof-with-checked-results
                  ((rewritten (proof-proof-rewrite proof (cdar original)
                                                   definition '(1)))
                   (evidence (h3-rewrite-search-add-evidence search evidence
                                                            rewritten)))
                (h3-book-order-expand-evidence (cdr original) evidence search
                                                (cadr result) wrappers)))
             (t (h3-book-order-expand-evidence (cdr original) evidence search
                                               (cadr result) wrappers))))
        (h3-book-order-expand-evidence (cdr original) evidence search
                                        expand wrappers)))))

(defun h3-book-order-bounds-init (library evidence)
  (let ((search (h3-rewrite-search-init library (list *proof-not*)
                                       nil nil 150 nil)))
    (proof-with-checked-results
        ((context (h3-rewrite-search-context search evidence)))
      (let* ((definitions (proof-proof-definitions (library-library-proof library)))
             (wrappers (h3-book-order-transparency
                        *h3-book-order-hypothesis-wrappers* definitions))
             (expand (h3-rewrite-search-init library wrappers nil nil 150 nil)))
        (proof-with-checked-results
            ((expanded (h3-book-order-expand-evidence context context search
                                                      expand wrappers)))
          (h3-book-order-make-bounds library search expanded))))))

(defun h3-book-order-bounds-rational (bounds term)
  (h3-book-quotient-rational-type (h3-book-order-bounds-lib bounds)
                                 term (h3-book-order-bounds-evidence bounds)))

(defun h3-book-order-bounds-numeric (bounds term)
  (let* ((library (h3-book-order-bounds-lib bounds))
         (number (assoc-equal (list *library-numberp* term)
                              (h3-book-order-bounds-evidence bounds))))
    (if number
        (cdr number)
      (let ((typed (h3-book-arithmetic-typed-number library term)))
        (if (h3-rewrite-unproved-p typed)
            (proof-with-checked-results
                ((rational (h3-book-order-bounds-rational bounds term)))
              (h3-book-signs-number library rational))
          typed)))))

(defun h3-book-order-bounds-compose-with-bounds (bounds first second)
  (h3-book-order-with-results bounds
      ((left (h3-book-order-step-parts first))
       (right (h3-book-order-step-parts second))
       (library (h3-numeric-order-numeric-order (h3-book-order-bounds-lib bounds))))
    (let* ((bounds (h3-book-order-bounds-with-library bounds library))
           (a (car left))
           (b (cadr left))
           (c (cadr right))
           (name (if (caddr left)
                     (if (caddr right) "LESS-TRANSITIVE" "LESS-THEN-WEAK")
                   (if (caddr right) "WEAK-THEN-LESS" "WEAK-TRANSITIVE"))))
      (h3-book-order-with-results bounds
          ((an (h3-book-order-bounds-numeric bounds a))
           (bn (h3-book-order-bounds-numeric bounds b))
           (cn (h3-book-order-bounds-numeric bounds c)))
        (cons (h3-numeric-order-cite library name (list a b c)
                                     (list an bn cn first second))
              bounds)))))

(defun h3-book-order-bounds-compose (bounds first second)
  (h3-book-order-expose-result
   (h3-book-order-bounds-compose-with-bounds bounds first second)))

(defun h3-book-order-reflect-reductions (terms index equation bounds)
  (let* ((library (h3-book-order-bounds-lib bounds))
         (proof (library-library-proof library)))
    (if (endp terms)
        (proof-proof-tidy proof equation)
      (let ((term (car terms)))
        (proof-with-checked-results
            ((reduction
              (if (proof-is-call term *proof-minus*)
                  (proof-with-checked-results
                      ((value (proof-term-at term 1))
                       (numeric (h3-book-order-bounds-numeric bounds value))
                       (fixed (h3-book-arithmetic-fix-value library value numeric))
                       (double (library-library-cite library *h3-book-sums-double*
                                                     (cdr term) nil)))
                    (proof-proof-chain proof double (list fixed)))
                (h3-rewrite-primitive library (library-minus term))))
             (equation (if reduction
                           (proof-proof-rewrite proof equation reduction
                                                (list 1 2 index))
                         equation)))
          (h3-book-order-reflect-reductions (cdr terms) (1+ index)
                                            equation bounds))))))

(defun h3-book-order-reflection (bounds first second)
  (let* ((library (h3-book-order-bounds-lib bounds))
         (proof (library-library-proof library)))
    (proof-with-checked-results
        ((reversed (library-library-axiom
                    library "<-ON-OTHERS" (list (library-minus second)
                                                (library-minus first))))
         (double (library-library-cite library *h3-book-sums-double* (list first) nil))
         (numeric (h3-book-order-bounds-numeric bounds first))
         (fixed (h3-book-arithmetic-fix-value library first numeric))
         (double (proof-proof-chain proof double (list fixed)))
         (reversed (proof-proof-rewrite proof reversed double '(1 2 1 2)))
         (exchange (library-library-axiom library "COMMUTATIVITY-OF-+"
                                          (list (library-minus second) first)))
         (reversed (proof-proof-rewrite proof reversed exchange '(1 2 1)))
         (original (library-library-axiom library "<-ON-OTHERS" (list first second)))
         (opposite (proof-proof-symmetric proof reversed))
         (equation (proof-proof-chain proof original (list opposite))))
      (h3-book-order-reflect-reductions (list second first) 1 equation bounds))))

(defun h3-book-order-bounds-reflect-with-bounds (bounds first second)
  (h3-book-order-with-results bounds
      ((lemmas (h3-book-sums-lemmas-with-library (h3-book-order-bounds-lib bounds)) :library))
    (cons (h3-book-order-reflection bounds first second) bounds)))

(defun h3-book-order-bounds-reflect (bounds first second)
  (h3-book-order-expose-result
   (h3-book-order-bounds-reflect-with-bounds bounds first second)))

(defun h3-book-order-add-edge (edges from to strict proof)
  (table-put edges from
               (append (table-get edges from nil)
                       (list (list to strict proof)))))

(defun h3-book-order-record-edges (candidates edges constants)
  (if (endp candidates)
      (list edges constants)
    (proof-with-checked-results
        ((parts (h3-book-order-step-parts (car candidates))))
      (let ((a (car parts))
            (b (cadr parts))
            (strict (caddr parts)))
        (h3-book-order-record-edges
         (cdr candidates)
         (h3-book-order-add-edge edges a b strict (car candidates))
         (table-put (table-put constants a nil) b nil))))))

(defun h3-book-order-mirrored-edge (bounds proof parts)
  (let* ((strict (caddr parts))
         (a (if strict (car parts) (cadr parts)))
         (b (if strict (cadr parts) (car parts))))
    (h3-book-order-with-results bounds
        ((order (h3-book-order-bounds-reflect-with-bounds bounds a b) :bounds))
      (let ((logic (library-library-proof (h3-book-order-bounds-lib bounds))))
        (cons (proof-proof-rewrite logic proof order (if strict '(1) '(1 1)))
              bounds)))))

(defun h3-book-order-premise-edges (evidence mirrored edges constants bounds)
  (if (endp evidence)
      (cons (list edges constants) bounds)
    (let ((proof (cdar evidence)))
      (h3-book-order-with-results bounds
          ((term (proof-step-first proof))
           (parts (h3-book-order-bound-parts term)))
        (if (not parts)
            (h3-book-order-premise-edges (cdr evidence) mirrored edges
                                        constants bounds)
          (let* ((reflected (if mirrored
                                (h3-book-order-mirrored-edge bounds proof parts)
                              (cons nil bounds)))
                 (bounds (cdr reflected))
                 (mirror (if (h3-rewrite-unproved-p (car reflected))
                             nil
                           (car reflected))))
            (h3-book-order-with-results bounds
                ((mirror mirror)
                 (graph (h3-book-order-record-edges
                         (if mirror (list proof mirror) (list proof))
                         edges constants)))
              (h3-book-order-premise-edges (cdr evidence) mirrored (car graph)
                                          (cadr graph) bounds))))))))

(defun h3-book-order-constant-values (constants)
  (if (endp constants)
      nil
    (let ((term (caar constants)))
      (if (proof-is-call term *proof-quote*)
          (proof-with-checked-results
              ((datum (proof-term-at term 1))
               (value (h3-rewrite-rational-value datum))
               (later (h3-book-order-constant-values (cdr constants))))
            (cons (cons term value) later))
        (h3-book-order-constant-values (cdr constants))))))

(defun h3-book-order-constant-edges-from (left number values edges bounds)
  (if (endp values)
      (cons edges bounds)
    (let ((right (caar values))
          (value (cdar values)))
      (if (and number value (< number value))
          (let* ((result (h3-rewrite-search-prove
                          (h3-book-order-bounds-search bounds)
                          (library-lt left right) nil))
                 (step (car result))
                 (bounds (h3-book-order-bounds-with-search bounds (cdr result))))
            (h3-book-order-with-results bounds ((step step))
              (h3-book-order-constant-edges-from
               left number (cdr values)
               (h3-book-order-add-edge edges left right t step) bounds)))
        (h3-book-order-constant-edges-from left number (cdr values) edges bounds)))))

(defun h3-book-order-constant-edges (lefts values edges bounds)
  (if (endp lefts)
      (cons edges bounds)
    (h3-book-order-with-results bounds
        ((edges (h3-book-order-constant-edges-from (caar lefts) (cdar lefts)
                                                   values edges bounds) :bounds))
      (h3-book-order-constant-edges (cdr lefts) values edges bounds))))

(defun h3-book-order-enqueue-edges (neighbors destination strict contains-strict
                                             reversed-path queued seen)
  (if (endp neighbors)
      (list queued seen)
    (let* ((edge (car neighbors))
           (term (car edge))
           (stronger (or contains-strict (cadr edge)))
           (path (cons (caddr edge) reversed-path))
           (mark (list term stronger)))
      (cond
       ((and (equal term destination) (or stronger (not strict)))
        (list :found (reverse path)))
       ((member-equal mark seen)
        (h3-book-order-enqueue-edges (cdr neighbors) destination strict
                                    contains-strict reversed-path queued seen))
       (t (h3-book-order-enqueue-edges
           (cdr neighbors) destination strict contains-strict reversed-path
           (append queued (list (list term stronger path))) (cons mark seen)))))))

(defun h3-book-order-breadth-first (n edges destination strict queued seen)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "h3-book-order-breadth-first"))
   ((endp queued) *h3-rewrite-unproved*)
   (t (let* ((current (car queued))
             (neighbors (table-get edges (car current) nil))
             (result (h3-book-order-enqueue-edges neighbors destination strict
                                                  (cadr current) (caddr current)
                                                  (cdr queued) seen)))
        (if (eq (car result) :found)
            (cadr result)
          (h3-book-order-breadth-first (1- n) edges destination strict
                                       (car result) (cadr result)))))))

(defun h3-book-order-bounds-path-with-bounds (bounds source destination strict mirrored)
  (let ((constants (table-put (list (cons source nil)) destination nil)))
    (h3-book-order-with-results bounds
        ((graph (h3-book-order-premise-edges (h3-book-order-bounds-evidence bounds)
                                            mirrored nil constants bounds) :bounds)
         (values (h3-book-order-constant-values (cadr graph)))
         (edges (h3-book-order-constant-edges values values (car graph) bounds) :bounds))
      (cons (h3-book-order-breadth-first 1000000 edges destination strict
                                         (list (list source nil nil))
                                         (list (list source nil)))
            bounds))))

(defun h3-book-order-bounds-path (bounds source destination strict mirrored)
  (h3-book-order-expose-result
   (h3-book-order-bounds-path-with-bounds bounds source destination strict mirrored)))

(defun h3-book-order-compose-path (bounds first later)
  (declare (xargs :measure (acl2-count later)))
  (if (or (endp later) (failure-p first))
      (cons first bounds)
    (let ((joined (h3-book-order-bounds-compose-with-bounds bounds first (car later))))
      (h3-book-order-compose-path (cdr joined) (car joined) (cdr later)))))

(defun h3-book-order-reflexive-bound (library term)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((difference (library-library-axiom library "<-ON-OTHERS" (list term term)))
         (inverse (library-library-axiom library "INVERSE-OF-+" (list term)))
         (equality (proof-proof-rewrite proof difference inverse '(1 2 1)))
         (zero (library-library-axiom library "ZERO" nil)))
      (library-library-transport-argument library zero equality 1))))

(defun h3-book-order-weaken-path (bounds first a b)
  (h3-book-order-with-results bounds
      ((library (h3-numeric-order-numeric-order (h3-book-order-bounds-lib bounds))))
    (let ((bounds (h3-book-order-bounds-with-library bounds library)))
      (h3-book-order-with-results bounds
          ((an (h3-book-order-bounds-numeric bounds a))
           (bn (h3-book-order-bounds-numeric bounds b)))
        (cons (h3-numeric-order-cite library "LESS-ASYMMETRIC" (list a b)
                                     (list an bn first))
              bounds)))))

(defun h3-book-order-bounds-direct-bound-with-bounds (bounds goal mirrored)
  (let* ((derived (h3-rewrite-search-derive (h3-book-order-bounds-search bounds)
                                            goal (h3-book-order-bounds-evidence bounds)
                                            nil nil))
         (step (car derived))
         (bounds (h3-book-order-bounds-with-search bounds (cadr derived))))
    (if (not (h3-rewrite-unproved-p step))
        (cons step bounds)
      (h3-book-order-with-results bounds ((parts (h3-book-order-required-parts goal)))
        (let ((a (car parts))
              (b (cadr parts))
              (strict (caddr parts)))
          (if (and (equal a b) (not strict))
              (cons (h3-book-order-reflexive-bound
                     (h3-book-order-bounds-lib bounds) a)
                    bounds)
            (h3-book-order-with-results bounds
                ((path (h3-book-order-bounds-path-with-bounds
                        bounds a b strict mirrored) :bounds)
                 (first (h3-book-order-compose-path bounds (car path) (cdr path)) :bounds)
                 (literal (proof-step-first first)))
              (if (and (not (equal literal goal)) (proof-is-call literal *proof-less*))
                  (h3-book-order-weaken-path bounds first a b)
                (cons first bounds)))))))))

(defun h3-book-order-bounds-direct-bound (bounds goal mirrored)
  (h3-book-order-expose-result
   (h3-book-order-bounds-direct-bound-with-bounds bounds goal mirrored)))

(defun h3-book-order-bounds-bound-with-bounds (bounds goal)
  (let ((direct (h3-book-order-bounds-direct-bound-with-bounds bounds goal nil)))
    (if (h3-rewrite-unproved-p (car direct))
        (h3-book-order-bounds-direct-bound-with-bounds (cdr direct) goal t)
      direct)))

(defun h3-book-order-bounds-bound (bounds goal)
  (h3-book-order-expose-result (h3-book-order-bounds-bound-with-bounds bounds goal)))

(defun h3-book-order-product-identity (library scalar scalar-type)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((unit (library-library-axiom library "UNICITY-OF-1" (list scalar)))
         (numeric (h3-book-signs-number library scalar-type))
         (fixed (h3-book-arithmetic-fix-value library scalar numeric)))
      (proof-proof-chain proof unit (list fixed)))))

(defun h3-book-order-negative-unit-product (library expression scalar identity)
  (let* ((proof (library-library-proof library))
         (moved (proof-with-checked-results
                    ((literal (proof-proof-compute proof (library-minus *proof-one*) -1))
                     (opposite (proof-proof-symmetric proof literal))
                     (start (proof-proof-reflexive proof expression)))
                  (proof-proof-rewrite proof start opposite '(1 2 1)))))
    (if (failure-p moved)
        (cons moved library)
      (let* ((opposite (h3-book-signs-minus-product-with-library library *proof-one* scalar t))
             (library (cdr opposite))
             (proof (library-library-proof library)))
        (cons (proof-with-checked-results
                  ((opposite (car opposite))
                   (chained (proof-proof-chain proof moved (list opposite))))
                (proof-proof-rewrite proof chained identity '(1 2 1)))
              library)))))

(defun h3-book-order-constant-product-with-library (library constant scalar scalar-type)
  (let ((expression (list *proof-times* constant scalar))
        (proof (library-library-proof library)))
    (cond
     ((equal constant *proof-zero*)
      (cons (proof-with-checked-results
                ((commuted (library-library-axiom library "COMMUTATIVITY-OF-*"
                                                  (list *proof-zero* scalar)))
                 (zero (h3-event-counts-multiply-zero library scalar)))
              (proof-proof-chain proof commuted (list zero)))
            library))
     ((or (equal constant *proof-one*) (equal constant *proof-neg-one*))
      (let ((identity (h3-book-order-product-identity library scalar scalar-type)))
        (if (or (failure-p identity) (equal constant *proof-one*))
            (cons identity library)
          (h3-book-order-negative-unit-product library expression scalar identity))))
     (t (cons (proof-proof-reflexive proof expression) library)))))

(defun h3-book-order-constant-product (library constant scalar scalar-type)
  (car (h3-book-order-constant-product-with-library library constant scalar scalar-type)))

(defun h3-book-order-try-signs (signs bounds rational term)
  (if (endp signs)
      (cons nil bounds)
    (let* ((sign (car signs))
           (result (h3-book-order-bounds-bound-with-bounds
                    bounds (h3-book-signs-sign-test term sign)))
           (step (car result))
           (bounds (cdr result)))
      (if (h3-rewrite-unproved-p step)
          (h3-book-order-try-signs (cdr signs) bounds rational term)
        (let ((library (h3-book-order-bounds-lib bounds)))
          (h3-book-order-with-results bounds
              ((step step)
               (numeric (h3-book-signs-number library rational)))
            (h3-book-order-carry-library
             bounds (h3-book-signs-sign-evidence-with-library library numeric sign step))))))))

(defun h3-book-order-selected-sign-with-bounds (library bounds rational)
  (let ((bounds (h3-book-order-bounds-with-library bounds library)))
    (h3-book-order-with-results bounds ((term (h3-book-order-step-at rational 1)))
      (h3-book-order-try-signs '(1 -1) bounds rational term))))

(defun h3-book-order-selected-sign (library bounds rational)
  (h3-book-order-expose-result
   (h3-book-order-selected-sign-with-bounds library bounds rational)))

(defun h3-book-order-rational-pair (bounds a b)
  (proof-with-checked-results
      ((first (h3-book-order-bounds-rational bounds a))
       (second (h3-book-order-bounds-rational bounds b)))
    (list first second)))

(defun h3-book-order-transport (library strict step equality)
  (if strict
      (proof-proof-transport (library-library-proof library) step equality)
    (library-library-transport-argument library step equality 1)))

(defun h3-book-order-clear-factor (bounds term divisor law scalar)
  (let ((library (h3-book-order-bounds-lib bounds)))
    (h3-book-order-with-results bounds
        ((fraction (h3-book-quotient-reciprocal-factor term)))
      (if (and fraction (equal (car fraction) divisor))
          (h3-book-order-with-results bounds
              ((rational (h3-book-order-bounds-rational bounds (cadr fraction)))
               (numeric (h3-book-signs-number library rational)))
            (cons (h3-book-quotient-clear-reciprocal library term divisor law numeric)
                  bounds))
        (h3-book-order-carry-library
         bounds (h3-book-order-constant-product-with-library library term divisor scalar))))))

(defun h3-book-order-clear-factors (bounds terms index divisor law scalar equation)
  (declare (xargs :measure (acl2-count terms)))
  (if (or (endp terms) (failure-p equation))
      (cons equation bounds)
    (let* ((result (h3-book-order-clear-factor bounds (car terms) divisor law scalar))
           (bounds (cdr result))
           (rewritten
            (proof-with-checked-results ((equality (car result)))
              (proof-proof-rewrite (library-library-proof (h3-book-order-bounds-lib bounds))
                                   equation equality (list 1 2 index)))))
      (h3-book-order-clear-factors bounds (cdr terms) (1+ index) divisor law scalar rewritten))))

(defun h3-book-order-quotient-equation (bounds a b divisor)
  (h3-book-order-with-results bounds
      ((scalar (h3-book-order-bounds-rational bounds divisor))
       (signs (h3-book-order-selected-sign-with-bounds
               (h3-book-order-bounds-lib bounds) bounds scalar) :bounds))
    (if (not signs)
        (cons *h3-rewrite-unproved* bounds)
      (let ((library (h3-book-order-bounds-lib bounds)))
        (h3-book-order-with-results bounds
            ((numeric (h3-book-signs-number library scalar))
             (law (h3-book-arithmetic-inverse library divisor numeric
                                              (h3-book-signs-signs-zero signs)))
             (types (h3-book-order-rational-pair bounds a b))
             (equation (h3-book-quotient-scale-order-with-library
                        library a b scalar signs types) :library))
          (let ((ordered (if (< 0 (h3-book-signs-signs-sign signs))
                             (list a b)
                           (list b a))))
            (h3-book-order-clear-factors bounds ordered 1 divisor law scalar equation)))))))

(defun h3-book-order-quotient-next (remaining goal bounds)
  (h3-book-order-with-results bounds ((parts (h3-book-order-required-parts goal)))
    (let* ((strict (caddr parts))
           (a (if strict (car parts) (cadr parts)))
           (b (if strict (cadr parts) (car parts))))
      (h3-book-order-with-results bounds
          ((left (h3-book-quotient-reciprocal-factor a))
           (right (h3-book-quotient-reciprocal-factor b)))
        (cond
         ((not (or left right)) (h3-book-order-bounds-bound-with-bounds bounds goal))
         ((zp remaining) (cons *h3-rewrite-unproved* bounds))
         (t
          (h3-book-order-with-results bounds
              ((equation (h3-book-order-quotient-equation bounds a b (car (or left right))) :bounds)
               (reduced (h3-book-order-step-at equation 2)))
            (cons (list :expand (if strict reduced (proof-neg reduced)) strict equation)
                  bounds))))))))

(defun h3-book-order-quotient-bound-loop (remaining next)
  (declare (xargs :measure (nfix remaining)))
  (let ((request (car next))
        (bounds (cdr next)))
    (cond
     ((not (eq (car request) :expand)) next)
     ((zp remaining) (cons *h3-rewrite-unproved* bounds))
     (t
      (let* ((remaining (1- remaining))
             (child (h3-book-order-quotient-next remaining (cadr request) bounds))
             (result (h3-book-order-quotient-bound-loop remaining child)))
        (h3-book-order-with-results bounds ((step result :bounds))
          (cons (h3-book-order-transport (h3-book-order-bounds-lib bounds)
                                         (caddr request) step (cadddr request))
                bounds)))))))

(defun h3-book-order-quotient-bound-with-bounds (library goal bounds depth)
  (let ((remaining (nfix (ceiling (- 3 (if (eq depth t) 1 depth)) 1)))
        (bounds (h3-book-order-bounds-with-library bounds library)))
    (h3-book-order-quotient-bound-loop
     remaining (h3-book-order-quotient-next remaining goal bounds))))

(defun h3-book-order-quotient-bound (library goal bounds depth)
  (h3-book-order-expose-result
   (h3-book-order-quotient-bound-with-bounds library goal bounds depth)))

(defun h3-book-order-common-factors (left right)
  (cond ((endp left) nil)
        ((member-equal (car left) right)
         (cons (car left) (h3-book-order-common-factors (cdr left) right)))
        (t (h3-book-order-common-factors (cdr left) right))))

(defun h3-book-order-other-factor (term scalar)
  (proof-with-checked-results ((first (proof-term-at term 1)))
    (if (equal first scalar) (proof-term-at term 2) first)))

(defun h3-book-order-zero-product (library factors scalar zero)
  (case (len factors)
    (2 (h3-book-arithmetic-zero-product library (car factors) (cadr factors) scalar zero))
    (1 '(:failure "failure" ""))
    (0 '(:failure "failure" ""))
    (otherwise
     '(:failure "failure" ""))))

(defun h3-book-order-scaled-zero-product (terms index scalar zero equation library)
  (declare (xargs :measure (acl2-count terms)))
  (let ((proof (library-library-proof library)))
    (cond
     ((failure-p equation) equation)
     ((endp terms) (proof-proof-tidy proof equation))
     (t
      (let ((rewritten
             (proof-with-checked-results
                 ((reduction (h3-book-order-zero-product library (cdar terms) scalar zero))
                  (symmetric (proof-proof-symmetric proof reduction)))
               (proof-proof-rewrite proof equation symmetric (list 1 1 index)))))
        (h3-book-order-scaled-zero-product (cdr terms) (1+ index) scalar zero
                                            rewritten library))))))

(defun h3-book-order-scaled-bound-case (signs bounds strict left right a b scalar rational)
  (let ((sign (h3-book-signs-signs-sign signs)))
    (if (equal sign 0)
        (let ((library (h3-book-order-bounds-lib bounds)))
          (h3-book-order-with-results bounds ((zero (library-library-axiom library "ZERO" nil)))
            (cons (if strict
                      *h3-rewrite-unproved*
                    (h3-book-order-scaled-zero-product
                     (list left right) 1 scalar (h3-book-signs-signs-zero signs) zero library))
                  bounds)))
      (let* ((first (if (< 0 sign) a b))
             (second (if (< 0 sign) b a))
             (comparison (library-lt first second)))
        (h3-book-order-with-results bounds
            ((base (h3-book-order-bounds-bound-with-bounds
                    bounds (if strict comparison (proof-neg comparison))) :bounds)
             (types (let ((pair (h3-book-order-rational-pair bounds first second)))
                      (if (h3-rewrite-unproved-p pair) nil pair)))
             (scaled (h3-book-quotient-scale-order-with-library
                      (h3-book-order-bounds-lib bounds) first second rational signs types) :library)
             (source (h3-book-order-step-at scaled 2))
             (aligned (h3-book-arithmetic-associative-equal
                       (h3-book-order-bounds-lib bounds) source (library-lt left right)))
             (proof (library-library-proof (h3-book-order-bounds-lib bounds)))
             (equality (proof-proof-chain proof scaled (list aligned)))
             (rewritten (proof-proof-rewrite proof base equality (if strict '(1) '(1 1)))))
          (cons (proof-proof-tidy proof rewritten) bounds))))))

(defun h3-book-order-scaled-bound-nonnegative-case
    (signs bounds goal nonnegative left right a b scalar rational)
  (if (<= 0 (h3-book-signs-signs-sign signs))
      (h3-book-order-scaled-bound-case signs bounds nil left right a b scalar rational)
    (let ((proof (library-library-proof (h3-book-order-bounds-lib bounds))))
      (h3-book-order-with-results bounds
          ((contradiction (proof-proof-cut proof (h3-book-signs-signs-negative signs) nonnegative)))
        (cons (proof-proof-subsume proof contradiction
                                   (cons goal (proof-step-clause contradiction)))
              bounds)))))

(defun h3-book-order-signed-case (bounds numeric sign step goal nonnegative
                                         left right a b scalar rational)
  (h3-book-order-with-results bounds
      ((sign-evidence (h3-book-signs-sign-evidence-with-library
                       (h3-book-order-bounds-lib bounds) numeric sign step) :library))
    (h3-book-order-scaled-bound-nonnegative-case sign-evidence bounds goal nonnegative
                                                 left right a b scalar rational)))

(defun h3-book-order-scale-nonnegative (bounds goal left right a b scalar rational)
  (h3-book-order-with-results bounds
      ((nonnegative (h3-book-order-bounds-bound-with-bounds
                     bounds (library-le *proof-zero* scalar)) :bounds)
       (numeric (h3-book-signs-number (h3-book-order-bounds-lib bounds) rational))
       (steps (h3-book-signs-each-sign-prepare-with-library
               (h3-book-order-bounds-lib bounds) numeric) :library)
       (positive (h3-book-order-signed-case bounds numeric 1 (car steps) goal nonnegative
                                            left right a b scalar rational) :bounds)
       (zero (h3-book-order-signed-case bounds numeric 0 (cadr steps) goal nonnegative
                                        left right a b scalar rational) :bounds)
       (negative (h3-book-order-signed-case bounds numeric -1 (caddr steps) goal nonnegative
                                            left right a b scalar rational) :bounds))
    (cons (h3-book-signs-each-sign-finish (h3-book-order-bounds-lib bounds) numeric
                                         positive zero negative)
          bounds)))

(defun h3-book-order-scaled-candidate (scalar bounds goal strict left right)
  (let ((rational (h3-book-order-bounds-rational bounds scalar)))
    (if (h3-rewrite-unproved-p rational)
        (cons :next bounds)
      (h3-book-order-with-results bounds
          ((rational rational)
           (a (h3-book-order-other-factor left scalar))
           (b (h3-book-order-other-factor right scalar))
           (signs (h3-book-order-selected-sign-with-bounds
                    (h3-book-order-bounds-lib bounds) bounds rational) :bounds))
        (cond
         (signs (h3-book-order-scaled-bound-case signs bounds strict left right a b scalar rational))
         ((not strict) (h3-book-order-scale-nonnegative bounds goal left right a b scalar rational))
         (t (cons :next bounds)))))))

(defun h3-book-order-scaled-candidates (candidates previous goal strict left right)
  (declare (xargs :measure (acl2-count candidates)))
  (cond
   ((not (eq (car previous) :next)) previous)
   ((endp candidates) (cons *h3-rewrite-unproved* (cdr previous)))
   (t (h3-book-order-scaled-candidates
       (cdr candidates)
       (h3-book-order-scaled-candidate (car candidates) (cdr previous) goal strict left right)
       goal strict left right))))

(defun h3-book-order-scaled-bound-with-bounds (library goal bounds)
  (let ((bounds (h3-book-order-bounds-with-library bounds library)))
    (h3-book-order-with-results bounds ((parts (h3-book-order-required-parts goal)))
      (let* ((strict (caddr parts))
             (left (if strict (car parts) (cadr parts)))
             (right (if strict (cadr parts) (car parts))))
        (if (and (proof-is-call left *proof-times*) (proof-is-call right *proof-times*))
            (h3-book-order-scaled-candidates
             (h3-book-order-common-factors (cdr left) (cdr right))
             (cons :next bounds) goal strict left right)
          (cons *h3-rewrite-unproved* bounds))))))

(defun h3-book-order-scaled-bound (library goal bounds)
  (h3-book-order-expose-result (h3-book-order-scaled-bound-with-bounds library goal bounds)))

(defun h3-book-order-comparison (low high strict)
  (if strict (library-lt low high) (library-le low high)))

(defun h3-book-order-product-chain (bounds low middle high first-strict second-strict)
  (h3-book-order-with-results bounds
      ((left (h3-book-order-scaled-bound-with-bounds
              (h3-book-order-bounds-lib bounds)
              (h3-book-order-comparison low middle first-strict) bounds) :bounds)
       (right (h3-book-order-scaled-bound-with-bounds
               (h3-book-order-bounds-lib bounds)
               (h3-book-order-comparison middle high second-strict) bounds) :bounds))
    (h3-book-order-bounds-compose-with-bounds bounds left right)))

(defun h3-book-order-product-chain-orders (bounds low middle high strict)
  (if strict
      (let ((result (h3-book-order-product-chain bounds low middle high t nil)))
        (if (h3-rewrite-unproved-p (car result))
            (h3-book-order-product-chain (cdr result) low middle high nil t)
          result))
    (h3-book-order-product-chain bounds low middle high nil nil)))

(defun h3-book-order-product-chain-middles (middles previous low high strict)
  (declare (xargs :measure (acl2-count middles)))
  (cond
   ((not (h3-rewrite-unproved-p (car previous))) previous)
   ((endp middles) (cons *h3-rewrite-unproved*
                        (cdr previous)))
   (t
    (h3-book-order-product-chain-middles
     (cdr middles)
     (h3-book-order-product-chain-orders (cdr previous) low (car middles) high strict)
     low high strict))))

(defun h3-book-order-product-intermediate (bounds low high strict)
  (if (and (proof-is-call low *proof-times*) (proof-is-call high *proof-times*))
      (h3-book-order-with-results bounds
          ((low-left (proof-term-at low 1))
           (high-right (proof-term-at high 2))
           (high-left (proof-term-at high 1))
           (low-right (proof-term-at low 2)))
        (h3-book-order-product-chain-middles
         (list (list *proof-times* low-left high-right)
               (list *proof-times* high-left low-right))
         (cons *h3-rewrite-unproved* bounds)
         low high strict))
    (cons *h3-rewrite-unproved* bounds)))

(defun h3-book-order-unit-expansion (unit high strict bounds)
  (let ((proof (library-library-proof (h3-book-order-bounds-lib bounds))))
    (proof-with-checked-results
        ((computed (proof-proof-compute proof (list *proof-times* unit unit) 1))
         (expanded (proof-proof-symmetric proof computed))
         (product (h3-book-order-step-at expanded 2)))
      (list expanded (h3-book-order-comparison product high strict)))))

(defun h3-book-order-product-next (goal bounds)
  (h3-book-order-with-results bounds ((parts (h3-book-order-required-parts goal)))
    (let ((low (car parts))
          (high (cadr parts))
          (strict (caddr parts)))
      (if (and (equal low *proof-one*) (proof-is-call high *proof-times*))
          (cons (list :unit high strict) bounds)
        (let ((scaled (h3-book-order-scaled-bound-with-bounds
                       (h3-book-order-bounds-lib bounds) goal bounds)))
          (if (h3-rewrite-unproved-p (car scaled))
              (h3-book-order-product-intermediate (cdr scaled) low high strict)
            scaled))))))

(mutual-recursion
 (defun h3-book-order-product-bound-loop (n next)
   (declare (xargs :measure (nfix n)))
   (let ((request (car next))
         (bounds (cdr next)))
     (cond
      ((zp n) (cons '(:failure "Fuel" "h3-book-order-product-bound-loop") bounds))
      ((not (eq (car request) :unit)) next)
      (t
       (let* ((high (cadr request))
              (strict (caddr request))
              (positive (h3-book-order-product-unit (1- n) *proof-one* high strict bounds)))
         (if (eq (car positive) :next)
             (let ((negative (h3-book-order-product-unit (1- n) *proof-neg-one*
                                                         high strict (cdr positive))))
               (if (eq (car negative) :next)
                   (cons *h3-rewrite-unproved* (cdr negative))
                 negative))
           positive))))))

 (defun h3-book-order-product-unit (n unit high strict bounds)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "h3-book-order-product-unit") bounds)
     (let* ((expansion (h3-book-order-unit-expansion unit high strict bounds))
            (child (if (failure-p expansion)
                       (cons expansion bounds)
                     (h3-book-order-product-next (cadr expansion) bounds)))
            (result (h3-book-order-product-bound-loop (1- n) child))
            (step (car result))
            (bounds (cdr result)))
       (cond
        ((failure-p expansion) result)
        ((h3-rewrite-unproved-p step) (cons :next bounds))
        (t
         (let ((proof (library-library-proof (h3-book-order-bounds-lib bounds))))
           (h3-book-order-with-results bounds
               ((step step)
                (symmetric (proof-proof-symmetric proof (car expansion)))
                (rewritten (proof-proof-rewrite proof step symmetric
                                                (if strict '(1 1) '(1 1 2)))))
             (cons (proof-proof-tidy proof rewritten) bounds)))))))))

(defun h3-book-order-product-bound-with-bounds (library goal bounds)
  (h3-book-order-product-bound-loop
   1000000 (h3-book-order-product-next
            goal (h3-book-order-bounds-with-library bounds library))))

(defun h3-book-order-product-bound (library goal bounds)
  (h3-book-order-expose-result (h3-book-order-product-bound-with-bounds library goal bounds)))

(defun h3-book-order-product-zero-align (library equation comparison product position)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((exchanged (library-library-axiom library "COMMUTATIVITY-OF-*" (cdr product)))
         (reflexive (proof-proof-reflexive proof comparison))
         (original (proof-proof-rewrite proof reflexive exchanged (list 1 2 position))))
      (proof-proof-chain proof original (list equation)))))

(defun h3-book-order-product-zero-factor (bounds index product comparison position orientation strict)
  (h3-book-order-with-results bounds
      ((factor (proof-term-at product index))
       (scalar (h3-book-order-bounds-rational bounds factor))
       (signs (h3-book-order-selected-sign-with-bounds
               (h3-book-order-bounds-lib bounds) bounds scalar) :bounds))
    (if (not signs)
        (cons nil bounds)
      (h3-book-order-with-results bounds
          ((term (proof-term-at product (- 3 index)))
           (rational (let ((typed (h3-book-order-bounds-rational bounds term)))
                       (if (h3-rewrite-unproved-p typed) nil typed)))
           (library (h3-book-order-bounds-lib bounds))
           (equation (if rational
                         (h3-book-signs-rational-scaling-with-library
                          library rational scalar signs orientation)
                       (h3-book-signs-scaled-comparison-with-library
                        library term scalar signs orientation))
                     :library)
           (equation (if (equal index 1)
                         (h3-book-order-product-zero-align (h3-book-order-bounds-lib bounds)
                                                           equation comparison product position)
                       equation))
           (reduced (h3-book-order-step-at equation 2))
           (step (h3-book-order-bounds-bound-with-bounds
                  bounds (if strict reduced (proof-neg reduced))) :bounds))
        (cons (h3-book-order-transport (h3-book-order-bounds-lib bounds) strict step equation)
              bounds)))))

(defun h3-book-order-product-zero-factors (indices previous product comparison position orientation strict)
  (declare (xargs :measure (acl2-count indices)))
  (let ((step (car previous))
        (bounds (cdr previous)))
    (cond
     ((and step (not (h3-rewrite-unproved-p step))) previous)
     ((endp indices) (cons *h3-rewrite-unproved* bounds))
     (t
      (h3-book-order-product-zero-factors
       (cdr indices)
       (h3-book-order-product-zero-factor bounds (car indices) product comparison
                                           position orientation strict)
       product comparison position orientation strict)))))

(defun h3-book-order-product-zero-bound-with-bounds (library goal bounds)
  (let ((bounds (h3-book-order-bounds-with-library bounds library))
        (strict (proof-is-call goal *proof-less*)))
    (h3-book-order-with-results bounds
        ((comparison (if strict goal (proof-term-at goal 1)))
         (right (proof-term-at comparison 2)))
      (let* ((orientation (if (equal right *proof-zero*) -1 1))
             (position (if (< orientation 0) 1 2)))
        (h3-book-order-with-results bounds ((product (proof-term-at comparison position)))
          (h3-book-order-product-zero-factors '(2 1) (cons nil bounds) product comparison
                                             position orientation strict))))))

(defun h3-book-order-product-zero-bound (library goal bounds)
  (h3-book-order-expose-result
   (h3-book-order-product-zero-bound-with-bounds library goal bounds)))

(defun h3-book-order-operand-tactic (low high)
  (cond
   ((and (or (proof-is-call low *proof-times*) (equal low *proof-one*))
         (proof-is-call high *proof-times*))
    :product-bound)
   ((or (and (equal low *proof-zero*) (proof-is-call high *proof-times*))
        (and (equal high *proof-zero*) (proof-is-call low *proof-times*)))
    :product-zero-bound)
   (t nil)))

(defun h3-book-order-bound-tactic (goal)
  (proof-with-checked-results ((parts (h3-book-order-bound-parts goal)))
    (if (not parts)
        nil
      (let ((low (car parts))
            (high (cadr parts)))
        (proof-with-checked-results
            ((left (h3-book-quotient-reciprocal-factor low)))
          (if left
              :quotient-bound
            (proof-with-checked-results ((right (h3-book-quotient-reciprocal-factor high)))
              (if right :quotient-bound (h3-book-order-operand-tactic low high)))))))))

(defun h3-book-order-bound-atoms (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((not (proof-is-call term *proof-if*)) (list term))
   ((not (consp (cdddr term))) '(:failure "failure" ""))
   ((equal (cadddr term) *proof-false*)
    (proof-with-checked-results
        ((test (h3-book-order-bound-atoms (cadr term)))
         (branch (h3-book-order-bound-atoms (caddr term))))
      (append test branch)))
   (t (list term))))

(defun h3-book-order-comparisons-p (terms)
  (if (endp terms)
      t
    (proof-with-checked-results ((parts (h3-book-order-bound-parts (car terms))))
      (and parts (h3-book-order-comparisons-p (cdr terms))))))

(defun h3-book-order-has-tactic-p (terms)
  (and (consp terms)
       (proof-with-checked-results ((tactic (h3-book-order-bound-tactic (car terms))))
         (if tactic t (h3-book-order-has-tactic-p (cdr terms))))))

(defun h3-book-order-nonlinear-theorem-prove-solve (target bounds)
  (declare (xargs :measure (acl2-count target)))
  (if (proof-is-call target *proof-if*)
      (if (not (consp (cddr target)))
          (cons '(:failure "failure" "") bounds)
        (let ((test (cadr target))
              (branch (caddr target)))
          (h3-book-order-with-results bounds
              ((result (h3-book-order-nonlinear-theorem-prove-solve branch bounds) :bounds)
               (condition (h3-book-order-nonlinear-theorem-prove-solve test bounds) :bounds)
               (proof (library-library-proof (h3-book-order-bounds-lib bounds)))
               (selected (proof-proof-select proof target condition)))
            (cons (proof-proof-transport proof result selected) bounds))))
    (h3-book-order-with-results bounds ((tactic (h3-book-order-bound-tactic target)))
      (let ((library (h3-book-order-bounds-lib bounds)))
        (case tactic
          (:quotient-bound (h3-book-order-quotient-bound-with-bounds library target bounds 0))
          (:product-bound (h3-book-order-product-bound-with-bounds library target bounds))
          (:product-zero-bound (h3-book-order-product-zero-bound-with-bounds library target bounds))
          (otherwise (h3-book-order-bounds-bound-with-bounds bounds target)))))))

(defun h3-book-order-nonlinear-theorem-prove (premises library goal)
  (let ((bounds (h3-book-order-bounds-init library premises)))
    (if (failure-p bounds)
        (cons bounds library)
      (let ((result (h3-book-order-nonlinear-theorem-prove-solve goal bounds)))
        (cons (car result) (h3-book-order-bounds-lib (cdr result)))))))

(defun h3-book-order-first-conditional (evidence)
  (if (endp evidence)
      nil
    (let ((term (caar evidence)))
      (if (proof-is-call term *proof-if*)
          (proof-with-checked-results ((alternative (proof-term-at term 3)))
            (if (equal alternative *proof-false*)
                (h3-book-order-first-conditional (cdr evidence))
              (cdar evidence)))
        (h3-book-order-first-conditional (cdr evidence))))))

(defun h3-book-order-conditional-branch (library goal evidence conditional test holds)
  (let* ((proof (library-library-proof library))
         (premises (proof-with-checked-results
                       ((guard (proof-proof-assume proof test holds))
                        (selected (proof-proof-prove-if proof conditional guard)))
                     (append evidence (list guard selected)))))
    (if (failure-p premises)
        (cons premises library)
      (h3-book-order-nonlinear-theorem-prove premises library goal))))

(defun h3-book-order-conditional-proof (library goal evidence conditional)
  (let ((test (h3-book-order-step-at conditional 1)))
    (if (failure-p test)
        (cons test library)
      (let* ((positive (h3-book-order-conditional-branch library goal evidence conditional test t))
             (library (cdr positive)))
        (if (failure-p (car positive))
            positive
          (let* ((negative (h3-book-order-conditional-branch
                            library goal evidence conditional test nil))
                 (library (cdr negative)))
            (if (failure-p (car negative))
                negative
              (cons (proof-proof-cases (library-library-proof library) test
                                       (car positive) (car negative))
                    library))))))))

(defun h3-book-order-nonlinear-retry (result goal evidence)
  (let* ((library (cdr result))
         (conditional (proof-with-checked-results
                          ((bounds (h3-book-order-bounds-init library evidence)))
                        (h3-book-order-first-conditional (h3-book-order-bounds-evidence bounds)))))
    (cond ((failure-p conditional) (cons conditional library))
          (conditional (h3-book-order-conditional-proof library goal evidence conditional))
          (t result))))

(defun h3-book-order-prove-implication (library guard goal)
  (let ((assumed (proof-proof-assume (library-library-proof library) guard t)))
    (if (failure-p assumed)
        (cons assumed library)
      (let* ((evidence (list assumed))
             (result (h3-book-order-nonlinear-theorem-prove evidence library goal))
             (result (if (h3-rewrite-unproved-p (car result))
                         (h3-book-order-nonlinear-retry result goal evidence)
                       result))
             (library (cdr result)))
        (if (failure-p (car result))
            result
          (cons (h3-rewrite-implication library guard (car result)) library))))))

(defun h3-book-order-nonlinear-theorem-with-library (library formula)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil library)
    (let ((parts (proof-list-of-length (cdr formula) 2)))
      (if (failure-p parts)
          (cons parts library)
        (let* ((guard (car parts))
               (goal (cadr parts))
               (eligible (proof-with-checked-results
                             ((atoms (h3-book-order-bound-atoms goal))
                              (comparisons (h3-book-order-comparisons-p atoms)))
                           (and comparisons (h3-book-order-has-tactic-p atoms)))))
          (cond ((failure-p eligible) (cons eligible library))
                (eligible (h3-book-order-prove-implication library guard goal))
                (t (cons nil library))))))))

(defun h3-book-order-nonlinear-theorem (library formula)
  (let ((result (h3-book-order-nonlinear-theorem-with-library library formula)))
    (if (car result) (h3-book-order-expose-result result) nil)))
