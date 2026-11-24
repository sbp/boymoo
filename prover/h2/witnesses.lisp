(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-witnesses-iff* (proof-sym "IFF" "ACL2"))
(defconst *h2-witnesses-implies* (proof-sym "IMPLIES" "ACL2"))

(mutual-recursion
 (defun h2-witnesses-rename-functions (term names)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) term)
    ((endp term) (proof-index-failure))
    (t
     (let ((head (car term)))
       (proof-with-checked-results
        ((head
          (if (proof-compound head)
              (if (consp (cddr head))
                  (proof-with-checked-results
                   ((body (h2-witnesses-rename-functions (caddr (car term)) names)))
                   (list (car head) (cadr head) body))
                (proof-index-failure))
            (table-get names head head)))
         (arguments (h2-witnesses-rename-arguments (cdr term) names)))
        (cons head arguments))))))
 (defun h2-witnesses-rename-arguments (arguments names)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results
      ((first (h2-witnesses-rename-functions (car arguments) names))
       (rest (h2-witnesses-rename-arguments (cdr arguments) names)))
      (cons first rest)))))

(defun h2-witnesses-witness-formals-from (remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons (proof-sym (concatenate 'string "H2-ARG-" (decimal-text index)) "ACL2")
          (h2-witnesses-witness-formals-from (1- remaining) (1+ index)))))

(defun h2-witnesses-witness-formals (arity)
  (h2-witnesses-witness-formals-from arity 1))

(defun h2-witnesses-compound-argument-p (arguments)
  (and (consp arguments)
       (or (proof-compound (car arguments))
           (h2-witnesses-compound-argument-p (cdr arguments)))))

(defun h2-witnesses-record-equation (equation target unknown equations)
  (if (not target)
      (cons equation equations)
    (proof-with-checked-results
     ((pair (proof-list-of-length equation 2)))
     (let* ((call (car pair))
            (body (cadr pair))
            (formals (cdr call))
            (candidate (list formals body)))
       (if (and (proof-is-call call (car target))
                (not (h2-witnesses-compound-argument-p formals))
                (equal (len (proof-unique formals)) (cadr target))
                (subsetp-equal (h2-search-variables body) formals))
           (proof-with-checked-results
            ((renamed (h2-witnesses-rename-functions body unknown)))
            (if (and (equal renamed body) (not (member-equal candidate equations)))
                (cons candidate equations)
              equations))
         equations)))))

(defun h2-witnesses-pair (value)
  (if (stringp value)
      (if (equal (length value) 2)
          (list (seq-slice value 0 1) (seq-slice value 1 2))
        (proof-length-failure 2 (length value)))
    (proof-list-of-length value 2)))

(defun h2-witnesses-equations (formula target unknown equations)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((proof-is-call formula *h2-witnesses-implies*)
    (if (consp (cddr formula))
        (h2-witnesses-equations (caddr formula) target unknown equations)
      (proof-index-failure)))
   ((proof-is-call formula *proof-if*)
    (cond
     ((endp (cdddr formula)) (proof-index-failure))
     ((equal (cadddr formula) *proof-false*)
      (proof-with-checked-results
       ((equations (h2-witnesses-equations (cadr formula) target unknown equations)))
       (h2-witnesses-equations (caddr formula) target unknown equations)))
     (t equations)))
   ((or (proof-is-call formula *proof-equal*)
        (proof-is-call formula *h2-witnesses-iff*))
    (proof-with-checked-results
     ((equations (h2-witnesses-record-equation (cdr formula) target unknown equations))
      (right (proof-term-at formula 2)))
     (h2-witnesses-record-equation (list right (cadr formula)) target unknown equations)))
   (t equations)))

(defun h2-witnesses-definitions-in (formula)
  (proof-with-checked-results ((equations (h2-witnesses-equations formula nil nil nil)))
    (reverse equations)))

(defun h2-witnesses-formula-candidates (formulas name arity unknown candidates)
  (if (endp formulas)
      candidates
    (proof-with-checked-results
     ((pair (h2-witnesses-pair (car formulas)))
      (candidates (h2-witnesses-equations (cadr pair) (list name arity) unknown candidates)))
     (h2-witnesses-formula-candidates (cdr formulas) name arity unknown candidates))))

(defun h2-witnesses-fallback-candidates (bodies formals)
  (if (endp bodies)
      nil
    (cons (list formals (car bodies))
          (h2-witnesses-fallback-candidates (cdr bodies) formals))))

(defun h2-witnesses-possible-bodies (name arity formulas unknown)
  (proof-with-checked-results
   ((candidates (h2-witnesses-formula-candidates formulas name arity unknown nil)))
   (let* ((formals (h2-witnesses-witness-formals arity))
          (bodies (append (list *proof-false* *proof-true*) formals (list *proof-zero*))))
     (proof-unique (append (reverse candidates)
                           (h2-witnesses-fallback-candidates bodies formals))))))

(defun h2-witnesses-names (functions identifier index)
  (if (endp functions)
      nil
    (cons (proof-sym (concatenate 'string "SELF-H2-WITNESS-" identifier "-" (decimal-text index))
                     "ACL2")
          (h2-witnesses-names (cdr functions) identifier (1+ index)))))

(defun h2-witnesses-replacements (functions witnesses names)
  (if (or (endp functions) (endp witnesses))
      names
    (proof-with-checked-results
     ((pair (h2-witnesses-pair (car functions))))
     (h2-witnesses-replacements (cdr functions) (cdr witnesses)
                                (table-put names (car pair) (car witnesses))))))

(defun h2-witnesses-candidates (functions formulas names)
  (if (endp functions)
      nil
    (proof-with-checked-results
     ((pair (h2-witnesses-pair (car functions)))
      (first (h2-witnesses-possible-bodies (car pair) (cadr pair) formulas names))
      (rest (h2-witnesses-candidates (cdr functions) formulas names)))
     (cons first rest))))

(defun h2-witnesses-goals (formulas names)
  (if (endp formulas)
      nil
    (proof-with-checked-results
     ((pair (h2-witnesses-pair (car formulas)))
      (first (h2-witnesses-rename-functions (cadr pair) names))
      (rest (h2-witnesses-goals (cdr formulas) names)))
     (cons first rest))))

(defun h2-witnesses-constant-assignment (functions value)
  (if (endp functions)
      nil
    (cons (list (h2-witnesses-witness-formals (cadar functions)) value)
          (h2-witnesses-constant-assignment (cdr functions) value))))

(defun h2-witnesses-first-product (tail limit candidate products)
  (if (or (zp limit) (endp tail))
      products
    (h2-witnesses-first-product (cdr tail) (1- limit) candidate
                                (cons (cons candidate (car tail)) products))))

(defun h2-witnesses-first-products (candidates tail limit products)
  (if (or (zp limit) (endp candidates))
      products
    (let ((next (h2-witnesses-first-product tail limit (car candidates) products)))
      (h2-witnesses-first-products (cdr candidates) tail
                                  (- limit (- (len next) (len products))) next))))

(defun h2-witnesses-products (candidates)
  (if (endp candidates)
      (list nil)
    (let ((tail (h2-witnesses-products (cdr candidates))))
      (reverse (h2-witnesses-first-products (car candidates) tail 20 nil)))))

(defun h2-witnesses-assignments (functions candidates)
  (seq-slice
   (proof-unique (list* (h2-witnesses-constant-assignment functions *proof-false*)
                        (h2-witnesses-constant-assignment functions *proof-true*)
                        (h2-witnesses-products candidates)))
   0 20))

(defun h2-witnesses-request-p (value)
  (and (consp value) (eq (car value) :h2-witnesses-request)))

(defun h2-witnesses-request-operation (request)
  (cadr request))

(defun h2-witnesses-request-proof (request)
  (caddr request))

(defun h2-witnesses-request-args (request)
  (cadddr request))

(defun h2-witnesses-request (operation proof args)
  (list :h2-witnesses-request operation proof args))

(defun h2-witnesses-install (proof witnesses assignment)
  (declare (xargs :measure (acl2-count witnesses)))
  (if (or (endp witnesses) (endp assignment))
      proof
    (proof-with-checked-results
     ((library (library-library-definition (h2-search-search-library proof)
                                           (car witnesses) (caar assignment) (cadar assignment))))
     (h2-witnesses-install (h2-search-search-with-library proof library)
                          (cdr witnesses) (cdr assignment)))))

(defun h2-witnesses-without-names (entries names)
  (if (endp entries)
      nil
    (if (member-equal (caar entries) names)
        (h2-witnesses-without-names (cdr entries) names)
      (cons (car entries) (h2-witnesses-without-names (cdr entries) names)))))

(defun h2-witnesses-rollback (proof witnesses count)
  (let* ((library (h2-search-search-library proof))
         (base (library-library-proof library))
         (facts (h2-witnesses-without-names (proof-proof-facts base) witnesses))
         (definitions (h2-witnesses-without-names (proof-proof-definitions base) witnesses))
         (base (proof-proof-with-kind
                (proof-make-proof facts definitions (proof-proof-primitives base))
                (proof-proof-kind base)))
         (entries (seq-slice (library-library-entries library) 0 count)))
    (h2-search-search-with-library proof (library-make-library base entries))))

(defun h2-witnesses-functions-used (calls definitions)
  (if (endp calls)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car calls) 0)))
     (let ((definition (assoc-equal name definitions)))
       (proof-with-checked-results
        ((body (if definition (proof-term-at (cdr definition) 1) nil))
         (small (cond ((not definition) nil)
                      ((integerp body) '(:failure "failure" ""))
                      ((stringp body) (<= (length body) 12))
                      (t (<= (len body) 12))))
         (rest (h2-witnesses-functions-used (cdr calls) definitions)))
        (if small (cons name rest) rest))))))

(defun h2-witnesses-unproved-p (result)
  (and (failure-p result) (equal (cadr result) "Unproved")))

(defun h2-witnesses-solve-reply (proof goal replies)
  (if (endp replies)
      (cons (h2-witnesses-request :solve proof (list goal 2500)) nil)
    (let ((reply (car replies)))
      (cons (if (failure-p reply) (cons reply proof) reply) (cdr replies)))))

(defun h2-witnesses-configuration-reply (proof goal definitions replies)
  (if (endp replies)
      (cons (h2-witnesses-request :configure-book proof (list definitions t)) nil)
    (let ((configured (car replies)))
      (if (failure-p configured)
          (cons (cons configured proof) (cdr replies))
        (h2-witnesses-solve-reply configured goal (cdr replies))))))

(defun h2-witnesses-goal-replies (proof goal witnesses replies)
  (if (endp replies)
      (cons (h2-witnesses-request :calls-in proof (list goal)) nil)
    (let ((calls (car replies)))
      (if (failure-p calls)
          (cons (cons calls proof) (cdr replies))
        (proof-with-checked-results
         ((used (h2-witnesses-functions-used
                 calls (proof-proof-definitions (library-library-proof (h2-search-search-library proof))))))
         (h2-witnesses-configuration-reply proof goal (append witnesses used) (cdr replies)))))))

(defun h2-witnesses-prove-goals (proof goals witnesses replies steps)
  (declare (xargs :measure (acl2-count goals)))
  (if (endp goals)
      (cons (cons (reverse steps) proof) replies)
    (proof-with-checked-results
     ((answer (h2-witnesses-goal-replies proof (car goals) witnesses replies)))
     (let ((result (car answer)))
       (if (or (h2-witnesses-request-p result) (failure-p (car result)))
           answer
         (h2-witnesses-prove-goals (cdr result) (cdr goals) witnesses (cdr answer)
                                   (cons (car result) steps)))))))

(defun h2-witnesses-prove-assignments (proof assignments goals root witnesses count replies)
  (declare (xargs :measure (acl2-count assignments)))
  (if (endp assignments)
      '(:failure "Unproved" "")
    (proof-with-checked-results
     ((proof (h2-witnesses-install proof witnesses (car assignments)))
      (answer (h2-witnesses-prove-goals proof goals witnesses replies nil)))
     (let* ((result (car answer))
            (value (car result))
            (proof (cdr result)))
       (cond
        ((h2-witnesses-request-p result) result)
        ((h2-witnesses-unproved-p value)
         (h2-witnesses-prove-assignments (h2-witnesses-rollback proof witnesses count)
                                         (cdr assignments) goals root witnesses count (cdr answer)))
        ((failure-p value) value)
        (t (proof-with-checked-results
            ((entry (proof-proof-entry "witness" root (cons root witnesses) value)))
            (cons entry proof))))))))

(defun h2-witnesses-prepare (data)
  (proof-with-checked-results
   ((data (h2-witnesses-pair data))
    (functions (car data))
    (formulas (cadr data))
    (first (proof-term-at functions 0))
    (root (proof-term-at first 0))
    (text (proof-write root))
    (witnesses (h2-witnesses-names functions (text-upper (seq-slice (siphash-hexdigest text) 0 16)) 0))
    (replacement (h2-witnesses-replacements functions witnesses nil))
    (candidates (h2-witnesses-candidates functions formulas replacement))
    (goals (h2-witnesses-goals formulas replacement)))
   (list :h2-witness-plan root witnesses goals (h2-witnesses-assignments functions candidates))))

(defun h2-witnesses-plan-root (plan)
  (cadr plan))

(defun h2-witnesses-plan-names (plan)
  (caddr plan))

(defun h2-witnesses-plan-goals (plan)
  (cadddr plan))

(defun h2-witnesses-plan-assignments (plan)
  (car (cddddr plan)))

(defun h2-witnesses-prove-prepared (proof plan replies)
  (if (failure-p plan)
      plan
    (h2-witnesses-prove-assignments proof (h2-witnesses-plan-assignments plan)
                                    (h2-witnesses-plan-goals plan)
                                    (h2-witnesses-plan-root plan)
                                    (h2-witnesses-plan-names plan)
                                    (len (library-library-entries (h2-search-search-library proof)))
                                    replies)))

(defun h2-witnesses-prove-witness (proof data replies)
  (proof-with-checked-results ((plan (h2-witnesses-prepare data)))
    (h2-witnesses-prove-prepared proof plan replies)))
