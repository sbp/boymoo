(in-package "BOYMOO-PROOFS")

(include-book "generator-inputs")

(logic)
(set-verify-guards-eagerness 0)

(set-irrelevant-formals-ok t)

; The branches expose the recursive calls of the three generator functions
; together with the accumulator, scope, and counters at each call.
(defun assembly-generator-induction
    (kind term formals scope body-scope depth tail context code high serial)
  (declare (xargs :measure (+ (* 2 (acl2-count term)) (if (eq kind :term) 1 0))))
  (case kind
    (:term
     (let ((head (car term))
           (args (cdr term)))
       (cond
        ((boymoo-compiler::gen-simple-p term) nil)
        ((equal head boymoo-compiler::*if-name*)
         (if (not (equal (length args) 3))
             nil
           (mv-let (test-code test-high test-serial)
             (boymoo-compiler::gen-term (car args) scope depth nil context code high serial)
             (let* ((yes (boymoo-compiler::gen-local test-serial))
                    (no (boymoo-compiler::gen-local (+ test-serial 1)))
                    (done (boymoo-compiler::gen-local (+ test-serial 2)))
                    (yes-code (boymoo-compiler::gen-emit
                               (list '(:cmp 0 34) (list :b-cond :ne yes)
                                     (list :b no) (list :label yes)) test-code)))
               (mv-let (then-code then-high then-serial)
                 (boymoo-compiler::gen-term (cadr args) scope depth tail context
                                            yes-code test-high (+ test-serial 3))
                 (let ((no-code (cons (list :label no)
                                      (if tail then-code (cons (list :b done) then-code)))))
                   (list (assembly-generator-induction
                          :term (car args) nil scope nil depth nil context code high serial)
                         (assembly-generator-induction
                          :term (cadr args) nil scope nil depth tail context
                          yes-code test-high (+ test-serial 3))
                         (assembly-generator-induction
                          :term (caddr args) nil scope nil depth tail context
                          no-code then-high then-serial))))))))
        ((and (boymoo-compiler::gen-mbe-p head args) (equal (length args) 3))
         (assembly-generator-induction
          :term (caddr args) nil scope nil depth tail context code high serial))
        ((consp head)
         (if (or (not (equal (car head) "COMMON-LISP::LAMBDA"))
                 (not (consp (cddr head))) (cdddr head)
                 (and (atom (cadr head)) (not (equal (cadr head) boymoo-compiler::*nil-name*))))
             nil
           (let ((lambda-formals (boymoo-compiler::declaration-list (cadr head))))
             (mv-let (arg-code arg-high arg-serial lambda-scope top)
               (boymoo-compiler::gen-lambda-args args lambda-formals scope nil depth
                                                 context code high serial)
               (list (assembly-generator-induction
                      :lambda-args args lambda-formals scope nil depth nil context code high serial)
                     (assembly-generator-induction
                      :term (caddr head) nil lambda-scope nil top tail context
                      arg-code arg-high arg-serial))))))
        (t
         (mv-let (target expected routine)
           (boymoo-compiler::gen-call-info head context)
           (declare (ignore target))
           (if (or (and expected (not (equal (length args) expected)))
                   (and routine (boymoo-compiler::gen-simple-args-p args)))
               nil
             (assembly-generator-induction
              :args args nil scope nil depth nil context code high serial)))))))
    (:args
     (if (atom term)
         nil
       (mv-let (arg-code arg-high arg-serial)
         (boymoo-compiler::gen-term (car term) scope depth nil context code high serial)
         (list (assembly-generator-induction
                :term (car term) nil scope nil depth nil context code high serial)
               (assembly-generator-induction
                :args (cdr term) nil scope nil (+ depth 1) nil context
                (boymoo-compiler::gen-push arg-code)
                (boymoo-compiler::gen-max arg-high (+ depth 1)) arg-serial)))))
    (otherwise
     (cond ((or (atom term) (atom formals)) nil)
           ((atom (car term))
            (assembly-generator-induction
             :lambda-args (cdr term) (cdr formals) scope
             (boymoo-compiler::bind-formal
              (car formals) (boymoo-compiler::gen-slot (car term) scope) body-scope)
             depth nil context code high serial))
           (t
            (mv-let (arg-code arg-high arg-serial)
              (boymoo-compiler::gen-term (car term) scope depth nil context code high serial)
              (list (assembly-generator-induction
                     :term (car term) nil scope nil depth nil context code high serial)
                    (assembly-generator-induction
                     :lambda-args (cdr term) (cdr formals) scope
                     (boymoo-compiler::bind-formal (car formals) depth body-scope)
                     (+ depth 1) nil context (boymoo-compiler::gen-push arg-code)
                     (boymoo-compiler::gen-max arg-high (+ depth 1)) arg-serial))))))))

(set-irrelevant-formals-ok nil)

(defun assembly-generator-result (kind term formals scope body-scope depth tail context code high serial)
  (case kind
    (:term
     (mv-let (result-code result-high result-serial)
       (boymoo-compiler::gen-term term scope depth tail context code high serial)
       (list result-code result-high result-serial)))
    (:args
     (mv-let (result-code result-high result-serial)
       (boymoo-compiler::gen-args term scope depth context code high serial)
       (list result-code result-high result-serial)))
    (otherwise
     (mv-let (result-code result-high result-serial result-scope result-depth)
       (boymoo-compiler::gen-lambda-args term formals scope body-scope depth context code high serial)
       (list result-code result-high result-serial result-scope result-depth)))))
