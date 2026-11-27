(in-package "BOYMOO-PROOFS")

(include-book "generator-induction")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-checked-bind-formal (name slot scope)
  (if (and (boymoo-compiler::variable-name-p name)
           (not (boymoo-compiler::table-tree-get name scope)))
      (mv t (boymoo-compiler::table-tree-put name slot scope))
    (mv nil nil)))

(defun assembly-checked-bind-formals (formals slot scope)
  (if (atom formals)
      (mv t scope)
    (mv-let (ok scope)
      (assembly-checked-bind-formal (car formals) slot scope)
      (if ok
          (assembly-checked-bind-formals (cdr formals) (+ 1 slot) scope)
        (mv nil nil)))))

(defun assembly-checked-gen-simple (term rd scope constants code)
  (if (atom term)
      (let ((slot (boymoo-compiler::table-tree-get term scope)))
        (if slot (mv t (boymoo-compiler::gen-frame-word rd slot code))
          (mv nil nil)))
    (if (and (stringp (cadr term)) (not (cddr term)))
        (let ((datum (boymoo-compiler::index-get (cadr term) constants)))
          (if datum (mv t (boymoo-compiler::gen-load-datum rd datum code))
            (mv nil nil)))
      (mv nil nil))))

(defun assembly-checked-gen-simple-args (args reg scope constants code)
  (if (atom args)
      (mv t code)
    (mv-let (ok code)
      (assembly-checked-gen-simple (car args) reg scope constants code)
      (if ok
          (assembly-checked-gen-simple-args (cdr args) (+ reg 1) scope constants code)
        (mv nil nil)))))

; The checked generator returns a status with the compiler's code,
; stack high-water mark, and serial counter. Argument binding also
; returns the scope and depth of the lambda body.
(mutual-recursion
 (defun assembly-checked-gen-term (term scope depth tail context code high serial)
   (declare (xargs :measure (* 2 (acl2-count term))))
   (if (boymoo-compiler::gen-simple-p term)
       (mv-let (ok code)
         (assembly-checked-gen-simple term 0 scope (caddr context) code)
         (if ok (mv t (boymoo-compiler::gen-finish tail code) high serial)
           (mv nil nil high serial)))
     (let ((head (car term))
           (args (cdr term)))
       (cond
        ((equal head boymoo-compiler::*if-name*)
         (if (not (equal (length args) 3))
             (mv nil nil high serial)
           (mv-let (ok code high serial)
             (assembly-checked-gen-term (car args) scope depth nil context code high serial)
             (if (not ok)
                 (mv nil nil high serial)
               (let* ((yes (boymoo-compiler::gen-local serial))
                      (no (boymoo-compiler::gen-local (+ serial 1)))
                      (done (boymoo-compiler::gen-local (+ serial 2)))
                      (code (boymoo-compiler::gen-emit
                             (list '(:cmp 0 34) (list :b-cond :ne yes)
                                   (list :b no) (list :label yes)) code)))
                 (mv-let (ok code high serial)
                   (assembly-checked-gen-term (cadr args) scope depth tail context code high (+ serial 3))
                   (if (not ok)
                       (mv nil nil high serial)
                     (let ((code (if tail code (cons (list :b done) code))))
                       (mv-let (ok code high serial)
                         (assembly-checked-gen-term
                          (caddr args) scope depth tail context
                          (cons (list :label no) code) high serial)
                         (mv ok (if tail code (cons (list :label done) code)) high serial))))))))))
        ((and (boymoo-compiler::gen-mbe-p head args) (equal (length args) 3))
         (mv-let (ok ignored-code ignored-high ignored-serial)
           (assembly-checked-gen-term (cadr args) scope depth nil context nil depth serial)
           (declare (ignore ignored-code ignored-high ignored-serial))
           (if ok (assembly-checked-gen-term (caddr args) scope depth tail context code high serial)
             (mv nil nil high serial))))
        ((consp head)
         (if (or (not (equal (car head) "COMMON-LISP::LAMBDA"))
                 (not (consp (cddr head))) (cdddr head)
                 (and (atom (cadr head)) (not (equal (cadr head) boymoo-compiler::*nil-name*))))
             (mv nil nil high serial)
           (mv-let (ok code high serial body-scope top)
             (assembly-checked-gen-lambda-args
              args (boymoo-compiler::declaration-list (cadr head)) scope nil
              depth context code high serial)
             (if (not ok)
                 (mv nil nil high serial)
               (mv-let (ok code high serial)
                 (assembly-checked-gen-term (caddr head) body-scope top tail context code high serial)
                 (mv ok (if tail code (boymoo-compiler::gen-drop (- top depth) code)) high serial))))))
        (t
         (mv-let (target expected routine)
           (boymoo-compiler::gen-call-info head context)
           (let ((arity (length args)))
             (cond
              ((and expected (not (equal arity expected))) (mv nil nil high serial))
              ((and routine (boymoo-compiler::gen-simple-args-p args))
               (mv-let (ok code)
                 (assembly-checked-gen-simple-args args 0 scope (caddr context) code)
                 (if (not ok)
                     (mv nil nil high serial)
                   (mv-let (code serial)
                     (boymoo-compiler::gen-routine target routine serial code)
                     (mv t (boymoo-compiler::gen-finish tail code) high serial)))))
              (t
               (mv-let (ok code high serial)
                 (assembly-checked-gen-args args scope depth context code high serial)
                 (cond
                  ((not ok) (mv nil nil high serial))
                  (routine
                   (mv-let (code serial)
                     (boymoo-compiler::gen-routine target routine serial
                                                  (boymoo-compiler::gen-argument-registers arity depth 0 code))
                     (mv t (if tail (boymoo-compiler::gen-finish t code)
                             (boymoo-compiler::gen-drop arity code)) high serial)))
                  (expected (mv t (boymoo-compiler::gen-defined-call target arity tail code) high serial))
                  (t (let ((datum (boymoo-compiler::index-get target (caddr context))))
                       (if datum
                           (mv t (cons '(:bl "rt:undefined")
                                       (boymoo-compiler::gen-load-datum 0 datum code))
                               high serial)
                         (mv nil nil high serial)))))))))))))))
 (defun assembly-checked-gen-args (args scope depth context code high serial)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (atom args)
       (mv t code high serial)
     (mv-let (ok code high serial)
       (assembly-checked-gen-term (car args) scope depth nil context code high serial)
       (if ok
           (assembly-checked-gen-args
            (cdr args) scope (+ depth 1) context (boymoo-compiler::gen-push code)
            (boymoo-compiler::gen-max high (+ depth 1)) serial)
         (mv nil nil high serial)))))
 (defun assembly-checked-gen-lambda-args (args formals scope body-scope depth context code high serial)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (cond ((atom args) (mv (not (consp formals)) code high serial body-scope depth))
         ((atom formals) (mv nil nil high serial body-scope depth))
         ((atom (car args))
          (let ((slot (boymoo-compiler::table-tree-get (car args) scope)))
            (mv-let (ok next-scope)
              (assembly-checked-bind-formal (car formals) slot body-scope)
              (if (and slot ok)
                  (assembly-checked-gen-lambda-args
                   (cdr args) (cdr formals) scope next-scope depth context code high serial)
                (mv nil nil high serial body-scope depth)))))
         (t
          (mv-let (ok code high serial)
            (assembly-checked-gen-term (car args) scope depth nil context code high serial)
            (if (not ok)
                (mv nil nil high serial body-scope depth)
              (mv-let (ok next-scope)
                (assembly-checked-bind-formal (car formals) depth body-scope)
                (if ok
                    (assembly-checked-gen-lambda-args
                     (cdr args) (cdr formals) scope next-scope (+ depth 1) context
                     (boymoo-compiler::gen-push code) (boymoo-compiler::gen-max high (+ depth 1)) serial)
                  (mv nil nil high serial body-scope depth)))))))))

(defun assembly-checked-gen-result (kind term formals scope body-scope depth tail context code high serial)
  (case kind
    (:term
     (mv-let (ok code high serial)
       (assembly-checked-gen-term term scope depth tail context code high serial)
       (list ok code high serial)))
    (:args
     (mv-let (ok code high serial)
       (assembly-checked-gen-args term scope depth context code high serial)
       (list ok code high serial)))
    (otherwise
     (mv-let (ok code high serial scope depth)
       (assembly-checked-gen-lambda-args term formals scope body-scope depth context code high serial)
       (list ok code high serial scope depth)))))

(local (in-theory (disable boymoo-compiler::index-get boymoo-compiler::variable-name-p
                           boymoo-compiler::table-tree-get boymoo-compiler::table-tree-put
                           boymoo-compiler::gen-frame-word boymoo-compiler::gen-load-datum
                           (:executable-counterpart boymoo-compiler::compiler-error))))

(defthm assembly-accepted-formal-bind-agrees
  (mv-let (ok result)
    (assembly-checked-bind-formal name slot scope)
    (implies ok
             (equal (boymoo-compiler::bind-formal name slot scope) result))))

(local (in-theory (disable assembly-checked-bind-formal boymoo-compiler::bind-formal)))

(defthm assembly-accepted-formals-agree
  (mv-let (ok result)
    (assembly-checked-bind-formals formals slot scope)
    (implies ok (equal (boymoo-compiler::bind-formals formals slot scope) result)))
  :hints (("Goal" :induct (assembly-checked-bind-formals formals slot scope))))

(defthm assembly-accepted-simple-generation-agrees
  (mv-let (ok result)
    (assembly-checked-gen-simple term rd scope constants code)
    (implies ok (equal (boymoo-compiler::gen-simple term rd scope constants code) result))))

(local (in-theory (disable assembly-checked-gen-simple boymoo-compiler::gen-simple)))

(defthm assembly-accepted-simple-args-agree
  (mv-let (ok result)
    (assembly-checked-gen-simple-args args reg scope constants code)
    (implies ok (equal (boymoo-compiler::gen-simple-args args reg scope constants code) result)))
  :hints (("Goal" :induct (assembly-checked-gen-simple-args args reg scope constants code))))

(local
 (defthm assembly-present-variable-uses-its-slot
   (implies (boymoo-compiler::table-tree-get name scope)
            (equal (boymoo-compiler::gen-slot name scope)
                   (boymoo-compiler::table-tree-get name scope)))))

(local
 (defthm assembly-present-constant-uses-its-datum
   (implies (boymoo-compiler::index-get text constants)
            (equal (boymoo-compiler::gen-datum text constants)
                   (boymoo-compiler::index-get text constants)))))

(local (in-theory (disable assembly-checked-gen-simple-args boymoo-compiler::gen-simple-args
                           boymoo-compiler::gen-simple-p boymoo-compiler::gen-simple-args-p
                           boymoo-compiler::gen-mbe-p boymoo-compiler::gen-slot
                           boymoo-compiler::gen-call-info boymoo-compiler::gen-datum
                           boymoo-compiler::gen-argument-registers boymoo-compiler::gen-defined-call
                           boymoo-compiler::gen-finish boymoo-compiler::gen-push boymoo-compiler::gen-drop
                           boymoo-compiler::gen-routine boymoo-compiler::gen-local boymoo-compiler::gen-emit
                           boymoo-compiler::declaration-list length)))

(defthm assembly-accepted-generation-agrees
  (let ((checked (assembly-checked-gen-result kind term formals scope body-scope depth
                                               tail context code high serial)))
    (implies (car checked)
             (equal (assembly-generator-result kind term formals scope body-scope depth
                                               tail context code high serial)
                    (cdr checked))))
  :hints (("Goal"
           :induct (assembly-generator-induction kind term formals scope body-scope depth
                                                 tail context code high serial)
           :in-theory (disable boymoo-compiler::gen-term boymoo-compiler::gen-args
                               boymoo-compiler::gen-lambda-args
                               assembly-checked-gen-term assembly-checked-gen-args
                               assembly-checked-gen-lambda-args)
           :expand ((:free (scope depth tail context code high serial)
                           (boymoo-compiler::gen-term term scope depth tail context code high serial))
                    (:free (scope depth context code high serial)
                           (boymoo-compiler::gen-args term scope depth context code high serial))
                    (:free (formals scope body-scope depth context code high serial)
                           (boymoo-compiler::gen-lambda-args term formals scope body-scope depth
                                                            context code high serial))
                    (:free (scope depth tail context code high serial)
                           (assembly-checked-gen-term term scope depth tail context code high serial))
                    (:free (scope depth context code high serial)
                           (assembly-checked-gen-args term scope depth context code high serial))
                    (:free (formals scope body-scope depth context code high serial)
                           (assembly-checked-gen-lambda-args term formals scope body-scope depth
                                                            context code high serial)))))
  :rule-classes nil)

(defthm assembly-accepted-term-generation-agrees
  (mv-let (ok checked-code checked-high checked-serial)
    (assembly-checked-gen-term term scope depth tail context code high serial)
    (implies ok
             (mv-let (actual-code actual-high actual-serial)
               (boymoo-compiler::gen-term term scope depth tail context code high serial)
               (and (equal actual-code checked-code)
                    (equal actual-high checked-high)
                    (equal actual-serial checked-serial)))))
  :hints (("Goal"
           :use ((:instance assembly-accepted-generation-agrees
                            (kind :term) (formals nil) (body-scope nil)))
           :in-theory (disable boymoo-compiler::gen-term assembly-checked-gen-term))))

(defun assembly-checked-gen-functions (definitions entry context serial code)
  (if (atom definitions)
      (mv t code)
    (let* ((definition (car definitions))
           (name (car definition))
           (formals (boymoo-compiler::declaration-list (cadr definition)))
           (arity (length formals)))
      (mv-let (bound scope)
        (assembly-checked-bind-formals formals 0 nil)
        (if (not bound)
            (mv nil nil)
          (mv-let (ok body high next)
            (assembly-checked-gen-term (caddr definition) scope arity t context nil arity (+ serial 2))
            (if (not ok)
                (mv nil nil)
              (let* ((code (if (equal name entry) (cons '(:label "rt:entry") code) code))
                     (code (cons (list :label (list :fn name)) code))
                     (code (boymoo-compiler::gen-prologue arity high serial code)))
                (assembly-checked-gen-functions
                 (cdr definitions) entry context next
                 (boymoo-compiler::reverse-onto
                  (boymoo-compiler::reverse-onto body nil) code))))))))))

(local (in-theory (disable assembly-checked-bind-formals boymoo-compiler::bind-formals
                           assembly-checked-gen-term boymoo-compiler::gen-term
                           boymoo-compiler::gen-prologue boymoo-compiler::reverse-onto)))

(defthm assembly-accepted-definition-generation-agrees
  (mv-let (ok result)
    (assembly-checked-gen-functions definitions entry context serial code)
    (implies ok
             (equal (boymoo-compiler::gen-functions definitions entry context serial code)
                    result)))
  :hints (("Goal" :induct (assembly-checked-gen-functions definitions entry context serial code))))
