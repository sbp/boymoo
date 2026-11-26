(in-package "BOYMOO-PROOFS")

(include-book "source")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::gen-term boymoo-compiler::gen-lambda-args
                    boymoo-compiler::gen-slot boymoo-compiler::bind-formal
                    boymoo-compiler::gen-simple-p boymoo-compiler::gen-drop
                    boymoo-model::core-eval-step proof-environment-p proof-world-machine
                    proof-machine-value-p proof-reg-value-p proof-load-word generated-load-word))

(defthm generated-single-variable-lambda-uses-caller-slot
  (let* ((slot (boymoo-compiler::gen-slot actual-text scope))
         (body-scope (boymoo-compiler::table-node (cons formal-text slot) nil nil))
         (compiled (boymoo-compiler::gen-lambda-args (list actual-text) (list formal-text) scope nil
                                                    depth context code high serial)))
    (implies (and (stringp actual-text) (boymoo-compiler::variable-name-p formal-text) (natp slot))
             (and (equal compiled (mv code high serial body-scope depth))
                  (equal (boymoo-compiler::gen-slot formal-text (mv-nth 3 compiled)) slot))))
  :hints (("Goal"
           :expand ((boymoo-compiler::gen-lambda-args (list actual-text) (list formal-text) scope nil
                                                     depth context code high serial)
                    (:free (body-scope)
                           (boymoo-compiler::gen-lambda-args nil nil scope body-scope
                                                            depth context code high serial))
                    (:free (tree) (boymoo-compiler::gen-slot formal-text tree)))
           :in-theory (e/d (boymoo-compiler::bind-formal boymoo-compiler::table-tree-get
                           boymoo-compiler::table-tree-put boymoo-compiler::table-node)
                          (boymoo-compiler::variable-name-p))))
  :rule-classes nil)

(defthm generated-single-variable-lambda-emits-body
  (let* ((slot (boymoo-compiler::gen-slot actual-text scope))
         (compiled (boymoo-compiler::gen-term
                    (list (list "COMMON-LISP::LAMBDA" (list formal-text) body-text) actual-text)
                    scope depth tail context code high serial))
         (body (boymoo-compiler::gen-term
                body-text (boymoo-compiler::table-node (cons formal-text slot) nil nil)
                depth tail context code high serial)))
    (implies (and (stringp actual-text) (boymoo-compiler::variable-name-p formal-text) (natp slot))
             (and (equal (mv-nth 0 compiled) (mv-nth 0 body))
                  (equal (mv-nth 1 compiled) (mv-nth 1 body))
                  (equal (mv-nth 2 compiled) (mv-nth 2 body)))))
  :hints (("Goal"
           :use generated-single-variable-lambda-uses-caller-slot
           :expand (boymoo-compiler::gen-term
                    (list (list "COMMON-LISP::LAMBDA" (list formal-text) body-text) actual-text)
                    scope depth tail context code high serial)
           :in-theory (e/d (boymoo-compiler::gen-simple-p boymoo-compiler::gen-drop
                           boymoo-compiler::gen-address boymoo-compiler::declaration-list)
                          (boymoo-compiler::variable-name-p))))
  :rule-classes nil)

(defthm generated-single-variable-lambda-evaluates-body
  (implies (and (symbolp actual) (symbolp formal) (natp fuel) (< 2 fuel)
                (assoc-eq actual env))
           (equal (boymoo-model::core-eval-step :term (list (list 'lambda (list formal) body) actual)
                                                env program fuel)
                  (boymoo-model::core-eval-step :term body (list (cons formal (cdr (assoc-eq actual env))))
                                                program (1- fuel))))
  :hints (("Goal"
           :use (:instance generated-source-arguments-first-then-rest
                           (first actual) (rest nil) (fuel (1- fuel)))
           :expand (boymoo-model::core-eval-step :terms nil env program (- fuel 2))))
  :rule-classes nil)

(defthm generated-single-variable-lambda-environment
  (let ((body-env (list (cons formal (cdr (assoc-eq actual env))))))
    (implies (and (symbolp formal) (symbolp actual)
                  (proof-environment-p bindings env frame world objects packages)
                  (member-equal (cons actual slot) bindings))
             (proof-environment-p (list (cons formal slot)) body-env frame world objects packages)))
  :hints (("Goal"
           :use (:instance generated-environment-binding (variable actual))
           :expand ((proof-environment-p (list (cons formal slot))
                                         (list (cons formal (cdr (assoc-eq actual env))))
                                         frame world objects packages)
                    (:free (env) (proof-environment-p nil env frame world objects packages)))
           :in-theory (enable generated-load-word)))
  :rule-classes nil)
