(in-package "BOYMOO-PROOFS")

(include-book "scope-tree")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::gen-lambda-args boymoo-compiler::gen-term boymoo-compiler::gen-slot
                    boymoo-compiler::bind-formals boymoo-compiler::bind-formal boymoo-compiler::variable-name-p
                    boymoo-compiler::gen-push boymoo-compiler::gen-max boymoo-compiler::table-tree-get
                    boymoo-compiler::table-tree-put))

(defun generated-formals-ready-p (formals scope)
  (if (atom formals)
      (null formals)
    (and (boymoo-compiler::variable-name-p (car formals))
         (not (member-equal (car formals) (cdr formals)))
         (not (boymoo-compiler::table-tree-get (car formals) scope))
         (generated-formals-ready-p (cdr formals) scope))))

(defun generated-bind-slots (formals slots scope)
  (if (atom formals)
      scope
    (generated-bind-slots (cdr formals) (cdr slots)
                          (boymoo-compiler::bind-formal (car formals) (car slots) scope))))

(local
 (defthm generated-variable-text-is-a-string
   (implies (boymoo-compiler::variable-name-p formal) (stringp formal))
   :hints (("Goal" :in-theory (enable boymoo-compiler::variable-name-p)))))

(defthm generated-bind-formal-preserves-scope-and-lookup
  (let ((after (boymoo-compiler::bind-formal formal slot scope)))
    (implies (and (stringp query) (boymoo-compiler::variable-name-p formal)
                  (not (boymoo-compiler::table-tree-get formal scope))
                  (generated-scope-tree-p scope nil nil))
             (and (generated-scope-tree-p after nil nil)
                  (equal (boymoo-compiler::table-tree-get query after)
                         (if (equal query formal) slot (boymoo-compiler::table-tree-get query scope))))))
  :hints (("Goal"
           :use (:instance generated-scope-insertion-preserves-lookup-and-order
                           (key formal) (value slot) (tree scope) (lower nil) (upper nil))
           :in-theory (enable boymoo-compiler::bind-formal generated-scope-key-between-p)))
  :rule-classes nil)

(local
 (defthm generated-distinct-formal-leaves-other-names-ready
   (implies (and (generated-scope-tree-p scope nil nil) (boymoo-compiler::variable-name-p formal)
                 (not (boymoo-compiler::table-tree-get formal scope)) (not (member-equal formal others))
                 (generated-formals-ready-p others scope))
            (generated-formals-ready-p others (boymoo-compiler::bind-formal formal slot scope)))
   :hints (("Goal" :induct (len others))
           ("Subgoal *1/1" :use (:instance generated-bind-formal-preserves-scope-and-lookup (query (car others)))))
   :rule-classes nil))

(defthm generated-paired-names-omit-absent-name
  (implies (not (member-equal name formals))
           (not (assoc-equal name (pairlis$ formals slots))))
  :hints (("Goal" :induct (pairlis$ formals slots))))

(defthm generated-binding-list-preserves-scope-and-lookup
  (let* ((after (generated-bind-slots formals slots scope))
         (binding (assoc-equal query (pairlis$ formals slots))))
    (implies (and (stringp query) (generated-formals-ready-p formals scope)
                  (generated-scope-tree-p scope nil nil))
             (and (generated-scope-tree-p after nil nil)
                  (equal (boymoo-compiler::table-tree-get query after)
                         (if binding (cdr binding) (boymoo-compiler::table-tree-get query scope))))))
  :hints (("Goal" :induct (generated-bind-slots formals slots scope))
          ("Subgoal *1/2"
           :use ((:instance generated-distinct-formal-leaves-other-names-ready
                            (formal (car formals)) (slot (car slots)) (others (cdr formals)))
                 (:instance generated-bind-formal-preserves-scope-and-lookup (formal (car formals)) (slot (car slots))))))
  :rule-classes nil)

(defun generated-lambda-slots (args scope depth)
  (if (atom args)
      nil
    (if (atom (car args))
        (cons (boymoo-compiler::gen-slot (car args) scope) (generated-lambda-slots (cdr args) scope depth))
      (cons depth (generated-lambda-slots (cdr args) scope (1+ depth))))))

(defun generated-lambda-push-count (args)
  (if (atom args)
      0
    (+ (if (consp (car args)) 1 0) (generated-lambda-push-count (cdr args)))))

(local
 (defun generated-lambda-slot-induction (args formals scope body-scope depth context code high serial)
   (cond ((or (atom args) (atom formals)) (list body-scope depth code high serial))
         ((atom (car args))
          (generated-lambda-slot-induction
           (cdr args) (cdr formals) scope
           (boymoo-compiler::bind-formal (car formals) (boymoo-compiler::gen-slot (car args) scope) body-scope)
           depth context code high serial))
         (t
          (mv-let (code high serial)
            (boymoo-compiler::gen-term (car args) scope depth nil context code high serial)
            (generated-lambda-slot-induction (cdr args) (cdr formals) scope
                                             (boymoo-compiler::bind-formal (car formals) depth body-scope)
                                             (1+ depth) context (boymoo-compiler::gen-push code)
                                             (boymoo-compiler::gen-max high (1+ depth)) serial))))))

(defthm generated-lambda-arguments-install-aliased-and-pushed-slots
  (let ((out (boymoo-compiler::gen-lambda-args args formals scope body-scope depth context code high serial)))
    (implies (and (natp depth) (equal (len args) (len formals)))
             (and (equal (mv-nth 3 out)
                         (generated-bind-slots formals (generated-lambda-slots args scope depth) body-scope))
                  (equal (mv-nth 4 out) (+ depth (generated-lambda-push-count args))))))
  :hints (("Goal"
           :induct (generated-lambda-slot-induction args formals scope body-scope depth context code high serial)
           :in-theory (enable boymoo-compiler::gen-lambda-args))))

(defthm generated-lambda-scope-looks-up-formal-slots
  (let* ((slots (generated-lambda-slots args scope depth))
         (out (boymoo-compiler::gen-lambda-args args formals scope nil depth context code high serial))
         (body-scope (mv-nth 3 out)))
    (implies (and (stringp query) (natp depth) (equal (len args) (len formals))
                  (generated-formals-ready-p formals nil))
             (and (generated-scope-tree-p body-scope nil nil)
                  (equal (boymoo-compiler::table-tree-get query body-scope)
                         (cdr (assoc-equal query (pairlis$ formals slots)))))))
  :hints (("Goal"
           :use (:instance generated-binding-list-preserves-scope-and-lookup
                           (scope nil) (slots (generated-lambda-slots args scope depth)))
           :in-theory (enable generated-scope-tree-p boymoo-compiler::table-tree-get)))
  :rule-classes nil)

(defun generated-consecutive-slots (count slot)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons slot (generated-consecutive-slots (1- count) (1+ slot)))))

(defthm generated-function-bindings-use-consecutive-slots
  (equal (boymoo-compiler::bind-formals formals slot scope)
         (generated-bind-slots formals (generated-consecutive-slots (len formals) slot) scope))
  :hints (("Goal" :induct (boymoo-compiler::bind-formals formals slot scope)
                  :in-theory (enable boymoo-compiler::bind-formals))))

(defthm generated-function-scope-looks-up-entry-slots
  (implies (and (stringp query) (generated-formals-ready-p formals nil))
           (let ((scope (boymoo-compiler::bind-formals formals 0 nil)))
             (and (generated-scope-tree-p scope nil nil)
                  (equal (boymoo-compiler::table-tree-get query scope)
                         (cdr (assoc-equal query (pairlis$ formals (generated-consecutive-slots (len formals) 0))))))))
  :hints (("Goal"
           :use (:instance generated-binding-list-preserves-scope-and-lookup
                           (scope nil) (slots (generated-consecutive-slots (len formals) 0)))
           :in-theory (enable generated-scope-tree-p boymoo-compiler::table-tree-get)))
  :rule-classes nil)
