(in-package "BOYMOO-COMPILER")

(include-book "../resolve")
(include-book "l1-well-formed")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable resolve-term resolve-args resolve-lambda-args
                    resolve-variable resolve-datum-word
                    table-tree-get index-get model-constant
                    boymoo-model::core-eval-step l1-eval-step))

(defthm p1-formal-number-count
  (equal (len (resolve-formal-numbers formals first)) (len formals)))

(local
 (defun p1-formal-index-induction (i formals first)
   (if (or (zp i) (endp formals))
       first
     (p1-formal-index-induction (1- i) (cdr formals) (1+ first)))))

(defthm p1-formal-number-at-index
  (implies (and (natp i) (natp first) (< i (len formals)))
           (equal (nth i (resolve-formal-numbers formals first)) (+ first i)))
  :hints (("Goal" :induct (p1-formal-index-induction i formals first)
           :expand ((resolve-formal-numbers formals first)))))

(defthm p1-immediate-constant-word
  (implies (and (integerp datum)
                (equal (index-get text constants) (cons :integer datum)))
           (equal (resolve-datum-word text constants) (model-integer-word datum)))
  :hints (("Goal" :in-theory (enable resolve-datum-word))))

(defthmd p1-resolved-variable
  (implies (and (stringp text) (table-tree-get text scope))
           (and (equal (mv-nth 0 (resolve-term text scope context next))
                       (list :var (table-tree-get text scope)))
                (equal (mv-nth 1 (resolve-term text scope context next)) next)))
  :hints (("Goal" :expand ((resolve-term text scope context next))
           :in-theory (enable resolve-variable))))

(defthmd p1-resolved-quote
  (implies (stringp text)
           (and (equal (mv-nth 0 (resolve-term (list *quote-name* text) scope context next))
                       (list :const (resolve-datum-word text (caddr context))))
                (equal (mv-nth 1 (resolve-term (list *quote-name* text) scope context next))
                       next)))
  :hints (("Goal" :expand ((resolve-term (list *quote-name* text) scope context next)))))

(defthmd p1-resolved-variable-agrees-with-core
  (let ((binding (assoc-equal (table-tree-get text scope) l1-env)))
    (implies (and (posp fuel) (stringp text) (symbolp name)
                  (table-tree-get text scope) binding
                  (equal (assoc-eq name core-env) (cons name (cdr binding))))
             (equal (l1-eval (mv-nth 0 (resolve-term text scope context next))
                                l1-env definitions constants program fuel)
                    (boymoo-model::core-eval name core-env program fuel))))
  :hints (("Goal" :in-theory (enable p1-resolved-variable l1-eval-step)
           :expand ((boymoo-model::core-eval-step :term name core-env program fuel)))))

(defthmd p1-resolved-quote-agrees-with-core
  (implies (and (posp fuel) (stringp text)
                (equal (model-constant (resolve-datum-word text (caddr context)) constants)
                       (boymoo-model::core-value datum)))
           (equal (l1-eval (mv-nth 0 (resolve-term (list *quote-name* text)
                                                       scope context next))
                              l1-env definitions constants program fuel)
                  (boymoo-model::core-eval (list 'quote datum) core-env program fuel)))
  :hints (("Goal" :in-theory (enable p1-resolved-quote l1-eval-step)
           :expand ((boymoo-model::core-eval-step :term (list 'quote datum) core-env program fuel)))))

(defthmd p1-resolved-mbe-selects-logical-term
  (and (equal (mv-nth 0
                     (resolve-term
                      (list "ACL2::RETURN-LAST" (list *quote-name* "ACL2::MBE1-RAW") executable logical)
                      scope context next))
              (mv-nth 0 (resolve-term logical scope context next)))
       (equal (mv-nth 1
                     (resolve-term
                      (list "ACL2::RETURN-LAST" (list *quote-name* "ACL2::MBE1-RAW") executable logical)
                      scope context next))
              (mv-nth 1 (resolve-term logical scope context next))))
  :hints (("Goal" :expand
           ((resolve-term
             (list "ACL2::RETURN-LAST" (list *quote-name* "ACL2::MBE1-RAW") executable logical)
             scope context next)))))

(defthmd p1-resolved-if
  (let* ((next1 (mv-nth 1 (resolve-term test scope context next)))
         (next2 (mv-nth 1 (resolve-term yes scope context next1))))
    (and (equal (mv-nth 0 (resolve-term (list *if-name* test yes no) scope context next))
                (list :if (mv-nth 0 (resolve-term test scope context next))
                      (mv-nth 0 (resolve-term yes scope context next1))
                      (mv-nth 0 (resolve-term no scope context next2))))
         (equal (mv-nth 1 (resolve-term (list *if-name* test yes no) scope context next))
                (mv-nth 1 (resolve-term no scope context next2)))))
  :hints (("Goal" :expand
           ((resolve-term (list *if-name* test yes no) scope context next)
            (resolve-args (list test yes no) scope context next)
            (:free (n) (resolve-args (list yes no) scope context n))
            (:free (n) (resolve-args (list no) scope context n))
            (:free (n) (resolve-args nil scope context n))))))

(defthmd p1-resolved-if-agrees-with-core
  (let* ((next1 (mv-nth 1 (resolve-term test scope context next)))
         (next2 (mv-nth 1 (resolve-term yes scope context next1)))
         (test-result (l1-eval (mv-nth 0 (resolve-term test scope context next))
                                  l1-env definitions constants program (1- fuel)))
         (yes-result (l1-eval (mv-nth 0 (resolve-term yes scope context next1))
                                 l1-env definitions constants program (1- fuel)))
         (no-result (l1-eval (mv-nth 0 (resolve-term no scope context next2))
                                l1-env definitions constants program (1- fuel))))
    (implies (and (posp fuel)
                  (equal test-result (boymoo-model::core-eval core-test core-env program (1- fuel)))
                  (equal yes-result (boymoo-model::core-eval core-yes core-env program (1- fuel)))
                  (equal no-result (boymoo-model::core-eval core-no core-env program (1- fuel))))
             (equal (l1-eval (mv-nth 0 (resolve-term (list *if-name* test yes no)
                                                         scope context next))
                                l1-env definitions constants program fuel)
                    (boymoo-model::core-eval (list 'if core-test core-yes core-no)
                                            core-env program fuel))))
  :hints (("Goal" :in-theory (enable p1-resolved-if)
           :expand ((:free (a b c) (l1-eval-step :term (list :if a b c)
                                                   l1-env definitions constants program fuel))
                    (boymoo-model::core-eval-step :term (list 'if core-test core-yes core-no)
                                                  core-env program fuel)))))

; A variable leaf carries its L0 spelling and Core symbol, and a quote
; leaf carries its L0 spelling and Core datum. An IF node has three
; children and uses the corresponding conditional syntax in each language.
(defund p1-conditional-tree-term (tree text)
  (declare (xargs :measure (acl2-count tree)))
  (case (car tree)
    (:var (if text (cadr tree) (caddr tree)))
    (:const (if text (list *quote-name* (cadr tree)) (list 'quote (caddr tree))))
    (:if (list (if text *if-name* 'if)
               (p1-conditional-tree-term (cadr tree) text)
               (p1-conditional-tree-term (caddr tree) text)
               (p1-conditional-tree-term (cadddr tree) text)))
    (otherwise nil)))

(defund p1-conditional-tree-agrees-p (tree scope context l1-env core-env constants)
  (declare (xargs :measure (acl2-count tree)))
  (case (car tree)
    (:var
     (let* ((text (cadr tree))
            (name (caddr tree))
            (number (table-tree-get text scope))
            (binding (assoc-equal number l1-env)))
       (and (stringp text) (symbolp name) number binding
            (equal (assoc-eq name core-env) (cons name (cdr binding))))))
    (:const
     (and (stringp (cadr tree))
          (equal (model-constant (resolve-datum-word (cadr tree) (caddr context)) constants)
                 (boymoo-model::core-value (caddr tree)))))
    (:if (and (p1-conditional-tree-agrees-p (cadr tree) scope context l1-env core-env constants)
              (p1-conditional-tree-agrees-p (caddr tree) scope context l1-env core-env constants)
              (p1-conditional-tree-agrees-p (cadddr tree) scope context l1-env core-env constants)))
    (otherwise nil)))

(defthmd p1-conditional-fragment-keeps-numbering
  (implies (p1-conditional-tree-agrees-p tree scope context l1-env core-env constants)
           (equal (mv-nth 1 (resolve-term (p1-conditional-tree-term tree t) scope context next))
                  next))
  :hints (("Goal" :induct (p1-conditional-tree-term tree t)
           :in-theory (enable p1-conditional-tree-term p1-conditional-tree-agrees-p
                              p1-resolved-variable p1-resolved-quote p1-resolved-if))))

(local
 (defun p1-conditional-evaluation-induction (tree fuel)
   (declare (xargs :measure (acl2-count tree)))
   (if (eq (car tree) :if)
       (list (p1-conditional-evaluation-induction (cadr tree) (1- fuel))
             (p1-conditional-evaluation-induction (caddr tree) (1- fuel))
             (p1-conditional-evaluation-induction (cadddr tree) (1- fuel)))
     fuel)))

(local
 (defthm p1-zero-fuel-outcomes
   (implies (zp fuel)
            (and (equal (l1-eval resolved l1-env definitions constants program fuel) :out-of-fuel)
                 (equal (boymoo-model::core-eval source core-env program fuel) :out-of-fuel)))
   :hints (("Goal" :in-theory (enable l1-eval-step boymoo-model::core-eval-step)))))

(defthmd p1-conditional-fragment-preserves-evaluation
  (implies (p1-conditional-tree-agrees-p tree scope context l1-env core-env constants)
           (equal (l1-eval (mv-nth 0 (resolve-term (p1-conditional-tree-term tree t)
                                                       scope context next))
                              l1-env definitions constants program fuel)
                  (boymoo-model::core-eval (p1-conditional-tree-term tree nil) core-env program fuel)))
  :hints (("Goal"
           :induct (p1-conditional-evaluation-induction tree fuel)
           :in-theory (e/d (p1-conditional-tree-term p1-conditional-tree-agrees-p
                            p1-conditional-fragment-keeps-numbering
                            p1-resolved-variable-agrees-with-core p1-resolved-quote-agrees-with-core
                            p1-resolved-if-agrees-with-core)
                           (l1-eval boymoo-model::core-eval)))
          ("Subgoal *1/2"
           :cases ((zp fuel))
           :use ((:instance p1-resolved-quote-agrees-with-core (text (cadr tree)) (datum (caddr tree)))
                 (:instance p1-resolved-variable-agrees-with-core (text (cadr tree)) (name (caddr tree)))))
          ("Subgoal *1/1"
           :cases ((zp fuel))
           :use ((:instance p1-conditional-fragment-keeps-numbering (tree (cadr tree)))
                 (:instance p1-conditional-fragment-keeps-numbering (tree (caddr tree)))
                 (:instance p1-resolved-if-agrees-with-core
                            (test (p1-conditional-tree-term (cadr tree) t))
                            (yes (p1-conditional-tree-term (caddr tree) t))
                            (no (p1-conditional-tree-term (cadddr tree) t))
                            (core-test (p1-conditional-tree-term (cadr tree) nil))
                            (core-yes (p1-conditional-tree-term (caddr tree) nil))
                            (core-no (p1-conditional-tree-term (cadddr tree) nil)))))))
