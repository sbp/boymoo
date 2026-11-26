(in-package "BOYMOO-PROOFS")

(include-book "generator-emission")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-routine-destinations (entries)
  (if (atom entries)
      nil
    (cons (cddar entries) (assembly-routine-destinations (cdr entries)))))

(defun assembly-allowed-generated-reference-p (key context)
  (or (equal key "rt:undefined")
      (member-equal key (assembly-routine-destinations boymoo-compiler::*jets*))
      (member-equal key (assembly-routine-destinations boymoo-compiler::*primitives*))
      (and (equal key (list :fn (cadr key)))
           (boymoo-compiler::index-get (cadr key) (car context)))))

(local
 (defthm assembly-reference-membership-of-append
   (iff (member-equal key (append first rest))
        (or (member-equal key first) (member-equal key rest)))))

(local
 (defthm assembly-destination-from-routine-entries
   (implies (assoc-equal name entries)
            (member-equal (cddr (assoc-equal name entries))
                          (assembly-routine-destinations entries)))))

(local
 (defun assembly-routine-destinations-present-p (entries)
   (if (atom entries)
       t
     (and (cddar entries) (assembly-routine-destinations-present-p (cdr entries))))))

(local
 (defthm assembly-routine-lookup-has-destination
   (implies (and (assembly-routine-destinations-present-p entries)
                 (assoc-equal name entries))
            (cddr (assoc-equal name entries)))))

(local
 (defthm assembly-allowed-call-destinations
   (mv-let (target arity routine)
     (boymoo-compiler::gen-call-info head context)
     (and (implies routine (assembly-allowed-generated-reference-p routine context))
          (implies (and (not routine) arity)
                   (assembly-allowed-generated-reference-p (list :fn target) context))))
   :hints (("Goal" :in-theory (disable assoc-equal member-equal boymoo-compiler::index-get
                                       assembly-routine-destinations-present-p
                                       assembly-routine-destinations
                                       (:executable-counterpart assembly-routine-destinations))))
   :rule-classes nil))

(defthm assembly-gen-call-info-index-for-non-routine
  (mv-let (target arity routine)
    (boymoo-compiler::gen-call-info head context)
    (implies (not routine)
             (equal arity (boymoo-compiler::index-get target (car context)))))
  :hints (("Goal"
           :in-theory (disable assoc-equal boymoo-compiler::index-get
                               assembly-routine-destinations-present-p)))
  :rule-classes nil)

(local
 (defthm assembly-generated-reference-can-be-undefined
   (assembly-allowed-generated-reference-p "rt:undefined" context)))

(local
 (defthm assembly-generated-reference-can-be-primitive-equal
   (assembly-allowed-generated-reference-p "prim:COMMON-LISP::EQUAL" context)))

(local
 (defthm assembly-routine-reference-is-local-or-external
   (implies (member-equal key (assembly-routine-references name label serial))
            (or (equal key label)
                (equal key "prim:COMMON-LISP::EQUAL")
                (member-equal key (assembly-routine-labels name serial))))
   :rule-classes nil))

(local
 (defthm assembly-generator-result-component-of-cons
   (equal (mv-nth n (cons first rest))
          (if (zp n) first (mv-nth (1- n) rest)))))

(local (in-theory (disable mv-nth length
                           boymoo-compiler::gen-term boymoo-compiler::gen-args
                           boymoo-compiler::gen-lambda-args boymoo-compiler::gen-simple
                           boymoo-compiler::gen-simple-p boymoo-compiler::gen-simple-args
                           boymoo-compiler::gen-simple-args-p boymoo-compiler::gen-frame-word
                           boymoo-compiler::gen-mbe-p boymoo-compiler::gen-slot
                           boymoo-compiler::gen-datum boymoo-compiler::gen-argument-registers
                           boymoo-compiler::gen-copy-arguments boymoo-compiler::gen-defined-call
                           boymoo-compiler::gen-address boymoo-compiler::gen-load-high
                           boymoo-compiler::gen-load-word boymoo-compiler::gen-load-datum
                           boymoo-compiler::gen-car-cdr boymoo-compiler::gen-equal
                           boymoo-compiler::gen-arithmetic boymoo-compiler::gen-boolean
                           boymoo-compiler::gen-routine boymoo-compiler::gen-call-info
                           boymoo-compiler::gen-prologue boymoo-compiler::gen-push
                           boymoo-compiler::gen-drop boymoo-compiler::gen-finish
                           boymoo-compiler::bind-formal boymoo-compiler::declaration-list
                           boymoo-compiler::reverse-onto
                           assembly-simple-form-p assembly-simple-forms-p
                           assembly-allowed-generated-reference-p)))

(local
 (defthm assembly-allowed-routine-reference
   (implies (and (assembly-allowed-generated-reference-p label context)
                 (not (assembly-allowed-generated-reference-p key context))
                 (member-equal key (assembly-routine-references name label serial)))
            (member-equal key (assembly-routine-labels name serial)))
   :hints (("Goal" :use (assembly-routine-reference-is-local-or-external)
                   :in-theory (disable assembly-routine-labels assembly-routine-references)))))

(local (in-theory (disable assembly-routine-labels assembly-routine-references)))

(local
 (defthm assembly-generator-reference-origin
   (let* ((result (assembly-generator-result kind term formals scope body-scope depth
                                             tail context code high serial))
          (out (mv-nth 0 result)))
     (implies (and (not (assembly-allowed-generated-reference-p key context))
                   (member-equal key (assembly-references out))
                   (not (member-equal key (assembly-label-names out))))
              (and (member-equal key (assembly-references code))
                   (not (member-equal key (assembly-label-names code))))))
   :hints (("Goal"
            :induct (assembly-generator-induction kind term formals scope body-scope depth
                                                  tail context code high serial)
            :expand ((:free (scope depth tail context code high serial)
                            (boymoo-compiler::gen-term term scope depth tail context code high serial))
                     (:free (scope depth context code high serial)
                            (boymoo-compiler::gen-args term scope depth context code high serial))
                     (:free (formals scope body-scope depth context code high serial)
                            (boymoo-compiler::gen-lambda-args term formals scope body-scope depth
                                                             context code high serial))))
           ("Subgoal *1/8" :use ((:instance assembly-allowed-call-destinations (head (car term)))))
           ("Subgoal *1/7" :use ((:instance assembly-allowed-call-destinations (head (car term))))))
   :rule-classes nil))

(defthm assembly-gen-term-reference-origin
  (let ((out (mv-nth 0 (boymoo-compiler::gen-term term scope depth tail context code high serial))))
    (implies (and (not (assembly-allowed-generated-reference-p key context))
                  (member-equal key (assembly-references out))
                  (not (member-equal key (assembly-label-names out))))
             (and (member-equal key (assembly-references code))
                  (not (member-equal key (assembly-label-names code))))))
  :hints (("Goal" :use ((:instance assembly-generator-reference-origin
                                   (kind :term) (formals nil) (body-scope nil)))))
  :rule-classes nil)
