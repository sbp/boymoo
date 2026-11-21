(in-package "BOYMOO")

(include-book "guards-steps")

(defthm cg-measure-table-shape
  (defs-shape-p (measure-table defs measures)))

(local
 (defthm cg-formals-and-measure-pair
   (implies (defs-shape-p defs)
            (true-listp (pair-of f defs)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :induct (pair-of f defs)))))

(local
 (defthm cg-call-measure-size-type
   (implies (size-bindings-p ss)
            (or (integerp (subst-size m (pair-up vars (subst-sizes xs ss))))
                (equal (subst-size m (pair-up vars (subst-sizes xs ss))) nil)))
   :hints (("Goal" :use ((:instance cg-subst-size-type
                                   (x m) (ss (pair-up vars (subst-sizes xs ss)))))
            :in-theory (disable subst-size subst-sizes pair-up)))
   :rule-classes :type-prescription))

(local
 (defthm cg-call-literal-size-type
   (implies (and (size-bindings-p ss) (integerp n))
            (integerp (+ 5 n (subst-size m (pair-up vars (subst-sizes xs ss))))))
   :hints (("Goal" :cases ((integerp (subst-size m (pair-up vars (subst-sizes xs ss)))))
            :in-theory (disable subst-size subst-sizes pair-up)))
   :rule-classes :type-prescription))

(verify-guards call-clause
  :hints (("Goal" :in-theory (disable rev-onto size subst-term subst-terms
                                     subst-size subst-sizes pair-of pair-up))))

(local
 (defthm cg-call-clause-has-sizes
   (implies (and (true-listp rl) (size-list-p rs) (size-bindings-p ss)
                 (call-context-p ctx))
            (proof-clause-p (call-clause x rl rs st ss ctx)))
   :hints (("Goal" :in-theory (disable rev-onto size subst-term subst-terms
                                      subst-size subst-sizes pair-of pair-up)))))

(verify-guards record-call-if
  :hints (("Goal" :in-theory (disable call-clause pair-of))))

(local
 (defthm cg-record-call-keeps-clauses
   (implies (and (true-listp rl) (size-list-p rs) (size-bindings-p ss)
                 (call-context-p ctx) (proof-clauses-p acc))
            (proof-clauses-p (record-call-if x rl rs st ss ctx acc)))
   :hints (("Goal" :in-theory (disable call-clause pair-of)))))

; Follow each recursive call with its own accumulator and bindings.
(local
 (defun cg-walk-induction (kind x rl rs st ss ctx acc)
   (declare (irrelevant rl rs st ss acc)
            (xargs :measure (+ (* 2 (acl2-count x))
                               (if (or (equal kind :walk) (equal kind :walk-list)) 1 0))))
   (if (consp x)
       (case kind
         (:walk
          (let ((ext (cadr ctx)))
            (cond
             ((equal (car x) '|COMMON-LISP::QUOTE|) nil)
             ((consp (car x))
              (let* ((formals (cadar x))
                     (args (cdr x))
                     (extend (lambdas-extend-p ext))
                     (after-args (if extend (walk-list args rl rs st ss ctx acc)
                                   (record-list args rl rs st ss ctx acc))))
                (list (cg-walk-induction (if extend :walk-list :record-list)
                                        args rl rs st ss ctx acc)
                      (cg-walk-induction :walk (caddar x) rl rs
                        (pair-up formals (subst-terms args st))
                        (pair-up formals (subst-sizes args ss))
                        ctx after-args))))
             ((equal (car x) '|COMMON-LISP::IF|)
              (let* ((test (cadr x))
                     (test2 (subst-term test st))
                     (n (subst-size test ss))
                     (neg-rl (cons (list '|COMMON-LISP::NOT| test2) rl))
                     (neg-rs (cons (+ 4 n) rs))
                     (extend (extends-p '|COMMON-LISP::IF| ext))
                     (after-test (if extend (walk test rl rs st ss ctx acc)
                                   (record test rl rs st ss ctx acc))))
                (list (if extend
                          (cg-walk-induction :walk test rl rs st ss ctx acc)
                        (cg-walk-induction :record test rl rs st ss ctx acc))
                      (cg-walk-induction :walk (caddr x) neg-rl neg-rs st ss ctx after-test)
                      (cg-walk-induction :walk (cadddr x) (cons test2 rl) (cons n rs) st ss ctx
                        (walk (caddr x) neg-rl neg-rs st ss ctx after-test)))))
             ((mbe-p x) (cg-walk-induction :walk (cadddr x) rl rs st ss ctx acc))
             ((extends-p (car x) ext)
              (cg-walk-induction :walk-list (cdr x) rl rs st ss ctx
                (record-call-if x rl rs st ss ctx acc)))
             (t (cg-walk-induction :record x rl rs st ss ctx acc)))))
         (:walk-list
          (list (cg-walk-induction :walk (car x) rl rs st ss ctx acc)
                (cg-walk-induction :walk-list (cdr x) rl rs st ss ctx
                  (walk (car x) rl rs st ss ctx acc))))
         (:record
          (cond ((equal (car x) '|COMMON-LISP::QUOTE|) nil)
                ((consp (car x))
                 (list (cg-walk-induction :record-list (cdr x) rl rs st ss ctx acc)
                       (cg-walk-induction :record (caddar x) rl rs
                         (pair-up (cadar x) (subst-terms (cdr x) st))
                         (pair-up (cadar x) (subst-sizes (cdr x) ss))
                         ctx (record-list (cdr x) rl rs st ss ctx acc))))
                ((mbe-p x) (cg-walk-induction :record (cadddr x) rl rs st ss ctx acc))
                (t (cg-walk-induction :record-list (cdr x) rl rs st ss ctx
                     (record-call-if x rl rs st ss ctx acc)))))
         (otherwise
          (list (cg-walk-induction :record (car x) rl rs st ss ctx acc)
                (cg-walk-induction :record-list (cdr x) rl rs st ss ctx
                  (record (car x) rl rs st ss ctx acc)))))
     nil)))

(local
 (defthm cg-walk-results-are-clauses
   (implies (and (true-listp rl) (size-list-p rs) (size-bindings-p ss)
                 (call-context-p ctx) (proof-clauses-p acc))
            (proof-clauses-p
             (case kind
               (:walk (walk x rl rs st ss ctx acc))
               (:walk-list (walk-list x rl rs st ss ctx acc))
               (:record (record x rl rs st ss ctx acc))
               (otherwise (record-list x rl rs st ss ctx acc)))))
   :hints (("Goal" :induct (cg-walk-induction kind x rl rs st ss ctx acc)
            :in-theory (disable call-context-p record-call-if subst-term subst-size
                                subst-sizes subst-terms pair-up mbe-p extends-p lambdas-extend-p)))
   :rule-classes nil))

(local
 (defthm cg-walk-keeps-clauses
   (implies (and (true-listp rl) (size-list-p rs) (size-bindings-p ss)
                 (call-context-p ctx) (proof-clauses-p acc))
            (proof-clauses-p (walk x rl rs st ss ctx acc)))
   :hints (("Goal" :use ((:instance cg-walk-results-are-clauses (kind :walk)))
            :in-theory (disable walk)))))

(local
 (defthm cg-walk-list-keeps-clauses
   (implies (and (true-listp rl) (size-list-p rs) (size-bindings-p ss)
                 (call-context-p ctx) (proof-clauses-p acc))
            (proof-clauses-p (walk-list x rl rs st ss ctx acc)))
   :hints (("Goal" :use ((:instance cg-walk-results-are-clauses (kind :walk-list)))
            :in-theory (disable walk-list)))))

(local
 (defthm cg-record-keeps-clauses
   (implies (and (true-listp rl) (size-list-p rs) (size-bindings-p ss)
                 (call-context-p ctx) (proof-clauses-p acc))
            (proof-clauses-p (record x rl rs st ss ctx acc)))
   :hints (("Goal" :use ((:instance cg-walk-results-are-clauses (kind :record)))
            :in-theory (disable record)))))

(local
 (defthm cg-record-list-keeps-clauses
   (implies (and (true-listp rl) (size-list-p rs) (size-bindings-p ss)
                 (call-context-p ctx) (proof-clauses-p acc))
            (proof-clauses-p (record-list x rl rs st ss ctx acc)))
   :hints (("Goal" :use ((:instance cg-walk-results-are-clauses (kind :record-list)))
            :in-theory (disable record-list)))))

(verify-guards walk
  :hints (("Goal" :in-theory (disable record-call-if
                                     subst-term subst-size subst-sizes subst-terms
                                     pair-up extends-p lambdas-extend-p))))

(local (in-theory (disable walk record walk-list record-list size)))

(verify-guards call-clauses)

(local
 (defthm cg-call-clauses-are-clauses
   (implies (and (defs-shape-p fns) (proof-clauses-p acc))
            (proof-clauses-p (call-clauses defs measures fns ext acc)))
   :hints (("Goal" :induct (call-clauses defs measures fns ext acc)))))

(local
 (defthm cg-o-p-clauses-are-clauses
   (implies (proof-clauses-p acc)
            (proof-clauses-p (o-p-clauses measures acc)))
   :hints (("Goal" :induct (o-p-clauses measures acc)))))

(local
 (defthm cg-rev-onto-keeps-clauses
   (implies (and (proof-clauses-p xs) (proof-clauses-p acc))
            (proof-clauses-p (rev-onto xs acc)))))

(verify-guards kept-p)
(verify-guards kept-lits)
(verify-guards keep-clauses
  :hints (("Goal" :in-theory (disable sum kept-p))))

(local
 (defthm cg-keep-clauses-keeps-shape
   (implies (and (proof-clauses-p cands)
                 (kept-clauses-p kept)
                 (not (equal (keep-clauses cands kept total) :over)))
            (kept-clauses-p (keep-clauses cands kept total)))
   :hints (("Goal" :induct (keep-clauses cands kept total)
            :in-theory (disable sum kept-p)))))

(local
 (defthm cg-kept-lits-is-list
   (implies (true-listp acc)
            (true-listp (kept-lits kept acc)))))

(verify-guards termination-obligations
  :hints (("Goal" :in-theory (disable measure-table call-clauses o-p-clauses
                                     keep-clauses kept-lits))))

(defthm cg-termination-obligations-list
  (implies (not (equal (termination-obligations defs measures ext) :over))
           (true-listp (termination-obligations defs measures ext)))
  :hints (("Goal" :in-theory (disable measure-table call-clauses o-p-clauses
                                     keep-clauses kept-lits))))

(verify-guards measures-p
  :hints (("Goal" :in-theory (disable term-p))))
(verify-guards witnesses-p
  :hints (("Goal" :in-theory (disable name-entry))))
(verify-guards witness-obligations
  :hints (("Goal" :in-theory (disable rename-calls))))

(defthm cg-witness-obligations-are-list
  (true-listp (witness-obligations terms ren))
  :hints (("Goal" :induct (len terms) :in-theory (disable rename-calls))))
