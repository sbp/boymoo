(in-package "BOYMOO")

(include-book "guards-admission-invariants")

(defthm cg-size-list-sum
  (implies (size-list-p xs) (integerp (sum xs)))
  :hints (("Goal" :induct (sum xs)))
  :rule-classes (:rewrite :type-prescription))

(verify-guards sum)

(defthm cg-size-integer
  (integerp (size x))
  :hints (("Goal" :use cg-size-is-natural))
  :rule-classes :type-prescription)

(defthm cg-sizes-form-size-list
  (size-list-p (sizes xs))
  :hints (("Goal" :induct (sizes xs) :in-theory (disable size))))

(defthm cg-size-list-app
  (implies (and (size-list-p x) (size-list-p y))
           (size-list-p (app x y))))

(defthm cg-size-list-tail
  (implies (size-list-p xs) (size-list-p (cdr xs)))
  :hints (("Goal" :expand ((size-list-p xs)))))

(defthm cg-size-list-is-proper
  (implies (size-list-p xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defthm cg-true-listp-app
  (implies (true-listp y)
           (true-listp (app x y))))

(defthm cg-size-list-rev-onto
  (implies (and (size-list-p x) (size-list-p acc))
           (size-list-p (rev-onto x acc))))

(defthm cg-true-listp-rev-onto
  (implies (true-listp acc)
           (true-listp (rev-onto x acc))))

(defthm cg-size-bindings-from-pair-up
  (implies (size-list-p vals)
           (size-bindings-p (pair-up keys vals))))

(local
 (defthm cg-binding-has-size
   (implies (and (size-bindings-p ss) (pair-of key ss))
            (or (integerp (cdr (pair-of key ss)))
                (equal (cdr (pair-of key ss)) nil)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (pair-of key ss)))))

(local
 (defun cg-size-induction (kind x)
   (declare (xargs :measure (acl2-count x)))
   (if (consp x)
       (if (equal kind :term)
           (if (equal (car x) '|COMMON-LISP::QUOTE|)
               nil
             (cg-size-induction :arguments (cdr x)))
         (cons (cg-size-induction :term (car x))
               (cg-size-induction :arguments (cdr x))))
     nil)))

(local
 (defthm cg-substitution-size-types
   (implies (size-bindings-p ss)
            (if (equal kind :term)
                (or (integerp (subst-size x ss)) (equal (subst-size x ss) nil))
              (integerp (args-subst-size x ss))))
   :hints (("Goal" :induct (cg-size-induction kind x)
            :in-theory (disable size pair-of)))
   :rule-classes nil))

(defthm cg-subst-size-type
  (implies (size-bindings-p ss)
           (or (integerp (subst-size x ss)) (equal (subst-size x ss) nil)))
  :hints (("Goal" :use ((:instance cg-substitution-size-types (kind :term)))))
  :rule-classes :type-prescription)

(defthm cg-args-subst-size-type
  (implies (size-bindings-p ss)
           (integerp (args-subst-size x ss)))
  :hints (("Goal" :use ((:instance cg-substitution-size-types (kind :arguments)))))
  :rule-classes :type-prescription)

(verify-guards subst-size
  :hints (("Goal" :in-theory (disable size pair-of))))
(verify-guards subst-sizes)

(defthm cg-subst-sizes-form-size-list
  (implies (size-bindings-p ss) (size-list-p (subst-sizes xs ss)))
  :hints (("Goal" :induct (subst-sizes xs ss)
           :in-theory (disable subst-size))))

(defthm cg-world-fields
  (implies (guard-world-p w)
           (and (true-listp w)
                (guard-trie-p (w-pkgs w) :package)
                (guard-trie-p (w-names w) :name)
                (guard-string-facts-p (w-sfacts w))
                (guard-natural-list-p (w-counts w))
                (true-listp (w-counts w))
                (guard-trie-p (w-acl2 w) :import)))
  :rule-classes :forward-chaining)

(defthm cg-name-entry-list
  (implies (guard-world-p w)
           (true-listp (name-entry s w)))
  :hints (("Goal" :expand ((guard-trie-value-p (name-entry s w) :name))
           :use ((:instance cg-trie-get-keeps-value
                            (key (sym-text s)) (node (w-names w)) (kind :name)))
           :in-theory (disable trie-get sym-text cg-trie-get-keeps-value)))
  :rule-classes (:rewrite :type-prescription))

(defthm cg-name-entry-cons-or-nil
  (implies (guard-world-p w)
           (or (consp (name-entry s w)) (equal (name-entry s w) nil)))
  :hints (("Goal" :use cg-name-entry-list :in-theory (disable name-entry)))
  :rule-classes :type-prescription)

(defthm cg-lookup-import-list
  (implies (guard-trie-p node :import)
           (true-listp (trie-get key node)))
  :hints (("Goal" :use ((:instance cg-trie-get-keeps-value (kind :import)))
           :expand ((guard-trie-value-p (trie-get key node) :import))
           :in-theory (disable trie-get cg-trie-get-keeps-value))))

(defthm cg-lookup-import-cons-or-nil
  (implies (guard-trie-p node :import)
           (or (consp (trie-get key node)) (equal (trie-get key node) nil)))
  :hints (("Goal" :use cg-import-of-lookup :in-theory (disable trie-get)))
  :rule-classes :type-prescription)

(defthm cg-import-in-package
  (implies (guard-trie-p pkgs :package)
           (let* ((rec (trie-get pkg pkgs))
                  (entry (trie-get name (prec-trie rec))))
             (and (true-listp rec)
                  (or (not entry) (and (consp entry) (symbolp (car entry)))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance cg-import-of-lookup (key name)
                                  (node (prec-trie (trie-get pkg pkgs)))))
           :in-theory (disable trie-get))))

(defthm cg-package-record-list
  (implies (guard-trie-p node :package)
           (true-listp (trie-get key node)))
  :hints (("Goal" :use cg-package-record-of-lookup :in-theory (disable trie-get)))
  :rule-classes :type-prescription)

(defthm cg-package-import-cons-or-nil
  (implies (guard-trie-p pkgs :package)
           (let ((entry (trie-get name (prec-trie (trie-get pkg pkgs)))))
             (or (consp entry) (equal entry nil))))
  :hints (("Goal" :use cg-import-in-package :in-theory (disable trie-get)))
  :rule-classes :type-prescription)

(defthm cg-package-import-symbol
  (implies (guard-trie-p pkgs :package)
           (symbolp (car (trie-get name (prec-trie (trie-get pkg pkgs))))))
  :hints (("Goal" :use cg-import-in-package :in-theory (disable trie-get))))

(local
 (defthm cg-make-character-list-type
   (character-listp (make-character-list x))
   :hints (("Goal" :in-theory (enable make-character-list)))))

(local
 (in-theory (disable guard-world-p trie-get name-entry size sym-parts sym-text)))

(verify-guards variable-list-p
  :hints (("Goal" :in-theory (disable variable-p))))

(verify-guards term-p
  :hints (("Goal" :in-theory (disable fn-arity variable-p variable-list-p pair-of))))

(defthm cg-terms-are-list
  (implies (terms-p xs vars extra w) (true-listp xs))
  :hints (("Goal" :induct (len xs) :in-theory (disable term-p))))

(local
 (defthm cg-lambda-application-fields
   (implies (and (term-p x :any nil w) (lambda-application-p x))
            (and (consp (cdr (car x)))
                 (consp (cddr (car x)))))
   :hints (("Goal" :expand ((term-p x :any nil w))
            :in-theory (disable variable-list-p variable-p fn-arity
                                terms-p distinct-p)))))

(verify-guards calls-p)
(verify-guards rename-calls
  :hints (("Goal" :in-theory (disable pair-of))))

(local
 (defthm cg-complete-native-less
   (equal (if (and (rationalp x) (rationalp y))
              (< x y)
            (let* ((a (fix x))
                   (b (fix y))
                   (re-a (realpart a))
                   (re-b (realpart b)))
              (or (< re-a re-b)
                  (and (equal re-a re-b) (< (imagpart a) (imagpart b))))))
          (< x y))
   :hints (("Goal" :use ((:instance acl2::completion-of-< (acl2::x x) (acl2::y y)))))))

(local
 (defthm cg-complete-native-complex
   (equal (complex (if (rationalp x) x 0) (if (rationalp y) y 0))
          (complex x y))
   :hints (("Goal" :use ((:instance acl2::completion-of-complex (acl2::x x) (acl2::y y)))))))

(local
 (defthm cg-complete-native-string
   (equal (coerce (make-character-list x) 'string) (coerce x 'string))
   :hints (("Goal" :use ((:instance acl2::completion-of-coerce
                                    (acl2::x x) (acl2::y 'string)))))))

(verify-guards prim-value
  :hints (("Goal"
           :use ((:instance acl2::completion-of-< (acl2::x (car args)) (acl2::y (cadr args))))
           :in-theory (disable sym-name intern-sym make-sym make-character-list))))

(defthm cg-prim-value-is-list
  (true-listp (prim-value f args w))
  :hints (("Goal" :in-theory (disable sym-name intern-sym make-sym make-character-list)))
  :rule-classes :type-prescription)

(defthm cg-naturals-form-size-list
  (implies (guard-natural-list-p xs) (size-list-p xs)))

(defthm cg-sized-clause-is-proof-clause
  (implies (guard-sized-clause-p c) (proof-clause-p c)))

(local
 (defthm cg-lookup-string-fact
   (implies (and (guard-string-facts-p al) (cdr (pair-of key al)))
            (guard-sized-clause-p (cdr (pair-of key al))))
   :hints (("Goal" :induct (pair-of key al) :in-theory (disable guard-sized-clause-p)))))

(local
 (defthm cg-name-fact-is-sized
   (implies (and (guard-world-p w) (entry-fact (name-entry name w)))
            (guard-sized-clause-p (entry-fact (name-entry name w))))
   :hints (("Goal"
            :use ((:instance cg-trie-get-keeps-value
                             (key (sym-text name)) (node (w-names w)) (kind :name)))
            :expand ((guard-trie-value-p (name-entry name w) :name))
            :in-theory (e/d (name-entry) (cg-trie-get-keeps-value guard-sized-clause-p))))))

(local
 (defthm cg-string-fact-cons-or-nil
   (implies (guard-string-facts-p al)
            (let ((fact (cdr (pair-of key al))))
              (or (consp fact) (equal fact nil))))
   :hints (("Goal" :use cg-lookup-string-fact
            :in-theory (disable pair-of cg-lookup-string-fact)))
   :rule-classes :type-prescription))

(local
 (defthm cg-name-fact-cons-or-nil
   (implies (guard-world-p w)
            (let ((fact (entry-fact (name-entry name w))))
              (or (consp fact) (equal fact nil))))
   :hints (("Goal" :use cg-name-fact-is-sized
            :in-theory (disable cg-name-fact-is-sized)))
   :rule-classes :type-prescription))

(local
 (defthm cg-string-fact-size-list
   (implies (guard-string-facts-p al)
            (size-list-p (cdr (cdr (pair-of key al)))))
   :hints (("Goal" :use cg-lookup-string-fact
            :in-theory (disable pair-of cg-lookup-string-fact)))))

(local
 (defthm cg-name-fact-size-list
   (implies (guard-world-p w)
            (size-list-p (cdr (entry-fact (name-entry name w)))))
   :hints (("Goal" :use cg-name-fact-is-sized
            :in-theory (disable cg-name-fact-is-sized)))))

(local
 (defthm cg-nth-proof-clause
   (implies (and (proof-clauses-p steps) (nth-elem n steps))
            (proof-clause-p (nth-elem n steps)))
   :hints (("Goal" :induct (nth-elem n steps)))))

(defthm cg-premise-is-proof-clause
  (implies (and (proof-clauses-p steps) (premise p steps count))
           (proof-clause-p (premise p steps count)))
  :hints (("Goal" :in-theory (disable nth-elem))))

(defthm cg-premise-cons-or-nil
  (implies (proof-clauses-p steps)
           (or (consp (premise p steps count)) (equal (premise p steps count) nil)))
  :hints (("Goal" :use cg-premise-is-proof-clause
           :in-theory (disable premise cg-premise-is-proof-clause)))
  :rule-classes :type-prescription)

(defthm cg-premise-fields
  (implies (proof-clauses-p steps)
           (and (true-listp (car (premise p steps count)))
                (size-list-p (cdr (premise p steps count)))))
  :hints (("Goal" :use cg-premise-is-proof-clause
           :in-theory (disable premise cg-premise-is-proof-clause))))

(local
 (defthm cg-premise-sizes-are-list
   (implies (proof-clauses-p steps)
            (true-listp (cdr (premise p steps count))))
   :hints (("Goal" :use cg-premise-fields :in-theory (disable premise cg-premise-fields)))
   :rule-classes :type-prescription))

(local
 (defthm cg-premise-literals-tail-is-list
   (implies (proof-clauses-p steps)
            (true-listp (cdr (car (premise p steps count)))))
   :hints (("Goal" :use cg-premise-fields :in-theory (disable premise cg-premise-fields)))))

(local
 (defthm cg-substitution-is-cons-list
   (implies (not (equal (read-subst s w) :bad))
            (cons-list-p (read-subst s w)))
   :hints (("Goal" :induct (read-subst s w)
            :in-theory (disable variable-p term-p pair-of)))))

(local
 (defthm cg-substitutions-are-cons-lists
   (implies (not (equal (read-substs ss w) :bad))
            (substitutions-p (read-substs ss w)))
   :hints (("Goal" :induct (read-substs ss w) :in-theory (disable read-subst)))))

(verify-guards fits)
(verify-guards read-subst
  :hints (("Goal" :in-theory (disable term-p variable-p))))
(verify-guards read-substs)
(verify-guards subst-size-alist)
(verify-guards unquote-all)

(local
 (defthm cg-unquote-all-is-list
   (true-listp (unquote-all xs))
   :rule-classes :type-prescription))

(local
 (defthm cg-subst-size-alist-has-sizes
   (size-bindings-p (subst-size-alist s))
   :hints (("Goal" :induct (subst-size-alist s)))))

(local
 (defthm cg-subst-size-of-sized-substitution
   (or (integerp (subst-size x (subst-size-alist s)))
       (equal (subst-size x (subst-size-alist s)) nil))
   :hints (("Goal" :use ((:instance cg-subst-size-type (ss (subst-size-alist s))))
            :in-theory (disable subst-size subst-size-alist)))
   :rule-classes :type-prescription))

(local
 (defthm cg-induct-literal-size-integer
   (integerp (+ 20 (subst-size m (subst-size-alist s))
                (size m) (subst-size phi (subst-size-alist s))))
   :hints (("Goal" :cases ((integerp (subst-size m (subst-size-alist s)))
                          (integerp (subst-size phi (subst-size-alist s))))
            :in-theory (disable size subst-size subst-size-alist)))
   :rule-classes :type-prescription))

(local
 (defthm cg-subst-terms-is-list
   (true-listp (subst-terms xs s))
   :hints (("Goal" :induct (len xs) :in-theory (disable subst-term)))
   :rule-classes :type-prescription))

(local
 (defthm cg-replace-nth-keeps-size-list
   (implies (and (size-list-p xs) (size-value-p v))
            (size-list-p (replace-nth i xs v)))))

(local
 (defthm cg-nth-size-value
   (implies (size-list-p xs)
            (or (integerp (nth-elem n xs)) (equal (nth-elem n xs) nil)))
   :rule-classes :type-prescription))

(local
 (defthm cg-nth-premise-size-value
   (implies (proof-clauses-p steps)
            (or (integerp (nth-elem i (cdr (premise p steps count))))
                (equal (nth-elem i (cdr (premise p steps count))) nil)))
   :hints (("Goal" :use ((:instance cg-nth-size-value
                                   (n i) (xs (cdr (premise p steps count)))))
            :in-theory (disable premise nth-elem)))
   :rule-classes :type-prescription))

(local
 (defthm cg-adjusted-premise-size
   (implies (and (proof-clauses-p steps) (integerp a) (integerp b))
            (integerp (+ (- a) b (nth-elem i (cdr (premise p steps count))))))
   :hints (("Goal" :cases ((integerp (nth-elem i (cdr (premise p steps count)))))
            :in-theory (disable premise nth-elem)))
   :rule-classes :type-prescription))

(local
 (defthm cg-beta-subst-size-value
   (or (integerp (subst-size body (pair-up keys (sizes args))))
       (equal (subst-size body (pair-up keys (sizes args))) nil))
   :hints (("Goal" :use ((:instance cg-subst-size-type
                                   (x body) (ss (pair-up keys (sizes args)))))
            :in-theory (disable subst-size sizes pair-up)))
   :rule-classes :type-prescription))

(local
 (defthm cg-beta-size-integer
   (integerp (+ 5 (size x) (subst-size body (pair-up keys (sizes args)))))
   :hints (("Goal" :cases ((integerp (subst-size body (pair-up keys (sizes args)))))
            :in-theory (disable size subst-size sizes pair-up)))
   :rule-classes :type-prescription))

(verify-guards induct-sizes
  :hints (("Goal" :in-theory (disable subst-size subst-size-alist))))

(local
 (defthm cg-induct-sizes-form-size-list
   (size-list-p (induct-sizes phi m ss))
   :hints (("Goal" :induct (induct-sizes phi m ss)
            :in-theory (disable subst-size subst-size-alist)))))

(local
 (in-theory (disable subst-size subst-size-alist subst-sizes sizes read-subst
                     read-substs premise nth-elem replace-nth fits app term-p terms-p
                     prim-value unquote-all induct-sizes sum)))

(verify-guards step-fact
  :hints (("Goal" :in-theory (disable pair-of))))
(verify-guards step-instantiate)
(verify-guards step-subsume)
(verify-guards step-cut)
(verify-guards step-substitute
  :hints (("Goal" :in-theory (disable replace-at))))
(verify-guards step-beta
  :hints (("Goal" :in-theory (disable pair-up))))
(verify-guards step-compute)
(verify-guards step-induct
  :hints (("Goal" :in-theory (disable induct-lits))))
(verify-guards check-step)

(local
 (defthm cg-replace-nth-list
   (implies (true-listp xs)
            (true-listp (replace-nth i xs v)))
   :hints (("Goal" :in-theory (enable replace-nth)))))

(local
 (defthm cg-fact-step-clause
   (implies (and (guard-world-p w) (step-fact data room w))
            (proof-clause-p (step-fact data room w)))))

(local
 (defthm cg-instantiate-step-clause
   (implies (and (step-instantiate data steps count room w)
                 (proof-clauses-p steps))
            (proof-clause-p (step-instantiate data steps count room w)))))

(local
 (defthm cg-subsume-step-clause
   (implies (step-subsume data steps count room w)
            (proof-clause-p (step-subsume data steps count room w)))))

(local
 (defthm cg-cut-step-clause
   (implies (and (step-cut data steps count room)
                 (proof-clauses-p steps))
            (proof-clause-p (step-cut data steps count room)))))

(local
 (defthm cg-substitute-step-clause
   (implies (and (step-substitute data steps count room)
                 (proof-clauses-p steps))
            (proof-clause-p (step-substitute data steps count room)))
   :hints (("Goal" :in-theory (disable replace-at)))))

(local
 (defthm cg-beta-step-clause
   (implies (step-beta data room w)
            (proof-clause-p (step-beta data room w)))
   :hints (("Goal" :in-theory (disable pair-up subst-term)))))

(local
 (defthm cg-compute-step-clause
   (implies (step-compute data room w)
            (proof-clause-p (step-compute data room w)))))

(local
 (defthm cg-induct-step-clause
   (implies (step-induct data steps count room w)
            (proof-clause-p (step-induct data steps count room w)))
   :hints (("Goal" :in-theory (disable induct-lits)))))

(defthm cg-check-step-clause
  (implies (and (proof-clauses-p steps)
                (guard-world-p w)
                (check-step word data steps count room w))
           (proof-clause-p (check-step word data steps count room w)))
  :hints (("Goal" :in-theory (disable step-fact step-instantiate step-subsume
                                     step-cut step-substitute step-beta step-compute
                                     step-induct))))

(defthm cg-check-step-fields
  (implies (and (proof-clauses-p steps) (guard-world-p w))
           (let ((c (check-step word data steps count room w)))
             (and (true-listp (car c)) (size-list-p (cdr c)))))
  :hints (("Goal" :use cg-check-step-clause
           :in-theory (disable check-step cg-check-step-clause))))

(defthm cg-check-step-cons-or-nil
  (implies (and (proof-clauses-p steps) (guard-world-p w))
           (or (consp (check-step word data steps count room w))
               (equal (check-step word data steps count room w) nil)))
  :hints (("Goal" :use cg-check-step-clause
           :in-theory (disable check-step cg-check-step-clause)))
  :rule-classes :type-prescription)
