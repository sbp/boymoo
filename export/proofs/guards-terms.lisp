(in-package "ACL2")

(include-book "guards-data")
(local (include-book "system/pseudo-termp-lemmas" :dir :system))
(local (include-book "system/remove-guard-holders1" :dir :system))
(local (include-book "tools/flag" :dir :system))

(local (in-theory (disable plist-worldp bx-world-properties-p)))

; Term walkers use the argument lists and lambda fields of pseudo-terms.

(defthm bx-pseudo-term-listp-of-symbol-list
  (implies (symbol-listp x) (pseudo-term-listp x)))

(defthm bx-pseudo-termp-of-named-call
  (implies (and (symbolp fn) (not (eq fn 'quote)) (pseudo-term-listp args))
           (pseudo-termp (cons fn args))))

(defthm bx-pseudo-term-listp-of-append
  (implies (and (pseudo-term-listp xs) (pseudo-term-listp ys))
           (pseudo-term-listp (append xs ys))))

(defthm bx-symbol-listp-of-all-fnnames1
  (implies (and (if flag (pseudo-term-listp x) (pseudo-termp x))
                (symbol-listp acc))
           (symbol-listp (all-fnnames1 flag x acc)))
  :hints (("Goal" :induct (all-fnnames1 flag x acc))))

(defthm bx-true-listp-of-symbol-list
  (implies (symbol-listp x) (true-listp x))
  :rule-classes (:rewrite :forward-chaining))

(defthm bx-listp-of-assoc-equal
  (implies (alistp xs)
           (or (consp (assoc-equal key xs))
               (equal (assoc-equal key xs) nil)))
  :rule-classes :type-prescription)

(defthm bx-listp-of-hons-get
  (or (consp (hons-get key xs))
      (equal (hons-get key xs) nil))
  :rule-classes :type-prescription)

(local (in-theory (disable fgetprop formals hons-get all-fnnames1)))

(local
 (defthm bx-alistp-of-pairlis$
   (alistp (pairlis$ keys vals))))

(local
 (defthm bx-true-listp-of-beta-in-lst
   (true-listp (bx-beta-in-lst x alist))))

(verify-guards bx-beta-in)
(verify-guards bx-beta)
(verify-guards bx-exec)
(verify-guards bx-bad-calls)
(verify-guards bx-mentions-some)

; Replacing an mbe call by its executable argument leaves a pseudo-term.
; The list walker preserves the number of actuals in a lambda call.

(local (make-flag bx-exec-flag bx-exec))

(local
 (defthm bx-len-of-exec-lst
   (equal (len (bx-exec-lst terms)) (len terms))
   :hints (("Goal" :induct (len terms) :in-theory (disable bx-exec)))))

(defthm-bx-exec-flag
  (defthm bx-pseudo-termp-of-exec
    (implies (pseudo-termp term) (pseudo-termp (bx-exec term)))
    :flag bx-exec)
  (defthm bx-pseudo-term-listp-of-exec-lst
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (bx-exec-lst terms)))
    :flag bx-exec-lst))

; Removing guard holders and flattening an 'and' are safe on the formulas
; used as constraint candidates.

(verify-guards bx-remove-guard-holders)

(local
 (defthm bx-pseudo-termp-of-remove-guard-holders
   (implies (pseudo-termp term)
            (pseudo-termp (bx-remove-guard-holders term)))))

(local
 (defthm bx-listp-of-flatten-ands-in-lit
   (true-listp (flatten-ands-in-lit term))
   :rule-classes :type-prescription))

(verify-guards bx-conjuncts
  :hints (("Goal" :in-theory (disable bx-remove-guard-holders
                                     flatten-ands-in-lit pseudo-termp))))

(defthm bx-listp-of-conjuncts
  (implies (not (equal (bx-conjuncts term terms) :none))
           (true-listp (bx-conjuncts term terms)))
  :hints (("Goal" :in-theory (disable flatten-ands-in-lit))))

; Choice construction substitutes one pseudo-term per bound or free
; variable. The mv-nth terms number exactly as many as the bound variables.

(verify-guards bx-mv-nths)

(local
 (defthm bx-pseudo-term-listp-of-mv-nths
   (implies (pseudo-termp call)
            (pseudo-term-listp (bx-mv-nths k i call)))))

(local
 (defthm bx-len-of-mv-nths
   (implies (and (natp k) (natp i))
            (equal (len (bx-mv-nths k i call)) (nfix (- k i))))))

(local (in-theory (disable bx-mv-nths subcor-var)))

(verify-guards bx-choose-literal)
(verify-guards bx-choose-axiom)

(local
 (defthm bx-pseudo-termp-of-choose-literal
   (implies (and (symbolp fn) (not (eq fn 'quote))
                 (consp bound) (symbol-listp bound)
                 (pseudo-term-listp free) (pseudo-termp body)
                 (or (not strong)
                     (and (symbol-listp free)
                          (pseudo-term-listp free2)
                          (equal (len free) (len free2)))))
            (pseudo-termp (bx-choose-literal fn bound free body free2 strong)))))

; The choice parser reads pseudo-term subexpressions and the formals and
; actuals of lambda applications.

(verify-guards bx-bound-one)
(verify-guards bx-bound-index)
(verify-guards bx-bound-many)
(verify-guards bx-choice-input-p)

(local
 (defthm bx-symbol-listp-of-bound-one
   (implies (symbol-listp formals)
            (symbol-listp (bx-bound-one formals actuals call)))))

(local
 (defthm bx-symbolp-of-bound-index
   (implies (symbol-listp formals)
            (symbolp (bx-bound-index formals actuals mv i)))))

(local
 (defthm bx-symbol-listp-of-bound-many
   (implies (symbol-listp formals)
            (symbol-listp (bx-bound-many formals actuals mv i fuel)))))

(local (in-theory (disable bx-bound-one bx-bound-index bx-bound-many)))

(defthm bx-pseudo-term-list-components
  (implies (pseudo-term-listp terms)
           (and (pseudo-termp (car terms))
                (pseudo-term-listp (cdr terms))))
  :hints (("Goal" :expand ((pseudo-term-listp terms)))))

(local
 (defthm bx-pseudo-termp-of-first-arg
   (implies (and (pseudo-termp term)
                 (not (eq (car term) 'quote)))
            (pseudo-termp (cadr term)))
   :hints (("Goal" :cases ((consp term)) :in-theory (disable pseudo-termp)))))

(local
 (defthm bx-pseudo-termp-of-second-arg
   (implies (and (pseudo-termp term)
                 (not (eq (car term) 'quote)))
            (pseudo-termp (caddr term)))
   :hints (("Goal" :cases ((consp term)) :in-theory (disable pseudo-termp)))))

(local
 (defthm bx-pseudo-term-lambda-components
   (implies (and (pseudo-termp term) (consp (car term)))
            (and (symbol-listp (cadar term))
                 (pseudo-termp (caddar term))
                 (equal (len (cadar term)) (len (cdr term)))))
   :hints (("Goal" :use ((:instance pseudo-termp-lambda-lemma (x term)))
            :in-theory (disable pseudo-termp pseudo-termp-lambda-lemma)))))

(local
 (in-theory (disable pseudo-termp pseudo-term-listp len true-listp plist-worldp)))

(verify-guards bx-choose-parts
  :hints (("Goal" :do-not-induct t)))

(local
 (defthm bx-choice-parts-types
   (implies (and (pseudo-termp axiom) (not (eq fn 'quote)))
            (and (symbol-listp (car (bx-choose-parts axiom fn wrld)))
                 (pseudo-termp (mv-nth 1 (bx-choose-parts axiom fn wrld)))
                 (pseudo-term-listp (mv-nth 2 (bx-choose-parts axiom fn wrld)))))))

(local
 (defthm bx-choice-parts-free2-length
   (implies (and (bx-choice-input-p fn wrld)
                 (mv-nth 2 (bx-choose-parts (getpropc fn 'defchoose-axiom nil wrld)
                                            fn wrld)))
            (equal (len (mv-nth 2 (bx-choose-parts
                                   (getpropc fn 'defchoose-axiom nil wrld)
                                   fn wrld)))
                   (len (formals fn wrld))))))

(defthm bx-choice-input-provides-function
  (implies (bx-choice-input-p fn wrld)
           (and (bx-function-p fn wrld) (not (eq fn 'quote))))
  :rule-classes (:forward-chaining :rewrite))

(local
 (defthm bx-nonempty-symbol-list-is-cons
   (implies (and (symbol-listp xs) xs) (consp xs))))

(verify-guards bx-note)
(verify-guards bx-stmt)
(verify-guards bx-prog)

(local (in-theory (disable bx-choice-input-p bx-world-properties-p bx-function-p)))

(verify-guards bx-choose-items
  :hints (("Goal" :in-theory (disable bx-beta bx-choose-parts bx-choose-literal)
           :do-not-induct t)))

; The emitted choice line carries the body recovered by the parser.

(defthm bx-item-list-p-of-choose-items
  (implies (and (symbolp fn) (bx-world-properties-p wrld)
                (bx-choice-input-p fn wrld))
           (bx-item-list-p (bx-choose-items fn wrld)))
  :hints (("Goal" :in-theory (disable bx-beta bx-choose-parts bx-choose-literal))))
