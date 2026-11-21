(in-package "ACL2")

(include-book "guards-events")

; A world property has the selected shape whenever its default has that
; shape. A present property is independent of the chosen default.

(defthm bx-structure-of-length-2
  (equal (>=-len x 2)
         (and (consp x) (consp (cdr x))))
  :hints (("Goal" :expand ((>=-len x 2) (>=-len (cdr x) 1)))))

(defthm bx-structure-of-length-3
  (equal (>=-len x 3)
         (and (consp x) (consp (cdr x)) (consp (cddr x))))
  :hints (("Goal" :expand ((>=-len x 3)))))

(defthm bx-structure-of-length-4
  (equal (>=-len x 4)
         (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x))))
  :hints (("Goal" :expand ((>=-len x 4)))))

(verify-guards bx-justification-p)
(verify-guards bx-attachment-property-p)
(verify-guards bx-ttags-alist-p)
(verify-guards bx-book-alist-p)
(verify-guards bx-package-import-formula-p)
(verify-guards bx-property-value-p)
(verify-guards bx-property-values-p)
(verify-guards bx-world-properties-p)

(defthm bx-world-properties-imply-plist-worldp
  (implies (bx-world-properties-p wrld) (plist-worldp wrld))
  :rule-classes (:rewrite :forward-chaining))

(defthm bx-world-properties-imply-property-values
  (implies (bx-world-properties-p wrld) (bx-property-values-p wrld))
  :rule-classes :forward-chaining)

(defthm bx-world-properties-p-of-cdr
  (implies (bx-world-properties-p wrld)
           (bx-world-properties-p (cdr wrld))))

(local
 (defthm bx-property-value-p-of-fgetprop
   (implies (and (bx-property-values-p wrld)
                 (bx-property-value-p name key default))
            (bx-property-value-p name key (fgetprop name key default wrld)))
   :hints (("Goal" :induct (fgetprop name key default wrld)
            :in-theory (disable bx-property-value-p)))
   :rule-classes nil))

(defthm bx-fgetprop-change-default
  (implies (not (equal (fgetprop name key default wrld) default))
           (equal (fgetprop name key other wrld)
                  (fgetprop name key default wrld)))
  :rule-classes nil)

(local
 (defthm bx-fgetprop-does-not-return-unbound
   (implies (not (eq default *acl2-property-unbound*))
            (not (eq (fgetprop name key default wrld) *acl2-property-unbound*)))))

(local (in-theory (disable fgetprop formals bx-property-value-p)))

(local (defthm bx-package-import-formula-of-nil
         (bx-package-import-formula-p name nil)))

(defthm bx-world-constraint-property
  (implies (bx-world-properties-p wrld)
           (and (listp (getpropc fn 'constraint-lst-etc nil wrld))
                (listp (getpropc fn 'constraint-lst-etc '(t . nil) wrld))))
  :hints (("Goal"
           :use ((:instance bx-property-value-p-of-fgetprop
                            (name fn) (key 'constraint-lst-etc) (default nil))
                 (:instance bx-property-value-p-of-fgetprop
                            (name fn) (key 'constraint-lst-etc) (default '(t . nil))))
           :in-theory (enable bx-property-value-p))))

(defthm bx-world-justification
  (implies (bx-world-properties-p wrld)
           (bx-justification-p (getpropc fn 'justification nil wrld)))
  :hints (("Goal" :use ((:instance bx-property-value-p-of-fgetprop
                                   (name fn) (key 'justification) (default nil)))
           :in-theory (e/d (bx-property-value-p) (bx-justification-p)))))

(defthm bx-world-event-number
  (implies (bx-world-properties-p wrld)
           (rationalp (getpropc fn 'absolute-event-number 0 wrld)))
  :hints (("Goal" :use ((:instance bx-property-value-p-of-fgetprop
                                   (name fn) (key 'absolute-event-number) (default 0)))
           :in-theory (enable bx-property-value-p))))

(defthm bx-quote-has-no-formals
  (implies (bx-property-values-p wrld)
           (equal (getpropc 'quote 'formals default wrld) default))
  :hints (("Goal" :induct (fgetprop 'quote 'formals default wrld)
           :in-theory (enable fgetprop bx-property-value-p))))

(defthm bx-present-function-is-not-quote
  (implies (and (bx-world-properties-p wrld) (bx-function-p fn wrld))
           (not (equal fn 'quote)))
  :rule-classes ((:forward-chaining :trigger-terms ((bx-function-p fn wrld)))))

(defthm bx-world-formals
  (implies (bx-world-properties-p wrld)
           (symbol-listp (formals fn wrld)))
  :hints (("Goal"
           :use ((:instance bx-property-value-p-of-fgetprop
                            (name fn) (key 'formals) (default nil))
                 (:instance bx-fgetprop-change-default
                            (name fn) (key 'formals) (default t) (other nil)))
           :cases ((eq fn 'quote))
           :in-theory (e/d (bx-property-value-p formals) (symbol-listp)))))

(defthm bx-world-body
  (implies (bx-world-properties-p wrld)
           (pseudo-termp (getpropc fn 'unnormalized-body nil wrld)))
  :hints (("Goal" :use ((:instance bx-property-value-p-of-fgetprop
                                   (name fn) (key 'unnormalized-body) (default nil)))
           :in-theory (e/d (bx-property-value-p) (pseudo-termp)))))

(defthm bx-world-theorem
  (implies (bx-world-properties-p wrld)
           (and (pseudo-termp (getpropc name 'theorem nil wrld))
                (bx-package-import-formula-p name (getpropc name 'theorem nil wrld))))
  :hints (("Goal" :use ((:instance bx-property-value-p-of-fgetprop
                                   (key 'theorem) (default nil)))
           :in-theory (e/d (bx-property-value-p)
                           (pseudo-termp bx-package-import-formula-p)))))

(defthm bx-world-choice
  (implies (bx-world-properties-p wrld)
           (pseudo-termp (getpropc fn 'defchoose-axiom nil wrld)))
  :hints (("Goal" :use ((:instance bx-property-value-p-of-fgetprop
                                   (name fn) (key 'defchoose-axiom) (default nil)))
           :in-theory (e/d (bx-property-value-p) (pseudo-termp)))))

(defthm bx-world-siblings
  (implies (bx-world-properties-p wrld)
           (symbol-listp (getpropc c 'siblings nil wrld)))
  :hints (("Goal" :use ((:instance bx-property-value-p-of-fgetprop
                                   (name c) (key 'siblings) (default nil)))
           :in-theory (e/d (bx-property-value-p) (symbol-listp)))))

(defthm bx-world-packages
  (implies (known-package-alistp
            (getpropc 'known-package-alist 'global-value :missing wrld))
           (known-package-alistp (getpropc 'known-package-alist 'global-value nil wrld)))
  :hints (("Goal" :use ((:instance bx-fgetprop-change-default
                                   (name 'known-package-alist) (key 'global-value)
                                   (default :missing) (other nil)))
           :in-theory (disable known-package-alistp))))

(defthm bx-world-attachment
  (implies (and (bx-world-properties-p wrld)
                (eq (cadar wrld) 'attachment))
           (bx-attachment-property-p (cddar wrld)))
  :hints (("Goal" :in-theory (enable bx-property-value-p bx-world-properties-p))))

; The book checks read only the current values of these globals.

(defthm bx-world-ttags
  (implies (bx-book-globals-p wrld)
           (bx-ttags-alist-p (global-val 'ttags-seen wrld)))
  :hints (("Goal" :use ((:instance bx-fgetprop-change-default
                                   (name 'ttags-seen) (key 'global-value)
                                   (default :missing)
                                   (other (global-val 'ttags-seen nil))))
           :in-theory (e/d (global-val) (bx-ttags-alist-p)))))

(defthm bx-world-book-alist
  (implies (bx-book-globals-p wrld)
           (bx-book-alist-p (global-val 'include-book-alist wrld)))
  :hints (("Goal" :use ((:instance bx-fgetprop-change-default
                                   (name 'include-book-alist) (key 'global-value)
                                   (default :missing)
                                   (other (global-val 'include-book-alist nil))))
           :in-theory (e/d (global-val) (bx-book-alist-p)))))

; These lookups are performed by symbols with formals in the world.

(local (in-theory (e/d (listp) (bx-world-properties-p))))

(verify-guards bx-function-p)
(verify-guards bx-functions-present-p)
(verify-guards bx-in-use-p)
(verify-guards bx-reserve-kind-p)
(verify-guards bx-constrained-p
  :hints (("Goal" :use bx-world-constraint-property)))
(verify-guards bx-rulers
  :hints (("Goal" :use bx-world-justification
           :in-theory (disable bx-world-justification))))
(verify-guards bx-event-number)

; Positions of formulas are written as decimal characters.

(local
 (defthm bx-characterp-of-digit-to-char
   (characterp (digit-to-char n))))

(defthm bx-characters-of-explode-nonnegative-integer
  (implies (character-listp acc)
           (character-listp (explode-nonnegative-integer n base acc)))
  :hints (("Goal" :in-theory (disable floor mod digit-to-char))))

(verify-guards bx-fresh-name
  :hints (("Goal" :in-theory (disable bx-in-use-p explode-nonnegative-integer))))
(verify-guards bx-formula-name)
(verify-guards bx-same-rulers)
(verify-guards bx-all-constrained-p)
(verify-guards bx-some-constrained-p)
(verify-guards bx-names-with-content)
(verify-guards bx-names-reserved)
(verify-guards bx-arities)
(verify-guards bx-defs)
(verify-guards bx-ground-defines)

; An encapsulate's first function either stores the constraint itself
; or names the function that stores it.

(defthm bx-names-of-cons
  (implies (consp x) (equal (bx-names x) x)))

(local
 (in-theory (disable bx-ev-unlocal bx-ev-type bx-ev-namex bx-ev-symbol-class
                     bx-event-tuple-p bx-event-fields-p bx-ev-form
                     bx-ev-depth bx-ev-number bx-names bx-defun-form-p
                     constraint-info)))

(defthm bx-constraint-info-for-owner
  (implies (bx-constraint-owner-p fn wrld)
           (equal (mv-nth 1 (constraint-info fn wrld))
                  (car (getpropc fn 'constraint-lst-etc nil wrld))))
  :hints (("Goal" :use ((:instance bx-fgetprop-change-default
                                   (name fn) (key 'constraint-lst-etc)
                                   (default nil) (other '(t . nil))))
           :in-theory (enable constraint-info))))

(defthm bx-constraint-result-for-owner
  (implies (bx-constraint-owner-p fn wrld)
           (or (unknown-constraints-p (mv-nth 1 (constraint-info fn wrld)))
               (pseudo-term-listp (mv-nth 1 (constraint-info fn wrld)))))
  :hints (("Goal" :in-theory (disable unknown-constraints-p pseudo-term-listp))))

; The error default here is the error default of ACL2's constraint reader.

(local
 (defthm bx-constraint-info-name
   (implies (bx-constrainer-input-p fn wrld)
            (let* ((value (car (getpropc fn 'constraint-lst-etc nil wrld)))
                   (owner (if (and value (symbolp value)) value fn)))
              (equal (mv-nth 0 (constraint-info fn wrld)) owner)))
   :hints (("Goal" :use ((:instance bx-fgetprop-change-default
                                    (name fn) (key 'constraint-lst-etc)
                                    (default nil) (other '(t . nil))))
            :in-theory (e/d (constraint-info)
                            (bx-constraint-owner-p unknown-constraints-p
                             pseudo-term-listp bx-functions-present-p))))))

(verify-guards bx-constraint-owner-p)
(verify-guards bx-constrainer-input-p)
(verify-guards bx-event-constraint-p)
(verify-guards bx-event-constraints-p)
(verify-guards bx-constrainer)

(defthm bx-owner-of-bx-constrainer
  (implies (and (bx-event-names-p ev)
                (bx-event-constraint-p ev wrld)
                (equal (bx-ev-type ev) 'encapsulate)
                (consp (bx-ev-namex ev)))
           (and (symbolp (bx-constrainer ev wrld))
                (bx-constraint-owner-p (bx-constrainer ev wrld) wrld)))
  :hints (("Goal" :in-theory (disable bx-constraint-owner-p
                                      bx-functions-present-p))))

(local
 (defthm bx-symbolp-of-bx-constrainer
   (implies (and (bx-event-names-p ev)
                 (bx-event-constraint-p ev wrld))
            (symbolp (bx-constrainer ev wrld)))))

(verify-guards bx-depth-stack-p)
(verify-guards bx-pop)
(verify-guards bx-first-constrainer)

(defthm bx-depth-stack-p-of-bx-pop
  (implies (bx-depth-stack-p stack)
           (bx-depth-stack-p (bx-pop stack d))))

(verify-guards bx-enclose
  :hints (("Goal" :in-theory (disable bx-constrainer bx-pop bx-first-constrainer
                                     bx-event-names-p bx-event-constraint-p
                                     bx-constrainer-input-p bx-constraint-owner-p))))
