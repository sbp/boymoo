(in-package "ACL2")

(include-book "well-formed-terms")
(include-book "system/pseudo-good-worldp" :dir :system)

(set-verify-guards-eagerness 0)

(local (in-theory (disable pseudo-good-worldp pseudo-good-worldp1
                           pseudo-good-world-triplep pseudo-global-valuep
                           fgetprop)))

;;; The stored property shapes from ACL2's PSEUDO-GOOD-WORLDP, for
;;; the properties used to construct statements and program text.

(defun wf-pseudo-property-p (prop val)
  (case prop
    ((unnormalized-body theorem defchoose-axiom) (pseudo-termp val))
    (constraint-lst-etc (constraint-lst-etc-p val))
    (justification (or (null val) (pseudo-justificationp nil val)))
    (global-value (known-package-alistp val))
    (otherwise t)))

(defun wf-world-property-shapes-p (wrld)
  (if (consp wrld)
      (and (or (eq (cddar wrld) *acl2-property-unbound*)
               (and (eq (cadar wrld) 'global-value)
                    (not (eq (caar wrld) 'known-package-alist)))
               (wf-pseudo-property-p (cadar wrld) (cddar wrld)))
           (wf-world-property-shapes-p (cdr wrld)))
    (null wrld)))

;;; Additional shape conditions on the values of stored properties.

(defun wf-function-name-list-p (xs)
  (if (consp xs)
      (and (wf-function-name-p (car xs)) (wf-function-name-list-p (cdr xs)))
    (null xs)))

(defun wf-package-alist-names-p (xs)
  (if (consp xs)
      (and (wf-package-name-p (caar xs)) (wf-package-alist-names-p (cdr xs)))
    t))

(defun wf-package-axiom-imports-p (rule formula)
  (case-match formula
    (('equal ('pkg-imports ('quote name)) ('quote imports))
     (or (not (and (stringp name)
                   (eq rule (intern-in-package-of-symbol
                             (concatenate 'string name "-PACKAGE") 'acl2::x))))
         (symbol-listp imports)))
    (& t)))

(defun wf-attachment-targets-p (pairs)
  (if (consp pairs)
      (and (symbolp (cdar pairs)) (wf-attachment-targets-p (cdr pairs)))
    t))

(defun wf-world-attachment-targets-p (wrld)
  (if (consp wrld)
      (let ((val (cddar wrld)))
        (and (or (not (eq (cadar wrld) 'attachment))
                 (atom val)
                 (eq (car val) :attachment-disallowed)
                 (wf-attachment-targets-p val))
             (wf-world-attachment-targets-p (cdr wrld))))
    t))

(defun wf-property-details-p (sym prop val)
  (or (eq val *acl2-property-unbound*)
      (case prop
        (formals (or (member-eq sym *initial-program-fns-with-raw-code*)
                     (arglistp val)))
        (unnormalized-body
         (or (null val) (and (wf-term-details-p val t) (wf-exec-input-p val))))
        (theorem (and (or (null val) (wf-term-details-p val t))
                      (wf-package-axiom-imports-p sym val)))
        (defchoose-axiom (or (null val) (wf-term-details-p val t)))
        (constraint-lst-etc
         (or (symbolp (car val))
             (unknown-constraints-p (car val))
             (wf-term-list-details-p (car val) t)))
        (siblings (wf-function-name-list-p val))
        (global-value
         (or (not (eq sym 'known-package-alist))
             (wf-package-alist-names-p val)))
        (otherwise t))))

(defun wf-world-property-list-p (wrld)
  (if (consp wrld)
      (and (wf-property-details-p (caar wrld) (cadar wrld) (cddar wrld))
           (wf-world-property-list-p (cdr wrld)))
    t))

; The exporter omits an initial function with raw code unless it finds
; a stored body. Such a body, if present, still needs legal formals.

(defun wf-raw-function-formals-p (names wrld)
  (if (consp names)
      (and (or (null (getpropc (car names) 'unnormalized-body nil wrld))
               (arglistp (formals (car names) wrld)))
           (wf-raw-function-formals-p (cdr names) wrld))
    t))

(defun wf-world-properties-p (wrld)
  (and (wf-world-property-list-p wrld)
       (wf-raw-function-formals-p *initial-program-fns-with-raw-code* wrld)))

(local
 (defthm wf-world-property-list-from-properties
   (implies (wf-world-properties-p wrld) (wf-world-property-list-p wrld))
   :rule-classes (:forward-chaining :rewrite)))

(local (in-theory (disable wf-world-properties-p)))

;;; The properties needed by individual events must be present. Event
;;; fields are read with the exporter's event-tuple accessors.

(defun wf-bodies-present-p (names wrld)
  (if (consp names)
      (and (getpropc (car names) 'unnormalized-body nil wrld)
           (wf-bodies-present-p (cdr names) wrld))
    t))

(defun wf-ground-functions-p (names wrld)
  (and (wf-function-name-list-p names) (wf-bodies-present-p names wrld)))

(defun wf-reserve-names-p (names wrld)
  (if (consp names)
      (and (or (not (bx-reserve-kind-p (car names) wrld))
               (wf-name-p (car names)))
           (wf-reserve-names-p (cdr names) wrld))
    t))

(defun wf-stobj-event-data-p (names wrld)
  (if (consp names)
      (let ((name (car names)))
        (and (cond ((bx-function-p name wrld)
                    (let ((body (getpropc name 'unnormalized-body nil wrld)))
                      (and (or (not (bx-programp name wrld)) body)
                           (or (null body) (wf-function-name-p name)))))
                   ((bx-reserve-kind-p name wrld) (wf-name-p name))
                   (t t))
             (wf-stobj-event-data-p (cdr names) wrld)))
    t))

(defun wf-constraint-owner-p (fn wrld)
  (let* ((prop (getpropc fn 'constraint-lst-etc nil wrld))
         (data (car prop)))
    (and (wf-function-name-p fn)
         (consp prop)
         (or (null data) (consp data)))))

(defun wf-encapsulate-data-p (names wrld)
  (and (wf-function-name-list-p names)
       (let* ((fn (car names))
              (prop (getpropc fn 'constraint-lst-etc nil wrld))
              (data (car prop)))
         (and (consp prop)
              (not (eq data t))
              (wf-constraint-owner-p
               (if (and data (symbolp data)) data fn) wrld)))))

; The strengthened axiom compares the choice function applied to two
; lists of free variables. Check the second list where this form occurs.

(defun wf-choice-second-formals-p (fn axiom formals)
  (case-match axiom
    (('if & ('if ('equal (!fn . &) (!fn . free2)) . &) ''nil)
     (or (null free2)
         (and (arglistp free2) (equal (len free2) (len formals)))))
    (& t)))

(defun wf-event-data-p (event wrld)
  (let* ((type (bx-ev-type event))
         (names (bx-names (bx-ev-namex event)))
         (name (car names)))
    (case type
      ((defun defuns)
       (cond ((eq (bx-ev-symbol-class event) :program)
              (or (not (bx-all-program-p names wrld))
                  (wf-function-name-list-p names)))
             ((bx-some-program-p names wrld) t)
             ((and (bx-some-constrained-p names wrld)
                   (not (bx-all-constrained-p names wrld))) t)
             (t (wf-ground-functions-p names wrld))))
      ((defthm defaxiom)
       (and (wf-name-p name) (not (null (getpropc name 'theorem nil wrld)))))
      (defchoose
       (let ((axiom (getpropc name 'defchoose-axiom nil wrld)))
         (cond ((bx-constrained-p name wrld)
                (and (wf-function-name-p name) (not (null axiom))))
               ((null axiom) t)
               (t (and (wf-function-name-p name)
                       (arglistp (formals name wrld))
                       (wf-choice-second-formals-p name axiom (formals name wrld)))))))
      (encapsulate (or (atom names)
                       (and (consp (bx-ev-namex event))
                            (wf-encapsulate-data-p names wrld))))
      (defpkg (not (null (getpropc 'known-package-alist 'global-value nil wrld))))
      ((defmacro defconst deflabel deftheory) (wf-reserve-names-p names wrld))
      ((defstobj defabsstobj) (wf-stobj-event-data-p names wrld))
      (otherwise t))))

(defun wf-world-event-data-p (tail wrld lo hi)
  (if (consp tail)
      (and (or (not (and (eq (caar tail) 'event-landmark)
                        (eq (cadar tail) 'global-value)))
               (let ((n (bx-ev-number (cddar tail))))
                 (or (not (integerp n)) (<= n lo) (< hi n)
                     (wf-event-data-p (cddar tail) wrld))))
           (wf-world-event-data-p (cdr tail) wrld lo hi))
    t))

(defun wf-translations-p (translations)
  (if (consp translations)
      (and (or (not (and (eq (cadar translations) :ok) (cddar translations)))
               (and (wf-term-p (cddar translations))
                    (wf-exec-input-p (cddar translations))))
           (wf-translations-p (cdr translations)))
    t))

;;; ACL2's world predicate entails the shapes used by the exporter.

(local
 (defthm wf-pseudo-property-of-triple
   (implies (and (pseudo-good-world-triplep triple wrld redefp)
                 (not (eq (cddr triple) *acl2-property-unbound*))
                 (or (not (eq (cadr triple) 'global-value))
                     (eq (car triple) 'known-package-alist)))
            (wf-pseudo-property-p (cadr triple) (cddr triple)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable pseudo-good-world-triplep pseudo-global-valuep)))))

(local
 (defthm wf-shapes-from-pseudo-good-worldp1
   (implies (pseudo-good-worldp1 wrld redefp)
            (wf-world-property-shapes-p wrld))
   :rule-classes nil
   :hints (("Goal" :induct (pseudo-good-worldp1 wrld redefp)
            :in-theory (e/d (pseudo-good-worldp1) (wf-pseudo-property-p)))
           ("Subgoal *1/2"
            :use ((:instance wf-pseudo-property-of-triple
                             (triple (car wrld)) (wrld (cdr wrld))))))))

(defthm well-formed-property-shapes-of-pseudo-good-world
  (implies (pseudo-good-worldp wrld redefp)
           (wf-world-property-shapes-p wrld))
  :hints (("Goal" :use wf-shapes-from-pseudo-good-worldp1
           :in-theory
           (e/d (pseudo-good-worldp)
                (wf-world-property-shapes-p sequential-event-landmarksp
                 sequential-command-landmarksp good-command-blocksp)))))

;;; Property lookups use ACL2's shapes with the additional restrictions.

(local
 (defthm wf-pseudo-property-of-fgetprop
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-pseudo-property-p prop default)
                 (or (not (eq prop 'global-value)) (eq sym 'known-package-alist)))
            (wf-pseudo-property-p prop (getpropc sym prop default wrld)))
   :rule-classes nil
   :hints (("Goal" :induct (fgetprop sym prop default wrld)
            :in-theory (e/d (fgetprop) (wf-pseudo-property-p))))))

(local
 (defthm wf-property-details-of-fgetprop
   (implies (and (wf-world-property-list-p wrld)
                 (wf-property-details-p sym prop default))
            (wf-property-details-p sym prop (getpropc sym prop default wrld)))
   :rule-classes nil
   :hints (("Goal" :induct (fgetprop sym prop default wrld)
            :in-theory (e/d (fgetprop getprop-default)
                            (wf-property-details-p))))))

(local
 (defthm wf-fgetprop-not-unbound
   (implies (not (eq default *acl2-property-unbound*))
            (not (eq (getpropc sym prop default wrld) *acl2-property-unbound*)))
   :hints (("Goal" :in-theory (enable fgetprop)))))

(local
 (defthm wf-fgetprop-change-default
   (implies (not (equal (getpropc sym prop first wrld) first))
            (equal (getpropc sym prop other wrld)
                   (getpropc sym prop first wrld)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fgetprop)))))

(local
 (defthm wf-world-formals-of-nonraw
   (implies (and (wf-world-property-list-p wrld)
                 (not (member-eq fn *initial-program-fns-with-raw-code*)))
            (arglistp (formals fn wrld)))
   :hints (("Goal"
            :use ((:instance wf-property-details-of-fgetprop
                             (prop 'formals) (sym fn) (default nil))
                  (:instance wf-fgetprop-change-default
                             (prop 'formals) (sym fn) (first t) (other nil)))
            :in-theory (enable formals hard-error wf-property-details-p
                               arglistp arglistp1)))))

(local
 (defthm wf-raw-function-formals-for-member
   (implies (and (wf-raw-function-formals-p names wrld)
                 (member-equal fn names)
                 (getpropc fn 'unnormalized-body nil wrld))
            (arglistp (formals fn wrld)))))

(defthm wf-world-formals
  (implies (and (wf-world-properties-p wrld)
                (or (not (member-eq fn *initial-program-fns-with-raw-code*))
                    (getpropc fn 'unnormalized-body nil wrld)))
           (arglistp (formals fn wrld)))
  :hints (("Goal"
           :use ((:instance wf-raw-function-formals-for-member
                            (names *initial-program-fns-with-raw-code*)))
           :in-theory (e/d (wf-world-properties-p)
                           (formals wf-raw-function-formals-p)))))

(defthm wf-world-body
  (implies (and (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (getpropc fn 'unnormalized-body nil wrld))
           (and (wf-term-p (getpropc fn 'unnormalized-body nil wrld))
                (wf-exec-input-p (getpropc fn 'unnormalized-body nil wrld))))
  :hints (("Goal"
           :use ((:instance wf-pseudo-property-of-fgetprop
                            (prop 'unnormalized-body) (sym fn) (default nil))
                 (:instance wf-property-details-of-fgetprop
                            (prop 'unnormalized-body) (sym fn) (default nil)))
           :in-theory (enable wf-term-p wf-property-details-p))))

(defthm wf-world-formula
  (implies (and (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (getpropc name 'theorem nil wrld))
           (wf-term-p (getpropc name 'theorem nil wrld)))
  :hints (("Goal"
           :use ((:instance wf-pseudo-property-of-fgetprop
                            (prop 'theorem) (sym name) (default nil))
                 (:instance wf-property-details-of-fgetprop
                            (prop 'theorem) (sym name) (default nil)))
           :in-theory (enable wf-term-p wf-property-details-p))))

(defthm wf-world-choice-axiom
  (implies (and (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (getpropc fn 'defchoose-axiom nil wrld))
           (wf-term-p (getpropc fn 'defchoose-axiom nil wrld)))
  :hints (("Goal"
           :use ((:instance wf-pseudo-property-of-fgetprop
                            (prop 'defchoose-axiom) (sym fn) (default nil))
                 (:instance wf-property-details-of-fgetprop
                            (prop 'defchoose-axiom) (sym fn) (default nil)))
           :in-theory (enable wf-term-p wf-property-details-p))))

(defthm wf-world-siblings
  (implies (wf-world-properties-p wrld)
           (wf-function-name-list-p (getpropc fn 'siblings nil wrld)))
  :hints (("Goal"
           :use ((:instance wf-property-details-of-fgetprop
                            (prop 'siblings) (sym fn) (default nil)))
           :in-theory (enable wf-property-details-p))))

(local
 (defthm wf-pseudo-function-symbol-listp-is-symbol-listp
   (equal (pseudo-function-symbol-listp x n) (symbol-listp x))
   :hints (("Goal" :induct (pseudo-function-symbol-listp x n)))))

(defthm wf-world-rulers
  (implies (wf-world-property-shapes-p wrld)
           (wf-ruler-extenders-p (bx-rulers fn wrld)))
  :hints (("Goal"
           :use ((:instance wf-pseudo-property-of-fgetprop
                            (prop 'justification) (sym fn) (default nil)))
           :in-theory (enable wf-ruler-extenders-p pseudo-ruler-extendersp
                              bx-rulers))))

(defthm wf-world-package-alist
  (implies (wf-world-property-shapes-p wrld)
           (known-package-alistp (getpropc 'known-package-alist 'global-value nil wrld)))
  :hints (("Goal"
           :use ((:instance wf-pseudo-property-of-fgetprop
                            (prop 'global-value) (sym 'known-package-alist)
                            (default nil))))))

(defthm wf-world-package-alist-names
  (implies (wf-world-properties-p wrld)
           (wf-package-alist-names-p
            (getpropc 'known-package-alist 'global-value nil wrld)))
  :hints (("Goal"
           :use ((:instance wf-property-details-of-fgetprop
                            (prop 'global-value) (sym 'known-package-alist)
                            (default nil)))
           :in-theory (enable wf-property-details-p))))

(defthm wf-world-package-axiom
  (implies (wf-world-properties-p wrld)
           (wf-package-axiom-imports-p rule (getpropc rule 'theorem nil wrld)))
  :hints (("Goal"
           :use ((:instance wf-property-details-of-fgetprop
                            (prop 'theorem) (sym rule) (default nil)))
           :in-theory (enable wf-property-details-p))))

(defthm wf-global-val-of-known-package-alist
  (implies (getpropc 'known-package-alist 'global-value nil wrld)
           (equal (global-val 'known-package-alist wrld)
                  (getpropc 'known-package-alist 'global-value nil wrld)))
  :hints (("Goal"
           :induct (getpropc 'known-package-alist 'global-value nil wrld)
           :in-theory (enable fgetprop global-val))))

;;; ACL2 stores a constraint as a list of formulas or a marker of
;;; unknown constraints. The first function's property may point to
;;; the function that owns that list.

(defthm wf-constraint-owner-of-encapsulate
  (implies (and (consp (bx-ev-namex ev))
                (eq (bx-ev-type ev) 'encapsulate)
                (wf-encapsulate-data-p (bx-names (bx-ev-namex ev)) wrld))
           (wf-constraint-owner-p (bx-constrainer ev wrld) wrld))
  :hints (("Goal" :in-theory
           (e/d (bx-constrainer constraint-info wf-encapsulate-data-p bx-names)
                (bx-ev-type bx-ev-namex wf-constraint-owner-p))
           :use ((:instance wf-fgetprop-change-default
                            (sym (car (bx-ev-namex ev))) (prop 'constraint-lst-etc)
                            (first nil) (other '(t)))))))

(defthm wf-world-constraint-formulas
  (implies (and (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (wf-constraint-owner-p fn wrld)
                (not (unknown-constraints-p (mv-nth 1 (constraint-info fn wrld)))))
           (wf-term-list-p (mv-nth 1 (constraint-info fn wrld))))
  :hints (("Goal"
           :use ((:instance wf-pseudo-property-of-fgetprop
                            (sym fn) (prop 'constraint-lst-etc) (default '(t)))
                 (:instance wf-property-details-of-fgetprop
                            (sym fn) (prop 'constraint-lst-etc) (default '(t)))
                 (:instance wf-fgetprop-change-default
                            (sym fn) (prop 'constraint-lst-etc)
                            (first nil) (other '(t))))
           :in-theory (enable constraint-info wf-term-list-p
                              wf-property-details-p))))
