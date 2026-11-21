(in-package "ACL2")

(include-book "core")

; The event tuple readers use the cons structure of the tuple and its
; header. The list of event records is preserved by the world scan.

(defthm bx-plist-worldp-of-cdr
  (implies (plist-worldp wrld)
           (plist-worldp (cdr wrld))))

(defthm bx-true-listp-of-plist-world
  (implies (plist-worldp wrld) (true-listp wrld))
  :rule-classes (:rewrite :forward-chaining))

(defthm bx-fields-of-world-triple
  (implies (and (plist-worldp wrld) (consp wrld))
           (and (consp (car wrld))
                (consp (cdar wrld))
                (symbolp (caar wrld))
                (symbolp (cadar wrld))))
  :rule-classes :forward-chaining)

(local
 (defthm bx-event-tuple-p-implies-consp
   (implies (bx-event-tuple-p ev) (consp ev))
   :rule-classes :forward-chaining))

(verify-guards bx-ev-unlocal)
(verify-guards bx-event-fields-p)
(verify-guards bx-event-tuple-p)
(verify-guards bx-ev-number)
(verify-guards bx-ev-depth)
(verify-guards bx-ev-type)
(verify-guards bx-ev-skipped-proofs-p)
(verify-guards bx-signature-fns)
(verify-guards bx-ev-namex)
(verify-guards bx-ev-form)
(verify-guards bx-ev-symbol-class)
(verify-guards bx-names)
(verify-guards bx-definition-forms-p)
(verify-guards bx-defun-form-p)

(defthm bx-rationalp-of-event-depth
  (implies (bx-event-tuple-p ev)
           (rationalp (bx-ev-depth ev))))

(defthm bx-true-listp-of-event-form
  (implies (bx-event-tuple-p ev)
           (true-listp (bx-ev-form ev))))

(local
 (in-theory (disable bx-ev-unlocal bx-event-fields-p bx-event-tuple-p
                     bx-ev-number bx-ev-depth bx-ev-type bx-ev-namex
                     bx-ev-symbol-class bx-ev-form bx-ev-skipped-proofs-p
                     bx-names bx-defun-form-p)))

(verify-guards bx-event-names-p)
(verify-guards bx-event-list-p)
(verify-guards bx-event-world-p)

(defthm bx-event-list-p-of-bx-events
  (implies (and (bx-event-world-p wrld)
                (bx-event-list-p acc))
           (bx-event-list-p (bx-events wrld lo hi acc)))
  :hints (("Goal" :induct (bx-events wrld lo hi acc))))

(verify-guards bx-events)
(verify-guards bx-world-at)
(verify-guards bx-skipped)
(verify-guards bx-book-files)

; Translation requests use the definition forms and their symbol names.

(local (in-theory (disable fgetprop formals)))

(verify-guards bx-programp)
(verify-guards bx-all-program-p)
(verify-guards bx-needs-translation-p)
(verify-guards bx-defun-forms
  :hints (("Goal" :in-theory (enable bx-defun-form-p))))

(defthm bx-alistp-when-definition-forms-p
  (implies (bx-definition-forms-p defs) (alistp defs)))

(local
 (defthm bx-definition-form-of-assoc-equal
   (implies (bx-definition-forms-p defs)
            (and (true-listp (assoc-equal fn defs))
                 (iff (consp (assoc-equal fn defs)) (assoc-equal fn defs))))))

(defthm bx-definition-forms-of-bx-defun-forms
  (implies (bx-defun-form-p form)
           (bx-definition-forms-p (bx-defun-forms form)))
  :hints (("Goal" :in-theory (enable bx-defun-form-p))))

(local (in-theory (disable bx-defun-forms)))

(local
 (defthm consp-of-last-of-cons
   (implies (consp x) (consp (last x)))
   :rule-classes (:type-prescription :rewrite)))

(local
 (defthm cons-of-last-of-bx-definition
   (implies (and (bx-definition-forms-p defs)
                 (assoc-equal fn defs))
            (consp (last (assoc-equal fn defs))))))

(verify-guards bx-requests-of
  :hints (("Goal" :in-theory (disable bx-needs-translation-p))))
(verify-guards bx-requests)
(verify-guards bx-translation-requests)
