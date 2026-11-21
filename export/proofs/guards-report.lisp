(in-package "ACL2")

(include-book "guards-items")

(local
 (in-theory (disable fgetprop formals plist-worldp bx-world-properties-p
                     bx-ev-unlocal bx-ev-type bx-ev-namex bx-ev-symbol-class
                     bx-event-tuple-p bx-event-fields-p bx-ev-form
                     bx-ev-depth bx-ev-number bx-names bx-defun-form-p
                     bx-event-names-p bx-defun-forms bx-justification-p
                     bx-line-p bx-item-list-p bx-attachment-property-p
                     bx-known-package-alist-is-alist bx-line-listp-implies-alistp
                     bx-item-listp-implies-alistp bx-alistp-when-definition-forms-p
                     bx-definition-list-structure bx-arities-list-structure
                     bx-named-formula-list-structure
                     hons-get)))

; Attachment properties form a table of aliases, lists of pairs, or
; marks. The attachment lookup only takes an association from a list.

(verify-guards bx-attachment-props)
(verify-guards bx-attachment-value)
(verify-guards bx-attachment-table-p)

(local
 (defthm bx-attachment-table-is-symbol-alist
   (implies (bx-attachment-table-p xs) (symbol-alistp xs))
   :hints (("Goal" :induct (bx-attachment-table-p xs)))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm bx-attachment-table-of-attachment-props
   (implies (and (bx-world-properties-p wrld) (bx-attachment-table-p acc))
            (bx-attachment-table-p (bx-attachment-props wrld acc)))
   :hints (("Goal" :induct (bx-attachment-props wrld acc)))))

(local
 (defthm bx-attachment-value-has-property-shape
   (implies (bx-attachment-table-p props)
            (bx-attachment-property-p (bx-attachment-value f props)))
   :hints (("Goal" :induct (hons-assoc-equal f props)
            :in-theory (enable hons-get hons-assoc-equal)))))

(local
 (defthm bx-allowed-attachment-value-is-alist
   (let ((val (bx-attachment-value f props)))
     (implies (and (bx-attachment-table-p props) (consp val)
                   (not (eq (car val) :attachment-disallowed)))
              (alistp val)))
   :hints (("Goal" :use bx-attachment-value-has-property-shape
            :in-theory (e/d (bx-attachment-property-p)
                            (bx-attachment-value bx-attachment-value-has-property-shape))))))

(verify-guards bx-pairs-of
  :hints (("Goal" :in-theory (disable bx-attachment-value)
           :do-not-induct t)))

(local
 (defthm bx-alistp-of-pairs-of
   (implies (and (bx-attachment-table-p props) (alistp acc))
            (alistp (bx-pairs-of xs props acc)))
   :hints (("Goal" :induct (bx-pairs-of xs props acc)
            :in-theory (disable bx-attachment-value assoc-equal)))))

(local
 (defthm bx-true-listp-of-pairs-of
   (implies (true-listp acc)
            (true-listp (bx-pairs-of xs props acc)))
   :hints (("Goal" :induct (bx-pairs-of xs props acc)
            :in-theory (disable bx-attachment-value assoc-equal)))))

(verify-guards bx-attachment-pairs
  :hints (("Goal" :in-theory (disable bx-attachment-props bx-pairs-of
                                     merge-sort-lexorder))))
(verify-guards bx-attach-lines)

(local
 (defthm bx-alistp-of-revappend
   (implies (and (alistp x) (alistp y))
            (alistp (revappend x y)))
   :hints (("Goal" :induct (revappend x y)))))

(local
 (defthm bx-alistp-of-merge-lexorder
   (implies (and (alistp x) (alistp y) (alistp acc))
            (alistp (merge-lexorder x y acc)))
   :hints (("Goal" :induct (merge-lexorder x y acc)
            :in-theory (disable lexorder)))))

(local
 (defthm bx-alistp-of-evens
   (implies (alistp x) (alistp (evens x)))
   :hints (("Goal" :induct (evens x)))))

(local
 (defthm bx-alistp-of-merge-sort-lexorder
   (implies (alistp x) (alistp (merge-sort-lexorder x)))
   :hints (("Goal" :induct (merge-sort-lexorder x)
            :in-theory (disable merge-lexorder)))))

(defthm bx-alistp-of-attachment-pairs
  (implies (bx-world-properties-p wrld)
           (alistp (bx-attachment-pairs wrld)))
  :hints (("Goal" :in-theory (disable bx-attachment-props bx-pairs-of
                                     merge-sort-lexorder))))

(local
 (defthm bx-true-listp-of-attachment-pairs
   (implies (bx-world-properties-p wrld)
            (true-listp (bx-attachment-pairs wrld)))
   :hints (("Goal" :use bx-alistp-of-attachment-pairs
            :in-theory (disable bx-attachment-pairs bx-alistp-of-attachment-pairs)))))

(defthm bx-world-properties-of-world-at
  (implies (bx-world-properties-p wrld)
           (bx-world-properties-p (bx-world-at n wrld)))
  :hints (("Goal" :induct (bx-world-at n wrld)
           :expand ((bx-world-properties-p nil)))))

; The event source forms and the justification record supply prover aids.

(verify-guards bx-kwd-value)
(verify-guards bx-xargs-items-p)
(verify-guards bx-declarations-p)
(verify-guards bx-xargs-items)

(local
 (defthm bx-xargs-items-are-list
   (true-listp (bx-xargs-items x))
   :rule-classes :type-prescription))

(verify-guards bx-xargs)
(verify-guards bx-aid-definitions-p)

(local
 (defthm bx-xargs-are-list
   (true-listp (bx-xargs x))
   :rule-classes :type-prescription))

(local
 (defthm bx-justification-record-fields
   (let ((just (getpropc fn 'justification nil wrld)))
     (implies (and (bx-world-properties-p wrld) just)
              (and (consp just) (consp (cdr just))
                   (consp (cddr just)) (consp (cdddr just))
                   (iff (consp (caddr just)) (caddr just))
                   (iff (consp (cdr (caddr just))) (cdr (caddr just)))
                   (iff (consp (cadddr just)) (cadddr just)))))
   :hints (("Goal" :use bx-world-justification
            :in-theory (e/d (bx-justification-p listp) (bx-world-justification))))))

(verify-guards bx-defun-aids
  :hints (("Goal" :in-theory (disable bx-xargs bx-xargs-items bx-declarations-p
                                     butlast bx-kwd-value)
           :do-not-induct t)))

(verify-guards bx-event-aid-input-p)
(verify-guards bx-event-aids-input-p
  :hints (("Goal" :in-theory (disable bx-event-aid-input-p))))
(verify-guards bx-world-aids-p
  :hints (("Goal" :in-theory (disable bx-event-aid-input-p))))

(local
 (defthm bx-defun-aids-are-list
   (true-listp (bx-defun-aids defs wrld))
   :rule-classes :type-prescription))

(local
 (defthm bx-true-listp-of-cdr
   (implies (true-listp x) (true-listp (cdr x)))
   :hints (("Goal" :expand ((true-listp x))))))

(local
 (defthm bx-event-form-cdrs-are-list-cells
   (let ((form (bx-ev-form ev)))
     (implies (bx-event-tuple-p ev)
              (and (iff (consp (cdr form)) (cdr form))
                   (iff (consp (cddr form)) (cddr form))
                   (true-listp (cdddr form)))))
   :hints (("Goal" :use bx-true-listp-of-event-form
            :in-theory (disable bx-true-listp-of-event-form)))))

(verify-guards bx-event-aids
  :hints (("Goal" :in-theory (disable bx-defun-aids bx-aid-definitions-p
                                     bx-xargs bx-kwd-value)
           :do-not-induct t)))

(defthm bx-event-aid-inputs-of-event-range
  (implies (and (bx-world-aids-p wrld) (bx-event-aids-input-p acc))
           (bx-event-aids-input-p (bx-events wrld lo hi acc)))
  :hints (("Goal" :induct (bx-events wrld lo hi acc)
           :in-theory (disable bx-event-aid-input-p))))

; A book's path and annotations determine the data written in its notes.

(verify-guards bx-strip-prefix)

(local
 (defthm bx-stringp-of-strip-prefix
   (implies (and (stringp s) (bx-strip-prefix prefix s))
            (stringp (bx-strip-prefix prefix s)))))

(verify-guards bx-book-name
  :hints (("Goal" :in-theory (disable bx-strip-prefix subseq))))
(verify-guards bx-marked-books
  :hints (("Goal" :in-theory (disable bx-book-name assoc-equal))))
(verify-guards bx-count-word)
(verify-guards bx-count-lines)
(verify-guards bx-book-ttags)
(verify-guards bx-note-lines)
(verify-guards bx-book-globals-p)

(local (in-theory (enable bx-item-listp-implies-alistp)))

(verify-guards bx-book-notes
  :hints (("Goal" :in-theory (disable bx-attachment-pairs bx-world-at bx-events
                                     bx-book-ttags bx-marked-books bx-skipped
                                     bx-select bx-note bx-item-list-p global-val))))

(defthm bx-book-notes-are-lists
  (implies (and (bx-item-list-p items) (bx-item-list-p check-notes))
           (true-list-listp (bx-book-notes items check-notes boot-hi lo hi
                                           books-dir cbd wrld)))
  :hints (("Goal" :in-theory (disable bx-attachment-pairs bx-world-at bx-events
                                     bx-book-ttags bx-marked-books bx-skipped
                                     bx-select bx-note bx-item-list-p global-val))))

(verify-guards bx-library-problems)

(defthm bx-library-problems-are-items
  (bx-item-list-p (bx-library-problems notes))
  :hints (("Goal" :in-theory (disable bx-select bx-note))))
