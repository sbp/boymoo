(in-package "ACL2")

(include-book "well-formed-items")

(set-verify-guards-eagerness 0)

(local
 (in-theory (disable fgetprop formals global-val wf-world-property-shapes-p
                     wf-world-properties-p wf-property-details-p wf-term-p
                     bx-items bx-range-items bx-enclose bx-events
                     bx-check-stmts bx-ground-tables bx-note-lines
                     bx-count-lines bx-book-notes bx-library-problems bx-event-aids)))

;;; Selecting or filtering whole lines preserves the recognizers.

(local
 (defthm wf-statement-lines-p-of-append
   (implies (and (wf-statement-lines-p a) (wf-statement-lines-p b))
            (wf-statement-lines-p (append a b)))))

(local
 (defthm wf-program-lines-p-of-append
   (implies (and (wf-program-lines-p a) (wf-program-lines-p b))
            (wf-program-lines-p (append a b)))))

(local
 (defthm wf-statement-lines-p-of-revappend
   (implies (and (wf-statement-lines-p a) (wf-statement-lines-p b))
            (wf-statement-lines-p (revappend a b)))))

(local
 (defthm wf-statement-lines-p-of-reverse
   (implies (wf-statement-lines-p a)
            (wf-statement-lines-p (reverse a)))))

(local
 (defthm wf-bx-select-statements
   (implies (wf-items-p items) (wf-statement-lines-p (bx-select :stmt items)))))

(local
 (defthm wf-bx-select-program
   (implies (wf-items-p items) (wf-program-lines-p (bx-select :prog items)))))

(local
 (defthm wf-bx-not-ground-statements
   (implies (wf-statement-lines-p lines)
            (wf-statement-lines-p (bx-not-ground lines ground)))
   :hints (("Goal" :induct (bx-not-ground lines ground)))))

(local
 (defthm wf-bx-not-ground-program
   (implies (wf-program-lines-p lines)
            (wf-program-lines-p (bx-not-ground lines ground)))
   :hints (("Goal" :induct (bx-not-ground lines ground)))))

(local
 (defthm wf-bx-words-statements
   (implies (wf-statement-lines-p lines)
            (wf-statement-lines-p (bx-words words lines)))))

(local
 (defthm wf-bx-words-define
   (implies (wf-statement-lines-p lines)
            (wf-program-lines-p (bx-words '("define") lines)))))

(local
 (defthm wf-bx-program-only
   (implies (wf-program-lines-p lines)
            (wf-program-lines-p (bx-program-only lines wrld)))))

(local
 (defthm wf-bx-runnable
   (implies (wf-program-lines-p lines)
            (wf-program-lines-p (bx-runnable lines)))))

(local
 (defthm wf-bx-ground-defines
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-ground-functions-p ground-fns wrld))
            (wf-program-lines-p (bx-ground-defines ground-fns wrld)))
   :hints (("Goal" :induct (bx-ground-defines ground-fns wrld)
            :in-theory (disable bx-rulers)))))

;;; The library's ordering walk places only lines taken from its
;;; input. The index and stack retain well-formed statements, even
;;; if the walk finds a cycle or uses up its fuel.

(local
 (defun wf-statement-index-p (index)
   (if (consp index)
       (and (wf-statement-line-p (cdar index))
            (wf-statement-index-p (cdr index)))
     (null index))))

(local
 (defun wf-statement-stack-p (stack)
   (if (consp stack)
       (and (wf-statement-line-p (caar stack))
            (wf-statement-stack-p (cdr stack)))
     (null stack))))

(local
 (defthm wf-statement-index-p-of-bx-index-fns
   (implies (and (wf-statement-index-p acc) (wf-statement-line-p stmt))
            (wf-statement-index-p (bx-index-fns fns stmt acc)))
   :hints (("Goal" :induct (bx-index-fns fns stmt acc)
            :in-theory (enable hons-acons)))))

(local
 (defthm wf-statement-index-p-of-bx-index
   (implies (and (wf-statement-lines-p lines) (wf-statement-index-p acc))
            (wf-statement-index-p (bx-index lines acc)))
   :hints (("Goal" :induct (bx-index lines acc)
            :in-theory (disable bx-index-fns)))))

(local
 (defthm wf-line-from-index
   (implies (and (wf-statement-index-p index) (hons-get fn index))
            (wf-statement-line-p (cdr (hons-get fn index))))
   :hints (("Goal" :induct (assoc-equal fn index)
            :in-theory (enable hons-assoc-equal)))))

(local
 (defthm wf-statements-of-bx-walk
   (implies (and (wf-statement-stack-p stack)
                 (wf-statement-lines-p todo)
                 (wf-statement-index-p index)
                 (wf-statement-lines-p acc))
            (wf-statement-lines-p
             (car (bx-walk stack todo index done acc notes fuel))))
   :hints (("Goal" :induct (bx-walk stack todo index done acc notes fuel)
            :in-theory (disable bx-introduced bx-used hons-get wf-statement-line-p)))))

(local
 (defthm wf-statements-of-bx-library-order
   (implies (wf-statement-lines-p lines)
            (wf-statement-lines-p (car (bx-library-order lines))))
   :hints (("Goal" :in-theory (disable bx-walk bx-index bx-steps bx-words)))))

;;; Attachment sources come from world keys. Attachment targets come
;;; from the values of the attachment property, possibly by way of
;;; another key. The old attachments only decide which pairs to omit.

(local
 (defun wf-attachment-properties-p (props)
   (if (consp props)
       (let ((val (cdar props)))
         (and (consp (car props))
              (symbolp (caar props))
              (or (atom val)
                  (eq (car val) :attachment-disallowed)
                  (wf-attachment-targets-p val))
              (wf-attachment-properties-p (cdr props))))
     (null props))))

(local
 (defun wf-attachment-pair-list-p (pairs)
   (if (consp pairs)
       (and (symbolp (caar pairs)) (symbolp (cdar pairs))
            (wf-attachment-pair-list-p (cdr pairs)))
     (null pairs))))

(local
 (defthm wf-attachment-properties-p-of-bx-attachment-props
   (implies (and (plist-worldp wrld)
                 (wf-world-attachment-targets-p wrld)
                 (wf-attachment-properties-p props))
            (wf-attachment-properties-p (bx-attachment-props wrld props)))
   :hints (("Goal" :induct (bx-attachment-props wrld props)
            :in-theory (enable hons-acons)))))

(local
 (defthm wf-attachment-value-has-symbol-targets
   (implies (and (wf-attachment-properties-p props)
                 (consp (bx-attachment-value fn props))
                 (not (eq (car (bx-attachment-value fn props)) :attachment-disallowed)))
            (wf-attachment-targets-p (bx-attachment-value fn props)))
   :hints (("Goal" :induct (hons-assoc-equal fn props)
            :in-theory (enable hons-assoc-equal hons-equal)))))

(local
 (defthm wf-attachment-target-of-assoc
   (implies (and (wf-attachment-targets-p props) (assoc-equal fn props))
            (symbolp (cdr (assoc-equal fn props))))))

(local
 (defthm wf-attachment-source-of-assoc
   (implies (and (symbolp fn) (assoc-equal fn props))
            (symbolp (car (assoc-equal fn props))))))

(local
 (defthm wf-attachment-pair-list-p-of-bx-pairs-of
   (implies (and (wf-attachment-properties-p alist)
                 (wf-attachment-properties-p props)
                 (wf-attachment-pair-list-p acc))
            (wf-attachment-pair-list-p (bx-pairs-of alist props acc)))
   :hints (("Goal" :induct (bx-pairs-of alist props acc)
            :in-theory (disable bx-attachment-value)))))

(local
 (defthm wf-attachment-pair-list-p-of-revappend
   (implies (and (wf-attachment-pair-list-p a) (wf-attachment-pair-list-p b))
            (wf-attachment-pair-list-p (revappend a b)))))

(local
 (defthm wf-attachment-pair-list-p-of-evens
   (implies (wf-attachment-pair-list-p xs)
            (wf-attachment-pair-list-p (evens xs)))
   :hints (("Goal" :induct (evens xs)))))

(local
 (defthm wf-attachment-pair-list-p-of-merge
   (implies (and (wf-attachment-pair-list-p a) (wf-attachment-pair-list-p b)
                 (wf-attachment-pair-list-p acc))
            (wf-attachment-pair-list-p (merge-lexorder a b acc)))
   :hints (("Goal" :induct (merge-lexorder a b acc)))))

(local
 (defthm wf-attachment-pair-list-p-of-sort
   (implies (wf-attachment-pair-list-p xs)
            (wf-attachment-pair-list-p (merge-sort-lexorder xs)))
   :hints (("Goal" :induct (merge-sort-lexorder xs)
            :in-theory (disable merge-lexorder evens)))))

(local
 (defthm wf-bx-attachment-pairs
   (implies (and (plist-worldp wrld) (wf-world-attachment-targets-p wrld))
            (wf-attachment-pair-list-p (bx-attachment-pairs wrld)))
   :hints (("Goal" :in-theory (disable bx-attachment-props bx-pairs-of
                                       merge-sort-lexorder)))))

(local
 (defthm wf-bx-attach-lines
   (implies (wf-attachment-pair-list-p pairs)
            (wf-program-lines-p (bx-attach-lines pairs except)))
   :hints (("Goal" :induct (bx-attach-lines pairs except)))))

;;; The statement and program outputs of the two exporter entry
;;; points. Other returned values carry notes and prover's aids.

(local
 (in-theory (disable reverse wf-world-event-data-p wf-world-attachment-targets-p
                     wf-translations-p wf-ground-functions-p
                     bx-world-at)))

(local
 (defthm wf-bx-items-of-event-range
   (implies (and (wf-world-property-shapes-p wrld)
                 (wf-world-properties-p wrld)
                 (wf-world-event-data-p wrld wrld lo hi)
                 (wf-translations-p translations))
            (wf-items-p (bx-items (bx-enclose (reverse (bx-events wrld lo hi nil))
                                             nil nil wrld)
                                  nil nil translations wrld nil)))
   :hints (("Goal" :use wf-bx-range-items
            :in-theory (union-theories (theory 'minimal-theory) '(bx-range-items))))))

(local
 (in-theory (disable bx-select bx-not-ground bx-words bx-library-order
                     bx-program-only bx-runnable bx-ground-defines
                     bx-attachment-pairs bx-attach-lines
                     wf-statement-line-p wf-program-line-p)))

(defthm well-formed-library-statements
  (implies (and (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (wf-world-event-data-p wrld wrld 0 hi))
           (wf-statement-lines-p
            (mv-nth 0 (bx-library-lines ground-fns hi translations wrld)))))

(defthm well-formed-library-program
  (implies (and (plist-worldp wrld)
                (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (wf-world-event-data-p wrld wrld 0 hi)
                (wf-world-attachment-targets-p wrld)
                (wf-translations-p translations)
                (wf-ground-functions-p ground-fns wrld))
           (wf-program-lines-p
            (mv-nth 1 (bx-library-lines ground-fns hi translations wrld)))))

(defthm well-formed-book-statements
  (implies (and (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (wf-world-event-data-p wrld wrld lo hi))
           (wf-statement-lines-p
            (mv-nth 0 (bx-book-lines ground-fns boot-hi lo hi translations
                                     books-dir cbd wrld)))))

(defthm well-formed-book-program
  (implies (and (plist-worldp wrld)
                (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (wf-world-event-data-p wrld wrld lo hi)
                (wf-world-attachment-targets-p wrld)
                (wf-translations-p translations))
           (wf-program-lines-p
            (mv-nth 1 (bx-book-lines ground-fns boot-hi lo hi translations
                                     books-dir cbd wrld)))))

;;; The statement recognizer includes the name rules for each line.

(local
 (defthm wf-statement-line-of-member
   (implies (and (member-equal line lines) (wf-statement-lines-p lines))
            (wf-statement-line-p line))
   :rule-classes nil))

(defthm well-formed-library-statement-with-names
  (implies (and (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (wf-world-event-data-p wrld wrld 0 hi)
                (member-equal line (mv-nth 0 (bx-library-lines ground-fns hi
                                                            translations wrld))))
           (wf-statement-line-p line))
  :rule-classes nil
  :hints (("Goal" :use (well-formed-library-statements
                        (:instance wf-statement-line-of-member
                                   (lines (mv-nth 0 (bx-library-lines ground-fns hi
                                                                    translations wrld)))))
           :in-theory (disable bx-library-lines well-formed-library-statements))))

(defthm well-formed-book-statement-with-names
  (implies (and (wf-world-property-shapes-p wrld)
                (wf-world-properties-p wrld)
                (wf-world-event-data-p wrld wrld lo hi)
                (member-equal line (mv-nth 0 (bx-book-lines ground-fns boot-hi lo hi
                                                         translations books-dir cbd wrld))))
           (wf-statement-line-p line))
  :rule-classes nil
  :hints (("Goal" :use (well-formed-book-statements
                        (:instance wf-statement-line-of-member
                                   (lines (mv-nth 0 (bx-book-lines ground-fns boot-hi lo hi
                                                                 translations books-dir cbd
                                                                 wrld)))))
           :in-theory (disable bx-book-lines well-formed-book-statements))))

;;; Every note item of the selected event range appears as a note
;;; line. The data, including the names in a missing-name note, are
;;; preserved by the selection and by the conversion to lines.

(local
 (defthm wf-note-line-of-member
   (implies (member-equal (list :note key data) items)
            (member-equal (list "note" (list key data))
                          (bx-note-lines (bx-select :note items))))
   :hints (("Goal" :induct (len items) :in-theory (enable bx-select bx-note-lines)))))

(local
 (defthm wf-member-of-append-left
   (implies (member-equal item items)
            (member-equal item (append items rest)))))

(local
 (defthm wf-member-of-append-right
   (implies (member-equal item rest)
            (member-equal item (append items rest)))))

(defthm well-formed-library-notes-include-item
  (implies (member-equal (list :note key data) (bx-range-items 0 hi translations wrld))
           (member-equal (list "note" (list key data))
                         (mv-nth 2 (bx-library-lines ground-fns hi translations wrld))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable bx-range-items))))

(defthm well-formed-book-notes-include-item
  (implies (member-equal (list :note key data) (bx-range-items lo hi translations wrld))
           (member-equal (list "note" (list key data))
                         (mv-nth 2 (bx-book-lines ground-fns boot-hi lo hi translations
                                                 books-dir cbd wrld))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable bx-book-notes))))
