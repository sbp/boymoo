(in-package "ACL2")

(include-book "faithful-program")

; ATTACHMENT holds an alist for the attached functions or the name of
; the function that holds that alist. A disallowed entry supplies no
; attachment.

(defund faithful-world-attachment (fn wrld)
  (let* ((entry (getprop fn 'attachment nil 'current-acl2-world wrld))
         (bindings (if (and entry (symbolp entry))
                       (getprop entry 'attachment nil 'current-acl2-world wrld)
                     entry)))
    (and (consp bindings)
         (not (eq (car bindings) :attachment-disallowed))
         (assoc-equal fn bindings))))

(defund faithful-attachment-data-p (args wrld)
  (let ((pair (faithful-world-attachment (car args) wrld)))
    (and pair (equal args (list (car pair) (cdr pair))))))

; Reading the first triple for each function agrees with the system
; property lookup, including an explicitly unbound property.

(local
 (defthm faithful-attachment-value-of-collected-props
   (equal (bx-attachment-value fn (bx-attachment-props triples props))
          (if (hons-get fn props)
              (bx-attachment-value fn props)
            (getprop fn 'attachment nil 'current-acl2-world triples)))
   :hints (("Goal"
            :induct (bx-attachment-props triples props)
            :in-theory (enable hons-get hons-assoc-equal hons-acons fgetprop)))))

(local
 (defthm faithful-collected-attachments-agree
   (equal (bx-attachment-value fn (bx-attachment-props wrld nil))
          (getprop fn 'attachment nil 'current-acl2-world wrld))
   :hints (("Goal" :in-theory (disable fgetprop bx-attachment-value)))))

(local
 (defthm faithful-key-of-attachment-assoc
   (implies (assoc-equal fn bindings)
            (equal (car (assoc-equal fn bindings)) fn))))

(local
 (defthm faithful-bx-pairs-come-from-world
   (implies (and (not (member-equal pair acc))
                 (member-equal pair
                               (bx-pairs-of keys (bx-attachment-props wrld nil)
                                            acc)))
            (and pair
                 (equal pair (faithful-world-attachment (car pair) wrld))))
   :hints (("Goal"
            :induct (bx-pairs-of keys (bx-attachment-props wrld nil) acc)
            :in-theory (e/d (faithful-world-attachment)
                            (bx-attachment-props bx-attachment-value fgetprop
                             assoc-equal))))
   :rule-classes nil))

; Sorting the pairs leaves their membership unchanged.

(local
 (defthm faithful-member-of-merge-lexorder
   (iff (member-equal pair (merge-lexorder left right acc))
        (or (member-equal pair left)
            (member-equal pair right)
            (member-equal pair acc)))
   :hints (("Goal" :induct (merge-lexorder left right acc)
            :in-theory (disable lexorder revappend)))))

(local
 (defthm faithful-member-of-evens-and-odds
   (iff (or (member-equal pair (evens pairs))
            (member-equal pair (odds pairs)))
        (member-equal pair pairs))
   :hints (("Goal" :induct (evens pairs)))))

(local
 (defthm faithful-member-of-merge-sort-lexorder
   (iff (member-equal pair (merge-sort-lexorder pairs))
        (member-equal pair pairs))
   :hints (("Goal" :induct (merge-sort-lexorder pairs)
            :in-theory (disable merge-lexorder evens odds
                                faithful-member-of-evens-and-odds))
           ("Subgoal *1/2" :use faithful-member-of-evens-and-odds))))

(local
 (defthm faithful-attachment-pair-of-world
   (implies (member-equal pair (bx-attachment-pairs wrld))
            (and pair (equal pair (faithful-world-attachment (car pair) wrld))))
   :hints (("Goal"
            :use ((:instance faithful-bx-pairs-come-from-world
                             (keys (bx-attachment-props wrld nil))
                             (acc nil)))
            :in-theory (disable bx-pairs-of bx-attachment-props merge-sort-lexorder)))
   :rule-classes nil))

; Each attachment line has the data of one pair. A book may omit a
; pair that was already in force.

(local
 (defun faithful-pair-for-attachment-line (line pairs)
   (if (endp pairs)
       nil
     (if (equal line (list "attach" (list (caar pairs) (cdar pairs))))
         (cons t (car pairs))
       (faithful-pair-for-attachment-line line (cdr pairs))))))

(local
 (defthm faithful-attachment-line-has-pair
   (implies (member-equal line (bx-attach-lines pairs except))
            (faithful-pair-for-attachment-line line pairs))
   :hints (("Goal" :induct (bx-attach-lines pairs except)))
   :rule-classes nil))

(local
 (defthm faithful-attachment-line-pair-data
   (let* ((found (faithful-pair-for-attachment-line line pairs))
          (pair (cdr found)))
     (implies found
              (and (member-equal pair pairs)
                   (equal line (list "attach" (list (car pair) (cdr pair)))))))
   :hints (("Goal" :induct (faithful-pair-for-attachment-line line pairs)))
   :rule-classes nil))

(local
 (defthm faithful-attachment-line-from-world
   (implies (member-equal line (bx-attach-lines (bx-attachment-pairs wrld) except))
            (faithful-attachment-data-p (cadr line) wrld))
   :hints (("Goal"
            :use ((:instance faithful-attachment-line-has-pair
                             (pairs (bx-attachment-pairs wrld)))
                  (:instance faithful-attachment-line-pair-data
                             (pairs (bx-attachment-pairs wrld)))
                  (:instance faithful-attachment-pair-of-world
                             (pair (cdr (faithful-pair-for-attachment-line
                                         line (bx-attachment-pairs wrld))))))
            :in-theory (e/d (faithful-attachment-data-p)
                            (bx-attach-lines bx-attachment-pairs
                             faithful-pair-for-attachment-line))
            :do-not-induct t))
   :rule-classes nil))

(defthm faithful-attach-program-line
  (implies
   (and (equal (car line) "attach")
        (or (member-equal line (mv-nth 1 (bx-library-lines ground hi translations wrld)))
            (member-equal line (mv-nth 1 (bx-book-lines ground boot-hi lo hi
                                                       translations books-dir
                                                       cbd wrld)))))
   (faithful-attachment-data-p (cadr line) wrld))
  :hints (("Goal"
           :use (faithful-library-program-sources
                 faithful-book-program-sources
                 (:instance faithful-ground-program-line (bodies-p nil))
                 (:instance faithful-program-line-from-range (lo 0) (bodies-p nil))
                 (:instance faithful-program-line-from-range (bodies-p nil))
                 (:instance faithful-attachment-line-from-world (except nil))
                 (:instance faithful-attachment-line-from-world
                            (except (bx-attachment-pairs (bx-world-at boot-hi wrld)))))
           :in-theory (disable bx-library-lines bx-book-lines bx-attach-lines
                               bx-ground-defines bx-attachment-pairs bx-world-at
                               bx-select bx-range-items)
           :do-not-induct t))
  :rule-classes nil)
