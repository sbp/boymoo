(in-package "ACL2")

(include-book "guards-lines")

; The entry guards supply the world, event data, and inputs required by
; the item and line walks.

(local
 (in-theory (disable bx-export-world-p bx-world-properties-p
                     bx-event-world-p bx-event-list-p bx-event-constraints-p
                     bx-event-aids-input-p bx-event-aids bx-world-aids-p
                     bx-enclose bx-events bx-enclosed-events-p
                     bx-items bx-range-items bx-select bx-not-ground
                     bx-library-order bx-check-stmts bx-library-problems
                     bx-ground-tables bx-ground-defines bx-library-program-order
                     bx-definition-lines-p bx-line-list-p bx-item-list-p
                     bx-line-p bx-runnable bx-attach-lines bx-attachment-pairs
                     bx-world-at bx-book-notes bx-note-lines bx-count-lines
                     bx-translations-p bx-functions-present-p
                     fgetprop plist-worldp known-package-alistp reverse)))

(local
 (defthm bx-items-are-cons-or-nil
   (let ((items (bx-items pairs pending defined translations wrld acc)))
     (implies (and (bx-world-properties-p wrld)
                   (known-package-alistp
                    (getpropc 'known-package-alist 'global-value :missing wrld))
                   (bx-enclosed-events-p pairs wrld) (bx-pending-p pending wrld)
                   (bx-translations-p translations) (bx-item-list-p acc))
              (and (true-listp items) (iff (consp items) items))))
   :hints (("Goal" :use ((:instance bx-item-listp-implies-true-listp
                                    (x (bx-items pairs pending defined translations wrld acc))))
            :in-theory (disable bx-item-listp-implies-true-listp)))))

(verify-guards bx-library-lines
  :hints (("Goal" :do-not-induct t)))

(verify-guards bx-book-lines
  :hints (("Goal" :do-not-induct t)))
