(in-package "BOYMOO-COMPILER")

(include-book "../expand")
(include-book "../rt-qir")
(include-book "qir-semantics")

(logic)
(set-verify-guards-eagerness 0)

(defthmd p4-copy-uses-current-substitution
  (equal (ex-insts (mv-nth 1 (ex-inst (list dest :copy operand) known ctx branch st)))
         (cons (list dest :copy (ex-sub operand st)) (ex-insts st))))

(defthmd p4-bad-atom-records-nil-substitution
  (equal (mv-nth 1 (ex-prim dest "ACL2::BAD-ATOM<=" (list a b) known negs symbols rtq branch st))
         (ex-note-subst dest *ex-nil* st)))

(defthmd p4-bad-atom-expansion-agrees-with-primitive
  (implies (and (qir-dtemp-p dest) (not (ex-subst st)))
           (let* ((name "ACL2::BAD-ATOM<=")
                  (before (list dest :prim name a b))
                  (expanded (mv-nth 1 (ex-prim dest name (list a b) known negs symbols rtq branch st)))
                  (result (qir-operand (ex-sub dest expanded) env :m heap)))
             (equal (qir-observe :m result heap)
                    (mv-nth 0 (qir-compute before (list datum1 datum2) nil 0 :a heap program)))))
  :hints (("Goal" :in-theory (enable p4-bad-atom-records-nil-substitution qir-operand
                                      qir-compute model-routine boymoo-model::core-primitive))))

(defthmd p4-nil-branch-is-not-taken
  (let* ((before (list :if *ex-nil* yes no))
         (after (qir-block-jump (car (ex-blocks (ex-jump before facts st))))))
    (and (equal (qir-branch before env :a heap) (boymoo-model::core-value no))
         (equal (qir-branch after env :m heap) (boymoo-model::core-value no))))
  :hints (("Goal" :in-theory (enable qir-branch qir-operand)
           :do-not-induct t)))

(assert-event
 (let* ((qir-a '((:fn "ACL2::FIRST" ((:d . 0))
                  ((0 nil (((:d . 1) :prim "COMMON-LISP::CAR" (:d . 0)))
                      (:ret (:d . 1)))))))
        (qir-m (expand-functions qir-a))
        (heap (model-heap 80 nil nil nil)))
   (mv-let (reference heap)
     (model-heap-cons 7 5 heap)
     (let ((word (boymoo-model::core-datum reference)))
       (mv-let (result heap)
         (qir-run "ACL2::FIRST" (list word) qir-m :m nil heap 50)
         (mv-let (expected expected-heap)
           (qir-run "ACL2::FIRST" '((3 . 2)) qir-a :a nil heap 50)
           (declare (ignore expected-heap))
           (and (qir-a-p qir-a) (qir-m-p qir-m)
                (equal (qir-observe :m result heap) expected))))))))

(assert-event
 (let* ((source '((:fn "ACL2::STRING-COMPARE" ((:d . 0) (:d . 1))
                      ((0 nil (((:d . 2) :prim "COMMON-LISP::EQUAL" (:d . 0) (:d . 1)))
                          (:if (:d . 2) 1 2))
                       (1 nil nil (:ret (:k . 58)))
                       (2 nil nil (:ret (:k . 34)))))))
        (expanded (append (expand-program source nil) (rt-qir-functions))))
   (mv-let (first heap)
     (model-allocate-string "abc" (model-heap 80 nil nil nil))
     (mv-let (second heap)
       (model-allocate-string "abc" heap)
       (mv-let (third heap)
         (model-allocate-string "abd" heap)
         (let ((left (boymoo-model::core-datum first))
               (same (boymoo-model::core-datum second))
               (other (boymoo-model::core-datum third)))
           (mv-let (yes yes-heap)
             (qir-run "ACL2::STRING-COMPARE" (list left same) expanded :m nil heap 120)
             (mv-let (no no-heap)
               (qir-run "ACL2::STRING-COMPARE" (list left other) expanded :m nil heap 120)
               (and (qir-a-p source) (qir-m-p expanded) (not (equal left same))
                    (equal (qir-observe :m yes yes-heap)
                           (boymoo-model::core-primitive 'equal '("abc" "abc") nil))
                    (equal (qir-observe :m no no-heap)
                           (boymoo-model::core-primitive 'equal '("abc" "abd") nil)))))))))))
