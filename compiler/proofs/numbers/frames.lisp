(in-package "BOYMOO-PROOFS")

(include-book "formulas")

(logic)
(set-verify-guards-eagerness 0)

; The frame starts at slot START in the initialized value stack. It
; extends through the current top. Its entries are ACL2 values.
(defund proof-number-frame-p (start slots world objects packages)
  (let ((prefix (proof-stack-prefix (proof-stack-top world) world objects packages)))
    (and prefix
         (natp start)
         (<= start (len (cdr prefix)))
         (true-listp slots)
         (equal (nthcdr start (cdr prefix))
                (proof-argument-views slots)))))

(defun proof-number-frame-address (start world)
  (+ (proof-stack-base world) (* 8 (nfix start))))

(defthm proof-number-frame-across-preserved-prefix
  (implies (and (proof-number-frame-p start slots before old-objects packages)
                (proof-prefix-preserved-p (proof-stack-top before)
                                          before after old-objects new-objects packages)
                (equal (proof-stack-top after) (proof-stack-top before)))
           (proof-number-frame-p start slots after new-objects packages))
  :hints (("Goal"
           :in-theory (e/d (proof-number-frame-p)
                           (proof-stack-prefix proof-stack-top proof-argument-views))))
  :rule-classes nil)

(local
 (defthm frame-keeps-register
   (implies (and (natp register) (natp upper) (<= register upper)
                 (not (member-equal register clobbers))
                 (proof-register-frame-p upper clobbers before after))
            (equal (proof-world-reg register before) (proof-world-reg register after)))
   :hints (("Goal" :induct (proof-register-frame-p upper clobbers before after)
                   :in-theory (disable proof-world-reg)))
   :rule-classes nil))

(local
 (defthm keep-frame-across-call
   (implies (and (proof-number-frame-p start slots before old-objects packages)
                 (proof-frame-return-p clobbers changes-flags before after)
                 (not (member-equal 25 clobbers))
                 (proof-preserved-heap-p may-intern before after old-objects
                                         new-objects packages))
            (proof-number-frame-p start slots after new-objects packages))
   :hints (("Goal"
            :use (proof-number-frame-across-preserved-prefix
                  (:instance frame-keeps-register (register 25) (upper 30)))
            :in-theory (disable proof-prefix-preserved-p proof-register-frame-p
                                proof-stack-prefix proof-world-reg proof-heap-p
                                proof-heap-frame-p proof-dynamic-table-preserved-p)))
   :rule-classes nil))

(defthm proof-number-frame-across-datum-return
  (implies (and (proof-number-frame-p start slots before old-objects packages)
                (proof-datum-return-p datum clobbers changes-flags allocates may-intern
                                      before after old-objects new-objects packages)
                (not (member-equal 25 clobbers)))
           (proof-number-frame-p start slots after new-objects packages))
  :hints (("Goal" :use keep-frame-across-call
                  :in-theory (disable proof-frame-return-p proof-preserved-heap-p
                                      proof-reg-value-p proof-fixed-heap-p)))
  :rule-classes nil)

(defthm proof-number-frame-across-runtime-return
  (implies (and (proof-number-frame-p start slots before old-objects packages)
                (proof-runtime-return-p name args program before after
                                        old-objects new-objects packages))
           (proof-number-frame-p start slots after new-objects packages))
  :hints (("Goal"
           :use ((:instance proof-number-frame-across-datum-return
                            (datum (boymoo-model::core-datum
                                    (proof-runtime-value name args program)))
                            (clobbers (proof-runtime-clobbers name))
                            (changes-flags (not (eq name 'acl2::bad-atom<=)))
                            (allocates (proof-runtime-allocates-p name args))
                            (may-intern (eq name 'acl2::intern-in-package-of-symbol))))
           :in-theory (disable proof-runtime-value proof-datum-return-p
                               proof-runtime-allocates-p)))
  :rule-classes nil)

(defthm proof-number-frame-across-reserve-return
  (implies (and (proof-number-frame-p start slots before old-objects packages)
                (proof-integer-reserve-return-p a b bytes before after old-objects
                                                new-objects packages))
           (proof-number-frame-p start slots after new-objects packages))
  :hints (("Goal"
           :use ((:instance keep-frame-across-call
                            (clobbers (append *proof-volatile-registers* '(24 26 27)))
                            (changes-flags t) (may-intern nil)))
           :in-theory (disable proof-frame-return-p proof-preserved-heap-p
                               proof-reserved-span-p proof-reg-value-p)))
  :rule-classes nil)

(defthm proof-number-frame-across-grow-return
  (implies (and (proof-number-frame-p start slots before old-objects packages)
                (proof-grow-return-p entry required before after old-objects
                                     new-objects packages))
           (proof-number-frame-p start slots after new-objects packages))
  :hints (("Goal"
           :use ((:instance keep-frame-across-call
                            (clobbers (if (equal entry "rt:grow")
                                          '(8 9 10 11 12 24) '(9 10 11 12 24)))
                            (changes-flags t) (may-intern nil)))
           :in-theory (disable proof-frame-return-p proof-preserved-heap-p
                               proof-fixed-heap-p proof-grow-limit proof-stack-limit)))
  :rule-classes nil)

(local
 (defun stack-slot-induction (index count address)
   (declare (xargs :measure (nfix count)))
   (if (or (zp index) (zp count))
       address
     (stack-slot-induction (1- index) (1- count) (+ 8 address)))))

(local
 (defthm length-of-stack-views
   (implies (proof-stack-views count address base objects packages machine)
            (equal (len (cdr (proof-stack-views count address base objects packages machine)))
                   (nfix count)))
   :hints (("Goal"
            :induct (proof-stack-views count address base objects packages machine)
            :in-theory (disable proof-view proof-load-word)))))

(defthm proof-number-stack-prefix-length
  (implies (proof-stack-prefix top world objects packages)
           (equal (len (cdr (proof-stack-prefix top world objects packages)))
                  (nfix (ash (- top (proof-stack-base world)) -3))))
  :hints (("Goal" :in-theory (disable proof-stack-views proof-stack-top proof-stack-base
                                      proof-heap-base proof-world-machine ash mod)))
  :rule-classes nil)

(local
 (defthm index-into-stack-views
   (implies (and (natp index) (< index (nfix count))
                 (integerp address)
                 (proof-stack-views count address base objects packages machine))
            (equal (nth index
                        (cdr (proof-stack-views count address base objects packages machine)))
                   (proof-view (proof-load-word (+ address (* 8 index)) machine)
                               base objects packages machine)))
   :hints (("Goal"
            :induct (stack-slot-induction index count address)
            :expand ((proof-stack-views count address base objects packages machine))
            :in-theory (disable proof-view proof-load-word)))
   :rule-classes nil))

(local
 (defthm index-into-values
   (implies (and (natp index) (< index (len slots)))
            (equal (nth index (proof-argument-views slots))
                   (proof-value-view (nth index slots))))
   :hints (("Goal" :induct (nth index slots)
                   :in-theory (disable proof-value-view)))))

(local
 (defthm length-of-argument-views
   (equal (len (proof-argument-views slots)) (len slots))))

(local
 (defthm index-into-tail
   (implies (and (natp start) (natp index))
            (equal (nth index (nthcdr start slots))
                   (nth (+ start index) slots)))
   :hints (("Goal" :induct (nthcdr start slots)))))

(local
 (defthm length-of-tail
   (implies (and (natp start) (<= start (len slots)))
            (equal (len (nthcdr start slots)) (- (len slots) start)))
   :hints (("Goal" :induct (nthcdr start slots)))))

(local
 (defthm frame-view-at-index
   (implies (and (natp start) (<= start (len views))
                 (natp index) (< index (len slots))
                 (equal (nthcdr start views) (proof-argument-views slots)))
            (and (< (+ start index) (len views))
                 (equal (nth (+ start index) views)
                        (proof-value-view (nth index slots)))))
   :hints (("Goal"
            :use ((:instance index-into-tail (slots views))
                  (:instance length-of-tail (slots views))
                  index-into-values)
            :in-theory (disable nth nthcdr len proof-argument-views proof-value-view
                                index-into-tail length-of-tail index-into-values)))
   :rule-classes nil))

(defthm proof-number-frame-slot-value
  (implies (and (proof-number-frame-p start slots world objects packages)
                (integerp (proof-stack-base world))
                (natp index) (< index (len slots)))
           (proof-machine-value-p
            (proof-load-word (+ (proof-number-frame-address start world) (* 8 index))
                             (proof-world-machine world))
            (nth index slots) world objects packages))
  :hints (("Goal"
           :use ((:instance index-into-stack-views
                            (index (+ start index))
                            (count (ash (- (proof-stack-top world) (proof-stack-base world)) -3))
                            (address (proof-stack-base world))
                            (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance frame-view-at-index
                            (views (cdr (proof-stack-prefix (proof-stack-top world)
                                                           world objects packages)))))
           :in-theory (e/d (proof-number-frame-p)
                           (proof-stack-views proof-argument-views proof-load-word mod
                            proof-stack-base proof-stack-top proof-view proof-value-view
                            proof-world-reg proof-world-machine proof-heap-base
                            ash nth nthcdr len true-listp))
           :do-not-induct t))
  :rule-classes nil)
