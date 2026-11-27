(in-package "BOYMOO-PROOFS")

(include-book "slot-calls")
(include-book "rewrite-words")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-slot-words (count base world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (collection-read-word base world) (collection-slot-words (1- count) (+ 8 base) world))))

(local
 (defun collection-slot-index-induction (index count base world)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (collection-slot-words count base world)
     (collection-slot-index-induction (1- index) (1- count) (+ 8 base) world))))

(defthm collection-slot-word-at-index
  (implies (and (natp count) (natp index) (< index count) (integerp base))
           (equal (nth index (collection-slot-words count base world))
                  (collection-read-word (+ base (* 8 index)) world)))
  :hints (("Goal" :induct (collection-slot-index-induction index count base world)
                  :in-theory (disable collection-read-word proof-load-word))
          ("Subgoal *1/1" :expand ((collection-slot-words count base world)))
          ("Subgoal *1/2" :expand ((collection-slot-words count base world)))))

; A plan entry gives one word returned by the forwarder and the trace
; of that call. The caller writes the returned word into its slot.
(defun collection-slot-rewrite-round-trace (roots plan origin)
  (append (collection-slot-call-trace roots origin)
          (cadr plan)
          (collection-slot-store-trace roots origin)))

(defun collection-slot-limit-test-trace (roots origin)
  (collection-linux-trace (collection-slot-loop-label roots) '(0 1) origin))

(defun collection-slot-rewrite-trace (roots plans origin)
  (if (endp plans)
      (collection-slot-limit-test-trace roots origin)
    (append (collection-slot-rewrite-round-trace roots (car plans) origin)
            (collection-slot-rewrite-trace roots (cdr plans) origin))))

(defun collection-slot-rewrite-entry-p (roots total position base origin world)
  (and (collection-cpu-p world)
       (proof-span-p origin (car *collection-linux-layout*))
       (equal (proof-world-pc world) (+ origin (collection-linux-offset (collection-slot-loop-label roots))))
       (natp base) (natp position) (natp total) (<= position total)
       (unsigned-byte-p 64 (+ base (* 8 total)))
       (equal (proof-world-reg (collection-slot-cursor-register roots) world) (+ base (* 8 position)))
       (equal (proof-world-reg (collection-slot-limit-register roots) world) (+ base (* 8 total)))))

(defun collection-slot-rewrite-call-return (roots plan origin world)
  (collection-trace-effect (cadr plan)
                           (collection-trace-effect (collection-slot-call-trace roots origin) world)))

(defun collection-slot-rewrite-round-input-p (roots plan total base origin world)
  (let* ((returned (collection-slot-rewrite-call-return roots plan origin world))
         (cursor (collection-slot-cursor-register roots))
         (limit (collection-slot-limit-register roots)))
    (and (collection-cpu-p returned)
         (equal (proof-world-pc returned)
                (+ origin (collection-linux-offset (collection-slot-loop-label roots)) 16))
         (equal (proof-world-reg cursor returned) (proof-world-reg cursor world))
         (equal (proof-world-reg limit returned) (proof-world-reg limit world))
         (equal (proof-world-reg 0 returned) (car plan))
         (alistp (boymoo-model::a64-memory (proof-world-machine returned)))
         (equal (collection-slot-words total base returned) (collection-slot-words total base world)))))

(defun collection-slot-rewrite-input-p (roots plans position base origin world)
  (let ((total (+ position (len plans))))
    (and (collection-slot-rewrite-entry-p roots total position base origin world)
         (or (endp plans)
             (and (collection-slot-rewrite-round-input-p roots (car plans) total base origin world)
                  (collection-slot-rewrite-input-p
                   roots (cdr plans) (1+ position) base origin
                   (collection-trace-effect (collection-slot-rewrite-round-trace roots (car plans) origin)
                                            world)))))))

(local
 (in-theory (disable proof-world-machine proof-world-pc proof-world-reg proof-reg
                     proof-load-word proof-instruction-effect collection-cpu-p
                     collection-read-word collection-write-pc collection-write-register collection-write-flags
                     collection-subtract-flags boymoo-model::a64-unsigned boymoo-model::a64-memory
                     boymoo-model::a64-condition boymoo-model::a64-nzcv
                     collection-slot-words collection-trace-effect)))

(local
 (defthm collection-array-word-is-kept-by-forwarder
   (let* ((returned (collection-slot-rewrite-call-return roots plan origin world))
          (address (+ base (* 8 index))))
     (implies (and (collection-slot-rewrite-round-input-p roots plan total base origin world)
                   (natp total) (natp index) (< index total) (integerp base))
              (equal (collection-read-word address returned) (collection-read-word address world))))
   :hints (("Goal"
            :use ((:instance collection-slot-word-at-index (count total))
                  (:instance collection-slot-word-at-index (count total)
                             (world (collection-slot-rewrite-call-return roots plan origin world))))
            :in-theory (disable collection-slot-rewrite-call-return collection-slot-word-at-index)))))

(local
 (defthm collection-slot-rewrite-round-commits-exactly-one-array-word
   (let* ((address (+ base (* 8 index)))
          (after (collection-trace-effect (collection-slot-rewrite-round-trace roots plan origin) world)))
     (implies (and (collection-slot-rewrite-entry-p roots total position base origin world)
                   (collection-slot-rewrite-round-input-p roots plan total base origin world)
                   (< position total) (natp index) (< index total))
              (equal (collection-read-word address after)
                     (if (equal index position) (car plan) (collection-read-word address world)))))
   :hints (("Goal"
            :cases ((< index position) (equal index position))
            :use ((:instance collection-array-word-is-kept-by-forwarder)
                  (:instance collection-slot-store-commits-returned-word
                             (other (+ base (* 8 index)))
                             (world (collection-slot-rewrite-call-return roots plan origin world))))
            :in-theory (e/d (collection-slot-rewrite-call-return)
                             (collection-slot-call-trace collection-slot-store-trace
                              collection-slot-store-commits-returned-word
                              collection-array-word-is-kept-by-forwarder))))))

(local
 (defthm collection-slot-rewrite-limit-leaves-array-unchanged
   (let ((after (collection-trace-effect (collection-slot-rewrite-trace roots nil origin) world)))
     (implies (collection-slot-rewrite-entry-p roots total total base origin world)
              (and (equal (proof-world-pc after) (+ origin (collection-linux-offset "rt:scan")))
                   (equal (collection-read-word address after) (collection-read-word address world)))))
   :hints (("Goal" :cases (roots) :in-theory (enable collection-trace-effect)))))

(local
 (in-theory (disable collection-slot-rewrite-entry-p collection-slot-rewrite-round-input-p
                     collection-slot-rewrite-round-trace collection-slot-limit-test-trace)))

(local
 (defthm collection-slot-rewrite-position-is-natural
   (implies (collection-slot-rewrite-entry-p roots total position base origin world)
            (natp position))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable collection-slot-rewrite-entry-p)))))

(local
 (defun collection-slot-rewrite-induction (roots plans position base origin world)
   (declare (xargs :measure (acl2-count plans)))
   (if (endp plans)
       (list position base world)
     (collection-slot-rewrite-induction
      roots (cdr plans) (1+ position) base origin
      (collection-trace-effect (collection-slot-rewrite-round-trace roots (car plans) origin) world)))))

(defthm collection-slot-rewrite-traversal-commits-all-returned-words
  (let* ((total (+ position (len plans)))
         (trace (collection-slot-rewrite-trace roots plans origin))
         (after (collection-trace-effect trace world))
         (address (+ base (* 8 index))))
    (implies (and (collection-slot-rewrite-input-p roots plans position base origin world)
                  (natp index) (< index total))
             (equal (collection-read-word address after)
                    (if (< index position)
                        (collection-read-word address world)
                      (nth (- index position) (strip-cars plans))))))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-slot-rewrite-induction roots plans position base origin world)
           :in-theory (disable collection-slot-rewrite-round-commits-exactly-one-array-word))
          ("Subgoal *1/2"
           :cases ((< index position) (equal index position))
           :do-not-induct t
           :expand ((:free (position) (collection-slot-rewrite-input-p roots plans position base origin world))
                    (collection-slot-rewrite-trace roots plans origin))
           :use ((:instance collection-slot-rewrite-round-commits-exactly-one-array-word
                            (plan (car plans)) (total (+ position (len plans)))))
           :in-theory (disable collection-slot-rewrite-round-commits-exactly-one-array-word
                               collection-slot-rewrite-input-p collection-slot-rewrite-trace))
          ("Subgoal *1/1"
           :do-not-induct t
           :expand ((:free (position) (collection-slot-rewrite-input-p roots plans position base origin world)))
           :use ((:instance collection-slot-rewrite-limit-leaves-array-unchanged
                            (total position) (address (+ base (* 8 index)))))
           :in-theory (disable collection-slot-rewrite-limit-leaves-array-unchanged
                               collection-slot-rewrite-input-p))))

(defthm collection-checked-slot-rewrite-traversal-writes-plan
  (let* ((trace (collection-slot-rewrite-trace roots plans origin))
         (cut (list (+ origin (collection-linux-offset "rt:scan"))))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-slot-rewrite-input-p roots plans 0 base origin world)
                  (collection-trace-ready-p trace cut world)
                  (natp index) (< index (len plans)))
             (and (proof-segment-p (len trace) cut world :cut after)
                  (equal (collection-read-word (+ base (* 8 index)) after)
                         (nth index (strip-cars plans))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-slot-rewrite-traversal-commits-all-returned-words (position 0))
                 (:instance collection-ready-trace-reaches-cut
                            (trace (collection-slot-rewrite-trace roots plans origin))
                            (cuts (list (+ origin (collection-linux-offset "rt:scan"))))))
           :in-theory (disable collection-slot-rewrite-input-p collection-slot-rewrite-trace
                               collection-trace-ready-p proof-segment-p))))

(local
 (defthm collection-relocated-slot-at-index
   (implies (and (natp count) (natp index) (< index count) (integerp source))
            (equal (nth index (collection-relocated-slot-list count source data-base objects machine work))
                   (collection-relocate-datum (proof-load-word (+ source (* 8 index)) machine)
                                               data-base objects work)))
   :hints (("Goal"
            :induct (collection-slot-index-induction index count source machine)
            :in-theory (disable collection-relocate-datum collection-relocated-slot-list))
           ("Subgoal *1/1" :expand ((collection-relocated-slot-list count source data-base objects machine work)))
           ("Subgoal *1/2" :expand ((collection-relocated-slot-list count source data-base objects machine work))))))

(defthm collection-checked-slot-rewrites-install-abstract-relocations
  (let* ((count (len plans))
         (trace (collection-slot-rewrite-trace roots plans origin))
         (cut (list (+ origin (collection-linux-offset "rt:scan"))))
         (after (collection-trace-effect trace world)))
    (mv-let (words final)
      (collection-rewrite-slots count source data-base objects machine work)
      (implies (and (collection-slot-rewrite-input-p roots plans 0 base origin world)
                    (collection-trace-ready-p trace cut world)
                    (integerp source) (natp index) (< index count)
                    (collection-slot-sources-known-p count source data-base objects machine work)
                    (equal (strip-cars plans) words))
               (and (proof-segment-p (len trace) cut world :cut after)
                    (equal (collection-read-word (+ base (* 8 index)) after)
                           (collection-relocate-datum (proof-load-word (+ source (* 8 index)) machine)
                                                       data-base objects final))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-checked-slot-rewrite-traversal-writes-plan)
                 (:instance collection-slot-rewrites-agree-with-resulting-forwarding-map
                            (count (len plans)) (address source) (base data-base))
                 (:instance collection-relocated-slot-at-index
                            (count (len plans))
                            (work (mv-nth 1 (collection-rewrite-slots (len plans) source data-base objects machine work)))))
           :in-theory (disable collection-slot-rewrite-input-p collection-slot-rewrite-trace
                               collection-trace-ready-p proof-segment-p collection-rewrite-slots
                               collection-relocated-slot-list collection-slot-sources-known-p
                               collection-relocate-datum collection-slot-rewrites-agree-with-resulting-forwarding-map
                               collection-relocated-slot-at-index))))
