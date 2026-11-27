(in-package "BOYMOO-PROOFS")

(include-book "sweep-rounds")

(logic)
(set-verify-guards-eagerness 0)

; A sweep record consists of the mapping base, its size and its
; retention decision. The head of the remaining list is read through
; the current link, which can be the global head or a survivor's link.
(defun collection-sweep-records (mappings forwarding)
  (if (endp mappings)
      nil
    (let* ((mapping (car mappings))
           (head (car mapping))
           (size (cadr mapping)))
      (cons (list head size (if (assoc-equal (+ head 24) forwarding) t nil))
            (collection-sweep-records (cdr mappings) forwarding)))))

(defun collection-sweep-retained-bytes (records)
  (if (endp records)
      0
    (+ (if (caddar records) (nfix (cadar records)) 0)
       (collection-sweep-retained-bytes (cdr records)))))

(defun collection-sweep-discard-count (records)
  (if (endp records)
      0
    (+ (if (caddar records) 0 1)
       (collection-sweep-discard-count (cdr records)))))

(defun collection-sweep-round-trace (record origin)
  (if (caddr record)
      (collection-sweep-retain-trace origin)
    (collection-sweep-discard-trace origin)))

(defun collection-sweep-traversal-trace (records origin)
  (if (endp records)
      (collection-linux-trace "rt:sweep-string" '(0 1) origin)
    (append (collection-sweep-round-trace (car records) origin)
            (collection-sweep-traversal-trace (cdr records) origin))))

(defun collection-sweep-round-input-p (record world)
  (let* ((link (proof-world-reg 19 world))
         (head (collection-read-word link world))
         (size (collection-read-word (+ head 8) world))
         (mark (collection-read-word (+ head 16) world)))
    (and (equal head (car record))
         (not (equal head 0))
         (equal size (cadr record))
         (proof-span-p head 24)
         (alistp (boymoo-model::a64-memory (proof-world-machine world)))
         (if (caddr record)
             (and (not (equal mark 0))
                  (unsigned-byte-p 64 (+ (proof-world-reg 22 world) size)))
           (and (equal mark 0)
                (proof-span-p link 8)
                (proof-disjoint-p link (+ link 8) head (+ head size))
                (collection-relinquish-p head size world))))))

(defun collection-sweep-traversal-input-p (records origin world)
  (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-string") origin world)
       (if (endp records)
           (equal (collection-read-word (proof-world-reg 19 world) world) 0)
         (and (collection-sweep-round-input-p (car records) world)
              (collection-sweep-traversal-input-p
               (cdr records) origin
               (collection-trace-effect
                (collection-sweep-round-trace (car records) origin) world))))))

(local
 (in-theory (disable collection-sweep-entry-p collection-cpu-p collection-relinquish-p
                     proof-world-reg proof-world-pc proof-world-replies
                     proof-world-machine collection-read-word proof-span-p
                     collection-trace-effect collection-trace-ready-p proof-segment-p
                     collection-sweep-retain-trace collection-sweep-discard-trace
                     boymoo-model::a64-memory boymoo-model::a64-unsigned boymoo-model::a64-sp)))

(local
 (defthm collection-sweep-empty-case-keeps-accumulator-and-replies
   (let* ((entry (collection-linux-offset "rt:sweep-string"))
          (trace (collection-linux-trace "rt:sweep-string" '(0 1) origin))
          (next (collection-trace-effect trace world)))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (equal (collection-read-word (proof-world-reg 19 world) world) 0))
              (and (equal (proof-world-pc next)
                          (+ origin (collection-linux-offset "rt:sweep-done")))
                   (collection-cpu-p next)
                   (equal (boymoo-model::a64-sp (proof-world-machine next))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (proof-world-stop next) (proof-world-stop world))
                   (proof-streams-preserved-p world next)
                   (implies (not (equal register 0))
                            (equal (proof-world-reg register next) (proof-world-reg register world)))
                   (equal (proof-world-reg 22 next) (proof-world-reg 22 world))
                   (equal (proof-world-replies next) (proof-world-replies world)))))
   :hints (("Goal"
            :in-theory (e/d (collection-sweep-entry-p collection-trace-effect proof-span-p
                                                     proof-world-replies)
                            (proof-instruction-effect proof-load-word proof-reg
                             collection-write-pc collection-write-register
                             boymoo-model::a64-condition boymoo-model::a64-read-bytes))))))

(defthm collection-sweep-traversal-counts-retained-bytes-and-unmaps
  (let* ((trace (collection-sweep-traversal-trace records origin))
         (after (collection-trace-effect trace world)))
    (implies (collection-sweep-traversal-input-p records origin world)
             (and (equal (proof-world-pc after)
                         (+ origin (collection-linux-offset "rt:sweep-done")))
                  (equal (proof-world-reg 22 after)
                         (+ (proof-world-reg 22 world) (collection-sweep-retained-bytes records)))
                  (equal (proof-world-replies after)
                         (nthcdr (collection-sweep-discard-count records)
                                 (proof-world-replies world))))))
  :hints (("Goal" :induct (collection-sweep-traversal-input-p records origin world))
          ("Subgoal *1/1"
           :use ((:instance collection-sweep-empty-case-keeps-accumulator-and-replies))
           :in-theory (disable collection-sweep-empty-case-keeps-accumulator-and-replies))))

(defthm collection-checked-sweep-traversal-reaches-accounting
  (let* ((trace (collection-sweep-traversal-trace records origin))
         (after (collection-trace-effect trace world))
         (cuts (list (+ origin (collection-linux-offset "rt:sweep-done")))))
    (implies (and (collection-sweep-traversal-input-p records origin world)
                  (collection-trace-ready-p trace cuts world))
             (and (proof-segment-p (len trace) cuts world :cut after)
                  (equal (proof-world-reg 22 after)
                         (+ (proof-world-reg 22 world) (collection-sweep-retained-bytes records)))
                  (equal (proof-world-replies after)
                         (nthcdr (collection-sweep-discard-count records)
                                 (proof-world-replies world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-sweep-traversal-trace records origin))
                            (cuts (list (+ origin (collection-linux-offset "rt:sweep-done"))))))
           :in-theory (disable collection-sweep-traversal-input-p
                               collection-sweep-traversal-trace
                               collection-sweep-retained-bytes collection-sweep-discard-count))))

(defthm collection-sweep-traversal-keeps-stack-and-unclobbered-registers
  (let* ((trace (collection-sweep-traversal-trace records origin))
         (after (collection-trace-effect trace world)))
    (implies (collection-sweep-traversal-input-p records origin world)
             (and (collection-cpu-p after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (proof-streams-preserved-p world after)
                  (implies (not (member-equal register '(0 1 2 8 19 20 22 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :induct (collection-sweep-traversal-input-p records origin world)
           :in-theory (disable collection-sweep-round-input-p collection-sweep-entry-p
                               collection-sweep-retains-one-mapping-and-resets-mark
                               collection-sweep-discards-one-mapping-and-relinks))
          ("Subgoal *1/1"
           :use ((:instance collection-sweep-empty-case-keeps-accumulator-and-replies)))
          ("Subgoal *1/2"
           :cases ((caddar records))
           :use ((:instance collection-sweep-retains-one-mapping-and-resets-mark)
                 (:instance collection-sweep-discards-one-mapping-and-relinks))
           :in-theory (enable collection-sweep-round-input-p))))
