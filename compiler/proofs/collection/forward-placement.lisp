(in-package "BOYMOO-PROOFS")

(include-book "forward-calls")
(include-book "placement")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-trace-placed-p (trace world)
  (if (endp trace)
      t
    (and (proof-instruction-at-p (cdar trace) (caar trace) world)
         (collection-trace-placed-p (cdr trace) world))))

(local
 (defthm collection-writable-pair-covers-its-words
   (implies (proof-covered-p address 16 :write regions)
            (and (proof-covered-p address 8 :write regions)
                 (proof-covered-p (+ address 8) 8 :write regions)))
   :hints (("Goal"
            :use ((:instance collection-covered-subspan
                             (base address) (extent 16) (width 8) (access :write))
                  (:instance collection-covered-subspan
                             (base address) (address (+ address 8))
                             (extent 16) (width 8) (access :write))
                  (:instance collection-covered-address-is-a-span
                             (width 16) (access :write)))
            :in-theory (disable collection-covered-address-is-a-span proof-covered-p)))))

(local
 (defthm collection-pair-access-at-register
   (implies (not (equal base 31))
            (equal (proof-instruction-access-p (list :pair load base first second :offset 0)
                                               world)
                   (proof-covered-p (proof-world-reg base world) 16
                                    (if load :read :write) (proof-world-regions world))))
   :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-unsigned)))))

(local
 (defthm collection-stop-after-forward-actions
   (and (equal (proof-world-stop (collection-write-register register value world))
               (proof-world-stop world))
        (equal (proof-world-stop (collection-write-pc address world))
               (proof-world-stop world))
        (equal (proof-world-stop (collection-write-flags flags world))
               (proof-world-stop world))
        (equal (proof-world-stop (collection-write-word address value world))
               (proof-world-stop world)))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned
                                       (:definition ash) (:definition acl2::binary-logand))))))

(local
 (in-theory (disable proof-instruction-effect proof-instruction-at-p proof-world-reg
                     proof-world-pc proof-world-machine proof-world-regions proof-world-stop
                     proof-reg proof-load-word proof-covered-p proof-regions-p
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-flags
                     collection-subtract-flags proof-word-tag
                     boymoo-model::a64-unsigned boymoo-model::a64-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand)
                     (:definition acl2::binary-logior))))

(local
 (defthm collection-instruction-at-after-writable-pair-store
   (let ((next (collection-write-word (+ address 8) second
                                      (collection-write-word address first world))))
     (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-regions-p (proof-world-regions world))
                   (proof-covered-p address 16 :write (proof-world-regions world)))
              (equal (proof-instruction-at-p instruction pc next)
                     (proof-instruction-at-p instruction pc world))))
   :hints (("Goal"
            :use ((:instance collection-writable-pair-covers-its-words
                             (regions (proof-world-regions world))))
            :in-theory (disable collection-writable-pair-covers-its-words)))))

(defthm collection-placed-cons-forward-is-ready
  (let* ((source (collection-cons-source world))
         (seen (equal (collection-read-word source world) 6))
         (destination (- (proof-world-reg 21 world) 16))
         (regions (proof-world-regions world))
         (trace (collection-cons-forward-trace seen origin))
         (link (proof-world-reg 30 world)))
    (implies (and (collection-cons-forward-entry-p origin world)
                  (not (proof-world-stop world))
                  (proof-regions-p regions)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (collection-trace-placed-p trace world)
                  (not (assoc-equal link trace))
                  (if seen
                      (proof-covered-p source 16 :read regions)
                    (and (proof-covered-p source 16 :write regions)
                         (proof-covered-p destination 16 :write regions))))
             (collection-trace-ready-p trace (list link) world)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-covered-address-is-a-span
                            (address (- (proof-world-reg 21 world) 16))
                            (width 16) (access :write) (regions (proof-world-regions world)))
                 (:instance collection-writable-pair-covers-its-words
                            (address (- (proof-world-reg 21 world) 16))
                            (regions (proof-world-regions world)))
                 (:instance collection-writable-pair-covers-its-words
                            (address (collection-cons-source world))
                            (regions (proof-world-regions world))))
           :cases ((equal (collection-read-word (collection-cons-source world) world) 6))
           :in-theory (disable collection-trace-effect-of-append
                               collection-covered-address-is-a-span
                               collection-writable-pair-covers-its-words))
          (and stable-under-simplificationp '(:in-theory (enable proof-pointer-address)))))

(local
 (defthm collection-payload-memory-access-at-register
   (implies (not (equal base 31))
            (equal (proof-instruction-access-p (list :single load 8 base register :offset 0)
                                               world)
                   (proof-covered-p (proof-world-reg base world) 8
                                    (if (equal load 1) :read :write)
                                    (proof-world-regions world))))
   :hints (("Goal"
            :in-theory (enable proof-reg proof-world-reg boymoo-model::a64-read-reg)))))

(local
 (defthm collection-word-span-contains-first-and-remaining-words
   (implies (and (posp count)
                 (proof-covered-p address (* 8 count) access regions)
                 (unsigned-byte-p 64 (+ 8 address)))
            (and (proof-covered-p address 8 access regions)
                 (proof-covered-p (+ 8 address) (* 8 (1- count)) access regions)))
   :hints (("Goal"
            :use ((:instance collection-covered-subspan
                             (base address) (extent (* 8 count)) (width 8))
                  (:instance collection-covered-subspan
                             (base address) (address (+ 8 address))
                             (extent (* 8 count)) (width (* 8 (1- count))))
                  (:instance collection-covered-address-is-a-span (width (* 8 count))))
            :in-theory (disable collection-covered-address-is-a-span)))))

(local
 (defthm collection-copy-iteration-keeps-placed-trace
   (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                 (proof-regions-p (proof-world-regions world))
                 (proof-covered-p (proof-world-reg 20 world) 8 :write
                                  (proof-world-regions world)))
            (equal (collection-trace-placed-p trace (collection-copy-word-effect world))
                   (collection-trace-placed-p trace world)))
   :hints (("Goal" :induct (collection-trace-placed-p trace world)))))

(local
 (defthm collection-copy-iteration-metadata-unchanged
   (let ((after (collection-copy-word-effect world)))
     (and (equal (proof-world-regions after) (proof-world-regions world))
          (equal (proof-world-stop after) (proof-world-stop world))))))

(defun collection-placed-payload-entry-p (count origin world)
  (let ((regions (proof-world-regions world))
        (bytes (* 8 count)))
    (and (collection-payload-span-p count world)
         (proof-span-p origin 224)
         (not (proof-world-stop world))
         (equal (proof-world-pc world) (+ origin (if (zp count) 212 188)))
         (proof-regions-p regions)
         (collection-trace-placed-p (collection-forward-trace :copy-word origin) world)
         (proof-covered-p (proof-world-reg 2 world) bytes :read regions)
         (proof-covered-p (proof-world-reg 20 world) bytes :write regions))))

(local
 (defthm collection-copy-iteration-prepares-next-payload-entry
   (implies (and (collection-placed-payload-entry-p count origin world)
                 (posp count))
            (collection-placed-payload-entry-p
             (1- count) origin (collection-copy-word-effect world)))
   :hints (("Goal"
            :use ((:instance collection-payload-iteration-frame)
                  (:instance collection-payload-iteration-preserves-span)
                  (:instance collection-copy-iteration-keeps-placed-trace
                             (trace (collection-forward-trace :copy-word origin)))
                  (:instance collection-word-span-contains-first-and-remaining-words
                             (address (proof-world-reg 2 world)) (access :read)
                             (regions (proof-world-regions world)))
                  (:instance collection-word-span-contains-first-and-remaining-words
                             (address (proof-world-reg 20 world)) (access :write)
                             (regions (proof-world-regions world))))
            :in-theory (disable collection-payload-iteration-frame
                                collection-payload-iteration-preserves-span
                                collection-forward-trace collection-trace-placed-p
                                collection-copy-iteration-keeps-placed-trace
                                collection-word-span-contains-first-and-remaining-words)))))

(local
 (defthm collection-copy-iteration-extends-ready-payload-trace
   (let* ((copy (collection-forward-trace :copy-word origin))
          (cuts (list (+ origin 212))))
     (implies (and (collection-placed-payload-entry-p count origin world)
                   (posp count)
                   (collection-trace-ready-p suffix cuts (collection-copy-word-effect world)))
              (collection-trace-ready-p (append copy suffix) cuts world)))
   :hints (("Goal"
            :use ((:instance collection-word-span-contains-first-and-remaining-words
                             (address (proof-world-reg 2 world)) (access :read)
                             (regions (proof-world-regions world)))
                  (:instance collection-word-span-contains-first-and-remaining-words
                             (address (proof-world-reg 20 world)) (access :write)
                             (regions (proof-world-regions world))))
            :in-theory (disable collection-word-span-contains-first-and-remaining-words
                                collection-copy-iteration-keeps-placed-trace
                                collection-copy-iteration-metadata-unchanged)))))

(defthm collection-placed-payload-copy-is-ready
  (implies (collection-placed-payload-entry-p count origin world)
           (collection-trace-ready-p (collection-copy-payload-trace count origin)
                                     (list (+ origin 212)) world))
  :rule-classes nil
  :hints (("Goal" :induct (collection-copy-payload-effect count world)
                  :in-theory (disable collection-placed-payload-entry-p
                                      collection-forward-trace collection-copy-word-effect
                                      collection-trace-ready-p
                                      collection-copy-iteration-extends-ready-payload-trace))
          ("Subgoal *1/1"
           :in-theory (enable collection-placed-payload-entry-p collection-trace-ready-p))
          ("Subgoal *1/2"
           :use ((:instance collection-copy-iteration-extends-ready-payload-trace
                            (suffix (collection-copy-payload-trace (1- count) origin)))))))

(defthm collection-placed-payload-copy-preserves-placement
  (implies (collection-placed-payload-entry-p count origin world)
           (equal (collection-trace-placed-p trace (collection-copy-payload-effect count world))
                  (collection-trace-placed-p trace world)))
  :rule-classes nil
  :hints (("Goal" :induct (collection-copy-payload-effect count world)
                  :in-theory (disable collection-placed-payload-entry-p
                                      collection-copy-word-effect collection-trace-placed-p))
          ("Subgoal *1/2"
           :use ((:instance collection-copy-iteration-prepares-next-payload-entry)
                 (:instance collection-copy-iteration-keeps-placed-trace)
                 (:instance collection-word-span-contains-first-and-remaining-words
                            (address (proof-world-reg 20 world)) (access :write)
                            (regions (proof-world-regions world))))
           :in-theory (disable collection-copy-iteration-prepares-next-payload-entry
                               collection-copy-iteration-keeps-placed-trace
                               collection-word-span-contains-first-and-remaining-words)
           :expand ((collection-placed-payload-entry-p count origin world)
                    (collection-payload-span-p count world)))))
