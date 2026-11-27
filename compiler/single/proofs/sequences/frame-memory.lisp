(in-package "BOYMOO-PROOFS")

(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-machine-span-agrees-p (start end first last)
  (let ((old (boymoo-model::a64-memory first))
        (new (boymoo-model::a64-memory last)))
    (and (proof-byte-entries-agree-p old start end old new)
         (proof-byte-entries-agree-p new start end old new))))

(defthm sequence-world-span-agreement
  (equal (proof-memory-span-agrees-p start end before after)
         (sequence-machine-span-agrees-p start end
                                         (proof-world-machine before)
                                         (proof-world-machine after))))

(in-theory (disable proof-memory-span-agrees-p))

(defthm sequence-read-in-agreed-machine-span
  (implies (and (sequence-machine-span-agrees-p start end first last)
                (proof-subspan-p address count start end))
           (equal (boymoo-model::a64-load count address last)
                  (boymoo-model::a64-load count address first)))
  :hints (("Goal"
           :in-theory (e/d (proof-world-machine)
                           (proof-subspan-p boymoo-model::a64-memory
                            proof-byte-entries-agree-p))
           :use ((:instance sequence-agreement-preserves-load
                            (before (list first)) (after (list last))))))
  :rule-classes nil)

(local
 (defthm sequence-entry-agreement-on-subinterval
   (implies (and (proof-byte-entries-agree-p entries lower upper first last)
                 (<= lower start) (<= end upper))
            (proof-byte-entries-agree-p entries start end first last))
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries lower upper first last)))
   :rule-classes nil))

(defthm sequence-machine-agreement-on-subinterval
  (implies (and (sequence-machine-span-agrees-p lower upper first last)
                (<= lower start) (<= end upper))
           (sequence-machine-span-agrees-p start end first last))
  :hints (("Goal"
           :in-theory (disable proof-byte-entries-agree-p)
           :use ((:instance sequence-entry-agreement-on-subinterval
                            (entries (boymoo-model::a64-memory first))
                            (first (boymoo-model::a64-memory first))
                            (last (boymoo-model::a64-memory last)))
                 (:instance sequence-entry-agreement-on-subinterval
                            (entries (boymoo-model::a64-memory last))
                            (first (boymoo-model::a64-memory first))
                            (last (boymoo-model::a64-memory last))))))
  :rule-classes nil)

(defun sequence-machine-write-confined-p (start end first last)
  (and (sequence-machine-span-agrees-p 0 start first last)
       (sequence-machine-span-agrees-p end (expt 2 64) first last)))

(defthm sequence-agreement-outside-confined-write
  (implies (and (sequence-machine-write-confined-p start end first last)
                (<= 0 lower) (<= upper (expt 2 64))
                (proof-disjoint-p lower upper start end))
           (sequence-machine-span-agrees-p lower upper first last))
  :hints (("Goal"
           :in-theory (disable sequence-machine-span-agrees-p)
           :use ((:instance sequence-machine-agreement-on-subinterval
                            (lower 0) (upper start) (start lower) (end upper))
                 (:instance sequence-machine-agreement-on-subinterval
                            (lower end) (upper (expt 2 64)) (start lower) (end upper)))))
  :rule-classes nil)

(defthm sequence-load-outside-confined-write
  (implies (and (sequence-machine-write-confined-p start end first last)
                (proof-span-p address count)
                (proof-disjoint-p address (+ address count) start end))
           (equal (boymoo-model::a64-load count address last)
                  (boymoo-model::a64-load count address first)))
  :hints (("Goal"
           :in-theory (disable sequence-machine-write-confined-p
                               sequence-machine-span-agrees-p)
           :use ((:instance sequence-agreement-outside-confined-write
                            (lower address) (upper (+ address count)))
                 (:instance sequence-read-in-agreed-machine-span
                            (start address) (end (+ address count))))))
  :rule-classes nil)

(local
 (defthm sequence-byte-at-noninteger-address
   (implies (not (integerp byte))
            (equal (boymoo-model::a64-byte byte memory)
                   (boymoo-model::a64-byte 0 memory)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte
                                    sequence-a64-unsigned-as-mod)))))

(local
 (defthm sequence-save-pair-outside-byte
   (let ((new (boymoo-model::a64-write-bytes
               8 (+ address 8) link
               (boymoo-model::a64-write-bytes 8 address saved memory))))
     (implies (and (proof-span-p address 16) (posp address)
                   (<= 0 byte) (< byte (expt 2 64))
                   (or (< byte address) (<= (+ address 16) byte)))
              (equal (boymoo-model::a64-byte byte new)
                     (boymoo-model::a64-byte byte memory))))
   :hints (("Goal" :cases ((integerp byte))))))

(local
 (defthm sequence-save-pair-outside-entries
   (let ((new (boymoo-model::a64-write-bytes
               8 (+ address 8) link
               (boymoo-model::a64-write-bytes 8 address saved memory))))
     (implies (and (proof-span-p address 16) (posp address)
                   (<= 0 start) (<= end (expt 2 64))
                   (proof-disjoint-p start end address (+ address 16)))
              (proof-byte-entries-agree-p entries start end memory new)))
   :hints (("Goal" :induct (len entries))
           ("Subgoal *1/1"
            :use ((:instance sequence-save-pair-outside-byte (byte (caar entries))))))
   :rule-classes nil))

(defthm sequence-save-pair-confines-memory-write
  (let ((memory (boymoo-model::a64-memory first)))
    (implies (and (proof-span-p address 16) (posp address)
                  (equal (boymoo-model::a64-memory last)
                         (boymoo-model::a64-write-bytes
                          8 (+ address 8) link
                          (boymoo-model::a64-write-bytes 8 address saved memory))))
             (sequence-machine-write-confined-p address (+ address 16) first last)))
  :hints
  (("Goal"
    :in-theory (disable proof-byte-entries-agree-p)
    :use ((:instance sequence-save-pair-outside-entries
                     (memory (boymoo-model::a64-memory first))
                     (entries (boymoo-model::a64-memory first))
                     (start 0) (end address))
          (:instance sequence-save-pair-outside-entries
                     (memory (boymoo-model::a64-memory first))
                     (entries (boymoo-model::a64-memory last))
                     (start 0) (end address))
          (:instance sequence-save-pair-outside-entries
                     (memory (boymoo-model::a64-memory first))
                     (entries (boymoo-model::a64-memory first))
                     (start (+ address 16)) (end (expt 2 64)))
          (:instance sequence-save-pair-outside-entries
                     (memory (boymoo-model::a64-memory first))
                     (entries (boymoo-model::a64-memory last))
                     (start (+ address 16)) (end (expt 2 64))))))
  :rule-classes nil)
