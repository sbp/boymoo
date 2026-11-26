(in-package "BOYMOO-PROOFS")

(include-book "frame-memory")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-span-agreement-can-fail-to-compose
  (let ((first (list (boymoo-model::a64-state nil 0 0 0 '((3/2 . 0)))))
        (middle (list (boymoo-model::a64-state nil 0 0 0 nil)))
        (last (list (boymoo-model::a64-state nil 0 0 0 '((0 . 1))))))
    (and (proof-memory-span-agrees-p 1 2 first middle)
         (proof-memory-span-agrees-p 1 2 middle last)
         (not (proof-memory-span-agrees-p 1 2 first last))))
  :hints
  (("Goal"
    :in-theory (enable proof-memory-span-agrees-p proof-byte-entries-agree-p
                       boymoo-model::a64-state boymoo-model::a64-memory boymoo-model::a64-byte)))
  :rule-classes nil)

(defun sequence-memory-addresses-p (memory)
  (if (atom memory)
      (null memory)
    (and (consp (car memory))
         (unsigned-byte-p 64 (caar memory))
         (sequence-memory-addresses-p (cdr memory)))))

(local
 (defthm sequence-word-update-keeps-word-addresses
   (implies (and (sequence-memory-addresses-p memory)
                 (unsigned-byte-p 64 address))
            (sequence-memory-addresses-p (put-assoc-equal address value memory)))
   :hints
   (("Goal" :induct (put-assoc-equal address value memory)))))

(defthm sequence-a64-writes-keep-word-addresses
  (implies (sequence-memory-addresses-p memory)
           (sequence-memory-addresses-p (boymoo-model::a64-write-bytes count address value memory)))
  :hints
  (("Goal"
    :in-theory (enable (:induction boymoo-model::a64-write-bytes))
    :induct (boymoo-model::a64-write-bytes count address value memory)
    :expand ((boymoo-model::a64-write-bytes count address value memory))))
  :rule-classes nil)

(local
 (defthm sequence-load-one-is-a-byte
   (equal (boymoo-model::a64-load 1 address machine)
          (boymoo-model::a64-byte address (boymoo-model::a64-memory machine)))
   :hints (("Goal" :expand ((boymoo-model::a64-read-bytes 1 address (boymoo-model::a64-memory machine))
                            (boymoo-model::a64-read-bytes 0 (+ 1 (ifix address))
                                                          (boymoo-model::a64-memory machine)))))))

(local
 (defthm sequence-ordinary-byte-agrees-through-intermediate-memory
   (implies (and (sequence-machine-span-agrees-p start end first middle)
                 (sequence-machine-span-agrees-p start end middle last)
                 (unsigned-byte-p 64 address)
                 (natp start) (natp end)
                 (<= start address) (< address end))
            (equal (boymoo-model::a64-byte address (boymoo-model::a64-memory first))
                   (boymoo-model::a64-byte address (boymoo-model::a64-memory last))))
   :hints
   (("Goal"
     :in-theory (disable sequence-machine-span-agrees-p)
     :use ((:instance sequence-read-in-agreed-machine-span (count 1) (last middle))
           (:instance sequence-read-in-agreed-machine-span (count 1) (first middle)))))
   :rule-classes nil))

(local
 (defthm sequence-word-address-entries-agree-through-intermediate-memory
   (implies (and (sequence-machine-span-agrees-p start end first middle)
                 (sequence-machine-span-agrees-p start end middle last)
                 (natp start) (natp end) (sequence-memory-addresses-p entries))
            (proof-byte-entries-agree-p entries start end
                                       (boymoo-model::a64-memory first) (boymoo-model::a64-memory last)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-byte-entries-agree-p) (sequence-machine-span-agrees-p))
     :induct (sequence-memory-addresses-p entries))
    ("Subgoal *1/2"
     :use ((:instance sequence-ordinary-byte-agrees-through-intermediate-memory
                      (address (caar entries))))))
   :rule-classes nil))

(defthm sequence-word-addressed-span-agreement-composes
  (implies (and (sequence-machine-span-agrees-p start end first middle)
                (sequence-machine-span-agrees-p start end middle last)
                (natp start) (natp end)
                (sequence-memory-addresses-p (boymoo-model::a64-memory first))
                (sequence-memory-addresses-p (boymoo-model::a64-memory last)))
           (sequence-machine-span-agrees-p start end first last))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-machine-span-agrees-p) (proof-byte-entries-agree-p))
    :use ((:instance sequence-word-address-entries-agree-through-intermediate-memory
                     (entries (boymoo-model::a64-memory first)))
          (:instance sequence-word-address-entries-agree-through-intermediate-memory
                     (entries (boymoo-model::a64-memory last))))))
  :rule-classes nil)
