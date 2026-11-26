(in-package "BOYMOO-PROOFS")

(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable acl2::binary-logior boymoo-model::a64-byte
                    boymoo-model::a64-load proof-byte-list))

(defthm p6-byte-range
  (unsigned-byte-p 8 (boymoo-model::a64-byte address memory))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte))))

(defthm p6-byte-natural
  (natp (boymoo-model::a64-byte address memory))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte))))

(defthm p6-byte-upper-bound
  (< (boymoo-model::a64-byte address memory) 256)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte))))

(defthm p6-read-bytes-natural
  (natp (boymoo-model::a64-read-bytes count address memory))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory))))

(defthm p6-read-bytes-step
  (implies (posp count)
           (equal (boymoo-model::a64-read-bytes count address memory)
                  (+ (boymoo-model::a64-byte address memory)
                     (* 256 (boymoo-model::a64-read-bytes (1- count)
                                                          (1+ (ifix address))
                                                          memory)))))
  :hints (("Goal" :expand ((boymoo-model::a64-read-bytes count address memory))
                  :in-theory (disable boymoo-model::a64-read-bytes))))

(in-theory (disable boymoo-model::a64-read-bytes))

(defthm p6-empty-byte-reads
  (implies (zp count)
           (and (equal (boymoo-model::a64-read-bytes count address memory) 0)
                (equal (proof-byte-list count address machine) nil)))
  :hints (("Goal" :expand ((boymoo-model::a64-read-bytes count address memory)
                           (proof-byte-list count address machine)))))

(defthm p6-load-one-byte
  (equal (boymoo-model::a64-load 1 address machine)
         (boymoo-model::a64-byte address (boymoo-model::a64-memory machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-load
                                   boymoo-model::a64-read-bytes))))

(defthm p6-loaded-header-fields
  (let ((header (proof-load-word address machine)))
    (and (equal (proof-header-type header) (boymoo-model::a64-load 1 address machine))
         (equal (proof-header-size header)
                (boymoo-model::a64-load 7 (1+ (ifix address)) machine))))
  :hints (("Goal"
           :in-theory (enable proof-load-word boymoo-model::a64-load
                              proof-header-size proof-header-type p6-unsigned-as-mod)
           :use ((:instance p6-floor-mod-of-scaled-sum
                            (d 256) (lo (boymoo-model::a64-byte address
                                                               (boymoo-model::a64-memory machine)))
                            (n (boymoo-model::a64-read-bytes 7 (1+ (ifix address))
                                                            (boymoo-model::a64-memory machine))))))))

(defthm p6-byte-list-step
  (implies (posp count)
           (equal (proof-byte-list count address machine)
                  (cons (boymoo-model::a64-byte address (boymoo-model::a64-memory machine))
                        (proof-byte-list (1- count) (1+ (ifix address)) machine))))
  :hints (("Goal" :expand ((proof-byte-list count address machine)))))

(local
 (defun p6-byte-pair-induct (count left right)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (list left right)
     (p6-byte-pair-induct (1- count) (1+ (ifix left)) (1+ (ifix right))))))

(defthm p6-load-equality-is-byte-list-equality
  (equal (equal (boymoo-model::a64-load count left first)
                (boymoo-model::a64-load count right second))
         (equal (proof-byte-list count left first)
                (proof-byte-list count right second)))
  :hints (("Goal"
           :induct (p6-byte-pair-induct count left right)
           :in-theory (enable boymoo-model::a64-load))
          ("Subgoal *1/2"
           :cases ((equal (boymoo-model::a64-load count left first)
                          (boymoo-model::a64-load count right second)))
           :use ((:instance p6-floor-mod-of-scaled-sum
                            (d 256) (lo (boymoo-model::a64-load 1 left first))
                            (n (boymoo-model::a64-load (1- count) (1+ (ifix left)) first)))
                 (:instance p6-floor-mod-of-scaled-sum
                            (d 256) (lo (boymoo-model::a64-load 1 right second))
                            (n (boymoo-model::a64-load (1- count) (1+ (ifix right)) second)))))
          ("Subgoal *1/1"
           :expand ((proof-byte-list count left first) (proof-byte-list count right second)
                    (boymoo-model::a64-read-bytes count left (boymoo-model::a64-memory first))
                    (boymoo-model::a64-read-bytes count right (boymoo-model::a64-memory second))))))

(defthm p6-byte-list-split
  (implies (and (natp prefix) (natp suffix) (integerp address))
           (equal (proof-byte-list (+ prefix suffix) address machine)
                  (append (proof-byte-list prefix address machine)
                          (proof-byte-list suffix (+ prefix address) machine))))
  :rule-classes nil
  :hints (("Goal" :induct (proof-byte-list prefix address machine)
                  :in-theory (enable (:induction proof-byte-list)))
          ("Subgoal *1/1" :expand ((proof-byte-list prefix address machine)))))

(local
 (defthm p6-byte-character-list
   (character-listp (proof-byte-characters bytes))))

(local
 (defun p6-bytes-p (bytes)
   (if (atom bytes)
       (null bytes)
     (and (unsigned-byte-p 8 (car bytes)) (p6-bytes-p (cdr bytes))))))

(local
 (defthm p6-string-bytes-of-byte-characters
   (implies (p6-bytes-p bytes)
            (equal (proof-string-bytes (proof-byte-characters bytes)) bytes))
   :hints (("Goal" :induct (proof-byte-characters bytes)))))

(local
 (defthm p6-unsigned-byte-list-of-span
   (p6-bytes-p (proof-byte-list count address machine))
   :hints (("Goal" :induct (proof-byte-list count address machine)
                   :in-theory (enable proof-byte-list)))))

(local
 (defthm p6-byte-characters-injective
   (implies (and (p6-bytes-p a) (p6-bytes-p b))
            (equal (equal (proof-byte-characters a) (proof-byte-characters b))
                   (equal a b)))
   :hints (("Goal"
            :in-theory (disable p6-string-bytes-of-byte-characters
                                proof-byte-characters proof-string-bytes p6-bytes-p)
            :cases ((equal (proof-byte-characters a) (proof-byte-characters b)))
            :use ((:instance p6-string-bytes-of-byte-characters (bytes a))
                  (:instance p6-string-bytes-of-byte-characters (bytes b)))))))

(defthm p6-string-views-equal-by-declared-bytes
  (equal (equal (proof-load-string left-count left first)
                (proof-load-string right-count right second))
         (equal (proof-byte-list left-count left first)
                (proof-byte-list right-count right second)))
  :hints (("Goal"
           :in-theory (disable proof-byte-characters proof-string-bytes
                               acl2::coerce-inverse-1)
           :cases ((equal (proof-load-string left-count left first)
                          (proof-load-string right-count right second)))
           :use ((:instance acl2::coerce-inverse-1
                            (acl2::x (proof-byte-characters (proof-byte-list left-count left first))))
                 (:instance acl2::coerce-inverse-1
                            (acl2::x (proof-byte-characters (proof-byte-list right-count right second))))))))

(defthm p6-byte-at-wrapped-address
  (equal (boymoo-model::a64-byte (boymoo-model::a64-unsigned 64 address) memory)
         (boymoo-model::a64-byte address memory))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte))))

(defthm p6-read-bytes-equal-at-congruent-addresses
  (implies (equal (boymoo-model::a64-unsigned 64 left)
                  (boymoo-model::a64-unsigned 64 right))
           (equal (boymoo-model::a64-read-bytes count left memory)
                  (boymoo-model::a64-read-bytes count right memory)))
  :rule-classes nil
  :hints (("Goal" :induct (p6-byte-pair-induct count left right))
          ("Subgoal *1/2"
           :use ((:instance p6-unsigned-add (width 64) (x left) (y 1))
                 (:instance p6-unsigned-add (width 64) (x right) (y 1)))
           :in-theory (e/d (boymoo-model::a64-byte)
                           (p6-unsigned-add p6-unsigned-add-integer)))))

(defthm p6-load-at-wrapped-address
  (equal (boymoo-model::a64-load count (boymoo-model::a64-unsigned 64 address) machine)
         (boymoo-model::a64-load count address machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-load)
                  :use ((:instance p6-read-bytes-equal-at-congruent-addresses
                                   (left (boymoo-model::a64-unsigned 64 address))
                                   (right address) (memory (boymoo-model::a64-memory machine)))))))

(local
 (defthm p6-positive-byte-power
   (implies (natp count) (posp (expt 256 count)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (expt 256 count) :in-theory (enable expt)))))

(defthm p6-read-bytes-bound
  (implies (natp count)
           (< (boymoo-model::a64-read-bytes count address memory) (expt 256 count)))
  :rule-classes nil
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory)
                  :in-theory (enable (:induction boymoo-model::a64-read-bytes)))
          ("Subgoal *1/2" :expand ((expt 256 count)))))

(defthm p6-load-word-range
  (unsigned-byte-p 64 (boymoo-model::a64-load 8 address machine))
  :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load) (boymoo-model::a64-memory))
                  :use ((:instance p6-read-bytes-bound
                                   (count 8) (memory (boymoo-model::a64-memory machine)))))))
