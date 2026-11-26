(in-package "BOYMOO-PROOFS")

(include-book "code-protection")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable ash mod floor assembly-low boymoo-model::a64-unsigned
                           boymoo-model::a64-ones boymoo-model::a64-read-bytes)))

(defthm assembly-byte-load-is-memory-lookup
  (equal (boymoo-model::a64-load 1 address machine)
         (boymoo-model::a64-byte address (boymoo-model::a64-memory machine)))
  :hints (("Goal"
           :expand ((:free (memory) (boymoo-model::a64-read-bytes 1 address memory))
                    (:free (at memory) (boymoo-model::a64-read-bytes 0 at memory))))))

(defthm assembly-memory-after-register-change
  (and (equal (boymoo-model::a64-memory (boymoo-model::a64-set-pc value machine))
              (boymoo-model::a64-memory machine))
       (equal (boymoo-model::a64-memory (boymoo-model::a64-set-nzcv value machine))
              (boymoo-model::a64-memory machine))
       (equal (boymoo-model::a64-memory
               (boymoo-model::a64-write-reg register width use-sp value machine))
              (boymoo-model::a64-memory machine)))
  :hints (("Goal" :in-theory (disable nth update-nth))))

(local
 (defthm assembly-low64-after-offset-addition
   (implies (and (integerp value) (integerp offset))
            (equal (assembly-low 64 (+ offset (assembly-low 64 value)))
                   (assembly-low 64 (+ offset value))))
   :hints (("Goal"
            :use ((:instance assembly-floor-bounds
                             (x (+ offset value)) (d (expt 2 64)))
                  (:instance assembly-floor-unique
                             (x (+ offset (assembly-low 64 value))) (d (expt 2 64))
                             (q (- (floor (+ offset value) (expt 2 64))
                                   (floor value (expt 2 64))))))
            :in-theory (enable assembly-low mod)))))

(local
 (defthm assembly-low64-of-ifix
   (equal (assembly-low 64 (ifix value)) (assembly-low 64 value))
   :hints (("Goal" :in-theory (enable assembly-low)))))

(defthm assembly-effective-address-plus
  (implies (and (integerp offset)
                (unsigned-byte-p 64 (+ offset (boymoo-model::a64-unsigned 64 base))))
           (equal (boymoo-model::a64-unsigned 64 (+ offset (ifix base)))
                  (+ offset (boymoo-model::a64-unsigned 64 base))))
  :hints (("Goal"
           :use ((:instance assembly-low64-after-offset-addition (value (ifix base))))
           :in-theory (disable assembly-low mod floor assembly-low64-after-offset-addition))))

(local (in-theory (disable assembly-a64-unsigned-is-low assembly-low)))

(local
 (defthm assembly-unsigned-address-is-natural
   (unsigned-byte-p 64 (boymoo-model::a64-unsigned 64 address))
   :hints (("Goal"
            :use ((:instance assembly-low-bounds (width 64) (value address)))
            :in-theory (enable assembly-a64-unsigned-is-low)))
   :rule-classes
   ((:rewrite)
    (:forward-chaining :trigger-terms ((boymoo-model::a64-unsigned 64 address))))))

(local
 (defthm assembly-unsigned-address-identity
   (implies (unsigned-byte-p 64 address)
            (equal (boymoo-model::a64-unsigned 64 address) address))
   :hints (("Goal" :in-theory (enable assembly-a64-unsigned-is-low)))))

(local
 (defthm assembly-assoc-other-key-after-word-write
   (implies (not (equal key updated))
            (equal (assoc-equal key (put-assoc-equal updated value memory))
                   (assoc-equal key memory)))
   :hints (("Goal" :induct (put-assoc-equal updated value memory)))))

(local
 (defthm assembly-byte-of-other-address-after-binding
   (implies (and (unsigned-byte-p 64 address) (not (equal address updated)))
            (equal (boymoo-model::a64-byte address (put-assoc-equal updated value memory))
                   (boymoo-model::a64-byte address memory)))))

(local (in-theory (disable boymoo-model::a64-byte)))

(local
 (defthm assembly-one-byte-write
   (equal (boymoo-model::a64-write-bytes 1 pointer value memory)
          (put-assoc-equal (boymoo-model::a64-unsigned 64 pointer)
                           (boymoo-model::a64-unsigned 8 value) memory))
   :hints (("Goal"
            :expand ((boymoo-model::a64-write-bytes 1 pointer value memory)
                     (:free (at word tail) (boymoo-model::a64-write-bytes 0 at word tail)))))))

(local
 (defthm assembly-other-byte-after-writes
   (let ((start (boymoo-model::a64-unsigned 64 pointer)))
     (implies (and (natp count) (unsigned-byte-p 64 address)
                   (<= (+ start count) (expt 2 64))
                   (or (< address start) (<= (+ start count) address)))
              (equal (boymoo-model::a64-byte
                      address (boymoo-model::a64-write-bytes count pointer value memory))
                     (boymoo-model::a64-byte address memory))))
   :hints (("Goal" :induct (boymoo-model::a64-write-bytes count pointer value memory))
           ("Subgoal *1/2"
            :cases ((equal count 1))
            :use ((:instance assembly-effective-address-plus (base pointer) (offset 1)))
            :in-theory (disable assembly-effective-address-plus)))))

(defthm assembly-model-store-writes-only-its-span
  (let ((start (boymoo-model::a64-unsigned 64 pointer)))
    (implies (and (natp count) (unsigned-byte-p 64 address)
                  (<= (+ start count) (expt 2 64))
                  (or (< address start) (<= (+ start count) address)))
             (equal (boymoo-model::a64-load 1 address
                                           (boymoo-model::a64-store count pointer value machine))
                    (boymoo-model::a64-load 1 address machine))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-write-bytes))))

(local
 (defthm assembly-assoc-outside-cleared-addresses
   (implies (or (< address start) (<= end address))
            (equal (assoc-equal address (proof-clear-memory start end memory))
                   (assoc-equal address memory)))
   :hints (("Goal" :induct (proof-clear-memory start end memory)))))

(defthm assembly-cleared-span-keeps-other-bytes
  (implies (and (unsigned-byte-p 64 address)
                (or (< address start) (<= end address)))
           (equal (boymoo-model::a64-load 1 address
                                         (proof-world-machine (proof-clear-span start end world)))
                  (boymoo-model::a64-load 1 address (proof-world-machine world))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte))))

(defthm assembly-store-bytes-keeps-other-bytes
  (implies (and (unsigned-byte-p 64 address) (natp start)
                (<= (+ start (len bytes)) (expt 2 64))
                (or (< address start) (<= (+ start (len bytes)) address)))
           (equal (boymoo-model::a64-load 1 address (proof-store-bytes bytes start machine))
                  (boymoo-model::a64-load 1 address machine)))
  :hints (("Goal" :in-theory (disable proof-overlay-bytes))))
