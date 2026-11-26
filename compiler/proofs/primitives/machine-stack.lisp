(in-package "BOYMOO-PROOFS")

(include-book "machine-ops")

(logic)
(set-verify-guards-eagerness 0)

(defmacro p6-sp (world)
  `(boymoo-model::a64-sp (proof-world-machine ,world)))

(defund p6-set-sp (address world)
  (update-nth 0 (boymoo-model::a64-write-reg 31 64 t address (proof-world-machine world)) world))

(defund p6-store-word (address value world)
  (update-nth 0 (boymoo-model::a64-store 8 address value (proof-world-machine world)) world))

(local
 (defthm p6-stack-update-nth-car
   (equal (car (update-nth index value list))
          (if (zp index) value (car list)))))

(local
 (defthm p6-stack-update-nth-same-index
   (equal (update-nth index value (update-nth index old list))
          (update-nth index value list))
   :hints (("Goal" :induct (update-nth index old list)))))

(defthm p6-stack-world-preserves-environment
  (and (equal (cdr (p6-set-sp address world)) (cdr world))
       (equal (cdr (p6-store-word address value world)) (cdr world))
       (equal (proof-world-stop (p6-set-sp address world)) (proof-world-stop world))
       (equal (proof-world-stop (p6-store-word address value world)) (proof-world-stop world))
       (equal (proof-world-regions (p6-set-sp address world)) (proof-world-regions world))
       (equal (proof-world-regions (p6-store-word address value world)) (proof-world-regions world)))
  :hints (("Goal" :in-theory (enable p6-set-sp p6-store-word proof-world-stop proof-world-regions))))

(defthm p6-stack-world-preserves-registers-and-flags
  (and (equal (proof-world-reg register (p6-set-sp address world)) (proof-world-reg register world))
       (equal (proof-world-reg register (p6-store-word address value world)) (proof-world-reg register world))
       (equal (proof-world-pc (p6-set-sp address world)) (proof-world-pc world))
       (equal (proof-world-pc (p6-store-word address value world)) (proof-world-pc world))
       (equal (boymoo-model::a64-nzcv (proof-world-machine (p6-set-sp address world)))
              (boymoo-model::a64-nzcv (proof-world-machine world)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine (p6-store-word address value world)))
              (boymoo-model::a64-nzcv (proof-world-machine world))))
  :hints (("Goal" :in-theory (enable p6-set-sp p6-store-word boymoo-model::a64-store
                                     proof-world-machine proof-world-reg proof-world-pc proof-reg
                                     boymoo-model::a64-read-reg boymoo-model::a64-nzcv))))

(defthm p6-register-frame-under-stack-operations
  (and (equal (proof-register-frame-p register clobbers before (p6-set-sp address after))
              (proof-register-frame-p register clobbers before after))
       (equal (proof-register-frame-p register clobbers before (p6-store-word address value after))
              (proof-register-frame-p register clobbers before after)))
  :hints (("Goal" :induct (proof-register-frame-p register clobbers before after)
                  :in-theory (disable (:definition proof-register-frame-p))
                  :expand ((:free (last) (proof-register-frame-p register clobbers before last))))))

(defthm p6-world-sp-under-stack-operations
  (and (equal (p6-sp (p6-set-sp address world)) (boymoo-model::a64-unsigned 64 address))
       (equal (p6-sp (p6-store-word address value world)) (p6-sp world)))
  :hints (("Goal" :in-theory (enable p6-set-sp p6-store-word proof-world-machine
                                     boymoo-model::a64-store boymoo-model::a64-sp))))

(defthm p6-stack-operations-preserve-register-file
  (implies (p6-register-file-p world)
           (and (p6-register-file-p (p6-set-sp address world))
                (p6-register-file-p (p6-store-word address value world))))
  :hints (("Goal" :in-theory (enable p6-set-sp p6-store-word p6-register-file-p
                                     boymoo-model::a64-store proof-world-machine))))

(defthm p6-sp-is-a-word
  (unsigned-byte-p 64 (p6-sp world))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-sp))))

(defthm p6-sp-is-natural
  (natp (p6-sp world))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable boymoo-model::a64-sp))))

(defthm p6-subtract-sixteen-without-wrap
  (implies (and (unsigned-byte-p 64 value) (<= 16 value))
           (equal (boymoo-model::a64-unsigned 64 (- value 16)) (- value 16)))
  :hints (("Goal" :in-theory (disable p6-unsigned-identity)
                  :use ((:instance p6-unsigned-identity (width 64) (x (- value 16)))))))

(defthm p6-set-sp-preserves-memory
  (equal (boymoo-model::a64-memory (proof-world-machine (p6-set-sp address world)))
         (boymoo-model::a64-memory (proof-world-machine world)))
  :hints (("Goal" :in-theory (enable p6-set-sp proof-world-machine boymoo-model::a64-memory))))

(defthm p6-stored-word-memory
  (equal (boymoo-model::a64-memory (proof-world-machine (p6-store-word address value world)))
         (boymoo-model::a64-write-bytes 8 address value
                                       (boymoo-model::a64-memory (proof-world-machine world))))
  :hints (("Goal" :in-theory (enable p6-store-word proof-world-machine
                                     boymoo-model::a64-store boymoo-model::a64-memory))))

(defthm p6-pair-access-at-sp
  (and (equal (proof-instruction-access-p (list :pair nil 31 first second :pre -16) world)
              (and (equal (mod (p6-sp world) 16) 0)
                   (proof-covered-p (boymoo-model::a64-unsigned 64 (- (p6-sp world) 16))
                                    16 :write (proof-world-regions world))))
       (equal (proof-instruction-access-p (list :pair t 31 first second :post 16) world)
              (and (equal (mod (p6-sp world) 16) 0)
                   (proof-covered-p (p6-sp world) 16 :read (proof-world-regions world)))))
  :hints (("Goal" :in-theory (enable proof-instruction-access-p proof-access-p
                                     boymoo-model::a64-read-reg))))

(defthm p6-effect-push-register-pair
  (implies (and (p6-register-file-p world) (natp first) (< first 31) (natp second) (< second 31))
           (let ((address (- (p6-sp world) 16)))
             (equal (proof-instruction-effect (list :pair nil 31 first second :pre -16) world)
                    (p6-set-sp address
                               (p6-store-word (+ address 8) (proof-world-reg second world)
                                              (p6-store-word address (proof-world-reg first world)
                                                             (p6-next world)))))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              boymoo-model::a64-read-reg p6-register-file-p p6-set-sp p6-store-word
                              p6-set-pc proof-world-machine proof-world-pc proof-world-reg
                              proof-reg boymoo-model::a64-sp boymoo-model::a64-memory))))

(local
 (defthm p6-machine-load-with-pc-update
   (equal (boymoo-model::a64-load count address (boymoo-model::a64-set-pc pc machine))
          (boymoo-model::a64-load count address machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-load boymoo-model::a64-memory)))))

(local
 (defthm p6-machine-sp-with-pc-update
   (equal (nth 1 (boymoo-model::a64-set-pc pc machine)) (nth 1 machine))))

(local
 (defthm p6-machine-registers-with-pc-update
   (equal (car (boymoo-model::a64-set-pc pc machine)) (car machine))))

(defthm p6-effect-pop-register-pair
  (implies (and (p6-register-file-p world) (natp first) (< first 31) (natp second) (< second 31))
           (let ((address (p6-sp world)))
             (equal (proof-instruction-effect (list :pair t 31 first second :post 16) world)
                    (p6-set-sp (+ address 16)
                               (p6-set-register second (p6-world-load 8 (+ address 8) world)
                                                (p6-set-register first (p6-world-load 8 address world)
                                                                 (p6-next world)))))))
  :hints (("Goal"
           :in-theory (e/d (proof-instruction-effect proof-execute boymoo-model::a64-execute
                                                   boymoo-model::a64-read-reg p6-register-file-p p6-set-sp
                                                   p6-world-load p6-set-pc p6-set-register proof-world-machine
                                                   proof-world-pc boymoo-model::a64-sp)
                           (boymoo-model::a64-set-pc)))))

(defthm p6-effect-branch-with-link
  (implies (and (p6-register-file-p world) (integerp delta))
           (equal (proof-instruction-effect (list :branch delta t) world)
                  (p6-set-pc (+ (proof-world-pc world) delta)
                             (p6-set-register 30 (+ (proof-world-pc world) 4) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                                    p6-register-file-p p6-set-pc p6-set-register
                                    proof-world-machine proof-world-pc))))

(local
 (defthm p6-assoc-updated-byte
   (equal (cdr (assoc-equal address (put-assoc-equal key value memory)))
          (if (equal address key) value (cdr (assoc-equal address memory))))))

(local
 (defthm p6-byte-at-written-key
   (equal (boymoo-model::a64-byte probe
                                 (put-assoc-equal (boymoo-model::a64-unsigned 64 address)
                                                  (boymoo-model::a64-unsigned 8 value) memory))
          (if (equal (boymoo-model::a64-unsigned 64 probe) (boymoo-model::a64-unsigned 64 address))
              (boymoo-model::a64-unsigned 8 value)
            (boymoo-model::a64-byte probe memory)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte)))))

(local (in-theory (disable boymoo-model::a64-write-bytes put-assoc-equal)))

(local
 (defthm p6-byte-at-in-range-key
   (implies (and (unsigned-byte-p 64 probe) (unsigned-byte-p 64 address))
            (equal (boymoo-model::a64-byte probe
                                           (put-assoc-equal address (boymoo-model::a64-unsigned 8 value) memory))
                   (if (equal probe address) (boymoo-model::a64-unsigned 8 value)
                     (boymoo-model::a64-byte probe memory))))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte)))))

(local
 (defthm p6-write-byte-step
   (and (implies (zp count)
                 (equal (boymoo-model::a64-write-bytes count address value memory) memory))
        (implies (posp count)
                 (equal (boymoo-model::a64-write-bytes count address value memory)
                        (boymoo-model::a64-write-bytes
                         (1- count) (1+ (ifix address)) (ash (ifix value) -8)
                         (put-assoc-equal (boymoo-model::a64-unsigned 64 address)
                                          (boymoo-model::a64-unsigned 8 value) memory)))))
   :hints (("Goal" :expand ((boymoo-model::a64-write-bytes count address value memory))))))

(defthm p6-write-bytes-preserves-outside-span
  (implies (and (proof-span-p address count) (unsigned-byte-p 64 probe)
                (or (< probe address) (<= (+ address count) probe)))
           (equal (boymoo-model::a64-byte probe
                                         (boymoo-model::a64-write-bytes count address value memory))
                  (boymoo-model::a64-byte probe memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory)
                  :in-theory (enable (:induction boymoo-model::a64-write-bytes) proof-span-p))
          ("Subgoal *1/2" :cases ((equal count 1)))))

(defthm p6-read-bytes-after-disjoint-write
  (implies (and (proof-span-p source width) (proof-span-p dest count)
                (proof-disjoint-p source (+ source width) dest (+ dest count)))
           (equal (boymoo-model::a64-read-bytes width source
                                              (boymoo-model::a64-write-bytes count dest value memory))
                  (boymoo-model::a64-read-bytes width source memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes width source memory)
                  :in-theory (enable (:induction boymoo-model::a64-read-bytes) proof-span-p proof-disjoint-p))
          ("Subgoal *1/2" :cases ((equal width 1)))))

(local
 (defthm p6-byte-base-multiplies-negation
   (equal (* 256 (- x)) (- (* 256 x)))
   :hints (("Goal" :use ((:instance distributivity (acl2::x 256) (acl2::y x) (acl2::z (- x))))))))

(local
 (defthm p6-quotient-remainder-byte-split
   (implies (and (integerp value) (posp radix))
            (equal (mod value (* 256 radix))
                   (+ (mod value 256) (* 256 (mod (floor value 256) radix)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable mod)
                   :use ((:instance p6-floor-unique
                                    (x value) (d (* 256 radix)) (q (floor (floor value 256) radix)))
                         (:instance p6-floor-bounds (x value) (d 256))
                         (:instance p6-floor-bounds (x (floor value 256)) (d radix))
                         (:instance distributivity (acl2::x 256) (acl2::y (floor value 256))
                                    (acl2::z (- (* radix (floor (floor value 256) radix))))))))))

(local
 (defthm p6-byte-power-is-positive
   (implies (natp count) (posp (expt 256 count)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (expt 256 count) :in-theory (enable expt)))))

(local
 (defthm p6-write-bytes-at-first-address
   (implies (and (proof-span-p address count) (posp count))
            (equal (boymoo-model::a64-byte address
                                          (boymoo-model::a64-write-bytes count address value memory))
                   (boymoo-model::a64-unsigned 8 value)))
   :hints (("Goal" :in-theory (e/d (proof-span-p)
                                   (p6-write-byte-step p6-write-bytes-preserves-outside-span))
                   :cases ((equal count 1))
                   :use ((:instance p6-write-bytes-preserves-outside-span
                                    (address (1+ address)) (count (1- count)) (probe address)
                                    (value (ash (ifix value) -8))
                                    (memory (put-assoc-equal (boymoo-model::a64-unsigned 64 address)
                                                             (boymoo-model::a64-unsigned 8 value) memory))))
                   :expand ((boymoo-model::a64-write-bytes count address value memory)
                            (boymoo-model::a64-write-bytes 1 address value memory)
                            (:free (v m) (boymoo-model::a64-write-bytes 0 (+ 1 address) v m)))))))

(local
 (defthm p6-read-written-bytes-step
   (implies (and (proof-span-p address count) (posp count) (integerp value))
            (equal (boymoo-model::a64-read-bytes count address
                                               (boymoo-model::a64-write-bytes count address value memory))
                   (+ (boymoo-model::a64-unsigned 8 value)
                      (* 256
                         (boymoo-model::a64-read-bytes
                          (1- count) (1+ address)
                          (boymoo-model::a64-write-bytes
                           (1- count) (1+ address) (ash value -8)
                           (put-assoc-equal address (boymoo-model::a64-unsigned 8 value) memory)))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-span-p) (p6-write-byte-step p6-read-bytes-step))
                   :use (p6-write-bytes-at-first-address p6-write-byte-step
                         (:instance p6-read-bytes-step
                                    (memory (boymoo-model::a64-write-bytes count address value memory))))))))

(defthm p6-read-bytes-after-write-at-same-address
  (implies (and (proof-span-p address count) (integerp value))
           (equal (boymoo-model::a64-read-bytes count address
                                              (boymoo-model::a64-write-bytes count address value memory))
                  (mod value (expt 256 count))))
  :hints (("Goal"
           :induct (boymoo-model::a64-write-bytes count address value memory)
           :in-theory (e/d ((:induction boymoo-model::a64-write-bytes) proof-span-p)
                           (p6-write-byte-step p6-read-bytes-step)))
          ("Subgoal *1/2"
           :cases ((equal count 1))
           :use (p6-read-written-bytes-step
                 (:instance p6-quotient-remainder-byte-split (radix (expt 256 (1- count))))
                 (:instance p6-unsigned-as-mod (width 8) (x value)))
           :expand ((expt 256 count)
                    (:free (v m) (boymoo-model::a64-write-bytes 0 (+ 1 address) v m))))
          ("Subgoal *1/1" :use ((:instance p6-mod-bounds (x value) (d 1))))))

(defthm p6-word-load-after-store-at-same-address
  (implies (and (proof-span-p address 8) (unsigned-byte-p 64 value))
           (equal (p6-world-load 8 address (p6-store-word address value world)) value))
  :hints (("Goal" :in-theory (e/d (p6-world-load boymoo-model::a64-load)
                                  (p6-read-bytes-after-write-at-same-address p6-write-byte-step p6-read-bytes-step))
                  :use ((:instance p6-read-bytes-after-write-at-same-address
                                   (count 8) (memory (boymoo-model::a64-memory (proof-world-machine world))))))))

(defthm p6-load-after-disjoint-word-store
  (implies (and (proof-span-p source width) (proof-span-p dest 8)
                (proof-disjoint-p source (+ source width) dest (+ dest 8)))
           (equal (p6-world-load width source (p6-store-word dest value world))
                  (p6-world-load width source world)))
  :hints (("Goal" :in-theory (e/d (p6-world-load boymoo-model::a64-load)
                                  (p6-write-byte-step p6-read-bytes-step)))))

(defund p6-store-register-pair (first second address world)
  (p6-store-word (+ address 8) (proof-world-reg second world)
                 (p6-store-word address (proof-world-reg first world) world)))

(defthm p6-load-stored-register-pair
  (implies (proof-span-p address 16)
           (let ((saved (p6-store-register-pair first second address world)))
             (and (equal (p6-world-load 8 address saved) (proof-world-reg first world))
                  (equal (p6-world-load 8 (+ 8 address) saved) (proof-world-reg second world)))))
  :hints (("Goal" :in-theory (enable p6-store-register-pair proof-span-p proof-disjoint-p))))

(defthm p6-load-outside-stored-register-pair
  (implies (and (proof-span-p address 16) (proof-span-p source width)
                (proof-disjoint-p source (+ source width) address (+ address 16)))
           (equal (p6-world-load width source (p6-store-register-pair first second address world))
                  (p6-world-load width source world)))
  :hints (("Goal" :in-theory (enable p6-store-register-pair proof-span-p proof-disjoint-p))))

(defthm p6-effect-load-register-pair
  (implies (and (p6-register-file-p world) (natp source) (< source 31)
                (natp first) (< first 31) (natp second) (< second 31))
           (let ((address (proof-world-reg source world)))
             (equal (proof-instruction-effect (list :pair t source first second :offset 0) world)
                    (p6-set-register second (p6-world-load 8 (+ 8 address) world)
                                     (p6-set-register first (p6-world-load 8 address world)
                                                      (p6-next world))))))
  :hints (("Goal"
           :in-theory (e/d (proof-instruction-effect proof-execute boymoo-model::a64-execute
                                                   boymoo-model::a64-read-reg p6-register-file-p p6-world-load
                                                   p6-set-pc p6-set-register proof-world-machine proof-world-pc
                                                   proof-world-reg proof-reg)
                           (boymoo-model::a64-set-pc)))))

(defthm p6-effect-load-word-from-sp
  (implies (and (p6-register-file-p world) (natp dest) (< dest 31))
           (equal (proof-instruction-effect (list :single 1 8 31 dest :offset 0) world)
                  (p6-set-register dest (p6-world-load 8 (p6-sp world) world) (p6-next world))))
  :hints (("Goal" :in-theory (e/d (proof-instruction-effect proof-execute boymoo-model::a64-execute
                                                         boymoo-model::a64-read-reg p6-register-file-p p6-world-load
                                                         p6-set-pc p6-set-register proof-world-machine proof-world-pc
                                                         boymoo-model::a64-sp)
                                 (boymoo-model::a64-set-pc)))))

(defthm p6-access-load-word-from-sp
  (equal (proof-instruction-access-p (list :single 1 8 31 dest :offset 0) world)
         (and (equal (mod (p6-sp world) 16) 0)
              (proof-covered-p (p6-sp world) 8 :read (proof-world-regions world))))
  :hints (("Goal" :in-theory (enable proof-instruction-access-p proof-access-p
                                     boymoo-model::a64-read-reg))))

(defthm p6-access-register-pair
  (implies (and (natp source) (< source 31))
           (equal (proof-instruction-access-p (list :pair load source first second :offset 0) world)
                  (proof-covered-p (proof-world-reg source world) 16 (if load :read :write)
                                   (proof-world-regions world))))
  :hints (("Goal" :in-theory (enable proof-instruction-access-p proof-access-p proof-world-reg proof-reg
                                     boymoo-model::a64-read-reg))))

(defthm p6-effect-store-register-pair
  (implies (and (p6-register-file-p world) (natp dest) (< dest 31)
                (natp first) (< first 31) (natp second) (< second 31))
           (equal (proof-instruction-effect (list :pair nil dest first second :offset 0) world)
                  (p6-store-register-pair first second (proof-world-reg dest world) (p6-next world))))
  :hints (("Goal"
           :in-theory (e/d (proof-instruction-effect proof-execute boymoo-model::a64-execute
                                                   boymoo-model::a64-read-reg p6-register-file-p
                                                   p6-store-register-pair p6-store-word p6-set-pc
                                                   proof-world-machine proof-world-pc proof-world-reg
                                                   proof-reg boymoo-model::a64-memory)
                           (boymoo-model::a64-write-bytes)))))

; Placement and access are checked in the world in which each instruction
; is executed. A store can therefore appear in a checked path.
(defun p6-checked-path-p (sites base cuts world)
  (if (atom sites)
      t
    (let ((instruction (cdar sites)))
      (and (not (proof-world-stop world))
           (equal (proof-world-pc world) (+ base (caar sites)))
           (not (member-equal (proof-world-pc world) cuts))
           (proof-instruction-at-p instruction (proof-world-pc world) world)
           (proof-instruction-access-p instruction world)
           (p6-checked-path-p (cdr sites) base cuts (proof-instruction-effect instruction world))))))

(defthm p6-checked-path-runs
  (implies (p6-checked-path-p sites base cuts world)
           (equal (proof-run (len sites) cuts world)
                  (proof-run 0 cuts (p6-path-end sites world))))
  :rule-classes nil
  :hints (("Goal" :induct (p6-checked-path-p sites base cuts world))
          ("Subgoal *1/1" :expand ((len sites)))))
