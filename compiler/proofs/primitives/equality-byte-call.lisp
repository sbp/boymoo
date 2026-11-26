(in-package "BOYMOO-PROOFS")

(include-book "equality-views")
(include-book "byte-ranges")
(include-book "machine-stack")

(logic)
(set-verify-guards-eagerness 0)

(defthm p6-header-word-from-type-and-size
  (implies (integerp header)
           (equal (+ (proof-header-type header) (* 256 (proof-header-size header))) header))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable proof-header-type proof-header-size p6-unsigned-as-mod)
                  :use ((:instance p6-mod-decomposition (x header) (d 256))))))

(local
 (defthm p6-string-payload-byte-count
   (equal (len (proof-byte-list count address machine)) (nfix count))
   :hints (("Goal" :induct (proof-byte-list count address machine)
                   :in-theory (enable (:induction proof-byte-list))))))

(local
 (defthm p6-equal-byte-lists-have-equal-lengths
   (implies (equal left right) (equal (len left) (len right)))
   :rule-classes nil))

(defthm p6-string-equality-by-header-and-payload
  (let* ((address-a (proof-pointer-address left base)) (address-b (proof-pointer-address right base))
         (header-a (proof-load-word address-a machine)) (header-b (proof-load-word address-b machine)))
    (implies (and (stringp first) (stringp second)
                  (proof-value-p left first base objects packages machine)
                  (proof-value-p right second base objects packages machine))
             (equal (equal first second)
                    (and (equal header-a header-b)
                         (equal (proof-byte-list (proof-header-size header-a) (+ 8 address-a) machine)
                                (proof-byte-list (proof-header-size header-b) (+ 8 address-b) machine))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-load-word boymoo-model::a64-load) (p6-read-bytes-step proof-header-size
                                                                   p6-load-equality-is-byte-list-equality))
           :use (p6-string-equality-by-payload-bytes
                 (:instance p6-string-view-reads-declared-span (word left) (value first))
                 (:instance p6-string-view-reads-declared-span (word right) (value second))
                 (:instance p6-header-word-from-type-and-size
                            (header (proof-load-word (proof-pointer-address left base) machine)))
                 (:instance p6-header-word-from-type-and-size
                            (header (proof-load-word (proof-pointer-address right base) machine)))
                 (:instance p6-equal-byte-lists-have-equal-lengths
                            (left (proof-byte-list (proof-header-size (proof-load-word (proof-pointer-address left base) machine))
                                                   (+ 8 (proof-pointer-address left base)) machine))
                            (right (proof-byte-list (proof-header-size (proof-load-word (proof-pointer-address right base) machine))
                                                    (+ 8 (proof-pointer-address right base)) machine)))))))

(local
 (defthm p6-low-fifty-six-bits-after-wrap
   (implies (integerp x)
            (equal (boymoo-model::a64-unsigned 56 (boymoo-model::a64-unsigned 64 x))
                   (boymoo-model::a64-unsigned 56 x)))
   :hints (("Goal"
            :in-theory (e/d (p6-unsigned-as-mod) (associativity-of-*))
            :use ((:instance p6-mod-decomposition (d (expt 2 64)))
                  (:instance p6-mod-sum (x (mod x (expt 2 64))) (d (expt 2 56))
                             (q (* 256 (floor x (expt 2 64)))))
                  (:instance associativity-of-* (acl2::x (expt 2 56)) (acl2::y 256)
                             (acl2::z (floor x (expt 2 64)))))))))

(local
 (defthm p6-mask-header-size-is-unsigned
   (implies (integerp value)
            (equal (logand value #x00ffffffffffffff) (boymoo-model::a64-unsigned 56 value)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned boymoo-model::a64-ones)))))

(local
 (defthm p6-header-size-fits-register
   (implies (unsigned-byte-p 64 header) (unsigned-byte-p 64 (proof-header-size header)))
   :hints (("Goal" :in-theory (enable proof-header-size)
                   :use ((:instance p6-floor-bounds (x header) (d 256)))))))

(local
 (defthm p6-header-logical-right-shift
   (implies (unsigned-byte-p 64 header)
            (and (equal (logand (boymoo-model::a64-ror 64 header 8) #x00ffffffffffffff)
                        (proof-header-size header))
                 (equal (boymoo-model::a64-unsigned 56 (boymoo-model::a64-ror 64 header 8))
                        (proof-header-size header))))
   :hints (("Goal"
            :in-theory (e/d (boymoo-model::a64-ror proof-header-size) (p6-unsigned-identity))
            :use ((:instance p6-logior-joins-fields (width 56) (lo (floor header 256)) (hi header))
                  (:instance p6-floor-bounds (x header) (d 256))
                  (:instance p6-unsigned-identity (width 64) (x header))
                  (:instance p6-floor-mod-of-scaled-sum (d (expt 2 56)) (lo (floor header 256)) (n header))
                  (:instance p6-unsigned-as-mod (width 56) (x (+ (floor header 256) (* (expt 2 56) header))))
                  (:instance p6-low-fifty-six-bits-after-wrap (x (+ (floor header 256) (* (expt 2 56) header)))))))))

(local
 (defthm p6-rotated-word-range
   (unsigned-byte-p 64 (boymoo-model::a64-ror 64 word amount))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-ror)))))

(local
 (defthm p6-mask-of-a-rotated-word
   (equal (logand (boymoo-model::a64-ror 64 word amount) #xffffffffffffffff)
          (boymoo-model::a64-ror 64 word amount))
   :hints (("Goal"
            :in-theory (e/d (boymoo-model::a64-ones boymoo-model::a64-unsigned)
                            (boymoo-model::a64-ror p6-unsigned-identity))
            :use ((:instance p6-unsigned-identity
                             (width 64) (x (boymoo-model::a64-ror 64 word amount))))))))

(local
 (defthm p6-logior-zero-with-integer
   (implies (integerp value) (equal (logior 0 value) value))
   :hints (("Goal" :use ((:instance p6-logior-joins-fields (width 0) (lo 0) (hi value)))))))

(local
 (defthm p6-effect-shift-header-size
   (implies (p6-register-file-p world)
            (equal (proof-instruction-effect
                    '(:bitfield 2 64 2 2 8 63 #xffffffffffffffff #x00ffffffffffffff) world)
                   (p6-set-register 2 (proof-header-size (proof-world-reg 2 world)) (p6-next world))))
   :hints (("Goal"
            :in-theory (e/d (proof-instruction-effect proof-execute boymoo-model::a64-execute
                                                     boymoo-model::a64-read-reg p6-register-file-p p6-set-register
                                                     p6-set-pc proof-world-machine proof-world-pc proof-world-reg proof-reg)
                            (boymoo-model::a64-ror proof-header-size))))))

(defconst *p6-equal-byte-call-sites* (p6-sites "rt:equal-byte-span" 2))

(defthm p6-equal-byte-call-passes-declared-length
  (let* ((target (+ base (p6-runtime-offset "rt:equal-bytes")))
         (link (+ base (p6-runtime-offset "rt:equal-byte-span") 8))
         (after (p6-path-end *p6-equal-byte-call-sites* world)))
    (implies (and (p6-register-file-p world) (not (proof-world-stop world))
                  (equal (proof-world-pc world) (+ base (caar *p6-equal-byte-call-sites*)))
                  (unsigned-byte-p 64 target) (unsigned-byte-p 64 link)
                  (p6-checked-path-p *p6-equal-byte-call-sites* base nil world))
             (and (proof-segment-p 2 nil world :limit after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 2 after) (proof-header-size (proof-world-reg 2 world)))
                  (proof-register-frame-p 30 '(2 30) world after)
                  (equal (p6-sp after) (p6-sp world))
                  (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                         (boymoo-model::a64-nzcv (proof-world-machine world)))
                  (p6-same-mapped-memory-p world after)
                  (equal (cdr world) (cdr after)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-segment-p p6-path-end p6-same-mapped-memory-p)
                           (p6-checked-path-p proof-header-size p6-run-step proof-run-reached-without-cuts))
           :use ((:instance p6-checked-path-runs (sites *p6-equal-byte-call-sites*) (cuts nil))))))

(defund p6-equal-byte-result-sites (result)
  (if (equal result 0)
      (nthcdr 2 (p6-sites "rt:equal-byte-span" 3))
    (nthcdr 2 (p6-sites "rt:equal-byte-span" 4))))

(defund p6-equal-byte-result-target (result base)
  (+ base (p6-runtime-offset (if (equal result 0) "rt:equal-no" "rt:equal-next"))))

(defthm p6-equal-byte-result-branches
  (let* ((result (proof-world-reg 0 world))
         (sites (p6-equal-byte-result-sites result))
         (target (p6-equal-byte-result-target result base))
         (cuts (list return-address))
         (after (p6-path-end sites world)))
    (implies (and (p6-register-file-p world) (not (proof-world-stop world)) (natp base)
                  (equal (proof-world-pc world) (+ base (caar sites)))
                  (p6-site-addresses-p sites base return-address)
                  (unsigned-byte-p 64 target) (not (equal target return-address))
                  (p6-checked-path-p sites base cuts world))
             (and (proof-segment-p (len sites) cuts world :limit after)
                  (equal (proof-world-pc after) target)
                  (proof-register-frame-p 30 nil world after)
                  (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                         (boymoo-model::a64-nzcv (proof-world-machine world)))
                  (equal (p6-sp after) (p6-sp world))
                  (p6-same-mapped-memory-p world after) (equal (cdr world) (cdr after)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-segment-p p6-path-end p6-equal-byte-result-sites p6-equal-byte-result-target
                                            p6-same-mapped-memory-p)
                           (p6-checked-path-p p6-run-step (:definition p6-runtime-offset)))
           :use ((:instance p6-checked-path-runs (sites (p6-equal-byte-result-sites (proof-world-reg 0 world)))
                            (cuts (list return-address)))))))
