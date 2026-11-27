(in-package "BOYMOO-PROOFS")

(include-book "header-calls")
(include-book "fixed-calls")
(include-book "forward-placement")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm collection-forward-word-access
   (implies (not (equal base 31))
            (equal (proof-instruction-access-p
                    (list :single load 8 base target :offset delta) world)
                   (proof-covered-p (boymoo-model::a64-unsigned
                                     64 (+ (proof-world-reg base world) delta))
                                    8 (if (equal load 1) :read :write)
                                    (proof-world-regions world))))
   :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-unsigned)))))

(local
 (defthm collection-forward-data-actions-keep-stop
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

(defthm collection-placed-seen-header-forward-is-ready
  (let* ((source (collection-header-source world))
         (regions (proof-world-regions world))
         (trace (collection-seen-box-trace origin))
         (link (proof-world-reg 30 world)))
    (implies (and (collection-box-forward-entry-p origin world)
                  (logbitp 63 (collection-read-word source world))
                  (not (proof-world-stop world))
                  (collection-trace-placed-p trace world)
                  (not (assoc-equal link trace))
                  (proof-covered-p (+ 64 (proof-world-reg 17 world)) 8 :read regions)
                  (proof-covered-p source 8 :read regions))
             (collection-trace-ready-p trace (list link) world)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (proof-pointer-address)
                                   (collection-covered-address-is-a-span logbitp)))))

(local
 (defthm collection-placement-mark-address-without-wrap
   (let ((address (boymoo-model::a64-unsigned 64 (+ -2 word base))))
     (implies (and (integerp word) (integerp base) (<= 8 address))
              (equal (boymoo-model::a64-unsigned 64 (+ -10 word base)) (- address 8))))
   :hints (("Goal"
            :use ((:instance collection-word-of-wrapped-addend
                             (left -8) (right (+ -2 word base))))
            :in-theory (disable collection-word-of-wrapped-addend)))))

(defthm collection-placed-fixed-forward-is-ready
  (let* ((kind (collection-fixed-forward-kind world))
         (source (proof-pointer-address (proof-world-reg 0 world) (proof-world-reg 28 world)))
         (mark (- source 8))
         (regions (proof-world-regions world))
         (trace (collection-fixed-forward-trace kind origin))
         (link (proof-world-reg 30 world)))
    (implies (and kind (collection-cpu-p world)
                  (proof-span-p origin 224)
                  (equal (proof-world-pc world) origin)
                  (not (proof-world-stop world))
                  (collection-trace-placed-p trace world)
                  (not (assoc-equal link trace))
                  (implies (eq kind :external-above)
                           (proof-covered-p (+ 64 (proof-world-reg 17 world)) 8 :read regions))
                  (implies (collection-external-forward-kind-p kind)
                           (and (proof-regions-p regions)
                                (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                                (proof-covered-p mark 8 :write regions))))
             (collection-trace-ready-p trace (list link) world)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (proof-pointer-address)
                                   (collection-covered-address-is-a-span))
                  :use ((:instance collection-covered-address-is-a-span
                                   (address (- (proof-pointer-address
                                                (proof-world-reg 0 world)
                                                (proof-world-reg 28 world)) 8))
                                   (width 8) (access :write)
                                   (regions (proof-world-regions world)))
                        (:instance collection-covered-address-is-a-span
                                   (address (+ 64 (proof-world-reg 17 world)))
                                   (width 8) (access :read)
                                   (regions (proof-world-regions world)))))))

(defthm collection-placed-box-marker-test-is-ready
  (let* ((source (proof-world-reg 2 world))
         (header (collection-read-word source world))
         (trace (collection-forward-trace :header-marker origin))
         (cut (+ origin (if (logbitp 63 header) 216 140))))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 128))
                  (not (proof-world-stop world))
                  (collection-trace-placed-p trace world)
                  (proof-covered-p source 8 :read (proof-world-regions world)))
             (collection-trace-ready-p trace (list cut) world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable collection-covered-address-is-a-span logbitp))))

