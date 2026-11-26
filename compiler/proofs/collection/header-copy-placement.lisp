(in-package "BOYMOO-PROOFS")

(include-book "header-placement")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm collection-header-copy-word-access
   (implies (not (equal base 31))
            (equal (proof-instruction-access-p
                    (list :single load 8 base target :offset delta) world)
                   (proof-covered-p (boymoo-model::a64-unsigned
                                     64 (+ (proof-world-reg base world) delta))
                                    8 (if (equal load 1) :read :write)
                                    (proof-world-regions world))))
   :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-unsigned)))))

(local
 (defthm collection-header-copy-actions-keep-stop
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
                     collection-subtract-flags proof-word-tag proof-header-size
                     boymoo-model::a64-unsigned boymoo-model::a64-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand)
                     (:definition acl2::binary-logior) logbitp)))

(local
 (defthm collection-header-copy-count-is-natural
   (natp (collection-header-payload-words header))
   :rule-classes :type-prescription))

(local
 (defthm collection-header-copy-span-covers-its-header-and-payload
   (implies (and (natp count)
                 (unsigned-byte-p 64 (+ base 8 (* 8 count)))
                 (proof-covered-p base (+ 8 (* 8 count)) access regions))
            (and (proof-covered-p base 8 access regions)
                 (proof-covered-p (+ 8 base) (* 8 count) access regions)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-covered-address-is-a-span
                             (address base) (width (+ 8 (* 8 count))))
                  (:instance collection-covered-subspan
                             (address base) (width 8) (extent (+ 8 (* 8 count))))
                  (:instance collection-covered-subspan
                             (address (+ 8 base)) (width (* 8 count))
                             (extent (+ 8 (* 8 count)))))
            :in-theory (disable collection-covered-address-is-a-span)))))

(local
 (defun collection-start-header-payload-trace (count origin)
   (append (collection-forward-trace :header-count origin)
           (if (zp count) nil (collection-forward-trace :header-payload origin)))))

(local
 (defun collection-fresh-header-setup-trace (count origin)
   (append (collection-forward-trace :copy-header origin)
           (collection-start-header-payload-trace count origin))))

(local
 (defthm collection-placed-header-store-is-ready
   (let* ((trace (collection-forward-trace :copy-header origin))
          (regions (proof-world-regions world)))
     (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                   (equal (proof-world-pc world) (+ origin 140))
                   (not (proof-world-stop world))
                   (proof-regions-p regions)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-covered-p (proof-world-reg 2 world) 8 :write regions)
                   (proof-covered-p (proof-world-reg 20 world) 8 :write regions)
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list (+ origin 180)) world)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable collection-covered-address-is-a-span)))))

(local
 (defthm collection-placed-header-payload-start-is-ready
   (let* ((count (proof-world-reg 3 world))
          (trace (collection-start-header-payload-trace count origin)))
     (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                   (equal (proof-world-pc world) (+ origin 180))
                   (not (proof-world-stop world))
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list (+ origin (if (zp count) 212 188))) world)))
   :rule-classes nil
   :hints (("Goal" :cases ((equal (proof-world-reg 3 world) 0))))))

(local
 (defthm collection-header-store-keeps-placement-and-cpu
   (let* ((regions (proof-world-regions world))
          (next (collection-trace-effect (collection-forward-trace :copy-header origin) world)))
     (implies (and (collection-cpu-p world)
                   (proof-regions-p regions)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-covered-p (proof-world-reg 2 world) 8 :write regions)
                   (proof-covered-p (proof-world-reg 20 world) 8 :write regions))
              (and (collection-cpu-p next)
                   (equal (proof-world-stop next) (proof-world-stop world))
                   (equal (collection-trace-placed-p trace next)
                          (collection-trace-placed-p trace world)))))
   :hints (("Goal" :induct (collection-trace-placed-p trace world)
                   :in-theory (disable collection-covered-address-is-a-span)))))

(local
 (defthm collection-header-store-excludes-payload-start-cutpoint
   (not (intersectp-equal (strip-cars (collection-forward-trace :copy-header origin))
                          (list (+ origin (if (zp count) 212 188)))))))

(local
 (defthm collection-header-copy-placement-splits-across-append
   (equal (collection-trace-placed-p (append first second) world)
          (and (collection-trace-placed-p first world) (collection-trace-placed-p second world)))
   :hints (("Goal" :induct (append first second)))))

(local
 (defthm collection-placed-fresh-header-setup-is-ready
   (let* ((count (collection-header-payload-words (proof-world-reg 3 world)))
          (trace (collection-fresh-header-setup-trace count origin))
          (regions (proof-world-regions world)))
     (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                   (equal (proof-world-pc world) (+ origin 140))
                   (not (proof-world-stop world))
                   (proof-regions-p regions)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-covered-p (proof-world-reg 2 world) 8 :write regions)
                   (proof-covered-p (proof-world-reg 20 world) 8 :write regions)
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list (+ origin (if (zp count) 212 188))) world)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-placed-header-store-is-ready)
                  (:instance collection-forward-installs-header-marker-and-copies-header)
                  (:instance collection-placed-header-payload-start-is-ready
                             (world (collection-trace-effect (collection-forward-trace :copy-header origin) world)))
                  (:instance collection-header-store-excludes-payload-start-cutpoint
                             (count (collection-header-payload-words (proof-world-reg 3 world))))
                  (:instance collection-ready-trace-of-append
                             (first (collection-forward-trace :copy-header origin))
                             (second (collection-start-header-payload-trace
                                      (collection-header-payload-words (proof-world-reg 3 world)) origin))
                             (first-cut (list (+ origin 180)))
                             (cuts (list (+ origin (if (zp (collection-header-payload-words (proof-world-reg 3 world)))
                                                            212 188))))))
            :in-theory (e/d (proof-header-size)
                             (collection-forward-trace collection-start-header-payload-trace
                              collection-trace-effect collection-trace-ready-p collection-trace-placed-p
                              collection-forward-installs-header-marker-and-copies-header
                              collection-ready-trace-of-append
                              collection-header-store-excludes-payload-start-cutpoint))))))

(local
 (defthm collection-header-marker-prefix-keeps-placement-and-metadata
   (let ((next (collection-trace-effect (collection-box-forward-prefix origin) world)))
     (implies (collection-cpu-p world)
              (and (equal (proof-world-regions next) (proof-world-regions world))
                   (equal (proof-world-stop next) (proof-world-stop world))
                   (equal (collection-trace-placed-p trace next)
                          (collection-trace-placed-p trace world)))))
   :hints (("Goal" :induct (collection-trace-placed-p trace world)
                   :in-theory (disable collection-trace-effect-of-append)))))

(local
 (defthm collection-fresh-box-prefix-splits-at-marker
   (equal (collection-fresh-box-prefix count origin)
          (append (collection-box-forward-prefix origin)
                  (collection-fresh-header-setup-trace count origin)))))

(local
 (defthm collection-header-copy-single-cut-intersection
   (iff (intersectp-equal addresses (list cut)) (member-equal cut addresses))
   :hints (("Goal" :induct (len addresses)))))

(local
 (defthm collection-box-forward-prefix-addresses
   (equal (strip-cars (collection-box-forward-prefix origin))
          (list (fix origin) (+ origin 4) (+ origin 8) (+ origin 12) (+ origin 16)
                (+ origin 20) (+ origin 24) (+ origin 80) (+ origin 84) (+ origin 88)
                (+ origin 92) (+ origin 96) (+ origin 128) (+ origin 132) (+ origin 136)))))

(local
 (defthm collection-fresh-header-marker-prefix-excludes-preparation-end
   (implies (integerp origin)
            (not (intersectp-equal (strip-cars (collection-box-forward-prefix origin))
                                   (list (+ origin (if (zp count) 212 188))))))
   :hints (("Goal" :cases ((zp count))
                   :in-theory (disable collection-box-forward-prefix)))))

(local
 (defthm collection-placed-fresh-header-prefix-is-ready
   (let* ((source (collection-header-source world))
          (header (collection-read-word source world))
          (count (collection-header-payload-words header))
          (destination (proof-world-reg 20 world))
          (regions (proof-world-regions world))
          (prefix (collection-fresh-box-prefix count origin)))
     (implies (and (collection-box-forward-entry-p origin world)
                   (not (logbitp 63 header))
                   (not (proof-world-stop world))
                   (collection-trace-ready-p (collection-box-forward-prefix origin)
                                             (list (+ origin 140)) world)
                   (collection-trace-placed-p prefix world)
                   (proof-regions-p regions)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-covered-p source 8 :write regions)
                   (proof-covered-p destination 8 :write regions))
              (collection-trace-ready-p prefix (list (+ origin (if (zp count) 212 188))) world)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-box-prefix-reads-header-and-selects-copy-or-reuse (register 20))
                  (:instance collection-fresh-header-marker-prefix-excludes-preparation-end
                             (count (collection-header-payload-words
                                     (collection-read-word (collection-header-source world) world))))
                  (:instance collection-placed-fresh-header-setup-is-ready
                             (world (collection-trace-effect
                                     (collection-box-forward-prefix origin) world)))
                  (:instance collection-ready-trace-of-append
                             (first (collection-box-forward-prefix origin))
                             (second (collection-fresh-header-setup-trace
                                      (collection-header-payload-words
                                       (collection-read-word (collection-header-source world) world)) origin))
                             (first-cut (list (+ origin 140)))
                             (cuts (list (+ origin (if (zp (collection-header-payload-words
                                                                 (collection-read-word (collection-header-source world) world)))
                                                            212 188))))))
            :in-theory (disable collection-box-prefix-reads-header-and-selects-copy-or-reuse
                                collection-ready-trace-of-append collection-fresh-box-prefix
                                collection-box-forward-prefix collection-forward-trace
                                collection-fresh-header-marker-prefix-excludes-preparation-end
                                collection-fresh-header-setup-trace collection-header-payload-words
                                collection-trace-effect collection-trace-ready-p
                                collection-trace-placed-p)))))

(local (in-theory (disable collection-fresh-box-prefix-splits-at-marker)))

(local
 (defthm collection-fresh-header-prefix-keeps-metadata
   (let* ((count (collection-header-payload-words
                  (collection-read-word (collection-header-source world) world)))
          (next (collection-trace-effect (collection-fresh-box-prefix count origin) world)))
     (implies (and (collection-box-forward-entry-p origin world)
                   (not (logbitp 63 (collection-read-word (collection-header-source world) world)))
                   (alistp (boymoo-model::a64-memory (proof-world-machine world))))
              (and (equal (proof-world-regions next) (proof-world-regions world))
                   (equal (proof-world-stop next) (proof-world-stop world))
                   (alistp (boymoo-model::a64-memory (proof-world-machine next))))))
   :hints (("Goal" :in-theory (disable collection-trace-effect-of-append
                                       collection-header-source)))))

(local
 (defthm collection-fresh-header-prefix-keeps-instruction-placement
   (let* ((source (collection-header-source world))
          (header (collection-read-word source world))
          (count (collection-header-payload-words header))
          (next (collection-trace-effect (collection-fresh-box-prefix count origin) world)))
     (implies (and (collection-box-forward-entry-p origin world)
                   (not (logbitp 63 header))
                   (proof-regions-p (proof-world-regions world))
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-covered-p source 8 :write (proof-world-regions world))
                   (proof-covered-p (proof-world-reg 20 world) 8 :write (proof-world-regions world)))
              (equal (proof-instruction-at-p instruction pc next)
                     (proof-instruction-at-p instruction pc world))))
   :hints (("Goal" :in-theory (e/d (proof-pointer-address)
                                   (collection-trace-effect-of-append
                                    collection-covered-address-is-a-span))))))

(local
 (in-theory (disable collection-fresh-box-prefix collection-fresh-box-trace
                     collection-box-forward-entry-p collection-header-source
                     collection-header-payload-words collection-copy-word-effect
                     collection-trace-effect collection-trace-ready-p)))

(local
 (defthm collection-fresh-header-prefix-keeps-trace-placement
   (let* ((source (collection-header-source world))
          (header (collection-read-word source world))
          (count (collection-header-payload-words header))
          (next (collection-trace-effect (collection-fresh-box-prefix count origin) world)))
     (implies (and (collection-box-forward-entry-p origin world)
                   (not (logbitp 63 header))
                   (proof-regions-p (proof-world-regions world))
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-covered-p source 8 :write (proof-world-regions world))
                   (proof-covered-p (proof-world-reg 20 world) 8 :write (proof-world-regions world)))
              (equal (collection-trace-placed-p trace next)
                     (collection-trace-placed-p trace world))))
   :hints (("Goal" :induct (collection-trace-placed-p trace world)))))

(defun collection-fresh-header-readiness-input-p (origin world)
  (let* ((source (collection-header-source world))
         (destination (proof-world-reg 20 world))
         (header (collection-read-word source world))
         (count (collection-header-payload-words header))
         (bytes (+ 8 (* 8 count)))
         (regions (proof-world-regions world))
         (link (proof-world-reg 30 world)))
    (and (collection-box-forward-entry-p origin world)
         (not (logbitp 63 header))
         (not (proof-world-stop world))
         (collection-trace-ready-p (collection-box-forward-prefix origin) (list (+ origin 140)) world)
         (proof-regions-p regions)
         (alistp (boymoo-model::a64-memory (proof-world-machine world)))
         (proof-covered-p source bytes :write regions)
         (proof-covered-p destination bytes :write regions)
         (unsigned-byte-p 64 (+ source bytes))
         (unsigned-byte-p 64 (+ destination bytes))
         (collection-trace-placed-p (collection-fresh-box-prefix count origin) world)
         (collection-trace-placed-p (collection-forward-trace :copy-word origin) world)
         (collection-trace-placed-p (collection-forward-trace :return origin) world)
         (or (< link origin) (<= (+ origin 224) link)))))

(local
 (defthm collection-fresh-header-readiness-input-splits-object-spans
   (let* ((source (collection-header-source world))
          (count (collection-header-payload-words (collection-read-word source world)))
          (destination (proof-world-reg 20 world))
          (regions (proof-world-regions world)))
     (implies (collection-fresh-header-readiness-input-p origin world)
              (and (proof-covered-p source 8 :write regions)
                   (proof-covered-p destination 8 :write regions)
                   (proof-covered-p (if (zp count) source (+ 8 source)) (* 8 count) :read regions)
                   (proof-covered-p (+ 8 destination) (* 8 count) :write regions))))
   :hints (("Goal"
            :use ((:instance collection-header-copy-span-covers-its-header-and-payload
                             (base (collection-header-source world))
                             (count (collection-header-payload-words (collection-read-word (collection-header-source world) world)))
                             (access :write) (regions (proof-world-regions world)))
                  (:instance collection-header-copy-span-covers-its-header-and-payload
                             (base (proof-world-reg 20 world))
                             (count (collection-header-payload-words (collection-read-word (collection-header-source world) world)))
                             (access :write) (regions (proof-world-regions world)))
                  (:instance collection-covered-subspan
                             (base (collection-header-source world))
                             (address (collection-header-source world))
                             (extent 8) (width 0) (access :read)
                             (regions (proof-world-regions world)))
                  (:instance collection-covered-address-is-a-span
                             (address (collection-header-source world)) (width 8) (access :write)
                             (regions (proof-world-regions world))))
            :in-theory (disable collection-forward-trace collection-trace-placed-p
                                collection-covered-address-is-a-span)))))

(local
 (defthm collection-fresh-header-preparation-is-ready
   (let* ((count (collection-header-payload-words
                  (collection-read-word (collection-header-source world) world)))
          (prefix (collection-fresh-box-prefix count origin))
          (next (collection-trace-effect prefix world)))
     (implies (collection-fresh-header-readiness-input-p origin world)
              (and (collection-trace-ready-p prefix (list (+ origin (if (zp count) 212 188))) world)
                   (collection-placed-payload-entry-p count origin next)
                   (equal (proof-world-reg 30 next) (proof-world-reg 30 world))
                   (collection-trace-placed-p (collection-forward-trace :return origin) next))))
   :hints (("Goal"
            :use ((:instance collection-fresh-header-readiness-input-splits-object-spans)
                  (:instance collection-placed-fresh-header-prefix-is-ready)
                  (:instance collection-prepared-header-admits-payload-copy)
                  (:instance collection-fresh-header-prefix-keeps-metadata)
                  (:instance collection-fresh-header-prefix-keeps-trace-placement
                             (trace (collection-forward-trace :copy-word origin)))
                  (:instance collection-fresh-header-prefix-keeps-trace-placement
                             (trace (collection-forward-trace :return origin)))
                  (:instance collection-fresh-header-prepares-copy-and-installs-marker (register 30)))
            :in-theory (e/d (collection-box-forward-entry-p)
                             (collection-forward-trace collection-trace-placed-p
                              collection-fresh-header-readiness-input-splits-object-spans
                              collection-fresh-header-prefix-keeps-metadata
                              collection-fresh-header-prefix-keeps-trace-placement
                              collection-fresh-header-prepares-copy-and-installs-marker
                              collection-prepared-header-admits-payload-copy))))))

(local
 (defthm collection-header-copy-addresses-of-appended-trace
   (equal (strip-cars (append first second)) (append (strip-cars first) (strip-cars second)))
   :hints (("Goal" :induct (append first second)))))

(local
 (defthm collection-header-copy-addresses-outside-payload
   (implies (and (integerp origin) (integerp link)
                 (or (< link origin) (<= (+ origin 224) link)))
            (not (member-equal link (strip-cars (collection-copy-payload-trace count origin)))))
   :hints (("Goal"
            :induct (collection-copy-payload-trace count origin)))))

(local
 (defthm collection-header-copy-addresses-outside-preparation
   (implies (and (integerp origin) (integerp link)
                 (or (< link origin) (<= (+ origin 224) link)))
            (not (member-equal link (strip-cars (collection-fresh-box-prefix count origin)))))
   :hints (("Goal" :cases ((zp count) (< link origin))
                   :in-theory (e/d (collection-fresh-box-prefix)
                                    (collection-box-forward-prefix))))))

(local
 (defthm collection-placed-header-return-is-ready
   (implies (and (collection-cpu-p world)
                 (equal (proof-world-pc world) (+ origin 212))
                 (not (proof-world-stop world))
                 (collection-trace-placed-p (collection-forward-trace :return origin) world)
                 (not (equal (proof-world-reg 30 world) (+ origin 212))))
            (collection-trace-ready-p (collection-forward-trace :return origin)
                                      (list (proof-world-reg 30 world)) world))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable collection-trace-ready-p)))))

(local
 (defthm collection-admitted-header-payload-keeps-cpu
   (implies (collection-payload-span-p count world)
            (collection-cpu-p (collection-copy-payload-effect count world)))
   :hints (("Goal" :induct (collection-copy-payload-effect count world)
                   :in-theory (disable collection-payload-span-p))
           ("Subgoal *1/1" :in-theory (enable collection-payload-span-p)))))

(local
 (defthm collection-empty-header-copy-trace-keeps-world
   (equal (collection-trace-effect nil world) world)
   :hints (("Goal" :in-theory (enable collection-trace-effect)))))

(local
 (defthm collection-placed-payload-reaches-return-register-state
   (let ((next (collection-copy-payload-effect count world)))
     (implies (collection-placed-payload-entry-p count origin world)
              (and (integerp origin)
                   (equal (collection-trace-effect (collection-copy-payload-trace count origin) world) next)
                   (collection-cpu-p next)
                   (equal (proof-world-pc next) (+ origin 212))
                   (equal (proof-world-reg 30 next) (proof-world-reg 30 world)))))
   :hints (("Goal"
            :cases ((zp count))
            :in-theory (enable collection-payload-span-p)
            :do-not-induct t))))

(local
 (defthm collection-ready-header-copy-ends-running
   (implies (collection-trace-ready-p trace cuts world)
            (not (proof-world-stop (collection-trace-effect trace world))))
   :hints (("Goal" :induct (collection-trace-ready-p trace cuts world)
                   :in-theory (enable collection-trace-ready-p collection-trace-effect)))))

(local
 (defthm collection-placed-header-payload-and-return-is-ready
   (let* ((payload (collection-copy-payload-trace count origin))
          (return (collection-forward-trace :return origin))
          (link (proof-world-reg 30 world))
          (after (collection-trace-effect payload world)))
     (implies (and (collection-placed-payload-entry-p count origin world)
                   (collection-trace-placed-p return world)
                   (or (< link origin) (<= (+ origin 224) link)))
              (and (equal (proof-world-reg 30 after) link)
                   (collection-trace-ready-p (append payload return) (list link) world))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-placed-payload-copy-is-ready)
                  (:instance collection-placed-payload-reaches-return-register-state)
                  (:instance collection-placed-payload-copy-preserves-placement
                             (trace (collection-forward-trace :return origin)))
                  (:instance collection-placed-header-return-is-ready
                             (world (collection-copy-payload-effect count world)))
                  (:instance collection-ready-header-copy-ends-running
                             (trace (collection-copy-payload-trace count origin))
                             (cuts (list (+ origin 212))))
                  (:instance collection-ready-trace-of-append
                             (first (collection-copy-payload-trace count origin))
                             (second (collection-forward-trace :return origin))
                             (first-cut (list (+ origin 212))) (cuts (list (proof-world-reg 30 world)))))
            :in-theory (disable collection-forward-trace collection-trace-placed-p
                                collection-copy-payload-trace collection-copy-payload-effect
                                collection-placed-payload-entry-p
                                collection-placed-payload-reaches-return-register-state
                                collection-ready-header-copy-ends-running
                                collection-ready-trace-of-append collection-ready-trace-gives-prefix)
            :do-not-induct t))))

(defthm collection-placed-fresh-header-forward-is-ready
  (let* ((count (collection-header-payload-words
                 (collection-read-word (collection-header-source world) world)))
         (trace (collection-fresh-box-trace count origin)))
    (implies (collection-fresh-header-readiness-input-p origin world)
             (collection-trace-ready-p trace (list (proof-world-reg 30 world)) world)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-fresh-header-preparation-is-ready)
                 (:instance collection-placed-header-payload-and-return-is-ready
                            (count (collection-header-payload-words
                                    (collection-read-word (collection-header-source world) world)))
                            (world (collection-trace-effect
                                    (collection-fresh-box-prefix
                                     (collection-header-payload-words
                                      (collection-read-word (collection-header-source world) world)) origin)
                                    world)))
                 (:instance collection-ready-trace-of-append
                            (first (collection-fresh-box-prefix
                                    (collection-header-payload-words
                                     (collection-read-word (collection-header-source world) world)) origin))
                            (second (append (collection-copy-payload-trace
                                             (collection-header-payload-words
                                              (collection-read-word (collection-header-source world) world)) origin)
                                            (collection-forward-trace :return origin)))
                            (first-cut (list (+ origin (if (zp (collection-header-payload-words
                                                                (collection-read-word (collection-header-source world) world)))
                                                           212 188))))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (e/d (collection-fresh-box-trace collection-box-forward-entry-p)
                            (collection-copy-payload-trace collection-forward-trace collection-trace-placed-p
                             collection-fresh-header-preparation-is-ready collection-ready-trace-of-append)))))

(local
 (defun collection-box-range-trace (origin)
   (append (collection-forward-trace :header-region origin)
           (collection-forward-trace :high-header-region origin))))

(local
 (defun collection-box-navigation-trace (origin)
   (append (collection-forward-trace :header-address origin)
           (collection-box-range-trace origin))))

(local
 (defthm collection-placed-header-address-is-ready
   (let ((trace (collection-forward-trace :header-address origin)))
     (implies (and (collection-box-forward-entry-p origin world)
                   (not (proof-world-stop world))
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list (+ origin 80)) world)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable collection-box-forward-entry-p
                               collection-trace-ready-p collection-trace-placed-p)))))

(local
 (defthm collection-placed-box-range-is-ready
   (let* ((trace (collection-box-range-trace origin))
          (metadata (+ 64 (proof-world-reg 17 world)))
          (source (proof-world-reg 2 world)))
     (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                   (equal (proof-world-pc world) (+ origin 80))
                   (not (proof-world-stop world))
                   (<= (proof-world-reg 19 world) source)
                   (< source (collection-read-word metadata world))
                   (proof-span-p metadata 8)
                   (proof-covered-p metadata 8 :read (proof-world-regions world))
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list (+ origin 128)) world)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (collection-trace-ready-p collection-trace-placed-p)
                             (collection-covered-address-is-a-span))))))

(local
 (defthm collection-decoded-header-address-prepares-range-test
   (let ((next (collection-trace-effect (collection-forward-trace :header-address origin) world)))
     (implies (collection-box-forward-entry-p origin world)
              (and (collection-cpu-p next)
                   (equal (proof-world-pc next) (+ origin 80))
                   (equal (proof-world-reg 2 next) (collection-header-source world))
                   (equal (proof-world-reg 17 next) (proof-world-reg 17 world))
                   (equal (proof-world-reg 19 next) (proof-world-reg 19 world))
                   (equal (collection-read-word address next) (collection-read-word address world))
                   (equal (proof-world-stop next) (proof-world-stop world))
                   (equal (proof-world-regions next) (proof-world-regions world))
                   (equal (collection-trace-placed-p trace next)
                          (collection-trace-placed-p trace world)))))
   :hints (("Goal" :induct (collection-trace-placed-p trace world)
                   :in-theory (enable collection-box-forward-entry-p collection-header-source
                                      proof-pointer-address collection-trace-effect)))))

(local
 (defthm collection-header-address-trace-excludes-box-marker
   (implies (integerp origin)
            (not (intersectp-equal (strip-cars (collection-forward-trace :header-address origin))
                                   (list (+ origin 128)))))))

(local
 (defthm collection-placed-box-navigation-is-ready
   (let ((trace (collection-box-navigation-trace origin)))
     (implies (and (collection-box-forward-entry-p origin world)
                   (not (proof-world-stop world))
                   (proof-covered-p (+ 64 (proof-world-reg 17 world)) 8 :read (proof-world-regions world))
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list (+ origin 128)) world)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-placed-header-address-is-ready)
                  (:instance collection-placed-box-range-is-ready
                             (world (collection-trace-effect (collection-forward-trace :header-address origin)
                                                             world)))
                  (:instance collection-header-address-trace-excludes-box-marker)
                  (:instance collection-ready-trace-of-append
                             (first (collection-forward-trace :header-address origin))
                             (second (collection-box-range-trace origin))
                             (first-cut (list (+ origin 80))) (cuts (list (+ origin 128)))))
            :in-theory (e/d (collection-box-forward-entry-p)
                             (collection-forward-trace collection-box-range-trace
                              collection-trace-placed-p collection-ready-trace-of-append
                              collection-header-address-trace-excludes-box-marker))))))

(local
 (defthm collection-box-navigation-keeps-source-and-marker-access
   (let ((next (collection-trace-effect (collection-box-navigation-trace origin) world)))
     (implies (collection-box-forward-entry-p origin world)
              (and (collection-cpu-p next)
                   (equal (proof-world-pc next) (+ origin 128))
                   (equal (proof-world-reg 2 next) (collection-header-source world))
                   (equal (collection-read-word address next) (collection-read-word address world))
                   (equal (proof-world-stop next) (proof-world-stop world))
                   (equal (proof-world-regions next) (proof-world-regions world))
                   (equal (collection-trace-placed-p trace next)
                          (collection-trace-placed-p trace world)))))
   :hints (("Goal" :induct (collection-trace-placed-p trace world)
                   :in-theory (enable collection-box-forward-entry-p collection-header-source
                                      proof-pointer-address collection-trace-effect)))))

(local
 (defthm collection-box-navigation-addresses
   (equal (strip-cars (collection-box-navigation-trace origin))
          (list (fix origin) (+ origin 4) (+ origin 8) (+ origin 12) (+ origin 16)
                (+ origin 20) (+ origin 24) (+ origin 80) (+ origin 84) (+ origin 88)
                (+ origin 92) (+ origin 96)))))

(local
 (defthm collection-box-navigation-excludes-marker-result
   (implies (integerp origin)
            (not (intersectp-equal (strip-cars (collection-box-navigation-trace origin))
                                   (list (+ origin (if marked 216 140))))))
   :hints (("Goal" :cases (marked)
                   :in-theory (disable collection-box-navigation-trace)))))

(local
 (defthm collection-box-prefix-ends-with-marker-test
   (equal (collection-box-forward-prefix origin)
          (append (collection-box-navigation-trace origin)
                  (collection-forward-trace :header-marker origin)))))

(defthm collection-placed-header-forward-prefix-is-ready
  (let* ((source (collection-header-source world))
         (header (collection-read-word source world))
         (regions (proof-world-regions world))
         (trace (collection-box-forward-prefix origin))
         (cut (+ origin (if (logbitp 63 header) 216 140))))
    (implies (and (collection-box-forward-entry-p origin world)
                  (not (proof-world-stop world))
                  (collection-trace-placed-p trace world)
                  (proof-covered-p (+ 64 (proof-world-reg 17 world)) 8 :read regions)
                  (proof-covered-p source 8 :read regions))
             (collection-trace-ready-p trace (list cut) world)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-placed-box-navigation-is-ready)
                 (:instance collection-box-navigation-excludes-marker-result
                            (marked (logbitp 63 (collection-read-word (collection-header-source world) world))))
                 (:instance collection-placed-box-marker-test-is-ready
                            (world (collection-trace-effect (collection-box-navigation-trace origin) world)))
                 (:instance collection-ready-trace-of-append
                            (first (collection-box-navigation-trace origin))
                            (second (collection-forward-trace :header-marker origin))
                            (first-cut (list (+ origin 128)))
                            (cuts (list (+ origin (if (logbitp 63 (collection-read-word
                                                                  (collection-header-source world) world)) 216 140))))))
           :in-theory (e/d (collection-box-forward-entry-p)
                            (collection-box-navigation-trace collection-box-forward-prefix
                             collection-trace-placed-p collection-forward-trace
                             collection-box-navigation-excludes-marker-result
                             collection-ready-trace-of-append))
           :do-not-induct t)))
