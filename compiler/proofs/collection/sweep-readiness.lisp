(in-package "BOYMOO-PROOFS")

(include-book "sweep-contents")
(include-book "forward-placement")
(include-book "unmap-placement")
(local (include-book "std/lists/update-nth" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

; A loop round starts at the address at which it finishes. The first
; instruction executes before the check for a return to that address.
(defun collection-loop-round-ready-p (trace world)
  (and (consp trace)
       (not (proof-world-stop world))
       (equal (proof-world-pc world) (caar trace))
       (proof-instruction-at-p (cdar trace) (caar trace) world)
       (proof-instruction-access-p (cdar trace) world)
       (collection-trace-ready-p
        (cdr trace) (list (caar trace))
        (proof-instruction-effect (cdar trace) world))))

(defthm collection-ready-loop-round-precedes-ready-suffix
  (implies (and (collection-loop-round-ready-p round world)
                (collection-trace-ready-p suffix cuts (collection-trace-effect round world))
                (not (intersectp-equal (strip-cars round) cuts)))
           (collection-trace-ready-p (append round suffix) cuts world))
  :hints (("Goal"
           :use ((:instance collection-ready-trace-of-append
                            (first (cdr round)) (second suffix)
                            (first-cut (list (caar round)))
                            (world (proof-instruction-effect (cdar round) world))))
           :expand ((collection-trace-ready-p (append round suffix) cuts world))
           :in-theory (disable collection-ready-trace-of-append
                               proof-world-pc proof-world-stop proof-instruction-at-p
                               proof-instruction-effect proof-instruction-access-p))))

(local
 (defthm collection-sweep-word-access-at-register
   (implies (and (not (equal register 31))
                 (unsigned-byte-p 64 (+ (proof-world-reg register world) offset)))
            (equal (proof-instruction-access-p
                    (list :single load 8 register operand :offset offset) world)
                   (proof-covered-p (+ (proof-world-reg register world) offset) 8
                                    (if (equal load 1) :read :write)
                                    (proof-world-regions world))))
   :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-unsigned)))))

(local
 (defthm collection-sweep-pair-load-access
   (equal (proof-instruction-access-p '(:pair t 0 20 1 :offset 0) world)
          (proof-covered-p (proof-world-reg 0 world) 16 :read (proof-world-regions world)))
   :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-unsigned)))))

(local
 (defthm collection-sweep-covered-metadata-words
   (implies (proof-covered-p head 24 :write regions)
            (and (proof-covered-p head 16 :read regions)
                 (proof-covered-p (+ head 16) 8 :read regions)
                 (proof-covered-p (+ head 16) 8 :write regions)
                 (unsigned-byte-p 64 (+ head 16))))
   :hints (("Goal"
            :use ((:instance collection-covered-subspan
                             (base head) (address head) (extent 24) (width 16) (access :write))
                  (:instance collection-covered-subspan
                             (base head) (address (+ head 16)) (extent 24) (width 8) (access :write))
                  (:instance collection-covered-address-is-a-span
                             (address head) (width 24) (access :write)))
            :in-theory (disable proof-covered-p collection-covered-address-is-a-span)))))

(local
 (defthm collection-sweep-cpu-actions-preserve-stop
   (and (equal (proof-world-stop (collection-write-pc address world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-register register value world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-word address value world)) (proof-world-stop world)))))

(local
 (defthm collection-sweep-read-after-cpu-action
   (and (equal (collection-read-word address (collection-write-pc pc world))
               (collection-read-word address world))
        (equal (collection-read-word address (collection-write-register register value world))
               (collection-read-word address world)))
   :hints (("Goal" :in-theory (e/d (collection-read-word proof-load-word)
                                  (boymoo-model::a64-read-bytes))))))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-regions
                     proof-world-stop proof-world-page-size proof-world-replies proof-load-word
                     proof-reg proof-covered-p proof-regions-p proof-instruction-at-p proof-instruction-effect
                     collection-read-word collection-write-register collection-write-pc collection-write-word
                     collection-cpu-p boymoo-model::a64-memory boymoo-model::a64-unsigned
                     (:definition ash) (:definition acl2::binary-logand)
                     (:definition acl2::binary-logior))))

(defthm collection-placed-sweep-terminator-is-ready
  (let* ((entry (collection-linux-offset "rt:sweep-string"))
         (trace (collection-linux-trace "rt:sweep-string" '(0 1) origin))
         (link (proof-world-reg 19 world)))
    (implies (and (collection-sweep-entry-p entry origin world)
                  (not (proof-world-stop world))
                  (collection-trace-placed-p trace world)
                  (proof-covered-p link 8 :read (proof-world-regions world))
                  (equal (collection-read-word link world) 0))
             (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "rt:sweep-done")))
                                       world))))

(defthm collection-placed-sweep-retain-round-is-ready
  (let* ((entry (collection-linux-offset "rt:sweep-string"))
         (trace (collection-sweep-retain-trace origin))
         (link (proof-world-reg 19 world))
         (head (collection-read-word link world))
         (regions (proof-world-regions world)))
    (implies (and (collection-sweep-entry-p entry origin world)
                  (not (proof-world-stop world))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-regions-p regions)
                  (collection-trace-placed-p trace world)
                  (proof-covered-p link 8 :read regions)
                  (not (equal head 0))
                  (proof-covered-p head 24 :write regions)
                  (not (equal (collection-read-word (+ head 16) world) 0)))
             (collection-loop-round-ready-p trace world)))
  :hints (("Goal"
           :use ((:instance collection-sweep-covered-metadata-words
                            (head (collection-read-word (proof-world-reg 19 world) world))
                            (regions (proof-world-regions world))))
           :in-theory (disable collection-sweep-covered-metadata-words
                               collection-covered-address-is-a-span))))

(local
 (defthm collection-placed-sweep-unlink-is-ready
   (let* ((entry (collection-linux-offset "rt:sweep-string"))
          (trace (collection-sweep-unlink-trace origin))
          (link (proof-world-reg 19 world))
          (head (collection-read-word link world))
          (regions (proof-world-regions world)))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (not (proof-world-stop world))
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-regions-p regions)
                   (collection-trace-placed-p trace world)
                   (proof-covered-p link 8 :write regions)
                   (not (equal head 0))
                   (proof-covered-p head 24 :write regions)
                   (equal (collection-read-word (+ head 16) world) 0))
              (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "sys:unmap")))
                                        world)))
   :hints (("Goal"
            :use ((:instance collection-sweep-covered-metadata-words
                             (head (collection-read-word (proof-world-reg 19 world) world))
                             (regions (proof-world-regions world))))
            :in-theory (disable collection-sweep-covered-metadata-words
                                collection-covered-address-is-a-span)))))

(local
 (defthm collection-sweep-unmap-actions-project-state
   (let ((after (collection-relinquish-range t head size world)))
     (and (equal (collection-cpu-p after) (collection-cpu-p world))
          (equal (proof-world-pc after) (proof-world-pc world))
          (equal (proof-world-reg register after) (proof-world-reg register world))
          (equal (proof-world-stop after) (proof-world-stop world))
          (equal (proof-world-replies after) (proof-world-replies world))))
   :hints (("Goal"
            :in-theory (e/d (collection-relinquish-range proof-clear-span collection-cpu-p
                                                       proof-world-pc proof-world-reg proof-reg
                                                       proof-world-machine proof-world-stop
                                                       proof-world-replies)
                             (proof-clear-memory proof-remove-region-span update-nth))))))

(local
 (defthm collection-sweep-returning-svc-effect
   (equal (proof-svc-return value world)
          (update-nth 6 (cdr (proof-world-replies world))
                      (collection-write-register 0 value (collection-next-instruction world))))
   :hints (("Goal" :in-theory (e/d (proof-svc-return proof-world-machine
                                                    proof-world-replies
                                                    collection-write-register collection-write-pc)
                                   (update-nth))))))

(local
 (defthm collection-sweep-instruction-and-cpu-after-reply
   (let ((after (update-nth 6 replies world)))
     (and (equal (proof-instruction-at-p instruction pc after)
                 (proof-instruction-at-p instruction pc world))
          (equal (collection-cpu-p after) (collection-cpu-p world))
          (equal (proof-world-stop after) (proof-world-stop world))
          (equal (proof-world-pc after) (proof-world-pc world))
          (equal (proof-world-reg register after) (proof-world-reg register world))))
   :hints (("Goal" :in-theory (e/d (proof-instruction-at-p proof-fetchable-p
                                                          proof-world-regions proof-world-machine
                                                          proof-world-pc proof-world-reg proof-world-stop
                                                          collection-cpu-p)
                                   (update-nth))))))

(local
 (defthm collection-sweep-relinquish-inputs-preserved-by-unlink-actions
   (and (equal (collection-relinquish-p head size (collection-write-pc pc world))
               (collection-relinquish-p head size world))
        (equal (collection-relinquish-p head size (collection-write-register register value world))
               (collection-relinquish-p head size world))
        (equal (collection-relinquish-p head size (collection-write-word address value world))
               (collection-relinquish-p head size world)))
   :hints (("Goal" :in-theory (enable proof-world-page-size proof-world-replies)))))

(local
 (defthm collection-sweep-covering-mapping-covers-metadata
   (implies (and (proof-covered-p head size :write regions)
                 (<= 24 size))
            (proof-covered-p head 24 :write regions))
   :hints (("Goal"
            :use ((:instance collection-covered-address-is-a-span
                             (address head) (width size) (access :write))
                  (:instance collection-covered-subspan
                             (base head) (address head) (extent size) (width 24) (access :write)))
            :in-theory (disable collection-covered-address-is-a-span)))))

(local
 (defthm collection-sweep-unlink-establishes-wrapper-state
   (let* ((entry (collection-linux-offset "rt:sweep-string"))
          (link (proof-world-reg 19 world))
          (head (collection-read-word link world))
          (size (collection-read-word (+ head 8) world))
          (after (collection-trace-effect (collection-sweep-unlink-trace origin) world))
          (regions (proof-world-regions world)))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-regions-p regions)
                   (proof-covered-p link 8 :write regions)
                   (not (equal head 0))
                   (proof-span-p head 24)
                   (equal (collection-read-word (+ head 16) world) 0))
              (and (collection-cpu-p after)
                   (equal (proof-world-pc after) (+ origin (collection-linux-offset "sys:unmap")))
                   (equal (proof-world-reg 30 after) (+ origin entry 28))
                   (equal (proof-world-reg 0 after) head)
                   (equal (proof-world-reg 1 after) size)
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (equal (proof-world-regions after) regions)
                   (alistp (boymoo-model::a64-memory (proof-world-machine after)))
                   (equal (collection-relinquish-p head size after)
                          (collection-relinquish-p head size world))
                   (equal (proof-instruction-at-p instruction pc after)
                          (proof-instruction-at-p instruction pc world)))))
   :hints (("Goal"
            :in-theory (disable collection-relinquish-p collection-covered-address-is-a-span)))))

(local
 (defthm collection-sweep-unlink-keeps-placement
   (let* ((entry (collection-linux-offset "rt:sweep-string"))
          (link (proof-world-reg 19 world))
          (head (collection-read-word link world))
          (after (collection-trace-effect (collection-sweep-unlink-trace origin) world))
          (regions (proof-world-regions world)))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-regions-p regions)
                   (proof-covered-p link 8 :write regions)
                   (not (equal head 0))
                   (proof-span-p head 24)
                   (equal (collection-read-word (+ head 16) world) 0))
              (equal (collection-trace-placed-p trace after)
                     (collection-trace-placed-p trace world))))
   :hints (("Goal"
            :induct (collection-trace-placed-p trace world)
            :in-theory (disable collection-trace-effect collection-sweep-unlink-trace
                                collection-sweep-entry-p proof-span-p)))))

(local
 (defthm collection-sweep-unmap-svc
   (let ((base (proof-world-reg 0 world)) (size (proof-world-reg 1 world)))
     (implies (and (equal (proof-world-reg 8 world) 215)
                   (collection-relinquish-p base size world))
              (equal (proof-instruction-effect '(:svc 0) world)
                     (proof-svc-return 0 (collection-relinquish-range t base size world)))))
   :hints (("Goal"
            :use ((:instance collection-svc-executes-relinquish (unmap t)))
            :in-theory (disable collection-svc-executes-relinquish collection-relinquish-p
                                collection-relinquish-range proof-svc-return)))))

(local
 (defthm collection-placed-unmap-wrapper-is-ready
   (let* ((entry (collection-linux-offset "sys:unmap"))
          (link (+ origin (collection-linux-offset "rt:sweep-string") 28))
          (base (proof-world-reg 0 world))
          (size (proof-world-reg 1 world))
          (trace (collection-relinquish-wrapper-trace t origin)))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (not (proof-world-stop world))
                   (equal (proof-world-reg 30 world) link)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-regions-p (proof-world-regions world))
                   (collection-relinquish-p base size world)
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list link) world)))
   :hints (("Goal"
            :in-theory (disable proof-svc-return collection-relinquish-range
                                collection-successful-linux-release
                                collection-covered-address-is-a-span)))))

(local
 (defthm collection-placed-sweep-unmap-continuation-is-ready
   (let ((entry (collection-linux-offset "rt:sweep-string"))
         (trace (collection-sweep-unmap-continuation origin)))
     (implies (and (collection-sweep-entry-p (+ entry 28) origin world)
                   (not (proof-world-stop world))
                   (equal (proof-world-reg 0 world) 0)
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list (+ origin entry)) world)))))

(defthm collection-matching-code-memory-and-regions-give-placement
   (implies (and (equal (boymoo-model::a64-memory (proof-world-machine first))
                        (boymoo-model::a64-memory (proof-world-machine second)))
                 (equal (proof-world-regions first) (proof-world-regions second)))
            (equal (collection-trace-placed-p trace first)
                   (collection-trace-placed-p trace second)))
   :rule-classes nil
   :hints (("Goal"
            :induct (len trace)
            :in-theory (e/d (proof-instruction-at-p proof-fetchable-p proof-decode-at
                                                    boymoo-model::a64-load)
                             (proof-decode boymoo-model::a64-read-bytes)))))

(defthm collection-unmap-keeps-trace-placement
   (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                 (proof-regions-p (proof-world-regions world))
                 (proof-covered-p base size :write (proof-world-regions world)))
            (equal (collection-trace-placed-p trace (collection-relinquish-range t base size world))
                   (collection-trace-placed-p trace world)))
   :hints (("Goal" :induct (collection-trace-placed-p trace world)
                   :in-theory (disable collection-relinquish-range
                                       collection-covered-address-is-a-span))))

(local
 (defthm collection-sweep-wrapper-returns-with-placed-continuation
   (let* ((entry (collection-linux-offset "sys:unmap"))
          (base (proof-world-reg 0 world))
          (size (proof-world-reg 1 world))
          (trace (collection-relinquish-wrapper-trace t origin))
          (after (collection-trace-effect trace world)))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (not (proof-world-stop world))
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-regions-p (proof-world-regions world))
                   (collection-relinquish-p base size world))
              (and (collection-cpu-p after)
                   (equal (proof-world-reg 0 after) 0)
                   (equal (proof-world-pc after) (proof-world-reg 30 world))
                   (not (proof-world-stop after))
                   (equal (collection-trace-placed-p continuation after)
                          (collection-trace-placed-p continuation world)))))
   :hints (("Goal"
            :use ((:instance collection-linux-relinquish-wrapper-effect (unmap t))
                  (:instance collection-matching-code-memory-and-regions-give-placement
                             (trace continuation)
                             (first (collection-trace-effect
                                     (collection-relinquish-wrapper-trace t origin) world))
                             (second (collection-relinquish-range
                                      t (proof-world-reg 0 world) (proof-world-reg 1 world) world))))
            :in-theory (disable collection-relinquish-wrapper-trace
                                collection-linux-relinquish-wrapper-effect collection-trace-effect
                                collection-trace-placed-p collection-relinquish-range
                                collection-covered-address-is-a-span)))))

(local
 (defthm collection-sweep-intersection-with-one-cut
   (iff (intersectp-equal addresses (list cut))
        (member-equal cut addresses))
   :hints (("Goal" :induct (len addresses)))))

(local
 (defthm collection-checked-prefix-and-suffix-close-loop-round
   (implies (and (consp prefix)
                 (collection-trace-ready-p prefix middle world)
                 (collection-trace-ready-p suffix (list (caar prefix))
                                           (collection-trace-effect prefix world))
                 (not (member-equal (caar prefix) (strip-cars (cdr prefix)))))
            (collection-loop-round-ready-p (append prefix suffix) world))
   :hints (("Goal"
            :use ((:instance collection-ready-trace-of-append
                             (first (cdr prefix)) (second suffix) (first-cut middle)
                             (cuts (list (caar prefix)))
                             (world (proof-instruction-effect (cdar prefix) world))))
            :expand ((collection-trace-ready-p prefix middle world)
                     (collection-trace-effect prefix world))
            :in-theory (disable collection-trace-ready-p collection-trace-effect
                                collection-ready-trace-of-append proof-instruction-access-p)
            :do-not-induct t))))

(local
 (defthm collection-sweep-discard-paths-exclude-early-loop-return
   (let* ((entry (+ origin (collection-linux-offset "rt:sweep-string")))
          (unlink (collection-sweep-unlink-trace origin))
          (wrapper (collection-relinquish-wrapper-trace t origin)))
     (and (consp unlink) (equal (caar unlink) entry)
          (not (member-equal entry (strip-cars (cdr unlink))))
          (not (intersectp-equal (strip-cars wrapper) (list entry)))))))

(local
 (defthm collection-sweep-discard-concatenates-checked-paths
   (let* ((entry (+ origin (collection-linux-offset "rt:sweep-string")))
          (unlink (collection-sweep-unlink-trace origin))
          (wrapper (collection-relinquish-wrapper-trace t origin))
          (resume (collection-sweep-unmap-continuation origin))
          (call (collection-trace-effect unlink world))
          (returned (collection-trace-effect wrapper call)))
     (implies (and (collection-trace-ready-p unlink
                                            (list (+ origin (collection-linux-offset "sys:unmap"))) world)
                   (collection-trace-ready-p wrapper (list (+ entry 28)) call)
                   (collection-trace-ready-p resume (list entry) returned))
              (collection-loop-round-ready-p (collection-sweep-discard-trace origin) world)))
   :hints (("Goal"
            :use ((:instance collection-sweep-discard-paths-exclude-early-loop-return)
                  (:instance collection-ready-trace-of-append
                             (first (collection-relinquish-wrapper-trace t origin))
                             (second (collection-sweep-unmap-continuation origin))
                             (first-cut (list (+ origin (collection-linux-offset "rt:sweep-string") 28)))
                             (cuts (list (+ origin (collection-linux-offset "rt:sweep-string"))))
                             (world (collection-trace-effect (collection-sweep-unlink-trace origin) world)))
                  (:instance collection-checked-prefix-and-suffix-close-loop-round
                             (prefix (collection-sweep-unlink-trace origin))
                             (suffix (append (collection-relinquish-wrapper-trace t origin)
                                             (collection-sweep-unmap-continuation origin)))
                             (middle (list (+ origin (collection-linux-offset "sys:unmap"))))))
            :in-theory (disable collection-ready-trace-of-append collection-trace-effect-of-append
                                collection-trace-ready-p collection-trace-effect
                                collection-loop-round-ready-p
                                collection-checked-prefix-and-suffix-close-loop-round
                                collection-sweep-unlink-trace collection-relinquish-wrapper-trace
                                collection-sweep-unmap-continuation)))))

(defthm collection-sweep-placement-of-appended-traces
  (equal (collection-trace-placed-p (append first second) world)
         (and (collection-trace-placed-p first world)
              (collection-trace-placed-p second world)))
  :hints (("Goal" :induct (append first second))))

(local
 (defthm collection-sweep-relinquish-supplies-writable-span
   (implies (collection-relinquish-p head size world)
            (proof-covered-p head size :write (proof-world-regions world)))))

(local
 (defun collection-sweep-discard-start-p (origin world)
   (let* ((link (proof-world-reg 19 world))
          (head (collection-read-word link world))
          (size (collection-read-word (+ head 8) world))
          (regions (proof-world-regions world)))
     (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-string") origin world)
          (not (proof-world-stop world))
          (alistp (boymoo-model::a64-memory (proof-world-machine world)))
          (proof-regions-p regions)
          (proof-covered-p link 8 :write regions)
          (not (equal head 0))
          (<= 24 size)
          (equal (collection-read-word (+ head 16) world) 0)
          (collection-relinquish-p head size world)))))

(local
 (defthm collection-sweep-discard-start-covers-metadata
   (implies (collection-sweep-discard-start-p origin world)
            (let ((head (collection-read-word (proof-world-reg 19 world) world))
                  (regions (proof-world-regions world)))
              (and (proof-covered-p head 24 :write regions)
                   (proof-span-p head 24))))
   :hints (("Goal"
            :use ((:instance collection-sweep-covering-mapping-covers-metadata
                             (head (collection-read-word (proof-world-reg 19 world) world))
                             (size (collection-read-word
                                    (+ 8 (collection-read-word (proof-world-reg 19 world) world)) world))
                             (regions (proof-world-regions world)))
                  (:instance collection-covered-address-is-a-span
                             (address (collection-read-word (proof-world-reg 19 world) world))
                             (width 24) (access :write) (regions (proof-world-regions world))))
            :in-theory (disable collection-relinquish-p collection-covered-address-is-a-span
                                collection-sweep-entry-p proof-span-p)))))

(local
 (in-theory (disable collection-relinquish-p collection-relinquish-range
                     collection-sweep-unlink-trace collection-relinquish-wrapper-trace
                     collection-sweep-unmap-continuation collection-trace-ready-p
                     collection-trace-effect collection-trace-placed-p proof-span-p)))

(local
 (defthm collection-sweep-discard-start-admits-unlink
   (implies (and (collection-sweep-discard-start-p origin world)
                 (collection-trace-placed-p (collection-sweep-unlink-trace origin) world))
            (collection-trace-ready-p (collection-sweep-unlink-trace origin)
                                      (list (+ origin (collection-linux-offset "sys:unmap"))) world))
   :hints (("Goal"
            :use ((:instance collection-sweep-discard-start-covers-metadata)
                  (:instance collection-placed-sweep-unlink-is-ready))
            :in-theory (disable collection-placed-sweep-unlink-is-ready collection-sweep-entry-p)))))

(local
 (defthm collection-sweep-discard-start-prepares-wrapper
   (let* ((call (collection-trace-effect (collection-sweep-unlink-trace origin) world))
          (entry (collection-linux-offset "rt:sweep-string")))
     (implies (collection-sweep-discard-start-p origin world)
              (and (collection-sweep-entry-p (collection-linux-offset "sys:unmap") origin call)
                   (not (proof-world-stop call))
                   (equal (proof-world-reg 30 call) (+ origin entry 28))
                   (alistp (boymoo-model::a64-memory (proof-world-machine call)))
                   (proof-regions-p (proof-world-regions call))
                   (collection-relinquish-p (proof-world-reg 0 call) (proof-world-reg 1 call) call)
                   (equal (collection-trace-placed-p trace call)
                          (collection-trace-placed-p trace world)))))
   :hints (("Goal"
            :use ((:instance collection-sweep-discard-start-covers-metadata)
                  (:instance collection-sweep-unlink-establishes-wrapper-state)
                  (:instance collection-sweep-unlink-keeps-placement))
            :in-theory (disable collection-sweep-unlink-establishes-wrapper-state
                                collection-sweep-unlink-keeps-placement)))))

(local
 (in-theory (disable collection-sweep-discard-start-p collection-sweep-entry-p
                     collection-sweep-discard-start-prepares-wrapper)))

(local
 (defthm collection-sweep-discard-start-admits-wrapper
   (let* ((call (collection-trace-effect (collection-sweep-unlink-trace origin) world))
          (trace (collection-relinquish-wrapper-trace t origin))
          (link (+ origin (collection-linux-offset "rt:sweep-string") 28)))
     (implies (and (collection-sweep-discard-start-p origin world)
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list link) call)))
   :hints (("Goal"
            :use ((:instance collection-sweep-discard-start-prepares-wrapper
                             (trace (collection-relinquish-wrapper-trace t origin)))
                  (:instance collection-placed-unmap-wrapper-is-ready
                             (world (collection-trace-effect
                                     (collection-sweep-unlink-trace origin) world))))
            :in-theory (disable collection-placed-unmap-wrapper-is-ready)))))

(local
 (defthm collection-sweep-discard-start-admits-continuation
   (let* ((call (collection-trace-effect (collection-sweep-unlink-trace origin) world))
          (returned (collection-trace-effect (collection-relinquish-wrapper-trace t origin) call))
          (trace (collection-sweep-unmap-continuation origin)))
     (implies (and (collection-sweep-discard-start-p origin world)
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "rt:sweep-string"))) returned)))
   :hints (("Goal"
            :use ((:instance collection-sweep-discard-start-prepares-wrapper
                             (trace (collection-sweep-unmap-continuation origin)))
                  (:instance collection-sweep-wrapper-returns-with-placed-continuation
                             (continuation (collection-sweep-unmap-continuation origin))
                             (world (collection-trace-effect (collection-sweep-unlink-trace origin) world)))
                  (:instance collection-placed-sweep-unmap-continuation-is-ready
                             (world (collection-trace-effect
                                     (collection-relinquish-wrapper-trace t origin)
                                     (collection-trace-effect (collection-sweep-unlink-trace origin) world)))))
            :in-theory (e/d (collection-sweep-entry-p)
                             (collection-sweep-wrapper-returns-with-placed-continuation
                              collection-placed-sweep-unmap-continuation-is-ready))))))

(defthm collection-placed-sweep-discard-round-is-ready
  (let* ((entry (collection-linux-offset "rt:sweep-string"))
         (trace (collection-sweep-discard-trace origin))
         (link (proof-world-reg 19 world))
         (head (collection-read-word link world))
         (size (collection-read-word (+ head 8) world))
         (regions (proof-world-regions world)))
    (implies (and (collection-sweep-entry-p entry origin world)
                  (not (proof-world-stop world))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-regions-p regions)
                  (collection-trace-placed-p trace world)
                  (proof-covered-p link 8 :write regions)
                  (not (equal head 0))
                  (<= 24 size)
                  (equal (collection-read-word (+ head 16) world) 0)
                  (collection-relinquish-p head size world))
             (collection-loop-round-ready-p trace world)))
  :hints (("Goal"
           :use ((:instance collection-sweep-discard-concatenates-checked-paths)
                 (:instance collection-sweep-discard-start-admits-unlink)
                 (:instance collection-sweep-discard-start-admits-wrapper)
                 (:instance collection-sweep-discard-start-admits-continuation))
           :in-theory (e/d (collection-sweep-discard-start-p)
                            (collection-loop-round-ready-p collection-sweep-discard-concatenates-checked-paths
                             collection-sweep-discard-start-admits-unlink
                             collection-sweep-discard-start-admits-wrapper
                             collection-sweep-discard-start-admits-continuation)))))
