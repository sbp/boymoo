(in-package "BOYMOO-PROOFS")

(include-book "release-pair")
(include-book "sweep-call")
(include-book "finish-tail")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-finish-sweep-branch (origin)
  (collection-linux-trace "rt:collect-finish" '(36) origin))

(defun collection-finish-sweep-entry (origin world)
  (let ((released (collection-trace-effect (collection-retired-release-pair-trace origin world) world)))
    (collection-trace-effect (collection-finish-sweep-branch origin) released)))

(defun collection-finish-before-restore (records origin world)
  (collection-trace-effect (collection-sweep-call-trace records origin)
                           (collection-finish-sweep-entry origin world)))

(defun collection-finish-cleanup-input-p (records origin world)
  (let* ((frame (boymoo-model::a64-sp (proof-world-machine world)))
         (end (+ frame 64))
         (heap (proof-world-reg 28 world))
         (sweep (collection-finish-sweep-entry origin world)))
    (and (proof-span-p origin (car *collection-linux-layout*))
         (<= 16 frame) (unsigned-byte-p 64 end) (<= 128 heap)
         (collection-retired-release-pair-input-p origin world)
         (collection-sweep-call-input-p records origin sweep)
         (alistp (boymoo-model::a64-memory
                  (proof-world-machine (collection-sweep-body-end records origin sweep))))
         (proof-disjoint-p frame end (proof-world-reg 19 world)
                           (collection-page-ceiling (proof-world-reg 8 world)))
         (proof-disjoint-p frame end (collection-page-floor (proof-world-reg 20 world))
                           (proof-world-reg 22 world))
         (proof-disjoint-p frame end (- heap 72) (- heap 40))
         (collection-sweep-spans-separate-p frame end records))))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-reg proof-world-pc proof-world-stop
                     proof-world-regions proof-world-replies proof-instruction-effect proof-load-word
                     collection-cpu-p collection-write-register collection-write-pc collection-read-word
                     collection-write-word collection-write-sp boymoo-model::a64-sp boymoo-model::a64-unsigned
                     boymoo-model::a64-memory collection-page-floor collection-page-ceiling)))

(local
 (defthm collection-finish-sweep-branch-prepares-call
   (let* ((trace (collection-finish-sweep-branch origin))
          (after (collection-trace-effect trace world)))
     (implies (and (collection-cpu-p world)
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:collect-finish") 144)))
              (and (equal (proof-world-pc after) (+ origin (collection-linux-offset "rt:sweep-strings")))
                   (equal (proof-world-reg 30 after) (+ origin (collection-linux-offset "rt:collect-finish") 148))
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (collection-read-word address after) (collection-read-word address world))
                   (equal (proof-world-replies after) (proof-world-replies world))
                   (implies (not (equal register 30))
                            (equal (proof-world-reg register after) (proof-world-reg register world))))))
   :hints (("Goal" :in-theory (enable proof-world-replies)))))

(local
 (in-theory (disable collection-finish-sweep-branch collection-retired-release-pair-trace
                     collection-retired-release-pair-input-p collection-trace-effect
                     collection-sweep-call-input-p collection-sweep-call-trace collection-sweep-body-end
                     collection-sweep-spans-separate-p)))

(local
 (defthm collection-finish-sweep-entry-keeps-frame-geometry
   (let ((next (collection-finish-sweep-entry origin world)))
     (implies (and (collection-retired-release-pair-input-p origin world)
                   (proof-span-p origin (car *collection-linux-layout*)))
              (and (equal (proof-world-reg 30 next) (+ origin (collection-linux-offset "rt:collect-finish") 148))
                   (equal (boymoo-model::a64-sp (proof-world-machine next))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (proof-world-reg 28 next) (proof-world-reg 28 world)))))
   :hints (("Goal"
            :use ((:instance collection-retired-release-pair-preserves-frame-and-counts-replies (register 28))
                  (:instance collection-finish-sweep-branch-prepares-call
                             (register 28)
                             (world (collection-trace-effect (collection-retired-release-pair-trace origin world) world))))
            :in-theory (disable collection-retired-release-pair-preserves-frame-and-counts-replies
                                collection-finish-sweep-branch-prepares-call)))))

(defthm collection-finish-cleanup-reaches-restoration-cutpoint
  (let* ((frame (boymoo-model::a64-sp (proof-world-machine world)))
         (swept (collection-finish-before-restore records origin world)))
    (implies (collection-finish-cleanup-input-p records origin world)
             (and (collection-final-restore-input-p origin swept)
                  (equal (boymoo-model::a64-sp (proof-world-machine swept)) frame))))
  :hints (("Goal"
           :use ((:instance collection-finish-sweep-entry-keeps-frame-geometry)
                 (:instance collection-sweep-call-returns-and-debits-kernel-replies
                            (register 28) (world (collection-finish-sweep-entry origin world))))
           :in-theory (disable collection-finish-sweep-entry collection-finish-sweep-entry-keeps-frame-geometry
                               collection-sweep-call-returns-and-debits-kernel-replies))))

(local
 (defthm collection-finish-sweep-entry-keeps-frame-word
   (let* ((frame (boymoo-model::a64-sp (proof-world-machine world)))
          (next (collection-finish-sweep-entry origin world)))
     (implies (and (collection-finish-cleanup-input-p records origin world)
                   (proof-subspan-p address 8 frame (+ frame 64)))
              (equal (collection-read-word address next) (collection-read-word address world))))
   :hints (("Goal"
            :use ((:instance collection-retired-release-pair-protects-word-outside-ranges-and-save)
                  (:instance collection-retired-release-pair-preserves-frame-and-counts-replies (register 28))
                  (:instance collection-finish-sweep-branch-prepares-call
                             (register 28)
                             (world (collection-trace-effect (collection-retired-release-pair-trace origin world) world))))
            :in-theory (disable collection-retired-release-pair-preserves-frame-and-counts-replies
                                collection-finish-sweep-branch-prepares-call)))))

(defthm collection-finish-cleanup-preserves-each-saved-word
  (let* ((frame (boymoo-model::a64-sp (proof-world-machine world)))
         (swept (collection-finish-before-restore records origin world)))
    (implies (and (collection-finish-cleanup-input-p records origin world)
                  (proof-subspan-p address 8 frame (+ frame 64)))
             (equal (collection-read-word address swept) (collection-read-word address world))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-finish-sweep-entry-keeps-frame-geometry)
                 (:instance collection-finish-sweep-entry-keeps-frame-word)
                 (:instance collection-sweep-subspan-separates-from-same-mappings
                            (width 8) (start (boymoo-model::a64-sp (proof-world-machine world)))
                            (end (+ 64 (boymoo-model::a64-sp (proof-world-machine world)))))
                 (:instance collection-sweep-call-preserves-word-outside-its-write-spans
                            (world (collection-finish-sweep-entry origin world))))
           :in-theory (disable collection-finish-sweep-entry collection-finish-sweep-entry-keeps-frame-geometry
                               collection-finish-sweep-entry-keeps-frame-word))))

(local
 (in-theory (disable collection-finish-before-restore collection-finish-cleanup-input-p)))

(defthm collection-finish-cleanup-preserves-saved-frame
  (let* ((frame (boymoo-model::a64-sp (proof-world-machine world)))
         (swept (collection-finish-before-restore records origin world)))
    (implies (collection-finish-cleanup-input-p records origin world)
             (equal (collection-frame-words frame swept) (collection-frame-words frame world))))
  :hints (("Goal"
           :use ((:instance collection-finish-cleanup-preserves-each-saved-word
                            (address (boymoo-model::a64-sp (proof-world-machine world))))
                 (:instance collection-finish-cleanup-preserves-each-saved-word
                            (address (+ 8 (boymoo-model::a64-sp (proof-world-machine world)))))
                 (:instance collection-finish-cleanup-preserves-each-saved-word
                            (address (+ 16 (boymoo-model::a64-sp (proof-world-machine world)))))
                 (:instance collection-finish-cleanup-preserves-each-saved-word
                            (address (+ 24 (boymoo-model::a64-sp (proof-world-machine world)))))
                 (:instance collection-finish-cleanup-preserves-each-saved-word
                            (address (+ 32 (boymoo-model::a64-sp (proof-world-machine world)))))
                 (:instance collection-finish-cleanup-preserves-each-saved-word
                            (address (+ 40 (boymoo-model::a64-sp (proof-world-machine world)))))
                 (:instance collection-finish-cleanup-preserves-each-saved-word
                            (address (+ 48 (boymoo-model::a64-sp (proof-world-machine world)))))
                 (:instance collection-finish-cleanup-preserves-each-saved-word
                            (address (+ 56 (boymoo-model::a64-sp (proof-world-machine world))))))
           :in-theory (enable collection-finish-cleanup-input-p))))

(defun collection-finish-cleanup-trace (records origin world)
  (let* ((frame (boymoo-model::a64-sp (proof-world-machine world)))
         (headerp (equal (collection-read-word (+ frame 8) world) 0)))
    (append (collection-retired-release-pair-trace origin world)
            (collection-finish-sweep-branch origin)
            (collection-sweep-call-trace records origin)
            (collection-finish-tail-trace headerp origin))))

(local
 (defthm collection-finish-cleanup-effect-composes-before-restoration
   (let* ((swept (collection-finish-before-restore records origin world))
          (sp (boymoo-model::a64-sp (proof-world-machine world)))
          (headerp (equal (collection-read-word (+ sp 8) world) 0)))
     (equal (collection-trace-effect (collection-finish-cleanup-trace records origin world) world)
            (collection-trace-effect (collection-finish-tail-trace headerp origin) swept)))
   :hints (("Goal" :in-theory (enable collection-finish-before-restore collection-finish-sweep-entry)))))

(local
 (in-theory (disable collection-finish-cleanup-trace collection-finish-sweep-entry collection-finish-tail-trace
                     proof-segment-p collection-trace-ready-p collection-final-restore-input-p)))

(defthm collection-checked-finish-cleanup-restores-frame-and-selects-allocator
  (let* ((frame (boymoo-model::a64-sp (proof-world-machine world)))
         (headerp (equal (collection-read-word (+ frame 8) world) 0))
         (trace (collection-finish-cleanup-trace records origin world))
         (after (collection-trace-effect trace world))
         (target (+ origin (collection-linux-offset (if headerp "rt:alloc" "rt:alloc-cells")))))
    (implies (and (collection-finish-cleanup-input-p records origin world)
                  (collection-trace-ready-p trace (list target) world))
             (and (proof-segment-p (len trace) (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ frame 64))
                  (equal (collection-saved-registers after) (collection-frame-words frame world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-finish-cleanup-reaches-restoration-cutpoint)
                 (:instance collection-finish-cleanup-preserves-saved-frame)
                 (:instance collection-finish-tail-restores-all-frame-words
                            (world (collection-finish-before-restore records origin world))
                            (headerp (equal (collection-read-word
                                             (+ 8 (boymoo-model::a64-sp (proof-world-machine world))) world) 0)))
                 (:instance collection-ready-trace-reaches-cut
                            (trace (collection-finish-cleanup-trace records origin world))
                            (cuts (list (+ origin (collection-linux-offset
                                                  (if (equal (collection-read-word
                                                              (+ 8 (boymoo-model::a64-sp (proof-world-machine world)))
                                                              world) 0)
                                                      "rt:alloc" "rt:alloc-cells")))))))
           :in-theory (disable collection-finish-cleanup-reaches-restoration-cutpoint
                               collection-finish-cleanup-preserves-saved-frame
                               collection-finish-tail-restores-all-frame-words))))
