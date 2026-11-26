(in-package "BOYMOO-PROOFS")

(include-book "frame")
(include-book "pages")
(include-book "placement")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-load-word collection-read-word
                     collection-write-word boymoo-model::a64-memory
                     boymoo-model::a64-unsigned boymoo-model::a64-byte
                     (:definition ash) (:definition acl2::binary-logior))))

(local
 (defthm collection-clear-keeps-byte-outside-range
   (implies (and (alistp memory) (unsigned-byte-p 64 address)
                 (or (< address base) (<= end address)))
            (equal (boymoo-model::a64-byte address (proof-clear-memory base end memory))
                   (boymoo-model::a64-byte address memory)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte)))))

(local
 (defthm collection-clear-preserves-bytes-outside-range
   (implies (and (alistp memory) (natp address) (natp width)
                 (<= (+ address width) (expt 2 64))
                 (proof-disjoint-p address (+ address width) base end))
            (equal (boymoo-model::a64-read-bytes
                    width address (proof-clear-memory base end memory))
                   (boymoo-model::a64-read-bytes width address memory)))
   :hints (("Goal" :induct (boymoo-model::a64-read-bytes width address memory)
                   :in-theory (disable proof-clear-memory)))))

(defthm collection-clear-preserves-word-outside-range
  (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                (proof-span-p address 8)
                (proof-disjoint-p address (+ address 8) base end))
           (equal (collection-read-word address (proof-clear-span base end world))
                  (collection-read-word address world)))
  :hints (("Goal" :in-theory (e/d (collection-read-word proof-load-word proof-world-machine
                                                       boymoo-model::a64-memory)
                                  (proof-clear-memory boymoo-model::a64-read-bytes))
                  :use ((:instance collection-clear-preserves-bytes-outside-range
                                   (width 8)
                                   (memory (boymoo-model::a64-memory
                                            (proof-world-machine world))))))))

(defthm collection-cleared-world-memory
  (equal (boymoo-model::a64-memory
          (proof-world-machine (proof-clear-span base end world)))
         (proof-clear-memory base end
                             (boymoo-model::a64-memory (proof-world-machine world))))
  :hints (("Goal" :in-theory (e/d (proof-clear-span proof-world-machine boymoo-model::a64-memory)
                                 (proof-clear-memory nth update-nth)))))

(local
 (defthm collection-clearing-keeps-memory-alist
   (implies (alistp memory)
            (alistp (proof-clear-memory base end memory)))
   :hints (("Goal" :induct (proof-clear-memory base end memory)))))

(defthm collection-retired-pages-preserve-word-outside-retired-space
  (let* ((floor (* *proof-runtime-page* first-page))
         (end (* *proof-runtime-page* last-page))
         (first (proof-clear-span floor (collection-page-ceiling box) world))
         (after (proof-clear-span (collection-page-floor cons-floor) end first)))
    (implies (and (natp first-page) (natp last-page) (natp box) (natp cons-floor)
                  (<= floor box) (<= box cons-floor) (<= cons-floor end)
                  (proof-span-p address 8) (proof-disjoint-p address (+ address 8) floor end)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world))))
             (equal (collection-read-word address after)
                    (collection-read-word address world))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-retired-release-ranges)
                 (:instance collection-clear-preserves-word-outside-range
                            (base (* *proof-runtime-page* first-page))
                            (end (collection-page-ceiling box)))
                 (:instance collection-clear-preserves-word-outside-range
                            (base (collection-page-floor cons-floor))
                            (end (* *proof-runtime-page* last-page))
                            (world (proof-clear-span (* *proof-runtime-page* first-page)
                                                     (collection-page-ceiling box) world))))
           :in-theory (disable proof-clear-span proof-clear-memory
                               collection-page-ceiling collection-page-floor
                               collection-clear-preserves-word-outside-range))))

(local (in-theory (disable proof-clear-span proof-clear-memory)))

(defthm collection-disjoint-store-keeps-saved-frame
  (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                (proof-span-p frame 64) (proof-span-p address 8)
                (proof-disjoint-p frame (+ frame 64) address (+ address 8)))
           (equal (collection-frame-words frame (collection-write-word address value world))
                  (collection-frame-words frame world))))

(defthm collection-disjoint-clear-keeps-saved-frame
  (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                (proof-span-p frame 64)
                (proof-disjoint-p frame (+ frame 64) base end))
           (equal (collection-frame-words frame (proof-clear-span base end world))
                  (collection-frame-words frame world))))

; The collector saves 64 bytes and can make a call that saves another
; pair while its own frame is still on the machine stack.
(defun collection-collector-stack-room-p (world)
  (let ((floor (- (proof-machine-limit world) *proof-machine-margin*))
        (sp (boymoo-model::a64-sp (proof-world-machine world))))
    (<= (+ floor 80) sp)))

(defthm collection-stack-reservation-covers-collector-and-nested-call
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (start (- sp 80))
         (heap-start (- (proof-heap-base world) *proof-heap-prefix*)))
    (implies (and (proof-heap-layout-p world)
                  (collection-collector-stack-room-p world))
             (and (proof-covered-p start 80 :write (proof-world-regions world))
                  (equal (mod sp 16) 0)
                  (proof-disjoint-p start sp heap-start (proof-spaces-end world))
                  (proof-disjoint-p start sp (proof-stack-base world) (proof-stack-end world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-covered-subspan
                            (base (- (proof-machine-limit world) *proof-machine-margin*))
                            (extent *proof-machine-reservation*)
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 80))
                            (width 80) (access :write) (regions (proof-world-regions world)))
                 (:instance collection-covered-address-is-a-span
                            (address (- (proof-machine-limit world) *proof-machine-margin*))
                            (width *proof-machine-reservation*) (access :write)
                            (regions (proof-world-regions world))))
           :in-theory (disable proof-world-reg proof-reg mod proof-covered-p proof-regions-p
                               proof-machine-limit proof-stack-top proof-stack-limit
                               proof-stack-base proof-stack-end proof-spaces-end proof-static-size
                               proof-box-top proof-cons-floor proof-heap-limit proof-inactive-end
                               proof-active-end proof-active-floor proof-inactive-floor
                               proof-align-up proof-heap-base boymoo-model::a64-sp
                               proof-world-page-size proof-page-size-p proof-world-regions
                               collection-covered-address-is-a-span))))
