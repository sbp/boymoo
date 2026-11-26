(in-package "BOYMOO-PROOFS")

(include-book "comparisons")
(include-book "runtime-layout")

(logic)
(set-verify-guards-eagerness 0)

(defconst *collection-forward-instructions*
  (let* ((start (collection-linux-offset "rt:forward"))
         (end (collection-linux-offset "rt:release-range"))
         (count (ash (- end start) -2)))
    (take count (nthcdr (ash start -2) *collection-linux-instructions*))))

; Indices are measured from rt:forward in the assembled text.
(defun collection-forward-trace (path origin)
  (collection-indexed-trace
   (case path
     (:immediate '(0 1 2 3))
     (:cons-address '(0 1 4 5 6))
     (:header-address '(0 1 2 3 4 5 6))
     (:cons-region '(7 8))
     (:cons-marker '(9 10 11))
     (:copy-cons '(12 13 14 15 16 17))
     (:seen-cons '(18 19))
     (:header-region '(20 21))
     (:high-header-region '(22 23 24))
     (:low-header-region '(26 27))
     (:mark-string '(28 29 30 31))
     (:header-marker '(32 33 34))
     (:copy-header '(35 36 37 38 39 40 41 42 43 44))
     (:header-count '(45))
     (:header-payload '(46))
     (:copy-word '(47 48 49 50 51 52))
     (:return '(53))
     (:seen-header '(54 55)))
   *collection-forward-instructions* origin))

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc
                     proof-world-machine proof-reg proof-load-word
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-flags
                     collection-subtract-flags proof-word-tag
                     boymoo-model::a64-unsigned boymoo-model::a64-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand)
                     (:definition acl2::binary-logior))))

(defthm collection-forward-seen-cons-effect
  (implies (collection-cpu-p world)
           (equal (collection-trace-effect
                   (collection-forward-trace :seen-cons origin) world)
                  (collection-write-pc
                   (proof-world-reg 30 world)
                   (collection-write-register 0 (proof-world-reg 4 world) world)))))

(defthm collection-forward-seen-header-effect
  (implies (collection-cpu-p world)
           (equal (collection-trace-effect
                   (collection-forward-trace :seen-header origin) world)
                  (collection-write-pc
                   (proof-world-reg 30 world)
                   (collection-write-register
                    0 (logand (proof-world-reg 3 world) #x7fffffffffffffff) world)))))

(defun collection-mark-string-effect (world)
  (let ((mark (- (proof-world-reg 2 world) 8)))
    (collection-write-pc
     (proof-world-reg 30 world)
     (collection-write-word
      (boymoo-model::a64-unsigned 64 mark) 1
      (collection-write-register 4 mark
                                 (collection-write-register 3 1 world))))))

(defthm collection-forward-mark-string-effect
  (implies (collection-cpu-p world)
           (equal (collection-trace-effect
                   (collection-forward-trace :mark-string origin) world)
                  (collection-mark-string-effect world))))

(defun collection-copy-cons-effect (world)
  (let* ((source (proof-world-reg 2 world))
         (destination (- (proof-world-reg 21 world) 16))
         (address (boymoo-model::a64-unsigned 64 destination))
         (word (- address (proof-world-reg 28 world)))
         (next (collection-write-register 21 destination world))
         (next (collection-write-word address (proof-world-reg 3 world) next))
         (next (collection-write-word (+ 8 address) (proof-world-reg 4 world) next))
         (next (collection-write-register 0 word next))
         (next (collection-write-register 3 6 next))
         (next (collection-write-word source 6 next))
         (next (collection-write-word (+ 8 source)
                                      (boymoo-model::a64-unsigned 64 word) next)))
    (collection-write-pc (proof-world-reg 30 world) next)))

(defthm collection-forward-copy-cons-effect
  (implies (collection-cpu-p world)
           (equal (collection-trace-effect
                   (collection-forward-trace :copy-cons origin) world)
                  (collection-copy-cons-effect world))))

(local
 (defthm collection-copy-cons-length
   (equal (len (collection-forward-trace :copy-cons origin)) 6)))

(defthm collection-forward-copy-cons-reaches-return
  (implies (and (collection-cpu-p world)
                (collection-trace-ready-p (collection-forward-trace :copy-cons origin)
                                          (list (proof-world-reg 30 world)) world))
           (proof-segment-p 6 (list (proof-world-reg 30 world)) world :cut
                            (collection-copy-cons-effect world)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-forward-trace :copy-cons origin))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable collection-forward-trace collection-trace-effect
                               collection-trace-ready-p proof-segment-p
                               collection-copy-cons-effect))))

(defun collection-copy-word-effect (world)
  (let* ((from (proof-world-reg 2 world))
         (to (proof-world-reg 20 world))
         (remaining (proof-world-reg 3 world))
         (word (collection-read-word from world))
         (next (collection-write-register 4 word world))
         (next (collection-write-word to (boymoo-model::a64-unsigned 64 word) next))
         (next (collection-write-register 2 (+ from 8) next))
         (next (collection-write-register 20 (+ to 8) next))
         (next (collection-write-register 3 (1- remaining) next))
         (next (collection-write-flags (collection-subtract-flags remaining 1) next)))
    (collection-write-pc (+ (proof-world-pc world) (if (equal remaining 1) 24 0)) next)))

(defthm collection-forward-copy-word-effect
  (implies (collection-cpu-p world)
           (equal (collection-trace-effect (collection-forward-trace :copy-word origin)
                                           world)
                  (collection-copy-word-effect world))))

(defthm collection-forward-copy-word-decreases-count
  (implies (and (collection-cpu-p world) (posp (proof-world-reg 3 world)))
           (equal (proof-world-reg 3 (collection-copy-word-effect world))
                  (1- (proof-world-reg 3 world)))))

(defthm collection-forward-immediate-selects-return
  (let* ((tag (proof-word-tag (proof-world-reg 0 world)))
         (next (collection-trace-effect (collection-forward-trace :immediate origin)
                                        world)))
    (implies (and (collection-cpu-p world)
                  (equal (proof-world-pc world) origin)
                  (unsigned-byte-p 64 (+ origin 212))
                  (not (equal tag 0)) (not (equal tag 2)))
             (and (equal (proof-world-pc next) (+ origin 212))
                  (equal (proof-world-reg 0 next) (proof-world-reg 0 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))))))

(defthm collection-forward-decodes-pointer-address
  (let* ((word (proof-world-reg 0 world))
         (tag (proof-word-tag word))
         (header (equal tag 2))
         (next (collection-trace-effect
                (collection-forward-trace (if header :header-address :cons-address) origin)
                world)))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) origin)
                  (or header (equal tag 0)))
             (and (equal (proof-world-pc next) (+ origin (if header 80 28)))
                  (equal (proof-world-reg 2 next)
                         (proof-pointer-address word (proof-world-reg 28 world)))
                  (equal (proof-world-reg 0 next) word)
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world))))))
  :hints (("Goal" :cases ((equal (proof-word-tag (proof-world-reg 0 world)) 2)))))

(defthm collection-forward-tests-cons-region
  (let* ((static (< (proof-world-reg 2 world) (proof-world-reg 19 world)))
         (next (collection-trace-effect (collection-forward-trace :cons-region origin) world)))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 28)))
             (and (equal (proof-world-pc next) (+ origin (if static 212 36)))
                  (equal (proof-world-reg 0 next) (proof-world-reg 0 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))))))

(defthm collection-forward-tests-header-region
  (let* ((below (< (proof-world-reg 2 world) (proof-world-reg 19 world)))
         (next (collection-trace-effect (collection-forward-trace :header-region origin)
                                        world)))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 80)))
             (and (equal (proof-world-pc next) (+ origin (if below 104 88)))
                  (equal (proof-world-reg 0 next) (proof-world-reg 0 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))))))

(defthm collection-forward-tests-low-header-region
  (let* ((static (<= (proof-world-reg 28 world) (proof-world-reg 2 world)))
         (next (collection-trace-effect (collection-forward-trace :low-header-region origin)
                                        world)))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 104)))
             (and (equal (proof-world-pc next) (+ origin (if static 212 112)))
                  (equal (proof-world-reg 0 next) (proof-world-reg 0 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))))))

(defthm collection-forward-tests-high-header-region
  (let* ((limit (boymoo-model::a64-unsigned
                 64 (collection-read-word (+ 64 (proof-world-reg 17 world)) world)))
         (heap (< (proof-world-reg 2 world) limit))
         (next (collection-trace-effect (collection-forward-trace :high-header-region origin)
                                        world)))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 88)))
             (and (equal (proof-world-pc next) (+ origin (if heap 128 100)))
                  (equal (proof-world-reg 0 next) (proof-world-reg 0 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))))))

(defthm collection-forward-tests-cons-marker
  (let* ((address (proof-world-reg 2 world))
         (first (boymoo-model::a64-unsigned 64 (collection-read-word address world)))
         (second (boymoo-model::a64-unsigned 64 (collection-read-word (+ address 8) world)))
         (next (collection-trace-effect (collection-forward-trace :cons-marker origin) world)))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 36)))
             (and (equal (proof-world-pc next) (+ origin (if (equal first 6) 72 48)))
                  (equal (proof-world-reg 3 next) first)
                  (equal (proof-world-reg 4 next) second)))))

(defthm collection-forward-tests-header-marker
  (let* ((header (boymoo-model::a64-unsigned
                  64 (collection-read-word (proof-world-reg 2 world) world)))
         (next (collection-trace-effect (collection-forward-trace :header-marker origin) world)))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 128)))
             (and (equal (proof-world-pc next) (+ origin (if (logbitp 63 header) 216 140)))
                  (equal (proof-world-reg 3 next) header)))))

(defthm collection-forward-installs-header-marker-and-copies-header
  (let* ((source (proof-world-reg 2 world))
         (destination (proof-world-reg 20 world))
         (header (proof-world-reg 3 world))
         (word (boymoo-model::a64-unsigned 64 (+ 2 (- destination (proof-world-reg 28 world)))))
         (mark (boymoo-model::a64-unsigned 64 (logior #x8000000000000000 word)))
         (size (boymoo-model::a64-unsigned 64 (ash header -8)))
         (rounded (boymoo-model::a64-unsigned 64 (+ size 7)))
         (count (boymoo-model::a64-unsigned 64 (ash rounded -3)))
         (next (collection-trace-effect (collection-forward-trace :copy-header origin) world))
         (written (collection-write-word
                   destination header (collection-write-word source mark world))))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 140)))
             (and (equal (proof-world-pc next) (+ origin 180))
                  (equal (proof-world-reg 0 next) word)
                  (equal (proof-world-reg 2 next) source)
                  (equal (proof-world-reg 3 next) count)
                  (equal (proof-world-reg 20 next)
                         (boymoo-model::a64-unsigned 64 (+ destination 8)))
                  (equal (proof-world-reg 21 next) (proof-world-reg 21 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine written)))))))

(defthm collection-forward-tests-payload-count
  (let ((next (collection-trace-effect (collection-forward-trace :header-count origin)
                                        world)))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 180)))
             (equal (proof-world-pc next)
                    (+ origin (if (equal (proof-world-reg 3 world) 0) 212 184))))))

(defthm collection-forward-enters-header-payload
  (let ((next (collection-trace-effect (collection-forward-trace :header-payload origin)
                                        world)))
    (implies (and (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) (+ origin 184)))
             (and (equal (proof-world-pc next) (+ origin 188))
                  (equal (proof-world-reg 2 next)
                         (boymoo-model::a64-unsigned 64 (+ 8 (proof-world-reg 2 world))))))))

(defthm collection-forward-return-changes-only-pc
  (implies (collection-cpu-p world)
           (equal (collection-trace-effect (collection-forward-trace :return origin) world)
                  (collection-write-pc (proof-world-reg 30 world) world))))
