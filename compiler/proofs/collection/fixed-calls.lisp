(in-package "BOYMOO-PROOFS")

(include-book "copied-words")
(include-book "segments")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-fixed-forward-kind (world)
  (let* ((base (proof-world-reg 28 world))
         (word (proof-world-reg 0 world))
         (tag (proof-word-tag word))
         (address (proof-pointer-address word base))
         (floor (proof-world-reg 19 world))
         (spaces-end (collection-read-word (+ 64 (proof-world-reg 17 world)) world)))
    (cond ((equal tag 0) (and (< address floor) :static-cons))
          ((not (equal tag 2)) :immediate)
          ((< address floor) (if (<= base address) :static-header :external-below))
          ((<= spaces-end address) :external-above))))

(defun collection-external-forward-kind-p (kind)
  (member-eq kind '(:external-below :external-above)))

(defun collection-fixed-forward-trace (kind origin)
  (case kind
    (:immediate
     (append (collection-forward-trace :immediate origin)
             (collection-forward-trace :return origin)))
    (:static-cons
     (append (collection-forward-trace :cons-address origin)
             (collection-forward-trace :cons-region origin)
             (collection-forward-trace :return origin)))
    (:external-above
     (append (collection-forward-trace :header-address origin)
             (collection-forward-trace :header-region origin)
             (collection-forward-trace :high-header-region origin)
             (collection-indexed-trace '(25) *collection-forward-instructions* origin)
             (collection-forward-trace :mark-string origin)))
    (otherwise
     (append (collection-forward-trace :header-address origin)
             (collection-forward-trace :header-region origin)
             (collection-forward-trace :low-header-region origin)
             (collection-forward-trace
              (if (eq kind :static-header) :return :mark-string) origin)))))

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

(local
 (defthm collection-mark-address-without-wrap
   (let ((address (boymoo-model::a64-unsigned 64 (+ -2 word base))))
     (implies (and (integerp word) (integerp base) (<= 8 address))
              (equal (boymoo-model::a64-unsigned 64 (+ -10 word base)) (- address 8))))
   :hints (("Goal"
            :use ((:instance collection-word-of-wrapped-addend
                             (left -8) (right (+ -2 word base))))
            :in-theory (disable collection-word-of-wrapped-addend)))))

(defthm collection-fixed-forward-returns-word-and-preserves-frontiers
  (let* ((kind (collection-fixed-forward-kind world))
         (word (proof-world-reg 0 world))
         (address (proof-pointer-address word (proof-world-reg 28 world)))
         (mark (- address 8))
         (after (collection-trace-effect (collection-fixed-forward-trace kind origin) world))
         (written (if (collection-external-forward-kind-p kind)
                      (collection-write-word mark 1 world)
                    world)))
    (implies (and kind
                  (collection-cpu-p world)
                  (proof-span-p origin 224)
                  (equal (proof-world-pc world) origin)
                  (implies (eq kind :external-above)
                           (proof-span-p (+ 64 (proof-world-reg 17 world)) 8))
                  (implies (collection-external-forward-kind-p kind)
                           (proof-span-p mark 8)))
             (and (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (proof-world-reg 0 after) word)
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine written)))
                  (implies (not (member-equal register '(1 2 3 4)))
                           (equal (proof-world-reg register after)
                                  (proof-world-reg register world))))))
  :hints (("Goal"
           :use ((:instance collection-mark-address-without-wrap
                            (word (proof-world-reg 0 world)) (base (proof-world-reg 28 world))))
           :in-theory (e/d (proof-pointer-address)
                           (collection-trace-effect-of-append
                            collection-forward-mark-string-effect
                            collection-mark-address-without-wrap)))))

(local
 (defthm collection-fixed-forward-mark-observed
   (let* ((kind (collection-fixed-forward-kind world))
          (address (proof-pointer-address (proof-world-reg 0 world) (proof-world-reg 28 world)))
          (mark (- address 8))
          (after (collection-trace-effect (collection-fixed-forward-trace kind origin) world)))
     (implies (and (collection-cpu-p world) (collection-external-forward-kind-p kind)
                   (proof-span-p origin 224) (proof-span-p mark 8)
                   (equal (proof-world-pc world) origin)
                   (implies (eq kind :external-above)
                            (proof-span-p (+ 64 (proof-world-reg 17 world)) 8))
                   (alistp (boymoo-model::a64-memory (proof-world-machine world))))
              (equal (collection-read-word mark after) 1)))
   :hints (("Goal"
            :use ((:instance collection-fixed-forward-returns-word-and-preserves-frontiers
                             (register 20)))
            :in-theory (e/d (collection-read-word proof-load-word)
                            (collection-fixed-forward-returns-word-and-preserves-frontiers
                             collection-fixed-forward-kind collection-fixed-forward-trace
                             collection-trace-effect boymoo-model::a64-read-bytes
                             collection-disjoint-byte-store-preserves-read))))))

(defthm collection-checked-fixed-forward-preserves-word-and-marks-external
  (let* ((kind (collection-fixed-forward-kind world))
         (word (proof-world-reg 0 world))
         (address (proof-pointer-address word (proof-world-reg 28 world)))
         (mark (- address 8))
         (trace (collection-fixed-forward-trace kind origin))
         (cuts (list (proof-world-reg 30 world)))
         (after (collection-trace-effect trace world)))
    (implies (and kind
                  (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) origin)
                  (implies (eq kind :external-above)
                           (proof-span-p (+ 64 (proof-world-reg 17 world)) 8))
                  (implies (collection-external-forward-kind-p kind)
                           (and (proof-span-p mark 8)
                                (alistp (boymoo-model::a64-memory (proof-world-machine world)))))
                  (collection-trace-ready-p trace cuts world))
             (and (proof-segment-p (len trace) cuts world :cut after)
                  (equal (proof-world-reg 0 after) word)
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (if (collection-external-forward-kind-p kind)
                      (equal (collection-read-word mark after) 1)
                    (equal (boymoo-model::a64-memory (proof-world-machine after))
                           (boymoo-model::a64-memory (proof-world-machine world)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-fixed-forward-trace
                                    (collection-fixed-forward-kind world) origin))
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance collection-fixed-forward-returns-word-and-preserves-frontiers
                            (register 20))
                 (:instance collection-fixed-forward-returns-word-and-preserves-frontiers
                            (register 21))
                 (:instance collection-fixed-forward-mark-observed))
           :in-theory (disable collection-fixed-forward-returns-word-and-preserves-frontiers
                               collection-fixed-forward-mark-observed proof-pointer-address
                               collection-fixed-forward-kind collection-fixed-forward-trace
                               collection-trace-effect collection-trace-ready-p proof-segment-p))))
