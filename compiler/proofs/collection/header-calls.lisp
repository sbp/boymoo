(in-package "BOYMOO-PROOFS")

(include-book "forward-calls")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-header-source (world)
  (proof-pointer-address (proof-world-reg 0 world) (proof-world-reg 28 world)))

(defun collection-box-forward-entry-p (origin world)
  (let ((source (collection-header-source world))
        (metadata (+ 64 (proof-world-reg 17 world))))
    (and (collection-cpu-p world)
         (proof-span-p origin 224)
         (equal (proof-world-pc world) origin)
         (equal (proof-word-tag (proof-world-reg 0 world)) 2)
         (<= (proof-world-reg 19 world) source)
         (proof-span-p metadata 8)
         (< source (collection-read-word metadata world)))))

(defun collection-box-forward-prefix (origin)
  (append (collection-forward-trace :header-address origin)
          (collection-forward-trace :header-region origin)
          (collection-forward-trace :high-header-region origin)
          (collection-forward-trace :header-marker origin)))

(defun collection-seen-box-trace (origin)
  (append (collection-box-forward-prefix origin)
          (collection-forward-trace :seen-header origin)))

(defun collection-fresh-box-prefix (count origin)
  (append (collection-box-forward-prefix origin)
          (collection-forward-trace :copy-header origin)
          (collection-forward-trace :header-count origin)
          (if (zp count) nil (collection-forward-trace :header-payload origin))))

(defun collection-fresh-box-trace (count origin)
  (append (collection-fresh-box-prefix count origin)
          (collection-copy-payload-trace count origin)
          (collection-forward-trace :return origin)))

(defun collection-header-payload-words (header)
  (let* ((size (boymoo-model::a64-unsigned 64 (proof-header-size header)))
         (rounded (boymoo-model::a64-unsigned 64 (+ size 7))))
    (boymoo-model::a64-unsigned 64 (ash rounded -3))))

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

(defthm collection-box-prefix-reads-header-and-selects-copy-or-reuse
  (let* ((source (collection-header-source world))
         (header (collection-read-word source world))
         (next (collection-trace-effect (collection-box-forward-prefix origin) world)))
    (implies (collection-box-forward-entry-p origin world)
             (and (collection-cpu-p next)
                  (equal (proof-world-pc next) (+ origin (if (logbitp 63 header) 216 140)))
                  (equal (proof-world-reg 2 next) source)
                  (equal (proof-world-reg 3 next) header)
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (implies (not (member-equal register '(1 2 3)))
                           (equal (proof-world-reg register next)
                                  (proof-world-reg register world))))))
  :hints (("Goal"
           :in-theory (e/d (proof-pointer-address)
                           (collection-trace-effect-of-append)))))

(local
 (in-theory (disable collection-box-forward-entry-p collection-header-source
                     collection-box-forward-prefix collection-forward-trace
                     collection-trace-effect collection-trace-ready-p proof-segment-p
                     collection-forwarding collection-unseen)))

(local
 (defthm collection-box-entry-text-span
   (implies (collection-box-forward-entry-p origin world)
            (proof-span-p origin 224))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable collection-box-forward-entry-p)))))

(defthm collection-checked-seen-header-reuses-discovery
  (let* ((source (collection-header-source world))
         (entry (assoc-equal source (collection-forwarding work)))
         (word (boymoo-model::a64-unsigned 64 (+ 2 (- (cdr entry) (proof-world-reg 28 world)))))
         (trace (collection-seen-box-trace origin))
         (cuts (list (proof-world-reg 30 world)))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-box-forward-entry-p origin world)
                  entry (not (assoc-equal source (collection-unseen work)))
                  (unsigned-byte-p 63 word)
                  (equal (collection-read-word source world)
                         (logior #x8000000000000000 word))
                  (collection-trace-ready-p trace cuts world))
             (and (proof-segment-p (len trace) cuts world :cut after)
                  (equal (collection-discover source work) work)
                  (equal (proof-world-reg 0 after) word)
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-seen-box-trace origin))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (enable collection-discover))))

(local
 (defthm collection-copy-word-keeps-unclobbered-register
   (implies (and (collection-cpu-p world)
                 (not (member-equal register '(2 3 4 20))))
            (equal (proof-world-reg register (collection-copy-word-effect world))
                   (proof-world-reg register world)))))

(local
 (defthm collection-copy-word-keeps-cpu
   (implies (collection-cpu-p world)
            (collection-cpu-p (collection-copy-word-effect world)))))

(local
 (in-theory (disable collection-copy-word-effect collection-payload-span-p)))

(defthm collection-copy-payload-keeps-unclobbered-register
  (implies (and (collection-cpu-p world)
                (not (member-equal register '(2 3 4 20))))
           (equal (proof-world-reg register (collection-copy-payload-effect count world))
                  (proof-world-reg register world)))
  :hints (("Goal" :induct (collection-copy-payload-effect count world))))

(local
 (defthm collection-copy-payload-keeps-cpu
   (implies (collection-cpu-p world)
            (collection-cpu-p (collection-copy-payload-effect count world)))
   :hints (("Goal" :induct (collection-copy-payload-effect count world)))))

(defthm collection-copy-payload-reaches-destination-frontier
  (implies (collection-payload-span-p count world)
           (equal (proof-world-reg 20 (collection-copy-payload-effect count world))
                  (+ (proof-world-reg 20 world) (* 8 (nfix count)))))
  :hints (("Goal" :induct (collection-copy-payload-effect count world)
                  :in-theory (disable collection-payload-iteration-frame))
          ("Subgoal *1/2"
           :use ((:instance collection-payload-iteration-frame))
           :in-theory (enable collection-payload-span-p))))

(defthm collection-fresh-header-prepares-copy-and-installs-marker
  (let* ((source (collection-header-source world))
         (destination (proof-world-reg 20 world))
         (word (boymoo-model::a64-unsigned 64 (+ 2 (- destination (proof-world-reg 28 world)))))
         (header (collection-read-word source world))
         (count (collection-header-payload-words header))
         (mark (boymoo-model::a64-unsigned 64 (logior #x8000000000000000 word)))
         (prefix (collection-fresh-box-prefix count origin))
         (next (collection-trace-effect prefix world))
         (written (collection-write-word destination header
                                         (collection-write-word source mark world))))
    (implies (and (collection-box-forward-entry-p origin world)
                  (not (logbitp 63 header))
                  (unsigned-byte-p 64 (+ 8 source))
                  (unsigned-byte-p 64 (+ 8 destination)))
             (and (collection-cpu-p next)
                  (equal (proof-world-pc next) (+ origin (if (zp count) 212 188)))
                  (equal (proof-world-reg 0 next) word)
                  (equal (proof-world-reg 2 next) (if (zp count) source (+ 8 source)))
                  (equal (proof-world-reg 3 next) count)
                  (equal (proof-world-reg 20 next) (+ 8 destination))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine written)))
                  (implies (not (member-equal register '(0 1 2 3 4 20)))
                           (equal (proof-world-reg register next)
                                  (proof-world-reg register world))))))
  :hints (("Goal"
           :use ((:instance collection-box-entry-text-span))
           :in-theory (e/d (collection-forward-trace collection-trace-effect proof-header-size)
                           (collection-forward-installs-header-marker-and-copies-header
                            collection-forward-tests-payload-count
                            collection-forward-enters-header-payload
                            collection-copy-payload-agrees-with-decoded-trace)))))

(local (in-theory (disable collection-fresh-box-prefix collection-header-payload-words)))

(local
 (defthm collection-header-count-is-natural
   (natp (collection-header-payload-words header))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable collection-header-payload-words)))))

(local
 (defthm collection-header-source-is-natural
   (natp (collection-header-source world))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable collection-header-source proof-pointer-address)))))

(defthm collection-prepared-header-admits-payload-copy
   (let* ((source (collection-header-source world))
          (destination (proof-world-reg 20 world))
          (header (collection-read-word source world))
          (count (collection-header-payload-words header))
          (bytes (+ 8 (* 8 count)))
          (prefix (collection-trace-effect (collection-fresh-box-prefix count origin) world)))
     (implies (and (collection-box-forward-entry-p origin world)
                   (not (logbitp 63 header))
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (unsigned-byte-p 64 (+ source bytes))
                   (unsigned-byte-p 64 (+ destination bytes)))
              (collection-payload-span-p count prefix)))
   :hints (("Goal" :in-theory (e/d (collection-payload-span-p) (logbitp)))))

(defthm collection-checked-fresh-header-matches-discovery
  (let* ((source (collection-header-source world))
         (destination (proof-world-reg 20 world))
         (header (collection-read-word source world))
         (count (collection-header-payload-words header))
         (size (+ 8 (* 8 count)))
         (word (boymoo-model::a64-unsigned 64 (+ 2 (- destination (proof-world-reg 28 world)))))
         (record (assoc-equal source (collection-unseen work)))
         (discovered (collection-discover source work))
         (trace (collection-fresh-box-trace count origin))
         (cuts (list (proof-world-reg 30 world)))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-box-forward-entry-p origin world)
                  (not (logbitp 63 header))
                  (eq (cadr record) :header)
                  (equal (collection-copy-bytes record) size)
                  (equal (proof-world-reg 20 world) (collection-header-frontier work))
                  (equal (proof-world-reg 21 world) (collection-cell-frontier work))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (unsigned-byte-p 64 (+ source size))
                  (unsigned-byte-p 64 (+ destination size))
                  (collection-trace-ready-p trace cuts world))
             (and (proof-segment-p (len trace) cuts world :cut after)
                  (equal (assoc-equal source (collection-forwarding discovered))
                         (cons source destination))
                  (equal (proof-world-reg 20 after) (collection-header-frontier discovered))
                  (equal (proof-world-reg 21 after) (collection-cell-frontier discovered))
                  (equal (proof-world-reg 0 after) word))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-fresh-box-trace
                                    (collection-header-payload-words
                                     (collection-read-word (collection-header-source world) world))
                                    origin))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable collection-copy-payload-effect collection-copy-bytes
                               collection-copy-payload-trace
                               collection-header-frontier collection-cell-frontier
                               collection-discover-installs-its-forwarding-entry logbitp))))

(local
 (defthm collection-header-word-depends-on-memory
   (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                   (boymoo-model::a64-memory (proof-world-machine second)))
            (equal (collection-read-word address first) (collection-read-word address second)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (collection-read-word proof-load-word)
                            (boymoo-model::a64-read-bytes))))))

(local
 (defthm collection-two-disjoint-word-stores-have-local-effects
   (let ((after (collection-write-word destination header
                                       (collection-write-word source mark world))))
     (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-span-p source 8) (proof-span-p destination 8)
                   (proof-disjoint-p source (+ source 8) destination (+ destination 8))
                   (unsigned-byte-p 64 mark) (unsigned-byte-p 64 header))
              (and (equal (collection-read-word source after) mark)
                   (equal (collection-read-word destination after) header)
                   (implies (and (proof-span-p other 8)
                                 (proof-disjoint-p other (+ other 8) source (+ source 8))
                                 (proof-disjoint-p other (+ other 8)
                                                   destination (+ destination 8)))
                            (equal (collection-read-word other after)
                                   (collection-read-word other world))))))))

(local
 (defthm collection-header-pair-readback-from-memory
   (let ((written (collection-write-word destination header
                                          (collection-write-word source mark world))))
     (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine written)))
                   (proof-span-p source 8) (proof-span-p destination 8)
                   (proof-disjoint-p source (+ source 8) destination (+ destination 8))
                   (unsigned-byte-p 64 mark) (unsigned-byte-p 64 header))
              (and (equal (collection-read-word source after) mark)
                   (equal (collection-read-word destination after) header)
                   (implies (and (proof-span-p other 8)
                                 (proof-disjoint-p other (+ other 8) source (+ source 8))
                                 (proof-disjoint-p other (+ other 8)
                                                   destination (+ destination 8)))
                            (equal (collection-read-word other after)
                                   (collection-read-word other world))))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-header-word-depends-on-memory
                             (address source) (first after)
                             (second (collection-write-word destination header
                                                            (collection-write-word source mark world))))
                  (:instance collection-header-word-depends-on-memory
                             (address destination) (first after)
                             (second (collection-write-word destination header
                                                            (collection-write-word source mark world))))
                  (:instance collection-header-word-depends-on-memory
                             (address other) (first after)
                             (second (collection-write-word destination header
                                                            (collection-write-word source mark world)))))))))

(defthm collection-header-prefix-exposes-copied-header-and-marker
  (let* ((source (collection-header-source world))
         (destination (proof-world-reg 20 world))
         (header (collection-read-word source world))
         (count (collection-header-payload-words header))
         (word (boymoo-model::a64-unsigned 64 (+ 2 (- destination (proof-world-reg 28 world)))))
         (mark (boymoo-model::a64-unsigned 64 (logior #x8000000000000000 word)))
         (prefix (collection-trace-effect (collection-fresh-box-prefix count origin) world)))
    (implies (and (collection-box-forward-entry-p origin world)
                  (not (logbitp 63 header))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (unsigned-byte-p 64 (+ source 8))
                  (unsigned-byte-p 64 (+ destination 8))
                  (proof-disjoint-p source (+ source 8) destination (+ destination 8)))
             (and (equal (collection-read-word source prefix) mark)
                  (equal (collection-read-word destination prefix) header)
                  (implies (and (proof-span-p other 8)
                                (proof-disjoint-p other (+ other 8) source (+ source 8))
                                (proof-disjoint-p other (+ other 8)
                                                  destination (+ destination 8)))
                           (equal (collection-read-word other prefix)
                                  (collection-read-word other world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-header-pair-readback-from-memory
                            (source (collection-header-source world))
                            (destination (proof-world-reg 20 world))
                            (header (collection-read-word (collection-header-source world) world))
                            (mark (boymoo-model::a64-unsigned
                                   64 (logior #x8000000000000000
                                              (boymoo-model::a64-unsigned
                                               64 (+ 2 (- (proof-world-reg 20 world)
                                                          (proof-world-reg 28 world)))))))
                            (after (collection-trace-effect
                                    (collection-fresh-box-prefix
                                     (collection-header-payload-words
                                      (collection-read-word (collection-header-source world) world))
                                     origin) world))))
           :in-theory (disable logbitp))))

(local
 (defthm collection-zero-payload-keeps-entry-world
   (and (equal (collection-copy-payload-trace 0 origin) nil)
        (equal (collection-copy-payload-effect 0 world) world)
        (equal (collection-trace-effect nil world) world))
   :hints (("Goal" :in-theory (enable collection-trace-effect)))))

(defthm collection-fresh-header-call-publishes-and-copies-entire-object
  (let* ((source (collection-header-source world))
         (destination (proof-world-reg 20 world))
         (header (collection-read-word source world))
         (count (collection-header-payload-words header))
         (bytes (+ 8 (* 8 count)))
         (word (boymoo-model::a64-unsigned 64 (+ 2 (- destination (proof-world-reg 28 world)))))
         (marker (boymoo-model::a64-unsigned 64 (logior #x8000000000000000 word)))
         (after (collection-trace-effect (collection-fresh-box-trace count origin) world)))
    (implies (and (collection-box-forward-entry-p origin world)
                  (not (logbitp 63 header))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (unsigned-byte-p 64 (+ source bytes))
                  (unsigned-byte-p 64 (+ destination bytes))
                  (proof-disjoint-p source (+ source bytes) destination (+ destination bytes)))
             (and (equal (collection-read-word source after) marker)
                  (equal (collection-read-word destination after) header)
                  (implies (and (natp index) (< index count))
                           (equal (collection-read-word (+ 8 destination (* 8 index)) after)
                                  (collection-read-word (+ 8 source (* 8 index)) world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-fresh-header-prepares-copy-and-installs-marker
                            (register 21))
                 (:instance collection-prepared-header-admits-payload-copy)
                 (:instance collection-header-prefix-exposes-copied-header-and-marker
                            (other (+ 8 (collection-header-source world) (* 8 index))))
                 (:instance collection-payload-copies-every-word
                            (count (collection-header-payload-words
                                    (collection-read-word (collection-header-source world) world)))
                            (world (collection-trace-effect
                                    (collection-fresh-box-prefix
                                     (collection-header-payload-words
                                      (collection-read-word (collection-header-source world) world))
                                     origin) world)))
                 (:instance collection-payload-preserves-disjoint-word
                            (count (collection-header-payload-words
                                    (collection-read-word (collection-header-source world) world)))
                            (address (collection-header-source world))
                            (world (collection-trace-effect
                                    (collection-fresh-box-prefix
                                     (collection-header-payload-words
                                      (collection-read-word (collection-header-source world) world))
                                     origin) world)))
                 (:instance collection-payload-preserves-disjoint-word
                            (count (collection-header-payload-words
                                    (collection-read-word (collection-header-source world) world)))
                            (address (proof-world-reg 20 world))
                            (world (collection-trace-effect
                                    (collection-fresh-box-prefix
                                     (collection-header-payload-words
                                      (collection-read-word (collection-header-source world) world))
                                     origin) world))))
           :in-theory (e/d (collection-payload-span-p)
                           (collection-copy-payload-trace collection-copy-payload-effect
                            collection-fresh-header-prepares-copy-and-installs-marker
                            collection-prepared-header-admits-payload-copy
                            collection-payload-preserves-disjoint-word logbitp)))))

(defthm collection-fresh-header-preserves-disjoint-word
  (let* ((source (collection-header-source world))
         (destination (proof-world-reg 20 world))
         (header (collection-read-word source world))
         (count (collection-header-payload-words header))
         (bytes (+ 8 (* 8 count)))
         (next (collection-trace-effect (collection-fresh-box-trace count origin) world)))
    (implies (and (collection-box-forward-entry-p origin world)
                  (not (logbitp 63 header))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (unsigned-byte-p 64 (+ source bytes))
                  (unsigned-byte-p 64 (+ destination bytes))
                  (proof-disjoint-p source (+ source bytes) destination (+ destination bytes))
                  (proof-span-p address 8)
                  (proof-disjoint-p address (+ address 8) source (+ source 8))
                  (proof-disjoint-p address (+ address 8) destination (+ destination bytes)))
             (equal (collection-read-word address next) (collection-read-word address world))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-fresh-header-prepares-copy-and-installs-marker
                            (register 21))
                 (:instance collection-prepared-header-admits-payload-copy)
                 (:instance collection-header-prefix-exposes-copied-header-and-marker (other address))
                 (:instance collection-payload-preserves-disjoint-word
                            (count (collection-header-payload-words
                                    (collection-read-word (collection-header-source world) world)))
                            (world (collection-trace-effect
                                    (collection-fresh-box-prefix
                                     (collection-header-payload-words
                                      (collection-read-word (collection-header-source world) world))
                                     origin)
                                    world))))
           :in-theory (e/d (collection-payload-span-p)
                           (collection-copy-payload-trace collection-copy-payload-effect
                            collection-fresh-header-prepares-copy-and-installs-marker
                            collection-prepared-header-admits-payload-copy
                            collection-payload-preserves-disjoint-word logbitp)))))

(defthm collection-fresh-header-keeps-unclobbered-register
  (let* ((source (collection-header-source world))
         (header (collection-read-word source world))
         (count (collection-header-payload-words header))
         (after (collection-trace-effect (collection-fresh-box-trace count origin) world)))
    (implies (and (collection-box-forward-entry-p origin world)
                  (not (logbitp 63 header))
                  (unsigned-byte-p 64 (+ source 8))
                  (unsigned-byte-p 64 (+ (proof-world-reg 20 world) 8))
                  (not (member-equal register '(0 1 2 3 4 20))))
             (equal (proof-world-reg register after) (proof-world-reg register world))))
  :hints (("Goal"
           :use ((:instance collection-fresh-header-prepares-copy-and-installs-marker))
           :in-theory (disable collection-copy-payload-trace collection-copy-payload-effect
                               collection-fresh-header-prepares-copy-and-installs-marker logbitp))))
