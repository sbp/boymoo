(in-package "BOYMOO-PROOFS")

(include-book "copied-words")
(include-book "segments")
(include-book "space")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-cons-source (world)
  (proof-pointer-address (proof-world-reg 0 world) (proof-world-reg 28 world)))

(defun collection-cons-forward-entry-p (origin world)
  (and (collection-cpu-p world)
       (proof-span-p origin 224)
       (equal (proof-world-pc world) origin)
       (equal (proof-word-tag (proof-world-reg 0 world)) 0)
       (<= (proof-world-reg 19 world) (collection-cons-source world))))

(defun collection-cons-forward-prefix (origin)
  (append (collection-forward-trace :cons-address origin)
          (collection-forward-trace :cons-region origin)
          (collection-forward-trace :cons-marker origin)))

(defun collection-cons-forward-trace (seen origin)
  (append (collection-cons-forward-prefix origin)
          (collection-forward-trace (if seen :seen-cons :copy-cons) origin)))

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

(defthm collection-cons-prefix-reads-source-and-selects-copy-or-reuse
  (let* ((source (collection-cons-source world))
         (first (collection-read-word source world))
         (second (collection-read-word (+ source 8) world))
         (next (collection-trace-effect (collection-cons-forward-prefix origin) world)))
    (implies (collection-cons-forward-entry-p origin world)
             (and (collection-cpu-p next)
                  (equal (proof-world-pc next) (+ origin (if (equal first 6) 72 48)))
                  (equal (proof-world-reg 2 next) source)
                  (equal (proof-world-reg 3 next) first)
                  (equal (proof-world-reg 4 next) second)
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (implies (not (member-equal register '(1 2 3 4)))
                           (equal (proof-world-reg register next)
                                  (proof-world-reg register world))))))
  :hints (("Goal"
           :in-theory (disable collection-trace-effect-of-append))
          ("Goal'" :in-theory (enable proof-pointer-address))))

(local
 (in-theory (disable collection-cons-forward-prefix collection-cons-source
                     collection-cons-forward-entry-p collection-copy-cons-effect
                     collection-forward-trace collection-trace-effect
                     collection-trace-ready-p proof-segment-p
                     collection-unseen collection-forwarding
                     collection-header-frontier collection-cell-frontier)))

(defthm collection-checked-fresh-cons-matches-discovery
  (let* ((source (collection-cons-source world))
         (destination (- (proof-world-reg 21 world) 16))
         (word (boymoo-model::a64-unsigned 64 (- destination (proof-world-reg 28 world))))
         (record (assoc-equal source (collection-unseen work)))
         (discovered (collection-discover source work))
         (trace (collection-cons-forward-trace nil origin))
         (cuts (list (proof-world-reg 30 world)))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-cons-forward-entry-p origin world)
                  (not (equal (collection-read-word source world) 6))
                  (eq (cadr record) :cons)
                  (equal (proof-world-reg 20 world) (collection-header-frontier work))
                  (equal (proof-world-reg 21 world) (collection-cell-frontier work))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-span-p source 16) (proof-span-p destination 16)
                  (proof-disjoint-p source (+ source 16) destination (+ destination 16))
                  (collection-trace-ready-p trace cuts world))
             (and (proof-segment-p (len trace) cuts world :cut after)
                  (equal (assoc-equal source (collection-forwarding discovered))
                         (cons source destination))
                  (equal (proof-world-reg 20 after) (collection-header-frontier discovered))
                  (equal (proof-world-reg 21 after) (collection-cell-frontier discovered))
                  (equal (proof-world-reg 0 after) word)
                  (equal (collection-read-word source after) 6)
                  (equal (collection-read-word (+ source 8) after) word)
                  (equal (collection-read-word destination after)
                         (collection-read-word source world))
                  (equal (collection-read-word (+ destination 8) after)
                         (collection-read-word (+ source 8) world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-trace-reaches-cut
                            (trace (collection-cons-forward-trace nil origin))
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance collection-cons-copy-publishes-marker-and-both-fields
                            (world (collection-trace-effect
                                    (collection-cons-forward-prefix origin) world))))
           :in-theory (disable collection-cons-copy-publishes-marker-and-both-fields
                               collection-discover-installs-its-forwarding-entry))))

(defthm collection-checked-seen-cons-reuses-discovery
  (let* ((source (collection-cons-source world))
         (entry (assoc-equal source (collection-forwarding work)))
         (word (boymoo-model::a64-unsigned 64 (- (cdr entry) (proof-world-reg 28 world))))
         (trace (collection-cons-forward-trace t origin))
         (cuts (list (proof-world-reg 30 world)))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-cons-forward-entry-p origin world)
                  entry (not (assoc-equal source (collection-unseen work)))
                  (equal (collection-read-word source world) 6)
                  (equal (collection-read-word (+ source 8) world) word)
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
                            (trace (collection-cons-forward-trace t origin))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (enable collection-discover))))

(defthm collection-word-read-from-equal-memories
  (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                  (boymoo-model::a64-memory (proof-world-machine second)))
           (equal (collection-read-word address first) (collection-read-word address second)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (collection-read-word proof-load-word)
                                  (boymoo-model::a64-read-bytes)))))

(defthm collection-fresh-cons-preserves-disjoint-word
  (let* ((source (collection-cons-source world))
         (destination (- (proof-world-reg 21 world) 16))
         (after (collection-trace-effect (collection-cons-forward-trace nil origin) world)))
    (implies (and (collection-cons-forward-entry-p origin world)
                  (not (equal (collection-read-word source world) 6))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-span-p source 16) (proof-span-p destination 16)
                  (proof-span-p address 8)
                  (proof-disjoint-p address (+ address 8) source (+ source 16))
                  (proof-disjoint-p address (+ address 8) destination (+ destination 16)))
             (equal (collection-read-word address after) (collection-read-word address world))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable collection-copy-cons-effect)
                  :use ((:instance collection-word-read-from-equal-memories
                                   (first (collection-trace-effect (collection-cons-forward-prefix origin) world))
                                   (second world))))))

(defthm collection-cons-forward-keeps-unclobbered-register
  (let* ((seen (equal (collection-read-word (collection-cons-source world) world) 6))
         (after (collection-trace-effect (collection-cons-forward-trace seen origin) world)))
    (implies (and (collection-cons-forward-entry-p origin world)
                  (not (member-equal register '(0 1 2 3 4 21))))
             (equal (proof-world-reg register after) (proof-world-reg register world))))
  :hints (("Goal" :cases ((equal (collection-read-word (collection-cons-source world) world) 6))
                  :in-theory (enable collection-copy-cons-effect collection-forward-trace
                                     collection-trace-effect))))
