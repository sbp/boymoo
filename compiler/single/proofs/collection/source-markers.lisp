(in-package "BOYMOO-PROOFS")

(include-book "header-copy-placement")
(include-book "marks")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-source-marker-p (source kind base work original world)
  (let* ((entry (assoc-equal source (collection-forwarding work)))
         (word (boymoo-model::a64-unsigned 64 (+ (- (cdr entry) base) (if (eq kind :cons) 0 2)))))
    (if entry
        (if (eq kind :cons)
            (and (equal (collection-read-word source world) 6)
                 (equal (collection-read-word (+ source 8) world) word))
          (equal (collection-read-word source world)
                 (boymoo-model::a64-unsigned 64 (logior #x8000000000000000 word))))
      (and (equal (collection-read-word source world) (collection-read-word source original))
           (implies (eq kind :cons)
                    (equal (collection-read-word (+ source 8) world)
                           (collection-read-word (+ source 8) original)))))))

(local
 (in-theory (disable collection-cons-source collection-header-source collection-cons-forward-entry-p
                     collection-box-forward-entry-p collection-header-payload-words collection-cons-forward-trace
                     collection-fresh-box-trace collection-forwarding collection-unseen collection-copy-bytes
                     collection-cpu-p collection-read-word proof-world-machine proof-world-reg proof-world-stop
                     proof-world-pc proof-world-regions proof-reg proof-load-word proof-covered-p proof-regions-p
                     proof-segment-p collection-trace-effect collection-trace-ready-p collection-trace-placed-p
                     collection-fresh-header-readiness-input-p
                     collection-cell-frontier collection-header-frontier boymoo-model::a64-unsigned
                     boymoo-model::a64-memory logbitp (:definition acl2::binary-logior))))

(defthm collection-unrelated-discovery-preserves-source-marker-invariant
  (implies (and (collection-source-marker-p query kind base work original before)
                (not (equal address query))
                (equal (collection-read-word query after) (collection-read-word query before))
                (implies (eq kind :cons)
                         (equal (collection-read-word (+ query 8) after)
                                (collection-read-word (+ query 8) before))))
           (collection-source-marker-p query kind base (collection-discover address work) original after)))

(defthm collection-placed-cons-discovery-establishes-source-marker-and-pending-copy
  (let* ((source (collection-cons-source world))
         (destination (- (proof-world-reg 21 world) 16))
         (base (proof-world-reg 28 world))
         (trace (collection-cons-forward-trace nil origin))
         (after (collection-trace-effect trace world))
         (work-next (collection-discover source work))
         (regions (proof-world-regions world)))
    (implies (and (collection-cons-forward-entry-p origin world)
                  (not (proof-world-stop world)) (proof-regions-p regions)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (eq (cadr (assoc-equal source (collection-unseen work))) :cons)
                  (not (assoc-equal source (collection-forwarding work)))
                  (collection-source-marker-p source :cons base work original world)
                  (not (equal (collection-read-word source original) 6))
                  (equal (proof-world-reg 20 world) (collection-header-frontier work))
                  (equal (proof-world-reg 21 world) (collection-cell-frontier work))
                  (proof-covered-p source 16 :write regions)
                  (proof-covered-p destination 16 :write regions)
                  (proof-disjoint-p source (+ source 16) destination (+ destination 16))
                  (collection-trace-placed-p trace world)
                  (not (assoc-equal (proof-world-reg 30 world) trace)))
             (and (proof-segment-p (len trace) (list (proof-world-reg 30 world)) world :cut after)
                  (collection-source-marker-p source :cons base work-next original after)
                  (equal (collection-read-word destination after) (collection-read-word source original))
                  (equal (collection-read-word (+ destination 8) after)
                         (collection-read-word (+ source 8) original))
                  (equal (proof-world-reg 20 after) (collection-header-frontier work-next))
                  (equal (proof-world-reg 21 after) (collection-cell-frontier work-next)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-placed-cons-forward-is-ready)
                 (:instance collection-checked-fresh-cons-matches-discovery)
                 (:instance collection-covered-address-is-a-span
                            (address (collection-cons-source world)) (width 16) (access :write)
                            (regions (proof-world-regions world)))
                 (:instance collection-covered-address-is-a-span
                            (address (- (proof-world-reg 21 world) 16)) (width 16) (access :write)
                            (regions (proof-world-regions world))))
           :in-theory (disable collection-discover collection-covered-address-is-a-span
                               collection-forwarding-lookup-after-discovery))))

(defthm collection-fresh-header-discovery-establishes-source-marker-and-pending-copy
  (let* ((source (collection-header-source world))
         (destination (proof-world-reg 20 world))
         (base (proof-world-reg 28 world))
         (header (collection-read-word source world))
         (count (collection-header-payload-words header))
         (bytes (+ 8 (* 8 count)))
         (trace (collection-fresh-box-trace count origin))
         (after (collection-trace-effect trace world))
         (work-next (collection-discover source work)))
    (implies (and (collection-box-forward-entry-p origin world)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (not (assoc-equal source (collection-forwarding work)))
                  (collection-source-marker-p source :header base work original world)
                  (not (logbitp 63 (collection-read-word source original)))
                  (eq (cadr (assoc-equal source (collection-unseen work))) :header)
                  (equal (collection-copy-bytes (assoc-equal source (collection-unseen work))) bytes)
                  (equal (proof-world-reg 20 world) (collection-header-frontier work))
                  (equal (proof-world-reg 21 world) (collection-cell-frontier work))
                  (unsigned-byte-p 64 (+ source bytes))
                  (unsigned-byte-p 64 (+ destination bytes))
                  (proof-disjoint-p source (+ source bytes) destination (+ destination bytes))
                  (or (collection-trace-ready-p trace (list (proof-world-reg 30 world)) world)
                      (collection-fresh-header-readiness-input-p origin world)))
             (and (proof-segment-p (len trace) (list (proof-world-reg 30 world)) world :cut after)
                  (collection-source-marker-p source :header base work-next original after)
                  (equal (collection-read-word destination after) (collection-read-word source original))
                  (implies (and (natp index) (< index count))
                           (equal (collection-read-word (+ 8 destination (* 8 index)) after)
                                  (collection-read-word (+ 8 source (* 8 index)) world)))
                  (equal (proof-world-reg 20 after) (collection-header-frontier work-next))
                  (equal (proof-world-reg 21 after) (collection-cell-frontier work-next)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-placed-fresh-header-forward-is-ready)
                 (:instance collection-checked-fresh-header-matches-discovery)
                 (:instance collection-fresh-header-call-publishes-and-copies-entire-object))
           :in-theory (disable collection-discover collection-forwarding-lookup-after-discovery))))
