(in-package "BOYMOO-PROOFS")

(include-book "exactness")
(include-book "fixed-calls")

(logic)
(set-verify-guards-eagerness 0)

; An external header has a mark word immediately before it.
(defun collection-external-mark-p (header work world)
  (equal (collection-read-word (- header 8) world)
         (if (assoc-equal header (collection-forwarding work)) 1 0)))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc
                     proof-heap-p proof-reg proof-load-word proof-span-p
                     proof-heap-base proof-header-size proof-header-type
                     proof-align-up proof-spaces-end proof-stack-base proof-stack-end
                     proof-machine-limit proof-world-regions proof-region
                     proof-pointer-address collection-read-word collection-write-word
                     collection-cpu-p collection-fixed-forward-kind collection-fixed-forward-trace
                     collection-trace-effect collection-trace-ready-p
                     collection-forwarding collection-unseen collection-discover
                     boymoo-model::a64-memory boymoo-model::a64-unsigned)))

(defthm collection-external-list-headers-have-clear-marks
  (let ((mappings (proof-external-objects head fuel world objects)))
    (implies (and mappings (member-equal header (cdr mappings)))
             (equal (collection-read-word (- header 8) world) 0)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
                  :in-theory (enable collection-read-word))))

(defthm collection-unrelated-discovery-keeps-external-mark-invariant
  (implies (and (collection-external-mark-p header work before)
                (not (equal address header))
                (equal (collection-read-word (- header 8) after)
                       (collection-read-word (- header 8) before)))
           (collection-external-mark-p header (collection-discover address work) after)))

(defthm collection-assigned-external-mark-establishes-invariant
  (implies (and (or (assoc-equal header (collection-unseen work))
                    (assoc-equal header (collection-forwarding work)))
                (equal (collection-read-word (- header 8) world) 1))
           (collection-external-mark-p header (collection-discover header work) world)))

(local
 (defthm collection-mark-word-depends-on-byte-memory
   (implies (equal (boymoo-model::a64-memory (proof-world-machine first))
                   (boymoo-model::a64-memory (proof-world-machine second)))
            (equal (collection-read-word address first) (collection-read-word address second)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (collection-read-word proof-load-word)
                                   (boymoo-model::a64-read-bytes))))))

(defthm collection-checked-external-forward-preserves-exact-marks
  (let* ((kind (collection-fixed-forward-kind world))
         (address (proof-pointer-address (proof-world-reg 0 world) (proof-world-reg 28 world)))
         (mark (- address 8))
         (trace (collection-fixed-forward-trace kind origin))
         (cuts (list (proof-world-reg 30 world)))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-external-forward-kind-p kind)
                  (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) origin)
                  (implies (eq kind :external-above)
                           (proof-span-p (+ 64 (proof-world-reg 17 world)) 8))
                  (proof-span-p mark 8)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (or (assoc-equal address (collection-unseen work))
                      (assoc-equal address (collection-forwarding work)))
                  (collection-external-mark-p header work world)
                  (implies (not (equal header address))
                           (and (proof-span-p (- header 8) 8)
                                (proof-disjoint-p (- header 8) header mark address)))
                  (collection-trace-ready-p trace cuts world))
             (and (proof-segment-p (len trace) cuts world :cut after)
                  (collection-external-mark-p header (collection-discover address work) after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-checked-fixed-forward-preserves-word-and-marks-external)
                 (:instance collection-fixed-forward-returns-word-and-preserves-frontiers (register 0))
                 (:instance collection-disjoint-word-store-preserves-word
                            (address (- header 8))
                            (start (- (proof-pointer-address (proof-world-reg 0 world)
                                                             (proof-world-reg 28 world)) 8))
                            (value 1))
                 (:instance collection-mark-word-depends-on-byte-memory
                            (first (collection-trace-effect
                                    (collection-fixed-forward-trace (collection-fixed-forward-kind world)
                                                                    origin)
                                    world))
                            (second (collection-write-word
                                     (- (proof-pointer-address (proof-world-reg 0 world)
                                                               (proof-world-reg 28 world)) 8) 1 world))
                            (address (- header 8))))
           :in-theory (disable collection-fixed-forward-returns-word-and-preserves-frontiers
                               collection-disjoint-word-store-preserves-word
                               proof-segment-p))
          (and stable-under-simplificationp
               '(:in-theory (enable proof-span-p proof-disjoint-p)))))

(local
 (in-theory (disable collection-published-object-graph collection-published-roots
                     collection-traverse collection-traversal-paths
                     proof-inactive-floor proof-inactive-end collection-edge-path-p
                     collection-reverse-path-p)))

(defthm collection-marked-external-has-published-root-witness
  (let* ((graph (collection-published-object-graph
                 objects (proof-heap-base before) objects (proof-world-machine before)))
         (roots (collection-published-roots before objects))
         (lower (proof-inactive-floor before))
         (upper (proof-inactive-end before))
         (work (collection-traverse roots graph lower upper))
         (path (cdr (assoc-equal header (collection-traversal-paths roots graph lower upper)))))
    (implies (and (proof-heap-p before objects packages)
                  (collection-external-mark-p header work after)
                  (not (equal (collection-read-word (- header 8) after) 0)))
             (and (equal (car path) header)
                  (collection-reverse-path-p path roots graph))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance collection-published-forwarding-has-root-witness
                                   (world before) (address header))))))

(defthm collection-published-reachable-external-is-marked
  (let* ((graph (collection-published-object-graph
                 objects (proof-heap-base before) objects (proof-world-machine before)))
         (roots (collection-published-roots before objects))
         (lower (proof-inactive-floor before))
         (upper (proof-inactive-end before))
         (work (collection-traverse roots graph lower upper)))
    (implies (and (collection-external-mark-p header work after)
                  (member-equal (car path) roots)
                  (collection-edge-path-p path graph)
                  (member-equal header path) (assoc-equal header graph))
             (equal (collection-read-word (- header 8) after) 1)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-traversal-assigns-every-reachable-object
                            (address header)
                            (roots (collection-published-roots before objects))
                            (graph (collection-published-object-graph
                                    objects (proof-heap-base before) objects (proof-world-machine before)))
                            (lower (proof-inactive-floor before))
                            (upper (proof-inactive-end before)))))))

(defun collection-external-mark-table-p (headers work world)
  (if (endp headers)
      t
    (and (collection-external-mark-p (car headers) work world)
         (collection-external-mark-table-p (cdr headers) work world))))

(defthm collection-listed-mark-agrees-with-forwarding-entry
  (implies (and (collection-external-mark-table-p headers work world)
                (member-equal header headers))
           (collection-external-mark-p header work world))
  :rule-classes nil
  :hints (("Goal" :induct (collection-external-mark-table-p headers work world)
                  :in-theory (disable collection-external-mark-p))))

(defthm collection-unvisited-external-list-has-exact-mark-table
  (let ((mappings (proof-external-objects head fuel world objects)))
    (implies (and mappings (not (collection-forwarding work)))
             (collection-external-mark-table-p (cdr mappings) work world)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
                  :in-theory (enable collection-read-word))))

(defun collection-external-mark-spans-separate-p (headers address)
  (if (endp headers)
      t
    (let ((header (car headers)))
      (and (proof-span-p (- header 8) 8)
           (or (equal header address)
               (proof-disjoint-p (- header 8) header (- address 8) address))
           (collection-external-mark-spans-separate-p (cdr headers) address)))))

(defthm collection-checked-external-forward-maintains-mark-table
  (let* ((kind (collection-fixed-forward-kind world))
         (address (proof-pointer-address (proof-world-reg 0 world) (proof-world-reg 28 world)))
         (trace (collection-fixed-forward-trace kind origin))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-external-forward-kind-p kind)
                  (collection-cpu-p world) (proof-span-p origin 224)
                  (equal (proof-world-pc world) origin)
                  (implies (eq kind :external-above)
                           (proof-span-p (+ 64 (proof-world-reg 17 world)) 8))
                  (proof-span-p (- address 8) 8)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (or (assoc-equal address (collection-unseen work))
                      (assoc-equal address (collection-forwarding work)))
                  (collection-external-mark-spans-separate-p headers address)
                  (collection-external-mark-table-p headers work world)
                  (collection-trace-ready-p trace (list (proof-world-reg 30 world)) world))
             (collection-external-mark-table-p headers (collection-discover address work) after)))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-external-mark-table-p headers work world)
           :in-theory (disable collection-external-mark-p proof-disjoint-p proof-segment-p))
          ("Subgoal *1/2"
           :use ((:instance collection-checked-external-forward-preserves-exact-marks
                            (header (car headers)))))))
