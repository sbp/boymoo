(in-package "BOYMOO-PROOFS")

(include-book "large-flow")
(include-book "mapping")
(include-book "frame-composition")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defconst *allocation-large-map-setup*
  (append *allocation-large-map-path* *allocation-map-setup-path*))

(defconst *allocation-map-svc-instruction* (nth 7 *allocation-map-code*))

(assert-event (equal *allocation-map-svc-instruction* '(:svc 0)))

(defconst *allocation-large-map-call*
  (append *allocation-large-map-setup* (list *allocation-map-svc-instruction*) *allocation-map-return-path*))

(defconst *allocation-large-map-clobbers* '(0 1 2 3 4 5 8 30))

(defund allocation-large-map-entry-p (origin world)
  (and (allocation-code-origin-p origin)
       (allocation-machine-state-p world)
       (not (proof-world-stop world))
       (equal (proof-world-pc world) (allocation-code-address "rt:map-string" origin))))

(defthm allocation-large-map-call-sets-up-svc
  (implies (and (allocation-large-map-entry-p origin before)
                (equal svc (allocation-path-end *allocation-large-map-setup* before)))
           (and (allocation-map-svc-arguments-p (proof-world-reg 20 before) svc)
                (equal (proof-world-pc svc) (+ 28 (allocation-code-address "sys:map" origin)))
                (< (+ 4 (proof-world-pc svc)) *allocation-word-modulus*)
                (equal (proof-world-reg 30 svc) (allocation-large-string-address origin 21))
                (allocation-machine-state-p svc)
                (not (proof-world-stop svc))
                (equal (allocation-sp svc) (allocation-sp before))
                (equal (allocation-memory svc) (allocation-memory before))
                (equal (proof-world-regions svc) (proof-world-regions before))
                (equal (proof-world-replies svc) (proof-world-replies before))
                (proof-streams-preserved-p before svc)
                (proof-register-frame-p 30 *allocation-large-map-clobbers* before svc)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (allocation-large-map-entry-p)
                                  (allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference)))))

(local
 (defthm allocation-sp-of-world-slot-update
   (implies (posp slot)
            (equal (allocation-sp (update-nth slot value world)) (allocation-sp world)))
   :hints (("Goal" :in-theory (e/d (allocation-sp) (allocation-read-sp-as-sp))))))

(local
 (defthm allocation-non-sp-write-makes-machine-state
   (implies (and (natp register) (< register 31))
            (allocation-machine-state-p (allocation-write-reg register value world)))
   :hints (("Goal" :in-theory (enable allocation-machine-state-p allocation-write-reg proof-world-machine)))))

(local
 (defthm allocation-machine-state-of-world-slot-update
   (implies (posp slot)
            (equal (allocation-machine-state-p (update-nth slot value world))
                   (allocation-machine-state-p world)))
   :hints (("Goal" :in-theory (enable allocation-machine-state-p)))))

(local
 (defthm allocation-register-frame-of-world-slot-update
   (implies (posp slot)
            (equal (proof-register-frame-p register clobbers before (update-nth slot value world))
                   (proof-register-frame-p register clobbers before world)))
   :hints (("Goal" :induct (proof-register-frame-p register clobbers before world)
            :expand ((:free (after) (proof-register-frame-p register clobbers before after)))
            :in-theory (enable (:induction proof-register-frame-p))))))

(local
 (defthm allocation-register-frame-of-clear-span
   (equal (proof-register-frame-p register clobbers before (proof-clear-span start end world))
          (proof-register-frame-p register clobbers before world))
   :hints (("Goal" :induct (proof-register-frame-p register clobbers before world)
            :expand ((:free (after) (proof-register-frame-p register clobbers before after)))
            :in-theory (e/d ((:induction proof-register-frame-p)) (proof-clear-span))))))

(local
 (defthm allocation-register-frame-of-svc-return
   (implies (member-equal 0 clobbers)
            (equal (proof-register-frame-p register clobbers before (proof-svc-return reply world))
                   (proof-register-frame-p register clobbers before world)))
   :hints (("Goal" :in-theory (enable proof-svc-return)))))

(local
 (defthm allocation-svc-return-machine-frame
   (and (allocation-machine-state-p (proof-svc-return reply world))
        (equal (allocation-sp (proof-svc-return reply world)) (allocation-sp world))
        (proof-streams-preserved-p world (proof-svc-return reply world))
        (proof-register-frame-p 30 '(0) world (proof-svc-return reply world)))
   :hints (("Goal" :in-theory (enable proof-svc-return proof-register-frame-p proof-world-input
                                     proof-world-stdout proof-world-stderr proof-world-page-size)))))

(local
 (defthm allocation-clear-span-machine-frame
   (and (equal (allocation-sp (proof-clear-span start end world)) (allocation-sp world))
        (proof-streams-preserved-p world (proof-clear-span start end world)))
   :hints (("Goal" :in-theory (e/d (proof-clear-span allocation-sp proof-world-machine
                                  boymoo-model::a64-sp
                                  proof-world-input proof-world-stdout proof-world-stderr proof-world-page-size)
                                  (allocation-read-sp-as-sp allocation-clear-span-preserves-cpu-and-replies))))))

(local
 (defthm allocation-region-replacement-machine-frame
   (proof-streams-preserved-p world (update-nth 1 regions world))
   :hints (("Goal" :in-theory (enable proof-world-input proof-world-stdout
                                     proof-world-stderr proof-world-page-size)))))

(local
 (defthm allocation-map-stream-frame-transitive
   (implies (and (proof-streams-preserved-p before middle)
                 (proof-streams-preserved-p middle after))
            (proof-streams-preserved-p before after))
   :rule-classes nil))

(local
 (defthm allocation-map-success-machine-frame
   (let ((after (allocation-map-success-world reply size before)))
     (and (allocation-machine-state-p after)
          (equal (allocation-sp after) (allocation-sp before))
          (proof-streams-preserved-p before after)
          (proof-register-frame-p 30 '(0) before after)))
   :hints (("Goal"
            :use ((:instance allocation-map-stream-frame-transitive
                   (middle (proof-clear-span reply (+ reply size) before))
                   (after (update-nth 1 (cons (proof-region reply (+ reply size) :rw) (proof-world-regions before))
                                      (proof-clear-span reply (+ reply size) before))))
                  (:instance allocation-map-stream-frame-transitive
                   (middle (update-nth 1 (cons (proof-region reply (+ reply size) :rw) (proof-world-regions before))
                                       (proof-clear-span reply (+ reply size) before)))
                   (after (allocation-map-success-world reply size before))))
            :in-theory (disable proof-streams-preserved-p proof-clear-span proof-svc-return allocation-svc-return-effect
                                proof-register-frame-p update-nth)))))

(defund allocation-large-map-reply-p (reply before)
  (or (proof-linux-errno-p reply)
      (allocation-map-admissible-success-p reply (proof-world-reg 20 before) before)))

(defun allocation-large-map-result (reply)
  (if (proof-linux-errno-p reply) 0 reply))

(defund allocation-map-resume-p (reply size before after)
  (and (allocation-machine-state-p after)
       (not (proof-world-stop after))
       (equal (allocation-sp after) (allocation-sp before))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
       (equal (proof-world-replies after) (cdr (proof-world-replies before)))
       (proof-streams-preserved-p before after)
       (proof-register-frame-p 30 '(0) before after)
       (if (proof-linux-errno-p reply)
           (and (equal (proof-world-reg 0 after) (+ *allocation-word-modulus* reply))
                (equal (allocation-memory after) (allocation-memory before))
                (equal (proof-world-regions after) (proof-world-regions before)))
         (and (equal (proof-world-reg 0 after) reply)
              (equal (allocation-memory after)
                     (proof-clear-memory reply (+ reply size) (allocation-memory before)))
              (equal (proof-world-regions after)
                     (cons (proof-region reply (+ reply size) :rw) (proof-world-regions before)))))))

(local
 (defthm allocation-map-success-and-refusal-differ
   (not (equal (allocation-map-success-world reply size world) (proof-svc-return reply world)))
   :hints (("Goal"
            :use ((:instance allocation-map-success-is-cleared (before world)))
            :in-theory (disable allocation-map-success-world proof-svc-return allocation-svc-return-effect
                                allocation-map-success-is-cleared proof-clear-memory)))))

(local
 (defthm allocation-admissible-map-reply-is-positive
   (implies (allocation-map-admissible-success-p reply size world)
            (and (integerp reply) (< 0 reply)))
   :rule-classes :forward-chaining))

(local
 (defthm allocation-admissible-map-reply-fits-signed-word
   (implies (and (allocation-map-admissible-success-p reply size world) (posp size))
            (< reply (expt 2 63)))
   :rule-classes :forward-chaining))

(defthm allocation-map-svc-admitted-resume
  (let ((reply (car (proof-world-replies before))))
    (implies (and (allocation-map-svc-arguments-p size before)
                  (proof-page-size-p (proof-world-page-size before))
                  (posp size) (equal (mod size *proof-runtime-page*) 0)
                  (consp (proof-world-replies before))
                  (not (proof-world-stop before))
                  (or (proof-linux-errno-p reply) (allocation-map-admissible-success-p reply size before))
                  (equal after (allocation-path-end (list *allocation-map-svc-instruction*) before)))
             (allocation-map-resume-p reply size before after)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((proof-linux-errno-p (car (proof-world-replies before))))
           :use (allocation-map-svc-success-effect allocation-map-svc-error-effect
                 (:instance allocation-map-success-machine-frame (reply (car (proof-world-replies before))))
                 (:instance allocation-svc-return-machine-frame (reply (car (proof-world-replies before))) (world before)))
           :in-theory (e/d (allocation-map-resume-p)
                           (allocation-svc-effect allocation-svc-return-effect
                            allocation-map-success-world allocation-map-admissible-success-p proof-svc-return proof-clear-memory
                            proof-page-size-p proof-register-frame-p
                            proof-streams-preserved-p allocation-map-svc-arguments-p mod)))))

(defund allocation-large-map-call-result-p (before after)
  (let ((reply (car (proof-world-replies before)))
        (size (proof-world-reg 20 before)))
    (and (allocation-machine-state-p after)
         (not (proof-world-stop after))
         (equal (allocation-sp after) (allocation-sp before))
         (equal (proof-world-replies after) (cdr (proof-world-replies before)))
         (equal (proof-world-reg 0 after) (allocation-large-map-result reply))
         (proof-streams-preserved-p before after)
         (proof-register-frame-p 30 *allocation-large-map-clobbers* before after)
         (if (proof-linux-errno-p reply)
             (and (equal (allocation-memory after) (allocation-memory before))
                  (equal (proof-world-regions after) (proof-world-regions before)))
           (and (equal (allocation-memory after)
                       (proof-clear-memory reply (+ reply size) (allocation-memory before)))
                (equal (proof-world-regions after)
                       (cons (proof-region reply (+ reply size) :rw) (proof-world-regions before))))))))

(local
 (defthm allocation-map-tail-keeps-state
   (implies (allocation-machine-state-p world)
            (allocation-machine-state-p (allocation-path-end *allocation-map-return-path* world)))))

(defthm allocation-large-map-call-effects
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before)))
    (implies (and (allocation-large-map-entry-p origin before)
                  (consp (proof-world-replies before))
                  (proof-page-size-p (proof-world-page-size before))
                  (posp size) (equal (mod size *proof-runtime-page*) 0)
                  (allocation-large-map-reply-p reply before)
                  (equal svc (allocation-path-end *allocation-large-map-setup* before))
                  (equal resumed (allocation-path-end (list *allocation-map-svc-instruction*) svc))
                  (equal after (allocation-path-end *allocation-map-return-path* resumed)))
             (and (equal (proof-world-pc after) (allocation-large-string-address origin 21))
                  (allocation-large-map-call-result-p before after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-map-call-sets-up-svc
                 (:instance allocation-map-svc-admitted-resume
                  (size (proof-world-reg 20 before)) (before svc) (after resumed))
                 (:instance allocation-map-tail-machine-return (before resumed))
                 (:instance allocation-register-frame-transitive
                  (middle svc) (after resumed) (register 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-transitive
                  (middle resumed) (register 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-under-more-clobbers
                  (before svc) (after resumed) (register 30) (small '(0)) (large *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-under-more-clobbers
                  (before resumed) (register 30) (small '(0)) (large *allocation-large-map-clobbers*)))
           :in-theory (e/d (allocation-large-map-reply-p allocation-large-map-call-result-p allocation-map-resume-p)
                           (allocation-path-end proof-register-frame-p
                            proof-page-size-p proof-region-disjoint-p proof-clear-memory mod)))))

(local
 (defthm allocation-large-map-call-splits-into-stages
   (let ((svc (allocation-path-end *allocation-large-map-setup* before)))
     (equal (allocation-path-end *allocation-large-map-call* before)
            (allocation-path-end *allocation-map-return-path*
                                 (allocation-path-end (list *allocation-map-svc-instruction*) svc))))
   :hints (("Goal"
            :use ((:instance allocation-path-end-of-append
                   (first *allocation-large-map-setup*)
                   (last (cons *allocation-map-svc-instruction* *allocation-map-return-path*))
                   (world before))
                  (:instance allocation-path-end-of-append
                   (first (list *allocation-map-svc-instruction*)) (last *allocation-map-return-path*)
                   (world (allocation-path-end *allocation-large-map-setup* before))))
            :in-theory (disable allocation-path-end allocation-path-end-of-append)))))

(defthm allocation-large-map-path-effects
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before)))
    (implies (and (allocation-large-map-entry-p origin before)
                  (consp (proof-world-replies before))
                  (proof-page-size-p (proof-world-page-size before))
                  (posp size) (equal (mod size *proof-runtime-page*) 0)
                  (allocation-large-map-reply-p reply before)
                  (equal after (allocation-path-end *allocation-large-map-call* before)))
             (and (equal (proof-world-pc after) (allocation-large-string-address origin 21))
                  (allocation-large-map-call-result-p before after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-map-call-effects
                  (svc (allocation-path-end *allocation-large-map-setup* before))
                  (resumed (allocation-path-end (list *allocation-map-svc-instruction*)
                                               (allocation-path-end *allocation-large-map-setup* before)))))
           :in-theory (disable allocation-path-end proof-page-size-p mod))))

(defthm allocation-large-checked-return-from-map-call
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before))
         (cuts (list (allocation-large-string-address origin 21))))
    (implies (and (allocation-large-map-entry-p origin before)
                  (consp (proof-world-replies before))
                  (proof-page-size-p (proof-world-page-size before))
                  (posp size) (equal (mod size *proof-runtime-page*) 0)
                  (allocation-large-map-reply-p reply before)
                  (allocation-path-ready-p *allocation-large-map-call* cuts before)
                  (equal after (allocation-path-end *allocation-large-map-call* before)))
             (and (proof-segment-p (len *allocation-large-map-call*) cuts before :cut after)
                  (equal (proof-world-pc after) (allocation-large-string-address origin 21))
                  (allocation-large-map-call-result-p before after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-map-path-effects
                 (:instance allocation-checked-cut
                  (instructions *allocation-large-map-call*) (world before)
                  (cuts (list (allocation-large-string-address origin 21)))))
           :in-theory (e/d (allocation-large-map-call-result-p)
                           (allocation-path-end allocation-path-ready-p allocation-checked-cut proof-segment-p
                            proof-register-frame-p proof-page-size-p mod)))))

(local
 (defthm allocation-large-map-refusal-target
   (implies (and (allocation-code-origin-p origin)
                 (allocation-machine-state-p world)
                 (equal (proof-world-pc world) (allocation-large-string-address origin 21))
                 (equal (proof-world-reg 0 world) 0))
            (equal (proof-world-pc (allocation-path-end (list *allocation-large-map-test*) world))
                   (allocation-code-address (proof-resource-label :mapping) origin)))
   :rule-classes nil))

(defthm allocation-large-checked-map-refusal-exits
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before))
         (test (list *allocation-large-map-test*))
         (path (append *allocation-large-map-call* test))
         (stop (allocation-code-address (proof-resource-label :mapping) origin))
         (cuts (list stop)))
    (implies (and (allocation-large-map-entry-p origin before)
                  (consp (proof-world-replies before)) (proof-linux-errno-p reply)
                  (proof-page-size-p (proof-world-page-size before))
                  (posp size) (equal (mod size *proof-runtime-page*) 0)
                  (allocation-path-ready-p *allocation-large-map-call* cuts before)
                  (equal returned (allocation-path-end *allocation-large-map-call* before))
                  (allocation-path-ready-p test cuts returned)
                  (equal cut (allocation-path-end test returned))
                  (natp stop-steps)
                  (proof-segment-p stop-steps nil cut '(:exit . 3) after)
                  (null (proof-world-stdout after)))
             (and (equal (proof-world-pc cut) stop)
                  (proof-segment-p (+ (len path) stop-steps) nil before '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-map-path-effects (after returned))
                 (:instance allocation-path-end-of-append
                  (first *allocation-large-map-call*) (last (list *allocation-large-map-test*)) (world before))
                 (:instance allocation-path-ready-of-append
                  (first *allocation-large-map-call*) (last (list *allocation-large-map-test*)) (world before)
                  (cuts (list (allocation-code-address (proof-resource-label :mapping) origin))))
                 (:instance allocation-path-then-resource-exit
                  (path (append *allocation-large-map-call* (list *allocation-large-map-test*)))
                  (cuts (list (allocation-code-address (proof-resource-label :mapping) origin))))
                 (:instance allocation-large-map-refusal-target (world returned)))
           :in-theory (e/d (allocation-large-map-entry-p allocation-large-map-reply-p allocation-large-map-call-result-p)
                           (allocation-path-end allocation-path-end-of-append allocation-path-ready-of-append
                            allocation-path-ready-p proof-segment-p proof-resource-observation-p
                            proof-page-size-p proof-linux-errno-p proof-register-frame-p mod)))))

(defthm allocation-large-unrepresentable-request-exits
  (let* ((length (proof-world-reg 0 before))
         (stop (allocation-code-address (proof-resource-label :string-size) origin))
         (cuts (list stop)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-large-string-address origin 0))
                  (<= *proof-space-size* length)
                  (allocation-path-ready-p *allocation-large-size-path* cuts before)
                  (equal cut (allocation-path-end *allocation-large-size-path* before))
                  (natp stop-steps)
                  (proof-segment-p stop-steps nil cut '(:exit . 3) after)
                  (null (proof-world-stdout after)))
             (and (equal (proof-world-pc cut) stop)
                  (proof-resource-bound-p :string-size length before)
                  (proof-segment-p (+ (len *allocation-large-size-path*) stop-steps) nil before '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-size-machine-edge
                 (:instance allocation-path-then-resource-exit
                  (path *allocation-large-size-path*)
                  (cuts (list (allocation-code-address (proof-resource-label :string-size) origin)))))
           :in-theory (disable allocation-path-end allocation-path-ready-p proof-segment-p proof-resource-observation-p))))
