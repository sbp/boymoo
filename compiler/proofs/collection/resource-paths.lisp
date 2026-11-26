(in-package "BOYMOO-PROOFS")

(include-book "entry")
(include-book "diagnostics")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-size-diagnostic-admitted-p (kind origin world)
  (let* ((replies (proof-world-replies world))
         (count (collection-size-message-length kind))
         (trace (collection-size-diagnostic-prefix kind replies origin))
         (exit-call (+ origin (collection-linux-offset "sys:exit") 4)))
    (and (collection-size-diagnostic-input-p kind origin world)
         (collection-diagnostic-replies-p count replies)
         (collection-diagnostic-replies-p 1 (collection-diagnostic-replies-after count replies))
         (collection-trace-ready-p trace (list exit-call) world)
         (proof-instruction-at-p '(:svc 0) exit-call (collection-trace-effect trace world))
         (null (proof-world-stdout world)))))

(defun collection-size-stop-count (branch kind origin world)
  (let ((entered (collection-trace-effect branch world)))
    (+ (len branch) 1
       (len (collection-size-diagnostic-prefix kind (proof-world-replies entered) origin)))))

(defun collection-size-stop-world (branch kind origin world)
  (let* ((entered (collection-trace-effect branch world))
         (trace (collection-size-diagnostic-prefix kind (proof-world-replies entered) origin)))
    (proof-step (collection-trace-effect trace entered))))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-world-replies proof-world-stdout proof-instruction-at-p
                     proof-world-exit proof-step proof-run proof-advance proof-segment-p
                     proof-resource-observation-p proof-resource-bound-p
                     collection-trace-effect collection-trace-ready-p collection-prefix-p
                     collection-size-diagnostic-input-p collection-size-diagnostic-prefix
                     collection-diagnostic-replies-p collection-diagnostic-replies-after
                     collection-size-message-length)))

(defthm collection-checked-size-branch-and-diagnostic-produce-resource-stop
  (let* ((entered (collection-trace-effect branch world))
         (target (+ origin (collection-linux-offset (proof-resource-label kind))))
         (after (collection-size-stop-world branch kind origin world)))
    (implies (and (collection-trace-ready-p branch (list target) world)
                  (proof-resource-bound-p kind demand entered)
                  (collection-size-diagnostic-admitted-p kind origin entered))
             (and (proof-segment-p (collection-size-stop-count branch kind origin world)
                                   nil world '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-checked-size-diagnostic-exits-with-status-three
                            (world (collection-trace-effect branch world)))
                 (:instance collection-ready-trace-gives-prefix
                            (trace branch) (cuts nil)
                            (terminal (list (+ origin (collection-linux-offset (proof-resource-label kind))))))
                 (:instance collection-run-after-prefix
                            (count (len branch)) (cuts nil)
                            (fuel (1+ (len (collection-size-diagnostic-prefix
                                           kind (proof-world-replies (collection-trace-effect branch world))
                                           origin))))))
           :in-theory (e/d (proof-segment-p)
                            (collection-ready-trace-gives-prefix collection-run-after-prefix)))))

(local
 (in-theory (disable collection-size-diagnostic-admitted-p collection-size-stop-count
                     collection-size-stop-world collection-request-test-trace
                     collection-entry-saves-frame-and-selects-request-path
                     collection-cpu-p proof-reg boymoo-model::a64-sp
                     boymoo-model::a64-memory boymoo-model::a64-unsigned)))

(defthm collection-oversized-request-path-stops
  (let* ((kind :allocation-size)
         (trace (collection-request-test-trace origin))
         (entered (collection-trace-effect trace world))
         (request (proof-world-reg 0 world))
         (after (collection-size-stop-world trace kind origin world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:collect")))
                  (<= 64 (boymoo-model::a64-sp (proof-world-machine world)))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (< *proof-space-size* request)
                  (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "rt:datum-size"))) world)
                  (collection-size-diagnostic-admitted-p kind origin entered))
             (and (proof-segment-p (collection-size-stop-count trace kind origin world) nil world '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-entry-saves-frame-and-selects-request-path (register 0))
                 (:instance collection-checked-size-branch-and-diagnostic-produce-resource-stop
                            (branch (collection-request-test-trace origin))
                            (kind :allocation-size) (demand (proof-world-reg 0 world)))))))

(defun collection-finish-capacity-trace (origin)
  (collection-linux-trace "rt:collect-finish" '(0 1 2 3 4 5 6 7 8) origin))

(defthm collection-excess-retention-path-stops
  (let* ((kind :heap-size)
         (trace (collection-finish-capacity-trace origin))
         (entered (collection-trace-effect trace world))
         (after (collection-size-stop-world trace kind origin world))
         (metadata (proof-world-reg 17 world))
         (floor (collection-read-word (+ metadata 24) world))
         (end (collection-read-word (+ metadata 32) world))
         (box (proof-world-reg 20 world))
         (cells (proof-world-reg 21 world))
         (request (collection-read-word (boymoo-model::a64-sp (proof-world-machine world)) world))
         (demand (+ (collection-retained-bytes floor box cells end) request)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:collect-finish")))
                  (equal end (+ floor *proof-space-size*))
                  (<= floor box) (<= box cells) (<= cells end)
                  (<= request *proof-space-size*) (< *proof-space-size* demand)
                  (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "rt:heap-size"))) world)
                  (collection-size-diagnostic-admitted-p kind origin entered))
             (and (proof-segment-p (collection-size-stop-count trace kind origin world) nil world '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-finish-tests-capacity)
                 (:instance collection-checked-size-branch-and-diagnostic-produce-resource-stop
                            (branch (collection-finish-capacity-trace origin))
                            (kind :heap-size)
                            (demand (+ (collection-retained-bytes
                                        (collection-read-word (+ (proof-world-reg 17 world) 24) world)
                                        (proof-world-reg 20 world) (proof-world-reg 21 world)
                                        (collection-read-word (+ (proof-world-reg 17 world) 32) world))
                                       (collection-read-word (boymoo-model::a64-sp (proof-world-machine world)) world)))))
           :in-theory (enable proof-resource-bound-p))))
