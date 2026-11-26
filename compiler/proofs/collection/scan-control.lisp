(in-package "BOYMOO-PROOFS")

(include-book "scanner")
(include-book "queues")
(include-book "forward-placement")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-scan-control-p (work origin world)
  (and (collection-cpu-p world)
       (proof-span-p origin (car *collection-linux-layout*))
       (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:scan")))
       (equal (proof-world-reg 20 world) (collection-header-frontier work))
       (equal (proof-world-reg 21 world) (collection-cell-frontier work))
       (collection-scan-cursors-p (proof-world-reg 8 world) (proof-world-reg 22 world) work)))

(defun collection-scan-selection-trace (work origin)
  (collection-linux-trace "rt:scan"
                          (if (consp (collection-cell-queue work)) '(0 1) '(0 1 2 3))
                          origin))

(defun collection-scan-selection-address (work origin)
  (+ origin
     (cond ((consp (collection-cell-queue work)) (collection-linux-offset "rt:scan-cons"))
           ((consp (collection-header-queue work)) (+ 16 (collection-linux-offset "rt:scan")))
           (t (collection-linux-offset "rt:collect-finish")))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-world-machine proof-reg
                     proof-world-stop proof-instruction-at-p proof-instruction-effect
                     collection-cpu-p collection-write-pc collection-write-flags
                     collection-subtract-flags collection-forwarding collection-scan-cursors-p
                     collection-cell-queue collection-header-queue
                     collection-cell-frontier collection-header-frontier
                     boymoo-model::a64-unsigned boymoo-model::a64-nzcv boymoo-model::a64-condition
                     (:definition ash) (:definition acl2::binary-logand))))

(local
 (defthm collection-scan-control-orders-frontiers
   (implies (collection-scan-control-p work origin world)
            (and (iff (consp (collection-cell-queue work))
                      (< (proof-world-reg 21 world) (proof-world-reg 22 world)))
                 (iff (consp (collection-header-queue work))
                      (< (proof-world-reg 8 world) (proof-world-reg 20 world)))
                 (implies (consp (collection-cell-queue work))
                          (equal (assoc-equal (caar (collection-cell-queue work))
                                              (collection-forwarding work))
                                 (cons (caar (collection-cell-queue work))
                                       (- (proof-world-reg 22 world) 16))))
                 (implies (consp (collection-header-queue work))
                          (equal (assoc-equal (caar (collection-header-queue work))
                                              (collection-forwarding work))
                                 (cons (caar (collection-header-queue work))
                                       (proof-world-reg 8 world))))))
   :hints (("Goal"
            :use ((:instance collection-queue-frontiers-select-pending-scan
                             (header (proof-world-reg 8 world)) (cell (proof-world-reg 22 world))))))))

(defthm collection-machine-selects-next-queued-copy
  (let* ((trace (collection-scan-selection-trace work origin))
         (after (collection-trace-effect trace world)))
    (implies (collection-scan-control-p work origin world)
             (and (equal (proof-world-pc after) (collection-scan-selection-address work origin))
                  (equal (proof-world-reg register after) (proof-world-reg register world))
                  (implies (consp (collection-cell-queue work))
                           (equal (assoc-equal (caar (collection-cell-queue work))
                                               (collection-forwarding work))
                                  (cons (caar (collection-cell-queue work))
                                        (- (proof-world-reg 22 world) 16))))
                  (implies (and (endp (collection-cell-queue work))
                                (consp (collection-header-queue work)))
                           (equal (assoc-equal (caar (collection-header-queue work))
                                               (collection-forwarding work))
                                  (cons (caar (collection-header-queue work))
                                        (proof-world-reg 8 world)))))))
  :hints (("Goal"
           :cases ((consp (collection-cell-queue work)) (consp (collection-header-queue work)))
           :use ((:instance collection-scan-control-orders-frontiers))
           :in-theory (disable collection-scan-control-orders-frontiers))))

(local
 (defthm collection-scan-selection-actions-keep-stop
   (and (equal (proof-world-stop (collection-write-pc pc world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-flags flags world)) (proof-world-stop world)))
   :hints (("Goal" :in-theory (enable proof-world-stop collection-write-pc collection-write-flags)))))

(defthm collection-placed-scan-selection-is-ready
  (let ((trace (collection-scan-selection-trace work origin)))
    (implies (and (collection-scan-control-p work origin world)
                  (not (proof-world-stop world))
                  (collection-trace-placed-p trace world))
             (collection-trace-ready-p
              trace (list (collection-scan-selection-address work origin)) world)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((consp (collection-cell-queue work)) (consp (collection-header-queue work)))
           :use ((:instance collection-scan-control-orders-frontiers))
           :in-theory (disable collection-scan-control-orders-frontiers))))

(defthm collection-scan-control-at-next-iteration
  (let ((next (collection-scan-one work)))
    (implies (and (collection-scan-control-p work origin before)
                  (collection-cpu-p after)
                  (equal (proof-world-pc after) (proof-world-pc before))
                  (equal (proof-world-reg 8 after)
                         (collection-header-cursor-after-scan (proof-world-reg 8 before) work))
                  (equal (proof-world-reg 22 after)
                         (collection-cons-cursor-after-scan (proof-world-reg 22 before) work))
                  (equal (proof-world-reg 20 after) (collection-header-frontier next))
                  (equal (proof-world-reg 21 after) (collection-cell-frontier next)))
             (collection-scan-control-p next origin after)))
  :hints (("Goal"
           :use ((:instance collection-scan-one-preserves-pending-span-layout
                            (header (proof-world-reg 8 before)) (cell (proof-world-reg 22 before))))
           :in-theory (disable collection-scan-one-preserves-pending-span-layout
                               collection-header-cursor-after-scan collection-cons-cursor-after-scan))))
