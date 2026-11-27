(in-package "BOYMOO-PROOFS")

(include-book "scan-control")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-scan-pending-p (work)
  (or (consp (collection-cell-queue work)) (consp (collection-header-queue work))))

(defun collection-scan-script-trace (bodies work origin)
  (declare (xargs :measure (acl2-count bodies)))
  (let ((selection (collection-scan-selection-trace work origin)))
    (if (and (collection-scan-pending-p work) (consp bodies))
        (append selection (car bodies)
                (collection-scan-script-trace (cdr bodies) (collection-scan-one work) origin))
      selection)))

; The object body starts at the instruction selected at the scan label.
; Its local obligations are to return to that label, advance the cursor
; of the selected queue and establish the two new allocation frontiers.
(defun collection-scan-body-post-p (work before after)
  (let ((next (collection-scan-one work)))
    (and (collection-cpu-p after)
         (equal (proof-world-pc after) (proof-world-pc before))
         (equal (proof-world-reg 8 after)
                (collection-header-cursor-after-scan (proof-world-reg 8 before) work))
         (equal (proof-world-reg 22 after)
                (collection-cons-cursor-after-scan (proof-world-reg 22 before) work))
         (equal (proof-world-reg 20 after) (collection-header-frontier next))
         (equal (proof-world-reg 21 after) (collection-cell-frontier next)))))

(defun collection-scan-script-input-p (bodies work origin world)
  (declare (xargs :measure (acl2-count bodies)))
  (let ((selection (collection-scan-selection-trace work origin)))
    (and (not (proof-world-stop world))
         (collection-trace-placed-p selection world)
         (if (collection-scan-pending-p work)
             (and (consp bodies)
                  (let* ((selected (collection-trace-effect selection world))
                         (body (car bodies))
                         (after (collection-trace-effect body selected)))
                    (and (collection-trace-ready-p
                          body (list (+ origin (collection-linux-offset "rt:scan"))) selected)
                         (not (assoc-equal (+ origin (collection-linux-offset "rt:collect-finish")) body))
                         (collection-scan-body-post-p work world after)
                         (collection-scan-script-input-p (cdr bodies) (collection-scan-one work)
                                                         origin after))))
           (endp bodies)))))

(local
 (in-theory (disable collection-scan-control-p collection-scan-body-post-p collection-scan-selection-address
                     collection-scan-selection-trace collection-scan-pending-p collection-trace-effect
                     collection-trace-ready-p collection-trace-placed-p proof-world-pc proof-world-stop
                     proof-world-reg collection-cpu-p collection-cell-queue collection-header-queue
                     collection-header-frontier collection-cell-frontier collection-scan-cursors-p
                     collection-header-cursor-after-scan collection-cons-cursor-after-scan)))

(defthm collection-script-length-bounded-by-original-scan-work
  (implies (collection-scan-script-input-p bodies work origin world)
           (<= (len bodies) (collection-work-size work)))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-scan-script-input-p bodies work origin world)
           :in-theory (enable collection-scan-pending-p))))

(local
 (defthm collection-only-finish-selection-goes-to-finish-address
   (equal (collection-scan-selection-address work origin)
          (+ origin (if (consp (collection-cell-queue work))
                        (collection-linux-offset "rt:scan-cons")
                      (if (consp (collection-header-queue work))
                          (+ 16 (collection-linux-offset "rt:scan"))
                        (collection-linux-offset "rt:collect-finish")))))
   :hints (("Goal" :in-theory (enable collection-scan-selection-address)))))

(local
 (defthm collection-scan-selection-excludes-finish-address
   (not (member-equal (+ origin (collection-linux-offset "rt:collect-finish"))
                      (strip-cars (collection-scan-selection-trace work origin))))
   :hints (("Goal" :in-theory (enable collection-scan-selection-trace)))))

(local
 (defthm collection-address-occurs-in-trace-exactly-if-it-has-an-instruction
   (implies address
            (iff (member-equal address (strip-cars trace)) (assoc-equal address trace)))
   :hints (("Goal" :induct (assoc-equal address trace)))))

(local
 (defthm collection-single-cut-intersects-through-membership
   (iff (intersectp-equal addresses (list cut)) (member-equal cut addresses))
   :hints (("Goal" :induct (len addresses)))))

(local
 (defthm collection-checked-scan-round-prepares-next-control
   (let* ((selected (collection-trace-effect (collection-scan-selection-trace work origin) world))
          (after (collection-trace-effect body selected)))
     (implies (and (collection-scan-control-p work origin world)
                   (collection-scan-body-post-p work world after))
              (collection-scan-control-p (collection-scan-one work) origin after)))
   :hints (("Goal" :in-theory (enable collection-scan-body-post-p)))))

(local
 (defthm collection-checked-scan-round-composes-with-suffix
   (let* ((end (list (+ origin (collection-linux-offset "rt:collect-finish"))))
          (selection (collection-scan-selection-trace work origin))
          (selected (collection-trace-effect selection world))
          (after (collection-trace-effect body selected)))
     (implies (and (collection-scan-control-p work origin world)
                   (not (proof-world-stop world))
                   (collection-trace-placed-p selection world)
                   (collection-trace-ready-p body (list (+ origin (collection-linux-offset "rt:scan"))) selected)
                   (not (assoc-equal (car end) body))
                   (collection-trace-ready-p suffix end after))
              (collection-trace-ready-p (append selection body suffix) end world)))
   :hints (("Goal"
            :use ((:instance collection-placed-scan-selection-is-ready)
                  (:instance collection-scan-selection-excludes-finish-address)
                  (:instance collection-ready-trace-of-append
                             (first body) (second suffix)
                             (first-cut (list (+ origin (collection-linux-offset "rt:scan"))))
                             (cuts (list (+ origin (collection-linux-offset "rt:collect-finish"))))
                             (world (collection-trace-effect (collection-scan-selection-trace work origin) world)))
                  (:instance collection-ready-trace-of-append
                             (first (collection-scan-selection-trace work origin))
                             (second (append body suffix))
                             (first-cut (list (collection-scan-selection-address work origin)))
                             (cuts (list (+ origin (collection-linux-offset "rt:collect-finish"))))))
            :in-theory (disable collection-ready-trace-of-append
                                collection-scan-selection-excludes-finish-address)))))

(defthm collection-admitted-scan-script-gives-ready-trace
  (implies (and (collection-scan-script-input-p bodies work origin world)
                (collection-scan-control-p work origin world))
           (collection-trace-ready-p (collection-scan-script-trace bodies work origin)
                                     (list (+ origin (collection-linux-offset "rt:collect-finish"))) world))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-scan-script-input-p bodies work origin world)
           :in-theory (disable collection-checked-scan-round-composes-with-suffix
                               collection-checked-scan-round-prepares-next-control))
          ("Subgoal *1/1"
           :use ((:instance collection-checked-scan-round-prepares-next-control (body (car bodies)))
                 (:instance collection-checked-scan-round-composes-with-suffix
                            (body (car bodies))
                            (suffix (collection-scan-script-trace (cdr bodies) (collection-scan-one work) origin)))))
          ("Subgoal *1/6"
           :use ((:instance collection-placed-scan-selection-is-ready))
           :in-theory (enable collection-scan-pending-p))))

(defthm collection-checked-scan-script-reaches-finish
  (let ((trace (collection-scan-script-trace bodies work origin)))
    (implies (and (collection-scan-script-input-p bodies work origin world)
                  (collection-scan-control-p work origin world))
             (proof-segment-p (len trace) (list (+ origin (collection-linux-offset "rt:collect-finish")))
                              world :cut (collection-trace-effect trace world))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-admitted-scan-script-gives-ready-trace)
                 (:instance collection-ready-trace-reaches-cut
                            (trace (collection-scan-script-trace bodies work origin))
                            (cuts (list (+ origin (collection-linux-offset "rt:collect-finish"))))))
           :in-theory (disable collection-scan-script-trace collection-scan-script-input-p proof-segment-p))))

(local
 (defthm collection-empty-scan-selection-keeps-final-cursors
   (let ((after (collection-trace-effect (collection-scan-selection-trace work origin) world)))
     (implies (and (collection-scan-control-p work origin world)
                   (not (collection-scan-pending-p work)))
              (and (equal (proof-world-reg 8 after) (collection-header-frontier work))
                   (equal (proof-world-reg 20 after) (collection-header-frontier work))
                   (equal (proof-world-reg 21 after) (collection-cell-frontier work))
                   (equal (proof-world-reg 22 after) (collection-cell-frontier work)))))
   :hints (("Goal"
            :use ((:instance collection-machine-selects-next-queued-copy (register 8))
                  (:instance collection-machine-selects-next-queued-copy (register 20))
                  (:instance collection-machine-selects-next-queued-copy (register 21))
                  (:instance collection-machine-selects-next-queued-copy (register 22)))
            :in-theory (e/d (collection-scan-control-p collection-scan-pending-p
                                                       collection-scan-cursors-p collection-queued-spans-p
                                                       collection-queue-frontier)
                             (collection-machine-selects-next-queued-copy))))))

(defthm collection-scan-script-finishes-at-abstract-allocation-frontiers
  (let* ((after (collection-trace-effect (collection-scan-script-trace bodies work origin) world))
         (done (collection-finish-scan work)))
    (implies (and (collection-scan-control-p work origin world)
                  (collection-scan-script-input-p bodies work origin world))
             (and (equal (proof-world-reg 8 after) (collection-header-frontier done))
                  (equal (proof-world-reg 20 after) (collection-header-frontier done))
                  (equal (proof-world-reg 21 after) (collection-cell-frontier done))
                  (equal (proof-world-reg 22 after) (collection-cell-frontier done)))))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-scan-script-input-p bodies work origin world)
           :in-theory (disable collection-finish-scan collection-empty-scan-selection-keeps-final-cursors
                               collection-checked-scan-round-prepares-next-control))
          ("Subgoal *1/1"
           :expand ((collection-finish-scan work))
           :in-theory (enable collection-scan-pending-p)
           :use ((:instance collection-checked-scan-round-prepares-next-control (body (car bodies)))))
          ("Subgoal *1/6"
           :expand ((collection-finish-scan work))
           :in-theory (enable collection-scan-pending-p)
           :use ((:instance collection-empty-scan-selection-keeps-final-cursors)))))
