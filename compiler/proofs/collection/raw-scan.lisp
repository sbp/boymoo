(in-package "BOYMOO-PROOFS")

(include-book "scan-traversal")
(include-book "header-calls")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-open-scan-header-trace (origin)
  (collection-linux-trace "rt:scan" '(4 5 6 7 8 9 10) origin))

(defun collection-skip-raw-fields-trace (type origin)
  (collection-linux-trace "rt:scan"
                          (if (equal type 1) '(11 12) '(11 12 13 14)) origin))

(defun collection-raw-header-scan-trace (type origin)
  (append (collection-open-scan-header-trace origin)
          (collection-skip-raw-fields-trace type origin)))

(local
 (defthm collection-raw-scan-load-at-header-cursor
   (equal (proof-instruction-access-p (list :single 1 8 8 9 :offset 0) world)
          (proof-covered-p (proof-world-reg 8 world) 8 :read (proof-world-regions world)))
   :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-unsigned)))))

(local
 (defthm collection-raw-scan-actions-keep-stop
   (and (equal (proof-world-stop (collection-write-register register value world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-flags flags world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-pc address world)) (proof-world-stop world)))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned (:definition ash)
                                       (:definition acl2::binary-logand))))))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-world-regions proof-reg proof-instruction-effect proof-instruction-at-p
                     proof-covered-p proof-load-word proof-header-size proof-header-type
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-flags collection-subtract-flags
                     boymoo-model::a64-unsigned boymoo-model::a64-memory boymoo-model::a64-condition
                     boymoo-model::a64-nzcv (:definition ash) (:definition acl2::binary-logand))))

(local
 (defthm collection-raw-scan-placement-of-append
   (equal (collection-trace-placed-p (append first second) world)
          (and (collection-trace-placed-p first world) (collection-trace-placed-p second world)))
   :hints (("Goal" :induct (append first second)))))

(local
 (defthm collection-raw-scan-open-has-no-scan-cutpoint
   (not (intersectp-equal
         (strip-cars (collection-open-scan-header-trace origin))
         (list (+ origin (collection-linux-offset "rt:scan")))))))

(local
 (defthm collection-open-placed-header-is-ready
   (let* ((trace (collection-open-scan-header-trace origin))
          (scan (+ origin (collection-linux-offset "rt:scan")))
          (address (proof-world-reg 8 world)))
     (implies (and (collection-cpu-p world) (not (proof-world-stop world))
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ scan 16))
                   (proof-covered-p address 8 :read (proof-world-regions world))
                   (collection-trace-placed-p trace world))
              (collection-trace-ready-p trace (list (+ scan 44)) world)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable collection-covered-address-is-a-span)))))

(local
 (defthm collection-open-scan-header-keeps-code-and-metadata
   (let ((next (collection-trace-effect (collection-open-scan-header-trace origin) world)))
     (implies (collection-cpu-p world)
              (and (collection-cpu-p next)
                   (equal (proof-world-stop next) (proof-world-stop world))
                   (equal (boymoo-model::a64-memory (proof-world-machine next))
                          (boymoo-model::a64-memory (proof-world-machine world)))
                   (implies (not (member-equal register '(8 9 10 11)))
                            (equal (proof-world-reg register next) (proof-world-reg register world)))
                   (equal (collection-trace-placed-p trace next)
                          (collection-trace-placed-p trace world)))))
   :hints (("Goal" :induct (collection-trace-placed-p trace world)))))

(local
 (defthm collection-placed-raw-header-skip-is-ready
   (let* ((trace (collection-skip-raw-fields-trace type origin))
          (next (collection-trace-effect trace world))
          (scan (+ origin (collection-linux-offset "rt:scan"))))
     (implies (and (collection-cpu-p world) (not (proof-world-stop world))
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ scan 44))
                   (equal (proof-world-reg 10 world) type)
                   (member-equal type '(1 3))
                   (collection-trace-placed-p trace world))
              (and (collection-trace-ready-p trace (list scan) world)
                   (collection-cpu-p next)
                   (equal (proof-world-pc next) scan)
                   (equal (proof-world-reg register next) (proof-world-reg register world))
                   (equal (boymoo-model::a64-memory (proof-world-machine next))
                          (boymoo-model::a64-memory (proof-world-machine world))))))
   :rule-classes nil
   :hints (("Goal" :cases ((equal type 1))))))

(local
 (in-theory (disable collection-open-scan-header-trace collection-skip-raw-fields-trace
                     collection-trace-placed-p collection-trace-ready-p collection-trace-effect)))

(local
 (defthm collection-open-scan-header-sets-payload-cursor
   (let* ((address (proof-world-reg 8 world))
          (header (collection-read-word address world))
          (end (+ address 8 (ash (collection-header-payload-words header) 3)))
          (scan (+ origin (collection-linux-offset "rt:scan")))
          (next (collection-trace-effect (collection-open-scan-header-trace origin) world)))
     (implies (and (collection-cpu-p world)
                   (proof-span-p origin (car *collection-linux-layout*))
                   (equal (proof-world-pc world) (+ scan 16))
                   (unsigned-byte-p 64 (+ 8 address)) (unsigned-byte-p 64 end))
              (and (equal (proof-world-pc next) (+ scan 44))
                   (equal (proof-world-reg 10 next)
                          (boymoo-model::a64-unsigned 64 (logand header 255)))
                   (equal (proof-world-reg 8 next) end))))
   :hints (("Goal"
            :use ((:instance collection-scan-opens-header-payload))
            :in-theory (e/d (collection-open-scan-header-trace proof-header-size)
                             (collection-scan-opens-header-payload))))))

(defthm collection-placed-raw-header-scan-advances-without-rewriting-memory
  (let* ((address (proof-world-reg 8 world))
         (header (collection-read-word address world))
         (type (boymoo-model::a64-unsigned 64 (logand header 255)))
         (end (+ address 8 (ash (collection-header-payload-words header) 3)))
         (scan (+ origin (collection-linux-offset "rt:scan")))
         (trace (collection-raw-header-scan-trace type origin))
         (next (collection-trace-effect trace world)))
    (implies (and (collection-cpu-p world) (not (proof-world-stop world))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ scan 16))
                  (member-equal type '(1 3))
                  (unsigned-byte-p 64 (+ 8 address))
                  (unsigned-byte-p 64 end)
                  (proof-covered-p address 8 :read (proof-world-regions world))
                  (collection-trace-placed-p trace world))
             (and (collection-trace-ready-p trace (list scan) world)
                  (collection-cpu-p next)
                  (equal (proof-world-pc next) scan)
                  (equal (proof-world-reg 8 next) end)
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (implies (not (member-equal register '(8 9 10 11)))
                           (equal (proof-world-reg register next) (proof-world-reg register world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-open-placed-header-is-ready)
                 (:instance collection-raw-scan-open-has-no-scan-cutpoint)
                 (:instance collection-placed-raw-header-skip-is-ready
                            (type (boymoo-model::a64-unsigned 64 (logand (collection-read-word (proof-world-reg 8 world) world) 255)))
                            (world (collection-trace-effect (collection-open-scan-header-trace origin) world)))
                 (:instance collection-placed-raw-header-skip-is-ready
                            (register 8)
                            (type (boymoo-model::a64-unsigned 64 (logand (collection-read-word (proof-world-reg 8 world) world) 255)))
                            (world (collection-trace-effect (collection-open-scan-header-trace origin) world)))
                 (:instance collection-ready-trace-of-append
                            (first (collection-open-scan-header-trace origin))
                            (second (collection-skip-raw-fields-trace
                                     (boymoo-model::a64-unsigned 64 (logand (collection-read-word (proof-world-reg 8 world) world) 255))
                                     origin))
                            (first-cut (list (+ origin (collection-linux-offset "rt:scan") 44)))
                            (cuts (list (+ origin (collection-linux-offset "rt:scan"))))))
           :in-theory (disable collection-ready-trace-of-append
                               collection-header-payload-words
                               collection-raw-scan-open-has-no-scan-cutpoint))))

(local
 (in-theory (disable collection-cpu-p collection-read-word collection-raw-header-scan-trace
                     collection-scan-selection-trace collection-trace-effect collection-trace-ready-p
                     collection-scan-control-p collection-header-frontier collection-cell-frontier
                     collection-header-queue collection-cell-queue collection-copy-bytes
                     collection-forwarding)))

(local
 (defthm collection-raw-scan-excludes-finish-address
   (not (assoc-equal (+ origin (collection-linux-offset "rt:collect-finish"))
                     (collection-raw-header-scan-trace type origin)))
   :hints (("Goal" :cases ((equal type 1))
                   :in-theory (enable collection-raw-header-scan-trace
                                      collection-open-scan-header-trace collection-skip-raw-fields-trace)))))

(local
 (defthm collection-raw-scan-dequeues-without-discovery
   (let* ((headers (collection-header-queue work))
          (next (collection-scan-one work)))
     (implies (and (endp (collection-cell-queue work))
                   (consp headers) (endp (cdddar headers)))
              (and (equal (collection-header-frontier next) (collection-header-frontier work))
                   (equal (collection-cell-frontier next) (collection-cell-frontier work)))))
   :hints (("Goal" :in-theory (enable collection-scan-one
                                      collection-header-frontier collection-cell-frontier)))))

(local
 (defthm collection-scan-selection-keeps-cpu-and-stop
   (let* ((selection (collection-scan-selection-trace work origin))
          (selected (collection-trace-effect selection world)))
     (implies (collection-cpu-p world)
              (and (collection-cpu-p selected)
                   (equal (proof-world-stop selected) (proof-world-stop world)))))
   :hints (("Goal"
            :cases ((consp (collection-cell-queue work)))
            :in-theory (enable collection-scan-selection-trace collection-trace-effect)))))

(defthm collection-scan-raw-header-establishes-body-post
  (let* ((selection (collection-scan-selection-trace work origin))
         (selected (collection-trace-effect selection world))
         (address (proof-world-reg 8 selected))
         (header (collection-read-word address selected))
         (type (boymoo-model::a64-unsigned 64 (logand header 255)))
         (record (car (collection-header-queue work)))
         (bytes (+ 8 (ash (collection-header-payload-words header) 3)))
         (trace (collection-raw-header-scan-trace type origin))
         (after (collection-trace-effect trace selected)))
    (implies (and (collection-scan-control-p work origin world)
                  (not (proof-world-stop world))
                  (endp (collection-cell-queue work))
                  (consp (collection-header-queue work)) (endp (cdddr record))
                  (equal (collection-copy-bytes record) bytes)
                  (member-equal type '(1 3))
                  (unsigned-byte-p 64 (+ 8 address))
                  (unsigned-byte-p 64 (+ address bytes))
                  (proof-covered-p address 8 :read (proof-world-regions selected))
                  (collection-trace-placed-p trace selected))
             (and (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "rt:scan"))) selected)
                  (not (assoc-equal (+ origin (collection-linux-offset "rt:collect-finish")) trace))
                  (collection-scan-body-post-p work world after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-raw-scan-excludes-finish-address
                            (type (boymoo-model::a64-unsigned
                                   64 (logand (collection-read-word
                                               (proof-world-reg 8 (collection-trace-effect
                                                                  (collection-scan-selection-trace work origin) world))
                                               (collection-trace-effect
                                                (collection-scan-selection-trace work origin) world))
                                              255))))
                 (:instance collection-placed-raw-header-scan-advances-without-rewriting-memory
                            (register 20) (world (collection-trace-effect
                                                  (collection-scan-selection-trace work origin) world)))
                 (:instance collection-placed-raw-header-scan-advances-without-rewriting-memory
                            (register 21) (world (collection-trace-effect
                                                  (collection-scan-selection-trace work origin) world)))
                 (:instance collection-placed-raw-header-scan-advances-without-rewriting-memory
                            (register 22) (world (collection-trace-effect
                                                  (collection-scan-selection-trace work origin) world))))
           :in-theory (e/d (collection-scan-control-p collection-scan-selection-address
                           collection-scan-step-address)
                            (collection-scan-cursors-p collection-header-payload-words
                             collection-raw-scan-excludes-finish-address)))))
