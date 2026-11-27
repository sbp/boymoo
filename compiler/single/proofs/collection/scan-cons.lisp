(in-package "BOYMOO-PROOFS")

(include-book "scan-traversal")
(include-book "scan-fields")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-cons-first-call-trace (origin)
  (collection-linux-trace "rt:scan-cons" '(0 1 2) origin))

(defun collection-cons-second-call-trace (origin)
  (collection-linux-trace "rt:scan-cons" '(3 4 5) origin))

(defun collection-cons-last-store-trace (origin)
  (collection-linux-trace "rt:scan-cons" '(6 7) origin))

(defun collection-cons-scan-trace (first second origin)
  (append (collection-cons-first-call-trace origin) first
          (collection-cons-second-call-trace origin) second
          (collection-cons-last-store-trace origin)))

(local
 (defthm collection-cons-scan-instruction-access
   (implies (unsigned-byte-p 64 (+ (proof-world-reg 22 world) offset))
            (equal (proof-instruction-access-p (list :single load 8 22 0 :offset offset) world)
                   (proof-covered-p (+ (proof-world-reg 22 world) offset) 8
                                    (if (equal load 1) :read :write) (proof-world-regions world))))
   :hints (("Goal" :in-theory (disable proof-covered-p boymoo-model::a64-unsigned)))))

(local
 (defthm collection-cons-scan-words-are-covered
   (implies (proof-covered-p cell 16 :write regions)
            (and (proof-span-p cell 16)
                 (proof-covered-p cell 8 :write regions)
                 (proof-covered-p (+ cell 8) 8 :write regions)
                 (unsigned-byte-p 64 (+ cell 8))))
   :hints (("Goal"
            :use ((:instance collection-covered-subspan
                             (base cell) (address cell) (extent 16) (width 8) (access :write))
                  (:instance collection-covered-subspan
                             (base cell) (address (+ cell 8)) (extent 16) (width 8) (access :write))
                  (:instance collection-covered-address-is-a-span
                             (address cell) (width 16) (access :write)))
            :in-theory (disable collection-covered-address-is-a-span proof-covered-p)))))

(local
 (defthm collection-cons-scan-cpu-actions-keep-stop
   (and (equal (proof-world-stop (collection-write-pc pc world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-register register value world)) (proof-world-stop world))
        (equal (proof-world-stop (collection-write-word address value world)) (proof-world-stop world)))))

(local
 (in-theory (disable proof-instruction-at-p proof-instruction-effect proof-span-p
                     proof-covered-p proof-world-machine proof-world-regions proof-regions-p
                     proof-world-reg proof-world-pc proof-world-stop proof-load-word
                     collection-cpu-p collection-read-word collection-write-word collection-write-pc
                     collection-write-register boymoo-model::a64-memory boymoo-model::a64-unsigned
                     (:definition ash) (:definition acl2::binary-logand))))

(defthm collection-placed-cons-scan-opens-first-forwarding-call
  (let* ((entry (+ origin (collection-linux-offset "rt:scan-cons")))
         (cell (- (proof-world-reg 22 world) 16))
         (trace (collection-cons-first-call-trace origin))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-cpu-p world)
                  (not (proof-world-stop world))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) entry)
                  (proof-covered-p cell 8 :read (proof-world-regions world))
                  (collection-trace-placed-p trace world))
             (and (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "rt:forward"))) world)
                  (equal (proof-world-reg 0 after) (collection-read-word cell world))
                  (equal (proof-world-reg 30 after) (+ entry 12))
                  (equal (proof-world-reg 22 after) cell)
                  (implies (not (member-equal register '(0 22 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-covered-address-is-a-span
                            (address (- (proof-world-reg 22 world) 16))
                            (width 8) (access :read) (regions (proof-world-regions world))))
           :in-theory (e/d (proof-span-p) (collection-covered-address-is-a-span)))))

(defthm collection-placed-cons-scan-opens-second-forwarding-call
  (let* ((entry (+ origin (collection-linux-offset "rt:scan-cons")))
         (cell (proof-world-reg 22 world))
         (trace (collection-cons-second-call-trace origin))
         (after (collection-trace-effect trace world))
         (regions (proof-world-regions world)))
    (implies (and (collection-cpu-p world)
                  (not (proof-world-stop world))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ entry 12))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-regions-p regions)
                  (proof-covered-p cell 16 :write regions)
                  (collection-trace-placed-p trace world))
             (and (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "rt:forward"))) world)
                  (equal (proof-world-reg 0 after) (collection-read-word (+ cell 8) world))
                  (equal (proof-world-reg 30 after) (+ entry 24))
                  (equal (collection-read-word cell after) (proof-world-reg 0 world))
                  (implies (not (member-equal register '(0 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-cons-scan-words-are-covered
                            (cell (proof-world-reg 22 world)) (regions (proof-world-regions world))))
           :in-theory (e/d (proof-span-p proof-disjoint-p)
                            (collection-cons-scan-words-are-covered)))))

(defthm collection-placed-cons-scan-stores-second-and-closes-round
  (let* ((entry (+ origin (collection-linux-offset "rt:scan-cons")))
         (cell (proof-world-reg 22 world))
         (trace (collection-cons-last-store-trace origin))
         (after (collection-trace-effect trace world))
         (regions (proof-world-regions world)))
    (implies (and (collection-cpu-p world)
                  (not (proof-world-stop world))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ entry 24))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-regions-p regions)
                  (proof-covered-p cell 16 :write regions)
                  (collection-trace-placed-p trace world))
             (and (collection-trace-ready-p trace (list (+ origin (collection-linux-offset "rt:scan"))) world)
                  (collection-cpu-p after)
                  (equal (proof-world-pc after) (+ origin (collection-linux-offset "rt:scan")))
                  (equal (proof-world-reg register after) (proof-world-reg register world))
                  (equal (collection-read-word cell after) (collection-read-word cell world))
                  (equal (collection-read-word (+ cell 8) after) (proof-world-reg 0 world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-cons-scan-words-are-covered
                            (cell (proof-world-reg 22 world)) (regions (proof-world-regions world))))
           :in-theory (e/d (proof-span-p proof-disjoint-p)
                            (collection-cons-scan-words-are-covered)))))

(local
 (defthm collection-cons-body-fixed-traces-avoid-scan-and-finish
   (let ((cuts (list (+ origin (collection-linux-offset "rt:scan"))
                     (+ origin (collection-linux-offset "rt:collect-finish")))))
     (and (not (intersectp-equal (strip-cars (collection-cons-first-call-trace origin)) cuts))
          (not (intersectp-equal (strip-cars (collection-cons-second-call-trace origin)) cuts))
          (not (intersectp-equal (strip-cars (collection-cons-last-store-trace origin)) cuts))))))

(local
 (defthm collection-cons-body-appended-addresses
   (equal (strip-cars (append left right)) (append (strip-cars left) (strip-cars right)))
   :hints (("Goal" :induct (append left right)))))

(local
 (defthm collection-cons-body-cut-intersection-of-append
   (iff (intersectp-equal (append left right) cuts)
        (or (intersectp-equal left cuts) (intersectp-equal right cuts)))))

(local
 (defthm collection-cons-body-address-occurs-as-trace-entry
   (implies address
            (iff (assoc-equal address trace)
                 (member-equal address (strip-cars trace))))
   :hints (("Goal" :induct (assoc-equal address trace)))))

(local
 (defthm collection-cons-body-member-of-append
   (iff (member-equal address (append left right))
        (or (member-equal address left) (member-equal address right)))
   :hints (("Goal" :induct (append left right)))))

(local
 (defthm collection-cons-body-one-cut-intersection
   (iff (intersectp-equal addresses (list cut)) (member-equal cut addresses))
   :hints (("Goal" :induct (len addresses)))))

(local
 (defthm collection-cons-body-two-cut-intersection
   (iff (intersectp-equal addresses (list first second))
        (or (member-equal first addresses)
            (member-equal second addresses)))
   :hints (("Goal" :induct (len addresses)))))

(local
 (in-theory (disable collection-cons-first-call-trace collection-cons-second-call-trace
                     collection-cons-last-store-trace collection-trace-effect
                     collection-trace-ready-p collection-trace-placed-p)))

(defthm collection-ready-cons-scan-segments-form-object-body
  (let* ((entry (+ origin (collection-linux-offset "rt:scan-cons")))
         (calls (list (+ origin (collection-linux-offset "rt:forward"))))
         (scan (+ origin (collection-linux-offset "rt:scan")))
         (finish (+ origin (collection-linux-offset "rt:collect-finish")))
         (called-first (collection-trace-effect (collection-cons-first-call-trace origin) world))
         (returned-first (collection-trace-effect first called-first))
         (called-second (collection-trace-effect (collection-cons-second-call-trace origin) returned-first))
         (returned-second (collection-trace-effect second called-second)))
    (implies (and (collection-trace-ready-p (collection-cons-first-call-trace origin) calls world)
                  (collection-trace-ready-p first (list (+ entry 12)) called-first)
                  (collection-trace-ready-p (collection-cons-second-call-trace origin) calls returned-first)
                  (collection-trace-ready-p second (list (+ entry 24)) called-second)
                  (collection-trace-ready-p (collection-cons-last-store-trace origin)
                                            (list scan) returned-second)
                  (not (intersectp-equal (strip-cars first) (list scan finish)))
                  (not (intersectp-equal (strip-cars second) (list scan finish))))
             (and (collection-trace-ready-p (collection-cons-scan-trace first second origin) (list scan) world)
                  (not (assoc-equal finish (collection-cons-scan-trace first second origin))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-cons-body-fixed-traces-avoid-scan-and-finish)
                 (:instance collection-ready-trace-of-append
                            (first second)
                            (second (collection-cons-last-store-trace origin))
                            (first-cut (list (+ origin (collection-linux-offset "rt:scan-cons") 24)))
                            (cuts (list (+ origin (collection-linux-offset "rt:scan"))))
                            (world (collection-trace-effect
                                    (collection-cons-second-call-trace origin)
                                    (collection-trace-effect
                                     first (collection-trace-effect
                                            (collection-cons-first-call-trace origin) world)))))
                 (:instance collection-ready-trace-of-append
                            (first (collection-cons-second-call-trace origin))
                            (second (append second (collection-cons-last-store-trace origin)))
                            (first-cut (list (+ origin (collection-linux-offset "rt:forward"))))
                            (cuts (list (+ origin (collection-linux-offset "rt:scan"))))
                            (world (collection-trace-effect
                                    first (collection-trace-effect
                                           (collection-cons-first-call-trace origin) world))))
                 (:instance collection-ready-trace-of-append
                            (second (append (collection-cons-second-call-trace origin) second
                                            (collection-cons-last-store-trace origin)))
                            (first-cut (list (+ origin (collection-linux-offset "rt:scan-cons") 12)))
                            (cuts (list (+ origin (collection-linux-offset "rt:scan"))))
                            (world (collection-trace-effect (collection-cons-first-call-trace origin) world)))
                 (:instance collection-ready-trace-of-append
                            (first (collection-cons-first-call-trace origin))
                            (second (append first (collection-cons-second-call-trace origin) second
                                            (collection-cons-last-store-trace origin)))
                            (first-cut (list (+ origin (collection-linux-offset "rt:forward"))))
                            (cuts (list (+ origin (collection-linux-offset "rt:scan"))))))
           :in-theory (disable collection-ready-trace-of-append
                               collection-cons-body-fixed-traces-avoid-scan-and-finish))))

; A call result keeps the selected cell accessible and all continuation
; instructions placed. The forwarder's effects on other objects are
; supplied by its own checked segment.
(defun collection-cons-scan-return-p (cell pc continuation world)
  (let ((regions (proof-world-regions world)))
    (and (collection-cpu-p world)
         (not (proof-world-stop world))
         (equal (proof-world-pc world) pc)
         (alistp (boymoo-model::a64-memory (proof-world-machine world)))
         (equal (proof-world-reg 22 world) cell)
         (proof-regions-p regions)
         (proof-covered-p cell 16 :write regions)
         (collection-trace-placed-p continuation world))))

(defthm collection-checked-cons-scan-body-stores-both-forwarded-words
  (let* ((entry (+ origin (collection-linux-offset "rt:scan-cons")))
         (scan (+ origin (collection-linux-offset "rt:scan")))
         (finish (+ origin (collection-linux-offset "rt:collect-finish")))
         (cell (- (proof-world-reg 22 world) 16))
         (start (collection-cons-first-call-trace origin))
         (middle (collection-cons-second-call-trace origin))
         (tail (collection-cons-last-store-trace origin))
         (called-first (collection-trace-effect start world))
         (returned-first (collection-trace-effect first called-first))
         (called-second (collection-trace-effect middle returned-first))
         (returned-second (collection-trace-effect second called-second))
         (trace (collection-cons-scan-trace first second origin))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-cpu-p world)
                  (not (proof-world-stop world))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) entry)
                  (proof-covered-p cell 8 :read (proof-world-regions world))
                  (collection-trace-placed-p start world)
                  (collection-trace-ready-p first (list (+ entry 12)) called-first)
                  (not (intersectp-equal (strip-cars first) (list scan finish)))
                  (collection-cons-scan-return-p cell (+ entry 12) middle returned-first)
                  (equal (collection-read-word (+ cell 8) returned-first)
                         (collection-read-word (+ cell 8) world))
                  (collection-trace-ready-p second (list (+ entry 24)) called-second)
                  (not (intersectp-equal (strip-cars second) (list scan finish)))
                  (collection-cons-scan-return-p cell (+ entry 24) tail returned-second)
                  (equal (collection-read-word cell returned-second)
                         (collection-read-word cell called-second)))
             (and (collection-trace-ready-p trace (list scan) world)
                  (not (assoc-equal finish trace))
                  (collection-cpu-p after)
                  (equal (proof-world-pc after) scan)
                  (equal (proof-world-reg register after) (proof-world-reg register returned-second))
                  (equal (proof-world-reg 0 called-first) (collection-read-word cell world))
                  (equal (proof-world-reg 0 called-second) (collection-read-word (+ cell 8) world))
                  (equal (collection-read-word cell after) (proof-world-reg 0 returned-first))
                  (equal (collection-read-word (+ cell 8) after) (proof-world-reg 0 returned-second)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-ready-cons-scan-segments-form-object-body)
                 (:instance collection-placed-cons-scan-opens-first-forwarding-call)
                 (:instance collection-placed-cons-scan-opens-second-forwarding-call
                            (world (collection-trace-effect
                                    first (collection-trace-effect (collection-cons-first-call-trace origin) world))))
                 (:instance collection-placed-cons-scan-stores-second-and-closes-round
                            (world (collection-trace-effect
                                    second (collection-trace-effect
                                            (collection-cons-second-call-trace origin)
                                            (collection-trace-effect
                                             first (collection-trace-effect
                                                    (collection-cons-first-call-trace origin) world)))))))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(collection-cons-scan-trace collection-cons-scan-return-p
                         collection-trace-effect-of-append
                         (:executable-counterpart collection-linux-offset)
                         default-+-1 default-+-2 acl2::fold-consts-in-+))
           :do-not-induct t)))
