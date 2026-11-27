(in-package "BOYMOO-PROOFS")

(include-book "instructions")
(include-book "memory")
(include-book "alignment")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defconst *allocation-map-setup-path* (take 7 *allocation-map-code*))
(defconst *allocation-map-return-path* (nthcdr 8 *allocation-map-code*))

(defun allocation-map-svc-arguments-p (size world)
  (and (equal (proof-world-reg 0 world) 0)
       (equal (proof-world-reg 1 world) size)
       (equal (proof-world-reg 2 world) 3)
       (equal (proof-world-reg 3 world) #x4022)
       (equal (proof-world-reg 4 world) #xffffffffffffffff)
       (equal (proof-world-reg 5 world) 0)
       (equal (proof-world-reg 8 world) 222)))

(defthm allocation-map-setup-machine-edge
  (implies (and (allocation-code-origin-p origin)
                (allocation-machine-state-p before)
                (not (proof-world-stop before))
                (equal (proof-world-pc before) (allocation-code-address "sys:map" origin))
                (equal cut (allocation-path-end *allocation-map-setup-path* before)))
           (and (not (proof-world-stop cut))
                (equal (proof-world-pc cut) (+ 28 (allocation-code-address "sys:map" origin)))
                (allocation-map-svc-arguments-p (proof-world-reg 0 before) cut)
                (proof-register-frame-p 30 '(0 1 2 3 4 5 8) before cut)
                (equal (allocation-sp cut) (allocation-sp before))
                (equal (allocation-memory cut) (allocation-memory before))
                (equal (proof-world-regions cut) (proof-world-regions before))
                (equal (proof-world-replies cut) (proof-world-replies before))
                (proof-streams-preserved-p before cut)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference))))

(defun allocation-map-admissible-success-p (reply size world)
  (and (posp reply)
       (equal (mod reply (proof-world-page-size world)) 0)
       (<= (+ reply size) (expt 2 63))
       (proof-region-disjoint-p reply (+ reply size) (proof-world-regions world))))

(defun allocation-map-success-world (reply size before)
  (let* ((end (+ reply size))
         (cleared (proof-clear-span reply end before))
         (regions (cons (proof-region reply end :rw) (proof-world-regions before))))
    (proof-svc-return reply (update-nth 1 regions cleared))))

(defthm allocation-clear-span-preserves-regions
  (equal (proof-world-regions (proof-clear-span start end world))
         (proof-world-regions world))
  :hints (("Goal" :in-theory (enable proof-world-regions))))

(defthm allocation-clear-span-preserves-cpu-and-replies
  (and (equal (proof-world-reg register (proof-clear-span start end world))
              (proof-world-reg register world))
       (equal (proof-world-pc (proof-clear-span start end world)) (proof-world-pc world))
       (equal (proof-world-replies (proof-clear-span start end world)) (proof-world-replies world))
       (equal (proof-world-stop (proof-clear-span start end world)) (proof-world-stop world)))
  :hints (("Goal" :in-theory (enable proof-world-reg proof-world-pc proof-world-machine
                                    proof-world-replies proof-world-stop))))

(defthm allocation-map-svc-success-effect
  (let ((reply (car (proof-world-replies before))))
    (implies (and (allocation-map-svc-arguments-p size before)
                  (proof-page-size-p (proof-world-page-size before))
                  (posp size) (equal (mod size *proof-runtime-page*) 0)
                  (consp (proof-world-replies before))
                  (allocation-map-admissible-success-p reply size before))
             (equal (proof-instruction-effect '(:svc 0) before)
                    (allocation-map-success-world reply size before))))
  :hints (("Goal" :in-theory (disable allocation-svc-return-effect proof-svc-return proof-clear-span
                                     proof-align-up proof-page-size-p proof-region-disjoint-p mod))))

(defthm allocation-map-svc-error-effect
  (let ((reply (car (proof-world-replies before))))
    (implies (and (allocation-map-svc-arguments-p size before)
                  (proof-page-size-p (proof-world-page-size before))
                  (posp size) (consp (proof-world-replies before))
                  (proof-linux-errno-p reply))
             (equal (proof-instruction-effect '(:svc 0) before) (proof-svc-return reply before))))
  :hints (("Goal" :in-theory (disable allocation-svc-return-effect proof-svc-return
                                     proof-align-up proof-page-size-p))))

(defthm allocation-memory-of-world-slot-update
  (implies (posp slot)
           (equal (allocation-memory (update-nth slot value world)) (allocation-memory world)))
  :hints (("Goal" :in-theory (enable allocation-memory proof-world-machine))))

(defthm allocation-cleared-memory-of-world
  (equal (allocation-memory (proof-clear-span start end world))
         (proof-clear-memory start end (allocation-memory world)))
  :hints (("Goal" :in-theory (enable allocation-memory proof-world-machine))))

(defthm allocation-regions-of-kernel-updates
  (and (equal (proof-world-regions (update-nth 6 value world)) (proof-world-regions world))
       (equal (proof-world-regions (update-nth 1 value world)) value))
  :hints (("Goal" :in-theory (enable proof-world-regions))))

(defthm allocation-map-success-is-cleared
  (let* ((end (+ reply size))
         (after (allocation-map-success-world reply size before)))
    (and (equal (proof-world-regions after)
                (cons (proof-region reply end :rw) (proof-world-regions before)))
         (equal (allocation-memory after)
                (proof-clear-memory reply end (allocation-memory before)))))
  :hints (("Goal" :in-theory (disable proof-svc-return proof-clear-span update-nth))))

(defthm allocation-map-success-zero-byte
  (implies (and (unsigned-byte-p 64 address) (<= reply address) (< address (+ reply size)))
           (equal (boymoo-model::a64-byte
                   address (allocation-memory (allocation-map-success-world reply size before)))
                  0))
  :hints (("Goal" :in-theory (disable allocation-map-success-world boymoo-model::a64-byte
                                     proof-clear-memory))))

(local
 (defthm allocation-read-with-empty-count
   (implies (zp bytes)
            (equal (boymoo-model::a64-read-bytes bytes address memory) 0))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-bytes)))))

(defthm allocation-read-within-cleared-span
  (implies (proof-subspan-p address bytes start end)
           (equal (boymoo-model::a64-read-bytes bytes address (proof-clear-memory start end memory)) 0))
  :rule-classes nil
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes bytes address memory)
           :expand ((:free (contents) (boymoo-model::a64-read-bytes bytes address contents)))
           :in-theory (e/d ((:induction boymoo-model::a64-read-bytes))
                           ((:definition boymoo-model::a64-read-bytes) boymoo-model::a64-byte proof-clear-memory)))))

(defthm allocation-map-success-preserves-outside-byte
  (implies (and (unsigned-byte-p 64 address) (or (< address reply) (<= (+ reply size) address)))
           (equal (boymoo-model::a64-byte
                   address (allocation-memory (allocation-map-success-world reply size before)))
                  (boymoo-model::a64-byte address (allocation-memory before))))
  :hints (("Goal" :in-theory (disable allocation-map-success-world boymoo-model::a64-byte
                                     proof-clear-memory))))

(defthm allocation-map-tail-machine-return
  (implies (and (allocation-machine-state-p before) (not (proof-world-stop before))
                (equal after (allocation-path-end *allocation-map-return-path* before)))
           (and (proof-frame-return-p '(0) t before after)
                (equal (proof-world-reg 0 after)
                       (if (< (proof-world-reg 0 before) (expt 2 63))
                           (proof-world-reg 0 before) 0))
                (equal (allocation-memory after) (allocation-memory before))
                (equal (proof-world-regions after) (proof-world-regions before))
                (equal (proof-world-replies after) (proof-world-replies before))
                (proof-streams-preserved-p before after)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference))))

(defthm allocation-linux-errno-word
  (implies (proof-linux-errno-p reply)
           (equal (boymoo-model::a64-unsigned 64 reply) (+ *allocation-word-modulus* reply)))
  :hints (("Goal" :use ((:instance allocation-unsigned-64-of-difference (left 0) (right (- reply))))
           :in-theory (enable unsigned-byte-p acl2::integer-range-p))))

(defthm allocation-signed-linux-errno
  (implies (proof-linux-errno-p reply)
           (equal (boymoo-model::a64-signed 64 (boymoo-model::a64-unsigned 64 reply)) reply))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-signed))))

(defthm allocation-machine-of-world-slot-update
  (implies (posp slot)
           (equal (proof-world-machine (update-nth slot value world)) (proof-world-machine world)))
  :hints (("Goal" :in-theory (enable proof-world-machine))))

(defthm allocation-reg-and-pc-of-world-slot-update
  (implies (posp slot)
           (and (equal (proof-world-reg register (update-nth slot value world))
                       (proof-world-reg register world))
                (equal (proof-world-pc (update-nth slot value world)) (proof-world-pc world))))
  :hints (("Goal" :in-theory (enable proof-world-reg proof-world-pc))))

(defthm allocation-svc-return-keeps-registers-and-resumes
  (and (equal (proof-world-reg register (proof-svc-return reply before))
              (if (equal register 0) (boymoo-model::a64-unsigned 64 reply)
                (proof-world-reg register before)))
       (equal (proof-world-pc (proof-svc-return reply before))
              (boymoo-model::a64-unsigned 64 (+ 4 (proof-world-pc before))))
       (equal (proof-world-replies (proof-svc-return reply before))
              (cdr (proof-world-replies before)))
       (equal (proof-world-stop (proof-svc-return reply before)) (proof-world-stop before)))
  :hints (("Goal" :in-theory (e/d (proof-world-replies proof-world-stop)
                                  (proof-svc-return update-nth boymoo-model::a64-unsigned)))))

(defthm allocation-svc-return-keeps-memory-and-regions
  (and (equal (allocation-memory (proof-svc-return reply before)) (allocation-memory before))
       (equal (proof-world-regions (proof-svc-return reply before)) (proof-world-regions before)))
  :hints (("Goal" :in-theory (disable proof-svc-return update-nth))))

(defthm allocation-region-update-preserves-replies-and-stop
  (and (equal (proof-world-replies (update-nth 1 value world)) (proof-world-replies world))
       (equal (proof-world-stop (update-nth 1 value world)) (proof-world-stop world)))
  :hints (("Goal" :in-theory (enable proof-world-replies proof-world-stop))))

(defthm allocation-map-success-returned-fields
  (let ((after (allocation-map-success-world reply size before)))
    (and (equal (proof-world-reg register after)
                (if (equal register 0) (boymoo-model::a64-unsigned 64 reply)
                  (proof-world-reg register before)))
         (equal (proof-world-pc after) (boymoo-model::a64-unsigned 64 (+ 4 (proof-world-pc before))))
         (equal (proof-world-replies after) (cdr (proof-world-replies before)))
         (equal (proof-world-stop after) (proof-world-stop before))))
  :hints (("Goal" :in-theory (disable proof-svc-return proof-clear-span update-nth
                                     allocation-svc-return-effect boymoo-model::a64-unsigned))))

(defthm allocation-fresh-mapping-disjoint-from-covered-span
  (implies (and (proof-region-disjoint-p start end regions)
                (proof-covered-p address size access regions))
           (proof-disjoint-p start end address (+ address size)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-region-disjoint-p start end regions)
           :in-theory (disable proof-region-allows-p proof-span-p))))

(defthm allocation-admissible-mapping-refusal
  (implies (and (allocation-map-svc-arguments-p size before)
                (proof-page-size-p (proof-world-page-size before))
                (posp size) (consp (proof-world-replies before))
                (proof-linux-errno-p (car (proof-world-replies before)))
                (not (proof-world-stop before))
                (< (+ 4 (proof-world-pc before)) *allocation-word-modulus*)
                (proof-instruction-at-p '(:svc 0) (proof-world-pc before) before))
           (proof-mapping-refused-p before))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-map-svc-error-effect
                 (:instance allocation-signed-linux-errno (reply (car (proof-world-replies before))))
                 (:instance allocation-svc-return-keeps-registers-and-resumes
                  (reply (car (proof-world-replies before))) (register 0))
                 (:instance proof-step-from-instruction (instruction '(:svc 0)) (world before)))
           :in-theory (e/d (proof-instruction-access-p)
                           (allocation-svc-effect allocation-svc-return-effect
                            allocation-map-svc-error-effect proof-step-from-instruction
                            allocation-svc-return-keeps-registers-and-resumes
                            allocation-linux-errno-word allocation-signed-word allocation-signed-linux-errno
                            boymoo-model::a64-signed
                            proof-svc-return proof-linux-errno-p proof-page-size-p)))))

(defthm allocation-map-checked-tail-return
  (let ((cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-machine-state-p before) (not (proof-world-stop before))
                  (allocation-path-ready-p *allocation-map-return-path* cuts before)
                  (equal after (allocation-path-end *allocation-map-return-path* before)))
             (and (proof-segment-p (len *allocation-map-return-path*) cuts before :cut after)
                  (equal (proof-world-reg 0 after)
                         (if (< (proof-world-reg 0 before) (expt 2 63))
                             (proof-world-reg 0 before) 0))
                  (equal (allocation-memory after) (allocation-memory before))
                  (equal (proof-world-regions after) (proof-world-regions before)))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-map-tail-machine-return
                        (:instance allocation-checked-cut
                         (instructions *allocation-map-return-path*) (world before)
                         (cuts (list (proof-world-reg 30 before)))))
           :in-theory (disable allocation-checked-cut allocation-path-ready-p allocation-path-end
                               proof-segment-p))))

(defthm allocation-map-success-checked-svc
  (let* ((reply (car (proof-world-replies before)))
         (cuts (list (+ 4 (proof-world-pc before)))))
    (implies (and (allocation-map-svc-arguments-p size before)
                  (proof-page-size-p (proof-world-page-size before))
                  (posp size) (equal (mod size *proof-runtime-page*) 0)
                  (consp (proof-world-replies before))
                  (allocation-map-admissible-success-p reply size before)
                  (< (+ 4 (proof-world-pc before)) *allocation-word-modulus*)
                  (not (proof-world-stop before))
                  (allocation-path-ready-p '((:svc 0)) cuts before)
                  (equal after (allocation-map-success-world reply size before)))
             (and (proof-segment-p 1 cuts before :cut after)
                  (equal (proof-world-reg 0 after) reply)
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
                  (equal (proof-world-replies after) (cdr (proof-world-replies before)))
                  (equal (allocation-memory after)
                         (proof-clear-memory reply (+ reply size) (allocation-memory before)))
                  (equal (proof-world-regions after)
                         (cons (proof-region reply (+ reply size) :rw) (proof-world-regions before))))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-map-svc-success-effect
                 (:instance allocation-checked-cut
                  (instructions '((:svc 0))) (world before) (cuts (list (+ 4 (proof-world-pc before))))))
           :in-theory (disable allocation-checked-cut allocation-map-success-world
                               allocation-map-svc-success-effect allocation-svc-effect
                               allocation-path-ready-p proof-segment-p proof-region-disjoint-p
                               proof-page-size-p proof-clear-memory mod))))

(defthm allocation-map-refusal-checked-svc
  (let* ((reply (car (proof-world-replies before)))
         (cuts (list (+ 4 (proof-world-pc before)))))
    (implies (and (allocation-map-svc-arguments-p size before)
                  (proof-page-size-p (proof-world-page-size before))
                  (posp size) (consp (proof-world-replies before))
                  (proof-linux-errno-p reply)
                  (< (+ 4 (proof-world-pc before)) *allocation-word-modulus*)
                  (allocation-path-ready-p '((:svc 0)) cuts before)
                  (equal after (proof-svc-return reply before)))
             (and (proof-mapping-refused-p before)
                  (proof-segment-p 1 cuts before :cut after)
                  (equal (proof-world-reg 0 after) (+ *allocation-word-modulus* reply))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
                  (equal (proof-world-replies after) (cdr (proof-world-replies before)))
                  (equal (allocation-memory after) (allocation-memory before))
                  (equal (proof-world-regions after) (proof-world-regions before)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-map-svc-error-effect allocation-admissible-mapping-refusal
                 (:instance allocation-checked-cut
                  (instructions '((:svc 0))) (world before) (cuts (list (+ 4 (proof-world-pc before))))))
           :in-theory (disable allocation-checked-cut proof-svc-return
                               allocation-svc-return-effect
                               allocation-map-svc-error-effect allocation-svc-effect
                               proof-mapping-refused-p proof-page-size-p proof-segment-p))))
