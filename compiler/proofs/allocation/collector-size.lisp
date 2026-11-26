(in-package "BOYMOO-PROOFS")

(include-book "instructions")
(include-book "memory")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defconst *allocation-collector-size-path* (allocation-instructions "rt:collect" 7))
(defconst *allocation-collector-live-size-path* (allocation-instructions "rt:collect-finish" 9))

(defun allocation-collector-size-target (bytes origin)
  (if (< *proof-space-size* bytes)
      (allocation-code-address (proof-resource-label :allocation-size) origin)
    (+ 28 (allocation-code-address "rt:collect" origin))))

(defthm allocation-collector-request-size-machine-edge
  (let ((bytes (proof-world-reg 0 before)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-code-address "rt:collect" origin))
                  (equal cut (allocation-path-end *allocation-collector-size-path* before)))
             (and (not (proof-world-stop cut))
                  (equal (proof-world-pc cut) (allocation-collector-size-target bytes origin))
                  (equal (proof-world-reg 0 cut) bytes)
                  (equal (proof-world-reg 1 cut) (proof-world-reg 1 before)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum
                                     allocation-unsigned-64-of-difference))))

(defthm allocation-collector-request-size-checked-edge
  (let* ((bytes (proof-world-reg 0 before))
         (cuts (list (allocation-collector-size-target bytes origin))))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-code-address "rt:collect" origin))
                  (allocation-path-ready-p *allocation-collector-size-path* cuts before)
                  (equal cut (allocation-path-end *allocation-collector-size-path* before)))
             (and (proof-segment-p (len *allocation-collector-size-path*) cuts before :cut cut)
                  (if (< *proof-space-size* bytes)
                      (proof-resource-bound-p :allocation-size bytes before)
                    (<= bytes *proof-space-size*)))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-collector-request-size-machine-edge
                        (:instance allocation-checked-cut
                         (instructions *allocation-collector-size-path*) (world before) (after cut)
                         (cuts (list (allocation-collector-size-target (proof-world-reg 0 before) origin)))))
           :in-theory (disable allocation-checked-cut allocation-path-ready-p allocation-path-end
                               allocation-collector-size-target proof-segment-p))))

(defthm allocation-collector-spills-request-and-mode
  (let ((sp (- (allocation-sp before) 64)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-code-address "rt:collect" origin))
                  (<= 64 (allocation-sp before))
                  (equal cut (allocation-path-end *allocation-collector-size-path* before)))
             (and (equal (allocation-sp cut) sp)
                  (equal (allocation-load-word sp cut) (proof-world-reg 0 before))
                  (equal (allocation-load-word (+ sp 8) cut) (proof-world-reg 1 before)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-register-range (register 0) (world before)))
           :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                           (allocation-word-register-range allocation-unsigned-64-of-sum
                            allocation-unsigned-64-of-difference)))))

(defun allocation-collector-live-bytes (floor box cells end)
  (+ (- box floor) (- end cells)))

(defthm allocation-collector-live-and-request-bound
  (let ((live (allocation-collector-live-bytes floor box cells end)))
    (implies (and (natp floor) (natp box) (natp cells) (natp end)
                  (<= floor box) (<= box cells) (<= cells end)
                  (equal end (+ floor *proof-space-size*))
                  (natp bytes) (<= bytes *proof-space-size*))
             (and (natp live) (<= live *proof-space-size*)
                  (unsigned-byte-p 64 (+ live bytes)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable unsigned-byte-p acl2::integer-range-p))))

(defun allocation-collector-finish-demand (before)
  (let* ((metadata (proof-world-reg 17 before))
         (floor (allocation-load-word (+ metadata 24) before))
         (end (allocation-load-word (+ metadata 32) before)))
    (+ (allocation-collector-live-bytes floor (proof-world-reg 20 before)
                                       (proof-world-reg 21 before) end)
       (allocation-load-word (allocation-sp before) before))))

(defun allocation-collector-finish-target (demand origin)
  (if (< *proof-space-size* demand)
      (allocation-code-address (proof-resource-label :heap-size) origin)
    (+ 36 (allocation-code-address "rt:collect-finish" origin))))

(defthm allocation-collector-finish-machine-edge
  (let* ((metadata (proof-world-reg 17 before))
         (floor (allocation-load-word (+ metadata 24) before))
         (end (allocation-load-word (+ metadata 32) before))
         (bytes (allocation-load-word (allocation-sp before) before))
         (demand (allocation-collector-finish-demand before)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-code-address "rt:collect-finish" origin))
                  (<= floor (proof-world-reg 20 before))
                  (<= (proof-world-reg 20 before) (proof-world-reg 21 before))
                  (<= (proof-world-reg 21 before) end)
                  (equal end (+ floor *proof-space-size*))
                  (<= bytes *proof-space-size*)
                  (equal cut (allocation-path-end *allocation-collector-live-size-path* before)))
             (and (not (proof-world-stop cut))
                  (equal (proof-world-pc cut) (allocation-collector-finish-target demand origin))
                  (equal (proof-world-reg 5 cut) demand)
                  (implies (< *proof-space-size* demand)
                           (proof-resource-bound-p :heap-size demand before)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-collector-live-and-request-bound
                  (floor (allocation-load-word (+ (proof-world-reg 17 before) 24) before))
                  (end (allocation-load-word (+ (proof-world-reg 17 before) 32) before))
                  (box (proof-world-reg 20 before)) (cells (proof-world-reg 21 before))
                  (bytes (allocation-load-word (allocation-sp before) before))))
           :in-theory (disable allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference))))

(defthm allocation-collector-finish-checked-edge
  (let* ((metadata (proof-world-reg 17 before))
         (floor (allocation-load-word (+ metadata 24) before))
         (end (allocation-load-word (+ metadata 32) before))
         (demand (allocation-collector-finish-demand before))
         (cuts (list (allocation-collector-finish-target demand origin))))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-code-address "rt:collect-finish" origin))
                  (<= floor (proof-world-reg 20 before))
                  (<= (proof-world-reg 20 before) (proof-world-reg 21 before))
                  (<= (proof-world-reg 21 before) end)
                  (equal end (+ floor *proof-space-size*))
                  (<= (allocation-load-word (allocation-sp before) before) *proof-space-size*)
                  (allocation-path-ready-p *allocation-collector-live-size-path* cuts before)
                  (equal cut (allocation-path-end *allocation-collector-live-size-path* before)))
             (and (proof-segment-p (len *allocation-collector-live-size-path*) cuts before :cut cut)
                  (equal (proof-world-reg 5 cut) demand)
                  (implies (< *proof-space-size* demand)
                           (proof-resource-bound-p :heap-size demand before)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-collector-finish-machine-edge
                 (:instance allocation-checked-cut
                  (instructions *allocation-collector-live-size-path*) (world before) (after cut)
                  (cuts (list (allocation-collector-finish-target (allocation-collector-finish-demand before) origin)))))
           :in-theory (disable allocation-checked-cut allocation-path-ready-p allocation-path-end
                               allocation-collector-finish-target allocation-collector-finish-demand proof-segment-p))))
