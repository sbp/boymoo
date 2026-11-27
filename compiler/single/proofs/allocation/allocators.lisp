(in-package "BOYMOO-PROOFS")

(include-book "instructions")
(include-book "memory")

(local (include-book "arithmetic-5/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defconst *allocation-header-fast-path* (take 7 *allocation-header-code*))
(defconst *allocation-header-overflow-path* (take 2 *allocation-header-code*))
(defconst *allocation-header-slow-path*
  (append (take 4 *allocation-header-code*) (nthcdr 7 *allocation-header-code*)))
(defconst *allocation-cells-fast-path* (take 9 *allocation-cells-code*))
(defconst *allocation-cells-slow-path*
  (append (take 4 *allocation-cells-code*) (nthcdr 9 *allocation-cells-code*)))

(defun allocation-request-machine-pre-p (kind bytes origin before)
  (and (member-eq kind '(:cons :header))
       (allocation-code-origin-p origin)
       (allocation-machine-state-p before)
       (not (proof-world-stop before))
       (equal (proof-world-pc before)
              (allocation-code-address (if (eq kind :cons) "rt:alloc-cells" "rt:alloc")
                                       origin))
       (equal bytes (proof-world-reg 0 before))
       (equal (mod bytes (if (eq kind :cons) 16 8)) 0)
       (<= 128 (proof-heap-base before))
       (<= (proof-box-top before) (proof-heap-limit before))
       (<= (proof-heap-limit before) (proof-cons-floor before))))

(defun allocation-fast-path (kind)
  (if (eq kind :cons) *allocation-cells-fast-path* *allocation-header-fast-path*))

(defun allocation-slow-path (kind)
  (if (eq kind :cons) *allocation-cells-slow-path* *allocation-header-slow-path*))

(defun allocation-fast-clobbers (kind)
  (if (eq kind :cons) '(0 1 2 9 26) '(0 1 27)))

(defun allocation-unspent-bytes (world)
  (- (proof-heap-limit world) (proof-box-top world)))

(defun allocation-reservation-address (kind bytes world)
  (if (eq kind :cons)
      (- (proof-cons-floor world) bytes)
    (proof-box-top world)))

(defun allocation-fast-machine-return-p (kind bytes before after)
  (let ((address (allocation-reservation-address kind bytes before)))
    (and (proof-frame-return-p (allocation-fast-clobbers kind) t before after)
         (proof-span-p address bytes)
         (equal (proof-world-reg 0 after) address)
         (equal (allocation-unspent-bytes after)
                (- (allocation-unspent-bytes before) bytes))
         (equal (proof-world-regions after) (proof-world-regions before))
         (equal (proof-world-replies after) (proof-world-replies before))
         (proof-streams-preserved-p before after)
         (if (eq kind :cons)
             (and (equal (proof-box-top after) (proof-box-top before))
                  (equal (proof-heap-limit after) (- (proof-heap-limit before) bytes))
                  (equal (proof-cons-floor after) address)
                  (equal (allocation-memory after)
                         (boymoo-model::a64-write-bytes
                          8 (- (proof-heap-base before) 112) address (allocation-memory before))))
           (and (equal (proof-box-top after) (+ address bytes))
                (equal (proof-heap-limit after) (proof-heap-limit before))
                (equal (proof-cons-floor after) (proof-cons-floor before))
                (equal (allocation-memory after) (allocation-memory before)))))))

(defthm allocation-fast-machine-return
  (implies (and (allocation-request-machine-pre-p kind bytes origin before)
                (proof-allocation-fits-p kind bytes before)
                (equal after (allocation-path-end (allocation-fast-path kind) before)))
           (allocation-fast-machine-return-p kind bytes before after))
  :rule-classes nil
  :hints (("Goal" :cases ((eq kind :cons)))))

(defthm allocation-fast-checked-return
  (let* ((path (allocation-fast-path kind))
         (cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-request-machine-pre-p kind bytes origin before)
                  (proof-allocation-fits-p kind bytes before)
                  (allocation-path-ready-p path cuts before)
                  (equal after (allocation-path-end path before)))
             (and (allocation-fast-machine-return-p kind bytes before after)
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-machine-return
                 (:instance allocation-checked-cut
                  (instructions (allocation-fast-path kind)) (world before)
                  (cuts (list (proof-world-reg 30 before)))))
           :in-theory (disable allocation-checked-cut allocation-request-machine-pre-p
                               allocation-fast-path allocation-path-end
                               allocation-path-ready-p proof-segment-p
                               proof-allocation-fits-p))))

(defun allocation-word-overflow-p (kind bytes world)
  (and (eq kind :header)
       (<= *allocation-word-modulus* (+ (proof-box-top world) bytes))))

(defthm allocation-header-overflow-edge
  (let* ((demand (+ (proof-box-top before) bytes))
         (stop (allocation-code-address (proof-resource-label :word-size) origin))
         (cuts (list stop))
         (path *allocation-header-overflow-path*))
    (implies (and (allocation-request-machine-pre-p :header bytes origin before)
                  (allocation-word-overflow-p :header bytes before)
                  (allocation-path-ready-p path cuts before)
                  (equal after (allocation-path-end path before)))
             (and (proof-resource-bound-p :word-size demand before)
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-checked-cut
                         (instructions *allocation-header-overflow-path*) (world before)
                         (cuts (list (allocation-code-address
                                      (proof-resource-label :word-size) origin)))))
           :in-theory (disable allocation-checked-cut allocation-path-ready-p
                               proof-segment-p))))

(defun allocation-collector-entry-p (kind bytes origin before)
  (and (not (proof-world-stop before))
       (equal (proof-world-pc before) (allocation-code-address "rt:collect" origin))
       (equal (proof-world-reg 0 before) bytes)
       (equal (proof-world-reg 1 before) (if (eq kind :cons) 1 0))))

(defun allocation-collector-prefix-p (before cut)
  (and (proof-register-frame-p 30 *proof-volatile-registers* before cut)
       (equal (allocation-sp cut) (allocation-sp before))
       (equal (allocation-memory cut) (allocation-memory before))
       (equal (proof-world-regions cut) (proof-world-regions before))
       (equal (proof-world-replies cut) (proof-world-replies before))
       (proof-streams-preserved-p before cut)))

(defthm allocation-slow-to-collector
  (let* ((path (allocation-slow-path kind))
         (cuts (list (allocation-code-address "rt:collect" origin))))
    (implies (and (allocation-request-machine-pre-p kind bytes origin before)
                  (not (proof-allocation-fits-p kind bytes before))
                  (not (allocation-word-overflow-p kind bytes before))
                  (allocation-path-ready-p path cuts before)
                  (equal cut (allocation-path-end path before)))
             (and (allocation-collector-entry-p kind bytes origin cut)
                  (allocation-collector-prefix-p before cut)
                  (proof-segment-p (len path) cuts before :cut cut))))
  :rule-classes nil
  :hints (("Goal" :cases ((eq kind :cons))
           :use ((:instance allocation-checked-cut (after cut) (world before)
                  (instructions (allocation-slow-path kind))
                  (cuts (list (allocation-code-address "rt:collect" origin)))))
           :in-theory (disable allocation-checked-cut allocation-path-ready-p proof-segment-p))))
