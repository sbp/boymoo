(in-package "BOYMOO-PROOFS")

(include-book "runtime-image")
(include-book "representation")

(logic)
(set-verify-guards-eagerness 0)

(defconst *integer-example-code-base* #x10000)
(defconst *integer-example-return* #xfffc)
(defconst *integer-example-stack-end* #x21000)
(defconst *integer-example-value-stack* #x30000)
(defconst *integer-example-heap-base* #x40000)
(defconst *integer-example-free* #x41000)

(defun integer-example-store-magnitude (count address magnitude machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      machine
    (integer-example-store-magnitude
     (1- count) (+ address 8) (floor magnitude *integer-limb-base*)
     (boymoo-model::a64-store 8 address (mod magnitude *integer-limb-base*) machine))))

(defun integer-example-datum (value address machine)
  (cond ((proof-immediate-integer-p value) (mv (proof-integer-word value) machine))
        ((characterp value) (mv (proof-character-word value) machine))
        (t (let* ((magnitude (abs (ifix value)))
                  (count (ceiling (integer-length magnitude) 32))
                  (machine (boymoo-model::a64-store 8 address (integer-header count) machine))
                  (machine (boymoo-model::a64-store 8 (+ address 8)
                                                     (if (< value 0) 1 0) machine)))
             (mv (+ (- address *integer-example-heap-base*) 2)
                 (integer-example-store-magnitude count (+ address 16) magnitude machine))))))

(defun integer-example-world (label x0 x1 machine replies)
  (let* ((registers (list (cons 0 x0) (cons 1 x1)
                          (cons 23 #x20000) (cons 24 #x31000)
                          (cons 25 *integer-example-value-stack*)
                          (cons 26 #x50000) (cons 27 *integer-example-free*)
                          (cons 28 *integer-example-heap-base*)
                          (cons 30 *integer-example-return*)))
         (pc (integer-runtime-address label *integer-example-code-base*))
         (machine (boymoo-model::a64-state registers *integer-example-stack-end*
                                           pc 0 (boymoo-model::a64-memory machine)))
         (loaded (proof-load-cleared-string *integer-runtime-bytes*
                                             *integer-example-code-base* machine))
         (regions (list (proof-region *integer-example-code-base*
                                       (+ *integer-example-code-base*
                                          (length *integer-runtime-bytes*)) :rx)
                        (proof-region #x20000 *integer-example-stack-end* :rw)
                        (proof-region *integer-example-value-stack* #x31000 :rw)
                        (proof-region *integer-example-heap-base* #x50000 :rw))))
    (proof-world loaded regions 4096 nil nil nil replies nil)))

(defun integer-example-start (label left right replies)
  (mv-let (x0 first)
    (integer-example-datum left (+ *integer-example-heap-base* 32) nil)
    (mv-let (x1 second)
      (integer-example-datum right (+ *integer-example-heap-base* 96) first)
      (integer-example-world label x0 x1 second replies))))

(defun integer-example-result (world)
  (let* ((word (proof-world-reg 0 world))
         (address (proof-pointer-address word *integer-example-heap-base*))
         (objects (list (proof-object address :active :header 0))))
    (proof-view word *integer-example-heap-base* objects nil
                (proof-world-machine world))))

(defun integer-check-runtime-result (entry left right expected)
  (let ((before (integer-example-start entry left right nil)))
    (mv-let (reason after)
      (proof-run 1024 (list *integer-example-return*) before)
      (and (eq reason :cut)
           (equal (integer-example-result after) (proof-value-view expected))
           (equal (boymoo-model::a64-sp (proof-world-machine after))
                  *integer-example-stack-end*)
           (equal (proof-world-reg 25 after) *integer-example-value-stack*)))))

(assert-event
 (and (integer-check-runtime-result "rt:z-add-op" (- (expt 2 62)) -1
                                    (- -1 (expt 2 62)))
      (integer-check-runtime-result "rt:z-add-op" (+ (expt 2 96) 7) (- (expt 2 96))
                                    7)
      (integer-check-runtime-result "rt:z-negate-op" (expt 2 62) 0
                                    (- (expt 2 62)))
      (integer-check-runtime-result "rt:z-multiply-op" (1- (expt 2 64)) (- (expt 2 64))
                                    (* (1- (expt 2 64)) (- (expt 2 64))))
      (integer-check-runtime-result "rt:z-multiply-op" (expt 2 96) #\A 0)))

(assert-event
 (and (integer-check-runtime-result "rt:z-compare" (- (expt 2 96)) -1 -1)
      (integer-check-runtime-result "rt:z-compare" (expt 2 96) (+ 1 (expt 2 96)) -1)
      (integer-check-runtime-result "rt:z-compare" 42 42 0)
      (integer-check-runtime-result "rt:z-compare" 1 #\A 1)))

(defun integer-check-ash (left right)
  (integer-check-runtime-result
   "jet:COMMON-LISP::ASH" left right
   (boymoo-model::core-datum (boymoo-model::core-prelude 'ash (list (ifix left) (ifix right))))))

(defun integer-check-xor (left right)
  (integer-check-runtime-result
   "jet:ACL2::BINARY-LOGXOR" left right
   (boymoo-model::core-datum
    (boymoo-model::core-prelude 'acl2::binary-logxor (list (ifix left) (ifix right))))))

(assert-event
 (and
      (integer-check-ash (- (expt 2 62)) 0)
      (integer-check-ash (- (expt 2 62)) -63)
      (integer-check-ash (- (expt 2 62)) 1)
      (integer-check-ash -1 62)
      (integer-check-ash 1 62)
      (integer-check-ash #\A 15)
      (integer-check-ash (expt 2 64) #\A)
      (integer-check-ash (expt 2 64) 97)
      (integer-check-ash (- (expt 2 64)) -32)
      (integer-check-ash (- (+ (expt 2 96) 1)) -65)
      (integer-check-ash (- (+ (expt 2 96) (expt 2 32))) -33)
      (integer-check-ash (- (expt 2 64)) (- -1 (expt 2 62)))
      (integer-check-ash (expt 2 64) (- -1 (expt 2 62)))))

(assert-event
 (and (integer-check-xor (- (expt 2 62)) (1- (expt 2 62)))
      (integer-check-xor (expt 2 96) -1)
      (integer-check-xor (- (expt 2 160)) (+ 1 (expt 2 96)))
      (integer-check-xor (- (expt 2 96)) (- 1 (expt 2 160)))
      (integer-check-xor (- (expt 2 64)) #\A)
      (integer-check-xor #\A #\B)))

(defun integer-check-number-size-stop ()
  (let* ((message "memory exhausted: a number is too large")
         (before (integer-example-start "jet:COMMON-LISP::ASH" 1 (expt 2 62)
                                        (list (length message) 1))))
    (mv-let (reason after)
      (proof-run 1024 (list *integer-example-return*) before)
      (and (equal reason (cons :exit 3))
           (proof-resource-observation-p after)
           (equal (proof-world-stderr after)
                  (append (proof-string-bytes (coerce message 'list)) '(10)))))))

(assert-event (integer-check-number-size-stop))
