(in-package "BOYMOO-PROOFS")

(include-book "wide-prologue")
(include-book "growth")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-step proof-segment-p proof-instruction-effect proof-label-address
                    generated-path-p generated-address-path generated-load-word generated-sp
                    boymoo-model::a64-unsigned expt))

(defun generated-prologue-depth-stop-path (target before)
  (append *generated-prologue-depth-path*
          (list (list :branch (- target (+ (proof-world-pc before) 12)) t))))

(defthm generated-prologue-reaches-failed-depth-check
  (let* ((pc (proof-world-pc before))
         (next-sp (- (generated-sp before) 16))
         (target (proof-label-address (proof-resource-label :machine-stack) base labels))
         (path (generated-prologue-depth-stop-path target before))
         (after (generated-path-after path before)))
    (implies (and (unsigned-byte-p 64 target) (< (+ 16 pc) (expt 2 64))
                  (<= 16 (generated-sp before)) (< next-sp (proof-machine-limit before))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p path (list target) before))
             (and (proof-segment-p 4 (list target) before :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (+ pc 16))
                  (equal (generated-sp after) (generated-sp before))
                  (proof-resource-bound-p :machine-stack next-sp after))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut
                           (instructions (generated-prologue-depth-stop-path
                                          (proof-label-address (proof-resource-label :machine-stack) base labels)
                                          before))
                           (cuts (list (proof-label-address (proof-resource-label :machine-stack) base labels))))
           :in-theory (enable proof-resource-bound-p)))
  :rule-classes nil)

(defun generated-growing-prologue-path (bytes target before)
  (let ((prefix (append *generated-prologue-depth-path*
                        '((:pair nil 31 19 30 :pre -16))
                        (generated-reservation-check-path bytes))))
    (append prefix
            (list (list :branch (- target (+ (proof-world-pc before) 4 (* 4 (len prefix)))) t)))))

(local
 (defthm generated-prologue-path-append-length
   (equal (len (append first second)) (+ (len first) (len second)))))

(defthm generated-prologue-reaches-growth-entry
  (let* ((pc (proof-world-pc before))
         (sp (- (generated-sp before) 16))
         (required (+ (proof-stack-top before) bytes))
         (target (proof-label-address "rt:grow" base labels))
         (path (generated-growing-prologue-path bytes target before))
         (link (+ pc 4 (* 4 (len path))))
         (after (generated-path-after path before)))
    (implies (and (unsigned-byte-p 64 target) (posp bytes) (unsigned-byte-p 64 bytes)
                  (<= 16 (generated-sp before)) (<= (proof-machine-limit before) sp)
                  (< (proof-stack-limit before) required) (< required (expt 2 64))
                  (< link (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p path (list target) before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 0 after) required)
                  (equal (proof-stack-top after) (proof-stack-top before))
                  (equal (generated-sp after) sp)
                  (equal (generated-load-word sp after) (proof-world-reg 19 before))
                  (equal (generated-load-word (+ sp 8) after) (proof-world-reg 30 before)))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut
                           (instructions (generated-growing-prologue-path
                                          bytes (proof-label-address "rt:grow" base labels) before))
                           (cuts (list (proof-label-address "rt:grow" base labels))))
           :in-theory (enable proof-span-p proof-disjoint-p)))
  :rule-classes nil)

(defthm generated-prologue-after-successful-growth
  (let* ((sp (generated-sp entered))
         (top (proof-stack-top entered))
         (resume (proof-world-reg 30 entered))
         (bytes (* 8 arity))
         (path (generated-address-path 19 25 bytes t))
         (body (+ resume (* 4 (len path))))
         (after (generated-path-after path returned))
         (machine-end (+ (- (proof-machine-limit entered) *proof-machine-margin*)
                         *proof-machine-reservation*)))
    (implies (and (natp arity) (unsigned-byte-p 64 bytes) (<= bytes top)
                  (natp required) (<= required (proof-stack-end entered))
                  (<= (+ sp 16) machine-end) (<= (+ sp 16) (expt 2 64))
                  (< body (expt 2 64)) (not (proof-world-stop returned))
                  (proof-grow-return-p "rt:grow" required entered returned old-objects new-objects packages)
                  (generated-path-p path (list body) returned))
             (and (proof-segment-p (len path) (list body) returned :cut after)
                  (equal (proof-world-pc after) body)
                  (equal (proof-world-reg 19 after) (- top bytes))
                  (equal (proof-stack-top after) top)
                  (<= required (proof-stack-limit after))
                  (equal (generated-sp after) sp)
                  (equal (generated-load-word sp after) (generated-load-word sp entered))
                  (equal (generated-load-word (+ sp 8) after)
                         (generated-load-word (+ sp 8) entered)))))
  :hints (("Goal"
           :use ((:instance generated-grow-return-preserves-prologue-frame
                            (before entered) (after returned))
                 (:instance generated-address-reaches-continuation (rd 19) (rn 25)
                            (bytes (* 8 arity)) (subtract t) (before returned)))
           :in-theory (disable proof-grow-return-p)))
  :rule-classes nil)
