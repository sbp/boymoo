(in-package "BOYMOO-PROOFS")

(include-book "prologue")
(include-book "addresses")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-segment-p proof-step proof-world-reg proof-world-stop proof-world-pc
                    proof-instruction-effect generated-address-path generated-load-word generated-sp
                    boymoo-model::a64-unsigned expt))

(defun generated-reservation-check-path (bytes)
  (append (generated-address-path 0 25 bytes nil)
          '((:arithmetic-reg 3 64 31 0 24 0 0) (:branch-cond 8 9))))

(local
 (defthm generated-prologue-append-length
   (equal (len (append first second)) (+ (len first) (len second)))))

(defthm generated-prologue-checks-full-width-demand
  (let* ((pc (proof-world-pc before))
         (path (generated-reservation-check-path bytes))
         (required (+ (proof-world-reg 25 before) bytes))
         (fits (<= required (proof-world-reg 24 before)))
         (end (+ pc (* 4 (len path)) (if fits 4 0)))
         (after (generated-path-after path before)))
    (implies (and (unsigned-byte-p 64 bytes) (< required (expt 2 64))
                  (< (+ pc (* 4 (len path)) 4) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p path (list end) before))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (equal (proof-world-pc after) end)
                  (equal (proof-world-reg 0 after) required)
                  (equal (generated-sp after) (generated-sp before))
                  (equal (proof-world-reg 25 after) (proof-world-reg 25 before))
                  (equal (generated-load-word address after)
                         (generated-load-word address before)))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut
                           (instructions (generated-reservation-check-path bytes))
                           (cuts (list (+ (proof-world-pc before)
                                          (* 4 (len (generated-reservation-check-path bytes)))
                                          (if (<= (+ (proof-world-reg 25 before) bytes)
                                                  (proof-world-reg 24 before)) 4 0)))))
           :in-theory (disable generated-path-p)))
  :rule-classes nil)

(defun generated-full-prologue-fits-path (arity high)
  (append *generated-prologue-depth-path*
          '((:pair nil 31 19 30 :pre -16))
          (if (< arity high) (generated-reservation-check-path (* 8 (- high arity))) nil)
          (generated-address-path 19 25 (* 8 arity) t)))

(defthm generated-full-prologue-when-frame-fits
  (let* ((pc (proof-world-pc before))
         (top (proof-world-reg 25 before))
         (sp (- (generated-sp before) 16))
         (argument-bytes (* 8 arity))
         (extra-bytes (* 8 (- high arity)))
         (path (generated-full-prologue-fits-path arity high))
         (end (+ pc (* 4 (len path)) (if (< arity high) 8 4)))
         (after (generated-path-after path before)))
    (implies (and (natp arity) (natp high) (<= arity high)
                  (unsigned-byte-p 64 argument-bytes) (<= argument-bytes top)
                  (unsigned-byte-p 64 extra-bytes) (<= (+ top extra-bytes) (proof-world-reg 24 before))
                  (<= 16 (generated-sp before)) (<= (proof-world-reg 23 before) sp)
                  (< end (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before)) (generated-path-p path (list end) before))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (equal (proof-world-pc after) end)
                  (equal (generated-sp after) sp)
                  (equal (generated-load-word sp after) (proof-world-reg 19 before))
                  (equal (generated-load-word (+ 8 sp) after) (proof-world-reg 30 before))
                  (equal (proof-world-reg 19 after) (- top argument-bytes))
                  (equal (proof-world-reg 25 after) top))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut
                           (instructions (generated-full-prologue-fits-path arity high))
                           (cuts (list (+ (proof-world-pc before)
                                          (* 4 (len (generated-full-prologue-fits-path arity high)))
                                          (if (< arity high) 8 4)))))
           :in-theory (e/d (proof-span-p proof-disjoint-p) (generated-path-p))))
  :rule-classes nil)
