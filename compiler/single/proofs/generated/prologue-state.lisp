(in-package "BOYMOO-PROOFS")

(include-book "prologue-heap")
(include-book "prefix-suffix")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-heap-layout-p proof-compiled-entry-p proof-world-machine
                    proof-world-pc proof-world-stop proof-world-reg proof-instruction-effect proof-segment-p
                    proof-stack-base proof-stack-top proof-stack-limit proof-stack-end proof-machine-limit
                    proof-stack-prefix proof-prefix-preserved-p proof-grow-return-p proof-preserved-heap-p
                    proof-heap-frame-p proof-frame-return-p proof-register-frame-p
                    generated-load-word generated-sp generated-path-after generated-path-p
                    generated-address-path generated-full-prologue-fits-path generated-growing-prologue-path
                    generated-reservation-check-path generated-heap-world-equiv proof-stack-end
                    proof-resource-bound-p proof-resource-observation-p generated-before-cuts-p proof-advance expt))

(defund generated-prologue-saved-world (before)
  (proof-instruction-effect '(:pair nil 31 19 30 :pre -16)
                            (generated-path-after *generated-prologue-depth-path* before)))

(local
 (defthm generated-depth-check-preserves-heap-observations
   (let ((after (generated-path-after *generated-prologue-depth-path* before)))
     (implies (generated-ordinary-machine-p before)
              (and (generated-heap-world-equiv after before)
                   (equal (proof-world-reg 23 after) (proof-world-reg 23 before))
                   (equal (proof-world-reg 25 after) (proof-world-reg 25 before))
                   (generated-ordinary-machine-p after))))
   :hints (("Goal" :in-theory (enable generated-path-after)))))

(local
 (defthm generated-frame-save-preserves-ordinary-machine
   (implies (generated-ordinary-machine-p before)
            (generated-ordinary-machine-p (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) before)))))

(defthm generated-prologue-saved-world-keeps-incoming-roots
  (let ((after (generated-prologue-saved-world before)))
    (implies (and (proof-heap-p before objects packages) (generated-ordinary-machine-p before)
                  (<= (proof-machine-limit before) (- (generated-sp before) 16)))
             (and (proof-heap-p after objects packages)
                  (equal (proof-stack-base after) (proof-stack-base before))
                  (equal (proof-stack-top after) (proof-stack-top before))
                  (proof-prefix-preserved-p (proof-stack-top before) before after objects objects packages)
                  (equal (generated-sp after) (- (generated-sp before) 16)))))
  :hints (("Goal"
           :use (:instance generated-prologue-frame-save-keeps-valid-heap
                           (before (generated-path-after *generated-prologue-depth-path* before)))
           :in-theory (e/d (generated-prologue-saved-world proof-prefix-preserved-p) (generated-effect-of-save-frame))))
  :rule-classes nil)

(local
 (defthm generated-saved-prologue-world-is-ordinary
   (implies (generated-ordinary-machine-p before)
            (generated-ordinary-machine-p (generated-prologue-saved-world before)))
   :hints (("Goal" :in-theory (e/d (generated-prologue-saved-world) (generated-effect-of-save-frame))))))

(defthm generated-address-adjustment-keeps-heap-observations
  (let ((after (generated-path-after (generated-address-path rd rn bytes subtract) before)))
    (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31) (unsigned-byte-p 64 bytes)
                  (not (member-equal rd '(23 24 25 26 27 28))))
             (and (generated-heap-world-equiv after before)
                  (implies (generated-ordinary-machine-p before) (generated-ordinary-machine-p after)))))
  :hints (("Goal" :in-theory (enable generated-address-path generated-path-after))))

(local
 (defthm generated-reservation-check-keeps-heap-observations
   (let ((after (generated-path-after (generated-reservation-check-path bytes) before)))
     (implies (and (unsigned-byte-p 64 bytes) (generated-ordinary-machine-p before))
              (and (generated-heap-world-equiv after before)
                   (generated-ordinary-machine-p after))))
   :hints (("Goal" :in-theory (enable generated-reservation-check-path generated-path-after)))))

(local
 (defthm generated-prologue-fits-keeps-saved-heap
   (let ((after (generated-path-after (generated-full-prologue-fits-path arity high) before)))
     (implies (and (unsigned-byte-p 64 (* 8 arity)) (unsigned-byte-p 64 (* 8 (- high arity)))
                   (generated-ordinary-machine-p before))
              (generated-heap-world-equiv after (generated-prologue-saved-world before))))
   :hints (("Goal"
            :in-theory (e/d (generated-full-prologue-fits-path generated-prologue-saved-world generated-path-after)
                            (generated-effect-of-save-frame))))))

(local
 (defthm generated-prologue-growth-edge-keeps-saved-heap
   (let ((after (generated-path-after (generated-growing-prologue-path bytes target before) before)))
     (implies (and (unsigned-byte-p 64 bytes) (generated-ordinary-machine-p before))
              (generated-heap-world-equiv after (generated-prologue-saved-world before))))
   :hints (("Goal"
            :in-theory (e/d (generated-growing-prologue-path generated-prologue-saved-world generated-path-after)
                            (generated-effect-of-save-frame))))))

(local
 (defthm generated-incoming-compiled-entry-supplies-heap
   (implies (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
            (and (proof-heap-p before objects packages) (<= (* 8 (len args)) (proof-stack-top before))))
   :hints (("Goal" :in-theory (enable proof-compiled-entry-p)))))

(defthm generated-full-fitting-prologue-establishes-body-entry
  (let* ((arity (len args)) (extra (* 8 (- high arity)))
         (sp (- (generated-sp before) 16)) (top (proof-stack-top before))
         (path (generated-full-prologue-fits-path arity high))
         (body (+ (proof-world-pc before) (* 4 (len path)) (if (< arity high) 8 4)))
         (after (generated-path-after path before)))
    (implies (and (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                  (natp high) (<= arity high) (unsigned-byte-p 64 (* 8 arity)) (unsigned-byte-p 64 extra)
                  (<= (+ top extra) (proof-stack-limit before)) (<= (proof-machine-limit before) sp)
                  (< body (expt 2 64)) (generated-ordinary-machine-p before)
                  (generated-path-p path (list body) before))
             (and (proof-segment-p (len path) (list body) before :cut after)
                  (proof-compiled-entry-p body args after objects packages)
                  (equal (proof-world-reg 19 after) (- top (* 8 arity)))
                  (equal (generated-sp after) sp)
                  (equal (generated-load-word sp after) (proof-world-reg 19 before))
                  (equal (generated-load-word (+ 8 sp) after) (proof-world-reg 30 before))
                  (proof-prefix-preserved-p top before after objects objects packages))))
  :hints (("Goal"
           :use (generated-incoming-compiled-entry-supplies-heap
                 (:instance generated-full-prologue-when-frame-fits (arity (len args)))
                 generated-prologue-saved-world-keeps-incoming-roots
                 (:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-heap-layout-value-stack-bounds (world before))
                 generated-incoming-machine-bound-prevents-subtraction-wrap
                 (:instance generated-compiled-arguments-survive-prefix-preservation (old-objects objects) (new-objects objects)
                            (after (generated-path-after (generated-full-prologue-fits-path (len args) high) before))))
           :in-theory (enable proof-prefix-preserved-p)))
  :rule-classes nil)

(defthm generated-growing-prologue-establishes-heap-at-runtime-entry
  (let* ((path (generated-growing-prologue-path bytes target before))
         (after (generated-path-after path before)))
    (implies (and (proof-heap-p before objects packages) (generated-ordinary-machine-p before)
                  (<= (proof-machine-limit before) (- (generated-sp before) 16)) (unsigned-byte-p 64 bytes))
             (and (proof-heap-p after objects packages)
                  (equal (proof-stack-base after) (proof-stack-base before))
                  (equal (proof-stack-top after) (proof-stack-top before))
                  (proof-prefix-preserved-p (proof-stack-top before) before after objects objects packages))))
  :hints (("Goal" :use generated-prologue-saved-world-keeps-incoming-roots
                  :in-theory (e/d (proof-prefix-preserved-p) (generated-value-top-is-x25))))
  :rule-classes nil)

(local
 (defthm generated-growth-return-keeps-entry-views
   (implies (proof-grow-return-p "rt:grow" required entered returned objects new-objects packages)
            (and (proof-heap-p returned new-objects packages)
                 (equal (proof-stack-base returned) (proof-stack-base entered))
                 (equal (proof-stack-top returned) (proof-stack-top entered))
                 (proof-prefix-preserved-p (proof-stack-top entered) entered returned objects new-objects packages)))
   :hints (("Goal"
            :use ((:instance generated-register-in-preserved-frame (register 25) (last 30)
                             (clobbers '(8 9 10 11 12 24)) (before entered) (after returned)))
            :in-theory (enable proof-grow-return-p proof-preserved-heap-p proof-heap-frame-p proof-frame-return-p)))
   :rule-classes nil))

(local
 (defthm generated-growth-and-frame-base-preserve-argument-views
   (let* ((arity (len args))
          (entered (generated-path-after (generated-growing-prologue-path bytes target before) before))
          (frame-path (generated-address-path 19 25 (* 8 arity) t))
          (after (generated-path-after frame-path returned))
          (top (proof-stack-top before)))
     (implies (and (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                   (generated-ordinary-machine-p before)
                   (<= (proof-machine-limit before) (- (generated-sp before) 16))
                   (unsigned-byte-p 64 bytes) (unsigned-byte-p 64 (* 8 arity))
                   (proof-grow-return-p "rt:grow" (+ top bytes) entered returned objects new-objects packages))
              (and (proof-compiled-entry-p (proof-world-pc after) args after new-objects packages)
                   (proof-prefix-preserved-p top before after objects new-objects packages))))
   :hints (("Goal"
            :use (generated-incoming-compiled-entry-supplies-heap
                  generated-growing-prologue-establishes-heap-at-runtime-entry
                  (:instance generated-growth-return-keeps-entry-views
                             (required (+ (proof-stack-top before) bytes))
                             (entered (generated-path-after (generated-growing-prologue-path bytes target before) before)))
                  (:instance generated-address-adjustment-keeps-heap-observations
                             (rd 19) (rn 25) (bytes (* 8 (len args))) (subtract t) (before returned))
                  (:instance generated-prefix-preserved-transitive
                             (top (proof-stack-top before)) (first before)
                             (middle (generated-path-after (generated-growing-prologue-path bytes target before) before))
                             (last returned) (first-objects objects) (middle-objects objects) (last-objects new-objects))
                  (:instance generated-compiled-arguments-survive-prefix-preservation
                             (old-objects objects) (after returned)))
            :in-theory (e/d (proof-prefix-preserved-p proof-compiled-entry-p)
                            (generated-value-top-is-x25 generated-address-adjustment-keeps-heap-observations))))
   :rule-classes nil))

(defthm generated-growing-prologue-establishes-body-entry
  (let* ((arity (len args)) (bytes (* 8 (- high arity)))
         (sp (- (generated-sp before) 16)) (top (proof-stack-top before)) (required (+ top bytes))
         (target (proof-label-address "rt:grow" base labels))
         (entry-path (generated-growing-prologue-path bytes target before))
         (entered (generated-path-after entry-path before))
         (frame-path (generated-address-path 19 25 (* 8 arity) t))
         (body (+ (proof-world-pc before) 4 (* 4 (len entry-path)) (* 4 (len frame-path))))
         (machine-end (+ (- (proof-machine-limit entered) *proof-machine-margin*) *proof-machine-reservation*))
         (after (generated-path-after frame-path returned)))
    (implies (and (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                  (natp high) (< arity high) (unsigned-byte-p 64 bytes) (unsigned-byte-p 64 (* 8 arity))
                  (<= (proof-machine-limit before) sp) (< (proof-stack-limit before) required)
                  (< required (expt 2 64)) (unsigned-byte-p 64 target) (< body (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p entry-path (list target body) before)
                  (<= required (proof-stack-end entered)) (<= (+ sp 16) machine-end)
                  (generated-before-cuts-p grow-steps (list body) entered)
                  (equal returned (proof-advance grow-steps entered))
                  (proof-grow-return-p "rt:grow" required entered returned objects new-objects packages)
                  (not (proof-world-stop returned)) (generated-path-p frame-path (list body) returned))
             (and (proof-segment-p (+ (len entry-path) (nfix grow-steps) (len frame-path))
                                   (list body) before :cut after)
                  (proof-compiled-entry-p body args after new-objects packages)
                  (equal (proof-world-reg 19 after) (- top (* 8 arity)))
                  (<= required (proof-stack-limit after))
                  (equal (generated-sp after) sp)
                  (equal (generated-load-word sp after) (proof-world-reg 19 before))
                  (equal (generated-load-word (+ sp 8) after) (proof-world-reg 30 before))
                  (proof-prefix-preserved-p top before after objects new-objects packages))))
  :hints (("Goal"
           :use (generated-incoming-compiled-entry-supplies-heap
                 generated-incoming-machine-bound-prevents-subtraction-wrap
                 (:instance generated-heap-has-layout-and-roots (world before))
                 (:instance generated-growth-and-frame-base-preserve-argument-views
                            (bytes (* 8 (- high (len args)))) (target (proof-label-address "rt:grow" base labels)))
                 (:instance generated-growing-prologue-enters-body
                            (arity (len args)) (bytes (* 8 (- high (len args)))) (old-objects objects)
                            (target (proof-label-address "rt:grow" base labels))
                            (entry-path (generated-growing-prologue-path
                                         (* 8 (- high (len args))) (proof-label-address "rt:grow" base labels) before))
                            (entered (generated-path-after (generated-growing-prologue-path
                                         (* 8 (- high (len args))) (proof-label-address "rt:grow" base labels) before) before))
                            (frame-path (generated-address-path 19 25 (* 8 (len args)) t))
                            (body (+ (proof-world-pc before) 4
                                     (* 4 (len (generated-growing-prologue-path
                                                (* 8 (- high (len args))) (proof-label-address "rt:grow" base labels) before)))
                                     (* 4 (len (generated-address-path 19 25 (* 8 (len args)) t)))))))
           :in-theory (disable proof-label-address)))
  :rule-classes nil)
