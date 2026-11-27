(in-package "BOYMOO-PROOFS")

(include-book "entry-bindings")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine proof-stack-top
                    proof-stack-limit proof-machine-limit proof-heap-p proof-compiled-entry-p proof-environment-p
                    proof-segment-p proof-instruction-effect generated-sp generated-load-word generated-path-p
                    generated-path-after generated-full-prologue-fits-path generated-address-path
                    boymoo-compiler::gen-term boymoo-compiler::bind-formals boymoo-compiler::declaration-list expt))

(local
 (defthm generated-fitting-prologue-keeps-value-top-and-limit
   (let ((after (generated-path-after (generated-full-prologue-fits-path arity high) before)))
     (implies (and (unsigned-byte-p 64 (* 8 arity)) (unsigned-byte-p 64 (* 8 (- high arity)))
                   (generated-ordinary-machine-p before))
              (and (equal (proof-stack-limit after) (proof-stack-limit before))
                   (equal (proof-stack-top after) (proof-stack-top before)))))
   :hints (("Goal" :in-theory (enable generated-full-prologue-fits-path generated-reservation-check-path
                                      generated-address-path generated-path-after proof-stack-limit proof-stack-top)))
   :rule-classes nil))

(defthm generated-fitting-definition-prologue-establishes-body-bindings-and-reservation
  (let* ((compiler-formals (boymoo-compiler::declaration-list (cadr definition)))
         (arity (len compiler-formals)) (scope (boymoo-compiler::bind-formals compiler-formals 0 nil))
         (body-code (boymoo-compiler::gen-term (caddr definition) scope arity t context nil arity (+ serial 2)))
         (high (mv-nth 1 body-code)) (extra (* 8 (- high arity)))
         (path (generated-full-prologue-fits-path arity high)) (after (generated-path-after path before))
         (body (+ (proof-world-pc before) (* 4 (len path)) (if (< arity high) 8 4)))
         (frame (proof-world-reg 19 after)) (saved-sp (- (generated-sp before) 16))
         (bindings (pairlis$ formals (generated-consecutive-slots arity 0))))
    (implies (and (equal (len args) arity) (symbol-listp formals) (no-duplicatesp-equal formals)
                  (equal (len formals) arity) (natp high) (<= arity high)
                  (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                  (unsigned-byte-p 64 (* 8 arity)) (unsigned-byte-p 64 extra)
                  (<= (+ (proof-stack-top before) extra) (proof-stack-limit before))
                  (<= (proof-machine-limit before) saved-sp) (< body (expt 2 64))
                  (generated-ordinary-machine-p before) (generated-path-p path (list body) before))
             (and (proof-segment-p (len path) (list body) before :cut after)
                  (proof-compiled-entry-p body args after objects packages)
                  (proof-environment-p bindings (pairlis$ formals args) frame after objects packages)
                  (equal frame (- (proof-stack-top before) (* 8 arity)))
                  (<= (+ frame (* 8 high)) (proof-stack-limit after))
                  (equal (generated-sp after) saved-sp)
                  (equal (generated-load-word saved-sp after) (proof-world-reg 19 before))
                  (equal (generated-load-word (+ saved-sp 8) after) (proof-world-reg 30 before)))))
  :hints (("Goal"
           :use ((:instance generated-full-fitting-prologue-establishes-body-entry
                            (high (mv-nth 1 (boymoo-compiler::gen-term
                                             (caddr definition) (boymoo-compiler::bind-formals
                                                                 (boymoo-compiler::declaration-list (cadr definition)) 0 nil)
                                             (len (boymoo-compiler::declaration-list (cadr definition)))
                                             t context nil (len (boymoo-compiler::declaration-list (cadr definition))) (+ serial 2)))))
                 (:instance generated-function-entry-provides-body-environment
                            (world (generated-path-after
                                    (generated-full-prologue-fits-path (len args)
                                     (mv-nth 1 (boymoo-compiler::gen-term
                                                (caddr definition) (boymoo-compiler::bind-formals
                                                                    (boymoo-compiler::declaration-list (cadr definition)) 0 nil)
                                                (len args) t context nil (len args) (+ serial 2)))) before)))
                 (:instance generated-fitting-prologue-keeps-value-top-and-limit
                            (arity (len args))
                            (high (mv-nth 1 (boymoo-compiler::gen-term
                                             (caddr definition) (boymoo-compiler::bind-formals
                                                                 (boymoo-compiler::declaration-list (cadr definition)) 0 nil)
                                             (len args) t context nil (len args) (+ serial 2))))))
           :in-theory (enable proof-compiled-entry-p proof-prefix-preserved-p)))
  :rule-classes nil)
