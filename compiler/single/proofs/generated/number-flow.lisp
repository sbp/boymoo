(in-package "BOYMOO-PROOFS")

(include-book "runtime-flow")
(include-book "conditional-flow")
(include-book "arithmetic-paths")
(include-book "immediate-views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine proof-segment-p
                    proof-heap-base proof-heap-p proof-value-p proof-reg-value-p proof-machine-value-p
                    proof-runtime-value proof-runtime-entry proof-runtime-return-p proof-register-arguments-p
                    proof-instruction-effect generated-path-p generated-path-after generated-link-to
                    generated-integer-tag-path generated-integer-result-path generated-heap-world-equiv
                    proof-immediate-integer-p proof-integer-word evenp oddp expt))

(defun generated-inline-number-name-p (name)
  (member-eq name '(acl2::binary-+ acl2::unary-- <)))

(defun generated-inline-integer-arguments-p (name args)
  (and (proof-immediate-integer-p (car args))
       (or (eq name 'acl2::unary--) (proof-immediate-integer-p (cadr args)))))

(defun generated-inline-integer-result (name args)
  (case name
    (acl2::binary-+ (+ (car args) (cadr args)))
    (acl2::unary-- (- (car args)))
    (otherwise (< (car args) (cadr args)))))

(defthm generated-inline-number-source-value
  (implies (generated-inline-number-name-p name)
           (equal (proof-runtime-value name args program)
                  (boymoo-model::core-value (generated-inline-integer-result name args))))
  :hints (("Goal" :in-theory (enable proof-runtime-value boymoo-model::core-primitive))))

(defun generated-inline-integer-fast-p (name args)
  (and (generated-inline-integer-arguments-p name args)
       (or (eq name '<) (proof-immediate-integer-p (generated-inline-integer-result name args)))))

(defun generated-inline-integer-body-path (name args)
  (if (generated-inline-integer-arguments-p name args)
      (if (eq name '<)
          *generated-integer-less-than-path*
        (generated-integer-result-path (not (eq name 'acl2::unary--))
                                       (not (proof-immediate-integer-p (generated-inline-integer-result name args)))))
    nil))

(defthm generated-heap-equivalent-states-agree-on-register-value
  (implies (and (generated-heap-world-equiv after before)
                (equal (proof-world-reg register after) (proof-world-reg register before)))
           (equal (proof-reg-value-p register datum after objects packages)
                  (proof-reg-value-p register datum before objects packages)))
  :hints (("Goal" :in-theory (enable proof-reg-value-p)))
  :rule-classes nil)

(defthm generated-immediate-tag-matches-represented-integer
  (implies (proof-reg-value-p register datum world objects packages)
           (and (equal (not (evenp (proof-world-reg register world))) (proof-immediate-integer-p datum))
                (implies (proof-immediate-integer-p datum)
                         (equal (proof-world-reg register world) (proof-integer-word datum)))))
  :hints (("Goal"
           :use ((:instance generated-fast-atomic-values-have-canonical-words
                            (word (proof-world-reg register world)) (value datum)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance generated-fast-atomic-word-has-atomic-value
                            (word (proof-world-reg register world)) (value datum)
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (enable proof-reg-value-p proof-machine-value-p proof-immediate-integer-p oddp)))
  :rule-classes nil)

(defthm generated-inline-number-guard-keeps-source-operands
  (let* ((binary (not (eq name 'acl2::unary--)))
         (path (generated-integer-tag-path binary))
         (after (generated-path-after path before))
         (immediate (generated-inline-integer-arguments-p name args))
         (end (+ (proof-world-pc before) (* 4 (len path)) (if immediate 0 20))))
    (implies (and (proof-reg-value-p 0 (car args) before objects packages)
                  (implies binary (proof-reg-value-p 1 (cadr args) before objects packages))
                  (< (+ (proof-world-pc before) 32) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p path (cons end cuts) before))
             (and (proof-segment-p (len path) (cons end cuts) before :cut after)
                  (equal (proof-world-pc after) end)
                  (generated-ordinary-machine-p after) (not (proof-world-stop after))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-heap-world-equiv after before)
                  (proof-reg-value-p 0 (car args) after objects packages)
                  (implies binary (proof-reg-value-p 1 (cadr args) after objects packages)))))
  :hints (("Goal"
           :use ((:instance generated-immediate-tag-matches-represented-integer (register 0) (datum (car args)) (world before))
                 (:instance generated-immediate-tag-matches-represented-integer (register 1) (datum (cadr args)) (world before))
                 (:instance generated-integer-tag-guard-selects-edge (binary-p (not (eq name 'acl2::unary--))))
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-integer-tag-path (not (eq name 'acl2::unary--))))
                            (cuts (list (+ (proof-world-pc before)
                                           (* 4 (len (generated-integer-tag-path (not (eq name 'acl2::unary--)))))
                                           (if (generated-inline-integer-arguments-p name args) 0 20))))
                            (all-cuts (cons (+ (proof-world-pc before)
                                               (* 4 (len (generated-integer-tag-path (not (eq name 'acl2::unary--)))))
                                               (if (generated-inline-integer-arguments-p name args) 0 20)) cuts)))
                 (:instance generated-placed-path-to-cut
                            (instructions (generated-integer-tag-path (not (eq name 'acl2::unary--))))
                            (cuts (cons (+ (proof-world-pc before)
                                           (* 4 (len (generated-integer-tag-path (not (eq name 'acl2::unary--)))))
                                           (if (generated-inline-integer-arguments-p name args) 0 20)) cuts))))
           :in-theory (enable proof-reg-value-p)))
  :rule-classes nil)

(local
 (defthm generated-signed-number-comparison-returns-source-value
   (let* ((end (+ (proof-world-pc before) 24))
          (after (generated-path-after *generated-integer-less-than-path* before)))
     (implies (and (proof-immediate-integer-p x) (proof-immediate-integer-p y)
                   (proof-reg-value-p 0 x before objects packages) (proof-reg-value-p 1 y before objects packages)
                   (proof-heap-p before objects packages) (< end (expt 2 64))
                   (generated-ordinary-machine-p before) (not (proof-world-stop before))
                   (generated-path-p *generated-integer-less-than-path* (list end) before))
              (and (equal (proof-world-pc after) end)
                   (generated-ordinary-machine-p after) (not (proof-world-stop after))
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                   (generated-heap-world-equiv after before)
                   (proof-reg-value-p 0 (< x y) after objects packages))))
   :hints (("Goal"
            :use ((:instance generated-immediate-tag-matches-represented-integer (register 0) (datum x) (world before))
                  (:instance generated-immediate-tag-matches-represented-integer (register 1) (datum y) (world before))
                  generated-inline-immediate-less-than-path
                  (:instance generated-static-booleans-in-published-heap (world before)))
            :in-theory (enable proof-reg-value-p)))
   :rule-classes nil))

(local
 (defthm generated-number-arithmetic-result-or-source-operands
   (let* ((datum (if binary-p (+ x y) (- x)))
          (fast (proof-immediate-integer-p datum))
          (path (generated-integer-result-path binary-p (not fast)))
          (after (generated-path-after path before))
          (end (+ (proof-world-pc before) (if fast 24 20))))
     (implies (and (proof-immediate-integer-p x)
                   (proof-reg-value-p 0 x before objects packages)
                   (implies binary-p (and (proof-immediate-integer-p y) (proof-reg-value-p 1 y before objects packages)))
                   (< (+ (proof-world-pc before) 24) (expt 2 64))
                   (generated-ordinary-machine-p before) (not (proof-world-stop before))
                   (generated-path-p path (list end) before))
              (and (equal (proof-world-pc after) end)
                   (generated-ordinary-machine-p after) (not (proof-world-stop after))
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                   (generated-heap-world-equiv after before)
                   (proof-reg-value-p 0 (if fast datum x) after objects packages)
                   (implies (and (not fast) binary-p) (proof-reg-value-p 1 y after objects packages)))))
   :hints (("Goal"
            :use ((:instance generated-immediate-tag-matches-represented-integer (register 0) (datum x) (world before))
                  (:instance generated-immediate-tag-matches-represented-integer (register 1) (datum y) (world before))
                  generated-inline-arithmetic-result-or-slow-edge
                  (:instance generated-immediate-word-view (value (if binary-p (+ x y) (- x)))
                             (base (proof-heap-base before)) (machine (proof-world-machine before))))
            :in-theory (enable proof-reg-value-p proof-machine-value-p proof-value-p)))
   :rule-classes nil))

(defthm generated-inline-number-body-has-source-result-or-operands
  (let* ((binary (not (eq name 'acl2::unary--))) (fast (generated-inline-integer-fast-p name args))
         (path (generated-inline-integer-body-path name args)) (after (generated-path-after path before))
         (end (+ (proof-world-pc before) (if fast 24 20))))
    (implies (and (generated-inline-number-name-p name) (generated-inline-integer-arguments-p name args)
                  (proof-reg-value-p 0 (car args) before objects packages)
                  (implies binary (proof-reg-value-p 1 (cadr args) before objects packages))
                  (proof-heap-p before objects packages) (< (+ (proof-world-pc before) 24) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (member-equal end cuts) (generated-path-p path cuts before))
             (and (proof-segment-p (len path) cuts before :cut after)
                  (equal (proof-world-pc after) end)
                  (generated-ordinary-machine-p after) (not (proof-world-stop after))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-heap-world-equiv after before)
                  (proof-reg-value-p 0 (if fast (generated-inline-integer-result name args) (car args))
                                     after objects packages)
                  (implies (and (not fast) binary) (proof-reg-value-p 1 (cadr args) after objects packages)))))
  :hints (("Goal"
           :use ((:instance generated-signed-number-comparison-returns-source-value (x (car args)) (y (cadr args)))
                 (:instance generated-number-arithmetic-result-or-source-operands (x (car args)) (y (cadr args))
                            (binary-p (not (eq name 'acl2::unary--))))
                 (:instance generated-placed-path-to-cut (instructions (generated-inline-integer-body-path name args)))
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-inline-integer-body-path name args)) (all-cuts cuts)
                            (cuts (list (+ (proof-world-pc before) (if (generated-inline-integer-fast-p name args) 24 20))))))))
  :rule-classes nil)

(defun generated-number-guard-end (name args pc)
  (+ pc (* 4 (len (generated-integer-tag-path (not (eq name 'acl2::unary--)))))
     (if (generated-inline-integer-arguments-p name args) 0 20)))

(defun generated-inline-number-continuation (name pc)
  (+ pc (* 4 (len (generated-integer-tag-path (not (eq name 'acl2::unary--))))) 24))

(local
 (defthm generated-empty-number-body-keeps-world
   (equal (generated-path-after nil world) world)
   :hints (("Goal" :in-theory (enable generated-path-after)))))

(local
 (defthm generated-number-placement-appends-guard-and-body
   (implies (and (true-listp guard)
                 (generated-path-p guard (cons guard-end cuts) before)
                 (generated-path-p body cuts (generated-path-after guard before)))
            (generated-path-p (append guard body) cuts before))
   :hints (("Goal"
            :use (:instance generated-placed-path-allows-fewer-cuts (path guard) (all-cuts (cons guard-end cuts)))))
   :rule-classes nil))

(local
 (defthm generated-number-heap-equivalence-is-transitive
   (implies (and (generated-heap-world-equiv middle before) (generated-heap-world-equiv after middle))
            (generated-heap-world-equiv after before))
   :hints (("Goal" :in-theory (enable generated-heap-world-equiv)))
   :rule-classes nil))

(defthm generated-inline-number-selects-source-value-or-linked-call-site
  (let* ((pc (proof-world-pc before)) (binary (not (eq name 'acl2::unary--)))
         (guard (generated-integer-tag-path binary))
         (body (generated-inline-integer-body-path name args))
         (guarded (generated-path-after guard before)) (after (generated-path-after body guarded))
         (guard-end (generated-number-guard-end name args pc))
         (done (generated-inline-number-continuation name pc))
         (fast (generated-inline-integer-fast-p name args)) (end (- done (if fast 0 4))))
    (implies (and (generated-inline-number-name-p name) (proof-heap-p before objects packages)
                  (proof-reg-value-p 0 (car args) before objects packages)
                  (implies binary (proof-reg-value-p 1 (cadr args) before objects packages))
                  (< done (expt 2 64)) (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (member-equal end cuts) (generated-path-p guard (cons guard-end cuts) before)
                  (generated-path-p body cuts guarded))
             (and (proof-segment-p (+ (len guard) (len body)) cuts before :cut after)
                  (equal (proof-world-pc after) end)
                  (generated-ordinary-machine-p after) (not (proof-world-stop after))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-heap-world-equiv after before)
                  (if fast
                      (generated-nontail-value-result-p (generated-inline-integer-result name args) done
                                                       before after objects objects packages)
                    (and (proof-heap-p after objects packages)
                         (proof-reg-value-p 0 (car args) after objects packages)
                         (implies binary (proof-reg-value-p 1 (cadr args) after objects packages)))))))
  :hints (("Goal"
           :use (generated-inline-number-guard-keeps-source-operands
                 (:instance generated-inline-number-body-has-source-result-or-operands
                            (before (generated-path-after (generated-integer-tag-path (not (eq name 'acl2::unary--))) before)))
                 (:instance generated-number-placement-appends-guard-and-body
                            (guard (generated-integer-tag-path (not (eq name 'acl2::unary--))))
                            (guard-end (generated-number-guard-end name args (proof-world-pc before)))
                            (body (generated-inline-integer-body-path name args)))
                 (:instance generated-number-heap-equivalence-is-transitive
                            (middle (generated-path-after (generated-integer-tag-path (not (eq name 'acl2::unary--))) before))
                            (after (generated-path-after (generated-inline-integer-body-path name args)
                                     (generated-path-after (generated-integer-tag-path (not (eq name 'acl2::unary--))) before))))
                 (:instance generated-placed-path-to-cut
                            (instructions (append (generated-integer-tag-path (not (eq name 'acl2::unary--)))
                                                  (generated-inline-integer-body-path name args))))
                 (:instance generated-heap-equivalent-state-provides-value-result
                            (datum (generated-inline-integer-result name args))
                            (after (generated-path-after (generated-inline-integer-body-path name args)
                                     (generated-path-after (generated-integer-tag-path (not (eq name 'acl2::unary--))) before)))))
           :in-theory (enable generated-integer-tag-path)))
  :rule-classes nil)

(local
 (defthm generated-inline-number-runtime-arity
   (implies (generated-inline-number-name-p name)
            (and (proof-runtime-entry name)
                 (equal (cadr (proof-runtime-entry name)) (if (eq name 'acl2::unary--) 1 2))))
   :hints (("Goal" :in-theory (enable proof-runtime-entry proof-routine-spelling)))))

(local
 (defthm generated-unary-or-binary-arguments-from-source-registers
   (implies (and (true-listp args) (equal (len args) (if unary 1 2))
                 (proof-reg-value-p 0 (car args) world objects packages)
                 (implies (not unary) (proof-reg-value-p 1 (cadr args) world objects packages)))
            (proof-register-arguments-p args 0 world objects packages))
   :hints (("Goal" :in-theory (enable proof-register-arguments-p)))))

(defthm generated-inline-number-slow-path-returns-source-value
  (let* ((pc (proof-world-pc before)) (unary (eq name 'acl2::unary--))
         (guard (generated-integer-tag-path (not unary))) (body (generated-inline-integer-body-path name args))
         (guarded (generated-path-after guard before)) (ready (generated-path-after body guarded))
         (guard-end (generated-number-guard-end name args pc))
         (done (generated-inline-number-continuation name pc)) (slow (- done 4))
         (label (cddr (proof-runtime-entry name))) (target (proof-label-address label base labels))
         (entered (generated-link-to target ready)))
    (implies (and (generated-inline-number-name-p name) (not (generated-inline-integer-fast-p name args))
                  (true-listp args) (equal (len args) (if unary 1 2)) (proof-program-packages-p program packages)
                  (proof-heap-p before objects packages) (proof-reg-value-p 0 (car args) before objects packages)
                  (implies (not unary) (proof-reg-value-p 1 (cadr args) before objects packages))
                  (< done (expt 2 64)) (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p guard (list* guard-end slow cuts) before)
                  (generated-path-p body (cons slow cuts) guarded)
                  (unsigned-byte-p 64 target) (not (equal slow target)) (not (member-equal slow cuts))
                  (member-equal done cuts) (natp routine-steps)
                  (generated-linked-item-p (list :bl label) (list :branch (- target slow) t) slow base labels ready)
                  (proof-segment-p routine-steps cuts entered :cut after)
                  (proof-runtime-return-p name args program entered after objects new-objects packages))
             (and (proof-runtime-pre-p name args program labels base entered objects packages)
                  (proof-segment-p (+ (len guard) (len body) 1 (nfix routine-steps)) cuts before :cut after)
                  (generated-nontail-value-result-p (generated-inline-integer-result name args) done
                                                    before after objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-inline-number-selects-source-value-or-linked-call-site
                            (cuts (cons (- (generated-inline-number-continuation name (proof-world-pc before)) 4) cuts)))
                 (:instance generated-unary-or-binary-arguments-from-source-registers (unary (eq name 'acl2::unary--))
                            (world (generated-path-after (generated-inline-integer-body-path name args)
                                     (generated-path-after (generated-integer-tag-path (not (eq name 'acl2::unary--))) before))))
                 (:instance generated-heap-equivalent-state-provides-value-result (datum (car args))
                            (after (generated-path-after (generated-inline-integer-body-path name args)
                                     (generated-path-after (generated-integer-tag-path (not (eq name 'acl2::unary--))) before))))
                 (:instance generated-linked-runtime-call-and-return-compose (old-objects objects)
                            (before (generated-path-after (generated-inline-integer-body-path name args)
                                      (generated-path-after (generated-integer-tag-path (not (eq name 'acl2::unary--))) before))))
                 (:instance generated-nontail-segments-compose
                            (prefix-steps (+ (len (generated-integer-tag-path (not (eq name 'acl2::unary--))))
                                             (len (generated-inline-integer-body-path name args))))
                            (suffix-steps (+ 1 (nfix routine-steps))) (prefix-datum (car args))
                            (middle-pc (- (generated-inline-number-continuation name (proof-world-pc before)) 4))
                            (middle (generated-path-after (generated-inline-integer-body-path name args)
                                     (generated-path-after (generated-integer-tag-path (not (eq name 'acl2::unary--))) before)))
                            (continuation (generated-inline-number-continuation name (proof-world-pc before)))
                            (old-objects objects) (middle-objects objects) (datum (generated-inline-integer-result name args))))
           :in-theory (disable generated-inline-integer-body-path generated-inline-integer-arguments-p
                               generated-inline-integer-fast-p generated-inline-integer-result
                               generated-unary-or-binary-arguments-from-source-registers
                               generated-number-guard-end generated-inline-number-continuation)))
  :rule-classes nil)
