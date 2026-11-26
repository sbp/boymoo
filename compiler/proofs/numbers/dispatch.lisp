(in-package "BOYMOO-PROOFS")

(include-book "reciprocal")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-load boymoo-model::a64-pc boymoo-model::a64-nzcv
                     boymoo-model::a64-sp boymoo-model::a64-set-pc
                     boymoo-model::a64-set-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-memory proof-execute proof-instruction-effect
                     proof-reg proof-load-word proof-world-machine proof-world-stop
                     proof-instruction-at-p proof-decode-at proof-fetchable-p
                     proof-step proof-run proof-segment-p proof-view proof-value-p
                     proof-number-checked-block-p
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand acl2::binary-logior mod floor ash)))

; A test records a register number, a word to compare against, and a
; destination label. The last label in each row is the default destination.
(defconst *proof-number-dispatch-rows*
  '(("rt:n-add"
     ((1 1 "rt:num-type-return")
      (0 1 "rt:num-return-second")
      (3 5 "rt:c-add")
      (3 4 "rt:q-add"))
     "rt:z-add-op")
    ("rt:n-multiply"
     ((0 1 "rt:zero")
      (1 1 "rt:zero")
      (1 3 "rt:num-type-return")
      (0 3 "rt:num-return-second")
      (3 5 "rt:c-multiply")
      (3 4 "rt:q-multiply"))
     "rt:z-multiply-op")
    ("rt:n-negate"
     ((3 5 "rt:c-negate")
      (3 4 "rt:q-negate")
      (3 0 "rt:zero"))
     "rt:z-negate-op")
    ("rt:n-reciprocal"
     ((3 0 "rt:zero")
      (3 5 "rt:c-reciprocal"))
     "rt:q-reciprocal")
    ("rt:q-compare"
     ((3 4 "rt:q-compare-products"))
     "rt:z-compare")))

(defun proof-number-dispatch-test (test pc addresses)
  (let* ((reg (car test))
         (word (cadr test))
         (target (cdr (assoc-equal (caddr test) addresses))))
    (if (equal word 0)
        (list (list :branch-zero (- target pc) 64 reg nil))
      (list (list :arithmetic-imm 3 64 31 reg word)
            (list :branch-cond (- target (+ pc 4)) 0)))))

(defun proof-number-dispatch-code (tests default pc addresses)
  (if (endp tests)
      (list (list :branch (- (cdr (assoc-equal default addresses)) pc) nil))
    (let ((test (proof-number-dispatch-test (car tests) pc addresses)))
      (append test (proof-number-dispatch-code
                    (cdr tests) default (+ pc (* 4 (len test))) addresses)))))

(defun proof-number-dispatch-path (tests default pc addresses world)
  (if (endp tests)
      (proof-number-dispatch-code nil default pc addresses)
    (let ((test (proof-number-dispatch-test (car tests) pc addresses)))
      (append test
              (if (equal (proof-world-reg (caar tests) world) (cadar tests))
                  nil
                (proof-number-dispatch-path (cdr tests) default
                                            (+ pc (* 4 (len test))) addresses world))))))

(defun proof-number-dispatch-label (tests default world)
  (cond ((endp tests) default)
        ((equal (proof-world-reg (caar tests) world) (cadar tests)) (caddar tests))
        (t (proof-number-dispatch-label (cdr tests) default world))))

(defun proof-number-addresses-for-labels (names labels)
  (if (endp names)
      nil
    (acons (car names) (boymoo-compiler::a64-offset (car names) labels)
           (proof-number-addresses-for-labels (cdr names) labels))))

(defun proof-number-dispatch-labels-of-tests (tests)
  (if (endp tests)
      nil
    (cons (caddar tests) (proof-number-dispatch-labels-of-tests (cdr tests)))))

(defun proof-number-dispatch-decoding-p (rows labels)
  (if (endp rows)
      t
    (let* ((name (caar rows))
           (tests (cadar rows))
           (default (caddar rows))
           (addresses (proof-number-addresses-for-labels
                       (cons default (proof-number-dispatch-labels-of-tests tests)) labels))
           (pc (+ 12 (boymoo-compiler::a64-offset name labels)))
           (code (proof-number-dispatch-code tests default pc addresses))
           (items (take (len code)
                        (nthcdr 4 (proof-number-code-at-label
                                   name (boymoo-compiler::runtime-primitive-code))))))
      (and (equal (proof-number-decode-items items pc labels) code)
           (proof-number-dispatch-decoding-p (cdr rows) labels)))))

(defthm proof-number-dispatch-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (proof-number-dispatch-decoding-p *proof-number-dispatch-rows* labels))
  :rule-classes nil)

(defthm proof-number-dispatch-reaches-selected-label
  (let* ((row (assoc-equal name *proof-number-dispatch-rows*))
         (tests (cadr row))
         (default (caddr row))
         (pc (proof-world-pc world))
         (path (proof-number-dispatch-path tests default pc addresses world))
         (label (proof-number-dispatch-label tests default world))
         (target (cdr (assoc-equal label addresses)))
         (after (proof-number-execute-block path world))
         (machine (proof-world-machine world)))
    (implies (and row
                  (unsigned-byte-p 64 (+ pc (* 8 (len tests))))
                  (unsigned-byte-p 64 target)
                  (not (eq (car machine) :svc))
                  (proof-number-checked-block-p path (list target) world))
             (and (proof-segment-p (len path) (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg register after) (proof-world-reg register world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-segment
                            (instructions
                             (proof-number-dispatch-path
                              (cadr (assoc-equal name *proof-number-dispatch-rows*))
                              (caddr (assoc-equal name *proof-number-dispatch-rows*))
                              (proof-world-pc world) addresses world))
                            (cuts (list (cdr (assoc-equal
                                             (proof-number-dispatch-label
                                              (cadr (assoc-equal name *proof-number-dispatch-rows*))
                                              (caddr (assoc-equal name *proof-number-dispatch-rows*))
                                              world)
                                             addresses))))))
           :in-theory (disable proof-number-checked-block-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-value-completions
  (let ((left (fix a))
        (right (fix b)))
    (and (equal (proof-runtime-value 'acl2::binary-+ (list a b) program)
                (boymoo-model::core-value (+ left right)))
         (equal (proof-runtime-value 'acl2::binary-* (list a b) program)
                (boymoo-model::core-value (* left right)))
         (equal (proof-runtime-value 'acl2::unary-- (list a) program)
                (boymoo-model::core-value (- left)))
         (equal (proof-runtime-value 'acl2::unary-/ (list a) program)
                (boymoo-model::core-value (/ left)))
         (equal (proof-runtime-value '< (list a b) program)
                (boymoo-model::core-value (< left right)))
         (equal (proof-runtime-value 'complex (list a b) program)
                (boymoo-model::core-value (complex (rfix a) (rfix b))))))
  :hints (("Goal" :in-theory (enable boymoo-model::core-primitive)))
  :rule-classes nil)

(defund proof-number-max-class (a b)
  (max (proof-number-datum-class a) (proof-number-datum-class b)))

; These are the outputs of the two classifications in rt:n-types.
(defund proof-number-binary-types-p (a b world objects packages)
  (and (proof-reg-value-p 0 (fix a) world objects packages)
       (proof-reg-value-p 1 (fix b) world objects packages)
       (equal (proof-world-reg 3 world) (proof-number-max-class a b))))

(defun proof-number-selected-label (name world)
  (let ((row (assoc-equal name *proof-number-dispatch-rows*)))
    (proof-number-dispatch-label (cadr row) (caddr row) world)))

(local
 (in-theory (enable proof-number-datum-class proof-number-max-class
                   proof-number-binary-types-p)))

(defthm proof-number-add-dispatch-by-value
  (implies (proof-number-binary-types-p a b world objects packages)
           (equal (proof-number-selected-label "rt:n-add" world)
                  (cond ((equal (fix b) 0) "rt:num-type-return")
                        ((equal (fix a) 0) "rt:num-return-second")
                        ((or (complex-rationalp a) (complex-rationalp b)) "rt:c-add")
                        ((or (and (rationalp a) (not (integerp a)))
                             (and (rationalp b) (not (integerp b))))
                         "rt:q-add")
                        (t "rt:z-add-op"))))
  :hints (("Goal"
           :use ((:instance proof-number-tagged-zero-and-one (value (fix a))
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-tagged-zero-and-one (value (fix b))
                            (word (proof-world-reg 1 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world))))))
  :rule-classes nil)

(defthm proof-number-multiply-dispatch-by-value
  (implies (proof-number-binary-types-p a b world objects packages)
           (equal (proof-number-selected-label "rt:n-multiply" world)
                  (cond ((or (equal (fix a) 0) (equal (fix b) 0)) "rt:zero")
                        ((equal (fix b) 1) "rt:num-type-return")
                        ((equal (fix a) 1) "rt:num-return-second")
                        ((or (complex-rationalp a) (complex-rationalp b)) "rt:c-multiply")
                        ((or (and (rationalp a) (not (integerp a)))
                             (and (rationalp b) (not (integerp b))))
                         "rt:q-multiply")
                        (t "rt:z-multiply-op"))))
  :hints (("Goal"
           :use ((:instance proof-number-tagged-zero-and-one (value (fix a))
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-tagged-zero-and-one (value (fix b))
                            (word (proof-world-reg 1 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world))))))
  :rule-classes nil)

(defthm proof-number-negation-dispatch-by-value
  (implies (equal (proof-world-reg 3 world) (proof-number-datum-class a))
           (equal (proof-number-selected-label "rt:n-negate" world)
                  (cond ((complex-rationalp a) "rt:c-negate")
                        ((integerp a) "rt:z-negate-op")
                        ((rationalp a) "rt:q-negate")
                        (t "rt:zero"))))
  :rule-classes nil)

(defthm proof-number-reciprocal-dispatch-by-value
  (implies (equal (proof-world-reg 3 world) (proof-number-datum-class a))
           (equal (proof-number-selected-label "rt:n-reciprocal" world)
                  (cond ((complex-rationalp a) "rt:c-reciprocal")
                        ((rationalp a) "rt:q-reciprocal")
                        (t "rt:zero"))))
  :rule-classes nil)

(defthm proof-number-rational-comparison-dispatch-by-value
  (implies (and (not (complex-rationalp a)) (not (complex-rationalp b))
                (proof-number-binary-types-p a b world objects packages))
           (equal (proof-number-selected-label "rt:q-compare" world)
                  (if (and (integerp (fix a)) (integerp (fix b)))
                      "rt:z-compare"
                    "rt:q-compare-products")))
  :rule-classes nil)
