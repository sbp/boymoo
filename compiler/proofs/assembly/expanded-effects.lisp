(in-package "BOYMOO-PROOFS")

(include-book "effects")
(include-book "expansions")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable ash floor mod logbitp
                           acl2::binary-logand acl2::binary-logior acl2::binary-logxor
                           assembly-high assembly-low assembly-power-of-two
                           boymoo-model::a64-pc boymoo-model::a64-nzcv
                           boymoo-model::a64-unsigned boymoo-model::a64-set-pc
                           boymoo-model::a64-set-nzcv)))

(local
 (defun assembly-update-induct (i j record)
   (declare (xargs :measure (nfix i)))
   (if (or (zp i) (zp j))
       record
     (assembly-update-induct (1- i) (1- j) (cdr record)))))

(local
 (defthm assembly-distinct-updates-commute
   (implies (and (natp i) (natp j) (not (equal i j)))
            (equal (update-nth i a (update-nth j b record))
                   (update-nth j b (update-nth i a record))))
   :hints (("Goal" :induct (assembly-update-induct i j record)
                   :expand ((:free (record) (update-nth i a record))
                            (:free (record) (update-nth j b record)))))
   :rule-classes nil))

(local
 (defthm assembly-set-pc-of-set-pc
   (equal (boymoo-model::a64-set-pc first (boymoo-model::a64-set-pc second machine))
          (boymoo-model::a64-set-pc first machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm assembly-set-nzcv-of-set-nzcv
   (equal (boymoo-model::a64-set-nzcv first (boymoo-model::a64-set-nzcv second machine))
          (boymoo-model::a64-set-nzcv first machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-nzcv)))))

(local
 (defthm assembly-set-pc-commutes-with-set-nzcv
   (equal (boymoo-model::a64-set-pc address (boymoo-model::a64-set-nzcv flags machine))
          (boymoo-model::a64-set-nzcv flags (boymoo-model::a64-set-pc address machine)))
   :hints (("Goal"
            :use ((:instance assembly-distinct-updates-commute
                             (i 2) (j 3) (record machine)
                             (a (boymoo-model::a64-unsigned 64 address))
                             (b (boymoo-model::a64-unsigned 4 flags))))
            :in-theory (enable boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv)))))

(local
 (defthm assembly-machine-pc-is-a-natural
   (natp (boymoo-model::a64-pc machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-pc)))
   :rule-classes :type-prescription))

(local
 (defthm assembly-pc-after-set-pc
   (equal (boymoo-model::a64-pc (boymoo-model::a64-set-pc address machine))
          (assembly-low 64 address))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-pc boymoo-model::a64-set-pc)))))

(local
 (defthm assembly-pc-after-set-nzcv
   (equal (boymoo-model::a64-pc (boymoo-model::a64-set-nzcv flags machine))
          (boymoo-model::a64-pc machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-pc boymoo-model::a64-set-nzcv)))))

(local
 (defthm assembly-nzcv-after-set-nzcv
   (equal (boymoo-model::a64-nzcv (boymoo-model::a64-set-nzcv flags machine))
          (assembly-low 4 flags))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-nzcv boymoo-model::a64-set-nzcv)))))

(defun assembly-execute-two (instructions machine)
  (proof-execute (cadr instructions) (proof-execute (car instructions) machine)))

(local
 (defthm assembly-zero-test-effect
   (equal (proof-execute '(:logical-reg 3 64 31 31 31 0 0 nil) machine)
          (boymoo-model::a64-set-nzcv
           4 (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))))

(defthm assembly-zero-source-discard-effect
  (implies (< (+ 4 (boymoo-model::a64-pc machine)) (expt 2 64))
           (equal (assembly-execute-two
                   (assembly-zero-source-instructions subtract 31 immediate) machine)
                  (boymoo-model::a64-set-nzcv
                   (assembly-zero-source-nzcv subtract immediate)
                   (boymoo-model::a64-set-pc (+ 8 (boymoo-model::a64-pc machine)) machine)))))

(defthm assembly-far-address-discard-effect
  (implies (< (+ 4 (boymoo-model::a64-pc machine)) (expt 2 64))
           (equal (assembly-execute-two
                   (assembly-far-address-instructions 31 target offset) machine)
                  (boymoo-model::a64-set-pc (+ 8 (boymoo-model::a64-pc machine)) machine))))

(local
 (defthm assembly-write-reg-commutes-with-set-pc
   (equal (boymoo-model::a64-write-reg register width use-sp value
                                       (boymoo-model::a64-set-pc address machine))
          (boymoo-model::a64-set-pc
           address (boymoo-model::a64-write-reg register width use-sp value machine)))
   :hints (("Goal"
            :use ((:instance assembly-distinct-updates-commute
                             (i 0) (j 2) (record machine)
                             (a (put-assoc-equal register
                                               (boymoo-model::a64-unsigned width value)
                                               (boymoo-model::a64-registers machine)))
                             (b (boymoo-model::a64-unsigned 64 address)))
                  (:instance assembly-distinct-updates-commute
                             (i 1) (j 2) (record machine)
                             (a (boymoo-model::a64-unsigned
                                 64 (boymoo-model::a64-unsigned width value)))
                             (b (boymoo-model::a64-unsigned 64 address))))
            :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm assembly-assoc-after-write
   (equal (assoc-equal register (put-assoc-equal register value registers))
          (cons register value))))

(local
 (defthm assembly-write-same-assoc-twice
   (equal (put-assoc-equal register first (put-assoc-equal register second registers))
          (put-assoc-equal register first registers))))

(local
 (defthm assembly-write-same-register-twice
   (equal (boymoo-model::a64-write-reg
           register width use-sp first
           (boymoo-model::a64-write-reg register other-width use-sp second machine))
          (boymoo-model::a64-write-reg register width use-sp first machine))))

(local
 (defthm assembly-read-written-register
   (implies (and (natp register) (< register 31))
            (equal (boymoo-model::a64-read-reg
                    register 64 use-sp
                    (boymoo-model::a64-write-reg register 64 store-sp value machine))
                   (assembly-low 64 value)))))

(local
 (defthm assembly-read-after-set-pc
   (equal (boymoo-model::a64-read-reg
           register width use-sp (boymoo-model::a64-set-pc address machine))
          (boymoo-model::a64-read-reg register width use-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc)))))

(local
 (defthm assembly-writing-low-64
   (equal (boymoo-model::a64-write-reg register 64 use-sp (assembly-low 64 value) machine)
          (boymoo-model::a64-write-reg register 64 use-sp value machine))))

(defthm assembly-add-immediate-effect
  (equal (proof-execute (list :arithmetic-imm 0 64 rd rn immediate) machine)
         (boymoo-model::a64-write-reg
          rd 64 t (+ (boymoo-model::a64-read-reg rn 64 t machine) immediate)
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg))))

(local
 (defthm assembly-execute-page-address
   (implies (integerp pages)
            (equal (proof-execute (list :address rd pages t) machine)
                   (boymoo-model::a64-write-reg
                    rd 64 nil
                    (+ (* 4096 (assembly-high 12 (boymoo-model::a64-pc machine))) (* 4096 pages))
                    (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))))))

(local
 (defthm assembly-target-page-address
   (implies (and (natp base) (natp offset) (natp target)
                 (equal (mod base 4096) 0))
            (equal (+ (* 4096 (assembly-high 12 (+ base offset)))
                      (* 4096 (- (assembly-high 12 target) (assembly-high 12 offset))))
                   (+ base (* 4096 (assembly-high 12 target)))))
   :hints (("Goal"
            :use ((:instance assembly-page-of-aligned-base-plus-offset (offset offset)))
            :in-theory (e/d (assembly-high mod)
                            (assembly-page-of-aligned-base-plus-offset))))))

(local
 (defthm assembly-low-word-of-addition
   (implies (and (integerp value) (integerp offset))
            (equal (assembly-low 64 (+ offset (assembly-low 64 value)))
                   (assembly-low 64 (+ offset value))))
   :hints (("Goal"
            :use ((:instance assembly-floor-bounds
                             (x (+ offset value)) (d (expt 2 64)))
                  (:instance assembly-floor-unique
                             (x (+ offset (assembly-low 64 value))) (d (expt 2 64))
                             (q (- (floor (+ offset value) (expt 2 64))
                                   (floor value (expt 2 64))))))
            :in-theory (enable assembly-low mod)))))

(local
 (defthm assembly-addition-to-masked-word
   (implies (and (integerp value) (integerp offset))
            (equal (boymoo-model::a64-write-reg
                    rd 64 use-sp (+ offset (assembly-low 64 value)) machine)
                   (boymoo-model::a64-write-reg rd 64 use-sp (+ offset value) machine)))))

(local
 (defthm assembly-ignore-register-thirty-one
   (equal (boymoo-model::a64-write-reg 31 width nil value machine) machine)))

(local
 (defthm assembly-register-sp-selection-is-irrelevant
   (implies (and (natp register) (< register 31))
            (equal (boymoo-model::a64-write-reg register width t value machine)
                   (boymoo-model::a64-write-reg register width nil value machine)))))

(local
 (defthm assembly-move-zero-to-zero
   (equal (proof-execute '(:logical-reg 1 64 31 31 31 0 0 nil) machine)
          (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))))

(local
 (defthm assembly-join-page-and-offset
   (implies (integerp target)
            (equal (+ (assembly-low 12 target) (* 4096 (assembly-high 12 target))) target))
   :hints (("Goal"
            :use ((:instance assembly-cat-of-low-and-high (width 12) (x target)))
            :in-theory (e/d (assembly-cat) (assembly-cat-of-low-and-high))))))

(local
 (defthm assembly-target-address-from-page-and-offset
   (implies (and (integerp base) (integerp target))
            (equal (+ base (assembly-low 12 target) (* 4096 (assembly-high 12 target)))
                   (+ base target)))
   :hints (("Goal" :use (assembly-join-page-and-offset)
                   :in-theory (disable assembly-join-page-and-offset)))
   :rule-classes nil))

(defthm assembly-far-address-effect
  (implies (and (natp base) (natp offset) (natp target)
                (unsigned-byte-p 5 rd)
                (equal (mod base 4096) 0)
                (equal (boymoo-model::a64-pc machine) (+ base offset))
                (< (+ base offset 4) (expt 2 64)))
           (equal (assembly-execute-two
                   (assembly-far-address-instructions rd target offset) machine)
                  (boymoo-model::a64-write-reg
                   rd 64 nil (+ base target)
                   (boymoo-model::a64-set-pc (+ base offset 8) machine))))
  :hints (("Goal"
           :use (assembly-target-page-address assembly-target-address-from-page-and-offset)
           :in-theory (disable boymoo-model::a64-write-reg boymoo-model::a64-read-reg
                               proof-execute assembly-far-address-discard-effect
                               assembly-target-page-address))))

(local
 (defun assembly-unsigned-bits-induct (value)
   (declare (xargs :measure (nfix value)))
   (if (zp value)
       value
     (assembly-unsigned-bits-induct (assembly-high 1 value)))))

(local
 (defthm assembly-and-with-its-own-bits
   (implies (natp value) (equal (logand value value) value))
   :hints (("Goal" :induct (assembly-unsigned-bits-induct value))
           ("Subgoal *1/2"
            :use ((:instance assembly-logand-by-bits (x value) (y value))
                  (:instance assembly-cat-of-low-and-high (width 1) (x value))
                  (:instance assembly-low-one-is-a-bit (x value)))
            :in-theory (e/d (assembly-cat) (assembly-cat-of-low-and-high))))))

(local
 (defthm assembly-movz-into-register
   (implies (integerp immediate)
            (equal (proof-execute (list :move-wide 2 64 rd immediate 0) machine)
                   (boymoo-model::a64-write-reg
                    rd 64 nil immediate
                    (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-write-reg)))))

(local
 (defthm assembly-tst-small-result-effect
   (implies (and (unsigned-byte-p 12 immediate)
                 (equal (boymoo-model::a64-read-reg rd 64 nil machine) immediate))
            (equal (proof-execute (list :logical-reg 3 64 31 rd rd 0 0 nil) machine)
                   (boymoo-model::a64-set-nzcv
                    (assembly-zero-source-nzcv nil immediate)
                    (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-read-reg
                                       boymoo-model::a64-write-reg)))))

(defthm assembly-zero-source-add-effect
  (implies (and (unsigned-byte-p 5 rd) (unsigned-byte-p 12 immediate)
                (< (+ 4 (boymoo-model::a64-pc machine)) (expt 2 64)))
           (equal (assembly-execute-two
                   (assembly-zero-source-instructions nil rd immediate) machine)
                  (boymoo-model::a64-set-nzcv
                   (assembly-zero-source-nzcv nil immediate)
                   (boymoo-model::a64-write-reg
                    rd 64 nil immediate
                    (boymoo-model::a64-set-pc (+ 8 (boymoo-model::a64-pc machine)) machine)))))
  :hints (("Goal" :use ((:instance assembly-zero-source-discard-effect (subtract nil))
                        (:instance assembly-tst-small-result-effect
                                   (machine (boymoo-model::a64-set-pc
                                             (+ 4 (boymoo-model::a64-pc machine))
                                             (boymoo-model::a64-write-reg rd 64 nil immediate machine)))))
                  :in-theory (disable proof-execute assembly-zero-source-discard-effect
                                      assembly-tst-small-result-effect
                                      boymoo-model::a64-read-reg boymoo-model::a64-write-reg))))

(local
 (defthm assembly-subs-known-right-register
   (implies (and (unsigned-byte-p 12 immediate)
                 (equal (boymoo-model::a64-read-reg rd 64 nil machine) immediate))
            (equal (proof-execute (list :arithmetic-reg 3 64 rd 31 rd 0 0) machine)
                   (boymoo-model::a64-exec-arithmetic
                    3 64 rd 31 immediate nil
                    (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-exec-arithmetic
                                       boymoo-model::a64-read-reg)))))

(local
 (defthm assembly-subs-overwrites-source-temporary
   (equal (boymoo-model::a64-exec-arithmetic
           3 64 rd 31 immediate nil
           (boymoo-model::a64-write-reg rd 64 nil temporary machine))
          (boymoo-model::a64-exec-arithmetic 3 64 rd 31 immediate nil machine))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-write-reg
                                       boymoo-model::a64-signed)))))

(local
 (defthm assembly-subs-overwrites-source-temporary-after-set-pc
   (equal (boymoo-model::a64-exec-arithmetic
           3 64 rd 31 immediate nil
           (boymoo-model::a64-set-pc
            address (boymoo-model::a64-write-reg rd 64 nil temporary machine)))
          (boymoo-model::a64-exec-arithmetic
           3 64 rd 31 immediate nil (boymoo-model::a64-set-pc address machine)))
   :hints (("Goal"
            :use ((:instance assembly-subs-overwrites-source-temporary
                             (machine (boymoo-model::a64-set-pc address machine))))
            :in-theory (disable boymoo-model::a64-exec-arithmetic boymoo-model::a64-write-reg
                                assembly-subs-overwrites-source-temporary)))))

(defthm assembly-zero-source-subtract-effect
  (implies (and (natp rd) (< rd 31) (unsigned-byte-p 12 immediate)
                (< (+ 4 (boymoo-model::a64-pc machine)) (expt 2 64)))
           (equal (assembly-execute-two
                   (assembly-zero-source-instructions t rd immediate) machine)
                  (boymoo-model::a64-exec-arithmetic
                   3 64 rd 31 immediate nil
                   (boymoo-model::a64-set-pc (+ 8 (boymoo-model::a64-pc machine)) machine))))
  :hints (("Goal"
           :use ((:instance assembly-subs-known-right-register
                            (machine (boymoo-model::a64-set-pc
                                      (+ 4 (boymoo-model::a64-pc machine))
                                      (boymoo-model::a64-write-reg rd 64 nil immediate machine)))))
           :in-theory (disable proof-execute boymoo-model::a64-exec-arithmetic
                               assembly-subs-known-right-register
                               boymoo-model::a64-read-reg boymoo-model::a64-write-reg))))

(defthm assembly-cset-effect
  (implies (and (assembly-condition-p condition) (not (eq condition :al)))
           (let ((code (boymoo-compiler::a64-condition condition)))
             (equal (proof-execute
                     (list :select 64 rd 31 31 (logxor code 1) t) machine)
                    (boymoo-model::a64-write-reg
                     rd 64 nil
                     (if (boymoo-model::a64-condition
                          code (boymoo-model::a64-nzcv machine))
                         1
                       0)
                     (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-write-reg))))
