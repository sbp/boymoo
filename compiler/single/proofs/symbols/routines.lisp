(in-package "BOYMOO-PROOFS")

(include-book "bits")
(include-book "execution")
(include-book "hash")
(include-book "layout")

(logic)
(set-verify-guards-eagerness 0)

(defconst *symbols-symbol-tag-miss*
  (symbols-code-path "rt:symbol-view" '(0 4 8 32 36)))

(defconst *symbols-symbol-header-miss*
  (symbols-code-path "rt:symbol-view" '(0 4 8 12 16 20 24 28 32 36)))

(defconst *symbols-symbol-hit*
  (symbols-code-path "rt:symbol-view" '(0 4 8 12 16 20 24 28 36)))

(defun symbols-box-address (word base)
  (boymoo-model::a64-unsigned 64 (+ base (boymoo-model::a64-unsigned 64 (- word 2)))))

(defun symbols-symbol-header (world)
  (symbols-box-address (proof-world-reg 0 world) (proof-heap-base world)))

(defun symbols-symbol-tag-p (world)
  (equal (boymoo-model::a64-unsigned 3 (proof-world-reg 0 world)) 2))

(defun symbols-symbol-header-p (world)
  (equal (boymoo-model::a64-unsigned
          8 (boymoo-model::a64-load
             1 (symbols-symbol-header world) (proof-world-machine world)))
         2))

(defun symbols-symbol-view-path (world)
  (cond ((not (symbols-symbol-tag-p world)) *symbols-symbol-tag-miss*)
        ((symbols-symbol-header-p world) *symbols-symbol-hit*)
        (t *symbols-symbol-header-miss*)))

(defun symbols-symbol-view-result (world)
  (if (and (symbols-symbol-tag-p world) (symbols-symbol-header-p world))
      (symbols-symbol-header world)
    0))

(defun symbols-machine-memory (world)
  (boymoo-model::a64-memory (proof-world-machine world)))

(defun symbols-no-memory-or-kernel-change-p (before after)
  (and (equal (symbols-machine-memory before) (symbols-machine-memory after))
       (equal (proof-world-regions before) (proof-world-regions after))
       (equal (proof-world-replies before) (proof-world-replies after))
       (proof-streams-preserved-p before after)))

(defun symbols-saved-link-world (before)
  (let* ((machine (proof-world-machine before))
         (sp (boymoo-model::a64-sp machine))
         (saved (boymoo-model::a64-store 8 (- sp 16) (proof-world-reg 29 before) machine))
         (saved (boymoo-model::a64-store 8 (- sp 8) (proof-world-reg 30 before) saved)))
    (update-nth 0 saved before)))

; The complete runtime code must fit in the address space. The
; instruction placement premise also requires executable coverage.
(defconst *symbols-runtime-size*
  (mv-let (end labels reversed)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore labels reversed))
    end))

(defun symbols-runtime-base-p (base)
  (and (natp base) (< (+ base *symbols-runtime-size*) (expt 2 64))))

(local
 (in-theory (set-difference-theories (current-theory :here)
                                     (theory 'symbols-state-operations))))

(local
 (in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-signed
                     boymoo-model::a64-ror acl2::binary-logand acl2::binary-logxor
                     mod floor ash logbitp
                     symbols-symbol-tag-p symbols-symbol-header-p
                     proof-run proof-runtime-entry symbols-runtime-offset)))

(local
 (defthm symbols-register-value-is-natural
   (natp (boymoo-model::a64-read-reg register width sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-register-value-bound
   (< (boymoo-model::a64-read-reg register width sp machine)
      (expt 2 (nfix width)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg)))
   :rule-classes :linear))

(local
 (defthm symbols-pc-is-natural
   (natp (boymoo-model::a64-pc machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-pc)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-instruction-register-without-sp
   (implies (and (natp register) (< register 31))
            (equal (boymoo-model::a64-read-reg register width t machine)
                   (boymoo-model::a64-read-reg register width nil machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg)))))

(local
 (defthm symbols-64-bits-of-byte
   (equal (boymoo-model::a64-unsigned 64 (boymoo-model::a64-unsigned 8 x))
          (boymoo-model::a64-unsigned 8 x))))

(local
 (defthm symbols-64-bits-of-low-tag
   (equal (boymoo-model::a64-unsigned 64 (boymoo-model::a64-unsigned 3 x))
          (boymoo-model::a64-unsigned 3 x))))

(local
 (defthm symbols-register-value-fits-its-width
   (equal (boymoo-model::a64-unsigned
           width (boymoo-model::a64-read-reg register width sp machine))
          (boymoo-model::a64-read-reg register width sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg)))))

(local
 (defthm symbols-logand-seven
   (implies (integerp x)
            (equal (logand x 7) (boymoo-model::a64-unsigned 3 x)))
   :hints (("Goal"
            :use ((:instance symbols-logand-low-mask (width 3))
                  (:instance symbols-unsigned-as-mod (width 3)))))))

(local
 (defthm symbols-logior-zero
   (equal (logior 0 x) (ifix x))
   :hints (("Goal" :in-theory (enable acl2::binary-logior acl2::binary-logand lognot)))))

(local
 (defthm symbols-ash-zero
   (equal (ash x 0) (ifix x))
   :hints (("Goal"
            :use ((:instance symbols-floor-of-decomposition
                             (q (ifix x)) (r 0) (divisor 1)))
            :in-theory (enable ash)))))

(local
 (defthm symbols-unsigned-word-plus-modulus
   (implies (integerp x)
            (equal (boymoo-model::a64-unsigned 64 (+ x (expt 2 64)))
                   (boymoo-model::a64-unsigned 64 x)))
   :hints (("Goal"
            :use ((:instance symbols-mod-translation (divisor (expt 2 64)) (q 1)))
            :in-theory (enable symbols-unsigned-as-mod)))))

(local
 (defthm symbols-word-difference-zero
   (implies (and (natp x) (< x (expt 2 64)) (natp y) (< y (expt 2 64)))
            (equal (equal (boymoo-model::a64-unsigned 64 (- x y)) 0)
                   (equal x y)))
   :hints (("Goal"
            :cases ((< x y))
            :use ((:instance symbols-unsigned-word-plus-modulus (x (- x y)))
                  (:instance symbols-unsigned-in-range (width 64) (x (- x y)))
                  (:instance symbols-unsigned-in-range (width 64)
                             (x (+ (expt 2 64) (- x y)))))
            :in-theory (disable symbols-unsigned-in-range
                                symbols-unsigned-word-plus-modulus)))))

(local
 (defthm symbols-conditions-from-result-flags
   (and (equal (boymoo-model::a64-condition
                0 (boymoo-model::a64-result-flags width result carry overflow))
               (equal result 0))
        (equal (boymoo-model::a64-condition
                1 (boymoo-model::a64-result-flags width result carry overflow))
               (not (equal result 0)))
        (iff (boymoo-model::a64-condition
              2 (boymoo-model::a64-result-flags width result carry overflow))
             carry)
        (equal (boymoo-model::a64-condition
                3 (boymoo-model::a64-result-flags width result carry overflow))
               (not carry)))
   :hints (("Goal"
            :in-theory (enable boymoo-model::a64-condition
                               boymoo-model::a64-result-flags)))))

(local
 (defthm symbols-result-flags-fit-nzcv
   (equal (boymoo-model::a64-unsigned
           4 (boymoo-model::a64-result-flags width result carry overflow))
          (boymoo-model::a64-result-flags width result carry overflow))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-result-flags)))))

(local
 (defthm symbols-subtract-two-as-difference
   (implies (integerp x)
            (equal (boymoo-model::a64-unsigned 64 (+ #xfffffffffffffffe x))
                   (boymoo-model::a64-unsigned 64 (- x 2))))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-word-plus-modulus (x (- x 2))))
            :in-theory (disable symbols-unsigned-word-plus-modulus)))))

(local
 (defun symbols-next-pc (world)
   (boymoo-model::a64-set-pc (+ 4 (proof-world-pc world))
                            (proof-world-machine world))))

(local
 (defthm symbols-effect-and-immediate
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect (list :logical-imm 0 64 rd rn mask) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 t (logand (proof-world-reg rn world) mask)
                                  (symbols-next-pc world))
                               world)))))

(local
 (defun symbols-compare-flags (value operand)
   (let* ((sum (+ value 1 (logxor operand (boymoo-model::a64-ones 64))))
          (result (boymoo-model::a64-unsigned 64 sum)))
     (boymoo-model::a64-result-flags
      64 result (logbitp 64 sum)
      (not (equal (- (boymoo-model::a64-signed 64 value)
                     (boymoo-model::a64-signed 64 operand))
                  (boymoo-model::a64-signed 64 result)))))))

(local
 (defthm symbols-effect-compare-immediate
   (implies (and (natp rn) (< rn 31)
                 (not (eq (car (proof-world-machine world)) :svc)))
            (equal (proof-instruction-effect (list :arithmetic-imm 3 64 31 rn operand) world)
                   (update-nth 0 (boymoo-model::a64-set-nzcv
                                  (symbols-compare-flags (proof-world-reg rn world) operand)
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-result-flags)))))

(local
 (defthm symbols-carry-on-unsigned-subtraction
   (implies (and (natp value) (< value (expt 2 64))
                 (natp operand) (< operand (expt 2 64)))
            (equal (logbitp 64 (+ #x10000000000000000 (- operand) value))
                   (<= operand value)))
   :hints (("Goal" :cases ((< value operand))
                   :use ((:instance symbols-floor-of-decomposition
                                    (q 0) (r (+ (expt 2 64) value (- operand)))
                                    (divisor (expt 2 64)))
                         (:instance symbols-floor-of-decomposition
                                    (q 1) (r (- value operand)) (divisor (expt 2 64))))
                   :in-theory (e/d (logbitp) (symbols-floor-of-decomposition))))))

(local
 (defthm symbols-xor-with-word-mask
   (implies (and (natp operand) (< operand (expt 2 64)))
            (equal (logxor operand #xffffffffffffffff)
                   (- #xffffffffffffffff operand)))
   :hints (("Goal"
            :use ((:instance symbols-xor-with-width-mask (width 64) (word operand)))
            :in-theory (disable symbols-xor-with-width-mask)))))

(local
 (defthm symbols-effects-of-word-comparison
   (implies (and (natp value) (< value (expt 2 64))
                 (natp operand) (< operand (expt 2 64)))
            (and (equal (boymoo-model::a64-condition 0 (symbols-compare-flags value operand))
                        (equal value operand))
                 (equal (boymoo-model::a64-condition 1 (symbols-compare-flags value operand))
                        (not (equal value operand)))
                 (equal (boymoo-model::a64-condition 2 (symbols-compare-flags value operand))
                        (<= operand value))
                 (equal (boymoo-model::a64-condition 3 (symbols-compare-flags value operand))
                        (< value operand))))
   :hints (("Goal"
            :use ((:instance symbols-word-difference-zero (x value) (y operand))
                  (:instance symbols-unsigned-word-plus-modulus (x (- value operand))))
            :in-theory (disable boymoo-model::a64-condition
                                boymoo-model::a64-result-flags
                                symbols-xor-with-width-mask
                                symbols-word-difference-zero
                                symbols-unsigned-word-plus-modulus)))))

(local
 (defthm symbols-compare-flags-fit-nzcv
   (equal (boymoo-model::a64-unsigned 4 (symbols-compare-flags value operand))
          (symbols-compare-flags value operand))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-result-flags)))))

(local
 (defthm symbols-effect-subtract-two
   (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31))
            (equal (proof-instruction-effect (list :arithmetic-imm 2 64 rd rn 2) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 t (boymoo-model::a64-unsigned
                                           64 (- (proof-world-reg rn world) 2))
                                  (symbols-next-pc world))
                               world)))))

(local
 (defthm symbols-effect-add-shifted-register
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect
                    (list :arithmetic-reg 0 64 rd rn rm 0 shift) world)
                   (update-nth
                    0 (boymoo-model::a64-write-reg
                       rd 64 nil
                       (boymoo-model::a64-unsigned
                        64 (+ (proof-world-reg rn world)
                              (boymoo-model::a64-unsigned
                               64 (ash (proof-world-reg rm world) shift))))
                       (symbols-next-pc world))
                    world)))))

(local
 (defthm symbols-effect-offset-load
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect
                    (list :single 1 size rn rd :offset offset) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd (* 8 size) nil
                                  (boymoo-model::a64-load
                                   size (+ (boymoo-model::a64-read-reg
                                            rn 64 t (proof-world-machine world))
                                           offset)
                                   (proof-world-machine world))
                                  (symbols-next-pc world))
                               world)))))

(local
 (defthm symbols-effect-move-zero
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect (list :move-wide 2 64 rd 0 0) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil 0 (symbols-next-pc world))
                               world)))))

(local
 (defthm symbols-effect-branch-cond
   (implies (not (eq (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect (list :branch-cond delta condition) world)
                   (update-nth
                    0 (if (boymoo-model::a64-condition
                           condition (boymoo-model::a64-nzcv (proof-world-machine world)))
                          (boymoo-model::a64-set-pc (+ (proof-world-pc world) delta)
                                                   (symbols-next-pc world))
                        (symbols-next-pc world))
                    world)))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition)))))

(local
 (defthm symbols-effect-branch-register
   (implies (not (eq (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect (list :branch-reg register nil) world)
                   (update-nth 0 (boymoo-model::a64-set-pc
                                  (proof-world-reg register world)
                                  (symbols-next-pc world))
                               world)))))

(local
 (in-theory (disable proof-instruction-effect symbols-compare-flags)))

(defthm symbols-replay-symbol-view
  (let* ((path (symbols-symbol-view-path before))
         (after (symbols-replay path before)))
    (implies (and (symbols-runtime-base-p code-base)
                  (equal (proof-world-pc before)
                         (symbols-runtime-address "rt:symbol-view" code-base))
                  (not (eq (car (proof-world-machine before)) :svc))
                  (not (proof-world-stop before)))
             (and (symbols-path-control-p path code-base before)
                  (proof-frame-return-p '(1 2) t before after)
                  (not (eq (car (proof-world-machine after)) :svc))
                  (equal (proof-world-reg 1 after) (symbols-symbol-view-result before))
                  (symbols-no-memory-or-kernel-change-p before after))))
  :hints (("Goal"
           :in-theory (e/d (symbols-symbol-tag-p symbols-symbol-header-p)
                           (boymoo-model::a64-condition
                            boymoo-model::a64-result-flags))))
  :rule-classes nil)

(defthm symbols-run-symbol-view
  (let* ((path (symbols-symbol-view-path before))
         (link (proof-world-reg 30 before))
         (after (proof-advance (len path) before)))
    (implies (and (symbols-runtime-base-p code-base)
                  (equal (proof-world-pc before)
                         (symbols-runtime-address "rt:symbol-view" code-base))
                  (not (eq (car (proof-world-machine before)) :svc))
                  (not (proof-world-stop before))
                  (symbols-path-ready-p path code-base link before))
             (and (proof-segment-p (len path) (list link) before :cut after)
                  (proof-frame-return-p '(1 2) t before after)
                  (not (eq (car (proof-world-machine after)) :svc))
                  (equal (proof-world-reg 1 after) (symbols-symbol-view-result before))
                  (symbols-no-memory-or-kernel-change-p before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-symbol-view)
                 (:instance symbols-replay-is-segment
                            (path (symbols-symbol-view-path before))
                            (base code-base) (cut (proof-world-reg 30 before)) (world before))
                 (:instance symbols-replay-is-advance
                            (path (symbols-symbol-view-path before))
                            (base code-base) (cut (proof-world-reg 30 before)) (world before)))
           :in-theory (disable symbols-symbol-view-path symbols-replay
                               symbols-path-ready-p proof-advance symbols-path-control-p symbols-replay-is-segment
                               proof-segment-p))))

(local
 (defthm symbols-effect-add-immediate
   (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31))
            (equal (proof-instruction-effect (list :arithmetic-imm 0 64 rd rn value) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 t (boymoo-model::a64-unsigned
                                           64 (+ (proof-world-reg rn world) value))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-and-register
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect (list :logical-reg 0 64 rd rn rm 0 0 nil) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil
                                  (logand (proof-world-reg rn world)
                                          (proof-world-reg rm world))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-write-register-already-clips
   (equal (boymoo-model::a64-write-reg
           register width sp (boymoo-model::a64-unsigned width value) machine)
          (boymoo-model::a64-write-reg register width sp value machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg)))))

(defun symbols-logical-right-shift-bits (value amount)
  (boymoo-model::a64-unsigned
   64 (logand (logand (boymoo-model::a64-ror 64 value amount) #xffffffffffffffff)
              (1- (expt 2 (- 64 amount))))))

(local
 (defthm symbols-effect-logical-right-shift
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect
                    (list :bitfield 2 64 rd rn amount 63 #xffffffffffffffff
                          (1- (expt 2 (- 64 amount))))
                    world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil
                                  (symbols-logical-right-shift-bits
                                   (proof-world-reg rn world) amount)
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-logical-right-shifts-used-by-symbols
   (implies (and (natp rd) (< rd 31))
            (and (equal (proof-instruction-effect
                         (list :bitfield 2 64 rd rn 1 63 #xffffffffffffffff #x7fffffffffffffff)
                         world)
                        (update-nth 0 (boymoo-model::a64-write-reg
                                       rd 64 nil
                                       (symbols-logical-right-shift-bits
                                        (proof-world-reg rn world) 1)
                                       (symbols-next-pc world))
                                    world))
                 (equal (proof-instruction-effect
                         (list :bitfield 2 64 rd rn 11 63 #xffffffffffffffff #x1fffffffffffff)
                         world)
                        (update-nth 0 (boymoo-model::a64-write-reg
                                       rd 64 nil
                                       (symbols-logical-right-shift-bits
                                        (proof-world-reg rn world) 11)
                                       (symbols-next-pc world))
                                    world))))
   :hints (("Goal"
            :use ((:instance symbols-effect-logical-right-shift (amount 1))
                  (:instance symbols-effect-logical-right-shift (amount 11)))
            :in-theory (disable symbols-effect-logical-right-shift
                                symbols-logical-right-shift-bits)))))

(local
 (in-theory (disable symbols-logical-right-shift-bits)))

(local
 (defthm symbols-logical-right-shift-is-natural
   (natp (symbols-logical-right-shift-bits value amount))
   :hints (("Goal" :in-theory (enable symbols-logical-right-shift-bits)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-logical-right-shift-word-bound
   (< (symbols-logical-right-shift-bits value amount) (expt 2 64))
   :hints (("Goal" :in-theory (enable symbols-logical-right-shift-bits)))
   :rule-classes :linear))

(local
 (defthm symbols-logical-right-shift-fits-word
   (equal (boymoo-model::a64-unsigned 64 (symbols-logical-right-shift-bits value amount))
          (symbols-logical-right-shift-bits value amount))
   :hints (("Goal" :in-theory (enable symbols-logical-right-shift-bits)))))

(defconst *symbols-package-row-path*
  (symbols-code-path "rt:package-row" '(0 4 8 12 16 20 24 28 32)))

(defun symbols-package-row-slot (world)
  (let* ((base (proof-heap-base world))
         (table (boymoo-model::a64-unsigned
                 64 (proof-load-word (+ base 8) (proof-world-machine world))))
         (first (boymoo-model::a64-unsigned 64 (+ base (boymoo-model::a64-unsigned
                                                        64 (+ table 6)))))
         (number (symbols-logical-right-shift-bits (proof-world-reg 0 world) 1))
         (offset (boymoo-model::a64-unsigned 64 (* 8 number))))
    (boymoo-model::a64-unsigned 64 (+ first offset))))

(defun symbols-package-row-address (world)
  (let ((word (boymoo-model::a64-unsigned
               64 (proof-load-word (symbols-package-row-slot world) (proof-world-machine world)))))
    (symbols-box-address word (proof-heap-base world))))

(local
 (defthm symbols-replay-package-row
   (let* ((path *symbols-package-row-path*)
          (after (symbols-replay path before)))
     (implies (and (symbols-runtime-base-p code-base)
                   (equal (proof-world-pc before)
                          (symbols-runtime-address "rt:package-row" code-base))
                   (not (eq (car (proof-world-machine before)) :svc))
                   (not (proof-world-stop before)))
              (and (symbols-path-control-p path code-base before)
                   (proof-frame-return-p '(0 1) nil before after)
                   (not (eq (car (proof-world-machine after)) :svc))
                   (equal (proof-world-reg 0 after) (symbols-package-row-address before))
                   (equal (proof-world-reg 1 after) (symbols-package-row-slot before))
                   (symbols-no-memory-or-kernel-change-p before after))))
   :rule-classes nil))

(defthm symbols-run-package-row
  (let* ((path *symbols-package-row-path*)
         (link (proof-world-reg 30 before))
         (after (proof-advance (len path) before)))
    (implies (and (symbols-runtime-base-p code-base)
                  (equal (proof-world-pc before)
                         (symbols-runtime-address "rt:package-row" code-base))
                  (not (eq (car (proof-world-machine before)) :svc))
                  (not (proof-world-stop before))
                  (symbols-path-ready-p path code-base link before))
             (and (proof-segment-p (len path) (list link) before :cut after)
                  (proof-frame-return-p '(0 1) nil before after)
                  (not (eq (car (proof-world-machine after)) :svc))
                  (equal (proof-world-reg 0 after) (symbols-package-row-address before))
                  (equal (proof-world-reg 1 after) (symbols-package-row-slot before))
                  (symbols-no-memory-or-kernel-change-p before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-package-row)
                 (:instance symbols-replay-is-segment
                            (path *symbols-package-row-path*)
                            (base code-base) (cut (proof-world-reg 30 before)) (world before))
                 (:instance symbols-replay-is-advance
                            (path *symbols-package-row-path*)
                            (base code-base) (cut (proof-world-reg 30 before)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p symbols-path-ready-p
                               proof-advance symbols-replay-is-segment proof-segment-p))))

(defconst *symbols-bucket-address-path*
  (symbols-code-path "rt:intern-bucket-address" '(0 4 8 12 16 20 24 28)))

(defun symbols-dynamic-mask-at (table world)
  (let ((header (boymoo-model::a64-unsigned
                 64 (proof-load-word table (proof-world-machine world)))))
    (boymoo-model::a64-unsigned
     64 (- (symbols-logical-right-shift-bits header 11) 2))))

(defun symbols-dynamic-mask (world)
  (symbols-dynamic-mask-at (proof-world-reg 1 world) world))

(defun symbols-dynamic-bucket-at (table tagged-hash world)
  (let* ((hash (symbols-logical-right-shift-bits tagged-hash 1))
         (index (boymoo-model::a64-unsigned 64 (logand hash (symbols-dynamic-mask-at table world))))
         (offset (boymoo-model::a64-unsigned 64 (* 8 index)))
         (address (boymoo-model::a64-unsigned 64 (+ table offset))))
    (boymoo-model::a64-unsigned 64 (+ address 16))))

(defun symbols-dynamic-bucket-address (world)
  (symbols-dynamic-bucket-at (proof-world-reg 1 world) (proof-world-reg 9 world) world))

(local
 (defthm symbols-replay-bucket-address
   (let* ((path *symbols-bucket-address-path*)
          (after (symbols-replay path before)))
     (implies (and (symbols-runtime-base-p code-base)
                   (equal (proof-world-pc before)
                          (symbols-runtime-address "rt:intern-bucket-address" code-base))
                   (not (eq (car (proof-world-machine before)) :svc))
                   (not (proof-world-stop before)))
              (and (symbols-path-control-p path code-base before)
                   (proof-frame-return-p '(3 4) nil before after)
                   (not (eq (car (proof-world-machine after)) :svc))
                   (equal (proof-world-reg 3 after) (symbols-dynamic-mask before))
                   (equal (proof-world-reg 4 after) (symbols-dynamic-bucket-address before))
                   (symbols-no-memory-or-kernel-change-p before after))))
   :rule-classes nil))

(defthm symbols-run-bucket-address
  (let* ((path *symbols-bucket-address-path*)
         (link (proof-world-reg 30 before))
         (after (proof-advance (len path) before)))
    (implies (and (symbols-runtime-base-p code-base)
                  (equal (proof-world-pc before)
                         (symbols-runtime-address "rt:intern-bucket-address" code-base))
                  (not (eq (car (proof-world-machine before)) :svc))
                  (not (proof-world-stop before))
                  (symbols-path-ready-p path code-base link before))
             (and (proof-segment-p (len path) (list link) before :cut after)
                  (proof-frame-return-p '(3 4) nil before after)
                  (not (eq (car (proof-world-machine after)) :svc))
                  (equal (proof-world-reg 3 after) (symbols-dynamic-mask before))
                  (equal (proof-world-reg 4 after) (symbols-dynamic-bucket-address before))
                  (symbols-no-memory-or-kernel-change-p before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-bucket-address)
                 (:instance symbols-replay-is-segment
                            (path *symbols-bucket-address-path*)
                            (base code-base) (cut (proof-world-reg 30 before)) (world before))
                 (:instance symbols-replay-is-advance
                            (path *symbols-bucket-address-path*)
                            (base code-base) (cut (proof-world-reg 30 before)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p symbols-path-ready-p
                               proof-advance symbols-replay-is-segment proof-segment-p))))

(local
 (defthm symbols-read-sp
   (equal (boymoo-model::a64-read-reg 31 64 t machine)
          (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg boymoo-model::a64-sp)))))

(local
 (defthm symbols-sp-is-natural
   (natp (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-effect-pair-load-on-stack
   (let* ((machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine))
          (address (if (eq mode :post) sp (+ sp offset)))
          (first (boymoo-model::a64-load 8 address machine))
          (second (boymoo-model::a64-load 8 (+ 8 address) machine))
          (next (boymoo-model::a64-write-reg rd 64 nil first (symbols-next-pc world)))
          (next (boymoo-model::a64-write-reg rd2 64 nil second next))
          (next (if (eq mode :post)
                    (boymoo-model::a64-write-reg 31 64 t (+ sp offset) next)
                  next)))
     (implies (and (natp rd) (< rd 31)
                   (natp rd2) (< rd2 31)
                   (member-eq mode '(:offset :post)))
              (equal (proof-instruction-effect (list :pair t 31 rd rd2 mode offset) world)
                     (update-nth 0 next world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-add-to-sp
   (implies
    (not (eq (car (proof-world-machine world)) :svc))
    (equal (proof-instruction-effect (list :arithmetic-imm 0 64 31 31 amount) world)
           (update-nth
            0 (boymoo-model::a64-write-reg
               31 64 t (+ (boymoo-model::a64-sp (proof-world-machine world)) amount)
               (symbols-next-pc world))
            world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-load-by-register
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect
                    (list :single 1 8 rn rd :register rm 3 0)
                    world)
                   (update-nth
                    0 (boymoo-model::a64-write-reg
                       rd 64 nil
                       (boymoo-model::a64-load
                        8 (+ (boymoo-model::a64-read-reg rn 64 t (proof-world-machine world))
                             (proof-world-reg rm world))
                        (proof-world-machine world))
                       (symbols-next-pc world))
                    world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-read-zero-register
   (equal (boymoo-model::a64-read-reg 31 64 nil machine) 0)
   :hints (("Goal" :in-theory (enable boymoo-model::a64-read-reg)))))

(local
 (defthm symbols-effect-register-move
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect
                    (list :logical-reg 1 64 rd 31 rm 0 0 nil)
                    world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil (proof-world-reg rm world)
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-branch-zero
   (implies (not (eq (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect (list :branch-zero delta 64 register invert)
                                             world)
                   (update-nth 0 (if (iff invert (not (equal (proof-world-reg register world) 0)))
                                     (boymoo-model::a64-set-pc
                                      (+ (proof-world-pc world) delta) (symbols-next-pc world))
                                   (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-branch-relative
   (implies (not (eq (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect (list :branch delta nil) world)
                   (update-nth 0 (boymoo-model::a64-set-pc (+ (proof-world-pc world) delta)
                                                          (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(defun symbols-load-register-word (address world)
  (boymoo-model::a64-unsigned 64 (proof-load-word address (proof-world-machine world))))

(defun symbols-stack-word (offset world)
  (symbols-load-register-word (+ (boymoo-model::a64-sp (proof-world-machine world))
                                  offset)
                               world))

(defun symbols-query-visible-row-p (world)
  (let ((row (proof-world-reg 0 world)))
    (and (not (equal row 0))
         (not (equal (symbols-load-register-word (+ row 24) world) *proof-nil*)))))

(defconst *symbols-query-found-path*
  (symbols-code-path "rt:package-query" '(60 64 68 72 76 80 84 88 92)))
(defconst *symbols-query-missing-imports-path*
  (symbols-code-path "rt:package-query" '(60 64 96 100 104)))
(defconst *symbols-query-hidden-imports-path*
  (symbols-code-path "rt:package-query" '(60 64 68 72 76 96 100 104)))
(defconst *symbols-query-missing-witness-path*
  (symbols-code-path "rt:package-query" '(60 64 96 100 104 108)))
(defconst *symbols-query-hidden-witness-path*
  (symbols-code-path "rt:package-query" '(60 64 68 72 76 96 100 104 108)))

(defun symbols-query-string-continuation (world)
  (if (symbols-query-visible-row-p world)
      *symbols-query-found-path*
    (if (equal (symbols-stack-word 8 world) 16)
        (if (equal (proof-world-reg 0 world) 0)
            *symbols-query-missing-imports-path*
          *symbols-query-hidden-imports-path*)
      (if (equal (proof-world-reg 0 world) 0)
          *symbols-query-missing-witness-path*
        *symbols-query-hidden-witness-path*))))

(defun symbols-query-string-target (base world)
  (cond ((symbols-query-visible-row-p world)
         (symbols-stack-word 24 world))
        ((equal (symbols-stack-word 8 world) 16)
         (symbols-runtime-address "rt:imports-absent" base))
        (t (symbols-runtime-address "rt:witness-absent" base))))

(defun symbols-query-string-result-word (world)
  (if (symbols-query-visible-row-p world)
      (symbols-load-register-word
       (+ (proof-world-reg 0 world) (symbols-stack-word 8 world)) world)
    (symbols-stack-word 0 world)))

(defun symbols-query-string-continuation-pre-p (code-base world)
  (and (symbols-runtime-base-p code-base)
       (equal (proof-world-pc world) (+ (symbols-runtime-address "rt:package-query" code-base)
                                        60))
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (member-equal (symbols-stack-word 8 world) '(16 24))
       (< (+ 32 (boymoo-model::a64-sp (proof-world-machine world))) (expt 2 64))))

(defun symbols-query-string-frame-p (base before after)
  (let ((sp (boymoo-model::a64-sp (proof-world-machine before))))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-query-string-target base before))
         (equal (proof-world-reg 0 after) (symbols-query-string-result-word before))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (if (symbols-query-visible-row-p before) (+ sp 32) sp))
         (symbols-no-memory-or-kernel-change-p before after)
         (proof-register-frame-p 30 '(0 1 5 6 29 30) before after)
         (implies (symbols-query-visible-row-p before)
                  (and (equal (proof-world-reg 29 after) (symbols-stack-word 16 before))
                       (equal (proof-world-reg 30 after) (symbols-stack-word 24 before)))))))

(local
 (defthm symbols-replay-query-string-continuation
   (let* ((path (symbols-query-string-continuation before))
          (after (symbols-replay path before)))
     (implies (symbols-query-string-continuation-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-query-string-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition
                                      boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-query-string-continuation
  (let* ((path (symbols-query-string-continuation before))
         (target (symbols-query-string-target code-base before))
         (after (proof-advance (len path) before)))
    (implies (and (symbols-query-string-continuation-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (symbols-query-string-frame-p code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-query-string-continuation)
                 (:instance symbols-replay-is-segment
                            (path (symbols-query-string-continuation before))
                            (base code-base) (cut (symbols-query-string-target code-base before))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path (symbols-query-string-continuation before))
                            (base code-base) (cut (symbols-query-string-target code-base before))
                            (world before)))
           :in-theory (disable symbols-query-string-continuation symbols-replay
                               symbols-path-ready-p proof-advance symbols-path-control-p
                               symbols-replay-is-segment proof-segment-p))))

(local
 (defthm symbols-effect-offset-store
   (implies (not (eq (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect (list :single 0 8 rn register :offset offset)
                                             world)
                   (update-nth
                    0 (boymoo-model::a64-store
                       8 (+ (boymoo-model::a64-read-reg rn 64 t (proof-world-machine world))
                            offset)
                       (proof-world-reg register world) (symbols-next-pc world))
                    world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

; This path begins at the return from the call that selects the new
; bucket. X10 holds the old link before either pointer is overwritten.
(defconst *symbols-rehash-link-path*
  (symbols-code-path "rt:intern-rehash-entry" '(24 28 32 36 40)))

(defun symbols-rehash-linked-world (world)
  (let* ((bucket (proof-world-reg 4 world))
         (entry (proof-world-reg 8 world))
         (head (symbols-load-register-word bucket world))
         (first (boymoo-model::a64-store 8 (+ entry 24) head (proof-world-machine world))))
    (update-nth 0 (boymoo-model::a64-store 8 bucket (proof-world-reg 5 world) first) world)))

(defun symbols-rehash-link-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-rehash-entry" base))
       (symbols-no-memory-or-kernel-change-p (symbols-rehash-linked-world before) after)
       (equal (proof-world-reg 5 after) (proof-world-reg 10 before))
       (proof-register-frame-p 30 '(3 5) before after)
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))))

(local
 (defthm symbols-replay-rehash-link
   (let ((after (symbols-replay *symbols-rehash-link-path* before))
         (loop-address (symbols-runtime-address "rt:intern-rehash-entry" code-base)))
     (implies (and (symbols-runtime-base-p code-base)
                   (equal (proof-world-pc before) (+ loop-address 24))
                   (not (eq (car (proof-world-machine before)) :svc))
                   (not (proof-world-stop before)))
              (and (symbols-path-control-p *symbols-rehash-link-path* code-base before)
                   (symbols-rehash-link-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-rehash-link
  (let* ((path *symbols-rehash-link-path*)
         (after (proof-advance (len path) before))
         (loop-address (symbols-runtime-address "rt:intern-rehash-entry" code-base)))
    (implies (and (symbols-runtime-base-p code-base)
                  (equal (proof-world-pc before) (+ loop-address 24))
                  (not (eq (car (proof-world-machine before)) :svc))
                  (not (proof-world-stop before))
                  (symbols-path-ready-p path code-base loop-address before))
             (and (proof-segment-p (len path) (list loop-address) before :cut after)
                  (symbols-rehash-link-frame-p code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-rehash-link)
                 (:instance symbols-replay-is-segment
                            (path *symbols-rehash-link-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:intern-rehash-entry" code-base))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path *symbols-rehash-link-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:intern-rehash-entry" code-base))
                            (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p
                               symbols-path-ready-p proof-advance
                               symbols-replay-is-segment proof-segment-p))))

(local
 (defthm symbols-effect-compare-register
   (implies (not (eq (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect
                    (list :arithmetic-reg 3 64 31 rn rm 0 0) world)
                   (update-nth 0 (boymoo-model::a64-set-nzcv
                                  (symbols-compare-flags (proof-world-reg rn world)
                                                         (proof-world-reg rm world))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (e/d (proof-instruction-effect symbols-compare-flags)
                                  (boymoo-model::a64-result-flags))))))

(local
 (defthm symbols-effect-shift-eight
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect
                    (list :bitfield 2 64 rd rn 8 63 #xffffffffffffffff #x00ffffffffffffff)
                    world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil
                                  (symbols-logical-right-shift-bits (proof-world-reg rn world) 8)
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :use ((:instance symbols-effect-logical-right-shift (amount 8)))
                   :in-theory (disable symbols-effect-logical-right-shift)))))

(local
 (defthm symbols-effect-call-relative
   (implies (not (eq (car (proof-world-machine world)) :svc))
            (equal (proof-instruction-effect (list :branch delta t) world)
                   (update-nth
                    0 (boymoo-model::a64-set-pc
                       (+ (proof-world-pc world) delta)
                       (boymoo-model::a64-write-reg
                        30 64 nil (+ 4 (proof-world-pc world)) (symbols-next-pc world)))
                    world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(defconst *symbols-find-exhausted-path*
  (symbols-code-path "rt:find-package-loop" '(0 4)))
(defconst *symbols-find-length-mismatch-path*
  (symbols-code-path "rt:find-package-loop" '(0 4 8 12 16 20 24 28 32 36 40 44 48)))
(defconst *symbols-find-byte-call-path*
  (symbols-code-path "rt:find-package-loop" '(0 4 8 12 16 20 24 28 32 36 40 44 48 52 56 60)))

(defun symbols-box-at-slot (address world)
  (symbols-box-address (symbols-load-register-word address world) (proof-heap-base world)))

(defun symbols-found-candidate (world)
  (symbols-box-at-slot (proof-world-reg 7 world) world))

(defun symbols-candidate-name-address (world)
  (symbols-box-at-slot (+ 8 (symbols-found-candidate world)) world))

(defun symbols-candidate-name-size (world)
  (symbols-logical-right-shift-bits
   (symbols-load-register-word (symbols-candidate-name-address world) world)
   8))

(defun symbols-find-iteration-exhausted-p (world)
  (<= (proof-world-reg 8 world) (proof-world-reg 7 world)))

(defun symbols-find-iteration-path (world)
  (cond ((symbols-find-iteration-exhausted-p world) *symbols-find-exhausted-path*)
        ((equal (symbols-candidate-name-size world) (proof-world-reg 6 world))
         *symbols-find-byte-call-path*)
        (t *symbols-find-length-mismatch-path*)))

(defun symbols-find-iteration-target (world base)
  (cond ((symbols-find-iteration-exhausted-p world)
         (symbols-runtime-address "rt:find-package-miss" base))
        ((equal (symbols-candidate-name-size world) (proof-world-reg 6 world))
         (symbols-runtime-address "rt:equal-bytes" base))
        (t (symbols-runtime-address "rt:find-package-loop" base))))

(defun symbols-find-iteration-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-find-iteration-target before base))
       (symbols-no-memory-or-kernel-change-p before after)
       (proof-register-frame-p 30 '(0 1 2 7 9 30) before after)
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (or (symbols-find-iteration-exhausted-p before)
           (and (equal (proof-world-reg 7 after)
                       (boymoo-model::a64-unsigned 64 (+ 8 (proof-world-reg 7 before))))
                (equal (proof-world-reg 9 after) (symbols-found-candidate before))
                (equal (proof-world-reg 2 after) (symbols-candidate-name-size before))
                (implies (equal (symbols-candidate-name-size before)
                                (proof-world-reg 6 before))
                         (and (equal (proof-world-reg 0 after)
                                     (boymoo-model::a64-unsigned
                                      64 (+ 8 (symbols-candidate-name-address before))))
                              (equal (proof-world-reg 1 after) (proof-world-reg 5 before))
                              (equal (proof-world-reg 30 after)
                                     (+ 64 (symbols-runtime-address
                                            "rt:find-package-loop" base)))))))))

(local
 (defthm symbols-replay-find-iteration
   (let* ((path (symbols-find-iteration-path before))
          (after (symbols-replay path before)))
     (implies (and (symbols-runtime-base-p code-base)
                   (equal (proof-world-pc before)
                          (symbols-runtime-address "rt:find-package-loop" code-base))
                   (not (eq (car (proof-world-machine before)) :svc))
                   (not (proof-world-stop before)))
              (and (symbols-path-control-p path code-base before)
                   (symbols-find-iteration-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition
                                      boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-find-iteration
  (let* ((path (symbols-find-iteration-path before))
         (after (symbols-replay path before)))
    (implies (and (symbols-runtime-base-p code-base)
                  (equal (proof-world-pc before)
                         (symbols-runtime-address "rt:find-package-loop" code-base))
                  (not (eq (car (proof-world-machine before)) :svc))
                  (not (proof-world-stop before))
                  (symbols-path-ready-p path code-base nil before))
             (and (equal (proof-advance (len path) before) after)
                  (symbols-find-iteration-frame-p code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-find-iteration)
                 (:instance symbols-replay-is-advance
                            (path (symbols-find-iteration-path before)) (base code-base)
                            (cut nil) (world before)))
           :in-theory (disable symbols-replay symbols-find-iteration-path proof-advance
                               symbols-path-control-p symbols-find-iteration-frame-p))))

(defconst *symbols-find-hit-path*
  (symbols-code-path "rt:find-package-loop" '(64 68 72 76)))
(defconst *symbols-find-next-path*
  (symbols-code-path "rt:find-package-loop" '(64)))
(defconst *symbols-find-miss-path*
  (symbols-code-path "rt:find-package-miss" '(0 4 8)))

(defun symbols-find-result-path (exhausted before)
  (cond (exhausted *symbols-find-miss-path*)
        ((equal (proof-world-reg 0 before) 0) *symbols-find-next-path*)
        (t *symbols-find-hit-path*)))

(defun symbols-find-result-entry (exhausted base)
  (if exhausted
      (symbols-runtime-address "rt:find-package-miss" base)
    (+ 64 (symbols-runtime-address "rt:find-package-loop" base))))

(defun symbols-find-result-target (exhausted base before)
  (if (or exhausted (not (equal (proof-world-reg 0 before) 0)))
      (symbols-stack-word 8 before)
    (symbols-runtime-address "rt:find-package-loop" base)))

(defun symbols-find-result-frame-p (exhausted base before after)
  (let ((returned (or exhausted (not (equal (proof-world-reg 0 before) 0))))
        (sp (boymoo-model::a64-sp (proof-world-machine before))))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-find-result-target exhausted base before))
         (equal (proof-world-reg 0 after)
                (if (and returned (not exhausted)) (proof-world-reg 9 before) 0))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (if returned (+ sp 16) sp))
         (implies returned
                  (and (equal (proof-world-reg 29 after) (symbols-stack-word 0 before))
                       (equal (proof-world-reg 30 after) (symbols-stack-word 8 before))))
         (proof-register-frame-p 30 '(0 29 30) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(defun symbols-find-result-pre-p (exhausted base before)
  (and (symbols-runtime-base-p base)
       (equal (proof-world-pc before) (symbols-find-result-entry exhausted base))
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (< (+ 16 (boymoo-model::a64-sp (proof-world-machine before))) (expt 2 64))))

(local
 (defthm symbols-replay-find-result
   (let* ((path (symbols-find-result-path exhausted before))
          (after (symbols-replay path before)))
     (implies (symbols-find-result-pre-p exhausted code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-find-result-frame-p exhausted code-base before after))))
   :rule-classes nil))

(defthm symbols-run-find-result
  (let* ((path (symbols-find-result-path exhausted before))
         (after (symbols-replay path before))
         (target (symbols-find-result-target exhausted code-base before)))
    (implies (and (symbols-find-result-pre-p exhausted code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (equal (proof-advance (len path) before) after)
                  (symbols-find-result-frame-p exhausted code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-find-result)
                 (:instance symbols-replay-is-segment
                            (path (symbols-find-result-path exhausted before))
                            (base code-base)
                            (cut (symbols-find-result-target exhausted code-base before))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path (symbols-find-result-path exhausted before))
                            (base code-base)
                            (cut (symbols-find-result-target exhausted code-base before))
                            (world before)))
           :in-theory (disable symbols-replay symbols-find-result-path proof-segment-p
                               proof-advance symbols-path-control-p symbols-replay-is-segment))))

(local
 (defthm symbols-effect-move-immediate
   (implies (and (natp rd) (< rd 31) (integerp value))
            (equal (proof-instruction-effect (list :move-wide 2 64 rd value 0) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil value (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(defconst *symbols-query-default-imports-path*
  (symbols-code-path "rt:package-query" '(48 52 84 88 92)))
(defconst *symbols-query-default-witness-path*
  (symbols-code-path "rt:package-query" '(36 40 44 84 88 92)))
(defconst *symbols-query-default-missing-path*
  (symbols-code-path "rt:package-query" '(36)))

(defun symbols-query-default-missing-p (witness before)
  (and witness (equal (proof-world-reg 0 before) 0)))

(defun symbols-query-default-path (witness before)
  (cond ((symbols-query-default-missing-p witness before) *symbols-query-default-missing-path*)
        (witness *symbols-query-default-witness-path*)
        (t *symbols-query-default-imports-path*)))

(defun symbols-query-default-target (witness base before)
  (if (symbols-query-default-missing-p witness before)
      (symbols-runtime-address "rt:missing-acl2" base)
    (symbols-stack-word 24 before)))

(defun symbols-query-default-pre-p (witness base before)
  (and (symbols-runtime-base-p base)
       (equal (proof-world-pc before)
              (+ (symbols-runtime-address "rt:package-query" base) (if witness 36 48)))
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (< (+ 32 (boymoo-model::a64-sp (proof-world-machine before))) (expt 2 64))))

(defun symbols-query-default-frame-p (witness base before after)
  (let* ((missing (symbols-query-default-missing-p witness before))
         (machine (proof-world-machine before))
         (sp (boymoo-model::a64-sp machine))
         (row (proof-world-reg 0 before)))
    (and (not (proof-world-stop after))
         (equal (proof-world-pc after) (symbols-query-default-target witness base before))
         (equal (proof-world-reg 0 after)
                (cond (missing 0)
                      (witness (symbols-load-register-word (+ row 24) before))
                      (t *proof-nil*)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (if missing sp (+ sp 32)))
         (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-nzcv machine))
         (implies (not missing)
                  (and (equal (proof-world-reg 29 after) (symbols-stack-word 16 before))
                       (equal (proof-world-reg 30 after) (symbols-stack-word 24 before))))
         (proof-register-frame-p 30 '(0 29 30) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-replay-query-default
   (let* ((path (symbols-query-default-path witness before))
          (after (symbols-replay path before)))
     (implies (symbols-query-default-pre-p witness code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-query-default-frame-p witness code-base before after))))
   :rule-classes nil))

(defthm symbols-run-query-default
  (let* ((path (symbols-query-default-path witness before))
         (after (proof-advance (len path) before))
         (target (symbols-query-default-target witness code-base before)))
    (implies (and (symbols-query-default-pre-p witness code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (symbols-query-default-frame-p witness code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-query-default)
                 (:instance symbols-replay-is-segment
                            (path (symbols-query-default-path witness before))
                            (base code-base)
                            (cut (symbols-query-default-target witness code-base before))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path (symbols-query-default-path witness before))
                            (base code-base) (cut (symbols-query-default-target witness code-base before))
                            (world before)))
           :in-theory (disable symbols-replay symbols-query-default-path proof-segment-p
                               symbols-path-ready-p proof-advance
                               symbols-path-control-p symbols-replay-is-segment))))

(defconst *symbols-name-found-path*
  (symbols-code-path "prim:COMMON-LISP::SYMBOL-NAME" '(8 12 16 20)))
(defconst *symbols-name-default-path*
  (symbols-code-path "prim:COMMON-LISP::SYMBOL-NAME" '(8 12)))

(defun symbols-name-continuation-path (before)
  (if (equal (proof-world-reg 1 before) 0)
      *symbols-name-default-path*
    *symbols-name-found-path*))

(defun symbols-name-continuation-target (base before)
  (if (equal (proof-world-reg 1 before) 0)
      (symbols-runtime-address "rt:empty-string" base)
    (symbols-stack-word 8 before)))

(defun symbols-name-continuation-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (equal (proof-world-pc before)
              (+ (symbols-runtime-address "prim:COMMON-LISP::SYMBOL-NAME" base) 8))
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (< (+ 16 (boymoo-model::a64-sp (proof-world-machine before))) (expt 2 64))))

(defun symbols-name-continuation-frame-p (base before after)
  (let ((header (proof-world-reg 1 before)))
    (and (not (proof-world-stop after))
         (equal (proof-world-pc after) (symbols-name-continuation-target base before))
         (equal (proof-world-reg 0 after)
                (if (equal header 0)
                    (proof-world-reg 0 before)
                  (symbols-load-register-word (+ header 8) before)))
         (equal (proof-world-reg 29 after) (symbols-stack-word 0 before))
         (equal (proof-world-reg 30 after) (symbols-stack-word 8 before))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (+ 16 (boymoo-model::a64-sp (proof-world-machine before))))
         (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-nzcv (proof-world-machine before)))
         (proof-register-frame-p 30 '(0 29 30) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-replay-name-continuation
   (let* ((path (symbols-name-continuation-path before))
          (after (symbols-replay path before)))
     (implies (symbols-name-continuation-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-name-continuation-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-name-continuation
  (let* ((path (symbols-name-continuation-path before))
         (after (proof-advance (len path) before))
         (target (symbols-name-continuation-target code-base before)))
    (implies (and (symbols-name-continuation-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (symbols-name-continuation-frame-p code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-name-continuation)
                 (:instance symbols-replay-is-segment
                            (path (symbols-name-continuation-path before))
                            (base code-base)
                            (cut (symbols-name-continuation-target code-base before))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path (symbols-name-continuation-path before))
                            (base code-base)
                            (cut (symbols-name-continuation-target code-base before))
                            (world before)))
           :in-theory (disable symbols-replay symbols-name-continuation-path proof-segment-p
                               symbols-path-ready-p proof-advance
                               symbols-path-control-p symbols-replay-is-segment))))

(local
 (defthm symbols-effect-save-stack-pair
   (let* ((machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine))
          (next (symbols-next-pc world))
          (saved-first (boymoo-model::a64-store 8 (- sp 16)
                                                (proof-world-reg first world) next))
          (saved-second (boymoo-model::a64-store 8 (- sp 8)
                                                 (proof-world-reg second world) saved-first)))
     (implies (not (eq (car machine) :svc))
              (equal (proof-instruction-effect (list :pair nil 31 first second :pre -16)
                                               world)
                     (update-nth 0 (boymoo-model::a64-write-reg
                                    31 64 t (- sp 16) saved-second)
                                 world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-sp-word-bound
   (< (boymoo-model::a64-sp machine) (expt 2 64))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :linear))

(defconst *symbols-query-setup-path*
  (symbols-code-path "rt:package-query" '(0 4 8)))

(defun symbols-query-saved-world (before)
  (let* ((machine (proof-world-machine (symbols-saved-link-world before)))
         (sp (boymoo-model::a64-sp machine))
         (saved (boymoo-model::a64-store 8 (- sp 32) (proof-world-reg 0 before) machine))
         (saved (boymoo-model::a64-store 8 (- sp 24) (proof-world-reg 6 before) saved)))
    (update-nth 0 saved before)))

(defun symbols-query-setup-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (<= 32 (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:package-query" base))))

(defun symbols-query-setup-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:string-view" base))
       (equal (proof-world-reg 30 after) (+ 12 (symbols-runtime-address "rt:package-query" base)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
       (symbols-no-memory-or-kernel-change-p (symbols-query-saved-world before) after)
       (proof-register-frame-p 30 '(30) before after)))

(local
 (defthm symbols-replay-query-setup
   (let ((after (symbols-replay *symbols-query-setup-path* before)))
     (implies (symbols-query-setup-pre-p code-base before)
              (and (symbols-path-control-p *symbols-query-setup-path* code-base before)
                   (symbols-query-setup-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-query-setup
  (let* ((path *symbols-query-setup-path*)
         (after (proof-advance (len path) before))
         (target (symbols-runtime-address "rt:string-view" code-base)))
    (implies (and (symbols-query-setup-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (symbols-query-setup-frame-p code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-query-setup)
                 (:instance symbols-replay-is-segment
                            (path *symbols-query-setup-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:string-view" code-base))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path *symbols-query-setup-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:string-view" code-base))
                            (world before)))
           :in-theory (disable symbols-replay proof-segment-p proof-advance symbols-path-ready-p
                               symbols-path-control-p symbols-replay-is-segment))))

(local
 (defthm symbols-effect-direct-address
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect (list :address rd offset nil) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil (+ (proof-world-pc world) offset)
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(defconst *symbols-query-dispatch-string-path*
  (symbols-code-path "rt:package-query" '(12 56)))
(defconst *symbols-query-dispatch-imports-path*
  (symbols-code-path "rt:package-query" '(12 16 20)))
(defconst *symbols-query-dispatch-witness-path*
  (symbols-code-path "rt:package-query" '(12 16 20 24 28 32)))

(defun symbols-query-dispatch-path (world)
  (cond ((not (equal (proof-world-reg 1 world) 0)) *symbols-query-dispatch-string-path*)
        ((equal (proof-world-reg 6 world) 16) *symbols-query-dispatch-imports-path*)
        (t *symbols-query-dispatch-witness-path*)))

(defun symbols-query-dispatch-target (base world)
  (if (and (equal (proof-world-reg 1 world) 0) (equal (proof-world-reg 6 world) 16))
      (symbols-runtime-address "rt:package-query-nil" base)
    (symbols-runtime-address "rt:find-package" base)))

(defun symbols-query-dispatch-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (member-equal (proof-world-reg 6 world) '(16 24))
       (equal (proof-world-pc world) (+ (symbols-runtime-address "rt:package-query" base) 12))))

(defun symbols-query-dispatch-frame-p (base before after)
  (let* ((string-case (not (equal (proof-world-reg 1 before) 0)))
         (acl2-lookup (and (not string-case) (equal (proof-world-reg 6 before) 24)))
         (query (symbols-runtime-address "rt:package-query" base)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-query-dispatch-target base before))
         (equal (proof-world-reg 1 after)
                (if acl2-lookup (symbols-runtime-address "rt:acl2-name" base)
                  (proof-world-reg 1 before)))
         (equal (proof-world-reg 2 after) (if acl2-lookup 4 (proof-world-reg 2 before)))
         (equal (proof-world-reg 30 after)
                (cond (acl2-lookup (+ query 36))
                      (string-case (+ query 60))
                      (t (proof-world-reg 30 before))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(1 2 30) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-replay-query-dispatch
   (let* ((path (symbols-query-dispatch-path before))
          (after (symbols-replay path before)))
     (implies (symbols-query-dispatch-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-query-dispatch-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition
                                      boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-query-dispatch
  (let* ((path (symbols-query-dispatch-path before))
         (after (proof-advance (len path) before))
         (target (symbols-query-dispatch-target code-base before)))
    (implies (and (symbols-query-dispatch-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (symbols-query-dispatch-frame-p code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-query-dispatch)
                 (:instance symbols-replay-is-segment
                            (path (symbols-query-dispatch-path before)) (base code-base)
                            (cut (symbols-query-dispatch-target code-base before))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path (symbols-query-dispatch-path before)) (base code-base)
                            (cut (symbols-query-dispatch-target code-base before))
                            (world before)))
           :in-theory (disable symbols-replay symbols-query-dispatch-path proof-segment-p
                               symbols-path-ready-p proof-advance
                               symbols-path-control-p symbols-replay-is-segment))))

(local
 (defthm symbols-rotate-word-is-natural
   (natp (boymoo-model::a64-ror 64 word amount))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-ror)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-rotate-word-fits
   (equal (boymoo-model::a64-unsigned 64 (boymoo-model::a64-ror 64 word amount))
          (boymoo-model::a64-ror 64 word amount))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-ror)))))

(defthmd symbols-logical-right-shift-correct
  (implies (and (natp word) (< word (expt 2 64))
                (member-equal amount '(1 8 11)))
           (equal (symbols-logical-right-shift-bits word amount)
                  (floor word (expt 2 amount))))
  :hints (("Goal"
           :use ((:instance symbols-mask-is-unsigned
                            (width 64) (value (boymoo-model::a64-ror 64 word amount)))
                 (:instance symbols-mask-is-unsigned
                            (width (- 64 amount))
                            (value (logand (boymoo-model::a64-ror 64 word amount)
                                           #xffffffffffffffff)))
                 (:instance symbols-rotate-low-field-is-right-shift)
                 (:instance symbols-fixed-right-shift-range))
           :in-theory (e/d (symbols-logical-right-shift-bits)
                           (symbols-rotate-low-field-is-right-shift)))))

(defthm symbols-package-row-slot-for-tagged-number
  (let* ((base (proof-heap-base world))
         (reference (symbols-load-register-word (+ base 8) world))
         (address (+ base reference 6 (* 8 number))))
    (implies (and (natp number) (< number (expt 2 63))
                  (equal (proof-world-reg 0 world) (+ 1 (* 2 number)))
                  (< address (expt 2 64)))
             (equal (symbols-package-row-slot world) address)))
  :hints (("Goal"
           :use ((:instance symbols-logical-right-shift-correct
                            (word (proof-world-reg 0 world)) (amount 1))
                 (:instance symbols-floor-of-decomposition (q number) (r 1) (divisor 2))
                 (:instance symbols-load-width
                            (count 8) (address (+ (proof-heap-base world) 8))
                            (machine (proof-world-machine world))))
           :in-theory (e/d (symbols-word-load-fits) (symbols-floor-of-decomposition))))
  :rule-classes nil)

(defthm symbols-vector-header-gives-dynamic-mask
  (let ((header (symbols-load-register-word (proof-world-reg 1 world) world)))
    (implies (and (posp size) (< (+ 1 size) (expt 2 53))
                  (equal header (+ 6 (* 2048 (1+ size)))))
             (equal (symbols-dynamic-mask world) (1- size))))
  :hints (("Goal"
           :use ((:instance symbols-logical-right-shift-correct
                            (word (symbols-load-register-word (proof-world-reg 1 world) world))
                            (amount 11))
                 (:instance symbols-floor-of-decomposition (q (1+ size)) (r 6) (divisor 2048)))
           :in-theory (disable symbols-floor-of-decomposition)))
  :rule-classes nil)

(defthm symbols-symbol-view-agrees-with-value
  (let* ((word (proof-world-reg 0 world))
         (base (proof-heap-base world))
         (machine (proof-world-machine world))
         (address (proof-pointer-address word base)))
    (implies (proof-value-p word datum base objects packages machine)
             (equal (symbols-symbol-view-result world)
                    (if (symbolp datum) address 0))))
  :hints (("Goal"
           :use ((:instance symbols-only-symbols-have-symbol-headers
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance symbols-load-low-byte
                            (count 8)
                            (address (proof-pointer-address (proof-world-reg 0 world)
                                                            (proof-heap-base world)))
                            (machine (proof-world-machine world)))
                 (:instance symbols-load-width
                            (count 1)
                            (address (proof-pointer-address (proof-world-reg 0 world)
                                                            (proof-heap-base world)))
                            (machine (proof-world-machine world))))
           :in-theory (e/d (symbols-symbol-tag-p symbols-symbol-header-p)
                           (proof-value-p symbols-only-symbols-have-symbol-headers
                            symbols-load-low-byte)))))

(defconst *symbols-find-setup-path*
  (symbols-code-path "rt:find-package" '(0 4 8 12 16 20 24 28 32 36)))

(defun symbols-find-setup-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (<= 16 (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (proof-world-pc before) (symbols-runtime-address "rt:find-package" base))))

(defun symbols-find-vector-address (heap world)
  (symbols-box-address (symbols-load-register-word (+ heap 8) world) heap))

(defun symbols-find-first-slot (heap world)
  (boymoo-model::a64-unsigned 64 (+ 8 (symbols-find-vector-address heap world))))

(defun symbols-find-vector-size (heap world)
  (symbols-logical-right-shift-bits
   (symbols-load-register-word (symbols-find-vector-address heap world) world) 8))

(defun symbols-find-setup-frame-p (base before after)
  (let* ((saved (symbols-saved-link-world before))
         (heap (proof-heap-base before))
         (slots (symbols-find-first-slot heap saved))
         (size (symbols-find-vector-size heap saved)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-runtime-address "rt:find-package-loop" base))
         (equal (proof-world-reg 5 after) (proof-world-reg 1 before))
         (equal (proof-world-reg 6 after) (proof-world-reg 2 before))
         (equal (proof-world-reg 7 after) slots)
         (equal (proof-world-reg 8 after) (boymoo-model::a64-unsigned 64 (+ slots size)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
         (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-nzcv (proof-world-machine before)))
         (proof-register-frame-p 30 '(5 6 7 8) before after)
         (symbols-no-memory-or-kernel-change-p saved after))))

(local
 (defthm symbols-replay-find-setup
   (let ((after (symbols-replay *symbols-find-setup-path* before)))
     (implies (symbols-find-setup-pre-p code-base before)
              (and (symbols-path-control-p *symbols-find-setup-path* code-base before)
                   (symbols-find-setup-frame-p code-base before after))))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                  ((:definition boymoo-model::a64-read-bytes)))))
   :rule-classes nil))

(defthm symbols-run-find-setup
  (let* ((path *symbols-find-setup-path*)
         (after (symbols-replay path before))
         (target (symbols-runtime-address "rt:find-package-loop" code-base)))
    (implies (and (symbols-find-setup-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (equal (proof-advance (len path) before) after)
                  (symbols-find-setup-frame-p code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-find-setup)
                 (:instance symbols-replay-is-segment
                            (path *symbols-find-setup-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:find-package-loop" code-base))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path *symbols-find-setup-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:find-package-loop" code-base))
                            (world before)))
           :in-theory (disable symbols-replay proof-segment-p symbols-path-ready-p
                               proof-advance symbols-path-control-p symbols-replay-is-segment))))

(defconst *symbols-package-name-entry* "prim:ACL2::SYMBOL-PACKAGE-NAME")

(defconst *symbols-package-name-found-path*
  (symbols-code-path *symbols-package-name-entry* '(24 28 32 36 40 44)))
(defconst *symbols-package-name-hidden-path*
  (symbols-code-path *symbols-package-name-entry* '(24 28 32 36 56 60)))

(defun symbols-package-name-hidden-p (world)
  (equal (symbols-load-register-word (+ (proof-world-reg 0 world) 24) world)
         *proof-nil*))

(defun symbols-package-name-continuation-path (world)
  (if (symbols-package-name-hidden-p world)
      *symbols-package-name-hidden-path*
    *symbols-package-name-found-path*))

(defun symbols-package-name-continuation-target (base world)
  (if (symbols-package-name-hidden-p world)
      (symbols-runtime-address "rt:hidden-symbol" base)
    (symbols-stack-word 8 world)))

(defun symbols-package-name-continuation-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (< (+ 16 (boymoo-model::a64-sp (proof-world-machine before))) (expt 2 64))
       (equal (proof-world-pc before)
              (+ (symbols-runtime-address *symbols-package-name-entry* base) 24))))

(defun symbols-package-name-continuation-frame-p (base before after)
  (and (not (proof-world-stop after))
       (equal (proof-world-pc after) (symbols-package-name-continuation-target base before))
       (equal (proof-world-reg 0 after)
              (if (symbols-package-name-hidden-p before)
                  (proof-world-reg 5 before)
                (symbols-load-register-word (+ (proof-world-reg 0 before) 8) before)))
       (equal (proof-world-reg 29 after) (symbols-stack-word 0 before))
       (equal (proof-world-reg 30 after) (symbols-stack-word 8 before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (+ 16 (boymoo-model::a64-sp (proof-world-machine before))))
       (proof-register-frame-p 30 '(0 1 29 30) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-replay-package-name-continuation
   (let* ((path (symbols-package-name-continuation-path before))
          (after (symbols-replay path before)))
     (implies (symbols-package-name-continuation-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-package-name-continuation-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition
                                      boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-package-name-continuation
  (let* ((path (symbols-package-name-continuation-path before))
         (after (proof-advance (len path) before))
         (target (symbols-package-name-continuation-target code-base before)))
    (implies (and (symbols-package-name-continuation-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (symbols-package-name-continuation-frame-p code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-package-name-continuation)
                 (:instance symbols-replay-is-segment
                            (path (symbols-package-name-continuation-path before))
                            (base code-base)
                            (cut (symbols-package-name-continuation-target code-base before))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path (symbols-package-name-continuation-path before))
                            (base code-base) (cut (symbols-package-name-continuation-target code-base before))
                            (world before)))
           :in-theory (disable symbols-replay symbols-package-name-continuation-path
                               symbols-path-ready-p proof-segment-p proof-advance symbols-path-control-p
                               symbols-replay-is-segment))))

(defconst *symbols-imports-wrapper-path*
  (symbols-code-path "prim:ACL2::PKG-IMPORTS" '(0 4)))
(defconst *symbols-witness-wrapper-path*
  (symbols-code-path "prim:ACL2::PKG-WITNESS" '(0)))

(defun symbols-query-wrapper-path (witness)
  (if witness *symbols-witness-wrapper-path* *symbols-imports-wrapper-path*))

(defun symbols-query-wrapper-pre-p (witness base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (equal (proof-world-pc before)
              (if witness
                  (symbols-runtime-address "prim:ACL2::PKG-WITNESS" base)
                (symbols-runtime-address "prim:ACL2::PKG-IMPORTS" base)))))

(defun symbols-query-wrapper-frame-p (witness base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:package-query" base))
       (equal (proof-world-reg 6 after) (if witness 24 16))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))
       (proof-register-frame-p 30 '(6) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-replay-query-wrapper
   (let* ((path (symbols-query-wrapper-path witness))
          (after (symbols-replay path before)))
     (implies (symbols-query-wrapper-pre-p witness code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-query-wrapper-frame-p witness code-base before after))))
   :rule-classes nil))

(defthm symbols-run-query-wrapper
  (let* ((path (symbols-query-wrapper-path witness))
         (after (proof-advance (len path) before))
         (target (symbols-runtime-address "rt:package-query" code-base)))
    (implies (and (symbols-query-wrapper-pre-p witness code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (symbols-query-wrapper-frame-p witness code-base before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-query-wrapper)
                 (:instance symbols-replay-is-segment
                            (path (symbols-query-wrapper-path witness)) (base code-base)
                            (cut (symbols-runtime-address "rt:package-query" code-base))
                            (world before))
                 (:instance symbols-replay-is-advance
                            (path (symbols-query-wrapper-path witness)) (base code-base)
                            (cut (symbols-runtime-address "rt:package-query" code-base))
                            (world before)))
           :in-theory (disable symbols-replay symbols-query-wrapper-path proof-segment-p
                               symbols-path-ready-p proof-advance
                               symbols-path-control-p symbols-replay-is-segment))))

(defconst *symbols-intern-reject-path*
  (symbols-code-path "rt:intern-nil" '(0 4 8 12 16)))

(defconst *symbols-intern-return-path* (cdr *symbols-intern-reject-path*))

(defun symbols-intern-reject-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (< (+ 48 (boymoo-model::a64-sp (proof-world-machine before))) (expt 2 64))
       (equal (proof-world-pc before) (symbols-runtime-address "rt:intern-nil" base))))

(defun symbols-intern-restore-frame-p (result before after)
  (and (not (proof-world-stop after))
       (equal (proof-world-pc after) (symbols-stack-word 8 before))
       (equal (proof-world-reg 0 after) result)
       (equal (proof-world-reg 29 after) (symbols-stack-word 0 before))
       (equal (proof-world-reg 30 after) (symbols-stack-word 8 before))
       (equal (proof-world-reg 21 after) (symbols-stack-word 16 before))
       (equal (proof-world-reg 22 after) (symbols-stack-word 24 before))
       (equal (proof-world-reg 19 after) (symbols-stack-word 32 before))
       (equal (proof-world-reg 20 after) (symbols-stack-word 40 before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (+ 48 (boymoo-model::a64-sp (proof-world-machine before))))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))
       (proof-register-frame-p 30 '(0 19 20 21 22 29 30) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-replay-intern-reject
   (let ((after (symbols-replay *symbols-intern-reject-path* before)))
     (implies (symbols-intern-reject-pre-p code-base before)
              (and (symbols-path-control-p *symbols-intern-reject-path* code-base before)
                   (symbols-intern-restore-frame-p *proof-nil* before after))))
   :rule-classes nil))

(defthm symbols-run-intern-reject
  (let* ((path *symbols-intern-reject-path*)
         (after (symbols-replay path before))
         (target (symbols-stack-word 8 before)))
    (implies (and (symbols-intern-reject-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (equal (proof-advance (len path) before) after)
                  (symbols-intern-restore-frame-p *proof-nil* before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-reject)
                 (:instance symbols-replay-is-segment
                            (path *symbols-intern-reject-path*) (base code-base)
                            (cut (symbols-stack-word 8 before)) (world before))
                 (:instance symbols-replay-is-advance
                            (path *symbols-intern-reject-path*) (base code-base)
                            (cut (symbols-stack-word 8 before)) (world before)))
           :in-theory (disable symbols-replay proof-segment-p proof-advance
                               symbols-path-control-p symbols-replay-is-segment))))

(defun symbols-intern-return-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (< (+ 48 (boymoo-model::a64-sp (proof-world-machine before))) (expt 2 64))
       (equal (proof-world-pc before) (symbols-runtime-address "rt:intern-return" base))))

(local
 (defthm symbols-replay-intern-return
   (let ((after (symbols-replay *symbols-intern-return-path* before)))
     (implies (symbols-intern-return-pre-p code-base before)
              (and (symbols-path-control-p *symbols-intern-return-path* code-base before)
                   (symbols-intern-restore-frame-p (proof-world-reg 0 before) before after))))
   :rule-classes nil))

(defthm symbols-run-intern-return
  (let* ((path *symbols-intern-return-path*)
         (after (proof-advance (len path) before)))
    (implies (and (symbols-intern-return-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-stack-word 8 before) before))
             (symbols-intern-restore-frame-p (proof-world-reg 0 before) before after)))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-return)
                 (:instance symbols-replay-is-advance
                            (path *symbols-intern-return-path*) (base code-base)
                            (cut (symbols-stack-word 8 before)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-hash-loop-done-path*
  (symbols-code-path "rt:intern-hash" '(0 4)))
(defconst *symbols-hash-loop-byte-path*
  (symbols-code-path "rt:intern-hash" '(0 4 8 12 16 20 24)))

(defun symbols-hash-loop-done-p (world)
  (<= (proof-world-reg 21 world) (proof-world-reg 4 world)))

(defun symbols-hash-loop-path (world)
  (if (symbols-hash-loop-done-p world)
      *symbols-hash-loop-done-path*
    *symbols-hash-loop-byte-path*))

(defun symbols-hash-loop-target (base world)
  (symbols-runtime-address (if (symbols-hash-loop-done-p world)
                               "rt:intern-bucket"
                             "rt:intern-hash")
                           base))

(defun symbols-hash-loop-byte (world)
  (boymoo-model::a64-load 1 (+ (proof-world-reg 8 world) (proof-world-reg 4 world))
                         (proof-world-machine world)))

(defun symbols-hash-loop-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:intern-hash" base))))

(defun symbols-hash-loop-frame-p (base before after)
  (let ((done (symbols-hash-loop-done-p before))
        (index (proof-world-reg 4 before))
        (hash (proof-world-reg 3 before)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-hash-loop-target base before))
         (equal (proof-world-reg 4 after) (if done index (1+ index)))
         (equal (proof-world-reg 3 after)
                (if done hash (symbols-hash-byte hash (symbols-hash-loop-byte before))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(3 4 5) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-effect-byte-load-by-register
   (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31))
            (equal (proof-instruction-effect (list :single 1 1 rn rd :register rm 3 0)
                                             world)
                   (update-nth
                    0 (boymoo-model::a64-write-reg
                       rd 8 nil
                       (boymoo-model::a64-load 1 (+ (proof-world-reg rn world)
                                                   (proof-world-reg rm world))
                                              (proof-world-machine world))
                       (symbols-next-pc world))
                    world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-byte-load-fits
   (equal (boymoo-model::a64-unsigned 8 (boymoo-model::a64-load 1 address machine))
          (boymoo-model::a64-load 1 address machine))
   :hints (("Goal"
            :use ((:instance symbols-load-width (count 1)))))))

(local
 (defthm symbols-replay-hash-loop-iteration
   (let* ((path (symbols-hash-loop-path before))
          (after (symbols-replay path before)))
     (implies (symbols-hash-loop-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-hash-loop-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable symbols-hash-byte-is-polynomial-step
                                       boymoo-model::a64-condition
                                       boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-hash-loop-iteration
  (let ((path (symbols-hash-loop-path before)))
    (implies (and (symbols-hash-loop-pre-p code-base before)
                  (symbols-path-ready-p path code-base nil before))
             (symbols-hash-loop-frame-p code-base before
                                        (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-hash-loop-iteration)
                 (:instance symbols-replay-is-advance
                            (path (symbols-hash-loop-path before)) (base code-base)
                            (cut nil) (world before)))
           :in-theory (disable symbols-replay symbols-hash-loop-path
                               symbols-hash-loop-frame-p proof-advance
                               symbols-path-control-p)))
  :rule-classes nil)

(defconst *symbols-string-tag-miss-path*
  (symbols-code-path "rt:string-view" '(0 4 8 48 52 56)))
(defconst *symbols-string-header-miss-path*
  (symbols-code-path "rt:string-view" '(0 4 8 12 16 20 24 28 32 48 52 56)))
(defconst *symbols-string-hit-path*
  (symbols-code-path "rt:string-view" '(0 4 8 12 16 20 24 28 32 36 40 44)))

(defun symbols-string-header-word (world)
  (symbols-load-register-word (symbols-symbol-header world) world))

(defun symbols-string-hit-p (world)
  (and (symbols-symbol-tag-p world)
       (equal (boymoo-model::a64-unsigned 8 (symbols-string-header-word world)) 1)))

(defun symbols-string-view-path (world)
  (cond ((not (symbols-symbol-tag-p world)) *symbols-string-tag-miss-path*)
        ((symbols-string-hit-p world) *symbols-string-hit-path*)
        (t *symbols-string-header-miss-path*)))

(defun symbols-string-payload (world)
  (boymoo-model::a64-unsigned 64 (+ 8 (symbols-symbol-header world))))

(defun symbols-string-view-frame-p (before after)
  (and (proof-frame-return-p '(1 2 3) t before after)
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-reg 1 after)
              (if (symbols-string-hit-p before) (symbols-string-payload before) 0))
       (equal (proof-world-reg 2 after)
              (if (symbols-string-hit-p before)
                  (symbols-logical-right-shift-bits (symbols-string-header-word before) 8)
                0))
       (symbols-no-memory-or-kernel-change-p before after)))

(defun symbols-string-view-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:string-view" base))))

(local
 (defthm symbols-logand-255
   (implies (integerp word)
            (equal (logand word 255) (boymoo-model::a64-unsigned 8 word)))
   :hints (("Goal" :use ((:instance symbols-mask-is-unsigned (width 8) (value word)))))))

(local
 (defthm symbols-replay-string-view
   (let* ((path (symbols-string-view-path before))
          (after (symbols-replay path before)))
     (implies (symbols-string-view-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-string-view-frame-p before after))))
   :hints (("Goal" :in-theory (e/d (symbols-symbol-tag-p)
                                  (boymoo-model::a64-condition boymoo-model::a64-result-flags))))
   :rule-classes nil))

(defthm symbols-run-string-view
  (let* ((path (symbols-string-view-path before))
         (after (proof-advance (len path) before))
         (target (proof-world-reg 30 before)))
    (implies (and (symbols-string-view-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (symbols-string-view-frame-p before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-string-view)
                 (:instance symbols-replay-is-segment
                            (path (symbols-string-view-path before)) (base code-base)
                            (cut (proof-world-reg 30 before)) (world before))
                 (:instance symbols-replay-is-advance
                            (path (symbols-string-view-path before)) (base code-base)
                            (cut (proof-world-reg 30 before)) (world before)))
           :in-theory (disable symbols-replay symbols-string-view-path proof-advance
                               proof-segment-p symbols-path-control-p symbols-replay-is-segment)))
  :rule-classes nil)

(defconst *symbols-rehash-skip-path*
  (symbols-code-path "rt:intern-rehash-entry" '(0 4)))
(defconst *symbols-rehash-prefix-path*
  (symbols-code-path "rt:intern-rehash-entry" '(0 4 8 12 16 20)))

(defun symbols-rehash-end-of-chain-p (world)
  (equal (proof-world-reg 5 world) *proof-nil*))

(defun symbols-rehash-prefix-path (world)
  (if (symbols-rehash-end-of-chain-p world)
      *symbols-rehash-skip-path*
    *symbols-rehash-prefix-path*))

(defun symbols-rehash-prefix-target (base world)
  (symbols-runtime-address (if (symbols-rehash-end-of-chain-p world)
                               "rt:intern-rehash-bucket"
                             "rt:intern-bucket-address")
                           base))

(defun symbols-rehash-entry-address (world)
  (symbols-box-address (proof-world-reg 5 world) (proof-heap-base world)))

(defun symbols-rehash-entry-hash (world)
  (symbols-load-register-word (+ (symbols-rehash-entry-address world) 16) world))

(defun symbols-rehash-next-entry (world)
  (symbols-load-register-word (+ (symbols-rehash-entry-address world) 24) world))

(defun symbols-rehash-prefix-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:intern-rehash-entry" base))))

(defun symbols-rehash-prefix-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-rehash-prefix-target base before))
       (implies (not (symbols-rehash-end-of-chain-p before))
                (and (equal (proof-world-reg 8 after) (symbols-rehash-entry-address before))
                     (equal (proof-world-reg 9 after) (symbols-rehash-entry-hash before))
                     (equal (proof-world-reg 10 after) (symbols-rehash-next-entry before))
                     (equal (proof-world-reg 30 after)
                            (+ 24 (symbols-runtime-address "rt:intern-rehash-entry" base)))))
       (proof-register-frame-p 30 '(8 9 10 30) before after)
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-effect-pair-load-at-offset
   (implies (and (natp source) (< source 31)
                 (natp first) (< first 31) (natp second) (< second 31))
            (let* ((machine (proof-world-machine world))
                   (address (+ (proof-world-reg source world) offset))
                   (left (boymoo-model::a64-load 8 address machine))
                   (right (boymoo-model::a64-load 8 (+ address 8) machine)))
              (equal (proof-instruction-effect (list :pair t source first second :offset offset)
                                               world)
                     (update-nth 0 (boymoo-model::a64-write-reg
                                    second 64 nil right
                                    (boymoo-model::a64-write-reg first 64 nil left
                                                                 (symbols-next-pc world)))
                                 world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-replay-rehash-prefix
   (let* ((path (symbols-rehash-prefix-path before))
          (after (symbols-replay path before)))
     (implies (symbols-rehash-prefix-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-rehash-prefix-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition
                                       boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-rehash-prefix
  (let ((path (symbols-rehash-prefix-path before)))
    (implies (and (symbols-rehash-prefix-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-rehash-prefix-target code-base before)
                                        before))
             (symbols-rehash-prefix-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-rehash-prefix)
                 (:instance symbols-replay-is-advance
                            (path (symbols-rehash-prefix-path before)) (base code-base)
                            (cut (symbols-rehash-prefix-target code-base before)) (world before)))
           :in-theory (disable symbols-replay proof-advance symbols-rehash-prefix-path
                               symbols-rehash-prefix-frame-p symbols-path-control-p
                               symbols-path-ready-p)))
  :rule-classes nil)

(defun symbols-name-entry-label (package-name)
  (if package-name *symbols-package-name-entry* "prim:COMMON-LISP::SYMBOL-NAME"))

(defconst *symbols-name-setup-path* (symbols-code-path (symbols-name-entry-label nil) '(0 4)))
(defconst *symbols-package-name-setup-path* (symbols-code-path (symbols-name-entry-label t) '(0 4)))

(defun symbols-name-setup-path (package-name)
  (if package-name *symbols-package-name-setup-path* *symbols-name-setup-path*))

(defun symbols-name-setup-pre-p (package-name base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (<= 16 (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (proof-world-pc before) (symbols-runtime-address (symbols-name-entry-label package-name) base))))

(defun symbols-name-setup-frame-p (package-name base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:symbol-view" base))
       (equal (proof-world-reg 30 after)
              (+ 8 (symbols-runtime-address (symbols-name-entry-label package-name) base)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
       (proof-register-frame-p 30 '(30) before after)
       (symbols-no-memory-or-kernel-change-p (symbols-saved-link-world before) after)))

(local
 (defthm symbols-replay-name-setup
   (let* ((path (symbols-name-setup-path package-name))
          (after (symbols-replay path before)))
     (implies (symbols-name-setup-pre-p package-name code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-name-setup-frame-p package-name code-base before after))))
   :rule-classes nil))

(defthm symbols-run-name-setup
  (let* ((path (symbols-name-setup-path package-name))
         (target (symbols-runtime-address "rt:symbol-view" code-base)))
    (implies (and (symbols-name-setup-pre-p package-name code-base before)
                  (symbols-path-ready-p path code-base target before))
             (symbols-name-setup-frame-p package-name code-base before
                                         (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-name-setup)
                 (:instance symbols-replay-is-advance
                            (path (symbols-name-setup-path package-name)) (base code-base)
                            (cut (symbols-runtime-address "rt:symbol-view" code-base)) (world before)))
           :in-theory (disable symbols-replay symbols-name-setup-path symbols-path-control-p
                               symbols-name-setup-frame-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-package-name-row-path*
  (symbols-code-path *symbols-package-name-entry* '(8 12 16 20)))
(defconst *symbols-package-name-empty-path*
  (symbols-code-path *symbols-package-name-entry* '(8 48 52)))

(defun symbols-package-name-dispatch-path (world)
  (if (equal (proof-world-reg 1 world) 0) *symbols-package-name-empty-path*
    *symbols-package-name-row-path*))

(defun symbols-package-name-dispatch-target (base world)
  (symbols-runtime-address (if (equal (proof-world-reg 1 world) 0) "rt:empty-string"
                             "rt:package-row") base))

(defun symbols-package-name-dispatch-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (+ 8 (symbols-runtime-address *symbols-package-name-entry* base)))
       (< (+ 16 (boymoo-model::a64-sp (proof-world-machine world))) (expt 2 64))))

(defun symbols-package-name-dispatch-frame-p (base before after)
  (let ((header (proof-world-reg 1 before))
        (sp (boymoo-model::a64-sp (proof-world-machine before))))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-package-name-dispatch-target base before))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (if (equal header 0) (+ sp 16) sp))
         (if (equal header 0)
             (and (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                  (equal (proof-world-reg 29 after) (symbols-stack-word 0 before))
                  (equal (proof-world-reg 30 after) (symbols-stack-word 8 before)))
           (and (equal (proof-world-reg 0 after) (symbols-load-register-word (+ header 16) before))
                (equal (proof-world-reg 5 after) (proof-world-reg 0 before))
                (equal (proof-world-reg 30 after)
                       (+ 24 (symbols-runtime-address *symbols-package-name-entry* base)))))
         (proof-register-frame-p 30 '(0 5 29 30) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-replay-package-name-dispatch
   (let* ((path (symbols-package-name-dispatch-path before))
          (after (symbols-replay path before)))
     (implies (symbols-package-name-dispatch-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-package-name-dispatch-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-package-name-dispatch
  (let* ((path (symbols-package-name-dispatch-path before))
         (target (symbols-package-name-dispatch-target code-base before)))
    (implies (and (symbols-package-name-dispatch-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (symbols-package-name-dispatch-frame-p code-base before
                                                    (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-package-name-dispatch)
                 (:instance symbols-replay-is-advance
                            (path (symbols-package-name-dispatch-path before)) (base code-base)
                            (cut (symbols-package-name-dispatch-target code-base before)) (world before)))
           :in-theory (disable symbols-replay symbols-package-name-dispatch-path proof-advance
                               symbols-package-name-dispatch-frame-p symbols-path-control-p
                               symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-intern-entry* "prim:ACL2::INTERN-IN-PACKAGE-OF-SYMBOL")
(defconst *symbols-intern-setup-path* (symbols-code-path *symbols-intern-entry* '(0 4 8 12 16 20)))

(defun symbols-intern-at-p (offset base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (+ offset (symbols-runtime-address *symbols-intern-entry* base)))))

(defun symbols-intern-saved-world (before)
  (let* ((machine (proof-world-machine before))
         (sp (boymoo-model::a64-sp machine))
         (saved (boymoo-model::a64-store 8 (- sp 16) (proof-world-reg 19 before) machine))
         (saved (boymoo-model::a64-store 8 (- sp 8) (proof-world-reg 20 before) saved))
         (saved (boymoo-model::a64-store 8 (- sp 32) (proof-world-reg 21 before) saved))
         (saved (boymoo-model::a64-store 8 (- sp 24) (proof-world-reg 22 before) saved))
         (saved (boymoo-model::a64-store 8 (- sp 48) (proof-world-reg 29 before) saved))
         (saved (boymoo-model::a64-store 8 (- sp 40) (proof-world-reg 30 before) saved)))
    (update-nth 0 saved before)))

(defun symbols-intern-setup-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:symbol-view" base))
       (equal (proof-world-reg 30 after) (+ 24 (symbols-runtime-address *symbols-intern-entry* base)))
       (equal (proof-world-reg 0 after) (proof-world-reg 1 before))
       (equal (proof-world-reg 19 after) (proof-world-reg 0 before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
       (proof-register-frame-p 30 '(0 19 30) before after)
       (symbols-no-memory-or-kernel-change-p (symbols-intern-saved-world before) after)))

(local
 (defthm symbols-replay-intern-setup
   (let ((after (symbols-replay *symbols-intern-setup-path* before)))
     (implies (and (symbols-intern-at-p 0 code-base before)
                   (<= 48 (boymoo-model::a64-sp (proof-world-machine before))))
              (and (symbols-path-control-p *symbols-intern-setup-path* code-base before)
                   (symbols-intern-setup-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-intern-setup
  (implies (and (symbols-intern-at-p 0 code-base before)
                (<= 48 (boymoo-model::a64-sp (proof-world-machine before)))
                (symbols-path-ready-p *symbols-intern-setup-path* code-base
                                      (symbols-runtime-address "rt:symbol-view" code-base) before))
           (symbols-intern-setup-frame-p code-base before
                                         (proof-advance (len *symbols-intern-setup-path*) before)))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-setup)
                 (:instance symbols-replay-is-advance (path *symbols-intern-setup-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:symbol-view" code-base)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p symbols-intern-setup-frame-p
                               proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-intern-designator-reject-path* (symbols-code-path *symbols-intern-entry* '(24)))
(defconst *symbols-intern-designator-accept-path* (symbols-code-path *symbols-intern-entry* '(24 28 32 36)))

(defun symbols-intern-designator-path (world)
  (if (equal (proof-world-reg 1 world) 0) *symbols-intern-designator-reject-path*
    *symbols-intern-designator-accept-path*))

(defun symbols-intern-designator-target (base world)
  (symbols-runtime-address (if (equal (proof-world-reg 1 world) 0) "rt:intern-nil"
                             "rt:string-view") base))

(defun symbols-intern-designator-frame-p (base before after)
  (let ((header (proof-world-reg 1 before)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-intern-designator-target base before))
         (implies (not (equal header 0))
                  (and (equal (proof-world-reg 20 after)
                              (symbols-load-register-word (+ header 16) before))
                       (equal (proof-world-reg 0 after) (proof-world-reg 19 before))
                       (equal (proof-world-reg 30 after)
                              (+ 40 (symbols-runtime-address *symbols-intern-entry* base)))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(0 20 30) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-replay-intern-designator-test
   (let* ((path (symbols-intern-designator-path before))
          (after (symbols-replay path before)))
     (implies (symbols-intern-at-p 24 code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-intern-designator-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-intern-designator-test
  (let ((path (symbols-intern-designator-path before)))
    (implies (and (symbols-intern-at-p 24 code-base before)
                  (symbols-path-ready-p path code-base (symbols-intern-designator-target code-base before)
                                        before))
             (symbols-intern-designator-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-designator-test)
                 (:instance symbols-replay-is-advance (path (symbols-intern-designator-path before))
                            (base code-base) (cut (symbols-intern-designator-target code-base before))
                            (world before)))
           :in-theory (disable symbols-replay symbols-intern-designator-path symbols-path-control-p
                               symbols-intern-designator-frame-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-intern-name-reject-path* (symbols-code-path *symbols-intern-entry* '(40)))
(defconst *symbols-intern-name-accept-path* (symbols-code-path *symbols-intern-entry* '(40 44 48 52 56)))

(defun symbols-intern-name-path (world)
  (if (equal (proof-world-reg 1 world) 0) *symbols-intern-name-reject-path*
    *symbols-intern-name-accept-path*))

(defun symbols-intern-name-target (base world)
  (symbols-runtime-address (if (equal (proof-world-reg 1 world) 0) "rt:intern-nil"
                             "rt:intern-hash") base))

(defun symbols-intern-name-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-intern-name-target base before))
       (implies (not (equal (proof-world-reg 1 before) 0))
                (and (equal (proof-world-reg 21 after) (proof-world-reg 2 before))
                     (equal (proof-world-reg 8 after) (proof-world-reg 1 before))
                     (equal (proof-world-reg 3 after) 0)
                     (equal (proof-world-reg 4 after) 0)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 '(3 4 8 21) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-replay-intern-name-test
   (let* ((path (symbols-intern-name-path before))
          (after (symbols-replay path before)))
     (implies (symbols-intern-at-p 40 code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-intern-name-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-intern-name-test
  (let ((path (symbols-intern-name-path before)))
    (implies (and (symbols-intern-at-p 40 code-base before)
                  (symbols-path-ready-p path code-base (symbols-intern-name-target code-base before)
                                        before))
             (symbols-intern-name-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-name-test)
                 (:instance symbols-replay-is-advance (path (symbols-intern-name-path before)) (base code-base)
                            (cut (symbols-intern-name-target code-base before)) (world before)))
           :in-theory (disable symbols-replay symbols-intern-name-path symbols-path-control-p
                               symbols-intern-name-frame-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-intern-bucket-path*
  (symbols-code-path "rt:intern-bucket" '(0 4 8 12 16 20 24 28 32 36 40 44)))

(defun symbols-intern-combined-hash (world)
  (boymoo-model::a64-unsigned
   64 (+ (proof-world-reg 3 world)
         (boymoo-model::a64-unsigned 64
                                    (* 7919 (symbols-logical-right-shift-bits
                                             (proof-world-reg 20 world) 1))))))

(defun symbols-intern-static-index (world)
  (boymoo-model::a64-unsigned 64 (logand (symbols-intern-combined-hash world) 4095)))

(defun symbols-intern-static-slot (world)
  (let* ((base (proof-heap-base world))
         (reference (symbols-load-register-word (+ base 16) world))
         (first (boymoo-model::a64-unsigned 64 (+ base (boymoo-model::a64-unsigned 64 (+ reference 6)))))
         (offset (boymoo-model::a64-unsigned 64 (* 8 (symbols-intern-static-index world)))))
    (boymoo-model::a64-unsigned 64 (+ first offset))))

(defun symbols-intern-bucket-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:intern-bucket" base))))

(defun symbols-intern-bucket-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-static" base))
       (equal (proof-world-reg 3 after) (symbols-intern-static-index before))
       (equal (proof-world-reg 9 after) (proof-integer-word (symbols-intern-combined-hash before)))
       (equal (proof-world-reg 22 after) (symbols-load-register-word (symbols-intern-static-slot before) before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))
       (proof-register-frame-p 30 '(3 4 5 9 22) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-effect-multiply
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect (list :multiply rd rn rm) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil (* (proof-world-reg rn world) (proof-world-reg rm world))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-left-shift-one
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect
                    (list :bitfield 2 64 rd rn 63 62 #xfffffffffffffffe #xffffffffffffffff) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil (* 2 (proof-world-reg rn world))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect symbols-left-shift-one-from-rotate)))))

(local
 (defthm symbols-replay-intern-bucket
   (let ((after (symbols-replay *symbols-intern-bucket-path* before)))
     (implies (symbols-intern-bucket-pre-p code-base before)
              (and (symbols-path-control-p *symbols-intern-bucket-path* code-base before)
                   (symbols-intern-bucket-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-intern-bucket
  (let ((path *symbols-intern-bucket-path*))
    (implies (and (symbols-intern-bucket-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-runtime-address "rt:intern-static" code-base)
                                        before))
             (symbols-intern-bucket-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-bucket)
                 (:instance symbols-replay-is-advance (path *symbols-intern-bucket-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:intern-static" code-base)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p symbols-intern-bucket-frame-p
                               proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(local
 (defthm symbols-effect-subtract-register
   (implies (and (natp rd) (< rd 31))
            (equal (proof-instruction-effect (list :arithmetic-reg 2 64 rd rn rm 0 0) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil (boymoo-model::a64-unsigned
                                             64 (- (proof-world-reg rn world) (proof-world-reg rm world)))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-word-plus-modulus
                             (x (- (proof-world-reg rn world) (proof-world-reg rm world)))))
            :in-theory (e/d (proof-instruction-effect)
                            (symbols-write-register-already-clips symbols-unsigned-word-plus-modulus))))))

(defun symbols-box-word (address heap)
  (boymoo-model::a64-unsigned 64 (+ 2 (boymoo-model::a64-unsigned 64 (- address heap)))))

(defconst *symbols-intern-publish-path*
  (symbols-code-path "rt:intern-allocate" '(72 76 80 84 88 92 96 100 104 108)))

(defun symbols-intern-publish-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (+ 72 (symbols-runtime-address "rt:intern-allocate" base)))))

(defun symbols-intern-linked-world (before)
  (let* ((entry (proof-world-reg 0 before))
         (table (proof-world-reg 1 before))
         (bucket (proof-world-reg 4 before))
         (head (symbols-load-register-word bucket before))
         (memory (proof-world-machine before))
         (linked (boymoo-model::a64-store 8 (+ entry 24) head memory))
         (entry-word (symbols-box-word entry (proof-heap-base before)))
         (published (boymoo-model::a64-store 8 bucket entry-word linked))
         (count (boymoo-model::a64-load 8 (+ table 8) published))
         (counted (boymoo-model::a64-store 8 (+ table 8)
                                           (boymoo-model::a64-unsigned 64 (+ 2 count)) published)))
    (update-nth 0 counted before)))

(defun symbols-intern-publish-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-return" base))
       (equal (proof-world-reg 0 after) (proof-world-reg 5 before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))
       (proof-register-frame-p 30 '(0 3) before after)
       (symbols-no-memory-or-kernel-change-p (symbols-intern-linked-world before) after)))

(local
 (defthm symbols-word-bytes-are-unsigned
   (equal (boymoo-model::a64-unsigned 64 (boymoo-model::a64-read-bytes 8 address memory))
          (boymoo-model::a64-read-bytes 8 address memory))
   :hints (("Goal"
            :use ((:instance symbols-word-load-fits (machine (list nil 0 0 0 memory))))
            :in-theory (e/d (boymoo-model::a64-load boymoo-model::a64-memory)
                            (boymoo-model::a64-read-bytes))))))

(local
 (defthm symbols-replay-intern-publish
   (let ((after (symbols-replay *symbols-intern-publish-path* before)))
     (implies (symbols-intern-publish-pre-p code-base before)
              (and (symbols-path-control-p *symbols-intern-publish-path* code-base before)
                   (symbols-intern-publish-frame-p code-base before after))))
   :hints (("Goal" :in-theory (e/d (symbols-word-load-fits boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm symbols-run-intern-publish
  (let ((path *symbols-intern-publish-path*))
    (implies (and (symbols-intern-publish-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-runtime-address "rt:intern-return" code-base)
                                        before))
             (symbols-intern-publish-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-publish)
                 (:instance symbols-replay-is-advance (path *symbols-intern-publish-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:intern-return" code-base)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p symbols-intern-publish-frame-p
                               proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-grown-root-path* (symbols-code-path "rt:intern-grown" '(0 4 8 12 16 20)))

(defun symbols-grown-root-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (< (+ 16 (boymoo-model::a64-sp (proof-world-machine world))) (expt 2 64))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:intern-grown" base))))

(defun symbols-grown-root-world (before)
  (let* ((table (proof-world-reg 1 before))
         (base (proof-heap-base before))
         (counted (boymoo-model::a64-store 8 (+ table 8) (proof-world-reg 0 before)
                                           (proof-world-machine before)))
         (published (boymoo-model::a64-store 8 (+ base 24) (symbols-box-word table base) counted)))
    (update-nth 0 published before)))

(defun symbols-grown-root-frame-p (before after)
  (let ((published (symbols-grown-root-world before)))
    (and (not (proof-world-stop after))
         (equal (proof-world-pc after) (symbols-stack-word 8 published))
         (equal (proof-world-reg 30 after) (symbols-stack-word 8 published))
         (equal (proof-world-reg 2 after) (symbols-stack-word 0 published))
         (equal (proof-world-reg 1 after) (symbols-box-word (proof-world-reg 1 before)
                                                           (proof-heap-base before)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (+ 16 (boymoo-model::a64-sp (proof-world-machine before))))
         (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-nzcv (proof-world-machine before)))
         (proof-register-frame-p 30 '(1 2 30) before after)
         (symbols-no-memory-or-kernel-change-p published after))))

(local
 (defthm symbols-replay-grown-root
   (let ((after (symbols-replay *symbols-grown-root-path* before)))
     (implies (symbols-grown-root-pre-p code-base before)
              (and (symbols-path-control-p *symbols-grown-root-path* code-base before)
                   (symbols-grown-root-frame-p before after))))
   :hints (("Goal" :in-theory (e/d (symbols-word-load-fits boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm symbols-run-publish-grown-root
  (let* ((path *symbols-grown-root-path*)
         (target (symbols-stack-word 8 (symbols-grown-root-world before))))
    (implies (and (symbols-grown-root-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (symbols-grown-root-frame-p before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-grown-root)
                 (:instance symbols-replay-is-advance (path *symbols-grown-root-path*) (base code-base)
                            (cut (symbols-stack-word 8 (symbols-grown-root-world before))) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p symbols-grown-root-frame-p
                               proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defun symbols-intern-scan-label (dynamic)
  (if dynamic "rt:intern-dynamic" "rt:intern-static"))

(defun symbols-address-plus-word (base word)
  (boymoo-model::a64-unsigned 64 (+ base word)))

; The fields are the next link, symbol word, cached hash, package
; number and name word. Only dynamic entries have a cached hash.
(defun symbols-intern-fields-at (dynamic link world)
  (let ((base (proof-heap-base world)))
    (if dynamic
        (let* ((entry (symbols-address-plus-word base (boymoo-model::a64-unsigned 64 (+ link 6))))
               (symbol (symbols-load-register-word entry world))
               (payload (symbols-address-plus-word base (boymoo-model::a64-unsigned 64 (+ symbol 6)))))
          (list (symbols-load-register-word (+ entry 16) world)
                symbol
                (symbols-load-register-word (+ entry 8) world)
                (symbols-load-register-word (+ payload 8) world)
                (symbols-load-register-word payload world)))
      (let* ((entry (symbols-address-plus-word base link))
             (pair (symbols-address-plus-word base (symbols-load-register-word entry world)))
             (key (symbols-address-plus-word base (symbols-load-register-word pair world))))
        (list (symbols-load-register-word (+ entry 8) world)
              (symbols-load-register-word (+ pair 8) world)
              nil
              (symbols-load-register-word key world)
              (symbols-load-register-word (+ key 8) world))))))

(defun symbols-intern-scan-fields (dynamic world)
  (symbols-intern-fields-at dynamic (proof-world-reg 22 world) world))

(defun symbols-intern-scan-empty-p (world)
  (equal (proof-world-reg 22 world) *proof-nil*))

(defun symbols-intern-scan-hash-mismatch-p (dynamic world)
  (and dynamic (not (equal (caddr (symbols-intern-scan-fields dynamic world))
                           (proof-world-reg 9 world)))))

(defun symbols-intern-scan-package-match-p (dynamic world)
  (equal (cadddr (symbols-intern-scan-fields dynamic world)) (proof-world-reg 20 world)))

(defun symbols-intern-scan-calls-compare-p (dynamic world)
  (and (not (symbols-intern-scan-empty-p world))
       (not (symbols-intern-scan-hash-mismatch-p dynamic world))
       (symbols-intern-scan-package-match-p dynamic world)))

(defconst *symbols-intern-static-empty-path* (symbols-code-path "rt:intern-static" '(0 4)))
(defconst *symbols-intern-static-next-path*
  (symbols-code-path "rt:intern-static" '(0 4 8 12 16 20 24 28 32 36)))
(defconst *symbols-intern-static-call-path*
  (symbols-code-path "rt:intern-static" '(0 4 8 12 16 20 24 28 32 36 40)))
(defconst *symbols-intern-dynamic-empty-path* (symbols-code-path "rt:intern-dynamic" '(0 4)))
(defconst *symbols-intern-dynamic-hash-miss-path*
  (symbols-code-path "rt:intern-dynamic" '(0 4 8 12 16 20 24 28)))
(defconst *symbols-intern-dynamic-next-path*
  (symbols-code-path "rt:intern-dynamic" '(0 4 8 12 16 20 24 28 32 36 40 44 48)))
(defconst *symbols-intern-dynamic-call-path*
  (symbols-code-path "rt:intern-dynamic" '(0 4 8 12 16 20 24 28 32 36 40 44 48 52)))

(defun symbols-intern-scan-path (dynamic world)
  (cond ((symbols-intern-scan-empty-p world)
         (if dynamic *symbols-intern-dynamic-empty-path* *symbols-intern-static-empty-path*))
        ((symbols-intern-scan-hash-mismatch-p dynamic world) *symbols-intern-dynamic-hash-miss-path*)
        ((symbols-intern-scan-package-match-p dynamic world)
         (if dynamic *symbols-intern-dynamic-call-path* *symbols-intern-static-call-path*))
        (t (if dynamic *symbols-intern-dynamic-next-path* *symbols-intern-static-next-path*))))

(defun symbols-intern-scan-target (dynamic base world)
  (symbols-runtime-address
   (cond ((symbols-intern-scan-empty-p world)
          (if dynamic "rt:intern-create" "rt:intern-dynamic-start"))
         ((symbols-intern-scan-calls-compare-p dynamic world) "rt:intern-name-equal")
         (t (symbols-intern-scan-label dynamic)))
   base))

(defun symbols-intern-scan-start-p (dynamic base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (symbols-runtime-address (symbols-intern-scan-label dynamic) base))))

(defun symbols-intern-scan-call-link (dynamic base)
  (+ (if dynamic 56 44) (symbols-runtime-address (symbols-intern-scan-label dynamic) base)))

(defun symbols-intern-scan-frame-p (dynamic base before after)
  (let ((fields (symbols-intern-scan-fields dynamic before)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-intern-scan-target dynamic base before))
         (equal (proof-world-reg 22 after) (if (symbols-intern-scan-empty-p before) *proof-nil* (car fields)))
         (implies (not (symbols-intern-scan-empty-p before))
                  (equal (proof-world-reg 5 after) (cadr fields)))
         (implies (symbols-intern-scan-calls-compare-p dynamic before)
                  (and (equal (proof-world-reg 0 after) (car (cddddr fields)))
                       (equal (proof-world-reg 30 after) (symbols-intern-scan-call-link dynamic base))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(0 4 5 6 22 30) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-loaded-word-is-natural
   (natp (boymoo-model::a64-load 8 address machine))
   :hints (("Goal" :use ((:instance symbols-load-width (count 8)))))
   :rule-classes :type-prescription))

(local
 (defthm symbols-loaded-word-is-bounded
   (< (boymoo-model::a64-load 8 address machine) (expt 2 64))
   :hints (("Goal" :use ((:instance symbols-load-width (count 8)))))
   :rule-classes :linear))

(local
 (defthm symbols-replay-intern-scan
   (let* ((path (symbols-intern-scan-path dynamic before))
          (after (symbols-replay path before)))
     (implies (symbols-intern-scan-start-p dynamic code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-intern-scan-frame-p dynamic code-base before after))))
   :hints (("Goal" :cases ((not dynamic))
                   :in-theory (e/d (symbols-word-load-fits)
                                   (boymoo-model::a64-condition boymoo-model::a64-result-flags))))
   :rule-classes nil))

(defthm symbols-run-intern-scan-iteration
  (let ((path (symbols-intern-scan-path dynamic before)))
    (implies (and (symbols-intern-scan-start-p dynamic code-base before)
                  (symbols-path-ready-p path code-base nil before))
             (symbols-intern-scan-frame-p dynamic code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-scan)
                 (:instance symbols-replay-is-advance
                            (path (symbols-intern-scan-path dynamic before))
                            (base code-base) (cut nil) (world before)))
           :in-theory (disable symbols-replay symbols-intern-scan-path symbols-path-control-p
                               symbols-intern-scan-frame-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-intern-name-length-miss-path*
  (symbols-code-path "rt:intern-name-equal" '(0 4 8 12 16 20)))
(defconst *symbols-intern-name-compare-path*
  (symbols-code-path "rt:intern-name-equal" '(0 4 8 12 16 20 24 28 32)))
(defconst *symbols-bytes-differ-path* (symbols-code-path "rt:bytes-differ" '(0 4)))

(defun symbols-intern-candidate-string (world)
  (symbols-box-address (proof-world-reg 0 world) (proof-heap-base world)))

(defun symbols-intern-candidate-length (world)
  (symbols-logical-right-shift-bits
   (symbols-load-register-word (symbols-intern-candidate-string world) world) 8))

(defun symbols-intern-name-length-miss-p (world)
  (not (equal (symbols-intern-candidate-length world) (proof-world-reg 21 world))))

(defun symbols-intern-name-equality-path (world)
  (if (symbols-intern-name-length-miss-p world)
      *symbols-intern-name-length-miss-path*
    *symbols-intern-name-compare-path*))

(defun symbols-intern-name-equality-target (base world)
  (symbols-runtime-address (if (symbols-intern-name-length-miss-p world)
                               "rt:bytes-differ" "rt:equal-bytes") base))

(defun symbols-intern-name-equality-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:intern-name-equal" base))))

(defun symbols-intern-name-equality-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-intern-name-equality-target base before))
       (implies (not (symbols-intern-name-length-miss-p before))
                (and (equal (proof-world-reg 0 after)
                            (boymoo-model::a64-unsigned 64 (+ 8 (symbols-intern-candidate-string before))))
                     (equal (proof-world-reg 1 after) (proof-world-reg 8 before))
                     (equal (proof-world-reg 2 after) (proof-world-reg 21 before))))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 '(0 1 2) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-replay-intern-name-equality
   (let* ((path (symbols-intern-name-equality-path before))
          (after (symbols-replay path before)))
     (implies (symbols-intern-name-equality-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-intern-name-equality-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-intern-name-equality
  (let ((path (symbols-intern-name-equality-path before)))
    (implies (and (symbols-intern-name-equality-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-intern-name-equality-target code-base before)
                                        before))
             (symbols-intern-name-equality-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-name-equality)
                 (:instance symbols-replay-is-advance (path (symbols-intern-name-equality-path before))
                            (base code-base) (cut (symbols-intern-name-equality-target code-base before))
                            (world before)))
           :in-theory (disable symbols-replay symbols-intern-name-equality-path symbols-path-control-p
                               symbols-intern-name-equality-frame-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(local
 (defthm symbols-replay-bytes-differ
   (let ((after (symbols-replay *symbols-bytes-differ-path* before)))
     (implies (and (symbols-runtime-base-p code-base)
                   (not (proof-world-stop before))
                   (not (eq (car (proof-world-machine before)) :svc))
                   (equal (proof-world-pc before) (symbols-runtime-address "rt:bytes-differ" code-base)))
              (and (symbols-path-control-p *symbols-bytes-differ-path* code-base before)
                   (proof-frame-return-p '(0) nil before after)
                   (not (eq (car (proof-world-machine after)) :svc))
                   (equal (proof-world-reg 0 after) 0)
                   (symbols-no-memory-or-kernel-change-p before after))))
   :rule-classes nil))

(defthm symbols-run-bytes-differ
  (let* ((path *symbols-bytes-differ-path*)
         (after (proof-advance (len path) before)))
    (implies (and (symbols-runtime-base-p code-base)
                  (not (proof-world-stop before))
                  (not (eq (car (proof-world-machine before)) :svc))
                  (equal (proof-world-pc before) (symbols-runtime-address "rt:bytes-differ" code-base))
                  (symbols-path-ready-p path code-base (proof-world-reg 30 before) before))
             (and (proof-frame-return-p '(0) nil before after)
                  (not (eq (car (proof-world-machine after)) :svc))
                  (equal (proof-world-reg 0 after) 0)
                  (symbols-no-memory-or-kernel-change-p before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-bytes-differ)
                 (:instance symbols-replay-is-advance (path *symbols-bytes-differ-path*)
                            (base code-base) (cut (proof-world-reg 30 before)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-intern-static-match-path* (symbols-code-path "rt:intern-static" '(44 48 52)))
(defconst *symbols-intern-static-nomatch-path* (symbols-code-path "rt:intern-static" '(44)))
(defconst *symbols-intern-dynamic-match-path* (symbols-code-path "rt:intern-dynamic" '(56 60 64)))
(defconst *symbols-intern-dynamic-nomatch-path* (symbols-code-path "rt:intern-dynamic" '(56)))

(defun symbols-intern-match-path (dynamic before)
  (if (equal (proof-world-reg 0 before) 0)
      (if dynamic *symbols-intern-dynamic-nomatch-path* *symbols-intern-static-nomatch-path*)
    (if dynamic *symbols-intern-dynamic-match-path* *symbols-intern-static-match-path*)))

(defun symbols-intern-match-target (dynamic base before)
  (symbols-runtime-address (if (equal (proof-world-reg 0 before) 0) (symbols-intern-scan-label dynamic)
                             "rt:intern-return") base))

(defun symbols-intern-match-pre-p (dynamic base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (equal (proof-world-pc before) (symbols-intern-scan-call-link dynamic base))))

(defun symbols-intern-match-frame-p (dynamic base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-intern-match-target dynamic base before))
       (equal (proof-world-reg 0 after)
              (if (equal (proof-world-reg 0 before) 0) 0 (proof-world-reg 5 before)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 '(0) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-replay-intern-match
   (let* ((path (symbols-intern-match-path dynamic before))
          (after (symbols-replay path before)))
     (implies (symbols-intern-match-pre-p dynamic code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-intern-match-frame-p dynamic code-base before after))))
   :rule-classes nil))

(defthm symbols-run-intern-match
  (let ((path (symbols-intern-match-path dynamic before)))
    (implies (and (symbols-intern-match-pre-p dynamic code-base before)
                  (symbols-path-ready-p path code-base (symbols-intern-match-target dynamic code-base before)
                                        before))
             (symbols-intern-match-frame-p dynamic code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-match)
                 (:instance symbols-replay-is-advance (path (symbols-intern-match-path dynamic before))
                            (base code-base) (cut (symbols-intern-match-target dynamic code-base before))
                            (world before)))
           :in-theory (disable symbols-replay symbols-intern-match-path symbols-path-control-p
                               symbols-intern-match-frame-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-intern-dynamic-uninitialized-path*
  (symbols-code-path "rt:intern-dynamic-start" '(0 4 8)))
(defconst *symbols-intern-dynamic-call-bucket-path*
  (symbols-code-path "rt:intern-dynamic-start" '(0 4 8 12 16 20)))
(defconst *symbols-intern-dynamic-head-path*
  (symbols-code-path "rt:intern-dynamic-start" '(24)))

(defun symbols-intern-dynamic-root-word (world)
  (symbols-load-register-word (+ (proof-heap-base world) 24) world))

(defun symbols-intern-dynamic-root-nil-p (world)
  (equal (symbols-intern-dynamic-root-word world) *proof-nil*))

(defun symbols-intern-dynamic-start-path (world)
  (if (symbols-intern-dynamic-root-nil-p world) *symbols-intern-dynamic-uninitialized-path*
    *symbols-intern-dynamic-call-bucket-path*))

(defun symbols-intern-dynamic-start-target (base world)
  (symbols-runtime-address (if (symbols-intern-dynamic-root-nil-p world) "rt:intern-create"
                             "rt:intern-bucket-address") base))

(defun symbols-intern-dynamic-start-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:intern-dynamic-start" base))))

(defun symbols-intern-dynamic-start-frame-p (base before after)
  (let ((nil-root (symbols-intern-dynamic-root-nil-p before))
        (reference (symbols-intern-dynamic-root-word before)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-intern-dynamic-start-target base before))
         (equal (proof-world-reg 1 after)
                (if nil-root reference (symbols-box-address reference (proof-heap-base before))))
         (implies (not nil-root)
                  (equal (proof-world-reg 30 after)
                         (+ 24 (symbols-runtime-address "rt:intern-dynamic-start" base))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(1 30) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-replay-intern-dynamic-start
   (let* ((path (symbols-intern-dynamic-start-path before))
          (after (symbols-replay path before)))
     (implies (symbols-intern-dynamic-start-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-intern-dynamic-start-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-intern-dynamic-start
  (let ((path (symbols-intern-dynamic-start-path before)))
    (implies (and (symbols-intern-dynamic-start-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-intern-dynamic-start-target code-base before)
                                        before))
             (symbols-intern-dynamic-start-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-dynamic-start)
                 (:instance symbols-replay-is-advance (path (symbols-intern-dynamic-start-path before))
                            (base code-base) (cut (symbols-intern-dynamic-start-target code-base before))
                            (world before)))
           :in-theory (disable symbols-replay symbols-intern-dynamic-start-path symbols-path-control-p
                               symbols-intern-dynamic-start-frame-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defun symbols-intern-dynamic-head-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (+ 24 (symbols-runtime-address "rt:intern-dynamic-start" base)))))

(local
 (defthm symbols-replay-intern-dynamic-head
   (let ((after (symbols-replay *symbols-intern-dynamic-head-path* before)))
     (implies (symbols-intern-dynamic-head-pre-p code-base before)
              (and (symbols-path-control-p *symbols-intern-dynamic-head-path* code-base before)
                   (not (proof-world-stop after))
                   (not (eq (car (proof-world-machine after)) :svc))
                   (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-dynamic" code-base))
                   (equal (proof-world-reg 22 after)
                          (symbols-load-register-word (proof-world-reg 4 before) before))
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine before)))
                   (proof-register-frame-p 30 '(22) before after)
                   (symbols-no-memory-or-kernel-change-p before after))))
   :rule-classes nil))

(defthm symbols-run-intern-dynamic-head
  (let* ((path *symbols-intern-dynamic-head-path*)
         (after (proof-advance (len path) before)))
    (implies (and (symbols-intern-dynamic-head-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-runtime-address "rt:intern-dynamic" code-base)
                                        before))
             (and (not (proof-world-stop after))
                  (not (eq (car (proof-world-machine after)) :svc))
                  (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-dynamic" code-base))
                  (equal (proof-world-reg 22 after)
                         (symbols-load-register-word (proof-world-reg 4 before) before))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine before)))
                  (proof-register-frame-p 30 '(22) before after)
                  (symbols-no-memory-or-kernel-change-p before after))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-dynamic-head)
                 (:instance symbols-replay-is-advance (path *symbols-intern-dynamic-head-path*)
                            (base code-base) (cut (symbols-runtime-address "rt:intern-dynamic" code-base))
                            (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(local
 (defthm symbols-effect-pair-store-at-offset
   (implies (and (natp source) (< source 31)
                 (not (eq (car (proof-world-machine world)) :svc)))
            (let* ((address (+ (proof-world-reg source world) offset))
                   (left (boymoo-model::a64-store 8 address (proof-world-reg first world)
                                                   (symbols-next-pc world)))
                   (right (boymoo-model::a64-store 8 (+ address 8) (proof-world-reg second world) left)))
              (equal (proof-instruction-effect (list :pair nil source first second :offset offset) world)
                     (update-nth 0 right world))))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-subtract-eight
   (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31))
            (equal (proof-instruction-effect (list :arithmetic-imm 2 64 rd rn 8) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 t (boymoo-model::a64-unsigned 64 (- (proof-world-reg rn world) 8))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-word-plus-modulus (x (- (proof-world-reg rn world) 8))))
            :in-theory (e/d (proof-instruction-effect)
                            (symbols-write-register-already-clips symbols-unsigned-word-plus-modulus))))))

(defconst *symbols-intern-initialize-path*
  (symbols-code-path "rt:intern-allocate" '(8 12 16 20 24 28 32 36 40 44 48 52 56 60 64 68)))

(defun symbols-intern-popped-stack-top (before)
  (boymoo-model::a64-unsigned 64 (- (proof-world-reg 25 before) 8)))

(defun symbols-intern-entry-location (before)
  (boymoo-model::a64-unsigned 64 (+ 24 (proof-world-reg 0 before))))

(defun symbols-intern-initialized-world (before)
  (let* ((symbol (proof-world-reg 0 before))
         (entry (symbols-intern-entry-location before))
         (name (symbols-load-register-word (symbols-intern-popped-stack-top before) before))
         (symbol-word (symbols-box-word symbol (proof-heap-base before)))
         (memory (proof-world-machine before))
         (memory (boymoo-model::a64-store 8 symbol 4098 memory))
         (memory (boymoo-model::a64-store 8 (+ symbol 8) name memory))
         (memory (boymoo-model::a64-store 8 (+ symbol 16) (proof-world-reg 20 before) memory))
         (memory (boymoo-model::a64-store 8 entry 6150 memory))
         (memory (boymoo-model::a64-store 8 (+ entry 8) symbol-word memory))
         (memory (boymoo-model::a64-store 8 (+ entry 16) (proof-world-reg 22 before) memory)))
    (update-nth 0 memory before)))

(defun symbols-intern-initialize-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (+ 8 (symbols-runtime-address "rt:intern-allocate" base)))))

(defun symbols-intern-initialize-frame-p (base before after)
  (let* ((initialized (symbols-intern-initialized-world before))
         (heap (proof-heap-base before))
         (table (symbols-box-address (symbols-load-register-word (+ heap 24) initialized) heap)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-bucket-address" base))
         (equal (proof-world-reg 0 after) (symbols-intern-entry-location before))
         (equal (proof-world-reg 1 after) table)
         (equal (proof-world-reg 5 after) (symbols-box-word (proof-world-reg 0 before) heap))
         (equal (proof-world-reg 9 after) (proof-world-reg 22 before))
         (equal (proof-world-reg 25 after) (symbols-intern-popped-stack-top before))
         (equal (proof-world-reg 30 after) (+ 72 (symbols-runtime-address "rt:intern-allocate" base)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (equal (boymoo-model::a64-nzcv (proof-world-machine after))
                (boymoo-model::a64-nzcv (proof-world-machine before)))
         (proof-register-frame-p 30 '(0 1 2 5 9 25 30) before after)
         (symbols-no-memory-or-kernel-change-p initialized after))))

(local
 (defthm symbols-replay-intern-initialize
   (let ((after (symbols-replay *symbols-intern-initialize-path* before)))
     (implies (symbols-intern-initialize-pre-p code-base before)
              (and (symbols-path-control-p *symbols-intern-initialize-path* code-base before)
                   (symbols-intern-initialize-frame-p code-base before after))))
   :hints (("Goal" :in-theory (e/d (symbols-word-load-fits boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm symbols-run-intern-initialize
  (let ((path *symbols-intern-initialize-path*))
    (implies (and (symbols-intern-initialize-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-runtime-address "rt:intern-bucket-address" code-base)
                                        before))
             (symbols-intern-initialize-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-initialize)
                 (:instance symbols-replay-is-advance (path *symbols-intern-initialize-path*) (base code-base)
                            (cut (symbols-runtime-address "rt:intern-bucket-address" code-base)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p symbols-intern-initialize-frame-p
                               proof-advance symbols-path-ready-p)))
  :rule-classes nil)

(defconst *symbols-clear-bucket-path*
  (symbols-code-path "rt:intern-clear-buckets" '(0 4 8 12)))

(defun symbols-clear-bucket-target (base before)
  (+ (symbols-runtime-address "rt:intern-clear-buckets" base)
     (if (< (+ 8 (proof-world-reg 4 before)) (proof-world-reg 2 before)) 0 16)))

(defun symbols-clear-bucket-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (equal (proof-world-pc before) (symbols-runtime-address "rt:intern-clear-buckets" base))
       (< (+ 8 (proof-world-reg 4 before)) (expt 2 64))))

(defun symbols-clear-bucket-memory (before)
  (update-nth 0 (boymoo-model::a64-store 8 (proof-world-reg 4 before) (proof-world-reg 0 before)
                                        (proof-world-machine before))
              before))

(defun symbols-clear-bucket-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-clear-bucket-target base before))
       (equal (proof-world-reg 4 after) (+ (proof-world-reg 4 before) 8))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 '(4) before after)
       (symbols-no-memory-or-kernel-change-p (symbols-clear-bucket-memory before) after)))

(local
 (defthm symbols-replay-clear-bucket
   (let ((after (symbols-replay *symbols-clear-bucket-path* before)))
     (implies (symbols-clear-bucket-pre-p code-base before)
              (and (symbols-path-control-p *symbols-clear-bucket-path* code-base before)
                   (symbols-clear-bucket-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-clear-bucket
  (implies (and (symbols-clear-bucket-pre-p code-base before)
                (symbols-path-ready-p *symbols-clear-bucket-path* code-base nil before))
           (symbols-clear-bucket-frame-p code-base before (proof-advance (len *symbols-clear-bucket-path*) before)))
  :hints (("Goal"
           :use ((:instance symbols-replay-clear-bucket)
                 (:instance symbols-replay-is-advance (path *symbols-clear-bucket-path*)
                            (base code-base) (cut nil) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p
                               symbols-clear-bucket-frame-p)))
  :rule-classes nil)

(defconst *symbols-rehash-last-bucket-path* (symbols-code-path "rt:intern-rehash-bucket" '(0 4)))
(defconst *symbols-rehash-load-bucket-path* (symbols-code-path "rt:intern-rehash-bucket" '(0 4 8 12)))

(defun symbols-rehash-buckets-exhausted-p (before)
  (<= (proof-world-reg 7 before) (proof-world-reg 6 before)))

(defun symbols-rehash-bucket-path (before)
  (if (symbols-rehash-buckets-exhausted-p before) *symbols-rehash-last-bucket-path* *symbols-rehash-load-bucket-path*))

(defun symbols-rehash-bucket-target (base before)
  (symbols-runtime-address (if (symbols-rehash-buckets-exhausted-p before) "rt:intern-grown"
                              "rt:intern-rehash-entry") base))

(defun symbols-rehash-bucket-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (equal (proof-world-pc before) (symbols-runtime-address "rt:intern-rehash-bucket" base))
       (implies (not (symbols-rehash-buckets-exhausted-p before))
                (< (+ 8 (proof-world-reg 6 before)) (expt 2 64)))))

(defun symbols-rehash-bucket-frame-p (base before after)
  (let ((exhausted (symbols-rehash-buckets-exhausted-p before)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-rehash-bucket-target base before))
         (equal (proof-world-reg 6 after) (if exhausted (proof-world-reg 6 before) (+ 8 (proof-world-reg 6 before))))
         (equal (proof-world-reg 5 after)
                (if exhausted (proof-world-reg 5 before) (symbols-load-register-word (proof-world-reg 6 before) before)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(5 6) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-replay-rehash-bucket-step
   (let* ((path (symbols-rehash-bucket-path before))
          (after (symbols-replay path before)))
     (implies (symbols-rehash-bucket-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-rehash-bucket-frame-p code-base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-rehash-bucket-step
  (let ((path (symbols-rehash-bucket-path before)))
    (implies (and (symbols-rehash-bucket-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-rehash-bucket-target code-base before) before))
             (symbols-rehash-bucket-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-rehash-bucket-step)
                 (:instance symbols-replay-is-advance (path (symbols-rehash-bucket-path before)) (base code-base)
                            (cut (symbols-rehash-bucket-target code-base before)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p
                               symbols-rehash-bucket-path symbols-rehash-bucket-frame-p)))
  :rule-classes nil)

(defconst *symbols-intern-ensure-stack-path* (symbols-code-path "rt:intern-create" '(0 4 8)))
(defconst *symbols-intern-allocate-call-path* (symbols-code-path "rt:intern-allocate" '(0 4)))

(defun symbols-intern-ensure-stack-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (equal (proof-world-pc before) (symbols-runtime-address "rt:intern-create" base))
       (< (+ 8 (proof-world-reg 25 before)) (expt 2 64))))

(defun symbols-intern-ensure-stack-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:ensure-stack" base))
       (equal (proof-world-reg 30 after) (+ 12 (symbols-runtime-address "rt:intern-create" base)))
       (equal (proof-world-reg 8 after) (+ 8 (proof-world-reg 25 before)))
       (equal (proof-world-reg 22 after) (proof-world-reg 9 before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))
       (proof-register-frame-p 30 '(8 22 30) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-replay-intern-ensure-stack
   (let ((after (symbols-replay *symbols-intern-ensure-stack-path* before)))
     (implies (symbols-intern-ensure-stack-pre-p code-base before)
              (and (symbols-path-control-p *symbols-intern-ensure-stack-path* code-base before)
                   (symbols-intern-ensure-stack-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-intern-ensure-stack-call
  (let ((path *symbols-intern-ensure-stack-path*)
        (target (symbols-runtime-address "rt:ensure-stack" code-base)))
    (implies (and (symbols-intern-ensure-stack-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (symbols-intern-ensure-stack-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-ensure-stack)
                 (:instance symbols-replay-is-advance (path *symbols-intern-ensure-stack-path*)
                            (base code-base) (cut (symbols-runtime-address "rt:ensure-stack" code-base)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p
                               symbols-intern-ensure-stack-frame-p)))
  :rule-classes nil)

(defun symbols-intern-allocate-call-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (equal (proof-world-pc before) (symbols-runtime-address "rt:intern-allocate" base))))

(defun symbols-intern-allocate-call-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:alloc" base))
       (equal (proof-world-reg 30 after) (+ 8 (symbols-runtime-address "rt:intern-allocate" base)))
       (equal (proof-world-reg 0 after) 56)
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))
       (proof-register-frame-p 30 '(0 30) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-replay-intern-allocate-call
   (let ((after (symbols-replay *symbols-intern-allocate-call-path* before)))
     (implies (symbols-intern-allocate-call-pre-p code-base before)
              (and (symbols-path-control-p *symbols-intern-allocate-call-path* code-base before)
                   (symbols-intern-allocate-call-frame-p code-base before after))))
   :rule-classes nil))

(defthm symbols-run-intern-allocate-call
  (let ((path *symbols-intern-allocate-call-path*)
        (target (symbols-runtime-address "rt:alloc" code-base)))
    (implies (and (symbols-intern-allocate-call-pre-p code-base before)
                  (symbols-path-ready-p path code-base target before))
             (symbols-intern-allocate-call-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-allocate-call)
                 (:instance symbols-replay-is-advance (path *symbols-intern-allocate-call-path*)
                            (base code-base) (cut (symbols-runtime-address "rt:alloc" code-base)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p
                               symbols-intern-allocate-call-frame-p)))
  :rule-classes nil)

(defconst *symbols-intern-root-name-without-table-path*
  (symbols-code-path "rt:intern-create" '(12 16 20 24 28 32)))

(defconst *symbols-intern-root-name-with-table-path*
  (symbols-code-path "rt:intern-create" '(12 16 20 24 28 32 36 40 44 48 52 56 60 64)))

(defun symbols-intern-rooted-name-world (before)
  (update-nth 0 (boymoo-model::a64-store 8 (proof-stack-top before) (proof-world-reg 19 before)
                                        (proof-world-machine before)) before))

(defun symbols-intern-name-root-table-word (before)
  (symbols-load-register-word (+ (proof-heap-base before) 24) (symbols-intern-rooted-name-world before)))

(defun symbols-intern-name-root-table-address (before)
  (symbols-box-address (symbols-intern-name-root-table-word before) (proof-heap-base before)))

(defun symbols-intern-name-root-capacity (before)
  (let* ((memory (symbols-intern-rooted-name-world before))
         (header (symbols-load-register-word (symbols-intern-name-root-table-address before) memory)))
    (boymoo-model::a64-unsigned 64 (- (symbols-logical-right-shift-bits header 11) 1))))

(defun symbols-intern-name-root-count (before)
  (let* ((memory (symbols-intern-rooted-name-world before))
         (count (symbols-load-register-word (+ (symbols-intern-name-root-table-address before) 8) memory)))
    (symbols-logical-right-shift-bits count 1)))

(defun symbols-intern-root-name-path (before)
  (if (equal (symbols-intern-name-root-table-word before) *proof-nil*)
      *symbols-intern-root-name-without-table-path*
    *symbols-intern-root-name-with-table-path*))

(defun symbols-intern-root-name-target (base before)
  (symbols-runtime-address
   (if (and (not (equal (symbols-intern-name-root-table-word before) *proof-nil*))
            (< (symbols-intern-name-root-count before) (symbols-intern-name-root-capacity before)))
       "rt:intern-allocate"
     "rt:intern-grow")
   base))

(defun symbols-intern-root-name-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (equal (proof-world-pc before) (+ 12 (symbols-runtime-address "rt:intern-create" base)))
       (< (+ 8 (proof-stack-top before)) (expt 2 64))))

(defun symbols-intern-root-name-frame-p (base before after)
  (let ((nil-table (equal (symbols-intern-name-root-table-word before) *proof-nil*)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-intern-root-name-target base before))
         (equal (proof-world-reg 0 after) (if nil-table 0 (symbols-intern-name-root-capacity before)))
         (equal (proof-world-reg 1 after) (if nil-table *proof-nil* (symbols-intern-name-root-table-address before)))
         (implies (not nil-table) (equal (proof-world-reg 2 after) (symbols-intern-name-root-count before)))
         (equal (proof-stack-top after) (+ 8 (proof-stack-top before)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(0 1 2 25) before after)
         (symbols-no-memory-or-kernel-change-p (symbols-intern-rooted-name-world before) after))))

(local
 (defthm symbols-effect-subtract-one
   (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31))
            (equal (proof-instruction-effect (list :arithmetic-imm 2 64 rd rn 1) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 t (boymoo-model::a64-unsigned 64 (- (proof-world-reg rn world) 1))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-word-plus-modulus (x (- (proof-world-reg rn world) 1))))
            :in-theory (e/d (proof-instruction-effect)
                            (symbols-write-register-already-clips symbols-unsigned-word-plus-modulus))))))

(local
 (defthm symbols-load-through-store-of-pc
   (equal (boymoo-model::a64-load width address
                                  (boymoo-model::a64-store 8 slot word (boymoo-model::a64-set-pc pc machine)))
          (boymoo-model::a64-load width address
                                  (boymoo-model::a64-store 8 slot word machine)))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-load)
                                   (boymoo-model::a64-read-bytes))))))

(local
 (defthm symbols-replay-intern-root-name
   (let* ((path (symbols-intern-root-name-path before))
          (after (symbols-replay path before)))
     (implies (symbols-intern-root-name-pre-p code-base before)
              (and (symbols-path-control-p path code-base before)
                   (symbols-intern-root-name-frame-p code-base before after))))
   :hints (("Goal" :in-theory (e/d (proof-stack-top symbols-word-load-fits)
                                   (boymoo-model::a64-load boymoo-model::a64-condition
                                    boymoo-model::a64-result-flags))))
   :rule-classes nil))

(defthm symbols-run-intern-root-name
  (let ((path (symbols-intern-root-name-path before)))
    (implies (and (symbols-intern-root-name-pre-p code-base before)
                  (symbols-path-ready-p path code-base (symbols-intern-root-name-target code-base before) before))
             (symbols-intern-root-name-frame-p code-base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-root-name)
                 (:instance symbols-replay-is-advance (path (symbols-intern-root-name-path before))
                            (base code-base) (cut (symbols-intern-root-name-target code-base before)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p
                               symbols-intern-root-name-frame-p symbols-intern-root-name-path)))
  :rule-classes nil)

(defconst *symbols-intern-grow-call-path* (symbols-code-path "rt:intern-grow" '(0)))
(defconst *symbols-grow-allocation-path*
  (symbols-code-path "rt:intern-grow-table" '(0 4 8 12 16 20 24 28)))
(defconst *symbols-grow-header-path*
  (symbols-code-path "rt:intern-grow-table" '(32 36 40 44 48 52 56 60 64)))

(local
 (defthm symbols-rotation-without-high-bits
   (implies (and (member-equal amount '(3 8)) (natp word)
                 (< word (expt 2 (- 64 amount))))
            (equal (boymoo-model::a64-ror 64 word (- 64 amount))
                   (* (expt 2 amount) word)))
   :hints (("Goal" :cases ((equal amount 3))
                   :use ((:instance symbols-floor-of-decomposition
                                    (q 0) (divisor 1)
                                    (r (* word (/ (expt 2 (- 64 amount)))))))
                   :in-theory (e/d (boymoo-model::a64-ror ash)
                                   (floor boymoo-model::a64-unsigned
                                    acl2::binary-logior symbols-floor-of-decomposition))))))

(local
 (defthm symbols-left-shift-without-high-bits
   (implies (and (member-equal amount '(3 8)) (natp word)
                 (< word (expt 2 (- 64 amount))))
            (equal (logand (logand (boymoo-model::a64-ror 64 word (- 64 amount))
                                   (- (expt 2 64) (expt 2 amount)))
                           (1- (expt 2 64)))
                   (* (expt 2 amount) word)))
   :hints (("Goal" :cases ((equal amount 3))
                   :use ((:instance symbols-and-of-joined-fields
                                    (width amount) (low-left 0) (low-right 0) (high-left word)
                                    (high-right (1- (expt 2 (- 64 amount)))))
                         (:instance symbols-mask-is-unsigned
                                    (width (- 64 amount)) (value word))
                         (:instance symbols-mask-is-unsigned
                                    (width 64) (value (* (expt 2 amount) word))))
                   :in-theory (disable boymoo-model::a64-ror boymoo-model::a64-unsigned
                                       symbols-and-of-joined-fields
                                       acl2::binary-logand)))))

(local
 (defthm symbols-effect-left-shift-three
   (implies (and (natp rd) (< rd 31) (< (proof-world-reg rn world) (expt 2 61)))
            (equal (proof-instruction-effect
                    (list :bitfield 2 64 rd rn 61 60 #xfffffffffffffff8 #xffffffffffffffff) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil (* 8 (proof-world-reg rn world))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :use ((:instance symbols-left-shift-without-high-bits
                                    (amount 3) (word (proof-world-reg rn world))))
                   :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-left-shift-eight
   (implies (and (natp rd) (< rd 31) (< (proof-world-reg rn world) (expt 2 56)))
            (equal (proof-instruction-effect
                    (list :bitfield 2 64 rd rn 56 55 #xffffffffffffff00 #xffffffffffffffff) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil (* 256 (proof-world-reg rn world))
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :use ((:instance symbols-left-shift-without-high-bits
                                    (amount 8) (word (proof-world-reg rn world))))
                   :in-theory (enable proof-instruction-effect)))))

(local
 (defthm symbols-effect-select-word
   (implies (and (natp rd) (< rd 31) (not (eq (car (proof-world-machine world)) :svc)))
            (equal (proof-instruction-effect (list :select 64 rd yes no condition nil) world)
                   (update-nth 0 (boymoo-model::a64-write-reg
                                  rd 64 nil
                                  (proof-world-reg
                                   (if (boymoo-model::a64-condition
                                        condition (boymoo-model::a64-nzcv (proof-world-machine world)))
                                       yes no)
                                   world)
                                  (symbols-next-pc world))
                               world)))
   :hints (("Goal" :in-theory (enable proof-instruction-effect)))))

(defun symbols-grow-call-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:intern-grow" base))))

(defun symbols-grow-call-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-grow-table" base))
       (equal (proof-world-reg 30 after) (symbols-runtime-address "rt:intern-allocate" base))
       (equal (boymoo-model::a64-sp (proof-world-machine before))
              (boymoo-model::a64-sp (proof-world-machine after)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine before))
              (boymoo-model::a64-nzcv (proof-world-machine after)))
       (proof-register-frame-p 30 '(30) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-replay-intern-grow-call
   (let ((after (symbols-replay *symbols-intern-grow-call-path* before)))
     (implies (symbols-grow-call-pre-p base before)
              (and (symbols-path-control-p *symbols-intern-grow-call-path* base before)
                   (symbols-grow-call-frame-p base before after))))
   :rule-classes nil))

(defthm symbols-run-intern-grow-call
  (let ((path *symbols-intern-grow-call-path*)
        (target (symbols-runtime-address "rt:intern-grow-table" base)))
    (implies (and (symbols-grow-call-pre-p base before)
                  (symbols-path-ready-p path base target before))
             (symbols-grow-call-frame-p base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-intern-grow-call)
                 (:instance symbols-replay-is-advance (path *symbols-intern-grow-call-path*)
                            (cut (symbols-runtime-address "rt:intern-grow-table" base)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p
                               symbols-grow-call-frame-p)))
  :rule-classes nil)

(defun symbols-grow-bucket-count (old-count)
  (if (equal old-count 0) 16 (* 2 old-count)))

(defun symbols-grow-allocation-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (<= 16 (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:intern-grow-table" base))
       (< (+ 16 (* 8 (symbols-grow-bucket-count (proof-world-reg 0 world)))) (expt 2 64))))

(defun symbols-grow-allocation-saves (before)
  (let* ((machine (proof-world-machine before))
         (sp (boymoo-model::a64-sp machine))
         (bucket-bytes (* 8 (symbols-grow-bucket-count (proof-world-reg 0 before))))
         (saved (boymoo-model::a64-store 8 (- sp 16) bucket-bytes machine))
         (saved (boymoo-model::a64-store 8 (- sp 8) (proof-world-reg 30 before) saved)))
    (update-nth 0 saved before)))

(defun symbols-grow-allocation-frame-p (base before after)
  (let ((bucket-bytes (* 8 (symbols-grow-bucket-count (proof-world-reg 0 before)))))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-runtime-address "rt:alloc" base))
         (equal (proof-world-reg 30 after) (+ 32 (symbols-runtime-address "rt:intern-grow-table" base)))
         (equal (proof-world-reg 0 after) (+ 16 bucket-bytes))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
         (proof-register-frame-p 30 '(0 2 3 30) before after)
         (symbols-no-memory-or-kernel-change-p (symbols-grow-allocation-saves before) after))))

(local
 (defthm symbols-replay-grow-allocation
   (let ((after (symbols-replay *symbols-grow-allocation-path* before)))
     (implies (symbols-grow-allocation-pre-p base before)
              (and (symbols-path-control-p *symbols-grow-allocation-path* base before)
                   (symbols-grow-allocation-frame-p base before after))))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-condition boymoo-model::a64-result-flags)))
   :rule-classes nil))

(defthm symbols-run-grow-allocation-call
  (let ((path *symbols-grow-allocation-path*) (target (symbols-runtime-address "rt:alloc" base)))
    (implies (and (symbols-grow-allocation-pre-p base before)
                  (symbols-path-ready-p path base target before))
             (symbols-grow-allocation-frame-p base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-grow-allocation)
                 (:instance symbols-replay-is-advance (path *symbols-grow-allocation-path*)
                            (cut (symbols-runtime-address "rt:alloc" base)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p
                               symbols-grow-allocation-frame-p)))
  :rule-classes nil)

(defun symbols-grow-header-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (+ 32 (symbols-runtime-address "rt:intern-grow-table" base)))
       (posp (symbols-stack-word 0 world))
       (< (+ 8 (symbols-stack-word 0 world)) (expt 2 56))
       (< (+ 16 (proof-world-reg 0 world) (symbols-stack-word 0 world)) (expt 2 64))))

(defun symbols-grow-header-world (before)
  (update-nth 0 (boymoo-model::a64-store
                 8 (proof-world-reg 0 before) (+ 6 (* 256 (+ 8 (symbols-stack-word 0 before))))
                 (proof-world-machine before))
              before))

(defun symbols-grow-header-frame-p (base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-clear-buckets" base))
       (equal (proof-world-reg 0 after) *proof-nil*)
       (equal (proof-world-reg 1 after) (proof-world-reg 0 before))
       (equal (proof-world-reg 4 after) (+ 16 (proof-world-reg 0 before)))
       (equal (proof-world-reg 2 after) (+ 16 (proof-world-reg 0 before) (symbols-stack-word 0 before)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))
       (proof-register-frame-p 30 '(0 1 2 3 4) before after)
       (symbols-no-memory-or-kernel-change-p (symbols-grow-header-world before) after)))

(local
 (defthm symbols-replay-grow-header
   (let ((after (symbols-replay *symbols-grow-header-path* before)))
     (implies (symbols-grow-header-pre-p base before)
              (and (symbols-path-control-p *symbols-grow-header-path* base before)
                   (symbols-grow-header-frame-p base before after))))
   :hints (("Goal" :in-theory (e/d (symbols-word-load-fits) (boymoo-model::a64-load))))
   :rule-classes nil))

(defthm symbols-run-grow-header
  (let ((path *symbols-grow-header-path*)
        (target (symbols-runtime-address "rt:intern-clear-buckets" base)))
    (implies (and (symbols-grow-header-pre-p base before)
                  (symbols-path-ready-p path base target before))
             (symbols-grow-header-frame-p base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-grow-header)
                 (:instance symbols-replay-is-advance (path *symbols-grow-header-path*)
                            (cut (symbols-runtime-address "rt:intern-clear-buckets" base)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p
                               symbols-grow-header-frame-p)))
  :rule-classes nil)

(defconst *symbols-grow-from-nil-path*
  (symbols-code-path "rt:intern-clear-buckets" '(16 20 24 28)))

(defconst *symbols-grow-from-table-path*
  (symbols-code-path "rt:intern-clear-buckets" '(16 20 24 28 32 36 40 44 48 52 56)))

(defun symbols-grow-old-table-word (before)
  (symbols-load-register-word (+ (proof-heap-base before) 24) before))

(defun symbols-grow-old-table-address (before)
  (symbols-box-address (symbols-grow-old-table-word before) (proof-heap-base before)))

(defun symbols-grow-after-clear-path (before)
  (if (equal (symbols-grow-old-table-word before) *proof-nil*)
      *symbols-grow-from-nil-path*
    *symbols-grow-from-table-path*))

(defun symbols-grow-after-clear-target (base before)
  (symbols-runtime-address
   (if (equal (symbols-grow-old-table-word before) *proof-nil*)
       "rt:intern-grown"
     "rt:intern-rehash-bucket")
   base))

(defun symbols-grow-after-clear-pre-p (base before)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop before))
       (not (eq (car (proof-world-machine before)) :svc))
       (equal (proof-world-pc before) (+ 16 (symbols-runtime-address "rt:intern-clear-buckets" base)))))

(defun symbols-grow-after-clear-frame-p (base before after)
  (let* ((empty (equal (symbols-grow-old-table-word before) *proof-nil*))
         (old (symbols-grow-old-table-address before))
         (size (symbols-logical-right-shift-bits (symbols-load-register-word old before) 8)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-grow-after-clear-target base before))
         (equal (proof-world-reg 0 after) (if empty 1 (symbols-load-register-word (+ old 8) before)))
         (equal (proof-world-reg 2 after) (if empty *proof-nil* old))
         (implies (not empty)
                  (and (equal (proof-world-reg 6 after) (boymoo-model::a64-unsigned 64 (+ old 16)))
                       (equal (proof-world-reg 7 after)
                              (boymoo-model::a64-unsigned 64
                                                         (+ (boymoo-model::a64-unsigned 64 (+ old 8)) size)))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(0 2 3 6 7) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-replay-grow-after-clear
   (let* ((path (symbols-grow-after-clear-path before))
          (after (symbols-replay path before)))
     (implies (symbols-grow-after-clear-pre-p base before)
              (and (symbols-path-control-p path base before)
                   (symbols-grow-after-clear-frame-p base before after))))
   :hints (("Goal" :in-theory (e/d (symbols-word-load-fits)
                                   (boymoo-model::a64-condition boymoo-model::a64-result-flags
                                    symbols-unsigned-sum-left symbols-unsigned-sum-right))))
   :rule-classes nil))

(defthm symbols-run-grow-after-clear
  (let ((path (symbols-grow-after-clear-path before)))
    (implies (and (symbols-grow-after-clear-pre-p base before)
                  (symbols-path-ready-p path base (symbols-grow-after-clear-target base before) before))
             (symbols-grow-after-clear-frame-p base before (proof-advance (len path) before))))
  :hints (("Goal"
           :use ((:instance symbols-replay-grow-after-clear)
                 (:instance symbols-replay-is-advance (path (symbols-grow-after-clear-path before))
                            (cut (symbols-grow-after-clear-target base before)) (world before)))
           :in-theory (disable symbols-replay symbols-path-control-p proof-advance symbols-path-ready-p
                               symbols-grow-after-clear-path symbols-grow-after-clear-frame-p)))
  :rule-classes nil)
