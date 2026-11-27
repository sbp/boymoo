(in-package "BOYMOO-PROOFS")

(include-book "wide-terms")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::gen-load-word boymoo-compiler::gen-load-high
                    boymoo-compiler::gen-load-datum boymoo-compiler::low-bits
                    boymoo-model::a64-unsigned generated-wide-word-items
                    generated-high-halfword-items generated-ash-as-floor ash floor expt mod))

(local
 (defthm generated-fold-tag-multipliers
   (implies (syntaxp (and (quotep first) (quotep second)))
            (equal (* first (* second x)) (* (* first second) x)))
   :hints (("Goal" :use (:instance associativity-of-*
                                   (acl2::x first) (acl2::y second) (acl2::z x))
                   :in-theory (disable associativity-of-*)))))

(local
 (defthm generated-halfword-ignores-truncated-bits
   (let* ((shifted (* (expt 2 (- 64 position)) multiple))
          (extended (+ word shifted))
          (scaled-multiple (* (expt 2 (- 48 position)) multiple)))
     (implies (and (integerp word) (integerp multiple) (member-equal position '(0 16 32 48)))
              (and (equal (ash extended -16) (+ (ash word -16) scaled-multiple))
                   (equal (boymoo-compiler::low-bits extended 16)
                          (boymoo-compiler::low-bits word 16)))))
   :hints (("Goal"
            :use (:instance generated-floor-add-multiple
                            (x word) (divisor 65536) (q (* (expt 2 (- 48 position)) multiple)))
            :in-theory (enable boymoo-compiler::low-bits)))
   :rule-classes nil))

(local
 (defthm generated-high-halfword-step
   (implies (and (natp position) (< position 64))
            (equal (generated-high-halfword-items rd word position)
                   (let* ((half (boymoo-compiler::low-bits word 16))
                          (rest (generated-high-halfword-items rd (ash word -16) (+ 16 position))))
                     (if (equal half 0) rest (cons (list :movk rd half position) rest)))))
   :hints (("Goal" :in-theory (enable generated-high-halfword-items)
                   :cases ((equal word 0))))
   :rule-classes nil))

(local
 (defun generated-truncated-halfword-induction (word position)
   (declare (xargs :measure (nfix (- 64 position))))
   (if (or (not (natp position)) (<= 64 position))
       word
     (generated-truncated-halfword-induction (ash word -16) (+ 16 position)))))

(local
 (defthm generated-high-halfwords-ignore-truncated-bits
   (implies (and (integerp word) (integerp multiple) (member-equal position '(16 32 48 64)))
            (equal (generated-high-halfword-items
                    rd (+ word (* (expt 2 (- 64 position)) multiple)) position)
                   (generated-high-halfword-items rd word position)))
   :hints (("Goal" :induct (generated-truncated-halfword-induction word position))
           ("Subgoal *1/1" :in-theory (enable generated-high-halfword-items))
           ("Subgoal *1/2"
            :use (generated-high-halfword-step generated-halfword-ignores-truncated-bits
                  (:instance generated-high-halfword-step
                             (word (+ word (* (expt 2 (- 64 position)) multiple)))))))
   :rule-classes nil))

(defthm generated-word-items-use-64-low-bits
  (implies (integerp word)
           (equal (generated-wide-word-items rd (boymoo-model::a64-unsigned 64 word))
                  (generated-wide-word-items rd word)))
  :hints (("Goal"
           :use ((:instance generated-unsigned-as-mod (n 64) (x word))
                 (:instance generated-halfword-ignores-truncated-bits
                            (position 0) (multiple (- (floor word (expt 2 64)))))
                 (:instance generated-high-halfwords-ignore-truncated-bits
                            (position 16) (word (ash word -16))
                            (multiple (- (floor word (expt 2 64))))))
           :in-theory (enable mod generated-wide-word-items))))

(local
 (defthm generated-floor-of-tagged-integer
   (implies (integerp datum)
            (equal (floor (+ 1 (* 2 datum)) 65536) (floor datum 32768)))
   :hints (("Goal"
            :use ((:instance generated-floor-bounds (x datum) (y 32768))
                  (:instance generated-integer-step
                             (x datum) (y (+ 32768 (* 32768 (floor datum 32768)))))
                  (:instance generated-floor-unique
                             (x (+ 1 (* 2 datum))) (y 65536) (q (floor datum 32768))))))))

(local
 (defthm generated-shift-down-fifteen
   (implies (integerp datum) (equal (ash datum -15) (floor datum 32768)))
   :hints (("Goal" :in-theory (enable ash floor)))))

(defthm generated-tagged-constant-emission
  (implies (integerp datum)
           (equal (boymoo-compiler::gen-load-datum rd (cons :integer datum) code)
                  (boymoo-compiler::gen-load-word rd (proof-integer-word datum) code)))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-load-datum boymoo-compiler::low-bits
                                    generated-wide-word-items proof-integer-word))))

(defthm generated-tagged-quote-emission
  (implies (and (stringp text) (integerp datum)
                (equal (boymoo-compiler::index-get text (caddr context)) (cons :integer datum)))
           (equal (mv-nth 0 (boymoo-compiler::gen-term
                             (list boymoo-compiler::*quote-name* text)
                             scope depth nil context code high serial))
                  (boymoo-compiler::reverse-onto
                   (generated-wide-word-items 0 (proof-integer-word datum)) code)))
  :hints (("Goal"
           :expand (boymoo-compiler::gen-term (list boymoo-compiler::*quote-name* text)
                                             scope depth nil context code high serial)
           :in-theory (enable boymoo-compiler::gen-simple-p boymoo-compiler::gen-simple
                              boymoo-compiler::gen-datum boymoo-compiler::gen-finish))))

(defthm generated-tagged-quote-execution
  (let* ((word (proof-integer-word datum))
         (path (generated-move-instructions (generated-wide-word-items 0 word)))
         (after (generated-path-after path before))
         (end (+ (proof-world-pc before) (* 4 (len path))))
         (result (boymoo-model::core-eval-step :term (list 'quote datum) env program fuel)))
    (implies (and (stringp text) (proof-immediate-integer-p datum) (posp fuel)
                  (equal (boymoo-compiler::index-get text (caddr context)) (cons :integer datum))
                  (< end (expt 2 64)) (not (proof-world-stop before))
                  (proof-heap-p before objects packages)
                  (generated-path-p path (list end) before))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (boymoo-model::core-value-p result)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after objects packages)
                  (proof-prefix-preserved-p (proof-stack-top before)
                                            before after objects objects packages))))
  :hints (("Goal"
           :use ((:instance generated-wide-word-load-continuation (rd 0) (word (proof-integer-word datum)))
                 (:instance generated-immediate-word-view (value datum) (base (proof-heap-base before))
                            (machine (proof-world-machine before))))
           :in-theory (e/d (proof-heap-p proof-reg-value-p proof-machine-value-p proof-value-p)
                           (generated-path-p generated-path-after))))
  :rule-classes nil)
