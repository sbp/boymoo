(in-package "BOYMOO-PROOFS")

(include-book "contracts")

(logic)
(set-verify-guards-eagerness 0)

(defund p6-unsigned-bitfield (word rotate write-mask top-mask)
  (logior 0 (logand (logand (boymoo-model::a64-ror 64 word rotate) write-mask) top-mask)))

(defthm p6-effect-unsigned-bitfield
  (implies (p6-register-file-p world)
           (equal (proof-instruction-effect
                   (list :bitfield 2 64 dest source rotate top write-mask top-mask) world)
                  (p6-set-register dest
                                   (p6-unsigned-bitfield (proof-world-reg source world)
                                                         rotate write-mask top-mask)
                                   (p6-next world))))
  :hints (("Goal"
           :in-theory (e/d (proof-instruction-effect proof-execute boymoo-model::a64-execute
                            p6-set-register p6-set-pc proof-world-machine proof-world-pc
                            proof-world-reg proof-reg boymoo-model::a64-read-reg
                            p6-register-file-p p6-unsigned-bitfield)
                           (boymoo-model::a64-ror proof-linux-svc)))))

; A character word occupies at most eleven bits. A valid tagged input
; to CODE-CHAR occupies at most nine. The table checks every word in
; the larger range for each of the three decoded bitfield operations.
(local
 (defun p6-character-shift-row-p (word)
   (and (equal (p6-unsigned-bitfield word 3 #xffffffffffffffff #x1fffffffffffffff) (floor word 8))
        (equal (p6-unsigned-bitfield word 63 #xfffffffffffffffe #xffffffffffffffff) (* 2 word))
        (equal (p6-unsigned-bitfield word 62 #xfffffffffffffffc #xffffffffffffffff) (* 4 word)))))

(local
 (defun p6-character-shift-rows-p (limit)
   (declare (xargs :measure (nfix limit)))
   (if (zp limit)
       t
     (and (p6-character-shift-row-p (1- limit))
          (p6-character-shift-rows-p (1- limit))))))

(local
 (defthm p6-checked-row
   (implies (and (natp word) (natp limit) (< word limit)
                 (p6-character-shift-rows-p limit))
            (p6-character-shift-row-p word))
   :rule-classes nil
   :hints (("Goal" :induct (p6-character-shift-rows-p limit)
                   :in-theory (disable p6-character-shift-row-p)))))

(defthm p6-character-shifts
  (implies (unsigned-byte-p 11 word)
           (and (equal (p6-unsigned-bitfield word 3 #xffffffffffffffff #x1fffffffffffffff) (floor word 8))
                (equal (p6-unsigned-bitfield word 63 #xfffffffffffffffe #xffffffffffffffff) (* 2 word))
                (equal (p6-unsigned-bitfield word 62 #xfffffffffffffffc #xffffffffffffffff) (* 4 word))))
  :hints (("Goal" :use ((:instance p6-checked-row (limit 2048))))))

(local
 (defthm p6-character-right-shift-range
   (implies (unsigned-byte-p 11 word)
            (and (<= 0 (floor word 8)) (< (floor word 8) 256)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance p6-floor-bounds (x word) (d 8)))))))

(defund p6-character-sites (name word)
  (if (eq name 'char-code)
      (if (equal (proof-word-tag word) 4)
          (p6-sites "prim:COMMON-LISP::CHAR-CODE" 7)
        (append (p6-sites "prim:COMMON-LISP::CHAR-CODE" 3) (p6-literal-sites "rt:zero")))
    (cond ((not (oddp word))
           (append (p6-sites "prim:COMMON-LISP::CODE-CHAR" 2) (p6-literal-sites "rt:zero-character")))
          ((< 511 word)
           (append (p6-sites "prim:COMMON-LISP::CODE-CHAR" 4) (p6-literal-sites "rt:zero-character")))
          (t (p6-sites "prim:COMMON-LISP::CODE-CHAR" 6)))))

(defund p6-character-result-word (name word)
  (if (eq name 'char-code)
      (if (equal (proof-word-tag word) 4) (+ 1 (* 2 (floor word 8))) 1)
    (if (and (oddp word) (<= word 511)) (* 4 word) 4)))

(local (in-theory (disable p6-sites-placed-p proof-segment-p)))

(defthm p6-character-routines-return
  (let* ((word (proof-world-reg 0 world))
         (sites (p6-character-sites name word)))
    (implies (and (member-equal name '(char-code code-char))
                  (implies (and (eq name 'char-code) (equal (proof-word-tag word) 4))
                           (unsigned-byte-p 11 word))
                  (p6-path-entry-p sites base world))
             (p6-read-only-return-p (p6-character-result-word name word)
                                    (proof-runtime-clobbers name) t sites world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable proof-word-tag p6-character-sites p6-character-result-word
                              p6-path-entry-p p6-path-end p6-literal-sites p6-read-only-return-p
                              p6-same-mapped-memory-p)
           :use ((:instance p6-read-only-path-to-cut
                            (sites (p6-character-sites name (proof-world-reg 0 world)))
                            (cuts (list (proof-world-reg 30 world))))))))

(defthm p6-view-of-odd-word
  (implies (and (unsigned-byte-p 64 word) (oddp word))
           (equal (proof-view word base objects packages machine)
                  (proof-value-view (ash (boymoo-model::a64-signed 64 word) -1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (proof-view) (p6-even-as-mod))
                  :expand ((:free (cap) (proof-view-step :word word 0 cap base objects packages machine))))))

(defthm p6-byte-integer-has-immediate-view
  (implies (unsigned-byte-p 8 value)
           (proof-value-p (+ 1 (* 2 value)) value base objects packages machine))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable proof-value-p)
           :use ((:instance p6-view-of-odd-word (word (+ 1 (* 2 value))))
                 (:instance p6-floor-mod-of-scaled-sum (lo 1) (d 2) (n value))))))

(defthm p6-character-word-has-value-view
  (implies (characterp value)
           (proof-value-p (proof-character-word value) value base objects packages machine))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-value-p proof-view proof-word-tag p6-unsigned-as-mod
                                          proof-character-word)
                           (p6-unsigned-identity))
           :use ((:instance p6-floor-mod-of-scaled-sum (lo 4) (d 8) (n (char-code value)))
                 (:instance p6-floor-mod-of-scaled-sum (lo 0) (d 2) (n (+ 2 (* 4 (char-code value))))))
           :expand ((:free (cap word) (proof-view-step :word word 0 cap base objects packages machine))))))

(defthm p6-character-view-has-byte-code
  (implies (and (unsigned-byte-p 64 word) (proof-value-p word value base objects packages machine)
                (equal (proof-word-tag word) 4))
           (and (characterp value) (unsigned-byte-p 11 word)
                (equal (floor word 8) (char-code value))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-value-p proof-view) (p6-even-as-mod proof-word-tag))
           :use ((:instance p6-floor-bounds (x word) (d 8))
                 p6-even-tag-is-not-an-immediate-integer)
           :expand ((:free (cap) (proof-view-step :word word 0 cap base objects packages machine))))))

(defthm p6-encoded-byte-integer-domain
  (implies (and (unsigned-byte-p 64 word) (proof-value-p word value base objects packages machine))
           (and (equal (and (oddp word) (<= word 511)) (unsigned-byte-p 8 value))
                (implies (unsigned-byte-p 8 value)
                         (equal word (+ 1 (* 2 value))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (proof-value-p proof-integer-word p6-word-class p6-datum-class
                                          proof-immediate-integer-p)
                           (p6-even-as-mod))
           :cases ((oddp word) (<= word 511))
           :use (p6-word-class-of-value p6-view-of-odd-word p6-odd-word-decodes-to-immediate
                 (:instance p6-floor-bounds (x word) (d 2))))))

(local
 (defthm p6-four-times-two
   (equal (* 4 (* 2 value)) (* 8 value))
   :hints (("Goal" :in-theory (disable associativity-of-*)
                   :use ((:instance associativity-of-* (acl2::x 4) (acl2::y 2) (acl2::z value)))))))

(defthm p6-character-result-has-core-view
  (implies (and (member-equal name '(char-code code-char))
                (unsigned-byte-p 64 word)
                (proof-value-p word value base objects packages machine))
           (proof-value-p
            (p6-character-result-word name word)
            (boymoo-model::core-datum (boymoo-model::core-primitive name (list value) program))
            base objects packages machine))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-character-result-word proof-character-word boymoo-model::core-primitive)
                           (proof-value-p p6-even-as-mod))
           :use (p6-character-view-has-byte-code p6-encoded-byte-integer-domain
                 (:instance p6-tag-tests-agree-with-core (name 'characterp))
                 (:instance p6-byte-integer-has-immediate-view (value 0))
                 (:instance p6-byte-integer-has-immediate-view (value (char-code value)))
                 (:instance p6-character-word-has-value-view (value (code-char 0)))
                 (:instance p6-character-word-has-value-view (value (code-char value))))
           :cases ((equal name 'char-code) (unsigned-byte-p 8 value)))))

(defthm p6-character-primitives-runtime-contract
  (let* ((word (proof-world-reg 0 world))
         (sites (p6-character-sites name word))
         (after (p6-path-end sites world))
         (args (list value)))
    (implies (and (member-equal name '(char-code code-char))
                  (proof-runtime-pre-p name args program labels code-base world objects packages)
                  (p6-path-entry-p sites runtime-base world))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p name args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-read-only-return-p proof-reg-value-p boymoo-model::core-primitive)
           :use ((:instance p6-runtime-pre-has-heap-and-first-arg (args (list value)))
                 (:instance p6-character-view-has-byte-code
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance p6-character-result-has-core-view
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance p6-character-routines-return (base runtime-base))
                 (:instance p6-read-only-datum-return
                            (before world) (word (p6-character-result-word name (proof-world-reg 0 world)))
                            (sites (p6-character-sites name (proof-world-reg 0 world)))
                            (value (boymoo-model::core-datum (boymoo-model::core-primitive name (list value) program)))
                            (clobbers (proof-runtime-clobbers name)) (flags t))))))
