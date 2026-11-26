(in-package "BOYMOO-PROOFS")

(include-book "link")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-item-refers-to-label-p (item)
  (member-eq (car item) '(:b :bl :b-cond :cbz :cbnz :adr :adr-far)))

(defun assembly-item-target-label (item)
  (if (member-eq (car item) '(:b :bl))
      (cadr item)
    (caddr item)))

(defun assembly-item-label-agreement-p (item labels offsets)
  (or (not (assembly-item-refers-to-label-p item))
      (let ((key (assembly-item-target-label item)))
        (equal (boymoo-compiler::a64-offset key labels)
               (assembly-label-offset key offsets)))))

(defun assembly-single-instruction (item pc offsets)
  (let ((a (cadr item)) (b (caddr item)) (c (cadddr item))
        (d (car (cddddr item))))
    (case (car item)
      (:movz (list :move-wide 2 64 a b c))
      (:movn (list :move-wide 0 64 a b c))
      (:movk (list :move-wide 3 64 a b c))
      (:mov (list :logical-reg 1 64 a 31 b 0 0 nil))
      (:mov-sp (list :arithmetic-imm 0 64 a b 0))
      (:add (list :arithmetic-imm 0 64 a b c))
      (:sub (list :arithmetic-imm 2 64 a b c))
      (:adds (list :arithmetic-imm 1 64 a b c))
      (:subs (list :arithmetic-imm 3 64 a b c))
      (:cmp (list :arithmetic-imm 3 64 31 a b))
      (:cmn (list :arithmetic-imm 1 64 31 a b))
      (:add-reg (list :arithmetic-reg 0 64 a b c 0 d))
      (:sub-reg (list :arithmetic-reg 2 64 a b c 0 d))
      (:adds-reg (list :arithmetic-reg 1 64 a b c 0 d))
      (:subs-reg (list :arithmetic-reg 3 64 a b c 0 d))
      (:cmp-reg (list :arithmetic-reg 3 64 31 a b 0 0))
      (:neg (list :arithmetic-reg 2 64 a 31 b 0 0))
      (:and-reg (list :logical-reg 0 64 a b c 0 0 nil))
      (:orr-reg (list :logical-reg 1 64 a b c 0 0 nil))
      (:eor-reg (list :logical-reg 2 64 a b c 0 0 nil))
      (:ands-reg (list :logical-reg 3 64 a b c 0 0 nil))
      (:tst-reg (list :logical-reg 3 64 31 a b 0 0 nil))
      (:mvn (list :logical-reg 1 64 a 31 b 0 0 t))
      (:and-mask (if (equal a 31)
                     (list :logical-reg 0 64 31 b 31 0 0 nil)
                   (list :logical-imm 0 64 a b (1- (assembly-power-of-two c)))))
      (:tst-mask (list :logical-imm 3 64 31 a (1- (assembly-power-of-two b))))
      (:lsl (list :bitfield 2 64 a b (assembly-low 6 (- c)) (- 63 c)
                  (- (expt 2 64) (assembly-power-of-two c)) (1- (expt 2 64))))
      (:lsr (list :bitfield 2 64 a b c 63
                  (1- (expt 2 64)) (1- (assembly-power-of-two (- 64 c)))))
      (:asr (list :bitfield 0 64 a b c 63
                  (1- (expt 2 64)) (1- (assembly-power-of-two (- 64 c)))))
      (:lslv (list :shift-variable 0 64 a b c))
      (:lsrv (list :shift-variable 1 64 a b c))
      (:asrv (list :shift-variable 2 64 a b c))
      (:clz (list :clz a b))
      (:mul (list :multiply a b c))
      (:smulh (list :signed-multiply-high a b c))
      (:msub (list :multiply-subtract a b c d))
      (:sdiv (list :divide a b c t))
      (:udiv (list :divide a b c nil))
      (:csel (list :select 64 a b c (boymoo-compiler::a64-condition d) nil))
      (:cset (if (eq b :al)
                 (list :move-wide 2 64 a 1 0)
               (list :select 64 a 31 31 (logxor (boymoo-compiler::a64-condition b) 1) t)))
      (:ldr (list :single 1 8 b a :offset c))
      (:str (list :single 0 8 b a :offset c))
      (:ldrb (list :single 1 1 b a :offset c))
      (:strb (list :single 0 1 b a :offset c))
      (:ldr-reg (list :single 1 8 b a :register c 3 0))
      (:str-reg (list :single 0 8 b a :register c 3 0))
      (:ldrb-reg (list :single 1 1 b a :register c 3 0))
      (:strb-reg (list :single 0 1 b a :register c 3 0))
      (:ldp (list :pair t c a b :offset d))
      (:stp (list :pair nil c a b :offset d))
      (:ldp-post (list :pair t c a b :post d))
      (:stp-pre (list :pair nil c a b :pre d))
      (:b (list :branch (- (assembly-label-offset a offsets) pc) nil))
      (:bl (list :branch (- (assembly-label-offset a offsets) pc) t))
      (:b-cond (list :branch-cond (- (assembly-label-offset b offsets) pc)
                     (boymoo-compiler::a64-condition a)))
      (:cbz (list :branch-zero (- (assembly-label-offset b offsets) pc) 64 a nil))
      (:cbnz (list :branch-zero (- (assembly-label-offset b offsets) pc) 64 a t))
      (:adr (list :address a (- (assembly-label-offset b offsets) pc) nil))
      (:br (list :branch-reg a nil))
      (:blr (list :branch-reg a t))
      (:ret (list :branch-reg 30 nil))
      (:svc (list :svc a))
      (otherwise nil))))

(defun assembly-specified-instructions (item pc offsets)
  (let ((op (car item)) (a (cadr item)) (b (caddr item)) (c (cadddr item)))
    (cond ((eq op :adr-far)
           (assembly-far-address-instructions a (assembly-label-offset b offsets) pc))
          ((and (member-eq op '(:adds :subs)) (equal b 31))
           (assembly-zero-source-instructions (eq op :subs) a c))
          ((and (member-eq op '(:cmp :cmn)) (equal a 31))
           (assembly-zero-source-instructions (eq op :cmp) 31 b))
          (t (let ((instruction (assembly-single-instruction item pc offsets)))
               (and instruction (list instruction)))))))

(local (in-theory (disable proof-decode proof-decode-agrees-with-model
                           boymoo-model::a64-decode boymoo-compiler::a64-word
                           boymoo-compiler::a64-offset boymoo-compiler::a64-condition
                           assembly-label-offset assembly-condition-p
                           assembly-low assembly-high assembly-power-of-two
                           floor ash mod expt acl2::binary-logxor)))

(local
 (defthm assembly-six-bit-reflection
   (implies (unsigned-byte-p 6 shift)
            (unsigned-byte-p 6 (- 63 shift)))))

(local
 (defthm assembly-low-mask-field-width
   (implies (and (posp width) (< width 64))
            (unsigned-byte-p 6 (1- width)))))

(local
 (defthm assembly-page-number-is-floor
   (implies (integerp value)
            (equal (floor value 4096) (assembly-high 12 value)))
   :hints (("Goal" :in-theory (enable assembly-high)))))

(local
 (defthm assembly-cancel-branch-scale
   (equal (* 4 (* 1/4 value)) (fix value))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-* (acl2::x 4) (acl2::y 1/4) (acl2::z value)))
            :in-theory (disable acl2::associativity-of-*)))))

(local
 (defthm assembly-cancel-word-scale
   (equal (* 8 (* 1/8 value)) (fix value))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-* (acl2::x 8) (acl2::y 1/8) (acl2::z value)))
            :in-theory (disable acl2::associativity-of-*)))))

(local
 (defmacro assembly-relocated-branch-rule (name decoder item label width bounds decoded)
   `(defthm ,name
      (let ((delta (- (boymoo-compiler::a64-offset ,label labels) pc)))
        (implies (and ,bounds (signed-byte-p ,width (* 1/4 delta)))
                 (equal (proof-decode (boymoo-compiler::a64-word ,item pc labels))
                        ,decoded)))
      :hints (("Goal"
               :use ((:instance ,decoder
                                (displacement (* 1/4 (- (boymoo-compiler::a64-offset
                                                          ,label labels)
                                                        pc)))))
               :in-theory (disable ,decoder signed-byte-p assembly-signed-width
                                   acl2::distributivity))))))

(local
 (assembly-relocated-branch-rule assembly-relocated-b assembly-decode-b
   (list :b label) label 26 t (list :branch delta nil)))

(local
 (assembly-relocated-branch-rule assembly-relocated-bl assembly-decode-bl
   (list :bl label) label 26 t (list :branch delta t)))

(local
 (assembly-relocated-branch-rule assembly-relocated-b-cond assembly-decode-b-cond
   (list :b-cond condition label) label 19 (assembly-condition-p condition)
   (list :branch-cond delta (boymoo-compiler::a64-condition condition))))

(local
 (assembly-relocated-branch-rule assembly-relocated-cbz assembly-decode-cbz
   (list :cbz rt label) label 19 (unsigned-byte-p 5 rt)
   (list :branch-zero delta 64 rt nil)))

(local
 (assembly-relocated-branch-rule assembly-relocated-cbnz assembly-decode-cbnz
   (list :cbnz rt label) label 19 (unsigned-byte-p 5 rt)
   (list :branch-zero delta 64 rt t)))

(local
 (defthm assembly-relocated-adr
   (let ((delta (- (boymoo-compiler::a64-offset label labels) pc)))
     (implies (and (unsigned-byte-p 5 rd) (signed-byte-p 21 delta))
              (equal (proof-decode (boymoo-compiler::a64-word (list :adr rd label) pc labels))
                     (list :address rd delta nil))))
   :hints (("Goal" :use ((:instance assembly-decode-adr
                                    (displacement (- (boymoo-compiler::a64-offset label labels) pc))))
                   :in-theory (disable assembly-decode-adr signed-byte-p assembly-signed-width)))))

(local
 (defmacro assembly-memory-decoding-at-byte-offset (name decoder operand item predicate decoded)
   `(defthm ,name
      (implies ,predicate
               (equal (proof-decode (boymoo-compiler::a64-word ,item pc labels))
                      ,decoded))
      :hints (("Goal"
               :use ((:instance ,decoder (,operand (* 1/8 offset))))
               :in-theory (disable ,decoder))))))

(local
 (assembly-memory-decoding-at-byte-offset assembly-ldr-at-byte-offset assembly-decode-ldr immediate
   (list :ldr rt rn offset)
   (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (assembly-unsigned-scaled-p 12 3 offset))
   (list :single 1 8 rn rt :offset offset)))

(local
 (assembly-memory-decoding-at-byte-offset assembly-str-at-byte-offset assembly-decode-str immediate
   (list :str rt rn offset)
   (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (assembly-unsigned-scaled-p 12 3 offset))
   (list :single 0 8 rn rt :offset offset)))

(local
 (assembly-memory-decoding-at-byte-offset assembly-ldp-at-byte-offset assembly-decode-ldp displacement
   (list :ldp rt rt2 rn offset)
   (and (assembly-pair-registers-p :ldp rt rt2 rn) (assembly-signed-scaled-p 7 3 offset))
   (list :pair t rn rt rt2 :offset offset)))

(local
 (assembly-memory-decoding-at-byte-offset assembly-stp-at-byte-offset assembly-decode-stp displacement
   (list :stp rt rt2 rn offset)
   (and (assembly-pair-registers-p :stp rt rt2 rn) (assembly-signed-scaled-p 7 3 offset))
   (list :pair nil rn rt rt2 :offset offset)))

(local
 (assembly-memory-decoding-at-byte-offset assembly-ldp-post-at-byte-offset assembly-decode-ldp-post displacement
   (list :ldp-post rt rt2 rn offset)
   (and (assembly-pair-registers-p :ldp-post rt rt2 rn) (assembly-signed-scaled-p 7 3 offset))
   (list :pair t rn rt rt2 :post offset)))

(local
 (assembly-memory-decoding-at-byte-offset assembly-stp-pre-at-byte-offset assembly-decode-stp-pre displacement
   (list :stp-pre rt rt2 rn offset)
   (and (assembly-pair-registers-p :stp-pre rt rt2 rn) (assembly-signed-scaled-p 7 3 offset))
   (list :pair nil rn rt rt2 :pre offset)))

(local
 (defthm assembly-one-word-for-unexpanded-item
   (implies (and (assembly-code-item-p item) (not (eq (car item) :adr-far))
                 (not (and (member-eq (car item) '(:adds :subs :cmp :cmn))
                           (boymoo-compiler::a64-zero-source-p item))))
            (equal (assembly-item-words item pc labels)
                   (list (boymoo-compiler::a64-word item pc labels))))
   :hints (("Goal" :in-theory (disable boymoo-compiler::a64-zero-source-p)))))

(local (in-theory (disable assembly-item-words assembly-adr-far-words
                           assembly-far-address-instructions assembly-zero-source-instructions)))

(local
 (defmacro assembly-check-shaped-decoding (name operands)
   `(defthm ,name
      (let ((item (list op ,@operands)))
        (implies (and (assembly-executable-item-p item pc offsets)
                      (assembly-item-label-agreement-p item labels offsets))
                 (equal (assembly-decode-words (assembly-item-words item pc labels))
                        (assembly-specified-instructions item pc offsets))))
      :rule-classes nil)))

(local (assembly-check-shaped-decoding assembly-decode-item-with-no-operands ()))
(local (assembly-check-shaped-decoding assembly-decode-item-with-one-operand (a)))
(local (assembly-check-shaped-decoding assembly-decode-item-with-two-operands (a b)))
(local (assembly-check-shaped-decoding assembly-decode-item-with-three-operands (a b c)))
(local (assembly-check-shaped-decoding assembly-decode-item-with-four-operands (a b c d)))

(local
 (defthm assembly-executable-item-is-short
   (implies (assembly-executable-item-p item pc offsets)
            (and (consp item) (true-listp item) (<= (len item) 5)))
   :rule-classes nil))

(local
 (defthm assembly-short-list-shapes
   (implies (and (consp item) (true-listp item) (<= (len item) 5))
            (let ((op (car item)) (a (cadr item)) (b (caddr item))
                  (c (cadddr item)) (d (car (cddddr item))))
              (or (equal item (list op))
                  (equal item (list op a))
                  (equal item (list op a b))
                  (equal item (list op a b c))
                  (equal item (list op a b c d)))))
   :hints (("Goal" :cases ((consp (cdr item)) (consp (cddr item))
                           (consp (cdddr item)) (consp (cddddr item)))))
   :rule-classes nil))

(defthm assembly-executable-item-decodes
  (implies (and (assembly-executable-item-p item pc offsets)
                (assembly-item-label-agreement-p item labels offsets))
           (equal (assembly-decode-words (assembly-item-words item pc labels))
                  (assembly-specified-instructions item pc offsets)))
  :hints (("Goal"
           :use (assembly-executable-item-is-short assembly-short-list-shapes
                 (:instance assembly-decode-item-with-no-operands
                            (op (car item)))
                 (:instance assembly-decode-item-with-one-operand
                            (op (car item)) (a (cadr item)))
                 (:instance assembly-decode-item-with-two-operands
                            (op (car item)) (a (cadr item)) (b (caddr item)))
                 (:instance assembly-decode-item-with-three-operands
                            (op (car item)) (a (cadr item)) (b (caddr item)) (c (cadddr item)))
                 (:instance assembly-decode-item-with-four-operands
                            (op (car item)) (a (cadr item)) (b (caddr item))
                            (c (cadddr item)) (d (car (cddddr item)))))
           :in-theory (disable assembly-executable-item-p assembly-item-label-agreement-p
                               assembly-specified-instructions assembly-decode-words)))
  :rule-classes nil)

(defthm assembly-executable-item-position
  (implies (assembly-executable-item-p item pc offsets)
           (and (natp pc) (equal (mod pc 4) 0) (assembly-code-item-p item)))
  :rule-classes nil)

(defthm assembly-executable-item-target-defined
  (implies (and (assembly-executable-item-p item pc offsets)
                (assembly-item-refers-to-label-p item))
           (assoc-equal (assembly-item-target-label item) offsets))
  :hints (("Goal" :in-theory (enable assembly-label-offset)))
  :rule-classes nil)

(defthm assembly-specified-instruction-shape
  (implies (assembly-executable-item-p item pc offsets)
           (let ((instructions (assembly-specified-instructions item pc offsets)))
             (and (assembly-decoded-list-p instructions)
                  (or (equal (len instructions) 1)
                      (and (equal (len instructions) 2)
                           (assembly-register-instruction-p (car instructions))
                           (assembly-register-instruction-p (cadr instructions)))))))
  :hints (("Goal" :in-theory (enable assembly-zero-source-instructions
                                     assembly-far-address-instructions)))
  :rule-classes nil)
