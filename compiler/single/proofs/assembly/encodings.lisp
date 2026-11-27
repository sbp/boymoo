(in-package "BOYMOO-PROOFS")

(include-book "fields")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod ash expt evenp logbitp
                     acl2::binary-logand acl2::binary-logior acl2::binary-logxor
                     assembly-cat assembly-low assembly-high assembly-power-of-two
                     boymoo-compiler::a64-word)))

(defthm assembly-unsigned-operand
  (implies (unsigned-byte-p width operand)
           (equal (boymoo-compiler::a64-unsigned operand width) operand))
  :hints (("Goal" :in-theory (disable unsigned-byte-p))))

(defthm assembly-reg-operand
  (implies (and (unsigned-byte-p 5 register) (natp shift))
           (equal (boymoo-compiler::a64-reg register shift)
                  (* (assembly-power-of-two shift) register)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p
                                      boymoo-compiler::a64-unsigned))))

(defthm assembly-unsigned-cat
  (implies (and (natp width) (natp n) (<= n width)
                (unsigned-byte-p n lo) (unsigned-byte-p (- width n) hi))
           (unsigned-byte-p width (assembly-cat n lo hi)))
  :hints (("Goal"
           :use ((:instance assembly-cat-bounds
                            (m (- width n)) (low lo) (high hi)))
           :in-theory (disable assembly-cat-bounds unsigned-byte-p))))

(defthm assembly-unsigned-operand-bounds
  (implies (unsigned-byte-p width value)
           (and (natp width) (natp value)
                (< value (assembly-power-of-two width))))
  :hints (("Goal" :in-theory (disable unsigned-byte-p)))
  :rule-classes :forward-chaining)

(defun assembly-packed-term (opcode position fields)
   (if (atom fields)
       (ash opcode (- position))
     (let* ((start (caar fields))
            (width (cadar fields))
            (operand (caddar fields))
            (next (assembly-packed-term opcode (+ start width) (cdr fields)))
            (field (list 'assembly-cat width operand next))
            (gap (- start position)))
       (if (zp gap)
           field
         (list 'assembly-cat gap (mod (ash opcode (- position)) (expt 2 gap)) field)))))

(defmacro assembly-decode-encoding-rule (name word bounds opcode fields instruction &optional extension)
  (let ((packed (assembly-packed-term opcode 0 fields))
        (decoder (if extension 'proof-decode 'boymoo-model::a64-decode)))
    `(encapsulate ()
       (local
        (defthm assembly-word-encoding
          (implies ,bounds
                   (equal ,word ,packed))
          :hints (("Goal"
                   :in-theory (e/d (boymoo-compiler::a64-word assembly-cat)
                                   (floor mod ash expt assembly-high assembly-low
                                    assembly-power-of-two unsigned-byte-p
                                    boymoo-compiler::a64-unsigned boymoo-compiler::a64-reg
                                    acl2::binary-logxor))))
          :rule-classes nil))
       (local
        (defthm assembly-packed-decoding
          (implies ,bounds
                   (equal (,decoder ,packed) ,instruction))
          :hints (("Goal" :in-theory (disable floor mod ash expt evenp logbitp
                                             acl2::binary-logand acl2::binary-logior acl2::binary-logxor
                                             assembly-cat assembly-low assembly-high assembly-power-of-two
                                             unsigned-byte-p assembly-unsigned-width
                                             proof-decode-agrees-with-model
                                             boymoo-model::a64-field boymoo-model::a64-unsigned
                                             boymoo-model::a64-decode-bit-masks
                                             boymoo-model::a64-signed)))
          :rule-classes nil))
       (defthm ,name
         (implies ,bounds
                  (equal (proof-decode ,word) ,instruction))
         :hints (("Goal" :use (assembly-word-encoding assembly-packed-decoding
                              ,@(if extension nil
                                  `((:instance proof-decode-agrees-with-model
                                               (word ,packed)))))
                         :in-theory (disable proof-decode proof-decode-agrees-with-model
                                             boymoo-model::a64-decode
                                             boymoo-compiler::a64-word boymoo-compiler::a64-adr
                                             assembly-cat)))))))

(defmacro assembly-decode-word-rule (name item bounds opcode fields instruction &optional extension)
  `(assembly-decode-encoding-rule ,name (boymoo-compiler::a64-word ,item pc labels)
     ,bounds ,opcode ,fields ,instruction ,extension))

(assembly-decode-word-rule assembly-decode-add
  (list :add rd rn immediate)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #x91000000 ((0 5 rd) (5 5 rn) (10 12 immediate))
  (list :arithmetic-imm 0 64 rd rn immediate))

(assembly-decode-word-rule assembly-decode-mov
  (list :mov rd rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rm))
  #xaa0003e0 ((0 5 rd) (16 5 rm))
  (list :logical-reg 1 64 rd 31 rm 0 0 nil))

(assembly-decode-word-rule assembly-decode-mov-sp
  (list :mov-sp rd rn)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn))
  #x91000000 ((0 5 rd) (5 5 rn))
  (list :arithmetic-imm 0 64 rd rn 0))

(assembly-decode-word-rule assembly-decode-sub
  (list :sub rd rn immediate)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #xd1000000 ((0 5 rd) (5 5 rn) (10 12 immediate))
  (list :arithmetic-imm 2 64 rd rn immediate))

(assembly-decode-word-rule assembly-decode-adds
  (list :adds rd rn immediate)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #xb1000000 ((0 5 rd) (5 5 rn) (10 12 immediate))
  (list :arithmetic-imm 1 64 rd rn immediate))

(assembly-decode-word-rule assembly-decode-subs
  (list :subs rd rn immediate)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #xf1000000 ((0 5 rd) (5 5 rn) (10 12 immediate))
  (list :arithmetic-imm 3 64 rd rn immediate))

(assembly-decode-word-rule assembly-decode-cmp
  (list :cmp rn immediate)
  (and (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #xf100001f ((5 5 rn) (10 12 immediate))
  (list :arithmetic-imm 3 64 31 rn immediate))

(assembly-decode-word-rule assembly-decode-cmn
  (list :cmn rn immediate)
  (and (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #xb100001f ((5 5 rn) (10 12 immediate))
  (list :arithmetic-imm 1 64 31 rn immediate))

(assembly-decode-word-rule assembly-decode-add-reg
  (list :add-reg rd rn rm shift)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn)
       (unsigned-byte-p 5 rm) (unsigned-byte-p 6 shift))
  #x8b000000 ((0 5 rd) (5 5 rn) (10 6 shift) (16 5 rm))
  (list :arithmetic-reg 0 64 rd rn rm 0 shift))

(assembly-decode-word-rule assembly-decode-sub-reg
  (list :sub-reg rd rn rm shift)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn)
       (unsigned-byte-p 5 rm) (unsigned-byte-p 6 shift))
  #xcb000000 ((0 5 rd) (5 5 rn) (10 6 shift) (16 5 rm))
  (list :arithmetic-reg 2 64 rd rn rm 0 shift))

(assembly-decode-word-rule assembly-decode-adds-reg
  (list :adds-reg rd rn rm shift)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn)
       (unsigned-byte-p 5 rm) (unsigned-byte-p 6 shift))
  #xab000000 ((0 5 rd) (5 5 rn) (10 6 shift) (16 5 rm))
  (list :arithmetic-reg 1 64 rd rn rm 0 shift))

(assembly-decode-word-rule assembly-decode-subs-reg
  (list :subs-reg rd rn rm shift)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn)
       (unsigned-byte-p 5 rm) (unsigned-byte-p 6 shift))
  #xeb000000 ((0 5 rd) (5 5 rn) (10 6 shift) (16 5 rm))
  (list :arithmetic-reg 3 64 rd rn rm 0 shift))

(assembly-decode-word-rule assembly-decode-cmp-reg
  (list :cmp-reg rn rm)
  (and (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #xeb00001f ((5 5 rn) (16 5 rm))
  (list :arithmetic-reg 3 64 31 rn rm 0 0))

(assembly-decode-word-rule assembly-decode-neg
  (list :neg rd rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rm))
  #xcb0003e0 ((0 5 rd) (16 5 rm))
  (list :arithmetic-reg 2 64 rd 31 rm 0 0))

(assembly-decode-word-rule assembly-decode-and-reg
  (list :and-reg rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x8a000000 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :logical-reg 0 64 rd rn rm 0 0 nil))

(assembly-decode-word-rule assembly-decode-orr-reg
  (list :orr-reg rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #xaa000000 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :logical-reg 1 64 rd rn rm 0 0 nil))

(assembly-decode-word-rule assembly-decode-eor-reg
  (list :eor-reg rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #xca000000 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :logical-reg 2 64 rd rn rm 0 0 nil))

(assembly-decode-word-rule assembly-decode-ands-reg
  (list :ands-reg rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #xea000000 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :logical-reg 3 64 rd rn rm 0 0 nil))

(assembly-decode-word-rule assembly-decode-tst-reg
  (list :tst-reg rn rm)
  (and (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #xea00001f ((5 5 rn) (16 5 rm))
  (list :logical-reg 3 64 31 rn rm 0 0 nil))

(assembly-decode-word-rule assembly-decode-mvn
  (list :mvn rd rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rm))
  #xaa2003e0 ((0 5 rd) (16 5 rm))
  (list :logical-reg 1 64 rd 31 rm 0 0 t))

(assembly-decode-word-rule assembly-decode-lslv
  (list :lslv rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x9ac02000 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :shift-variable 0 64 rd rn rm))

(assembly-decode-word-rule assembly-decode-lsrv
  (list :lsrv rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x9ac02400 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :shift-variable 1 64 rd rn rm))

(assembly-decode-word-rule assembly-decode-asrv
  (list :asrv rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x9ac02800 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :shift-variable 2 64 rd rn rm))

(assembly-decode-word-rule assembly-decode-clz
  (list :clz rd rn)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn))
  #xdac01000 ((0 5 rd) (5 5 rn))
  (list :clz rd rn))

(assembly-decode-word-rule assembly-decode-mul
  (list :mul rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x9b007c00 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :multiply rd rn rm))

(assembly-decode-word-rule assembly-decode-smulh
  (list :smulh rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x9b407c00 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :signed-multiply-high rd rn rm))

(assembly-decode-word-rule assembly-decode-sdiv
  (list :sdiv rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x9ac00c00 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :divide rd rn rm t))

(assembly-decode-word-rule assembly-decode-udiv
  (list :udiv rd rn rm)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x9ac00800 ((0 5 rd) (5 5 rn) (16 5 rm))
  (list :divide rd rn rm nil))


(assembly-decode-word-rule assembly-decode-ldr-reg
  (list :ldr-reg rt rn rm)
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #xf8606800 ((0 5 rt) (5 5 rn) (16 5 rm))
  (list :single 1 8 rn rt :register rm 3 0))

(assembly-decode-word-rule assembly-decode-str-reg
  (list :str-reg rt rn rm)
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #xf8206800 ((0 5 rt) (5 5 rn) (16 5 rm))
  (list :single 0 8 rn rt :register rm 3 0))

(assembly-decode-word-rule assembly-decode-ldrb-reg
  (list :ldrb-reg rt rn rm)
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x38606800 ((0 5 rt) (5 5 rn) (16 5 rm))
  (list :single 1 1 rn rt :register rm 3 0))

(assembly-decode-word-rule assembly-decode-strb-reg
  (list :strb-reg rt rn rm)
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm))
  #x38206800 ((0 5 rt) (5 5 rn) (16 5 rm))
  (list :single 0 1 rn rt :register rm 3 0))

(assembly-decode-word-rule assembly-decode-ldrb
  (list :ldrb rt rn immediate)
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #x39400000 ((0 5 rt) (5 5 rn) (10 12 immediate))
  (list :single 1 1 rn rt :offset immediate))

(assembly-decode-word-rule assembly-decode-strb
  (list :strb rt rn immediate)
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #x39000000 ((0 5 rt) (5 5 rn) (10 12 immediate))
  (list :single 0 1 rn rt :offset immediate))

(assembly-decode-word-rule assembly-decode-br
  (list :br rn)
  (unsigned-byte-p 5 rn)
  #xd61f0000 ((5 5 rn))
  (list :branch-reg rn nil))

(assembly-decode-word-rule assembly-decode-blr
  (list :blr rn)
  (unsigned-byte-p 5 rn)
  #xd63f0000 ((5 5 rn))
  (list :branch-reg rn t))

(assembly-decode-word-rule assembly-decode-ret
  (list :ret)
  t
  #xd65f03c0 ()
  (list :branch-reg 30 nil))

(assembly-decode-word-rule assembly-decode-svc
  (list :svc immediate)
  (unsigned-byte-p 16 immediate)
  #xd4000001 ((5 16 immediate))
  (list :svc immediate))

(assembly-decode-word-rule assembly-decode-and-mask-discard
  (list :and-mask 31 rn k)
  (and (unsigned-byte-p 5 rn) (posp k) (< k 64))
  #x8a1f001f ((5 5 rn))
  (list :logical-reg 0 64 31 rn 31 0 0 nil))

(assembly-decode-word-rule assembly-decode-cset-al
  (list :cset rd :al)
  (unsigned-byte-p 5 rd)
  #xd2800020 ((0 5 rd))
  (list :move-wide 2 64 rd 1 0))
