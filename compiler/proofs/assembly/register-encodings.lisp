(in-package "BOYMOO-PROOFS")

(include-book "encodings")

(logic)
(set-verify-guards-eagerness 0)

(defmacro assembly-move-wide-decoding (name item opcode operation)
  `(assembly-decode-word-rule ,name
     (list ,item rd immediate shift)
     (and (unsigned-byte-p 5 rd) (unsigned-byte-p 16 immediate)
          (member-equal shift '(0 16 32 48)))
     ,opcode ((0 5 rd) (5 16 immediate) (21 2 (* 1/16 shift)))
     (list :move-wide ,operation 64 rd immediate shift)))

(assembly-move-wide-decoding assembly-decode-movz :movz #xd2800000 2)
(assembly-move-wide-decoding assembly-decode-movn :movn #x92800000 0)
(assembly-move-wide-decoding assembly-decode-movk :movk #xf2800000 3)

(defthm assembly-condition-field
  (implies (assembly-condition-p condition)
           (unsigned-byte-p 4 (boymoo-compiler::a64-condition condition))))

(defthm assembly-inverted-condition-field
  (implies (assembly-condition-p condition)
           (unsigned-byte-p 4
                            (logxor (boymoo-compiler::a64-condition condition) 1))))

(local (in-theory (disable assembly-condition-p boymoo-compiler::a64-condition
                           assembly-condition-field assembly-inverted-condition-field
                           acl2::binary-logxor)))

(assembly-decode-word-rule assembly-decode-csel
  (list :csel rd rn rm condition)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 5 rm)
       (assembly-condition-p condition)
       (unsigned-byte-p 4 (boymoo-compiler::a64-condition condition)))
  #x9a800000 ((0 5 rd) (5 5 rn) (12 4 (boymoo-compiler::a64-condition condition)) (16 5 rm))
  (list :select 64 rd rn rm (boymoo-compiler::a64-condition condition) nil))

(assembly-decode-word-rule assembly-decode-cset
  (list :cset rd condition)
  (and (unsigned-byte-p 5 rd)
       (assembly-condition-p condition) (not (eq condition :al))
       (unsigned-byte-p 4 (logxor (boymoo-compiler::a64-condition condition) 1)))
  #x9a9f07e0 ((0 5 rd) (12 4 (logxor (boymoo-compiler::a64-condition condition) 1)))
  (list :select 64 rd 31 31 (logxor (boymoo-compiler::a64-condition condition) 1) t))

(assembly-decode-word-rule assembly-decode-msub
  (list :msub rd rn rm ra)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn)
       (unsigned-byte-p 5 rm) (unsigned-byte-p 5 ra))
  #x9b008000 ((0 5 rd) (5 5 rn) (10 5 ra) (16 5 rm))
  (list :multiply-subtract rd rn rm ra))
