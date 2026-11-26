(in-package "BOYMOO-PROOFS")

(include-book "encodings")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defun assembly-integers-below (end)
   (declare (xargs :measure (nfix end)))
   (if (zp end)
       nil
     (cons (1- end) (assembly-integers-below (1- end))))))

(local
 (defthm assembly-integer-enumeration
   (implies (and (natp value) (natp end) (< value end))
            (member-equal value (assembly-integers-below end)))
   :hints (("Goal" :induct (assembly-integers-below end)))
   :rule-classes nil))

(local
 (defthm assembly-model-low-mask
   (implies (and (posp k) (< k 64))
            (mv-let (valid write-mask test-mask)
              (boymoo-model::a64-decode-bit-masks 64 1 (1- k) 0 t)
              (declare (ignore test-mask))
              (and (equal valid t)
                   (equal write-mask (1- (assembly-power-of-two k))))))
   :hints (("Goal" :use ((:instance assembly-integer-enumeration (value k) (end 64)))
                   :in-theory (disable boymoo-model::a64-decode-bit-masks)))))

(local
 (defthm assembly-model-right-shift-masks
   (implies (unsigned-byte-p 6 shift)
            (mv-let (valid write-mask test-mask)
              (boymoo-model::a64-decode-bit-masks 64 1 63 shift nil)
              (and (equal valid t)
                   (equal write-mask (1- (expt 2 64)))
                   (equal test-mask (1- (assembly-power-of-two (- 64 shift)))))))
   :hints (("Goal" :use ((:instance assembly-integer-enumeration (value shift) (end 64)))
                   :in-theory (disable boymoo-model::a64-decode-bit-masks)))))

(local
 (defthm assembly-model-left-shift-masks
   (implies (unsigned-byte-p 6 shift)
            (mv-let (valid write-mask test-mask)
              (boymoo-model::a64-decode-bit-masks
               64 1 (- 63 shift) (assembly-low 6 (- shift)) nil)
              (and (equal valid t)
                   (equal write-mask (- (expt 2 64) (assembly-power-of-two shift)))
                   (equal test-mask (1- (expt 2 64))))))
   :hints (("Goal" :use ((:instance assembly-integer-enumeration (value shift) (end 64)))
                   :in-theory (disable boymoo-model::a64-decode-bit-masks
                                       assembly-low assembly-power-of-two)))))

(assembly-decode-word-rule assembly-decode-and-mask
  (list :and-mask rd rn k)
  (and (unsigned-byte-p 5 rd) (not (equal rd 31))
       (unsigned-byte-p 5 rn) (posp k) (< k 64)
       (unsigned-byte-p 6 (1- k)))
  #x92400000 ((0 5 rd) (5 5 rn) (10 6 (1- k)))
  (list :logical-imm 0 64 rd rn (1- (assembly-power-of-two k))))

(assembly-decode-word-rule assembly-decode-tst-mask
  (list :tst-mask rn k)
  (and (unsigned-byte-p 5 rn) (posp k) (< k 64)
       (unsigned-byte-p 6 (1- k)))
  #xf240001f ((5 5 rn) (10 6 (1- k)))
  (list :logical-imm 3 64 31 rn (1- (assembly-power-of-two k))))

(assembly-decode-word-rule assembly-decode-lsl
  (list :lsl rd rn shift)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 6 shift)
       (unsigned-byte-p 6 (- 63 shift))
       (unsigned-byte-p 6 (assembly-low 6 (- shift))))
  #xd3400000 ((0 5 rd) (5 5 rn) (10 6 (- 63 shift)) (16 6 (assembly-low 6 (- shift))))
  (list :bitfield 2 64 rd rn (assembly-low 6 (- shift)) (- 63 shift)
        (- (expt 2 64) (assembly-power-of-two shift)) (1- (expt 2 64))))

(assembly-decode-word-rule assembly-decode-lsr
  (list :lsr rd rn shift)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 6 shift))
  #xd340fc00 ((0 5 rd) (5 5 rn) (16 6 shift))
  (list :bitfield 2 64 rd rn shift 63
        (1- (expt 2 64)) (1- (assembly-power-of-two (- 64 shift)))))

(assembly-decode-word-rule assembly-decode-asr
  (list :asr rd rn shift)
  (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn) (unsigned-byte-p 6 shift))
  #x9340fc00 ((0 5 rd) (5 5 rn) (16 6 shift))
  (list :bitfield 0 64 rd rn shift 63
        (1- (expt 2 64)) (1- (assembly-power-of-two (- 64 shift)))))
