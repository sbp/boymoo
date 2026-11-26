(in-package "BOYMOO-PROOFS")

(include-book "bitfield-encodings")
(include-book "control-encodings")
(include-book "fetch")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-decode boymoo-model::a64-decode
                           floor mod ash expt assembly-high assembly-low
                           assembly-power-of-two unsigned-byte-p
                           boymoo-compiler::a64-unsigned
                           boymoo-compiler::a64-offset)))

(defun assembly-zero-source-nzcv (subtract immediate)
  (if subtract
      (if (equal immediate 0) 6 8)
    (if (equal immediate 0) 4 0)))

(defun assembly-zero-source-instructions (subtract rd immediate)
  (if (equal rd 31)
      (list '(:logical-reg 3 64 31 31 31 0 0 nil)
            (list :ccmp 31 31 1 (assembly-zero-source-nzcv subtract immediate)))
    (list (list :move-wide 2 64 rd immediate 0)
          (if subtract
              (list :arithmetic-reg 3 64 rd 31 rd 0 0)
            (list :logical-reg 3 64 31 rd rd 0 0 nil)))))

(local
 (defthm assembly-decode-ccmp-immediate-nzcv
   (implies (member-equal flags '(0 4 6 8))
            (equal (proof-decode (+ #xfa5f13e0 flags))
                   (list :ccmp 31 31 1 flags)))))

(local
 (defthm assembly-decode-movz-zero-shift
   (implies (and (unsigned-byte-p 5 rd) (unsigned-byte-p 12 immediate))
            (equal (proof-decode (boymoo-compiler::a64-wide #xd2800000 rd immediate 0))
                   (list :move-wide 2 64 rd immediate 0)))
   :hints (("Goal"
            :use ((:instance assembly-decode-movz (shift 0) (pc 0) (labels nil)))
            :in-theory (disable assembly-decode-movz boymoo-compiler::a64-wide)))))

(local
 (defthm assembly-decode-subtract-from-zero
   (implies (unsigned-byte-p 5 rd)
            (equal (proof-decode (boymoo-compiler::a64-rrr #xeb000000 rd 31 rd))
                   (list :arithmetic-reg 3 64 rd 31 rd 0 0)))
   :hints (("Goal"
            :use ((:instance assembly-decode-subs-reg
                             (rn 31) (rm rd) (shift 0) (pc 0) (labels nil)))
            :in-theory (disable assembly-decode-subs-reg boymoo-compiler::a64-rrr)))))

(local
 (defthm assembly-decode-test-result
   (implies (unsigned-byte-p 5 rd)
            (equal (proof-decode (boymoo-compiler::a64-rrr #xea000000 31 rd rd))
                   (list :logical-reg 3 64 31 rd rd 0 0 nil)))
   :hints (("Goal"
            :use ((:instance assembly-decode-tst-reg (rn rd) (rm rd) (pc 0) (labels nil)))
            :in-theory (disable assembly-decode-tst-reg boymoo-compiler::a64-rrr)))))

(local (in-theory (disable boymoo-compiler::a64-wide boymoo-compiler::a64-rrr
                           assembly-unsigned-width)))

(defthm assembly-decode-zero-source-arithmetic
  (implies (and (member-eq op '(:adds :subs)) (unsigned-byte-p 5 rd)
                (unsigned-byte-p 12 immediate))
           (equal (assembly-decode-words
                   (assembly-item-words (list op rd 31 immediate) pc labels))
                  (assembly-zero-source-instructions (eq op :subs) rd immediate))))

(defthm assembly-decode-zero-source-compare
  (implies (and (member-eq op '(:cmp :cmn)) (unsigned-byte-p 12 immediate))
           (equal (assembly-decode-words
                   (assembly-item-words (list op 31 immediate) pc labels))
                  (assembly-zero-source-instructions (eq op :cmp) 31 immediate))))

(defun assembly-far-address-instructions (rd target pc)
  (list (list :address rd (- (assembly-high 12 target) (assembly-high 12 pc)) t)
        (if (equal rd 31)
            '(:logical-reg 1 64 31 31 31 0 0 nil)
          (list :arithmetic-imm 0 64 rd rd (assembly-low 12 target)))))

(local
 (defthm assembly-decode-add-to-address
   (implies (and (unsigned-byte-p 5 rd) (unsigned-byte-p 12 immediate))
            (equal (proof-decode (boymoo-compiler::a64-uimm #x91000000 rd rd immediate 0))
                   (list :arithmetic-imm 0 64 rd rd immediate)))
   :hints (("Goal"
            :use ((:instance assembly-decode-add (rn rd) (pc 0) (labels nil)))
            :in-theory (disable assembly-decode-add boymoo-compiler::a64-uimm)))))

(defthm assembly-decode-far-address-item
  (let ((target (boymoo-compiler::a64-offset label labels)))
    (implies (and (unsigned-byte-p 5 rd) (natp pc) (natp target)
                  (signed-byte-p 21 (- (assembly-high 12 target) (assembly-high 12 pc))))
             (equal (assembly-decode-words
                     (assembly-item-words (list :adr-far rd label) pc labels))
                    (assembly-far-address-instructions rd target pc))))
  :hints (("Goal"
           :in-theory (disable boymoo-compiler::a64-uimm boymoo-compiler::a64-adr signed-byte-p))))
