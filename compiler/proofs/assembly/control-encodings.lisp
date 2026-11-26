(in-package "BOYMOO-PROOFS")

(include-book "signed-fields")
(include-book "register-encodings")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-compiler::a64-offset
                           boymoo-compiler::a64-signed-scaled
                           boymoo-compiler::a64-condition assembly-condition-p
                           assembly-condition-field
                           floor mod ash expt assembly-high assembly-low
                           assembly-power-of-two)))

(local
 (defthm assembly-branch-top-bit
   (and (<= 0 (assembly-high 25 (assembly-low 26 displacement)))
        (< (assembly-high 25 (assembly-low 26 displacement)) 2))
   :hints (("Goal"
            :use ((:instance assembly-floor-bounds (x (assembly-low 26 displacement)) (d (expt 2 25)))
                  (:instance assembly-low-bounds (width 26) (value displacement)))
            :in-theory (enable assembly-high)))
   :rule-classes :linear))

(assembly-decode-word-rule assembly-decode-b
  (list :b label)
  (and (signed-byte-p 26 displacement)
       (equal (- (boymoo-compiler::a64-offset label labels) pc) (* 4 displacement)))
  #x14000000 ((0 26 (assembly-low 26 displacement)))
  (list :branch (* 4 displacement) nil))

(assembly-decode-word-rule assembly-decode-bl
  (list :bl label)
  (and (signed-byte-p 26 displacement)
       (equal (- (boymoo-compiler::a64-offset label labels) pc) (* 4 displacement)))
  #x94000000 ((0 26 (assembly-low 26 displacement)))
  (list :branch (* 4 displacement) t))

(assembly-decode-word-rule assembly-decode-b-cond
  (list :b-cond condition label)
  (and (assembly-condition-p condition)
       (unsigned-byte-p 4 (boymoo-compiler::a64-condition condition))
       (signed-byte-p 19 displacement)
       (equal (- (boymoo-compiler::a64-offset label labels) pc) (* 4 displacement)))
  #x54000000 ((0 4 (boymoo-compiler::a64-condition condition)) (5 19 (assembly-low 19 displacement)))
  (list :branch-cond (* 4 displacement) (boymoo-compiler::a64-condition condition)))

(assembly-decode-word-rule assembly-decode-cbz
  (list :cbz rt label)
  (and (unsigned-byte-p 5 rt) (signed-byte-p 19 displacement)
       (equal (- (boymoo-compiler::a64-offset label labels) pc) (* 4 displacement)))
  #xb4000000 ((0 5 rt) (5 19 (assembly-low 19 displacement)))
  (list :branch-zero (* 4 displacement) 64 rt nil))

(assembly-decode-word-rule assembly-decode-cbnz
  (list :cbnz rt label)
  (and (unsigned-byte-p 5 rt) (signed-byte-p 19 displacement)
       (equal (- (boymoo-compiler::a64-offset label labels) pc) (* 4 displacement)))
  #xb5000000 ((0 5 rt) (5 19 (assembly-low 19 displacement)))
  (list :branch-zero (* 4 displacement) 64 rt t))

(local
 (defthm assembly-adr-upper-field
   (unsigned-byte-p 19 (assembly-high 2 (assembly-low 21 delta)))
   :hints (("Goal"
            :use ((:instance assembly-floor-bounds
                             (x (assembly-low 21 delta)) (d 4))
                  (:instance assembly-low-bounds (width 21) (value delta)))
            :in-theory (e/d (assembly-high) (unsigned-byte-p))))))

(local
 (defthm assembly-adr-upper-bounds
   (and (<= 0 (assembly-high 2 (assembly-low 21 delta)))
        (< (assembly-high 2 (assembly-low 21 delta)) (expt 2 19)))
   :hints (("Goal" :use (assembly-adr-upper-field)
                   :in-theory (disable assembly-adr-upper-field)))
   :rule-classes :linear))

(local
 (defthm assembly-adr-low-field-in-three-bits
   (unsigned-byte-p 3 (assembly-low 2 (assembly-low 21 delta)))
   :hints (("Goal"
            :use ((:instance assembly-low-bounds
                             (width 2) (value (assembly-low 21 delta))))
            :in-theory (disable unsigned-byte-p)))))

(local
 (defthm assembly-join-adr-fields
   (implies (integerp bits)
            (equal (+ (* 4 (assembly-high 2 bits)) (assembly-low 2 bits))
                   bits))
   :hints (("Goal" :use ((:instance assembly-cat-of-low-and-high (width 2) (x bits)))
                   :in-theory (e/d (assembly-cat) (assembly-cat-of-low-and-high))))))

(assembly-decode-word-rule assembly-decode-adr
  (list :adr rd label)
  (and (unsigned-byte-p 5 rd) (signed-byte-p 21 displacement)
       (equal (- (boymoo-compiler::a64-offset label labels) pc) displacement))
  #x10000000 ((0 5 rd) (5 19 (assembly-high 2 (assembly-low 21 displacement)))
              (29 2 (assembly-low 2 (assembly-low 21 displacement))))
  (list :address rd displacement nil))

(assembly-decode-encoding-rule assembly-decode-adrp
  (boymoo-compiler::a64-adr #x90000000 rd displacement)
  (and (unsigned-byte-p 5 rd) (signed-byte-p 21 displacement))
  #x90000000 ((0 5 rd) (5 19 (assembly-high 2 (assembly-low 21 displacement)))
              (29 2 (assembly-low 2 (assembly-low 21 displacement))))
  (list :address rd displacement t))
