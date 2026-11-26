(in-package "BOYMOO-PROOFS")

(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt
                           acl2::binary-logand acl2::binary-logior lognot
                           assembly-cat assembly-low assembly-high assembly-power-of-two)))

(defthm assembly-high-of-high
  (implies (and (natp a) (natp b) (integerp x))
           (equal (assembly-high b (assembly-high a x))
                  (assembly-high (+ a b) x)))
  :hints (("Goal" :use ((:instance assembly-split-above-cat
                                   (width (+ a b)) (n a)
                                   (low (assembly-low a x))
                                   (high (assembly-high a x))))
                  :in-theory (disable assembly-split-above-cat))))

(defthm assembly-logior-zero
  (implies (integerp x)
           (and (equal (logior x 0) x)
                (equal (logior 0 x) x)))
  :hints (("Goal" :in-theory (enable acl2::binary-logior lognot))))

(defthm assembly-lognot-of-cat
  (implies (and (integerp low) (integerp high))
           (equal (lognot (assembly-cat n low high))
                  (assembly-cat n (- (1- (assembly-power-of-two n)) low)
                                (lognot high))))
  :hints (("Goal" :in-theory (enable lognot assembly-cat) :nonlinearp t)))

(local
 (defthm assembly-logand-left-congruence
   (implies (equal a b)
            (equal (logand a c) (logand b c)))
   :rule-classes nil))

(local
 (defthm assembly-and-complemented-fields
   (implies (and (natp width) (natp low) (< low (assembly-power-of-two width))
                 (integerp high))
            (equal (logand (lognot low) (lognot (assembly-cat width 0 high)))
                   (lognot (assembly-cat width low high))))
   :hints (("Goal"
            :use ((:instance assembly-lognot-of-cat (n width) (high 0))
                  (:instance assembly-logand-left-congruence
                             (a (lognot low))
                             (b (assembly-cat width (- (1- (assembly-power-of-two width)) low) -1))
                             (c (lognot (assembly-cat width 0 high)))))))))

(local
 (defthm assembly-double-lognot
   (implies (integerp x) (equal (lognot (lognot x)) x))
   :hints (("Goal" :in-theory (enable lognot)))))

(defthm assembly-logior-disjoint-fields
  (implies (and (natp width) (natp low) (< low (assembly-power-of-two width))
                (integerp high))
           (equal (logior low (assembly-cat width 0 high))
                  (assembly-cat width low high)))
  :hints (("Goal"
           :in-theory (e/d (acl2::binary-logior) (assembly-lognot-of-cat)))))

