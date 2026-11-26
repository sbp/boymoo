(in-package "BOYMOO-PROOFS")

(include-book "machine-ops")

(logic)
(set-verify-guards-eagerness 0)

; The caller's return address must be different from every executed
; instruction address. Each instruction address is a 64-bit address.
(defun p6-site-addresses-p (sites base link)
  (if (atom sites)
      t
    (let ((address (+ base (caar sites))))
      (and (unsigned-byte-p 64 address)
           (not (equal address link))
           (p6-site-addresses-p (cdr sites) base link)))))

(defund p6-path-entry-p (sites base world)
  (and (natp base)
       (consp sites)
       (p6-register-file-p world)
       (not (proof-world-stop world))
       (equal (proof-world-pc world) (+ base (caar sites)))
       (p6-site-addresses-p sites base (proof-world-reg 30 world))
       (p6-sites-placed-p sites base world)))

(defund p6-read-only-return-p (word clobbers changes-flags sites before)
  (let ((after (p6-path-end sites before)))
    (and (proof-segment-p (len sites) (list (proof-world-reg 30 before))
                          before :cut after)
         (proof-frame-return-p clobbers changes-flags before after)
         (p6-same-mapped-memory-p before after)
         (equal (cdr before) (cdr after))
         (equal (proof-world-reg 0 after) word))))

(defund p6-boolean-word (truth)
  (if truth *proof-t* *proof-nil*))

(defconst *p6-boolean-sites* (p6-sites "rt:boolean-eq" 4))

(defund p6-literal-sites (entry)
  (cond ((equal entry "rt:true") (p6-sites "rt:true" 2))
        ((equal entry "rt:nil") (p6-sites "rt:nil" 2))
        ((equal entry "rt:zero") (p6-sites "rt:zero" 2))
        ((equal entry "rt:one") (p6-sites "rt:one" 2))
        ((equal entry "rt:zero-character") (p6-sites "rt:zero-character" 2))
        ((equal entry "rt:bytes-differ") (p6-sites "rt:bytes-differ" 2))
        ((equal entry "rt:bytes-match") (p6-sites "rt:bytes-match" 2))
        (t nil)))

(defund p6-literal-word (entry)
  (cond ((equal entry "rt:true") *proof-t*)
        ((equal entry "rt:nil") *proof-nil*)
        ((equal entry "rt:zero") 1)
        ((equal entry "rt:one") 3)
        ((equal entry "rt:zero-character") 4)
        ((equal entry "rt:bytes-differ") 0)
        ((equal entry "rt:bytes-match") 1)
        (t nil)))

(defund p6-tag-test-sites (name)
  (append (if (eq name 'consp)
              (p6-sites "prim:COMMON-LISP::CONSP" 2)
            (p6-sites "prim:COMMON-LISP::CHARACTERP" 3))
          *p6-boolean-sites*))

(local (in-theory (disable proof-segment-p p6-sites-placed-p)))

(defthm p6-register-frame-reflexive
  (proof-register-frame-p register clobbers world world)
  :hints (("Goal" :induct (proof-register-frame-p register clobbers world world))))

(local
 (defun p6-register-index-induct (register)
   (declare (xargs :measure (nfix register)))
   (if (zp register) nil (p6-register-index-induct (1- register)))))

(defthm p6-register-frame-under-updates
  (and (equal (proof-register-frame-p register clobbers before (p6-set-pc address after))
              (proof-register-frame-p register clobbers before after))
       (equal (proof-register-frame-p register clobbers before (p6-set-flags flags after))
              (proof-register-frame-p register clobbers before after))
       (implies (member-equal dest clobbers)
                (equal (proof-register-frame-p register clobbers before
                                              (p6-set-register dest value after))
                       (proof-register-frame-p register clobbers before after))))
  :hints (("Goal" :induct (p6-register-index-induct register)
                  :in-theory (disable proof-register-frame-p)
                  :expand ((:free (last) (proof-register-frame-p register clobbers before last))))))

(defthm p6-literal-entry-returns
  (let ((sites (p6-literal-sites entry)))
    (implies (p6-path-entry-p sites base world)
             (p6-read-only-return-p (p6-literal-word entry) '(0) nil sites world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-literal-sites p6-literal-word p6-path-entry-p
                              p6-read-only-return-p p6-same-mapped-memory-p)
           :use ((:instance p6-read-only-path-to-cut
                            (sites (p6-literal-sites entry))
                            (cuts (list (proof-world-reg 30 world))))))))

(defthm p6-boolean-entry-returns
  (implies (p6-path-entry-p *p6-boolean-sites* base world)
           (p6-read-only-return-p
            (p6-boolean-word (boymoo-model::a64-condition
                             0 (boymoo-model::a64-nzcv (proof-world-machine world))))
            '(0 1 2) nil *p6-boolean-sites* world))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-path-entry-p p6-read-only-return-p
                              p6-boolean-word p6-same-mapped-memory-p)
           :use ((:instance p6-read-only-path-to-cut
                            (sites *p6-boolean-sites*) (cuts (list (proof-world-reg 30 world))))))))

(defthm p6-tag-test-returns
  (let* ((sites (p6-tag-test-sites name))
         (word (proof-world-reg 0 world))
         (tag (if (eq name 'consp) 0 4)))
    (implies (and (member-eq name '(consp characterp))
                  (p6-path-entry-p sites base world))
             (p6-read-only-return-p (p6-boolean-word (equal (proof-word-tag word) tag))
                                    '(0 1 2) t sites world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-tag-test-sites p6-path-entry-p p6-read-only-return-p
                              proof-word-tag p6-boolean-word p6-same-mapped-memory-p)
           :use ((:instance p6-read-only-path-to-cut
                            (sites (p6-tag-test-sites name))
                            (cuts (list (proof-world-reg 30 world))))))))

(defund p6-projection-sites (name word)
  (let ((carp (eq name 'car)))
    (if (equal (proof-word-tag word) 0)
        (if carp (p6-sites "prim:COMMON-LISP::CAR" 4)
          (p6-sites "prim:COMMON-LISP::CDR" 5))
      (append (if carp (p6-sites "prim:COMMON-LISP::CAR" 2)
                (p6-sites "prim:COMMON-LISP::CDR" 2))
              (p6-literal-sites "rt:nil")))))

(defund p6-projection-address (name word heap-base)
  (boymoo-model::a64-unsigned 64 (+ heap-base word (if (eq name 'car) 0 8))))

(defthm p6-cons-projection-returns
  (let* ((word (proof-world-reg 0 world))
         (address (p6-projection-address name word (proof-heap-base world)))
         (sites (p6-projection-sites name word))
         (cons-tag (equal (proof-word-tag word) 0)))
    (implies (and (member-eq name '(car cdr))
                  (p6-path-entry-p sites base world)
                  (or (not cons-tag) (proof-covered-p address 8 :read (proof-world-regions world))))
             (p6-read-only-return-p (if cons-tag (p6-world-load 8 address world) *proof-nil*)
                                    '(0) t sites world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-projection-sites p6-projection-address p6-path-entry-p
                              p6-literal-sites p6-read-only-return-p p6-same-mapped-memory-p
                              proof-word-tag)
           :use ((:instance p6-read-only-path-to-cut
                            (sites (p6-projection-sites name (proof-world-reg 0 world)))
                            (cuts (list (proof-world-reg 30 world))))))))

(defund p6-header-address (world)
  (boymoo-model::a64-unsigned 64 (+ (proof-heap-base world) (- (proof-world-reg 0 world) 2))))

(defund p6-header-byte (world)
  (p6-world-load 1 (p6-header-address world) world))

(defund p6-header-test-sites (tag)
  (if (equal tag 2)
      (append (p6-sites "rt:header-p" 7) *p6-boolean-sites*)
    (append (p6-sites "rt:header-p" 3) (p6-literal-sites "rt:nil"))))

(defund p6-number-test-sites (odd tag type limit)
  (cond (odd
         (append (p6-sites "rt:number-p" 2) (p6-literal-sites "rt:true")))
        ((not (equal tag 2))
         (append (p6-sites "rt:number-p" 5) (p6-literal-sites "rt:nil")))
        ((< type 3)
         (append (p6-sites "rt:number-p" 9) (p6-literal-sites "rt:nil")))
        ((<= type limit)
         (append (p6-sites "rt:number-p" 11) (p6-literal-sites "rt:true")))
        (t (append (p6-sites "rt:number-p" 12) (p6-literal-sites "rt:nil")))))

(defund p6-type-test-sites (name word type limit)
  (let ((tag (proof-word-tag word)) (odd (oddp word)))
    (case name
      (:header (p6-header-test-sites tag))
      (:number (p6-number-test-sites odd tag type limit))
      (stringp (append (p6-sites "prim:COMMON-LISP::STRINGP" 2) (p6-header-test-sites tag)))
      (symbolp (append (p6-sites "prim:COMMON-LISP::SYMBOLP" 2) (p6-header-test-sites tag)))
      (complex-rationalp (append (p6-sites "prim:ACL2::COMPLEX-RATIONALP" 2)
                                 (p6-header-test-sites tag)))
      (integerp (if odd
                    (append (p6-sites "prim:COMMON-LISP::INTEGERP" 2) (p6-literal-sites "rt:true"))
                  (append (p6-sites "prim:COMMON-LISP::INTEGERP" 3) (p6-header-test-sites tag))))
      (rationalp (append (p6-sites "prim:COMMON-LISP::RATIONALP" 2) (p6-number-test-sites odd tag type 4)))
      (acl2-numberp (append (p6-sites "prim:ACL2::ACL2-NUMBERP" 1) (p6-number-test-sites odd tag type 5)))
      (otherwise nil))))

(defund p6-type-test-value (name word type limit)
  (let ((tag (proof-word-tag word)) (odd (oddp word)))
    (case name
      (:header (and (equal tag 2) (equal type limit)))
      (:number (or odd (and (equal tag 2) (<= 3 type) (<= type limit))))
      (stringp (and (equal tag 2) (equal type 1)))
      (symbolp (and (equal tag 2) (equal type 2)))
      (complex-rationalp (and (equal tag 2) (equal type 5)))
      (integerp (or odd (and (equal tag 2) (equal type 3))))
      (rationalp (or odd (and (equal tag 2) (<= 3 type) (<= type 4))))
      (acl2-numberp (or odd (and (equal tag 2) (<= 3 type) (<= type 5)))))))

(defund p6-type-test-contract-p (name base world)
  (let* ((word (proof-world-reg 0 world))
         (tag (proof-word-tag word))
         (type (p6-header-byte world))
         (limit (proof-world-reg 1 world))
         (sites (p6-type-test-sites name word type limit)))
    (implies (and (p6-path-entry-p sites base world)
                  (or (not (equal tag 2))
                      (proof-covered-p (p6-header-address world) 1 :read (proof-world-regions world))))
             (p6-read-only-return-p (p6-boolean-word (p6-type-test-value name word type limit))
                                    '(0 1 2) t sites world))))

(defmacro p6-prove-type-test (theorem name)
  `(defthm ,theorem
     (p6-type-test-contract-p ',name base world)
     :rule-classes nil
     :hints (("Goal"
              :in-theory (enable p6-type-test-contract-p p6-type-test-sites p6-path-entry-p
                                 p6-read-only-return-p p6-header-test-sites p6-number-test-sites
                                 p6-literal-sites p6-type-test-value p6-boolean-word
                                 p6-same-mapped-memory-p p6-header-byte p6-header-address
                                 proof-word-tag)
              :use ((:instance p6-read-only-path-to-cut
                               (sites (p6-type-test-sites ',name
                                                          (proof-world-reg 0 world)
                                                          (p6-header-byte world) (proof-world-reg 1 world)))
                               (cuts (list (proof-world-reg 30 world)))))))))

(p6-prove-type-test p6-header-test-returns :header)
(p6-prove-type-test p6-stringp-returns stringp)
(p6-prove-type-test p6-symbolp-returns symbolp)
(p6-prove-type-test p6-complex-rationalp-returns complex-rationalp)
(p6-prove-type-test p6-integerp-returns integerp)
(p6-prove-type-test p6-number-test-returns :number)
(p6-prove-type-test p6-rationalp-returns rationalp)
(p6-prove-type-test p6-acl2-numberp-returns acl2-numberp)
