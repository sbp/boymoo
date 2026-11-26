(in-package "BOYMOO-PROOFS")

(include-book "heap-views")
(include-book "equality-views")
(include-book "characters")

(logic)
(set-verify-guards-eagerness 0)

(defconst *p6-equal-same-word-sites*
  (append (p6-sites "prim:COMMON-LISP::EQUAL" 2) (p6-literal-sites "rt:true")))

(defthm p6-equal-same-word-returns
  (implies (and (equal (proof-world-reg 0 world) (proof-world-reg 1 world))
                (p6-path-entry-p *p6-equal-same-word-sites* base world))
           (p6-read-only-return-p *proof-t* '(0) t *p6-equal-same-word-sites* world))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-path-entry-p p6-read-only-return-p p6-same-mapped-memory-p p6-path-end)
                           (proof-segment-p p6-sites-placed-p))
           :use ((:instance p6-read-only-path-to-cut (sites *p6-equal-same-word-sites*)
                            (cuts (list (proof-world-reg 30 world))))))))

(local
 (defthm p6-runtime-pre-has-two-args
   (implies (proof-runtime-pre-p name (list first second) program labels code-base world objects packages)
            (and (proof-reg-value-p 0 first world objects packages)
                 (proof-reg-value-p 1 second world objects packages)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-runtime-pre-p)
                                   (proof-runtime-entry proof-program-packages-p))))))

(local
 (defthm p6-equal-register-frame-weakening
   (implies (and (member-equal clobbers '((0) (0 2)))
                 (proof-register-frame-p register clobbers before after))
            (proof-register-frame-p register '(0 1 2 3 4 5 6 7 8 9 10 11 12 24) before after))
   :rule-classes nil
   :hints (("Goal" :induct (proof-register-frame-p register clobbers before after)))))

(local
 (defthm p6-equal-datum-frame-weakening
   (implies (and (member-equal clobbers '((0) (0 2)))
                 (proof-datum-return-p datum clobbers t nil nil before after objects objects packages))
            (proof-datum-return-p datum '(0 1 2 3 4 5 6 7 8 9 10 11 12 24) t nil nil
                                  before after objects objects packages))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-datum-return-p)
                                   (proof-preserved-heap-p proof-fixed-heap-p))
                   :use ((:instance p6-equal-register-frame-weakening (register 30)))))))

(defthm p6-equal-same-word-runtime-contract
  (let* ((sites *p6-equal-same-word-sites*)
         (after (p6-path-end sites world))
         (args (list first second)))
    (implies (and (equal (proof-world-reg 0 world) (proof-world-reg 1 world))
                  (proof-runtime-pre-p 'equal args program labels code-base world objects packages)
                  (p6-path-entry-p sites runtime-base world))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p 'equal args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-read-only-return-p p6-boolean-views-p proof-reg-value-p
                              boymoo-model::core-primitive)
           :use ((:instance p6-runtime-pre-has-two-args (name 'equal))
                 p6-heap-has-boolean-views
                 (:instance p6-runtime-pre-has-heap-and-first-arg (name 'equal) (args (list first second)))
                 (:instance p6-equal-same-word-returns (base runtime-base))
                 (:instance p6-view-of-equal-words
                            (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world))
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-read-only-datum-return
                            (before world) (sites *p6-equal-same-word-sites*) (word *proof-t*) (value t)
                            (clobbers '(0)) (flags t))
                 (:instance p6-equal-datum-frame-weakening
                            (before world) (after (p6-path-end *p6-equal-same-word-sites* world))
                            (clobbers '(0)) (datum t))))))

(defthm p6-effect-exclusive-or
  (implies (and (p6-register-file-p world) (natp dest) (< dest 31))
           (equal (proof-instruction-effect (list :logical-reg 2 64 dest left right 0 0 nil) world)
                  (p6-set-register dest (logxor (proof-world-reg left world) (proof-world-reg right world))
                                   (p6-next world))))
  :hints (("Goal"
           :in-theory (enable proof-instruction-effect proof-execute boymoo-model::a64-execute
                              boymoo-model::a64-read-reg p6-register-file-p p6-set-pc p6-set-register
                              proof-world-machine proof-world-pc proof-world-reg proof-reg))))

(defund p6-equal-early-rejects-p (left right)
  (and (not (equal left right))
       (or (not (equal (proof-word-tag left) (proof-word-tag right)))
           (not (member-equal (proof-word-tag left) '(0 2))))))

(defund p6-equal-reject-sites (left right)
  (append (if (equal (proof-word-tag left) (proof-word-tag right))
              (p6-sites "prim:COMMON-LISP::EQUAL" 9)
            (p6-sites "prim:COMMON-LISP::EQUAL" 5))
          (p6-literal-sites "rt:nil")))

(defthm p6-equal-early-rejection-returns
  (let* ((left (proof-world-reg 0 world)) (right (proof-world-reg 1 world))
         (sites (p6-equal-reject-sites left right)))
    (implies (and (p6-equal-early-rejects-p left right) (p6-path-entry-p sites base world))
             (p6-read-only-return-p *proof-nil* '(0 2) t sites world)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-equal-reject-sites p6-equal-early-rejects-p p6-literal-sites
                                                 p6-path-entry-p p6-path-end p6-read-only-return-p
                                                 p6-same-mapped-memory-p proof-word-tag)
                           (proof-segment-p p6-sites-placed-p))
           :use ((:instance p6-read-only-path-to-cut
                            (sites (p6-equal-reject-sites (proof-world-reg 0 world) (proof-world-reg 1 world)))
                            (cuts (list (proof-world-reg 30 world))))))))

(local
 (defthm p6-represented-even-word-has-datum-tag
   (implies (and (proof-value-p word value base objects packages machine) (not (oddp word)))
            (member-equal (proof-word-tag word) '(0 2 4)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-value-p proof-view) (p6-even-as-mod))
            :expand ((:free (depth) (proof-view-step :word word 0 depth base objects packages machine)))))))

(local
 (defthm p6-odd-value-view-is-canonical
   (implies (and (unsigned-byte-p 64 word) (oddp word) (proof-value-p word value base objects packages machine))
            (equal (proof-integer-word value) word))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-value-p) (p6-even-as-mod))
                   :use (p6-view-of-odd-word p6-odd-word-decodes-to-immediate)))))

(local
 (defthm p6-character-value-view-is-canonical
   (implies (and (unsigned-byte-p 64 word) (equal (proof-word-tag word) 4)
                 (proof-value-p word value base objects packages machine))
            (equal (proof-character-word value) word))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable proof-character-word proof-word-tag p6-unsigned-as-mod)
                   :use (p6-character-view-has-byte-code (:instance p6-mod-decomposition (x word) (d 8)))))))

(defthm p6-early-equality-rejection-agrees-with-core
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right)
                (proof-value-p left first base objects packages machine)
                (proof-value-p right second base objects packages machine)
                (p6-equal-early-rejects-p left right))
           (not (equal first second)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-equal-early-rejects-p p6-word-class p6-datum-class)
                           (p6-even-as-mod proof-immediate-integer-p proof-header-type proof-load-word))
           :use ((:instance p6-word-class-of-value (word left) (value first))
                 (:instance p6-word-class-of-value (word right) (value second))
                 (:instance p6-represented-even-word-has-datum-tag (word left) (value first))
                 (:instance p6-represented-even-word-has-datum-tag (word right) (value second))
                 (:instance p6-odd-value-view-is-canonical (word left) (value first))
                 (:instance p6-odd-value-view-is-canonical (word right) (value second))
                 (:instance p6-character-value-view-is-canonical (word left) (value first))
                 (:instance p6-character-value-view-is-canonical (word right) (value second))))))

(defthm p6-equal-early-rejection-runtime-contract
  (let* ((left (proof-world-reg 0 world)) (right (proof-world-reg 1 world))
         (sites (p6-equal-reject-sites left right)) (after (p6-path-end sites world))
         (args (list first second)))
    (implies (and (p6-equal-early-rejects-p left right)
                  (proof-runtime-pre-p 'equal args program labels code-base world objects packages)
                  (p6-path-entry-p sites runtime-base world))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p 'equal args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-read-only-return-p p6-boolean-views-p proof-reg-value-p
                              boymoo-model::core-primitive)
           :use ((:instance p6-runtime-pre-has-two-args (name 'equal))
                 p6-heap-has-boolean-views
                 (:instance p6-equal-early-rejection-returns (base runtime-base))
                 (:instance p6-runtime-pre-has-heap-and-first-arg (name 'equal) (args (list first second)))
                 (:instance p6-early-equality-rejection-agrees-with-core
                            (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world))
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance p6-read-only-datum-return
                            (before world) (sites (p6-equal-reject-sites (proof-world-reg 0 world) (proof-world-reg 1 world)))
                            (word *proof-nil*) (value nil) (clobbers '(0 2)) (flags t))
                 (:instance p6-equal-datum-frame-weakening
                            (before world) (clobbers '(0 2)) (datum nil)
                            (after (p6-path-end (p6-equal-reject-sites (proof-world-reg 0 world)
                                                                      (proof-world-reg 1 world)) world)))))))
