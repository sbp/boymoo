(in-package "BOYMOO-PROOFS")

(include-book "numeric-stack-paths")
(include-book "scratch-frame")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm p6-mapped-memory-is-transitive
   (implies (and (p6-same-mapped-memory-p first second) (p6-same-mapped-memory-p second third))
            (p6-same-mapped-memory-p first third))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable p6-same-mapped-memory-p)))))

(local
 (defthm p6-member-equal-of-append
   (iff (member-equal value (append first second))
        (or (member-equal value first) (member-equal value second)))))

(local
 (defthm p6-register-frame-compose
   (implies (and (proof-register-frame-p register first before middle)
                 (proof-register-frame-p register second middle after))
            (proof-register-frame-p register (append first second) before after))
   :rule-classes nil
   :hints (("Goal" :induct (proof-register-frame-p register first before middle)))))

(local
 (defthm p6-member-equal-after-removal
   (iff (member-equal value (remove-equal removed entries))
        (and (not (equal value removed)) (member-equal value entries)))
   :hints (("Goal" :induct (remove-equal removed entries)))))

(local
 (defthm p6-remove-restored-register-from-frame
   (implies (and (proof-register-frame-p register clobbers before after)
                 (equal (proof-world-reg restored before) (proof-world-reg restored after)))
            (proof-register-frame-p register (remove-equal restored clobbers) before after))
   :rule-classes nil
   :hints (("Goal" :induct (proof-register-frame-p register clobbers before after)))))

(local
 (defthm p6-end-of-concatenated-path
   (equal (p6-path-end (append sites tail) world)
          (p6-path-end tail (p6-path-end sites world)))
   :hints (("Goal" :induct (p6-path-end sites world) :in-theory (enable p6-path-end)))))

(local
 (defthm p6-header-address-for-numeric-word
   (implies (equal (proof-word-tag (proof-world-reg 0 world)) 2)
            (equal (p6-header-address world)
                   (proof-pointer-address (proof-world-reg 0 world) (proof-heap-base world))))
   :hints (("Goal" :in-theory (enable p6-header-address proof-pointer-address)))))

(local
 (defcong p6-memory-equiv equal (p6-projected-numeric-word name word base machine) 4
   :hints (("Goal" :in-theory (enable p6-projected-numeric-word p6-field-word)))))

(defthm p6-numeric-suffix-word-agrees-with-projection
  (let* ((word (proof-world-reg 0 world)) (base (proof-heap-base world))
         (address (proof-pointer-address word base)) (machine (proof-world-machine world))
         (type (p6-numeric-class word (proof-header-type (proof-load-word address machine)))))
    (implies (and (member-equal name *p6-numeric-projections*)
                  (implies (member-equal type '(4 5)) (equal (proof-world-reg 4 world) address)))
             (equal (p6-numeric-suffix-word name type world)
                    (p6-projected-numeric-word name word base machine))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable p6-numeric-suffix-word p6-projected-numeric-word
                                     p6-numeric-projection-field-offset p6-field-word
                                     p6-world-load proof-load-word))))

(defund p6-numeric-entered-world (name world)
  (p6-path-end (p6-numeric-prologue-sites name) world))

(defund p6-numeric-classifying-sites (world)
  (p6-number-class-sites (proof-world-reg 0 world) (p6-header-byte world)))

(defund p6-numeric-classified-world (world)
  (p6-path-end (p6-numeric-classifying-sites world) world))

(defund p6-numeric-restored-world (name world)
  (p6-path-end (p6-numeric-restore-sites name) (p6-numeric-classified-world (p6-numeric-entered-world name world))))

(defund p6-boxed-numeric-sites (name world)
  (let ((entered (p6-numeric-entered-world name world))
        (restored (p6-numeric-restored-world name world)))
    (append (p6-numeric-prologue-sites name)
            (p6-numeric-classifying-sites entered)
            (p6-numeric-restore-sites name)
            (p6-numeric-suffix-sites name (proof-world-reg 3 restored)))))

(defund p6-boxed-numeric-pre-p (name base world)
  (let* ((prologue (p6-numeric-prologue-sites name))
         (word (proof-world-reg 0 world))
         (entered (p6-numeric-entered-world name world))
         (classifying (p6-numeric-classifying-sites entered))
         (classified (p6-numeric-classified-world entered))
         (restored (p6-numeric-restored-world name world))
         (type (proof-world-reg 3 restored))
         (suffix (p6-numeric-suffix-sites name type))
         (offset (p6-numeric-projection-field-offset name type)))
    (and (member-equal name *p6-numeric-projections*) (not (oddp word))
         (p6-register-file-p world) (not (proof-world-stop world)) (<= 16 (p6-sp world))
         (equal (proof-world-pc world) (+ base (caar prologue)))
         (unsigned-byte-p 64 (p6-numeric-type-target base))
         (unsigned-byte-p 64 (+ base (caar (p6-numeric-restore-sites name))))
         (p6-path-entry-p classifying base entered)
         (or (not (equal (proof-word-tag (proof-world-reg 0 entered)) 2))
             (proof-covered-p (p6-header-address entered) 1 :read (proof-world-regions entered)))
         (p6-register-file-p classified)
         (p6-path-entry-p suffix base restored)
         (or (not offset)
             (proof-covered-p (boymoo-model::a64-unsigned 64 (+ (proof-world-reg 4 restored) offset))
                              8 :read (proof-world-regions restored)))
         (p6-checked-path-p (p6-boxed-numeric-sites name world) base (list (proof-world-reg 30 world)) world))))

(local
 (defthm p6-mapped-memory-gives-memory-equivalence
   (implies (p6-same-mapped-memory-p first second)
            (p6-memory-equiv (proof-world-machine first) (proof-world-machine second)))
   :rule-classes (:forward-chaining)
   :hints (("Goal" :in-theory (enable p6-same-mapped-memory-p p6-memory-equiv)))))

(local
 (defthm p6-boxed-numeric-call-state
   (let ((entered (p6-numeric-entered-world name world)))
     (implies (p6-boxed-numeric-pre-p name base world)
              (and (equal (proof-world-reg 0 entered) (proof-world-reg 0 world))
                   (equal (proof-heap-base entered) (proof-heap-base world))
                   (equal (p6-sp entered) (- (p6-sp world) 16))
                   (p6-same-mapped-memory-p (p6-numeric-save-world world) entered)
                   (equal (cdr world) (cdr entered))
                   (proof-register-frame-p 30 '(30) world entered))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-boxed-numeric-pre-p p6-numeric-entered-world)
                            (p6-path-end p6-checked-path-p proof-register-frame-p))
            :use (p6-numeric-prologue-saves-link-and-calls
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 0) (clobbers '(30)) (before world)
                             (after (p6-path-end (p6-numeric-prologue-sites name) world)))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 28) (clobbers '(30)) (before world)
                             (after (p6-path-end (p6-numeric-prologue-sites name) world))))))))

(local
 (defthm p6-boxed-numeric-classified-state
   (let* ((entered (p6-numeric-entered-world name world))
          (classified (p6-numeric-classified-world entered))
          (scratch (p6-numeric-save-world world))
          (word (proof-world-reg 0 world))
          (address (proof-pointer-address word (proof-heap-base world)))
          (header (proof-load-word address (proof-world-machine scratch))))
     (implies (p6-boxed-numeric-pre-p name base world)
              (and (equal (proof-world-reg 0 classified) word)
                   (equal (proof-heap-base classified) (proof-heap-base world))
                   (equal (p6-sp classified) (- (p6-sp world) 16))
                   (p6-same-mapped-memory-p scratch classified)
                   (equal (cdr world) (cdr classified))
                   (proof-register-frame-p 30 '(30 3 4 5) world classified)
                   (equal (proof-world-reg 3 classified) (p6-numeric-class word (proof-header-type header)))
                   (implies (equal (proof-word-tag word) 2)
                            (equal (proof-world-reg 4 classified) address)))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-boxed-numeric-pre-p p6-numeric-classified-world p6-numeric-classifying-sites
                                                   p6-read-only-return-p proof-frame-return-p)
                            (p6-path-end p6-checked-path-p proof-register-frame-p proof-segment-p
                             p6-loaded-header-fields))
            :use (p6-boxed-numeric-call-state
                  (:instance p6-numeric-type-entry-returns (world (p6-numeric-entered-world name world)))
                  (:instance p6-header-byte-is-header-type (world (p6-numeric-entered-world name world)))
                  (:instance p6-even-tag-is-not-an-immediate-integer (word (proof-world-reg 0 world)))
                  (:instance p6-mapped-memory-is-transitive
                             (first (p6-numeric-save-world world)) (second (p6-numeric-entered-world name world))
                             (third (p6-numeric-classified-world (p6-numeric-entered-world name world))))
                  (:instance p6-register-frame-compose
                             (register 30) (first '(30)) (second '(3 4 5)) (before world)
                             (middle (p6-numeric-entered-world name world))
                             (after (p6-numeric-classified-world (p6-numeric-entered-world name world))))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 28) (clobbers '(3 4 5))
                             (before (p6-numeric-entered-world name world))
                             (after (p6-numeric-classified-world (p6-numeric-entered-world name world))))))
           (and stable-under-simplificationp '(:in-theory (enable p6-numeric-class))))))

(local
 (defthm p6-boxed-numeric-restoration
   (let* ((entered (p6-numeric-entered-world name world))
          (classified (p6-numeric-classified-world entered))
          (restored (p6-numeric-restored-world name world)))
     (implies (p6-boxed-numeric-pre-p name base world)
              (and (equal (proof-world-reg 29 restored) (proof-world-reg 29 world))
                   (equal (proof-world-reg 30 restored) (proof-world-reg 30 world))
                   (equal (p6-sp restored) (p6-sp world))
                   (p6-same-mapped-memory-p (p6-numeric-save-world world) restored)
                   (equal (cdr world) (cdr restored))
                   (proof-register-frame-p 30 '(29 30) classified restored))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-boxed-numeric-pre-p p6-numeric-restored-world)
                            (p6-path-end p6-checked-path-p proof-register-frame-p))
            :use (p6-boxed-numeric-classified-state
                  (:instance p6-numeric-save-and-restore-agree
                             (before world)
                             (middle (p6-numeric-classified-world (p6-numeric-entered-world name world)))))))))

(local
 (defthm p6-boxed-numeric-suffix-selects-projection
   (let* ((restored (p6-numeric-restored-world name world))
          (type (proof-world-reg 3 restored))
          (scratch (p6-numeric-save-world world)))
     (implies (p6-boxed-numeric-pre-p name base world)
              (equal (p6-numeric-suffix-word name type restored)
                     (p6-projected-numeric-word name (proof-world-reg 0 world) (proof-heap-base world)
                                                (proof-world-machine scratch)))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-boxed-numeric-pre-p)
                            (p6-path-end p6-checked-path-p proof-register-frame-p p6-loaded-header-fields))
            :use (p6-boxed-numeric-classified-state p6-boxed-numeric-restoration
                  (:instance p6-numeric-suffix-word-agrees-with-projection (world (p6-numeric-restored-world name world)))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 0) (clobbers '(29 30))
                             (before (p6-numeric-classified-world (p6-numeric-entered-world name world)))
                             (after (p6-numeric-restored-world name world)))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 3) (clobbers '(29 30))
                             (before (p6-numeric-classified-world (p6-numeric-entered-world name world)))
                             (after (p6-numeric-restored-world name world)))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 4) (clobbers '(29 30))
                             (before (p6-numeric-classified-world (p6-numeric-entered-world name world)))
                             (after (p6-numeric-restored-world name world)))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 28) (clobbers '(29 30))
                             (before (p6-numeric-classified-world (p6-numeric-entered-world name world)))
                             (after (p6-numeric-restored-world name world)))))
           (and stable-under-simplificationp '(:in-theory (enable p6-numeric-class))))))

(local
 (defthm p6-boxed-numeric-restored-frame
   (implies (p6-boxed-numeric-pre-p name base world)
            (proof-register-frame-p 30 '(3 4 5) world (p6-numeric-restored-world name world)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (disable proof-register-frame-p)
            :use (p6-boxed-numeric-classified-state p6-boxed-numeric-restoration
                  (:instance p6-register-frame-compose
                             (register 30) (first '(30 3 4 5)) (second '(29 30)) (before world)
                             (middle (p6-numeric-classified-world (p6-numeric-entered-world name world)))
                             (after (p6-numeric-restored-world name world)))
                  (:instance p6-remove-restored-register-from-frame
                             (register 30) (restored 29) (clobbers '(30 3 4 5 29 30)) (before world)
                             (after (p6-numeric-restored-world name world)))
                  (:instance p6-remove-restored-register-from-frame
                             (register 30) (restored 30) (clobbers '(30 3 4 5 30)) (before world)
                             (after (p6-numeric-restored-world name world))))))))

(local
 (defthm p6-projection-clobber-order
   (equal (proof-register-frame-p register '(3 4 5 0) before after)
          (proof-register-frame-p register '(0 3 4 5) before after))
   :hints (("Goal" :induct (proof-register-frame-p register '(3 4 5 0) before after)))))

(local
 (defthm p6-boxed-numeric-finish
   (let* ((restored (p6-numeric-restored-world name world))
          (type (proof-world-reg 3 restored))
          (suffix (p6-numeric-suffix-sites name type))
          (after (p6-path-end suffix restored))
          (scratch (p6-numeric-save-world world)))
     (implies (p6-boxed-numeric-pre-p name base world)
              (and (proof-frame-return-p '(0 3 4 5) t world after)
                   (p6-same-mapped-memory-p scratch after)
                   (equal (cdr world) (cdr after))
                   (equal (proof-world-reg 0 after)
                          (p6-projected-numeric-word name (proof-world-reg 0 world) (proof-heap-base world)
                                                     (proof-world-machine scratch))))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-boxed-numeric-pre-p p6-read-only-return-p proof-frame-return-p)
                            (p6-path-end p6-checked-path-p proof-segment-p proof-register-frame-p))
            :use (p6-boxed-numeric-restoration p6-boxed-numeric-suffix-selects-projection p6-boxed-numeric-restored-frame
                  (:instance p6-numeric-projection-continuations-return
                             (world (p6-numeric-restored-world name world)))
                  (:instance p6-mapped-memory-is-transitive
                             (first (p6-numeric-save-world world)) (second (p6-numeric-restored-world name world))
                             (third (p6-path-end (p6-numeric-suffix-sites name
                                                                         (proof-world-reg 3 (p6-numeric-restored-world name world)))
                                                 (p6-numeric-restored-world name world))))
                  (:instance p6-register-frame-compose
                             (register 30) (first '(3 4 5)) (second '(0)) (before world)
                             (middle (p6-numeric-restored-world name world))
                             (after (p6-path-end (p6-numeric-suffix-sites name
                                                                         (proof-world-reg 3 (p6-numeric-restored-world name world)))
                                                 (p6-numeric-restored-world name world)))))))))

(defthm p6-boxed-numeric-projection-runs
  (let* ((sites (p6-boxed-numeric-sites name world))
         (after (p6-path-end sites world))
         (scratch (p6-numeric-save-world world)))
    (implies (p6-boxed-numeric-pre-p name base world)
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-frame-return-p '(0 3 4 5) t world after)
                  (p6-same-mapped-memory-p scratch after)
                  (equal (cdr world) (cdr after))
                  (equal (proof-world-reg 0 after)
                         (p6-projected-numeric-word name (proof-world-reg 0 world) (proof-heap-base world)
                                                    (proof-world-machine scratch))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-boxed-numeric-pre-p p6-boxed-numeric-sites p6-numeric-restored-world
                                                   p6-numeric-classified-world p6-numeric-entered-world
                                                   proof-segment-p proof-frame-return-p)
                           (p6-checked-path-p (:definition p6-path-end) (:definition binary-append)
                            proof-register-frame-p))
           :use (p6-boxed-numeric-finish
                 (:instance p6-checked-path-runs (sites (p6-boxed-numeric-sites name world))
                            (cuts (list (proof-world-reg 30 world))))))))

(local
 (defcong p6-heap-world-equiv equal (proof-memory-span-agrees-p start end before after) 4
   :hints (("Goal" :in-theory (enable p6-heap-world-equiv p6-memory-equiv)))))

(local
 (defcong p6-heap-world-equiv equal (proof-fixed-external-p mappings before after) 3
   :hints (("Goal" :induct (proof-fixed-external-p mappings before after)
                   :in-theory (disable proof-memory-span-agrees-p)))))

(local
 (defcong p6-heap-world-equiv equal (proof-fixed-heap-p before after objects) 2
   :hints (("Goal"
            :in-theory (disable proof-external-objects proof-fixed-external-p proof-memory-span-agrees-p
                                proof-runtime-word)))))

(local
 (defcong p6-heap-world-equiv equal
   (proof-preserved-heap-p may-intern before after old-objects new-objects packages) 3
   :hints (("Goal"
            :in-theory (disable proof-memory-span-agrees-p proof-heap-p proof-stack-prefix proof-dynamic-view
                                proof-dynamic-entries proof-runtime-word proof-static-size)))))

(local
 (defthm p6-numeric-return-has-scratch-world-heap
   (implies (and (proof-frame-return-p '(0 3 4 5) t world after)
                 (p6-same-mapped-memory-p (p6-numeric-save-world world) after)
                 (equal (cdr world) (cdr after)))
            (p6-heap-world-equiv (p6-numeric-save-world world) after))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (p6-heap-world-equiv proof-frame-return-p p6-numeric-save-world
                                                 p6-store-register-pair)
                            (proof-register-frame-p p6-stored-word-memory))
            :use ((:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 23) (clobbers '(0 3 4 5)) (before world))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 24) (clobbers '(0 3 4 5)) (before world))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 25) (clobbers '(0 3 4 5)) (before world))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 26) (clobbers '(0 3 4 5)) (before world))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 27) (clobbers '(0 3 4 5)) (before world))
                  (:instance p6-frame-preserves-unlisted-register
                             (max 30) (register 28) (clobbers '(0 3 4 5)) (before world)))))))

(defund p6-numeric-scratch-preserves-observations-p (value world objects packages)
  (let ((scratch (p6-numeric-save-world world)))
    (and (proof-preserved-heap-p nil world scratch objects objects packages)
         (proof-fixed-heap-p world scratch objects)
         (proof-reg-value-p 0 value scratch objects packages))))

(local
 (defthm p6-numeric-save-world-preserves-input-registers
   (equal (proof-world-reg register (p6-numeric-save-world world)) (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable p6-numeric-save-world p6-store-register-pair)))))

(defthm p6-boxed-numeric-projections-runtime-contract
  (let* ((sites (p6-boxed-numeric-sites name world))
         (after (p6-path-end sites world))
         (args (list value)))
    (implies (and (p6-boxed-numeric-pre-p name runtime-base world)
                  (proof-runtime-pre-p name args program labels code-base world objects packages)
                  (p6-numeric-scratch-preserves-observations-p value world objects packages))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p name args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-boxed-numeric-pre-p p6-numeric-scratch-preserves-observations-p
                                                   proof-reg-value-p proof-datum-return-p boymoo-model::core-primitive)
                           (p6-path-end p6-checked-path-p proof-fixed-heap-p proof-preserved-heap-p
                            proof-register-frame-p proof-segment-p))
           :use ((:instance p6-boxed-numeric-projection-runs (base runtime-base))
                 (:instance p6-numeric-return-has-scratch-world-heap
                            (after (p6-path-end (p6-boxed-numeric-sites name world) world)))
                 (:instance p6-numeric-projection-word-agrees-with-core
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine (p6-numeric-save-world world))))))))

(defthm p6-boxed-numeric-projections-with-machine-save-room
  (let* ((sites (p6-boxed-numeric-sites name world))
         (after (p6-path-end sites world))
         (scratch (p6-numeric-save-world world))
         (args (list value)))
    (implies (and (p6-boxed-numeric-pre-p name runtime-base world)
                  (proof-runtime-pre-p name args program labels code-base world objects packages)
                  (p6-machine-save-room-p world)
                  (proof-preserved-heap-p nil world scratch objects objects packages)
                  (proof-reg-value-p 0 value scratch objects packages))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p name args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-numeric-scratch-preserves-observations-p p6-numeric-save-world)
                           (proof-fixed-heap-p proof-preserved-heap-p proof-segment-p proof-runtime-return-p))
           :use (p6-boxed-numeric-projections-runtime-contract
                 (:instance p6-runtime-pre-has-heap-and-first-arg (args (list value)))
                 (:instance p6-machine-save-pair-leaves-heap-fixed (first 29) (second 30))))))
