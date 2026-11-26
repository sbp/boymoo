(in-package "BOYMOO-PROOFS")

(include-book "coerce-list-layout")
(include-book "cons-views")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-backward-copy-ranks-p (prefix cell first-rank objects)
  (declare (xargs :measure (nfix prefix)))
  (if (zp prefix)
      t
    (let* ((index (1- prefix))
           (address (+ cell (* 16 index))))
      (and (equal (assoc-equal address objects)
                  (proof-object address :active :cons (+ first-rank index)))
           (sequence-backward-copy-ranks-p index cell first-rank objects)))))

(defun sequence-backward-copy-root (prefix cell tail base)
  (if (zp prefix)
      tail
    (sequence-cell-word (+ cell (* 16 (1- prefix))) base)))

(defun sequence-read-characters-onto-list (count address memory tail)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      tail
    (cons (code-char (boymoo-model::a64-byte address memory))
          (sequence-read-characters-onto-list (1- count) (+ 1 address) memory tail))))

(local
 (defthm sequence-read-characters-onto-list-is-appended-view
   (implies (integerp address)
            (equal (sequence-read-characters-onto-list
                    count address (boymoo-model::a64-memory machine) tail)
                   (append (coerce (proof-load-string count address machine) 'list) tail)))
   :hints (("Goal"
            :in-theory (disable proof-load-string)
            :induct (sequence-read-characters-onto-list count address
                                                       (boymoo-model::a64-memory machine) tail)
            :expand ((proof-byte-list count address machine))))))

(local
 (defthm sequence-backward-copy-last-record
   (implies (and (posp prefix) (sequence-backward-copy-ranks-p prefix cell first-rank objects))
            (and (equal (assoc-equal (+ cell (* 16 (1- prefix))) objects)
                        (proof-object (+ cell (* 16 (1- prefix))) :active :cons
                                      (+ first-rank (1- prefix))))
                 (sequence-backward-copy-ranks-p (1- prefix) cell first-rank objects)))
   :hints (("Goal" :expand ((sequence-backward-copy-ranks-p prefix cell first-rank objects))))))

(local
 (defthm sequence-backward-cell-is-in-span
   (implies (and (natp index) (natp count) (< index count)
                 (proof-span-p cell (* 16 count))
                 (natp base) (<= base cell) (equal (mod (- cell base) 8) 0))
            (let ((address (+ cell (* 16 index))))
              (and (proof-span-p address 16)
                   (<= base address)
                   (equal (mod (- address base) 8) 0))))
   :hints (("Goal"
            :in-theory (disable sequence-mod-add-multiple)
            :use ((:instance sequence-mod-add-multiple
                             (value (- cell base)) (divisor 8) (multiple (* 2 index)))
                  (:instance associativity-of-* (acl2::x 8) (acl2::y 2) (acl2::z index))
                  (:instance sequence-cons-iteration-extent (first cell)))))
   :rule-classes nil))

(local
 (defthm sequence-backward-copy-tail-view-at-next-rank
   (let* ((index (1- prefix))
          (root (sequence-backward-copy-root index cell tail base))
          (rank (+ first-rank index)))
     (implies (and (posp prefix) (natp first-rank)
                   (proof-span-p cell (* 16 prefix))
                   (natp base) (<= base cell) (equal (mod (- cell base) 8) 0)
                   (sequence-backward-copy-ranks-p prefix cell first-rank objects)
                   (equal (proof-view-step :word tail 0 first-rank base objects packages machine)
                          (proof-value-view tail-value))
                   (proof-value-p root datum base objects packages machine)
                   (implies (equal prefix 1) (equal datum tail-value)))
              (equal (proof-view-step :word root 0 rank base objects packages machine)
                     (proof-value-view datum))))
   :hints
   (("Goal"
     :in-theory (disable proof-view-step proof-value-p proof-pointer-address proof-word-tag
                         sequence-backward-copy-ranks-p sequence-cell-word oddp)
     :cases ((equal prefix 1))
     :use ((:instance sequence-backward-copy-last-record)
           (:instance sequence-backward-copy-last-record (prefix (1- prefix)))
           (:instance sequence-backward-cell-is-in-span (index (+ -2 prefix)) (count prefix))
           (:instance sequence-cell-word-is-relative-pointer (cell (+ cell (* 16 (+ -2 prefix)))))
           (:instance sequence-datum-view-at-sufficient-rank
                      (word (sequence-backward-copy-root (1- prefix) cell tail base))
                      (depth (+ first-rank (1- prefix)))))))
   :rule-classes nil))

(local
 (defun sequence-copy-prefix-induction (prefix)
   (if (zp prefix)
       nil
     (sequence-copy-prefix-induction (1- prefix)))))

(local
 (defthm sequence-coerce-list-prefix-after-copy
   (let* ((finished (sequence-coerce-list-copy-memory count source cell tail base memory))
          (root (sequence-backward-copy-root prefix cell tail base))
          (value (sequence-read-characters-onto-list prefix (+ source count (- prefix))
                                                      memory tail-value)))
     (implies (and (natp prefix) (natp count) (<= prefix count)
                   (natp first-rank)
                   (proof-span-p source count) (proof-span-p cell (* 16 count))
                   (natp base) (<= base cell) (equal (mod (- cell base) 8) 0)
                   (unsigned-byte-p 64 tail)
                   (proof-disjoint-p source (+ source count) cell (+ cell (* 16 count)))
                   (equal (boymoo-model::a64-memory machine) finished)
                   (equal (proof-view-step :word tail 0 first-rank base objects packages machine)
                          (proof-value-view tail-value))
                   (sequence-backward-copy-ranks-p prefix cell first-rank objects))
              (proof-value-p root value base objects packages machine)))
   :hints
   (("Goal"
     :induct (sequence-copy-prefix-induction prefix)
     :in-theory (e/d (proof-load-word)
                     (proof-view-step proof-value-p proof-pointer-address proof-word-tag
                      proof-disjoint-p sequence-coerce-list-copy-memory sequence-cell-word
                      sequence-backward-copy-last-record
                      (:definition sequence-backward-copy-ranks-p))))
    ("Subgoal *1/1"
     :use ((:instance sequence-value-view-at-its-own-rank
                      (word tail) (datum tail-value) (depth first-rank))))
    ("Subgoal *1/2"
     :expand ((sequence-read-characters-onto-list prefix (+ source count (- prefix)) memory tail-value))
     :use ((:instance sequence-backward-copy-last-record)
           (:instance sequence-backward-cell-is-in-span (index (1- prefix)))
           (:instance sequence-cell-word-is-relative-pointer (cell (+ cell (* 16 (1- prefix)))))
           (:instance sequence-coerce-list-cell-contents (index (1- prefix)))
           (:instance sequence-backward-copy-tail-view-at-next-rank
                      (datum (sequence-read-characters-onto-list
                              (1- prefix) (+ source count (- (1- prefix))) memory tail-value)))
           (:instance sequence-character-view-at-any-rank
                      (byte (boymoo-model::a64-byte (+ source count (- prefix)) memory))
                      (depth (+ first-rank (1- prefix))))
           (:instance sequence-cons-value-from-ranked-fields
                      (word (sequence-backward-copy-root prefix cell tail base))
                      (first (code-char (boymoo-model::a64-byte (+ source count (- prefix)) memory)))
                      (rest (sequence-read-characters-onto-list
                             (1- prefix) (+ source count (- (1- prefix))) memory tail-value))))))
   :rule-classes nil))

(local
 (defthm sequence-copy-register-and-base-are-natural
   (and (natp (proof-world-reg 5 world)) (natp (proof-heap-base world)))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-heap-base)))
   :rule-classes nil))

(defthm sequence-coerce-list-copy-source-value
  (let* ((first (proof-world-machine before))
         (source (proof-world-reg 1 before))
         (cell (proof-world-reg 5 before))
         (base (proof-heap-base before))
         (path (sequence-coerce-list-copy-path count))
         (after (sequence-execute path before))
         (last (proof-world-machine after))
         (cuts (list (+ 32 (proof-world-pc before)))))
    (implies
     (and (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers first))
          (equal (proof-world-reg 2 before) count)
          (equal (proof-world-reg 0 before) *proof-nil*)
          (posp count) (natp first-rank)
          (equal datum (proof-load-string count source first))
          (proof-span-p source count)
          (unsigned-byte-p 64 (+ cell (* 16 count)))
          (unsigned-byte-p 64 (+ 32 (proof-world-pc before)))
          (<= base cell) (equal (mod (- cell base) 8) 0)
          (proof-disjoint-p source (+ source count) cell (+ cell (* 16 count)))
          (equal (proof-view-step :word *proof-nil* 0 first-rank base objects packages last)
                 (proof-value-view nil))
          (sequence-backward-copy-ranks-p count cell first-rank objects)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (* 8 count) cuts before :cut after)
          (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                             objects packages last)
                 (boymoo-model::core-primitive 'coerce (list datum 'list) program)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-value-p)
                    (proof-view proof-view-step proof-load-string sequence-core-coerce
                     proof-world-machine proof-world-reg proof-world-pc proof-heap-base
                     sequence-cell-word sequence-execute proof-segment-p
                     sequence-coerce-list-copy-memory sequence-coerce-list-copy-path
                     sequence-backward-copy-ranks-p sequence-read-characters-onto-list))
    :use (sequence-coerce-list-copy-segment sequence-coerce-list-copy-effects
          (:instance sequence-copy-register-and-base-are-natural (world before))
          (:instance sequence-core-coerce (result-type 'list))
          (:instance sequence-coerce-list-prefix-after-copy
                     (prefix count) (source (proof-world-reg 1 before)) (cell (proof-world-reg 5 before))
                     (tail *proof-nil*) (tail-value nil) (base (proof-heap-base before))
                     (memory (boymoo-model::a64-memory (proof-world-machine before)))
                     (machine (proof-world-machine
                               (sequence-execute (sequence-coerce-list-copy-path count) before)))))))
  :rule-classes nil)
