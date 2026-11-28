(in-package "BOYMOO-PROOFS")

(include-book "expansions")
(include-book "memory-encodings")
(include-book "effects")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-world-machine proof-world-regions
                           proof-decode proof-decode-agrees-with-model
                           proof-instruction-at-p proof-instructions-at-p
                           assembly-layout-input-p assembly-labels assembly-labels-after-prefix
                           boymoo-compiler::a64-layout
                           boymoo-compiler::a64-assemble-image
                           boymoo-compiler::a64-word
                           boymoo-compiler::a64-image-item-size
                           floor mod)))

(defthm assembly-coverage-of-subspan
  (implies (and (proof-covered-p base size access regions)
                (natp base) (natp size) (natp offset) (posp count)
                (<= (+ offset count) size))
           (proof-covered-p (+ base offset) count access regions))
  :hints (("Goal" :induct (proof-covered-p base size access regions)
                  :in-theory (disable proof-region-allows-p)))
  :rule-classes nil)

(local
 (defthm assembly-aligned-next-word
   (implies (and (integerp address) (equal (mod address 4) 0))
            (equal (mod (+ 4 address) 4) 0))
   :hints (("Goal"
            :use ((:instance assembly-floor-unique
                             (x (+ 4 address)) (d 4) (q (+ 1 (floor address 4)))))
            :in-theory (enable mod)))))

(local
 (defthm assembly-page-aligned-is-word-aligned
   (implies (and (integerp address) (equal (mod address 4096) 0))
            (equal (mod address 4) 0))
   :hints (("Goal"
            :use ((:instance assembly-floor-unique
                             (x address) (d 4) (q (* 1024 (floor address 4096)))))
            :in-theory (enable mod)))))

(local
 (defthm assembly-sum-of-word-aligned-addresses
   (implies (and (integerp address) (integerp offset)
                 (equal (mod address 4) 0) (equal (mod offset 4) 0))
            (equal (mod (+ address offset) 4) 0))
   :hints (("Goal"
            :use ((:instance assembly-floor-unique
                             (x (+ address offset)) (d 4) (q (+ (floor address 4) (floor offset 4)))))
            :in-theory (enable mod)))))

(local
 (defthm assembly-nonempty-length
   (implies (consp words) (<= 1 (len words)))
   :hints (("Goal" :expand ((len words))))
   :rule-classes :linear))

(defthm assembly-covered-span-supplies-fetches
  (implies (and (true-listp words) (natp address)
                (proof-covered-p address (* 4 (len words)) :execute (proof-world-regions world))
                (equal (mod address 4) 0))
           (assembly-word-fetches-p words address world))
  :hints (("Goal" :induct (assembly-word-fetches-p words address world)
                  :in-theory (disable proof-covered-p))
          ("Subgoal *1/3"
           :use ((:instance assembly-coverage-of-subspan
                            (base address) (size (* 4 (len words))) (access :execute)
                            (regions (proof-world-regions world)) (offset 0) (count 4)))
           :in-theory (disable proof-covered-p))
          ("Subgoal *1/2"
           :use ((:instance assembly-coverage-of-subspan
                            (base address) (size (* 4 (len words))) (access :execute)
                            (regions (proof-world-regions world)) (offset 0) (count 4))
                 (:instance assembly-coverage-of-subspan
                            (base address) (size (* 4 (len words))) (access :execute)
                            (regions (proof-world-regions world)) (offset 4)
                            (count (* 4 (len (cdr words))))))
           :in-theory (disable proof-covered-p))))

(defun assembly-code-item-p (item)
  (not (member-eq (car item) '(:label :image :bytes :quad))))

(local
 (defthm assembly-code-characters-are-word-characters
   (implies (assembly-code-item-p item)
            (equal (assembly-item-characters item pc labels)
                   (assembly-words-characters (assembly-item-words item pc labels))))
   :hints (("Goal" :in-theory (disable assembly-item-words)))))

(local
 (defthm assembly-code-item-size
   (implies (assembly-code-item-p item)
            (equal (boymoo-compiler::a64-image-item-size item)
                   (* 4 (len (assembly-item-words item pc labels)))))
   :hints (("Goal"
            :use (assembly-item-character-count)
            :in-theory (disable assembly-item-character-count
                                assembly-item-characters assembly-item-words
                                assembly-words-characters assembly-word-characters)))
   :rule-classes nil))

(local
 (defthm assembly-size-is-natural-for-data
   (implies (assembly-data-list-p items) (natp (assembly-size items)))
   :hints (("Goal" :use ((:instance assembly-items-character-count (pc 0) (labels nil)))
                   :in-theory (disable assembly-items-character-count assembly-items-characters)))))

(local
 (defthm assembly-size-of-cons
   (equal (assembly-size (cons item suffix))
          (+ (boymoo-compiler::a64-image-item-size item) (assembly-size suffix)))))

(local
 (defthm assembly-code-item-has-positive-size
   (implies (assembly-code-item-p item)
            (posp (boymoo-compiler::a64-image-item-size item)))
   :hints (("Goal" :in-theory (enable boymoo-compiler::a64-image-item-size)))))

(local
 (defthm assembly-data-list-p-of-link-append
   (equal (assembly-data-list-p (append prefix suffix))
          (and (assembly-data-list-p prefix) (assembly-data-list-p suffix)))))

(local
 (defthm assembly-data-list-p-of-link-cons
   (equal (assembly-data-list-p (cons item suffix))
          (and (assembly-data-p item) (assembly-data-list-p suffix)))))

(local
 (defthm assembly-words-p-is-true-list
   (implies (assembly-words-p words) (true-listp words))))

(local
 (defthm assembly-linked-image-span
   (implies (and (assembly-layout-input-p items 0 nil ranks)
                 (assembly-data-list-p items)
                 (assoc-equal entry (assembly-labels items 0))
                 (proof-linked-image-p items entry base world))
            (and (natp base) (equal (mod base 4096) 0)
                 (natp (assembly-size items))
                 (proof-covered-p base (assembly-size items) :execute
                                  (proof-world-regions world))))
   :hints (("Goal"
            :use (assembly-flattened-image)
            :in-theory (disable assembly-flattened-image assembly-items-characters
                                assembly-size assembly-data-list-p proof-fragments-at-p
                                proof-covered-p proof-fragments-p)))
   :rule-classes nil))

(local
 (defthm assembly-item-offset-span
   (implies (and (assembly-data-list-p prefix) (assembly-data-list-p suffix)
                 (assembly-code-item-p item))
            (let* ((offset (assembly-size prefix))
                   (count (* 4 (len (assembly-item-words item offset labels))))
                   (size (assembly-size (append prefix (cons item suffix)))))
              (and (natp offset) (posp count) (<= (+ offset count) size))))
   :hints (("Goal" :use ((:instance assembly-code-item-size (pc (assembly-size prefix)))
                         (:instance assembly-size-is-natural-for-data (items prefix))
                         (:instance assembly-size-is-natural-for-data (items suffix)))
                   :in-theory (disable assembly-size assembly-item-words assembly-code-item-p
                                       assembly-size-is-natural-for-data
                                       assembly-data-list-p)))
   :rule-classes nil))

(defthm assembly-linked-item-instructions
  (let* ((items (append prefix (cons item suffix)))
         (offset (assembly-size prefix))
         (labels (mv-nth 1 (boymoo-compiler::a64-layout items 0 nil nil)))
         (words (assembly-item-words item offset labels)))
    (implies (and (assembly-layout-input-p items 0 nil ranks)
                  (assembly-data-list-p items)
                  (assoc-equal entry (assembly-labels items 0))
                  (proof-linked-image-p items entry base world)
                  (assembly-code-item-p item)
                  (equal (mod offset 4) 0)
                  (assembly-words-p words))
             (proof-instructions-at-p
              (assembly-decode-words words) (+ base offset) world)))
  :hints (("Goal"
           :use ((:instance assembly-linked-image-places-item)
                 (:instance assembly-linked-image-span (items (append prefix (cons item suffix))))
                 (:instance assembly-item-offset-span
                            (labels (mv-nth 1 (boymoo-compiler::a64-layout
                                              (append prefix (cons item suffix)) 0 nil nil))))
                 (:instance assembly-coverage-of-subspan
                            (size (assembly-size (append prefix (cons item suffix))))
                            (access :execute) (regions (proof-world-regions world))
                            (offset (assembly-size prefix))
                            (count (* 4 (len (assembly-item-words
                                              item (assembly-size prefix)
                                              (mv-nth 1 (boymoo-compiler::a64-layout
                                                        (append prefix (cons item suffix)) 0 nil nil)))))))
                 (:instance assembly-covered-span-supplies-fetches
                            (address (+ base (assembly-size prefix)))
                            (words (assembly-item-words item (assembly-size prefix)
                                                       (mv-nth 1 (boymoo-compiler::a64-layout
                                                                 (append prefix (cons item suffix)) 0 nil nil)))))
                 (:instance assembly-fetch-serialized-words
                            (address (+ base (assembly-size prefix)))
                            (words (assembly-item-words item (assembly-size prefix)
                                                       (mv-nth 1 (boymoo-compiler::a64-layout
                                                                 (append prefix (cons item suffix)) 0 nil nil))))))
           :in-theory (disable assembly-linked-image-places-item proof-linked-image-p
                               assembly-covered-span-supplies-fetches assembly-fetch-serialized-words
                               assembly-size assembly-data-list-p assembly-word-fetches-p
                               assembly-characters-at-p assembly-words-characters
                               proof-fragments-at-p proof-fragments-p
                               assembly-item-words assembly-item-characters assembly-code-item-p
                               proof-covered-p))))

(local
 (defthm assembly-head-decode-placed
   (implies (and (consp words)
                 (proof-instructions-at-p (assembly-decode-words words) address world))
            (proof-instruction-at-p (proof-decode (car words)) address world))
   :hints (("Goal" :expand ((assembly-decode-words words)
                            (:free (first rest)
                              (proof-instructions-at-p (cons first rest) address world)))))
   :rule-classes nil))

(defthm assembly-linked-item-first-step
  (let* ((items (append prefix (cons item suffix)))
         (offset (assembly-size prefix))
         (labels (mv-nth 1 (boymoo-compiler::a64-layout items 0 nil nil)))
         (words (assembly-item-words item offset labels))
         (instruction (proof-decode (car words))))
    (implies (and (assembly-layout-input-p items 0 nil ranks)
                  (assembly-data-list-p items)
                  (assoc-equal entry (assembly-labels items 0))
                  (proof-linked-image-p items entry base world)
                  (assembly-code-item-p item)
                  (equal (mod offset 4) 0)
                  (assembly-words-p words) (consp words)
                  (equal (proof-world-pc world) (+ base offset))
                  (not (proof-world-stop world))
                  (proof-instruction-access-p instruction world))
             (equal (proof-step world) (proof-instruction-effect instruction world))))
  :hints (("Goal"
           :use (assembly-linked-item-instructions
                 (:instance assembly-head-decode-placed
                            (address (+ base (assembly-size prefix)))
                            (words (assembly-item-words item (assembly-size prefix)
                                     (mv-nth 1 (boymoo-compiler::a64-layout
                                               (append prefix (cons item suffix)) 0 nil nil)))))
                 (:instance proof-step-from-instruction
                            (instruction (proof-decode
                                          (car (assembly-item-words
                                                item (assembly-size prefix)
                                                (mv-nth 1
                                                  (boymoo-compiler::a64-layout
                                                   (append prefix (cons item suffix)) 0 nil nil))))))))
           :in-theory (disable assembly-linked-item-instructions
                            proof-linked-image-p proof-step-from-instruction
                            proof-step proof-world-pc proof-world-stop
                            proof-instruction-access-p proof-instruction-effect
                            assembly-item-words assembly-code-item-p
                            assembly-data-list-p assembly-data-p assembly-size))))

(local
 (defthm assembly-model-decode-outside-word-range
   (implies (not (unsigned-byte-p 32 word))
            (equal (boymoo-model::a64-decode word) :undefined))))

(local
 (defthm assembly-decoded-word-fits
   (implies (consp (proof-decode word))
            (unsigned-byte-p 32 word))
   :hints (("Goal" :in-theory (e/d (proof-decode) (boymoo-model::a64-decode))))))

(defun assembly-decoded-list-p (instructions)
  (if (atom instructions)
      (null instructions)
    (and (consp (car instructions))
         (assembly-decoded-list-p (cdr instructions)))))

(local
 (defthm assembly-decode-implies-word-list
   (implies (and (true-listp words) (assembly-decoded-list-p (assembly-decode-words words)))
            (assembly-words-p words))
   :hints (("Goal" :induct (assembly-decode-words words)))))

(local
 (defthm assembly-item-words-is-a-list
   (true-listp (assembly-item-words item offset labels))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (disable boymoo-compiler::a64-zero-source-words
                                      boymoo-compiler::a64-offset)))))

(defun assembly-linked-item-input-p (prefix item suffix entry base world ranks)
  (let ((items (append prefix (cons item suffix))))
    (and (assembly-layout-input-p items 0 nil ranks)
         (assembly-data-list-p items)
         (assoc-equal entry (assembly-labels items 0))
         (proof-linked-image-p items entry base world)
         (assembly-code-item-p item)
         (equal (mod (assembly-size prefix) 4) 0))))

(defun assembly-linked-item-words (prefix item suffix)
  (mv-let (size labels reversed)
    (boymoo-compiler::a64-layout (append prefix (cons item suffix)) 0 nil nil)
    (declare (ignore size reversed))
    (assembly-item-words item (assembly-size prefix) labels)))

(defthm assembly-linked-specified-instructions
  (implies (and (assembly-linked-item-input-p prefix item suffix entry base world ranks)
                (assembly-decoded-list-p instructions)
                (equal (assembly-decode-words (assembly-linked-item-words prefix item suffix))
                       instructions))
           (proof-instructions-at-p instructions (+ base (assembly-size prefix)) world))
  :hints (("Goal"
           :use (assembly-linked-item-instructions
                 (:instance assembly-decode-implies-word-list
                            (words (assembly-linked-item-words prefix item suffix))))
           :in-theory (disable assembly-linked-item-instructions assembly-decode-implies-word-list
                               assembly-decoded-list-p assembly-item-words
                               assembly-size assembly-data-list-p assembly-data-p
                               proof-linked-image-p assembly-code-item-p))))

(defthm assembly-linked-single-instruction-step
  (let ((address (+ base (assembly-size prefix))))
    (implies (and (assembly-linked-item-input-p prefix item suffix entry base world ranks)
                  (consp instruction)
                  (equal (assembly-decode-words (assembly-linked-item-words prefix item suffix))
                         (list instruction))
                  (not (proof-world-stop world))
                  (equal (proof-world-pc world) address)
                  (proof-instruction-access-p instruction world))
             (and (proof-instruction-at-p instruction address world)
                  (equal (proof-step world) (proof-instruction-effect instruction world)))))
  :hints (("Goal"
           :use ((:instance assembly-linked-specified-instructions (instructions (list instruction)))
                 proof-step-from-instruction)
           :in-theory (e/d (proof-instructions-at-p)
                           (assembly-linked-specified-instructions proof-step-from-instruction
                            assembly-linked-item-input-p assembly-linked-item-words
                            proof-world-pc proof-world-stop proof-step
                            proof-instruction-access-p proof-instruction-effect)))))

(local
 (defthm assembly-register-instruction-is-cons
   (implies (assembly-register-instruction-p instruction) (consp instruction))))

(local
 (defthm assembly-register-pair-is-decoded-list
   (implies (and (assembly-register-instruction-p first)
                 (assembly-register-instruction-p second))
            (assembly-decoded-list-p (list first second)))
   :hints (("Goal" :in-theory (disable assembly-register-instruction-p)))
   :rule-classes nil))

(defthm assembly-linked-two-register-instructions-run
  (let ((address (+ base (assembly-size prefix))))
    (implies (and (assembly-linked-item-input-p prefix item suffix entry base before ranks)
                  (equal (assembly-decode-words (assembly-linked-item-words prefix item suffix))
                         (list first second))
                  (assembly-register-instruction-p first)
                  (assembly-register-instruction-p second)
                  (not (equal (car (proof-world-machine before)) :svc))
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) address)
                  (natp address) (< (+ address 4) (expt 2 64))
                  (not (member-equal address cuts))
                  (not (member-equal (+ address 4) cuts))
                  (member-equal (boymoo-model::a64-unsigned 64 (+ address 8)) cuts))
             (proof-segment-p
              2 cuts before :cut (assembly-straight-line-effect (list first second) before))))
  :hints (("Goal"
           :use (assembly-register-pair-is-decoded-list
                 (:instance assembly-linked-specified-instructions
                            (world before) (instructions (list first second)))
                 (:instance assembly-two-register-instructions-run
                            (address (+ base (assembly-size prefix)))))
           :in-theory (theory 'acl2::minimal-theory))))
