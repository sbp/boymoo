(in-package "BOYMOO-COMPILER")

(include-book "../rt-qir")
(include-book "qir-semantics")
(include-book "word-properties")

(logic)
(set-verify-guards-eagerness 0)

; Exercise runtime dispatch from a QIR-M caller. These are unary or binary
; routines, and ARGS contains their already represented datum words.
(defun rt-call-functions (label params)
  (let* ((inst (list* '(:d . 2) :rt label params))
         (entry (list :fn "ACL2::RUNTIME-CALL" params
                      (list (list 0 nil (list inst) '(:ret (:d . 2)))))))
    (cons entry (rt-qir-functions))))

(defund rt-call (label args heap fuel)
  (let ((params (if (equal (len args) 1) '((:d . 0)) '((:d . 0) (:d . 1)))))
    (qir-run "ACL2::RUNTIME-CALL" args (rt-call-functions label params) :m nil heap fuel)))

(defund rt-observe (label args heap fuel)
  (mv-let (result heap)
    (rt-call label args heap fuel)
    (qir-observe :m result heap)))

(defthmd rt-equal-on-identical-words
  (let ((run (rt-call "rt-qir:EQUAL" (list word word) heap fuel)))
    (implies (and (natp fuel) (<= 14 fuel))
             (and (equal (mv-nth 0 run) (boymoo-model::core-value 58))
                  (equal (mv-nth 1 run) heap))))
  :hints (("Goal"
           :in-theory (e/d (rt-call qir-phi-bindings qir-operand qir-operands
                            qir-compute qir-branch model-word-equality-computes-flag)
                           (qir-eval-step model-word))
           :expand ((:free (input fns frame memory steps)
                     (qir-eval-step :call input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :block input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :insts input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :jump input fns :m nil frame memory steps)))
           :do-not-induct t)))

(defthmd rt-equal-identical-datums-agrees-with-core
  (let ((data (model-heap-datum word heap)))
    (implies (and (boymoo-model::core-value-p data) (natp fuel) (<= 14 fuel))
             (equal (rt-observe "rt-qir:EQUAL" (list word word) heap fuel)
                    (boymoo-model::core-primitive 'equal
                                                 (list (boymoo-model::core-datum data)
                                                       (boymoo-model::core-datum data))
                                                 nil))))
  :hints (("Goal" :in-theory (e/d (rt-observe rt-equal-on-identical-words
                                   boymoo-model::core-primitive)
                                  (qir-run)))))

(defthmd rt-equal-distinct-unboxed-words-return-nil
  (let ((tag (model-word-op :and left 7))
        (run (rt-call "rt-qir:EQUAL" (list left right) heap fuel)))
    (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right) (not (equal left right))
                  (not (equal tag 0)) (not (equal tag 2))
                  (natp fuel) (<= 32 fuel))
             (and (equal (mv-nth 0 run) (boymoo-model::core-value 34))
                  (equal (mv-nth 1 run) heap))))
  :hints (("Goal"
           :in-theory (e/d (rt-call qir-phi-bindings qir-operand qir-operands
                            qir-compute qir-branch model-word-equality-computes-flag)
                           (qir-eval-step model-word))
           :expand ((:free (input fns frame memory steps)
                     (qir-eval-step :call input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :block input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :insts input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :jump input fns :m nil frame memory steps)))
           :do-not-induct t)))

(defund rt-header-read (word heap)
  (model-heap-read 8 (model-word (+ word #xFFFFFFFFFFFFFFFE)) heap))

(local
 (defthmd rt-word-inequality-computes-flag
   (equal (model-word-op :cne left right)
          (model-flag (not (equal (model-word left) (model-word right)))))
   :hints (("Goal" :in-theory (e/d (model-word-op) (model-word))))))

(defthmd rt-equal-different-headers-return-nil
  (let ((run (rt-call "rt-qir:EQUAL" (list left right) heap fuel)))
    (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right) (not (equal left right))
                  (equal (model-word-op :and left 7) 2)
                  (equal (rt-header-read left heap) (boymoo-model::core-value left-header))
                  (equal (rt-header-read right heap) (boymoo-model::core-value right-header))
                  (not (equal (model-word left-header) (model-word right-header)))
                  (natp fuel) (<= 64 fuel))
             (and (equal (mv-nth 0 run) (boymoo-model::core-value 34))
                  (equal (mv-nth 1 run) heap))))
  :hints (("Goal"
           :in-theory (e/d (rt-call rt-header-read qir-phi-bindings qir-operand
                            qir-operands qir-compute qir-branch model-word-equality-computes-flag
                            rt-word-inequality-computes-flag)
                           (qir-eval-step model-word))
           :expand ((:free (input fns frame memory steps)
                     (qir-eval-step :call input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :block input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :insts input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :jump input fns :m nil frame memory steps)))
           :do-not-induct t)))

(defthmd rt-length-reads-string-header
  (implies (and (equal (model-word-op :and word 7) 2)
                (equal (rt-header-read word heap) (boymoo-model::core-value header))
                (equal (model-word-op :and header 255) 1)
                (natp fuel) (<= 32 fuel))
           (let* ((run (rt-call "rt-qir:LENGTH" (list word) heap fuel))
                  (count (model-word-op :shr header 8))
                  (tagged (model-word-op :or (model-word-op :shl count 1) 1)))
             (and (equal (mv-nth 0 run) (boymoo-model::core-value tagged))
                  (equal (mv-nth 1 run) heap))))
  :hints (("Goal"
           :in-theory (e/d (rt-call rt-header-read qir-phi-bindings qir-operand
                            qir-operands qir-compute qir-branch model-word-equality-computes-flag)
                           (qir-eval-step model-word))
           :expand ((:free (input fns frame memory steps)
                     (qir-eval-step :call input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :block input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :insts input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :jump input fns :m nil frame memory steps)))
           :do-not-induct t)))

(defund rt-string-byte (word index heap)
  (model-heap-read 1 (model-word (+ word (model-word-op :add index 6))) heap))

(defthmd rt-char-reads-indexed-byte
  (let* ((signed-index (model-word-op :sar index-word 1))
         (positive (model-word-op :csgt signed-index 0))
         (index (if (equal positive 0) 0 signed-index))
         (count (model-word-op :shr header 8)))
    (implies (and (equal (model-word-op :and word 7) 2)
                  (equal (rt-header-read word heap) (boymoo-model::core-value header))
                  (equal (model-word-op :and header 255) 1)
                  (equal (model-word-op :and index-word 1) 1)
                  (not (equal (model-word-op :cult index count) 0))
                  (equal (rt-string-byte word index heap) (boymoo-model::core-value byte))
                  (natp fuel) (<= 50 fuel))
             (let* ((run (rt-call "rt-qir:CHAR" (list word index-word) heap fuel))
                    (tagged (model-word-op :or (model-word-op :shl byte 3) 4)))
               (and (equal (mv-nth 0 run) (boymoo-model::core-value tagged))
                    (equal (mv-nth 1 run) heap)))))
  :hints (("Goal"
           :in-theory (e/d (rt-call rt-header-read rt-string-byte qir-phi-bindings
                            qir-operand qir-operands qir-compute qir-branch
                            model-word-equality-computes-flag)
                           (qir-eval-step model-word))
           :expand ((:free (input fns frame memory steps)
                     (qir-eval-step :call input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :block input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :insts input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :jump input fns :m nil frame memory steps)))
           :do-not-induct t)))

(defthmd rt-char-fixnum-index-outside-string-returns-nil
  (let* ((signed-index (model-word-op :sar index-word 1))
         (positive (model-word-op :csgt signed-index 0))
         (index (if (equal positive 0) 0 signed-index))
         (count (model-word-op :shr header 8))
         (run (rt-call "rt-qir:CHAR" (list word index-word) heap fuel)))
    (implies (and (equal (model-word-op :and word 7) 2)
                  (equal (rt-header-read word heap) (boymoo-model::core-value header))
                  (equal (model-word-op :and header 255) 1)
                  (equal (model-word-op :and index-word 1) 1)
                  (equal (model-word-op :cult index count) 0)
                  (natp fuel) (<= 50 fuel))
             (and (equal (mv-nth 0 run) (boymoo-model::core-value 34))
                  (equal (mv-nth 1 run) heap))))
  :hints (("Goal"
           :in-theory (e/d (rt-call rt-header-read qir-phi-bindings qir-operand
                            qir-operands qir-compute qir-branch model-word-equality-computes-flag)
                           (qir-eval-step model-word))
           :expand ((:free (input fns frame memory steps)
                     (qir-eval-step :call input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :block input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :insts input fns :m nil frame memory steps))
                    (:free (input fns frame memory steps)
                     (qir-eval-step :jump input fns :m nil frame memory steps)))
           :do-not-induct t)))

(local (include-book "ihs/logops-lemmas" :dir :system))

(local
 (defthmd rt-word-with-tag
   (implies (and (unsigned-byte-p bits tag) (integerp high))
            (equal (logior (ash high bits) tag) (acl2::logapp bits tag high)))
   :hints (("Goal" :induct (acl2::sub1-logcdr-induction-1 bits tag)
            :in-theory (e/d (acl2::logops-recursive-definitions-theory)
                             (ash acl2::binary-logior acl2::logapp unsigned-byte-p
                              acl2::commutativity-of-logior)))
           ("Subgoal *1/2" :use (:instance acl2::commutativity-of-logior (acl2::i high) (acl2::j 0))))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthmd rt-immediate-integer-tag-is-odd
   (implies (model-immediate-integer-p value)
            (logbitp 0 (model-word-op :and (model-integer-word value) 7)))
   :hints (("Goal" :use ((:instance model-immediate-word-is-odd (datum value))
                         (:instance acl2::logand-with-mask (acl2::size 3) (acl2::mask 7)
                                    (acl2::i (model-integer-word value))))
            :in-theory (e/d (model-word-op)
                             (model-word model-integer-word acl2::logand-constant-mask
                              acl2::loghead (:definition logbitp) (:definition acl2::binary-logand)))))))

(local
 (defthmd rt-immediate-integer-tags-exclude-pointers
   (let ((tag (model-word-op :and (model-integer-word value) 7)))
     (implies (model-immediate-integer-p value)
              (and (not (equal tag 0)) (not (equal tag 2)))))
   :hints (("Goal" :use rt-immediate-integer-tag-is-odd
            :in-theory (disable model-word model-integer-word (:definition logbitp))))))

(local
 (defthmd rt-immediate-integer-words-are-injective
   (implies (and (model-immediate-integer-p left) (model-immediate-integer-p right))
            (equal (equal (model-integer-word left) (model-integer-word right))
                   (equal left right)))
   :hints (("Goal"
            :use ((:instance model-constant-of-immediate-integer (datum left) (constants nil))
                  (:instance model-constant-of-immediate-integer (datum right) (constants nil)))
            :in-theory (disable model-word model-integer-word)))))

(defthmd rt-equal-of-fixnums-agrees-with-core
  (implies (and (model-immediate-integer-p left) (model-immediate-integer-p right)
                (natp fuel) (<= 32 fuel))
           (equal (rt-observe "rt-qir:EQUAL" (list (model-integer-word left)
                                                    (model-integer-word right)) heap fuel)
                  (boymoo-model::core-primitive 'equal (list left right) nil)))
  :hints (("Goal"
           :cases ((equal left right))
           :use (:instance rt-equal-distinct-unboxed-words-return-nil
                           (left (model-integer-word left)) (right (model-integer-word right)))
           :in-theory (e/d (rt-observe rt-equal-on-identical-words
                            rt-immediate-integer-tags-exclude-pointers
                            rt-immediate-integer-words-are-injective boymoo-model::core-primitive)
                           (rt-call qir-run model-word model-integer-word)))))

(local
 (defthm rt-string-header-is-a-word
   (implies (unsigned-byte-p 56 count)
            (unsigned-byte-p 64 (+ 1 (* 256 count))))))

(local
 (defthmd rt-string-header-fields
   (implies (unsigned-byte-p 56 count)
            (let ((header (+ 1 (* 256 count))))
              (and (equal (model-word-op :and header 255) 1)
                   (equal (model-word-op :shr header 8) count))))
   :hints (("Goal"
            :use (:instance acl2::logand-with-mask
                            (acl2::mask 255) (acl2::size 8) (acl2::i (+ 1 (* 256 count))))
            :in-theory (e/d (model-word-op acl2::loghead ash)
                             (model-word (:definition acl2::binary-logand) mod floor))))))

(local
 (defthmd rt-length-encoding-is-immediate
   (implies (unsigned-byte-p 56 count)
            (equal (model-word-op :or (model-word-op :shl count 1) 1)
                   (model-integer-word count)))
   :hints (("Goal"
            :use (:instance rt-word-with-tag (bits 1) (high count) (tag 1))
            :in-theory (e/d (model-word-op acl2::logapp ash)
                             (model-word (:definition acl2::binary-logior)))))))

(defund rt-string-represented-p (word string heap)
  (let ((count (length string)))
    (and (stringp string)
         (unsigned-byte-p 64 word)
         (equal (model-heap-datum word heap) (boymoo-model::core-value string))
         (equal (model-word-op :and word 7) 2)
         (unsigned-byte-p 56 count)
         (equal (rt-header-read word heap) (boymoo-model::core-value (+ 1 (* 256 count)))))))

(defthmd rt-equal-of-different-length-strings-agrees-with-core
  (implies (and (rt-string-represented-p left first heap)
                (rt-string-represented-p right second heap)
                (not (equal (length first) (length second)))
                (natp fuel) (<= 64 fuel))
           (equal (rt-observe "rt-qir:EQUAL" (list left right) heap fuel)
                  (boymoo-model::core-primitive 'equal (list first second) nil)))
  :hints (("Goal"
           :cases ((equal left right) (equal first second))
           :use (:instance rt-equal-different-headers-return-nil
                           (left-header (+ 1 (* 256 (length first))))
                           (right-header (+ 1 (* 256 (length second)))))
           :in-theory (e/d (rt-string-represented-p rt-observe boymoo-model::core-primitive)
                            (rt-call qir-run length model-word)))))

(defthmd rt-length-of-represented-string-agrees-with-core
  (implies (and (rt-string-represented-p word string heap) (natp fuel) (<= 32 fuel))
           (equal (rt-observe "rt-qir:LENGTH" (list word) heap fuel)
                  (boymoo-model::core-prelude 'length (list string))))
  :hints (("Goal"
           :use (:instance rt-length-reads-string-header (header (+ 1 (* 256 (length string)))))
           :in-theory (e/d (rt-string-represented-p rt-observe rt-string-header-fields
                            rt-length-encoding-is-immediate model-constant-of-immediate-integer
                            boymoo-model::core-prelude)
                           (rt-call qir-run length model-word model-integer-word)))))

(local
 (defthmd rt-fixnum-index-decodes
   (implies (unsigned-byte-p 62 index)
            (let* ((word (model-integer-word index))
                   (decoded (model-word-op :sar word 1)))
              (and (equal (model-word-op :and word 1) 1)
                   (equal decoded index)
                   (equal (model-word-op :csgt index 0)
                          (model-flag (< 0 index))))))
   :hints (("Goal"
            :use (:instance acl2::logand-with-mask
                            (acl2::mask 1) (acl2::size 1) (acl2::i (+ 1 (* 2 index))))
            :in-theory (e/d (model-word-op acl2::loghead ash)
                             (model-word (:definition acl2::binary-logand) mod floor))))))

(local
 (defthm rt-unsigned-comparison-uses-word-order
   (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
            (equal (model-word-op :cult left right) (model-flag (< left right))))
   :hints (("Goal" :in-theory (e/d (model-word-op) (model-word))))))

(local
 (defthmd rt-character-encoding-is-character-word
   (implies (characterp ch)
            (equal (model-word-op :or (model-word-op :shl (char-code ch) 3) 4)
                   (model-character-word ch)))
   :hints (("Goal"
            :use (:instance rt-word-with-tag (bits 3) (high (char-code ch)) (tag 4))
            :in-theory (e/d (model-word-op acl2::logapp ash)
                             (model-word (:definition acl2::binary-logior)))))))

(local
 (defthmd rt-character-word-decodes
   (implies (characterp ch)
            (equal (model-heap-datum (model-character-word ch) heap)
                   (boymoo-model::core-value ch)))
   :hints (("Goal"
            :use (:instance acl2::logand-with-mask (acl2::mask 7) (acl2::size 3)
                            (acl2::i (+ 4 (* 8 (char-code ch)))))
            :in-theory (e/d (model-constant acl2::loghead ash logbitp oddp evenp)
                             (model-word (:definition acl2::binary-logand) mod floor))))))

(local
 (defthm rt-character-of-in-range-string-index
   (implies (and (stringp string) (natp index) (< index (length string)))
            (characterp (char string index)))
   :hints (("Goal" :in-theory (enable char length)
            :use (:instance acl2::characterp-nth (acl2::x (coerce string 'list)) (acl2::i index))))))

(defthmd rt-char-of-represented-string-agrees-with-core
  (let* ((ch (char string index))
         (byte (char-code ch)))
    (implies (and (rt-string-represented-p word string heap)
                  (natp index) (< index (length string))
                  (equal (rt-string-byte word index heap) (boymoo-model::core-value byte))
                  (natp fuel) (<= 50 fuel))
             (equal (rt-observe "rt-qir:CHAR" (list word (model-integer-word index)) heap fuel)
                    (boymoo-model::core-prelude 'char (list string index)))))
  :hints (("Goal"
           :use (:instance rt-char-reads-indexed-byte
                           (header (+ 1 (* 256 (length string))))
                           (index-word (model-integer-word index))
                           (byte (char-code (char string index))))
           :in-theory (e/d (rt-string-represented-p rt-observe rt-string-header-fields
                            rt-fixnum-index-decodes rt-character-encoding-is-character-word
                            rt-character-word-decodes boymoo-model::core-prelude)
                           (rt-call qir-run length char model-word model-integer-word
                            model-character-word model-heap-datum)))))

(local
 (defthm rt-nth-past-end-is-nil
   (implies (and (natp index) (<= (len data) index))
            (equal (nth index data) nil))
   :hints (("Goal" :induct (nth index data)))))

(local
 (defthm rt-core-char-past-end-is-nil
   (implies (and (stringp string) (natp index) (<= (length string) index))
            (equal (char string index) nil))
   :hints (("Goal" :in-theory (enable char length)))))

(defthmd rt-char-of-represented-string-past-end-agrees-with-core
  (implies (and (rt-string-represented-p word string heap)
                (unsigned-byte-p 62 index) (<= (length string) index)
                (natp fuel) (<= 50 fuel))
           (equal (rt-observe "rt-qir:CHAR" (list word (model-integer-word index)) heap fuel)
                  (boymoo-model::core-prelude 'char (list string index))))
  :hints (("Goal"
           :use (:instance rt-char-fixnum-index-outside-string-returns-nil
                           (header (+ 1 (* 256 (length string))))
                           (index-word (model-integer-word index)))
           :in-theory (e/d (rt-string-represented-p rt-observe rt-string-header-fields
                            rt-fixnum-index-decodes boymoo-model::core-prelude)
                           (rt-call qir-run length char model-word model-integer-word)))))

(local
 (defthmd rt-negative-fixnum-index-clamps-to-zero
   (let* ((encoded (model-integer-word index))
          (decoded (model-word-op :sar encoded 1)))
     (implies (and (model-immediate-integer-p index) (< index 0))
              (and (equal (model-word-op :and encoded 1) 1)
                   (equal (model-word-op :csgt decoded 0) 0))))
   :hints (("Goal"
            :use ((:instance model-immediate-word-is-odd (datum index))
                  (:instance model-immediate-signed-word (datum index))
                  (:instance acl2::logand-with-mask (acl2::size 1) (acl2::mask 1)
                             (acl2::i (model-integer-word index)))
                  (:instance acl2::logbitp* (acl2::pos 0) (acl2::i (model-integer-word index))))
            :in-theory (e/d (model-word-op acl2::loghead acl2::logcar ash)
                             (model-word model-signed model-integer-word acl2::logand-constant-mask
                              acl2::binary-logand (:definition logbitp) floor mod))))))

(local
 (defthm rt-core-char-negative-index-is-first
   (implies (and (stringp string) (integerp index) (< index 0))
            (equal (char string index) (char string 0)))
   :hints (("Goal" :in-theory (enable char)))))

(defthmd rt-char-of-represented-string-negative-index-agrees-with-core
  (let ((byte (char-code (char string 0))))
    (implies (and (rt-string-represented-p word string heap)
                  (model-immediate-integer-p index) (< index 0)
                  (implies (< 0 (length string))
                           (equal (rt-string-byte word 0 heap) (boymoo-model::core-value byte)))
                  (natp fuel) (<= 50 fuel))
             (equal (rt-observe "rt-qir:CHAR" (list word (model-integer-word index)) heap fuel)
                    (boymoo-model::core-prelude 'char (list string index)))))
  :hints (("Goal"
           :cases ((equal (length string) 0))
           :use ((:instance rt-character-word-decodes (ch (char string 0)))
                 (:instance rt-char-reads-indexed-byte
                            (header (+ 1 (* 256 (length string))))
                            (index-word (model-integer-word index)) (byte (char-code (char string 0))))
                 (:instance rt-char-fixnum-index-outside-string-returns-nil
                            (header (+ 1 (* 256 (length string))))
                            (index-word (model-integer-word index))))
           :in-theory (e/d (rt-string-represented-p rt-observe rt-string-header-fields
                            rt-negative-fixnum-index-clamps-to-zero rt-character-encoding-is-character-word
                            rt-character-word-decodes boymoo-model::core-prelude)
                           (rt-call qir-run length char model-word model-integer-word
                            model-character-word)))))

; A model heap can supply just the bytes of the static NIL header that
; guarded loads read. Its type is a symbol, with two words of payload.
(defun rt-example-heap ()
  (model-heap 80 (boymoo-model::a64-write-bytes 8 32 #x1002 nil) nil nil))

(assert-event (qir-m-p (rt-qir-functions)))

(assert-event
 (and (equal (rt-observe "rt-qir:EQUAL" '(3 3) nil 40)
             (boymoo-model::core-primitive 'equal '(1 1) nil))
      (equal (rt-observe "rt-qir:EQUAL" '(3 5) nil 40)
             (boymoo-model::core-primitive 'equal '(1 2) nil))
      (equal (rt-observe "rt-qir:EQUAL" '(3 11) nil 40)
             (boymoo-model::core-primitive 'equal '(1 5) nil))
      (equal (rt-observe "prim:COMMON-LISP::EQUAL" '(3 5) nil 40)
             (boymoo-model::core-primitive 'equal '(1 2) nil))))

(assert-event
 (mv-let (first heap)
   (model-allocate-string "aaabbbccc" (rt-example-heap))
   (mv-let (second heap)
     (model-allocate-string "aaabbbccc" heap)
     (mv-let (third heap)
       (model-allocate-string "aaabbbccd" heap)
       (let ((a (boymoo-model::core-datum first))
             (b (boymoo-model::core-datum second))
             (c (boymoo-model::core-datum third)))
         (and (not (equal a b))
              (equal (rt-observe "rt-qir:EQUAL" (list a b) heap 160)
                     (boymoo-model::core-primitive 'equal '("aaabbbccc" "aaabbbccc") nil))
              (equal (rt-observe "rt-qir:EQUAL" (list a c) heap 160)
                     (boymoo-model::core-primitive 'equal '("aaabbbccc" "aaabbbccd") nil))))))))

(assert-event
 (mv-let (first heap)
   (model-encode '(1 2 3) (rt-example-heap))
   (mv-let (second heap)
     (model-encode '(1 2 4) heap)
     (equal (rt-observe "rt-qir:EQUAL" (list (boymoo-model::core-datum first)
                                               (boymoo-model::core-datum second)) heap 140)
            (boymoo-model::core-primitive 'equal '((1 2 3) (1 2 4)) nil)))))

(assert-event
 (mv-let (result heap)
   (model-encode '(1 2 3) (rt-example-heap))
   (and (equal (rt-observe "rt-qir:LENGTH" (list 34) heap 100)
               (boymoo-model::core-prelude 'length '(nil)))
        (equal (rt-observe "rt-qir:LENGTH" (list (boymoo-model::core-datum result)) heap 100)
               (boymoo-model::core-prelude 'length '((1 2 3)))))))

(assert-event
 (mv-let (result heap)
   (model-allocate-string "abc" (rt-example-heap))
   (let ((word (boymoo-model::core-datum result)))
     (and (equal (rt-observe "rt-qir:LENGTH" (list word) heap 60)
                 (boymoo-model::core-prelude 'length '("abc")))
          (equal (rt-observe "rt-qir:CHAR" (list word 1) heap 60)
                 (boymoo-model::core-prelude 'char '("abc" 0)))
          (equal (rt-observe "rt-qir:CHAR" (list word 3) heap 60)
                 (boymoo-model::core-prelude 'char '("abc" 1)))
          (equal (rt-observe "rt-qir:CHAR" (list word 5) heap 60)
                 (boymoo-model::core-prelude 'char '("abc" 2)))))))
