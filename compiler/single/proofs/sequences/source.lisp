(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-count (value)
  (if (posp value) value 0))

(defun sequence-runtime-count (value)
  (if (posp value)
      (if (proof-immediate-integer-p value) value *proof-space-size*)
    0))

(defthm sequence-count-when-zp
  (implies (zp value)
           (equal (sequence-count value) 0)))

(defthm sequence-runtime-count-for-lookup
  (implies (and (natp length) (<= length *proof-space-size*))
           (equal (< (sequence-runtime-count value) length)
                  (< (sequence-count value) length))))

(defthm sequence-runtime-count-for-size
  (equal (< (sequence-runtime-count value) *proof-space-size*)
         (< (sequence-count value) *proof-space-size*)))

(defthm sequence-runtime-count-exact-for-bounded-size
  (implies (< (sequence-runtime-count value) *proof-space-size*)
           (equal (sequence-runtime-count value) (sequence-count value))))

(defun sequence-drop (count datum)
  (declare (xargs :measure (acl2-count datum)))
  (if (and (posp count) (consp datum))
      (sequence-drop (1- count) (cdr datum))
    datum))

(defthm sequence-drop-when-zp
  (implies (zp count)
           (equal (sequence-drop count datum) datum)))

(defthm sequence-drop-of-large-count
  (implies (and (integerp count) (<= (len datum) count))
           (not (consp (sequence-drop count datum))))
  :hints (("Goal" :induct (sequence-drop count datum))))

(defthm sequence-take-of-atom
  (implies (and (atom datum) (syntaxp (not (equal datum ''nil))))
           (equal (take count datum) (take count nil)))
  :hints (("Goal" :induct (take count datum))))

(defthm sequence-take-after-drop
  (equal (take size (sequence-drop count datum))
         (take size (boymoo-model::core-nthcdr (sequence-count count) datum)))
  :hints (("Goal" :induct (sequence-drop count datum)
                  :in-theory (enable boymoo-model::core-nthcdr))))

(defthm sequence-take-after-saturation
  (implies (<= (len datum) *proof-space-size*)
           (equal (take size (sequence-drop (sequence-runtime-count start) datum))
                  (take size (sequence-drop start datum))))
  :hints (("Goal" :use ((:instance sequence-drop-of-large-count
                                   (count *proof-space-size*))
                         (:instance sequence-drop-of-large-count
                                   (count start)))
                  :in-theory (disable sequence-take-after-drop
                                      sequence-drop))))

(defthm sequence-take-after-saturated-drop
  (implies (<= (len datum) *proof-space-size*)
           (equal (take size (sequence-drop (sequence-runtime-count start) datum))
                  (take size (boymoo-model::core-nthcdr (sequence-count start) datum))))
  :hints (("Goal" :use (sequence-take-after-saturation
                        (:instance sequence-take-after-drop (count start)))
                  :in-theory (disable sequence-runtime-count sequence-drop
                                      sequence-take-after-drop
                                      sequence-take-after-saturation))))

(defun sequence-elements (datum)
  (if (stringp datum) (coerce datum 'list) datum))

(defun sequence-end (end datum)
  (if end end (len (sequence-elements datum))))

(defun sequence-result-size (datum start end)
  (sequence-count (- (sequence-end end datum) start)))

(defun sequence-slice (datum start end)
  (let ((elements (take (sequence-result-size datum start end)
                        (sequence-drop (sequence-runtime-count start)
                                       (sequence-elements datum)))))
    (if (stringp datum) (coerce elements 'string) elements)))

(defthm sequence-core-length
  (equal (boymoo-model::core-prelude 'length (list datum))
         (boymoo-model::core-value (len (sequence-elements datum))))
  :hints (("Goal" :in-theory (enable boymoo-model::core-prelude length))))

(defthm sequence-len-zero
  (equal (equal (len elements) 0) (atom elements)))

(defthm sequence-nth-out-of-range
  (implies (and (natp index) (<= (len elements) index))
           (equal (nth index elements) nil))
  :hints (("Goal" :induct (nth index elements))))

(defthm sequence-nth-of-fixed-count
  (equal (nth (sequence-count index) elements)
         (nth index elements))
  :hints (("Goal" :expand ((nth 0 elements)))))

(defthm sequence-take-of-fixed-count
  (equal (take (sequence-count count) elements)
         (take count elements))
  :hints (("Goal" :cases ((posp count)))))

(defthm sequence-nthcdr-of-fixed-count
  (equal (boymoo-model::core-nthcdr (sequence-count count) elements)
         (boymoo-model::core-nthcdr count elements))
  :hints (("Goal" :in-theory (enable boymoo-model::core-nthcdr)
                  :cases ((posp count)))))

(defthm sequence-core-char
  (implies (<= (len (sequence-elements datum)) *proof-space-size*)
           (equal (boymoo-model::core-prelude 'char (list datum index))
                  (boymoo-model::core-value
                   (if (and (stringp datum)
                            (< (sequence-runtime-count index)
                               (len (sequence-elements datum))))
                       (nth (sequence-runtime-count index) (sequence-elements datum))
                     nil))))
  :hints (("Goal" :in-theory (enable boymoo-model::core-prelude char)
                  :use ((:instance sequence-nth-of-fixed-count
                                   (elements (sequence-elements datum)))))))

(defthm sequence-core-subseq
  (implies (<= (len (sequence-elements datum)) *proof-space-size*)
           (equal (boymoo-model::core-prelude 'subseq (list datum start end))
                  (boymoo-model::core-value (sequence-slice datum start end))))
  :hints (("Goal"
           :in-theory (e/d (boymoo-model::core-prelude boymoo-model::core-subseq
                                                       sequence-result-size)
                           (boymoo-model::core-subseq-is-subseq
                            boymoo-model::core-prelude-values
                            sequence-count sequence-take-after-drop
                            sequence-take-after-saturated-drop))
           :use ((:instance sequence-take-after-saturated-drop
                            (size (sequence-result-size datum start end))
                            (datum (sequence-elements datum)))))))

(defun sequence-list-bytes (datum)
  (if (consp datum)
      (cons (char-code (car datum)) (sequence-list-bytes (cdr datum)))
    nil))

(defthm sequence-list-bytes-length
  (equal (len (sequence-list-bytes datum)) (len datum)))

(defthm sequence-char-code-when-noncharacter
  (implies (not (characterp datum))
           (equal (char-code datum) 0))
  :hints (("Goal" :use ((:instance acl2::completion-of-char-code (acl2::x datum))))))

(defthm sequence-byte-characters-of-list-bytes
  (equal (proof-byte-characters (sequence-list-bytes datum))
         (acl2::make-character-list datum))
  :hints (("Goal" :induct (sequence-list-bytes datum))))

(defthm sequence-core-coerce
  (equal (boymoo-model::core-primitive 'coerce (list datum result-type) program)
         (boymoo-model::core-value
          (if (eq result-type 'list)
              (if (stringp datum) (coerce datum 'list) nil)
            (coerce (proof-byte-characters (sequence-list-bytes datum)) 'string))))
  :hints (("Goal" :in-theory (enable boymoo-model::core-primitive)
                  :use ((:instance acl2::completion-of-coerce
                                   (acl2::x datum) (acl2::y result-type))))))

(defthm sequence-byte-characters-character-listp
  (character-listp (proof-byte-characters bytes)))

(defthm sequence-byte-characters-length
  (equal (len (proof-byte-characters bytes)) (len bytes)))

(defthm sequence-byte-list-length
  (equal (len (proof-byte-list count address machine)) (nfix count)))

(defthm sequence-load-string-characters
  (equal (coerce (proof-load-string count address machine) 'list)
         (proof-byte-characters (proof-byte-list count address machine))))

(defthm sequence-load-string-length
  (equal (len (coerce (proof-load-string count address machine) 'list))
         (nfix count))
  :hints (("Goal" :in-theory (disable proof-load-string))))

(defthm sequence-load-string-is-string
  (stringp (proof-load-string count address machine)))

(defthm sequence-character-of-byte
  (implies (and (natp index) (< index (len bytes)))
           (equal (nth index (proof-byte-characters bytes))
                  (code-char (nth index bytes))))
  :hints (("Goal" :induct (nth index bytes))))

(local
 (defun sequence-byte-index-induction (index count address)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (list count address)
     (sequence-byte-index-induction (1- index) (1- count) (1+ address)))))

(defthm sequence-nth-byte-of-memory
  (implies (and (natp index) (natp count) (< index count) (integerp address))
           (equal (nth index (proof-byte-list count address machine))
                  (boymoo-model::a64-load 1 (+ address index) machine)))
  :hints (("Goal" :induct (sequence-byte-index-induction index count address)
                  :in-theory (disable boymoo-model::a64-load)
                  :expand ((proof-byte-list count address machine)))))

(defthm sequence-char-of-load-string
  (implies (and (natp index) (natp count) (< index count) (integerp address))
           (equal (char (proof-load-string count address machine) index)
                  (code-char (boymoo-model::a64-load 1 (+ address index) machine))))
  :hints (("Goal" :in-theory (e/d (char) (proof-load-string boymoo-model::a64-load)))))
