(in-package "BOYMOO-PROOFS")

(include-book "emission")
(include-book "memory")
(include-book "ranges")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable mod ash proof-decode
                     boymoo-model::a64-byte boymoo-model::a64-read-bytes
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(local
 (defthm division-byte-characters-form-character-list
   (character-listp (proof-byte-characters bytes))
   :hints (("Goal" :induct (proof-byte-characters bytes)))))

(local
 (defun division-byte-index-induct (index count address)
   (declare (xargs :measure (nfix index)))
   (if (zp index)
       (list count address)
     (division-byte-index-induct (1- index) (1- count) (1+ (ifix address))))))

(local
 (defthm division-byte-character-at-index
   (implies (and (natp index) (natp count) (< index count) (integerp address))
            (equal (nth index (proof-byte-characters (proof-byte-list count address machine)))
                   (code-char (boymoo-model::a64-byte
                               (+ address index) (boymoo-model::a64-memory machine)))))
   :hints (("Goal" :induct (division-byte-index-induct index count address)
                   :in-theory (disable boymoo-model::a64-memory))
           ("Subgoal *1/1" :expand ((proof-byte-list count address machine))))))

(local
 (defthm division-load-string-byte-at-index
   (implies (and (natp index) (natp count) (< index count) (integerp address))
            (equal (char-code (char (proof-load-string count address machine) index))
                   (boymoo-model::a64-byte (+ address index) (boymoo-model::a64-memory machine))))
   :hints (("Goal"
            :use (:instance division-byte-value-range
                            (address (+ address index)) (memory (boymoo-model::a64-memory machine)))
            :in-theory (disable boymoo-model::a64-memory division-byte-value-range)))))

(defthm division-file-le-of-loaded-string
  (implies (and (natp index) (natp count) (natp total)
                (integerp address) (<= (+ index count) total))
           (equal (proof-file-le count index (proof-load-string total address machine))
                  (boymoo-model::a64-load count (+ address index) machine)))
  :hints (("Goal" :induct (proof-file-le count index file)
                  :in-theory (disable proof-load-string boymoo-model::a64-memory
                                      char char-code))
          ("Subgoal *1/2"
           :use (:instance division-read-bytes-little-endian
                           (address (+ address index)) (memory (boymoo-model::a64-memory machine))))
          ("Subgoal *1/1"
           :expand ((boymoo-model::a64-read-bytes
                     0 (+ address index) (boymoo-model::a64-memory machine)))))
  :rule-classes nil)

(defun division-image-word-at (offset fragments)
  (declare (xargs :measure (acl2-count fragments)))
  (if (atom fragments)
      nil
    (let ((length (length (car fragments))))
      (cond ((<= (+ offset 4) length)
             (proof-file-le 4 offset (car fragments)))
            ((<= length offset)
             (division-image-word-at (- offset length) (cdr fragments)))
            (t nil)))))

(local
 (defun division-fragment-offset-induct (offset fragments base)
   (declare (xargs :measure (acl2-count fragments)))
   (if (atom fragments)
       (list offset base)
     (let ((length (length (car fragments))))
       (division-fragment-offset-induct (- offset length) (cdr fragments) (+ base length))))))

(defthm division-image-word-matches-memory
  (implies (and (natp offset) (integerp base)
                (proof-fragments-p fragments)
                (proof-fragments-at-p fragments base machine)
                (integerp (division-image-word-at offset fragments)))
           (equal (boymoo-model::a64-load 4 (+ base offset) machine)
                  (division-image-word-at offset fragments)))
  :hints (("Goal" :induct (division-fragment-offset-induct offset fragments base)
                  :in-theory (disable proof-load-string proof-file-le boymoo-model::a64-load))
          ("Subgoal *1/2"
           :use (:instance division-file-le-of-loaded-string
                           (count 4) (index offset) (total (length (car fragments))) (address base))))
  :rule-classes nil)

(defthm division-linked-image-instruction-at-offset
  (let* ((image (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry)))
         (word (division-image-word-at offset (cdr image))))
    (implies (and (proof-linked-image-p items entry base world)
                  (natp offset) (<= (+ offset 4) (car image))
                  (equal (mod (+ base offset) 4) 0)
                  (integerp word))
             (proof-instruction-at-p (proof-decode word) (+ base offset) world)))
  :hints (("Goal"
           :use ((:instance division-image-word-matches-memory
                            (fragments (cdr (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry))))
                            (machine (proof-world-machine world)))
                 (:instance division-covered-slice
                            (bytes (car (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry))))
                            (size 4) (access :execute) (regions (proof-world-regions world))))
           :in-theory (disable boymoo-compiler::a64-assemble-image
                               division-image-word-at proof-covered-p proof-fragments-at-p
                               proof-fragments-p boymoo-model::a64-load))
          ("Goal'" :use (:instance division-covered-span
                                   (address base)
                                   (size (car (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry))))
                                   (access :execute) (regions (proof-world-regions world)))))
  :rule-classes nil)

(defun division-image-matches-instructions-p (instructions offset fragments)
  (if (atom instructions)
      (null instructions)
    (let ((word (division-image-word-at offset fragments)))
      (and (integerp word)
           (equal (proof-decode word) (car instructions))
           (division-image-matches-instructions-p (cdr instructions) (+ 4 offset) fragments)))))

(local
 (defthm division-plus-four-keeps-alignment
   (implies (integerp address)
            (equal (mod (+ 4 address) 4) (mod address 4)))
   :hints (("Goal"
            :use ((:instance division-floor-mod-identity (a address) (b 4))
                  (:instance division-signed-floor-integer (a address) (b 4))
                  (:instance division-signed-mod-bounds (a address) (b 4))
                  (:instance division-signed-remainder-unique
                             (a (+ 4 address)) (b 4) (q (+ 1 (floor address 4)))
                             (r (mod address 4))))
            :in-theory (disable floor division-floor-mod-identity)))))

(local
 (defun division-linked-offset-induct (instructions offset)
   (if (atom instructions)
       offset
     (division-linked-offset-induct (cdr instructions) (+ 4 offset)))))

(defthm division-linked-image-instructions-at-offset
  (let ((image (mv-nth 0 (boymoo-compiler::a64-assemble-image items entry))))
    (implies (and (proof-linked-image-p items entry base world)
                  (natp offset) (integerp base) (equal (mod (+ base offset) 4) 0)
                  (<= (+ offset (* 4 (len instructions))) (car image))
                  (division-image-matches-instructions-p instructions offset (cdr image)))
             (proof-instructions-at-p instructions (+ base offset) world)))
  :hints (("Goal" :induct (division-linked-offset-induct instructions offset)
                  :in-theory (disable boymoo-model::a64-load
                                      boymoo-compiler::a64-assemble-image proof-linked-image-p
                                      proof-instruction-at-p division-image-word-at))
          ("Subgoal *1/2"
           :use ((:instance division-linked-image-instruction-at-offset)
                 (:instance division-plus-four-keeps-alignment (address (+ base offset))))
           :in-theory (disable division-plus-four-keeps-alignment
                               boymoo-compiler::a64-assemble-image proof-linked-image-p
                               proof-instruction-at-p division-image-word-at)))
  :rule-classes nil)

(defun division-decode-image-words (count offset fragments)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (proof-decode (division-image-word-at offset fragments))
          (division-decode-image-words (1- count) (+ offset 4) fragments))))

(defconst *division-runtime-items* (division-linked-example-items))
(defconst *division-runtime-image*
  (mv-let (image offset)
    (boymoo-compiler::a64-assemble-image *division-runtime-items* "os:main")
    (declare (ignore offset))
    image))

(defun division-runtime-offset (label)
  (division-label-offset label *division-runtime-items*))

(defun division-runtime-block (label skip count)
  (division-decode-image-words
   count (+ (division-runtime-offset label) (* 4 skip)) (cdr *division-runtime-image*)))
