(in-package "BOYMOO-PROOFS")

; The loader model PROOF-LOAD-LINUX leaves each byte of the file in
; memory at the load address plus its offset in the file, so that the
; image that ELF-IMAGE-EXECUTABLE wrote is found, fragment by fragment, at
; the code address.

(include-book "load")

(logic)
(set-verify-guards-eagerness 0)

(defun linux-bytes-p (bytes)
  (if (atom bytes)
      t
    (and (natp (car bytes))
         (< (car bytes) 256)
         (linux-bytes-p (cdr bytes)))))

(defthm linux-bytes-p-of-string-bytes
  (linux-bytes-p (proof-string-bytes chars)))

(defthm linux-len-of-string-bytes
  (equal (len (proof-string-bytes chars)) (len chars)))

(defthm linux-assoc-of-clear-memory
  (implies (and (<= base k) (< k end))
           (equal (assoc-equal k (proof-clear-memory base end memory)) nil)))

(defthm linux-assoc-of-overlay-outside
  (implies (and (natp k) (natp a)
                (or (< k a) (<= (+ a (len bytes)) k))
                (<= (+ a (len bytes)) (expt 2 64)))
           (equal (assoc-equal k (proof-overlay-bytes bytes a memory t))
                  (assoc-equal k memory))))

(defthm linux-assoc-of-overlay-inside
  (implies (and (natp k) (natp a)
                (<= a k) (< k (+ a (len bytes)))
                (<= (+ a (len bytes)) (expt 2 64))
                (not (assoc-equal k memory))
                (linux-bytes-p bytes))
           (equal (boymoo-model::a64-unsigned
                   8 (cdr (assoc-equal k (proof-overlay-bytes bytes a memory t))))
                  (nth (- k a) bytes)))
  :hints (("Goal" :induct (proof-overlay-bytes bytes a memory t))))

(defthm linux-nth-of-string-bytes
  (equal (nth i (proof-string-bytes chars))
         (if (< (nfix i) (len chars)) (char-code (nth i chars)) nil)))

(defthm linux-logior-zero
  (implies (natp b) (equal (logior b 0) b)))

(defthm linux-read-one-byte
  (equal (boymoo-model::a64-read-bytes 1 a memory)
         (logior (boymoo-model::a64-byte a memory) 0))
  :hints (("Goal" :expand ((boymoo-model::a64-read-bytes 1 a memory)))))

(local
 (defthm linux-car-nthcdr
   (equal (car (nthcdr i l)) (nth i l))))

(local
 (defthm linux-cdr-nthcdr
   (implies (natp i)
            (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l)))))

(defthm linux-load-memory
  (implies (proof-load-linux file machine regions page input replies)
           (equal (boymoo-model::a64-memory
                   (proof-world-machine
                    (proof-load-linux file machine regions page input replies)))
                  (proof-overlay-bytes
                   (proof-string-bytes (coerce file 'list))
                   *proof-linux-file-base*
                   (proof-clear-memory
                    *proof-linux-file-base*
                    (proof-align-up (+ *proof-linux-file-base* (length file)) page)
                    (boymoo-model::a64-memory machine))
                   t)))
  :hints (("Goal" :in-theory (enable proof-load-linux))))

(defthm linux-load-accepts
  (implies (proof-load-linux file machine regions page input replies)
           (and (proof-elf-p file)
                (proof-page-size-p page)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable proof-load-linux))))

(defthm linux-loaded-byte-value
  (implies (and (natp k) (natp base) (character-listp chars)
                (<= base k) (< k (+ base (len chars)))
                (<= (+ base (len chars)) end)
                (<= (+ base (len chars)) (expt 2 64)))
           (equal (boymoo-model::a64-unsigned
                   8 (cdr (assoc-equal k (proof-overlay-bytes
                                          (proof-string-bytes chars) base
                                          (proof-clear-memory base end memory)
                                          t))))
                  (char-code (nth (- k base) chars)))))

(defthm linux-load-byte
  (implies (and (proof-load-linux file machine regions page input replies)
                (natp k)
                (<= *proof-linux-file-base* k)
                (< k (+ *proof-linux-file-base* (length file))))
           (equal (boymoo-model::a64-load
                   1 k
                   (proof-world-machine
                    (proof-load-linux file machine regions page input replies)))
                  (char-code (nth (- k *proof-linux-file-base*) (coerce file 'list)))))
  :hints (("Goal" :use (linux-load-accepts
                        linux-elf-length-range
                        (:instance linux-align-up-covers
                                   (end (+ *proof-linux-file-base* (length file)))))
                  :in-theory (disable proof-world-machine boymoo-model::a64-memory))))

(defthm linux-load-file-stringp
  (implies (proof-load-linux file machine regions page input replies)
           (stringp file))
  :rule-classes :forward-chaining
  :hints (("Goal" :use (linux-load-accepts linux-elf-length-range))))

(local
 (defthm linux-take-nthcdr-step
   (implies (and (natp j) (not (zp n)))
            (equal (take n (nthcdr j l))
                   (cons (nth j l) (take (- n 1) (nthcdr (+ 1 j) l)))))))

(local
 (defthm linux-character-nth
   (implies (and (character-listp l) (natp j) (< j (len l)))
            (characterp (nth j l)))))

(defthm linux-load-characters
  (implies (and (proof-load-linux file machine regions page input replies)
                (natp a)
                (natp n)
                (<= *proof-linux-file-base* a)
                (<= (+ a n) (+ *proof-linux-file-base* (length file))))
           (equal (proof-byte-characters
                   (proof-byte-list
                    n a
                    (proof-world-machine
                     (proof-load-linux file machine regions page input replies))))
                  (take n (nthcdr (- a *proof-linux-file-base*) (coerce file 'list)))))
  :hints (("Goal" :induct (proof-byte-list
                           n a
                           (proof-world-machine
                            (proof-load-linux file machine regions page input replies)))
                  :in-theory (disable linux-load-memory proof-world-machine
                                      boymoo-model::a64-load))))

(local
 (defthm linux-take-of-append-exact
   (implies (true-listp a)
            (equal (take (len a) (append a b)) a))))

(local
 (defthm linux-nthcdr-of-append-exact
   (equal (nthcdr (len a) (append a b)) b)))

(local
 (defthm linux-nthcdr-nthcdr
   (implies (and (natp i) (natp j))
            (equal (nthcdr i (nthcdr j l)) (nthcdr (+ i j) l)))
   :rule-classes nil))

(local
 (defthm linux-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm linux-nthcdr-after-prefix
   (implies (and (natp j) (equal (nthcdr j l) (append x y)))
            (equal (nthcdr (+ (len x) j) l) y))
   :rule-classes nil
   :hints (("Goal" :use ((:instance linux-nthcdr-nthcdr (i (len x))))))))

(local
 (defthm linux-true-listp-of-fragment-characters
   (true-listp (linux-fragment-characters fragments))))

(local
 (defthm linux-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

(defthm linux-load-fragments
  (implies (and (proof-load-linux file machine regions page input replies)
                (proof-fragments-p fragments)
                (natp a)
                (<= *proof-linux-file-base* a)
                (<= (+ a (proof-fragments-size fragments))
                    (+ *proof-linux-file-base* (length file)))
                (equal (nthcdr (- a *proof-linux-file-base*) (coerce file 'list))
                       (append (linux-fragment-characters fragments) rest)))
           (proof-fragments-at-p
            fragments a
            (proof-world-machine
             (proof-load-linux file machine regions page input replies))))
  :hints (("Goal" :induct (proof-fragments-at-p
                           fragments a
                           (proof-world-machine
                            (proof-load-linux file machine regions page input replies)))
                  :in-theory (disable linux-load-memory proof-world-machine
                                      boymoo-model::a64-load))
          ("Subgoal *1/2"
           :use ((:instance linux-nthcdr-after-prefix
                            (x (coerce (car fragments) 'list))
                            (y (append (linux-fragment-characters (cdr fragments)) rest))
                            (j (- a *proof-linux-file-base*))
                            (l (coerce file 'list)))))))

(defthm linux-load-executable-image
  (implies (and (linux-elf-arguments-p image entry)
                (linux-load-environment-p (car image) machine regions page input))
           (proof-image-at-p
            image *proof-linux-code-base*
            (proof-world-machine
             (proof-load-linux (boymoo-compiler::elf-image-executable image entry)
                               machine regions page input replies))))
  :hints (("Goal" :use (linux-load-executable-accepted
                        (:instance linux-load-fragments
                                   (file (boymoo-compiler::elf-image-executable
                                          image entry))
                                   (fragments (cdr image))
                                   (a *proof-linux-code-base*)
                                   (rest nil)))
                  :in-theory (disable linux-load-memory proof-world-machine
                                      linux-load-fragments))))
