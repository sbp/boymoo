(in-package "BOYMOO-PROOFS")

(include-book "../model/a64")

(logic)
(set-verify-guards-eagerness 0)

(defun proof-reg (register machine)
  (boymoo-model::a64-read-reg register 64 nil machine))

(defun proof-load-word (address machine)
  (boymoo-model::a64-load 8 address machine))

; A span has an ordinary integer endpoint even when the endpoint is 2^64.
(defun proof-span-p (address size)
  (and (unsigned-byte-p 64 address)
       (natp size)
       (<= (+ address size) (expt 2 64))))

(defun proof-subspan-p (address size lower upper)
  (and (proof-span-p address size)
       (natp lower) (natp upper)
       (<= lower address)
       (<= (+ address size) upper)))

(defun proof-disjoint-p (start end other-start other-end)
  (or (<= end other-start) (<= other-end start)))

(defun proof-align-up (address alignment)
  (* (nfix alignment) (ceiling (nfix address) (nfix alignment))))

(defun proof-decode (word)
  (let ((decoded (boymoo-model::a64-decode word)))
    (cond
     ((not (eq decoded :undefined)) decoded)
     ((not (unsigned-byte-p 32 word)) :undefined)
     ((boymoo-model::a64-match word #xfffffc00 #xdac01000)
      (list :clz (boymoo-model::a64-field word 0 5)
            (boymoo-model::a64-field word 5 5)))
     ((boymoo-model::a64-match word #xffe00c10 #xfa400000)
      (list :ccmp (boymoo-model::a64-field word 5 5)
            (boymoo-model::a64-field word 16 5)
            (boymoo-model::a64-field word 12 4)
            (boymoo-model::a64-field word 0 4)))
     (t :undefined))))

(defthm proof-decode-agrees-with-model
  (implies (not (eq (boymoo-model::a64-decode word) :undefined))
           (equal (proof-decode word) (boymoo-model::a64-decode word)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-decode))))

(defun proof-execute (instruction machine)
  (case (car instruction)
    (:clz
     (boymoo-model::a64-write-reg
      (cadr instruction) 64 nil
      (- 64 (integer-length (proof-reg (caddr instruction) machine)))
      (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
    (:ccmp
     (let ((next (boymoo-model::a64-set-pc
                  (+ 4 (boymoo-model::a64-pc machine)) machine)))
       (if (boymoo-model::a64-condition (cadddr instruction)
                                       (boymoo-model::a64-nzcv machine))
           (boymoo-model::a64-exec-arithmetic
            3 64 31 (cadr instruction) (proof-reg (caddr instruction) machine)
            nil next)
         (boymoo-model::a64-set-nzcv (car (cddddr instruction)) next))))
    (otherwise (boymoo-model::a64-execute instruction machine))))

(defun proof-decode-at (address machine)
  (proof-decode (boymoo-model::a64-load 4 address machine)))

(defun proof-cpu-step (machine)
  (proof-execute (proof-decode-at (boymoo-model::a64-pc machine) machine)
                 machine))

(defun proof-byte-list (count address machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (boymoo-model::a64-load 1 address machine)
          (proof-byte-list (1- count) (1+ (ifix address)) machine))))

(defun proof-string-bytes (chars)
  (if (atom chars)
      nil
    (cons (char-code (car chars)) (proof-string-bytes (cdr chars)))))

(defun proof-byte-characters (bytes)
  (if (atom bytes)
      nil
    (cons (code-char (car bytes)) (proof-byte-characters (cdr bytes)))))

(defun proof-load-string (count address machine)
  (coerce (proof-byte-characters (proof-byte-list count address machine))
          'string))

(defun proof-overlay-bytes (bytes address memory omit-zero)
  (if (atom bytes)
      memory
    (let ((byte (boymoo-model::a64-unsigned 8 (car bytes)))
          (rest (proof-overlay-bytes (cdr bytes) (1+ (ifix address))
                                     memory omit-zero)))
      (if (and omit-zero (equal byte 0))
          rest
        (acons (boymoo-model::a64-unsigned 64 address) byte rest)))))

(defun proof-store-bytes (bytes address machine)
  (update-nth 4 (proof-overlay-bytes bytes address (boymoo-model::a64-memory machine) nil)
              machine))

(defun proof-store-string (string address machine)
  (proof-store-bytes (proof-string-bytes (coerce string 'list)) address machine))

; Loading into a cleared region can omit the zero bytes from sparse memory.
(defun proof-load-cleared-string (string address machine)
  (update-nth 4 (proof-overlay-bytes (proof-string-bytes (coerce string 'list))
                                     address (boymoo-model::a64-memory machine) t)
              machine))

(defun proof-fragments-size (fragments)
  (if (atom fragments)
      0
    (+ (length (car fragments)) (proof-fragments-size (cdr fragments)))))

(defun proof-fragments-p (fragments)
  (if (atom fragments)
      (null fragments)
    (and (stringp (car fragments))
         (proof-fragments-p (cdr fragments)))))

(defun proof-image-p (image)
  (and (consp image)
       (natp (car image))
       (proof-fragments-p (cdr image))
       (equal (car image) (proof-fragments-size (cdr image)))))

(defun proof-fragments-at-p (fragments address machine)
  (if (atom fragments)
      (null fragments)
    (and (equal (proof-load-string (length (car fragments)) address machine)
                (car fragments))
         (proof-fragments-at-p (cdr fragments)
                               (+ address (length (car fragments)))
                               machine))))

(defun proof-image-at-p (image address machine)
  (and (proof-image-p image)
       (proof-span-p address (car image))
       (proof-fragments-at-p (cdr image) address machine)))
