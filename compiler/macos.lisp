(in-package "BOYMOO-COMPILER")

(include-book "a64")
(include-book "sha256")

(set-verify-guards-eagerness 0)

; Darwin reports syscall errors with carry set and the error number in x0.
(defun system-code ()
  '((:label "sys:map")
    (:mov 1 0)
    (:movz 0 0 0)
    (:movz 2 3 0)
    (:movz 3 #x1002 0)
    (:movn 4 0 0)
    (:movz 5 0 0)
    (:movz 16 197 0)
    (:svc #x80)
    (:csel 0 0 31 :lo)
    (:ret)
    (:label "sys:release")
    (:movz 2 3 0)
    (:movz 3 #x1012 0)
    (:movn 4 0 0)
    (:movz 5 0 0)
    (:movz 16 197 0)
    (:svc #x80)
    (:b-cond :hs "sys:io-error")
    (:movz 0 0 0)
    (:ret)
    (:label "sys:unmap")
    (:movz 16 73 0)
    (:svc #x80)
    (:b-cond :hs "sys:io-error")
    (:ret)
    (:label "sys:read")
    (:movz 16 3 0)
    (:svc #x80)
    (:b-cond :hs "sys:io-error")
    (:ret)
    (:label "sys:write")
    (:movz 16 4 0)
    (:svc #x80)
    (:b-cond :hs "sys:io-error")
    (:ret)
    (:label "sys:io-error")
    (:neg 0 0)
    (:ret)
    (:label "sys:exit")
    (:movz 16 1 0)
    (:svc #x80)
    (:label "sys:exit:halt")
    (:b "sys:exit:halt")
    (:label "os:main")
    (:bl "rt:start")
    (:movz 0 1 0)
    (:b "sys:exit")))

(defconst *macho-text-address* #x100000000)
(defconst *macho-text-page-size* #x4000)
(defconst *macho-hash-page-size* #x1000)
(defconst *macho-code-offset* #x1000)
(defconst *macho-identifier* "boymoo")

(defun macho-prepend-zeroes (left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (macho-prepend-zeroes (- left 1) (cons (code-char 0) acc))))

(defun macho-prepend-string (s left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (macho-prepend-string s (- left 1) (cons (char s (- left 1)) acc))))

(defun macho-prepend-le (word left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (let ((high (ash word -8)))
      (cons (code-char (- word (ash high 8)))
            (macho-prepend-le high (- left 1) acc)))))

(defun macho-prepend-le32s (words acc)
  (if (atom words)
      acc
    (macho-prepend-le (car words) 4 (macho-prepend-le32s (cdr words) acc))))

(defun macho-prepend-be32s (words acc)
  (if (atom words)
      acc
    (sha256-prepend-be (car words) 4 (macho-prepend-be32s (cdr words) acc))))

(defun macho-prepend-padded-name (name size acc)
  (let ((n (length name)))
    (macho-prepend-string name n (macho-prepend-zeroes (- size n) acc))))

(defun macho-prepend-install-name (name size acc)
  (cons #\/ (macho-prepend-padded-name name (- size 1) acc)))

(defun macho-prepend-segment (name address space offset bytes protections acc)
  (let* ((acc (macho-prepend-le32s (list protections protections 0 0) acc))
         (acc (macho-prepend-le bytes 8 acc))
         (acc (macho-prepend-le offset 8 acc))
         (acc (macho-prepend-le space 8 acc))
         (acc (macho-prepend-le address 8 acc))
         (acc (macho-prepend-padded-name name 16 acc)))
    (macho-prepend-le32s '(#x19 72) acc)))

(defun macho-segment-size (bytes)
  (ash (ash (+ bytes (- *macho-text-page-size* 1)) -14) 14))

(defun macho-header (entry text-size sig-size)
  (let* ((command-count 7)
         (command-bytes (+ 72 72 72 48 32 24 16))
         (acc (macho-prepend-zeroes (- *macho-code-offset* (+ 32 command-bytes)) nil))
         ; LC_CODE_SIGNATURE points to the embedded signature.
         (acc (macho-prepend-le32s (list #x1d 16 text-size sig-size) acc))
         ; LC_MAIN gives the file offset of the entry point.
         (acc (macho-prepend-le 0 8 acc))
         (acc (macho-prepend-le (+ *macho-code-offset* entry) 8 acc))
         (acc (macho-prepend-le32s '(#x80000028 24) acc))
         ; LC_LOAD_DYLINKER names dyld.
         (acc (macho-prepend-install-name "usr/lib/dyld" 20 acc))
         (acc (macho-prepend-le32s '(#xe 32 12) acc))
         ; LC_DYLD_INFO_ONLY describes empty relocation and export streams.
         (acc (macho-prepend-le32s '(#x80000022 48 0 0 0 0 0 0 0 0 0 0) acc))
         (acc (macho-prepend-segment "__LINKEDIT" (+ *macho-text-address* text-size)
                                    (macho-segment-size sig-size) text-size sig-size 1 acc))
         (acc (macho-prepend-segment "__TEXT" *macho-text-address* text-size
                                    0 text-size 5 acc))
         (acc (macho-prepend-segment "__PAGEZERO" 0 *macho-text-address* 0 0 0 acc)))
    (coerce (macho-prepend-le32s
             (list #xfeedfacf #x0100000c 0 2 command-count command-bytes #x200085 0)
             acc)
            'string)))

; CodeDirectory version 0x20400 has an 88-byte header. The identifier
; includes its terminating zero byte.
(defun macho-code-directory-hash-offset ()
  (+ 88 (length *macho-identifier*) 1))

(defun macho-code-directory-size (slots)
  (+ (macho-code-directory-hash-offset) (ash slots 5)))

(defun macho-blob-size (slots)
  (+ 20 (macho-code-directory-size slots)))

(defun macho-signature-size (slots)
  (ash (ash (+ (macho-blob-size slots) 15) -4) 4))

; The first slot covers the header. The remaining slots cover the
; assembled image and its zero padding in file order.
(defun macho-code-slots (chunks at left digests)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      (reverse-onto digests nil)
    (mv-let (digest chunks at)
      (sha256-page chunks at *macho-hash-page-size*)
      (macho-code-slots chunks at (- left 1)
                        (cons (coerce (sha256-prepend-digest digest nil) 'string)
                              digests)))))

(defun macho-signature-prefix (header text-size slots)
  (let* ((blob-size (macho-blob-size slots))
         (digest (sha256-range-words header 0 *macho-code-offset* *macho-code-offset*))
         (acc (sha256-prepend-digest digest nil))
         (acc (macho-prepend-padded-name *macho-identifier*
                                         (+ (length *macho-identifier*) 1) acc))
         ; The executable segment begins at file offset zero and is the main binary.
         (acc (sha256-prepend-be 1 8 acc))
         (acc (sha256-prepend-be text-size 8 acc))
         (acc (macho-prepend-zeroes 28 acc))
         ; SHA-256 uses 32-byte hashes and a page-size exponent of 12.
         (acc (macho-prepend-be32s (list #x2002000c 0) acc))
         (acc (macho-prepend-be32s
               (list #xfade0c02 (macho-code-directory-size slots)
                     #x20400 #x20002 (macho-code-directory-hash-offset)
                     88 0 slots text-size)
               acc)))
    (coerce (macho-prepend-be32s (list #xfade0cc0 blob-size 1 0 20) acc) 'string)))

(defun macho-image-executable (image entry)
  (let* ((code-size (car image))
         (text-size (macho-segment-size (+ *macho-code-offset* code-size))))
    (if (and (natp entry) (<= (+ entry 4) code-size)
             (equal entry (ash (ash entry -2) 2))
             (< text-size #x100000000))
        (let* ((slots (ash text-size -12))
               (sig-size (macho-signature-size slots))
               (header (macho-header entry text-size sig-size))
               (code (cdr image))
               (digests (macho-code-slots code 0 (- slots 1) nil))
               (signature (cons (macho-signature-prefix header text-size slots)
                                (image-onto digests
                                            (image-padding (- sig-size (macho-blob-size slots)) nil))))
               (tail (image-padding (- text-size (+ *macho-code-offset* code-size))
                                    signature)))
          (image-string (cons header (image-onto code tail))))
      "")))

(defun macho-executable (code entry)
  (macho-image-executable (cons (length code) (list code)) entry))
