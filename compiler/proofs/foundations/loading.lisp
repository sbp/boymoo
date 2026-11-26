(in-package "BOYMOO-PROOFS")

(include-book "kernel")

(logic)
(set-verify-guards-eagerness 0)

; These are the address and file offset of the assembled image.
(defconst *proof-linux-file-base* #x400000)
(defconst *proof-linux-code-offset* #x1000)
(defconst *proof-linux-code-base*
  (+ *proof-linux-file-base* *proof-linux-code-offset*))

(defun proof-file-le (count index file)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (char-code (char file index))
       (* 256 (proof-file-le (1- count) (1+ (nfix index)) file)))))

(defun proof-elf-entry (file) (proof-file-le 8 24 file))

; Recognize the single loadable executable segment with no relocation
; and with an entry in the part following the headers and their padding.
(defun proof-elf-p (file)
  (and (stringp file)
       (< *proof-linux-code-offset* (length file))
       (<= (+ *proof-linux-file-base* (length file)) (expt 2 63))
       (equal (proof-file-le 16 0 file) #x00010102464c457f)
       (equal (proof-file-le 2 16 file) 2)
       (equal (proof-file-le 2 18 file) 183)
       (equal (proof-file-le 4 20 file) 1)
       (equal (proof-file-le 8 32 file) 64)
       (equal (proof-file-le 8 40 file) 0)
       (equal (proof-file-le 4 48 file) 0)
       (equal (proof-file-le 2 52 file) 64)
       (equal (proof-file-le 2 54 file) 56)
       (equal (proof-file-le 2 56 file) 1)
       (equal (proof-file-le 6 58 file) 0)
       (equal (proof-file-le 4 64 file) 1)
       (equal (proof-file-le 4 68 file) 5)
       (equal (proof-file-le 8 72 file) 0)
       (equal (proof-file-le 8 80 file) *proof-linux-file-base*)
       (equal (proof-file-le 8 88 file) *proof-linux-file-base*)
       (equal (proof-file-le 8 96 file) (length file))
       (equal (proof-file-le 8 104 file) (length file))
       (equal (proof-file-le 8 112 file) #x10000)
       (let ((entry (proof-elf-entry file)))
         (and (equal (mod entry 4) 0)
              (proof-subspan-p entry 4 *proof-linux-code-base*
                               (+ *proof-linux-file-base* (length file)))))))

(defun proof-load-linux (file machine regions page input replies)
  (let* ((base *proof-linux-file-base*)
         (end (+ base (length file)))
         (sp (boymoo-model::a64-sp machine)))
    (if (and (proof-elf-p file)
             (stringp input)
             (proof-page-size-p page)
             (proof-regions-p regions)
             (proof-region-disjoint-p base (proof-align-up end page) regions)
             (<= 16 sp)
             (equal (mod sp 16) 0)
             (proof-covered-p (- sp 16) 16 :write regions))
        (let* ((memory (proof-clear-memory base (proof-align-up end page)
                                           (boymoo-model::a64-memory machine)))
               (machine (proof-load-cleared-string file base (update-nth 4 memory machine)))
               (machine (boymoo-model::a64-set-pc (proof-elf-entry file) machine)))
          (proof-world machine
                       (cons (proof-region base (proof-align-up end page) :rx) regions)
                       page (proof-string-bytes (coerce input 'list))
                       nil nil replies nil))
      nil)))
