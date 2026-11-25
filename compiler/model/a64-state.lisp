(in-package "BOYMOO-MODEL")

(logic)
(set-verify-guards-eagerness 0)

(defun a64-ones (width)
  (1- (ash 1 (nfix width))))

(defun a64-unsigned (width value)
  (logand (ifix value) (a64-ones width)))

(defun a64-field (word start width)
  (a64-unsigned width (ash (ifix word) (- (nfix start)))))

(defun a64-signed (width value)
  (let ((bits (a64-unsigned width value)))
    (if (and (posp width) (logbitp (1- width) bits))
        (- bits (ash 1 width))
      bits)))

(defun a64-state (registers sp pc nzcv memory)
  (list registers (a64-unsigned 64 sp) (a64-unsigned 64 pc)
        (a64-unsigned 4 nzcv) memory))

(defun a64-registers (machine) (nth 0 machine))
(defun a64-sp (machine) (a64-unsigned 64 (nth 1 machine)))
(defun a64-pc (machine) (a64-unsigned 64 (nth 2 machine)))
(defun a64-nzcv (machine) (a64-unsigned 4 (nth 3 machine)))
(defun a64-memory (machine) (nth 4 machine))

(defun a64-set-pc (pc machine)
  (update-nth 2 (a64-unsigned 64 pc) machine))

(defun a64-set-nzcv (nzcv machine)
  (update-nth 3 (a64-unsigned 4 nzcv) machine))

(defun a64-read-reg (reg width use-sp machine)
  (a64-unsigned
   width
   (if (and (natp reg) (< reg 31))
       (cdr (assoc-equal reg (a64-registers machine)))
     (if (and (equal reg 31) use-sp) (a64-sp machine) 0))))

(defun a64-write-reg (reg width use-sp value machine)
  (let ((value (a64-unsigned width value)))
    (cond ((and (natp reg) (< reg 31))
           (update-nth 0 (put-assoc-equal reg value (a64-registers machine))
                       machine))
          ((and (equal reg 31) use-sp)
           (update-nth 1 (a64-unsigned 64 value) machine))
          (t machine))))

(defun a64-byte (address memory)
  (a64-unsigned 8 (cdr (assoc-equal (a64-unsigned 64 address) memory))))

(defun a64-read-bytes (count address memory)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (logior (a64-byte address memory)
            (ash (a64-read-bytes (1- count) (1+ (ifix address)) memory) 8))))

(defun a64-write-bytes (count address value memory)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      memory
    (a64-write-bytes (1- count) (1+ (ifix address)) (ash (ifix value) -8)
                     (put-assoc-equal (a64-unsigned 64 address)
                                      (a64-unsigned 8 value) memory))))

(defun a64-load (count address machine)
  (a64-read-bytes count address (a64-memory machine)))

(defun a64-store (count address value machine)
  (update-nth 4 (a64-write-bytes count address value (a64-memory machine))
              machine))
