(in-package "BOYMOO-COMPILER")

(include-book "a64")

(set-verify-guards-eagerness 0)

; The mapping uses PROT_READ, PROT_WRITE, MAP_PRIVATE, MAP_ANONYMOUS and
; MAP_NORESERVE. The runtime maps a large span of address space for each
; heap space and touches only the pages it uses, as it does on macOS.
; Without MAP_NORESERVE, Linux in its default overcommit mode refuses a
; mapping larger than its memory and swap together, even if most of it is
; never touched.
(defun linux-system-code ()
  '((:label "sys:map")
    (:mov 1 0)
    (:movz 0 0 0)
    (:movz 2 3 0)
    (:movz 3 #x4022 0)
    (:movn 4 0 0)
    (:movz 5 0 0)
    (:movz 8 222 0)
    (:svc 0)
    (:cmp 0 0)
    (:csel 0 0 31 :ge)
    (:ret)
    (:label "sys:release")
    (:movz 2 4 0)
    (:movz 8 233 0)
    (:svc 0)
    (:ret)
    (:label "sys:unmap")
    (:movz 8 215 0)
    (:svc 0)
    (:ret)
    (:label "sys:read")
    (:movz 8 63 0)
    (:svc 0)
    (:ret)
    (:label "sys:write")
    (:movz 8 64 0)
    (:svc 0)
    (:ret)
    (:label "sys:exit")
    (:movz 8 94 0)
    (:svc 0)
    (:label "sys:exit:halt")
    (:b "sys:exit:halt")
    (:label "os:main")
    (:bl "rt:start")
    (:movz 0 1 0)
    (:b "sys:exit")))

(defconst *elf-load-address* #x400000)
(defconst *elf-segment-alignment* #x10000)
(defconst *elf-code-offset* #x1000)

(defun elf-prepend-zeroes (left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (elf-prepend-zeroes (- left 1) (cons (code-char 0) acc))))

(defun elf-prepend-le (word left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (let ((high (ash word -8)))
      (cons (code-char (- word (ash high 8)))
            (elf-prepend-le high (- left 1) acc)))))

(defun elf-prepend-header (entry file-size acc)
  (let* ((header-size 64)
         (program-header-size 56)
         (acc (elf-prepend-zeroes
               (- *elf-code-offset* (+ header-size program-header-size)) acc))
         (acc (elf-prepend-le *elf-segment-alignment* 8 acc)) ; p_align
         (acc (elf-prepend-le file-size 8 acc))              ; p_memsz
         (acc (elf-prepend-le file-size 8 acc))              ; p_filesz
         (acc (elf-prepend-le *elf-load-address* 8 acc))      ; p_paddr
         (acc (elf-prepend-le *elf-load-address* 8 acc))      ; p_vaddr
         (acc (elf-prepend-le 0 8 acc))                      ; p_offset
         (acc (elf-prepend-le 5 4 acc))                      ; p_flags (PF_R + PF_X)
         (acc (elf-prepend-le 1 4 acc))                      ; p_type (PT_LOAD)
         (acc (elf-prepend-zeroes 6 acc))                    ; e_shentsize, e_shnum, e_shstrndx
         (acc (elf-prepend-le 1 2 acc))                      ; e_phnum
         (acc (elf-prepend-le program-header-size 2 acc))    ; e_phentsize
         (acc (elf-prepend-le header-size 2 acc))            ; e_ehsize
         (acc (elf-prepend-le 0 4 acc))                      ; e_flags
         (acc (elf-prepend-le 0 8 acc))                      ; e_shoff
         (acc (elf-prepend-le header-size 8 acc))            ; e_phoff
         (acc (elf-prepend-le entry 8 acc))                  ; e_entry
         (acc (elf-prepend-le 1 4 acc))                      ; e_version
         (acc (elf-prepend-le 183 2 acc))                    ; e_machine (EM_AARCH64)
         (acc (elf-prepend-le 2 2 acc)))                     ; e_type (ET_EXEC)
    (elf-prepend-le #x00010102464c457f 16 acc)))              ; e_ident

(defun elf-image-executable (image entry)
  (let ((code-size (car image)))
    (if (and (natp entry) (< entry code-size)
             (equal entry (ash (ash entry -2) 2)))
        (let ((header (elf-prepend-header (+ *elf-load-address* *elf-code-offset* entry)
                                         (+ *elf-code-offset* code-size) nil)))
          (image-string (cons (coerce header 'string) (cdr image))))
      "")))

(defun elf-executable (code entry)
  (elf-image-executable (cons (length code) (list code)) entry))
