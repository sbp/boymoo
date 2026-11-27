(in-package "BOYMOO-PROOFS")

; COMPILE-TEXT, for a program whose target is Linux, writes the ELF file
; of the image that the assembler lays out from the compiled items, with
; the entry at the label os:main. Loading that file by PROOF-LOAD-LINUX
; gives a world that meets PROOF-LINKED-IMAGE-P, the linked-image
; contract of the shared books, with the program counter at os:main.

(include-book "install")

(logic)
(set-verify-guards-eagerness 0)

; The first part of COMPILE-TEXT, up to the items it assembles: whether
; the program has an entry line, whether its target is Linux, and the
; items, which end with LINUX-SYSTEM-CODE.
(defun linux-text-items (text)
  (let ((lines (boymoo-compiler::read-program text)))
    (mv-let (defs names attachments sources packages entry target)
      (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)
      (let ((resolved (boymoo-compiler::resolve-attachments
                       sources attachments nil (length sources))))
        (mv-let (data constants)
          (boymoo-compiler::data-build lines packages)
          (let* ((context (list names resolved constants))
                 (defs (boymoo-compiler::compile-entry-definitions entry defs context)))
            (mv (if entry t nil)
                (eq target :linux)
                (boymoo-compiler::compile-items
                 entry defs context data (boymoo-compiler::linux-system-code)))))))))

(defun linux-text-image (text)
  (mv-let (ok linux items)
    (linux-text-items text)
    (declare (ignore ok linux))
    (mv-let (image entry)
      (boymoo-compiler::a64-assemble-image items "os:main")
      (declare (ignore entry))
      image)))

(defun linux-text-entry (text)
  (mv-let (ok linux items)
    (linux-text-items text)
    (declare (ignore ok linux))
    (mv-let (image entry)
      (boymoo-compiler::a64-assemble-image items "os:main")
      (declare (ignore image))
      entry)))

(defthm linux-compile-text-is-elf
  (implies (and (mv-nth 0 (linux-text-items text))
                (mv-nth 1 (linux-text-items text)))
           (equal (boymoo-compiler::compile-text text)
                  (boymoo-compiler::elf-image-executable
                   (linux-text-image text)
                   (linux-text-entry text))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::elf-image-executable
                                      boymoo-compiler::a64-assemble-image))))

(defun linux-text-program-items (text)
  (mv-let (ok linux items)
    (linux-text-items text)
    (declare (ignore ok linux))
    items))

(defthm linux-assembled-image-of-text
  (and (equal (mv-nth 0 (boymoo-compiler::a64-assemble-image
                         (linux-text-program-items text) "os:main"))
              (linux-text-image text))
       (equal (mv-nth 1 (boymoo-compiler::a64-assemble-image
                         (linux-text-program-items text) "os:main"))
              (linux-text-entry text)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::a64-assemble-image))))

(in-theory (disable linux-text-items linux-text-image linux-text-entry
                    linux-text-program-items boymoo-compiler::compile-text))

; The obligations that the other phases discharge: the program has an
; entry line and the Linux target, the assembled image and the offset of
; os:main meet LINUX-ELF-ARGUMENTS-P, and the environment meets
; LINUX-LOAD-ENVIRONMENT-P.
(defun linux-text-has-entry-p (text)
  (mv-let (ok linux items)
    (linux-text-items text)
    (declare (ignore linux items))
    ok))

(defun linux-text-target-p (text)
  (mv-let (ok linux items)
    (linux-text-items text)
    (declare (ignore ok items))
    linux))

(defun linux-text-obligations-p (text machine regions page input)
  (and (linux-text-has-entry-p text)
       (linux-text-target-p text)
       (linux-elf-arguments-p (linux-text-image text) (linux-text-entry text))
       (linux-load-environment-p (car (linux-text-image text))
                                 machine regions page input)))

(defthm linux-compiled-start-accepted
  (implies (linux-text-obligations-p text machine regions page input)
           (proof-compiled-start text machine regions page input replies))
  :hints (("Goal" :use ((:instance linux-load-executable-accepted
                                   (image (linux-text-image text))
                                   (entry (linux-text-entry text))))
                  :in-theory (disable linux-load-executable-accepted
                                      linux-elf-arguments-p
                                      linux-load-environment-p))))

(defthm linux-compiled-start-pc
  (implies (linux-text-obligations-p text machine regions page input)
           (equal (proof-world-pc
                   (proof-compiled-start text machine regions page input replies))
                  (+ *proof-linux-code-base* (linux-text-entry text))))
  :hints (("Goal" :use ((:instance linux-load-executable-pc
                                   (image (linux-text-image text))
                                   (entry (linux-text-entry text))))
                  :in-theory (disable linux-load-executable-pc
                                      linux-elf-arguments-p
                                      linux-load-environment-p
                                      proof-world-pc))))

(defthm linux-compiled-start-linked
  (implies (linux-text-obligations-p text machine regions page input)
           (proof-linked-image-p
            (linux-text-program-items text) "os:main" *proof-linux-code-base*
            (proof-compiled-start text machine regions page input replies)))
  :hints (("Goal" :use (linux-compiled-start-accepted
                        (:instance linux-load-executable-image
                                   (image (linux-text-image text))
                                   (entry (linux-text-entry text)))
                        (:instance linux-load-executable-code-executable
                                   (image (linux-text-image text))
                                   (entry (linux-text-entry text))))
                  :in-theory (disable linux-load-executable-image
                                      linux-load-executable-code-executable
                                      boymoo-compiler::a64-assemble-image
                                      proof-image-at-p
                                      proof-covered-p
                                      linux-load-environment-p))))

(defthm linux-compiled-start-streams
  (implies (linux-text-obligations-p text machine regions page input)
           (let ((world (proof-compiled-start text machine regions page input replies)))
             (and (equal (proof-world-input world)
                         (proof-string-bytes (coerce input 'list)))
                  (equal (proof-world-stdout world) nil)
                  (equal (proof-world-stderr world) nil)
                  (equal (proof-world-replies world) replies)
                  (equal (proof-world-stop world) nil)
                  (equal (boymoo-model::a64-registers (proof-world-machine world))
                         (boymoo-model::a64-registers machine))
                  (equal (boymoo-model::a64-sp (proof-world-machine world))
                         (boymoo-model::a64-sp machine)))))
  :hints (("Goal" :use ((:instance linux-compiled-start-accepted)
                        (:instance linux-load-streams
                                   (file (boymoo-compiler::compile-text text)))
                        (:instance linux-load-registers
                                   (file (boymoo-compiler::compile-text text))))
                  :in-theory (disable linux-compiled-start-accepted
                                      linux-load-streams linux-load-registers
                                      linux-text-obligations-p
                                      proof-world-input proof-world-stdout
                                      proof-world-stderr proof-world-replies
                                      proof-world-stop proof-world-machine
                                      boymoo-model::a64-registers
                                      boymoo-model::a64-sp))))
