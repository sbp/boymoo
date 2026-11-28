(in-package "BOYMOO-PROOFS")

; What the Linux loader model PROOF-LOAD-LINUX gives a program: the
; program counter at the ELF entry, the file mapped read and execute at
; its load address, the input as a byte stream, empty output streams,
; and the registers and stack pointer of the machine it was given. The
; same facts are then stated for the files that ELF-IMAGE-EXECUTABLE
; writes.

(include-book "elf")

(logic)
(set-verify-guards-eagerness 0)

(defthm linux-a64-unsigned-identity
  (implies (and (natp width) (natp x) (< x (expt 2 width)))
           (equal (boymoo-model::a64-unsigned width x) x))
  :hints (("Goal" :in-theory (enable ash)
                  :use ((:instance linux-logand-mask (n width))))))

(defthm linux-elf-entry-range
  (implies (proof-elf-p file)
           (and (natp (proof-elf-entry file))
                (< (proof-elf-entry file) (expt 2 64))
                (<= *proof-linux-code-base* (proof-elf-entry file))
                (<= (+ 4 (proof-elf-entry file))
                    (+ *proof-linux-file-base* (length file)))))
  :rule-classes nil)

(defthm linux-elf-length-range
  (implies (proof-elf-p file)
           (and (stringp file)
                (< *proof-linux-code-offset* (length file))
                (<= (+ *proof-linux-file-base* (length file)) (expt 2 63))))
  :rule-classes nil)

(defthm linux-align-up-covers
  (implies (and (natp end) (proof-page-size-p page))
           (and (natp (proof-align-up end page))
                (<= end (proof-align-up end page))))
  :hints (("Goal" :use ((:instance linux-round-up-covers (e end) (c page))))))

(in-theory (disable proof-elf-p proof-align-up proof-page-size-p
                    boymoo-model::a64-unsigned))

;;; The world after loading

(defthm linux-load-pc
  (implies (proof-load-linux file machine regions page input replies)
           (equal (proof-world-pc
                   (proof-load-linux file machine regions page input replies))
                  (proof-elf-entry file)))
  :hints (("Goal" :use (linux-elf-entry-range linux-elf-length-range))))

(defthm linux-load-regions
  (implies (proof-load-linux file machine regions page input replies)
           (equal (proof-world-regions
                   (proof-load-linux file machine regions page input replies))
                  (cons (proof-region *proof-linux-file-base*
                                      (proof-align-up
                                       (+ *proof-linux-file-base* (length file))
                                       page)
                                      :rx)
                        regions))))

(defthm linux-load-streams
  (implies (proof-load-linux file machine regions page input replies)
           (let ((world (proof-load-linux file machine regions page input replies)))
             (and (equal (proof-world-page-size world) page)
                  (equal (proof-world-input world)
                         (proof-string-bytes (coerce input 'list)))
                  (equal (proof-world-stdout world) nil)
                  (equal (proof-world-stderr world) nil)
                  (equal (proof-world-replies world) replies)
                  (equal (proof-world-stop world) nil)))))

(defthm linux-load-registers
  (implies (proof-load-linux file machine regions page input replies)
           (let ((loaded (proof-world-machine
                          (proof-load-linux file machine regions page input replies))))
             (and (equal (boymoo-model::a64-registers loaded)
                         (boymoo-model::a64-registers machine))
                  (equal (boymoo-model::a64-sp loaded)
                         (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-nzcv loaded)
                         (boymoo-model::a64-nzcv machine))))))

(defthm linux-load-code-executable
  (implies (proof-load-linux file machine regions page input replies)
           (proof-covered-p *proof-linux-code-base*
                            (- (length file) *proof-linux-code-offset*)
                            :execute
                            (proof-world-regions
                             (proof-load-linux file machine regions page input replies))))
  :hints (("Goal" :use (linux-elf-length-range
                        (:instance linux-align-up-covers
                                   (end (+ *proof-linux-file-base* (length file))))))))

(in-theory (disable proof-load-linux))

;;; Loading the files that the compiler writes

(defun linux-load-environment-p (size machine regions page input)
  (let ((sp (boymoo-model::a64-sp machine)))
    (and (stringp input)
         (proof-page-size-p page)
         (proof-regions-p regions)
         (proof-region-disjoint-p
          *proof-linux-file-base*
          (proof-align-up (+ *proof-linux-code-base* size) page)
          regions)
         (<= 16 sp)
         (equal (mod sp 16) 0)
         (proof-covered-p (- sp 16) 16 :write regions))))

(defthm linux-load-executable-accepted
  (implies (and (linux-elf-arguments-p image entry)
                (linux-load-environment-p (car image) machine regions page input))
           (proof-load-linux (boymoo-compiler::elf-image-executable image entry)
                             machine regions page input replies))
  :hints (("Goal" :in-theory (enable proof-load-linux)
                  :use linux-elf-image-executable-accepted)))

(defthm linux-load-executable-pc
  (implies (and (linux-elf-arguments-p image entry)
                (linux-load-environment-p (car image) machine regions page input))
           (equal (proof-world-pc
                   (proof-load-linux (boymoo-compiler::elf-image-executable image entry)
                                     machine regions page input replies))
                  (+ *proof-linux-code-base* entry)))
  :hints (("Goal" :use (linux-load-executable-accepted
                        (:instance linux-load-pc
                                   (file (boymoo-compiler::elf-image-executable
                                          image entry))))
                  :in-theory (disable proof-elf-entry))))

(defthm linux-load-executable-code-executable
  (implies (and (linux-elf-arguments-p image entry)
                (linux-load-environment-p (car image) machine regions page input))
           (proof-covered-p *proof-linux-code-base* (car image) :execute
                            (proof-world-regions
                             (proof-load-linux
                              (boymoo-compiler::elf-image-executable image entry)
                              machine regions page input replies))))
  :hints (("Goal" :use (linux-load-executable-accepted
                        (:instance linux-load-code-executable
                                   (file (boymoo-compiler::elf-image-executable
                                          image entry)))))))
