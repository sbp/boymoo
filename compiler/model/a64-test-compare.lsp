(in-package "BOYMOO-MODEL")

(logic)
(set-verify-guards-eagerness 0)
(set-guard-checking :none)

(defun a64-test-code-memory (code offset end base)
  (declare (xargs :measure (nfix (- end offset))))
  (if (and (natp offset) (natp end) (< offset end))
      (acons (+ base offset) (char-code (char code offset))
             (a64-test-code-memory code (1+ offset) end base))
    nil))

(defun a64-test-registers (registers overrides)
  (if (endp registers)
      nil
    (let ((register (car registers)))
      (acons register (boymoo-compiler::a64-test-register-word register overrides)
             (a64-test-registers (cdr registers) overrides)))))

; The record holds X0 through X30, with PC in the slot for X18,
; then SP, NZCV and the words in the test buffer.
(defun a64-test-observe-registers (register machine)
  (declare (xargs :measure (nfix (- 31 register))))
  (if (or (not (natp register)) (<= 31 register))
      nil
    (cons (if (= register 18)
              (a64-pc machine)
            (a64-read-reg register 64 nil machine))
          (a64-test-observe-registers (1+ register) machine))))

(defun a64-test-observe-buffer (words address machine)
  (declare (xargs :measure (nfix words)))
  (if (zp words)
      nil
    (cons (a64-load 8 address machine)
          (a64-test-observe-buffer (1- words) (+ address 8) machine))))

(defun a64-test-run-case (case-data items code base buffer)
  (let ((name (car case-data)))
    (mv-let (begin-code begin-offset)
      (boymoo-compiler::a64-assemble items (list :begin name))
      (declare (ignore begin-code))
      (mv-let (end-code end-offset)
        (boymoo-compiler::a64-assemble items (list :end name))
        (declare (ignore end-code))
        (let* ((begin (+ base begin-offset))
               (end (+ base end-offset))
               (registers (acons 28 buffer
                                 (a64-test-registers
                                  boymoo-compiler::*a64-test-input-registers*
                                  (cadr case-data))))
               (machine (a64-state registers
                                   (+ buffer boymoo-compiler::*a64-test-stack-offset*)
                                   begin (nth 3 case-data)
                                   (a64-test-code-memory code begin-offset end-offset base))))
          (mv-let (status last)
            (a64-run 64 begin end end machine)
            (if (eq status :return)
                (append (a64-test-observe-registers 0 last)
                        (list (a64-sp last) (a64-nzcv last))
                        (a64-test-observe-buffer
                         boymoo-compiler::*a64-test-buffer-words*
                         (+ buffer boymoo-compiler::*a64-test-buffer-offset*)
                         last))
              (list status (a64-pc last)))))))))

(defun a64-test-compare-cases (cases items code base buffer observed)
  (declare (xargs :hints (("Goal" :in-theory (disable a64-test-run-case)))))
  (if (endp cases)
      (endp observed)
    (let* ((case-data (car cases))
           (size (+ 33 boymoo-compiler::*a64-test-buffer-words*))
           (actual (take size observed))
           (expected (a64-test-run-case case-data items code base buffer)))
      (if (equal expected actual)
          (a64-test-compare-cases (cdr cases) items code base buffer
                                  (nthcdr size observed))
        (prog2$ (cw "Case ~x0.~%Processor gave ~x1.~%Model gave ~x2.~%"
                    (car case-data) actual expected)
                nil)))))

(defun a64-test-compare (observed)
  (let* ((base (car observed))
         (buffer (cadr observed))
         (items (boymoo-compiler::a64-test-items)))
    (and (posp base) (= (mod base 4096) 0)
         (posp buffer) (= (mod buffer 4096) 0)
         (a64-test-compare-cases boymoo-compiler::*a64-test-cases*
                                 items (boymoo-compiler::a64-bytes items)
                                 base buffer (cddr observed)))))
