(in-package "BOYMOO-COMPILER")

(include-book "emit")
(include-book "proofs/rega-check")
(include-book "simplify")
(include-book "lower")
(include-book "expand")
(include-book "rt-qir")
(include-book "opt")
(include-book "macos")
(include-book "linux")
(include-book "runtime")

(set-verify-guards-eagerness 0)

; The driver of the many-pass compiler: program text to an executable,
; through the passes of compiler/DESIGN.md, section 2.

; P6 to P8 for one QIR-M function: the MIR function with homes. The
; register assignment of every function is checked by the validator of
; compiler/proofs/rega-check.lisp, and a function whose assignment fails
; the check stops the compiler.
(defun back-end-function (fn)
  (car (rega-validated-program (list (isel-function (abi-function fn))))))

; The functions are taken one at a time through the passes, so that only
; the forms of one function are held at once beside the results.
(defun back-end-functions (fns acc)
  (if (atom fns)
      acc
    (back-end-functions (cdr fns) (cons (back-end-function (car fns)) acc))))

; Every item of the executable: the system's routines, the runtime, the
; entry adapter, the compiled functions, which P9 writes from the MIR
; functions MFNS, and the static block.
(defun program-items (entry mfns data system)
  (let* ((code (emit-items system nil))
         (code (emit-items (runtime-code) code))
         (code (emit-entry-adapter entry code))
         (code (emit-program mfns code)))
    (reverse-onto code (list '(:label "data:static") (list :image (car data) (cdr data))))))

(defun program-executable (entry mfns data linux)
  (mv-let (code location)
    (a64-assemble-image (program-items entry mfns data (if linux (linux-system-code) (system-code)))
                        "os:main")
    (if linux
        (elf-image-executable code location)
      (macho-image-executable code location))))

; An executable from program text, for its static block and entry, and
; QIR-M functions written apart from it: a test of the back end.
(defun compile-qir (text fns)
  (let ((lines (read-program text)))
    (mv-let (defs names attachments sources packages entry target)
      (index-lines lines nil nil nil nil nil nil nil)
      (declare (ignore defs names attachments sources))
      (mv-let (data constants)
        (data-build lines packages)
        (declare (ignore constants))
        (program-executable entry (reverse-onto (back-end-functions fns nil) nil) data
                       (eq target :linux))))))

; The definition of the entry, as compile-entry-definitions in
; compiler/single/compile.lisp makes it.
(defun remove-definition (entry defs prefix)
  (cond ((atom defs) (reverse-onto prefix nil))
        ((equal entry (caar defs)) (reverse-onto prefix (cdr defs)))
        (t (remove-definition entry (cdr defs) (cons (car defs) prefix)))))

(defun entry-definitions (entry defs context)
  (mv-let (target arity routine)
    (resolve-call-info entry context)
    (cond ((and arity (not (equal arity 1)))
           (compiler-error "The entry must name a function of one argument: ~x0." entry))
          ((and arity (equal target entry) (not routine)) defs)
          (t (cons (list entry '("BOYMOO-COMPILER::ENTRY-INPUT")
                         (list target "BOYMOO-COMPILER::ENTRY-INPUT"))
                   (remove-definition entry defs nil))))))

; The passes from L0 to QIR-M. P2 runs when SIMPLIFY is not NIL, and
; P5 when OPTIMIZE is not NIL; each can be left out without changing what
; a program computes.
; P2 for one definition of L1, as simplify-program does it for each,
; with the analysis and the functions to inline of the whole program.
(defun simplify-definition (definition analysis inlinees)
  (let ((next (car (table-tree-get (car definition) analysis))))
    (mv-let (term next)
      (simplify-term (caddr definition) 0 nil nil inlinees *inline-depth* next)
      (declare (ignore next))
      (mv-let (term used)
        (simplify-live-term term nil)
        (declare (ignore used))
        (list (car definition) (cadr definition) term)))))

; P2 (when SIMPLIFY) to P8 for each definition in turn. ANALYSIS and
; INLINEES are P2's, from the whole program.
(defun middle-end-functions (defs simplify analysis inlinees symbols optimize acc)
  (if (atom defs)
      acc
    (let* ((def (if simplify (simplify-definition (car defs) analysis inlinees) (car defs)))
           (fn (expand-fn (lower-def def) symbols t)))
      (middle-end-functions (cdr defs) simplify analysis inlinees symbols optimize
                           (cons (back-end-function (if optimize (opt-function fn) fn)) acc)))))

(defun rt-functions (fns optimize acc)
  (if (atom fns)
      acc
    (rt-functions (cdr fns) optimize
                     (cons (back-end-function (if optimize (opt-function (car fns)) (car fns)))
                           acc))))

; P1 to P8: the MIR functions with homes, in the order of the
; definitions, then the routines of the runtime written in QIR. P1 and
; P2's analysis take the whole program; P2 itself and P3 to P8 take one
; function at a time, so that only one function's forms are held at once
; beside the results.
(defun middle-end (defs context simplify optimize)
  (let* ((l1 (resolve-definitions defs context))
         (analysis (if simplify (simplify-analyze l1 nil) nil))
         (inlinees (if simplify (simplify-inlinees l1 analysis nil) nil))
         (acc (middle-end-functions l1 simplify analysis inlinees
                                   (ex-index-symbols (caddr context) 12 nil) optimize nil)))
    (reverse-onto (rt-functions (rt-qir-functions) optimize acc) nil)))

; Whether COMPILE-TEXT runs P2 and P5.
(defconst *simplify-enabled* t)
(defconst *optimize-enabled* t)

; COMPILE-TEXT-WITH takes the input as a string and gives the
; executable as a string, as COMPILE-TEXT does in
; compiler/single/compile.lisp, with P2 and P5 run or not as SIMPLIFY and
; OPTIMIZE say.
(defun compile-text-with (text simplify optimize)
  (let ((lines (read-program text)))
    (mv-let (defs names attachments sources packages entry target)
      (index-lines lines nil nil nil nil nil nil nil)
      (if (not entry)
          (compiler-error "The input needs an entry line: ~x0." nil)
        (let ((resolved (resolve-attachments sources attachments nil (length sources))))
          (mv-let (data constants)
            (data-build lines packages)
            (let* ((context (list names resolved constants))
                   (defs (entry-definitions entry defs context)))
              (program-executable entry (middle-end defs context simplify optimize) data
                             (eq target :linux)))))))))

(defun compile-text (text)
  (compile-text-with text *simplify-enabled* *optimize-enabled*))
