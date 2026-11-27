; Writes the offset of every named label of the executable that the
; many-pass compiler writes from one input, for compiler/bench/profile.sh,
; which replaces PROFILE-INPUT by the absolute name of the input and runs
; this file in a directory of certified books of the many-pass compiler.
; The items are those of COMPILE-TEXT, laid out as A64-LAYOUT lays them
; out; a label is named when it is a string or (:FN NAME). Each line
; between LABELS-BEGIN and LABELS-END is the offset in bytes from the
; start of the code, then the label.
(ld "version.lsp")
(ld "package.lsp")
(include-book "compile")
(in-package "BOYMOO-COMPILER")
(set-guard-checking :none)
(defun profile-labels (items pc acc)
  (if (atom items)
      acc
    (let ((item (car items)))
      (if (eq (car item) :label)
          (let ((key (cadr item)))
            (profile-labels (cdr items) pc
                            (cond ((stringp key) (cons (cons pc key) acc))
                                  ((and (consp key) (eq (car key) :fn))
                                   (cons (cons pc (cadr key)) acc))
                                  (t acc))))
        (profile-labels (cdr items) (+ pc (a64-image-item-size item)) acc)))))
(defun profile-items (text)
  (let ((lines (read-program text)))
    (mv-let (defs names attachments sources packages entry target)
      (index-lines lines nil nil nil nil nil nil nil)
      (let ((resolved (resolve-attachments sources attachments nil (length sources))))
        (mv-let (data constants)
          (data-build lines packages)
          (let* ((context (list names resolved constants))
                 (defs (entry-definitions entry defs context)))
            (program-items entry (middle-end defs context *simplify-enabled* *optimize-enabled*) data
                      (if (eq target :linux) (linux-system-code) (system-code)))))))))
(defun profile-print (labels)
  (if (atom labels)
      nil
    (prog2$ (cw "~x0 ~s1~%" (caar labels) (cdar labels))
            (profile-print (cdr labels)))))
(defun profile-main (text)
  (prog2$ (cw "LABELS-BEGIN~%")
          (prog2$ (profile-print (reverse (profile-labels (profile-items text) 0 nil)))
                  (cw "LABELS-END~%"))))
(profile-main (read-file-into-string "PROFILE-INPUT"))
(good-bye)
