(in-package "BOYMOO-PROOFS")

(include-book "machine")

(logic)
(set-verify-guards-eagerness 0)

; The Linux system code and the runtime precede the generated functions.
; The labels at the end complete references from the entry code. The
; collector's branch targets are within the fixed part of the text.
(defconst *collection-linux-items*
  (append (boymoo-compiler::linux-system-code)
          (boymoo-compiler::runtime-code)
          '((:label "rt:entry") (:ret)
            (:label "data:static") (:quad 0))))

(defconst *collection-linux-layout*
  (mv-let (length labels reversed)
    (boymoo-compiler::a64-layout *collection-linux-items* 0 nil nil)
    (declare (ignore reversed))
    (cons length labels)))

(defconst *collection-linux-instructions*
  (collection-decode-items *collection-linux-items*))

(defun collection-linux-offset (label)
  (boymoo-compiler::a64-offset label (cdr *collection-linux-layout*)))

(defun collection-linux-trace (label indices origin)
  (let ((offset (collection-linux-offset label)))
    (collection-indexed-trace indices
                              (nthcdr (ash offset -2) *collection-linux-instructions*)
                              (+ origin offset))))
