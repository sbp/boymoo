(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

; The indexer refuses every attach line whose target is IF. On refusal it
; returns no definitions, names, attachments, sources, packages, entry or
; target, and the compiler writes no executable.
(defthm generated-attachment-to-if-is-refused
  (implies (and (consp line) (equal (car line) "attach")
                (equal (caddr line) boymoo-compiler::*if-name*))
           (equal (boymoo-compiler::index-lines
                   (cons line lines) defs names attachments sources packages entry target)
                  (list nil nil nil nil nil nil nil)))
  :hints (("Goal" :in-theory (enable boymoo-compiler::compiler-error)
                  :expand ((boymoo-compiler::index-lines
                            (cons line lines) defs names attachments sources packages entry target)))))
