(in-package "BOYMOO-PROOFS")

(include-book "static-data")
(include-book "source-bounds")
(include-book "index-acceptance")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable assembly-accepted-program-reader-agrees
                           assembly-accepted-definition-index-agrees
                           assembly-accepted-line-index-agrees
                           assembly-accepted-attachment-chain-agrees
                           assembly-accepted-attachment-resolution-agrees
                           assembly-accepted-text-index-agrees
                           assembly-checked-text-index)))

(defmacro assembly-indexed-source-lines (lines)
  `(boymoo-compiler::index-lines ,lines nil nil nil nil nil nil nil))

(defun assembly-static-text-input-p (text)
  (let ((lines (boymoo-compiler::read-program text)))
    (mv-let (defs names attachments sources packages entry target)
      (assembly-indexed-source-lines lines)
      (declare (ignore defs names attachments sources entry target))
      (assembly-static-build-input-p lines packages))))

(local (in-theory (disable boymoo-compiler::read-program boymoo-compiler::index-lines
                           boymoo-compiler::resolve-attachments boymoo-compiler::data-build
                           boymoo-compiler::compile-entry-definitions
                           assembly-static-build-input-p assembly-constant-index-p proof-image-p)))

(local
 (defthm assembly-first-source-layout-result
   (equal (mv-nth 0 values) (car values))))

(local
 (defthm assembly-second-source-layout-result
   (equal (mv-nth 1 values) (cadr values))))

(defthm assembly-static-text-supplies-image-and-constants
  (let ((inputs (assembly-read-compiler-inputs text)))
    (implies (and inputs (assembly-static-text-input-p text))
             (and (proof-image-p (cadddr inputs))
                  (assembly-constant-index-p (caddr (caddr inputs)) 12))))
  :hints (("Goal"
           :use ((:instance assembly-data-build-produces-sized-image-and-typed-index
                            (lines (boymoo-compiler::read-program text))
                            (package-lines (mv-nth 4 (assembly-indexed-source-lines
                                                     (boymoo-compiler::read-program text))))))
           :in-theory (disable assembly-data-build-produces-sized-image-and-typed-index))))

(defun assembly-source-layout-input-p (text)
  (mv-let (accepted lines defs names resolved packages entry target)
    (assembly-checked-text-index text)
    (let ((context (list names resolved nil)))
      (and accepted entry
           (assembly-static-build-input-p lines packages)
           (assembly-entry-arity-p entry context)
           (< (assembly-source-prefix-upper-bound
               (boymoo-compiler::compile-entry-definitions entry defs context)
               (assembly-system-for-target target))
              (expt 2 20))))))

(local
 (defthm assembly-entry-arity-independent-of-constants
   (implies (syntaxp (not (equal constants ''nil)))
            (equal (assembly-entry-arity-p entry (list arities attachments constants))
                   (assembly-entry-arity-p entry (list arities attachments nil))))
   :hints (("Goal" :in-theory (e/d (assembly-entry-arity-p)
                                    (boymoo-compiler::index-get assoc-equal))))))

(local
 (defthm assembly-layout-input-supplies-source-bound
   (implies (assembly-source-layout-input-p text)
            (assembly-source-bounded-compiler-text-p text))
   :hints (("Goal"
            :use (assembly-accepted-text-index-agrees
                  assembly-static-text-supplies-image-and-constants)
            :in-theory (e/d (assembly-read-compiler-inputs assembly-static-text-input-p
                            assembly-source-prefix-bound-for-text)
                            (assembly-checked-text-index assembly-accepted-text-index-agrees
                             assembly-static-text-supplies-image-and-constants
                             assembly-source-prefix-upper-bound assembly-system-for-target
                             assembly-entry-arity-p length))))))

(local (in-theory (disable assembly-read-compiler-inputs assembly-static-text-input-p
                           assembly-entry-arity-p assembly-source-prefix-bound-for-text)))

(defthm assembly-source-layout-inputs-establish-compiler-bound
  (implies (assembly-source-layout-input-p text)
           (assembly-bounded-compiler-text-p text))
  :hints (("Goal"
           :use (assembly-source-bound-implies-compiler-bound
                 assembly-layout-input-supplies-source-bound)
           :in-theory (disable assembly-bounded-compiler-text-p
                               assembly-source-bounded-compiler-text-p
                               assembly-layout-input-supplies-source-bound
                               assembly-source-layout-input-p assembly-source-bound-implies-compiler-bound))))

(defthm assembly-source-layout-inputs-pass-image-checks
  (implies (assembly-source-layout-input-p text)
           (assembly-image-program-p (assembly-compiler-input-items (assembly-read-compiler-inputs text))))
  :hints (("Goal"
           :use (assembly-bounded-compiler-text-passes-image-checks)
           :in-theory (disable assembly-source-layout-input-p assembly-bounded-compiler-text-p
                               assembly-image-program-p assembly-compiler-input-items)))
  :rule-classes nil)
