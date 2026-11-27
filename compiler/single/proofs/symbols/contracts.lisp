(in-package "BOYMOO-PROOFS")

(include-book "routines")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                     (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-heap-base proof-view proof-value-p
                     boymoo-model::a64-unsigned symbols-runtime-offset)))

(defun symbols-query-field (primitive)
  (if (eq primitive 'acl2::pkg-imports) 16 24))

(defun symbols-query-row-value (primitive row)
  (if (eq primitive 'acl2::pkg-imports)
      (proof-package-imports row)
    (proof-package-witness row)))

; The package table agreement supplies the value represented by a row
; field. The result word can be interpreted in the continuation's
; memory because the return path preserves that memory.
(defthm symbols-visible-query-return-implements-core
  (let* ((row (assoc-equal datum packages))
         (offset (symbols-query-field primitive))
         (field (symbols-load-register-word (+ (proof-world-reg 0 before) offset) before))
         (result (boymoo-model::core-primitive primitive (list datum) program)))
    (implies (and (member-eq primitive '(acl2::pkg-imports acl2::pkg-witness))
                  (stringp datum)
                  (proof-program-packages-p program packages)
                  (proof-package-visible row)
                  (symbols-query-visible-row-p before)
                  (equal (symbols-stack-word 8 before) offset)
                  (proof-machine-value-p field (symbols-query-row-value primitive row)
                                         before objects packages)
                  (equal (proof-world-reg 0 after) (symbols-query-string-result-word before))
                  (symbols-no-memory-or-kernel-change-p before after))
             (and (boymoo-model::core-value-p result)
                  (proof-machine-value-p (proof-world-reg 0 after)
                                         (boymoo-model::core-datum result)
                                         before objects packages))))
  :hints (("Goal"
           :use ((:instance symbols-package-query-implements-core))
           :in-theory (disable symbols-package-query-implements-core
                               symbols-query-visible-row-p
                               symbols-load-register-word symbols-stack-word
                               symbols-no-memory-or-kernel-change-p
                               proof-machine-value-p proof-program-packages-p assoc-equal)))
  :rule-classes nil)

(defthm symbols-hidden-or-absent-query-implements-core
  (let* ((row (assoc-equal datum packages))
         (target (symbols-query-string-target code-base before)))
    (implies (and (member-eq primitive '(acl2::pkg-imports acl2::pkg-witness))
                  (stringp datum)
                  (proof-program-packages-p program packages)
                  (not (proof-package-visible row))
                  (not (symbols-query-visible-row-p before))
                  (equal (symbols-stack-word 8 before) (symbols-query-field primitive))
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 0 after) (symbols-query-string-result-word before)))
             (and (equal (boymoo-model::core-primitive primitive (list datum) program)
                         :no-value)
                  (equal (proof-world-reg 0 after) (symbols-stack-word 0 before))
                  (equal (proof-world-pc after)
                         (symbols-runtime-address
                          (if (eq primitive 'acl2::pkg-imports)
                              "rt:imports-absent" "rt:witness-absent")
                          code-base)))))
  :hints (("Goal"
           :use ((:instance symbols-package-query-implements-core))
           :in-theory (disable symbols-package-query-implements-core
                               symbols-query-visible-row-p symbols-stack-word
                               symbols-runtime-address proof-program-packages-p assoc-equal)))
  :rule-classes nil)

(defthm symbols-symbol-name-return-implements-core
  (let* ((word (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (machine (proof-world-machine before))
         (result (boymoo-model::core-primitive 'symbol-name (list datum) program)))
    (implies (and (symbolp datum)
                  (proof-value-p word datum base objects packages machine)
                  (equal (proof-world-reg 1 before) (proof-pointer-address word base))
                  (not (equal (proof-world-reg 1 before) 0))
                  (symbols-name-continuation-frame-p code-base before after))
             (proof-machine-value-p (proof-world-reg 0 after)
                                    (boymoo-model::core-datum result)
                                    before objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-published-symbol-fields
                            (word (proof-world-reg 0 before)) (symbol datum)
                            (base (proof-heap-base before))
                            (machine (proof-world-machine before))))
           :in-theory (e/d (boymoo-model::core-primitive symbols-word-load-fits)
                           (symbols-name-continuation-target
                            symbols-no-memory-or-kernel-change-p proof-value-p proof-view
                            proof-pointer-address boymoo-model::a64-load))))
  :rule-classes nil)
