(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defconst *data-entry-variable* "BOYMOO-COMPILER::ENTRY-INPUT")

(defun data-entry-wrapper (entry target)
  (list entry (list *data-entry-variable*) (list target *data-entry-variable*)))

(defun data-definitions-without-first (entry definitions)
  (cond ((atom definitions) nil)
        ((equal entry (caar definitions)) (cdr definitions))
        (t (cons (car definitions)
                 (data-definitions-without-first entry (cdr definitions))))))

(local
 (defthm reverse-onto-of-cons
   (equal (boymoo-compiler::reverse-onto (cons x xs) tail)
          (boymoo-compiler::reverse-onto xs (cons x tail)))))

(local
 (defthm reverse-onto-appends
   (equal (boymoo-compiler::reverse-onto xs (append mid tail))
          (append (boymoo-compiler::reverse-onto xs mid) tail))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto xs mid)))))

(defthm data-removal-of-entry-definition
  (equal (boymoo-compiler::remove-entry-definition entry definitions prefix)
         (boymoo-compiler::reverse-onto prefix
                                        (data-definitions-without-first entry definitions)))
  :hints (("Goal" :induct (boymoo-compiler::remove-entry-definition entry definitions prefix)
                  :in-theory (disable (:definition boymoo-compiler::reverse-onto)))))

(defthmd data-entry-definitions-agreement
  (mv-let (target arity routine) (boymoo-compiler::gen-call-info entry context)
    (implies (or (not arity) (equal arity 1))
             (equal (boymoo-compiler::compile-entry-definitions entry definitions context)
                    (if (and (equal arity 1) (equal target entry) (not routine)) definitions
                      (cons (data-entry-wrapper entry target)
                            (data-definitions-without-first entry definitions))))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-call-info
                                      boymoo-compiler::remove-entry-definition))))

(defthm data-entry-wrapper-uses-slot-zero
  (let* ((definition (data-entry-wrapper entry target))
         (formals (boymoo-compiler::declaration-list (cadr definition)))
         (scope (boymoo-compiler::bind-formals formals 0 nil)))
    (and (equal (length formals) 1)
         (equal (boymoo-compiler::gen-slot (cadr (caddr definition)) scope) 0))))

(local
 (defthm subspan-address-is-natural
   (implies (proof-subspan-p address size lower upper) (natp address))
   :rule-classes :forward-chaining))

(defthmd data-entry-argument-environment
  (implies (and (proof-subspan-p frame 8 (proof-stack-base world) (proof-stack-top world))
                (proof-machine-value-p (proof-load-word frame (proof-world-machine world))
                                       input world objects packages))
           (proof-environment-p (list (cons variable 0)) (list (cons variable input))
                                frame world objects packages))
  :hints (("Goal" :in-theory (disable proof-machine-value-p proof-load-word proof-subspan-p
                                      proof-stack-base proof-stack-top proof-world-machine))))

(defthmd data-entry-argument-source-value
  (implies (and (symbolp variable) (posp fuel))
           (equal (boymoo-model::core-eval variable (list (cons variable input)) program fuel)
                  (boymoo-model::core-value input)))
  :hints (("Goal" :in-theory (enable boymoo-model::core-eval-step))))
