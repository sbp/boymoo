(in-package "BOYMOO")

(include-book "guards-termination")

(defthm cg-defs-are-cons-list
  (implies (defs-shape-p defs) (cons-list-p defs)))

(defthm cg-function-pairs-are-cons-list
  (implies (guard-function-arities-p fns) (cons-list-p fns)))

(defthm cg-world-is-proper
  (implies (guard-world-p w) (true-listp w)))

(defthm cg-world-counts-are-natural
  (implies (guard-world-p w) (guard-natural-list-p (car (cddddr w)))))

(local
 (defthm cg-optional-clauses-are-list
   (implies (guard-optional-clauses-p facts)
            (true-listp facts))))

(local
 (in-theory (disable guard-world-p trie-get name-entry put-entry
                     guard-name-record-p guard-sized-clause-p unit-fact)))

(verify-guards enable-fns)
(verify-guards add-facts)
(verify-guards ascending-p)

(verify-guards package-conditions
  :hints (("Goal" :in-theory (disable symbol-names ascending-p lower-case-in-p))))

(verify-guards package-rule-name
  :hints (("Goal"
           :use ((:instance cg-import-in-package
                            (pkgs (w-pkgs w))
                            (pkg *acl2-chars*)
                            (name (app name (coerce "-PACKAGE" 'list)))))
           :in-theory (disable intern-sym app))))

(defthm cg-package-rule-name-is-symbol
  (implies (guard-world-p w)
           (symbolp (package-rule-name name w)))
  :hints (("Goal"
           :use ((:instance cg-import-in-package
                            (pkgs (w-pkgs w))
                            (pkg *acl2-chars*)
                            (name (app name (coerce "-PACKAGE" 'list)))))
           :in-theory (disable intern-sym app))))

(verify-guards admit-package
  :hints (("Goal" :in-theory (disable package-rule-name package-conditions
                                     declare-package new-name-p))))
(verify-guards admit-hidden-package
  :hints (("Goal" :in-theory (disable package-conditions declare-package))))

(verify-guards def-names)
(verify-guards arities-of)
(verify-guards defs-terms-p
  :hints (("Goal" :in-theory (disable variable-list-p term-p))))

(verify-guards add-definitions
  :hints (("Goal" :in-theory (disable def-names def-arities equations enable-fns
                                     guard-definition-list-p))))
(verify-guards add-constraint
  :hints (("Goal" :in-theory (disable formula-names formula-terms unit-facts
                                     enable-fns))))

(verify-guards admit-define
  :hints (("Goal" :in-theory (disable def-names def-arities def-bodies
                                     guard-definition-list-p defs-terms-p
                                     put-entries add-definitions calls-list-p
                                     fn-names-p distinct-p))))
(verify-guards admit-constrain
  :hints (("Goal" :in-theory (disable constrain-arities def-names formula-names
                                     formula-terms fn-names-p names-p terms-p
                                     distinct-p put-entries add-constraint))))

(local
 (defthm cg-variables-form-list
   (implies (variable-list-p xs w) (true-listp xs))))

(verify-guards admit-choose
  :hints (("Goal" :in-theory (disable variable-list-p term-p choice-axiom
                                     new-name-p))))
(verify-guards admit-theorem
  :hints (("Goal" :in-theory (e/d (guard-name-record-p) (term-p new-name-p)))))
(verify-guards admit-axiom
  :hints (("Goal" :in-theory (e/d (guard-name-record-p) (term-p new-name-p)))))

(verify-guards first-name)

(verify-guards repeat-p
  :hints (("Goal" :in-theory (disable first-name))))

(verify-guards admit
  :hints (("Goal" :in-theory (disable repeat-p admit-package admit-hidden-package
                                     admit-define admit-constrain admit-choose
                                     admit-theorem admit-axiom admit-reserve))))
