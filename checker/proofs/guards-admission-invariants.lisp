(in-package "BOYMOO")

(include-book "guards-reader-stack")

(local
 (defthm cg-natural-list-fields
   (implies (guard-natural-list-p xs)
            (and (or (not (car xs)) (natp (car xs)))
                 (guard-natural-list-p (cdr xs))))
   :hints (("Goal" :expand ((guard-natural-list-p xs))))))

(defthm cg-optional-clauses-fields
  (implies (guard-optional-clauses-p xs)
           (and (or (not (car xs)) (guard-sized-clause-p (car xs)))
                (guard-optional-clauses-p (cdr xs))))
  :hints (("Goal" :expand ((guard-optional-clauses-p xs)))))

(local
 (defthm cg-name-entry-record
   (implies (guard-world-p w)
            (guard-trie-value-p (name-entry name w) :name))
   :hints (("Goal" :in-theory (disable trie-get sym-text guard-trie-value-p)))))

(local
 (defthm cg-name-entry-fields
   (implies (guard-world-p w)
            (let ((entry (name-entry name w)))
              (and (or (not (entry-arity entry)) (natp (entry-arity entry)))
                   (or (not (entry-fact entry))
                       (guard-sized-clause-p (entry-fact entry)))
                   (true-listp (entry-line entry)))))
   :hints (("Goal" :use cg-name-entry-record
            :expand ((guard-trie-value-p (name-entry name w) :name))
            :in-theory (disable name-entry guard-world-p cg-name-entry-record)))))

(local
 (in-theory (disable guard-world-p guard-sized-clause-p put-entry name-entry)))

(defthm cg-record-with-arity
  (implies (and (guard-world-p w) (natp arity))
           (let ((entry (name-entry name w)))
             (guard-name-record-p (list arity (entry-fact entry) (entry-line entry)))))
  :hints (("Goal" :use cg-name-entry-fields
           :in-theory (disable cg-name-entry-fields))))

(defthm cg-record-with-fact
  (implies (and (guard-world-p w)
                (or (not fact) (guard-sized-clause-p fact)))
           (let ((entry (name-entry name w)))
             (guard-name-record-p (list (entry-arity entry) fact (entry-line entry)))))
  :hints (("Goal" :use cg-name-entry-fields
           :in-theory (disable cg-name-entry-fields))))

(defthm cg-put-entries-keeps-world
  (implies (and (guard-world-p w)
                (guard-natural-list-p arities)
                (guard-optional-clauses-p facts)
                (true-listp line))
           (guard-world-p (put-entries names arities facts line w)))
  :hints (("Goal" :induct (put-entries names arities facts line w))))

(defthm cg-enable-fns-keeps-world
  (implies (and (guard-world-p w) (guard-function-arities-p fns))
           (guard-world-p (enable-fns fns w)))
  :hints (("Goal" :induct (enable-fns fns w)
           :in-theory (disable guard-name-record-p))))

(defthm cg-add-facts-keeps-world
  (implies (and (guard-world-p w) (guard-optional-clauses-p facts))
           (guard-world-p (add-facts names facts w)))
  :hints (("Goal" :induct (add-facts names facts w)
           :in-theory (disable guard-name-record-p))))

(defthm cg-def-arities-have-shape
  (implies (symbol-listp (def-names defs))
           (guard-function-arities-p (def-arities defs)))
  :hints (("Goal" :induct (def-arities defs))))

(defthm cg-equations-have-sizes
  (guard-optional-clauses-p (equations defs))
  :hints (("Goal" :induct (equations defs) :in-theory (disable unit-fact))))

(defthm cg-unit-facts-have-sizes
  (guard-optional-clauses-p (unit-facts terms))
  :hints (("Goal" :induct (unit-facts terms) :in-theory (disable unit-fact))))

(defthm cg-add-definitions-keeps-world
  (implies (and (guard-world-p w) (symbol-listp (def-names defs)))
           (guard-world-p (add-definitions defs w)))
  :hints (("Goal" :in-theory (disable enable-fns add-facts def-arities equations))))

(defthm cg-add-constraint-keeps-world
  (implies (and (guard-world-p w) (guard-function-arities-p fns))
           (guard-world-p (add-constraint fns formulas w)))
  :hints (("Goal" :in-theory (disable enable-fns add-facts unit-facts))))

(defthm cg-constrain-arities-have-shape
  (implies (constrain-fns-p fns)
           (guard-function-arities-p (constrain-arities fns)))
  :hints (("Goal" :induct (constrain-arities fns))))

(defthm cg-def-names-is-list
  (true-listp (def-names defs)))

(defthm cg-fn-names-are-symbols
  (implies (and (true-listp names) (fn-names-p names book w))
           (symbol-listp names))
  :hints (("Goal" :induct (fn-names-p names book w))))

(defthm cg-formula-names-is-list
  (true-listp (formula-names formulas)))

(defthm cg-names-are-symbols
  (implies (and (true-listp names) (names-p names w))
           (symbol-listp names))
  :hints (("Goal" :induct (names-p names w))))

(defthm cg-package-conditions-require-symbols
  (implies (package-conditions name imports)
           (symbol-listp imports)))

(defthm cg-world-has-package-trie
  (implies (guard-world-p w)
           (guard-trie-p (w-pkgs w) :package))
  :hints (("Goal" :in-theory (enable guard-world-p))))

(local
 (defthm cg-package-lookup-has-lines
   (implies (guard-world-p w)
            (true-listp (prec-lines (trie-get key (w-pkgs w)))))
   :hints (("Goal"
            :use ((:instance cg-trie-get-keeps-value
                             (node (w-pkgs w)) (kind :package)))
            :expand ((guard-trie-value-p (trie-get key (w-pkgs w)) :package))
            :in-theory (disable trie-get cg-trie-get-keeps-value)))))

(local
 (in-theory (disable package-conditions declare-package package-rule-name
                     count-one add-definitions add-constraint put-entries
                     unit-fact new-name-p new-fn-name-p term-p terms-p
                     trie-get def-names def-arities formula-names formula-terms
                     variable-list-p distinct-p disjoint-p choice-axiom
                     fn-names-p names-p calls-list-p cg-reader-stack-is-list)))

(local
 (defthm cg-admit-package-keeps-world
   (implies (and (guard-world-p w)
                 (not (stringp (admit-package data line w))))
            (guard-world-p (car (admit-package data line w))))))

(local
 (defthm cg-admit-hidden-package-keeps-world
   (implies (and (guard-world-p w)
                 (not (stringp (admit-hidden-package data line w))))
            (guard-world-p (car (admit-hidden-package data line w))))))

(local
 (defthm cg-admit-define-keeps-world
   (implies (and (guard-world-p w) (true-listp line)
                 (not (stringp (admit-define data line book w))))
            (guard-world-p (car (admit-define data line book w))))))

(local
 (defthm cg-admit-constrain-keeps-world
   (implies (and (guard-world-p w) (true-listp line)
                 (not (stringp (admit-constrain data line book w))))
            (guard-world-p (car (admit-constrain data line book w))))))

(local
 (defthm cg-admit-choose-keeps-world
   (implies (and (guard-world-p w) (true-listp line)
                 (not (stringp (admit-choose data line book w))))
            (guard-world-p (car (admit-choose data line book w))))))

(local
 (defthm cg-admit-theorem-keeps-world
   (implies (and (guard-world-p w) (true-listp line)
                 (not (stringp (admit-theorem data line w))))
            (guard-world-p (car (admit-theorem data line w))))))

(local
 (defthm cg-admit-axiom-keeps-world
   (implies (and (guard-world-p w) (true-listp line)
                 (not (stringp (admit-axiom data line library w))))
            (guard-world-p (car (admit-axiom data line library w))))))

(local
 (defthm cg-admit-reserve-keeps-world
   (implies (and (guard-world-p w) (true-listp line)
                 (not (stringp (admit-reserve data line w))))
            (guard-world-p (car (admit-reserve data line w))))))

(defthm cg-prepare-statement-keeps-world
  (implies (and (guard-world-p w) (true-listp line)
                (not (stringp (prepare-statement line input w))))
           (guard-world-p (car (prepare-statement line input w))))
  :hints (("Goal"
           :in-theory (disable repeat-p admit-package admit-hidden-package
                               admit-define admit-constrain admit-choose
                               admit-theorem admit-axiom admit-reserve))))

(defthm cg-guard-definition-list-characterization
  (equal (guard-definition-list-p defs)
         (and (defs-shape-p defs) (symbol-listp (def-names defs))))
  :hints (("Goal" :induct (guard-definition-list-p defs)
           :in-theory (enable def-names))))

(defthm cg-new-name-is-symbol
  (implies (new-name-p name w)
           (symbolp name))
  :hints (("Goal" :in-theory (enable new-name-p))))

(local
 (defthm cg-admit-define-pending
   (implies (and (not (stringp (admit-define data line book w)))
                 (cdr (admit-define data line book w)))
            (guard-pending-p (cdr (admit-define data line book w))))
   :hints (("Goal" :in-theory (disable defs-terms-p)))))

(local
 (defthm cg-admit-constrain-pending
   (implies (and (not (stringp (admit-constrain data line book w)))
                 (cdr (admit-constrain data line book w)))
            (guard-pending-p (cdr (admit-constrain data line book w))))
   :hints (("Goal" :in-theory (disable constrain-arities)))))

(local
 (defthm cg-admit-theorem-pending
   (implies (and (not (stringp (admit-theorem data line w)))
                 (cdr (admit-theorem data line w)))
            (guard-pending-p (cdr (admit-theorem data line w))))))

(defthm cg-prepared-pending
  (implies (and (not (stringp (prepare-statement line input w)))
                (cdr (prepare-statement line input w)))
           (guard-pending-p (cdr (prepare-statement line input w))))
  :hints (("Goal" :in-theory (disable admit-define admit-constrain admit-theorem
                                     repeat-p guard-pending-p))))
