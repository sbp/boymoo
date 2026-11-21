(in-package "BOYMOO")

(include-book "guards-run-invariants")

(local
 (in-theory (disable guard-world-p trie-get name-entry put-entry count-one
                     declare-package guard-sized-clause-p size)))

(verify-guards ground-line
  :hints (("Goal" :in-theory (disable package-rule-name
                                     symbol-names import-trie set-acl2 set-sfacts
                                     set-specials specials-trie))))

(verify-guards load-ground
  :hints (("Goal" :in-theory (disable parse-line ground-line guard-ground-line-p))))

(defthm cg-ground-loader-keeps-world
  (implies (and (guard-world-p w) (not (equal (load-ground lines w) :bad)))
           (guard-world-p (load-ground lines w)))
  :hints (("Goal" :induct (load-ground lines w)
           :in-theory (disable parse-line ground-line guard-ground-line-p))))

(local
 (defthm cg-function-pairs-are-list
   (implies (guard-function-arities-p fns) (true-listp fns))))

(local
 (defthm cg-function-pairs-head
   (implies (and (guard-function-arities-p fns) (not (consp (car fns))))
            (equal (car fns) nil))
   :hints (("Goal" :expand ((guard-function-arities-p fns))))))

(verify-guards finish
  :hints (("Goal" :in-theory (disable add-facts add-definitions add-constraint
                                     formula-names formula-terms unit-fact
                                     guard-definition-list-p))))

(local
 (defthm cg-measures-are-list
   (implies (measures-p measures defs w) (true-listp measures))
   :hints (("Goal" :induct (measures-p measures defs w)
            :in-theory (disable term-p defs-shape-p)))))

(verify-guards measure-entry
  :hints (("Goal" :in-theory (disable measures-p termination-obligations
                                     pending-name def-arities enable-fns
                                     guard-definition-list-p))))

(verify-guards witness-entry
  :hints (("Goal" :in-theory (disable pending-name witnesses-p witness-obligations
                                     formula-terms formula-names def-names))))

(verify-guards pending-entry
  :hints (("Goal" :in-theory (disable finish measure-entry witness-entry
                                     pending-name guard-definition-list-p))))

(verify-guards lemma-head
  :hints (("Goal" :in-theory (disable term-p terms-p new-name-p))))

(verify-guards entry-head
  :hints (("Goal" :in-theory (disable admit pending-entry lemma-head))))

(local
 (defthm cg-proof-context-spine
   (implies (guard-proof-context-p ctx)
            (true-listp ctx))
   :rule-classes :forward-chaining))

(verify-guards proof-step
  :hints (("Goal" :in-theory (disable check-step sum finish start-proofs member-p))))

(verify-guards proof-line
  :hints (("Goal" :expand ((guard-proof-context-p ctx))
           :in-theory (disable proof-step entry-head pending-entry))))

(local
 (defthm cg-entry-context-shape
   (implies (guard-pending-p p)
            (guard-proof-context-p (list :entry p)))))

(verify-guards run
  :hints (("Goal" :in-theory (disable admit parse-line proof-line
                                     guard-proof-context-p))))

(verify-guards check-library
  :hints (("Goal" :in-theory (disable admit parse-line))))

(local
 (defthm cg-world-is-not-rejection
   (implies (guard-world-p w)
            (not (rejected-p w)))
   :hints (("Goal" :expand ((guard-world-p w))
            :cases ((equal (car w) :rejected))))))

(local
 (defthm cg-rejection-record
   (implies (stringp input)
            (let ((r (rejection input n reason)))
              (and (rejected-p r)
                   (true-listp r)
                   (stringp (cadr r)))))))

(local
 (defthm cg-library-rejection-record
   (implies (and (guard-world-p w) (rejected-p (check-library lines n w)))
            (let ((r (check-library lines n w)))
              (and (true-listp r)
                   (stringp (cadr r)))))
   :hints (("Goal" :induct (check-library lines n w)
            :in-theory (disable admit parse-line rejected-p rejection)))))

(local
 (defthm cg-run-rejection-record
   (implies (and (guard-world-p w) (guard-proof-context-p ctx)
                 (rejected-p (run slines sn plines pn ctx w)))
            (let ((r (run slines sn plines pn ctx w)))
              (and (true-listp r)
                   (stringp (cadr r)))))
   :hints (("Goal" :induct (run slines sn plines pn ctx w)
            :expand ((run slines sn plines pn ctx w)
                     (run slines sn plines pn nil w))
            :in-theory (disable (:definition run) admit parse-line proof-line
                                guard-proof-context-p rejected-p rejection)))))

(local
 (defthm cg-world-counts-are-list
   (implies (guard-world-p w) (true-listp (w-counts w)))))

(local (in-theory (disable (:executable-counterpart initial-world))))

(verify-guards check
  :hints (("Goal" :in-theory (disable load-ground lines-of initial-world check-library
                                     run rejected-p rejection-verdict verdict))))
