(in-package "BOYMOO")

(include-book "guards-admission")

(local
 (in-theory (disable guard-world-p guard-sized-clause-p guard-definition-list-p
                     add-facts add-definitions add-constraint enable-fns
                     count-one put-entry unit-fact new-name-p def-arities
                     terms-p term-p witness-obligations witnesses-p measures-p
                     termination-obligations pending-name cg-reader-stack-is-list)))

(defthm cg-finish-keeps-world
  (implies (and (guard-world-p w) (guard-pending-p p))
           (guard-world-p (finish p w))))

(local
 (defthm cg-start-proofs-keeps-state
   (implies (and (guard-world-p w)
                 (guard-pending-p p)
                 (true-listp goals)
                 (guard-proof-context-p back))
            (let ((r (start-proofs goals p back w)))
              (and (guard-proof-context-p (car r))
                   (guard-world-p (cdr r)))))))

(local
 (in-theory (disable finish start-proofs)))

(local
 (defthm cg-measure-entry-keeps-state
   (implies (and (guard-world-p w)
                 (guard-pending-p p)
                 (equal (car p) :define)
                 (guard-proof-context-p back)
                 (not (stringp (measure-entry data p back w))))
            (let ((r (measure-entry data p back w)))
              (and (guard-proof-context-p (car r))
                   (guard-world-p (cdr r)))))))

(local
 (defthm cg-witness-entry-keeps-state
   (implies (and (guard-world-p w)
                 (guard-pending-p p)
                 (guard-proof-context-p back)
                 (not (stringp (witness-entry data p back w))))
            (let ((r (witness-entry data p back w)))
              (and (guard-proof-context-p (car r))
                   (guard-world-p (cdr r)))))))

(local
 (in-theory (disable measure-entry witness-entry guard-pending-p)))

(local
 (defthm cg-pending-entry-keeps-state
   (implies (and (guard-world-p w)
                 (guard-pending-p p)
                 (guard-proof-context-p back)
                 (not (stringp (pending-entry line p back w))))
            (let ((r (pending-entry line p back w)))
              (and (guard-proof-context-p (car r))
                   (guard-world-p (cdr r)))))))

(local
 (defthm cg-lemma-head-keeps-state
   (implies (and (guard-world-p w)
                 (guard-pending-p p)
                 (true-listp data)
                 (not (stringp (lemma-head data p w))))
            (let ((r (lemma-head data p w)))
              (and (guard-proof-context-p (car r))
                   (guard-world-p (cdr r)))))
   :hints (("Goal" :in-theory (enable guard-pending-p)))))

(local
 (defthm cg-entry-head-keeps-state
   (implies (and (guard-world-p w)
                 (guard-pending-p p)
                 (true-listp line)
                 (not (stringp (entry-head line p w))))
            (let ((r (entry-head line p w)))
              (and (guard-proof-context-p (car r))
                   (guard-world-p (cdr r)))))
   :hints (("Goal" :in-theory (disable admit lemma-head pending-entry)))))

(local
 (defthm cg-check-step-total-size
   (implies (and (proof-clauses-p steps) (guard-world-p w))
            (integerp (sum (cdr (check-step word data steps count room w)))))
   :hints (("Goal" :use ((:instance cg-size-list-sum
                                   (xs (cdr (check-step word data steps count room w)))))
            :in-theory (disable check-step cg-size-list-sum sum)))
   :rule-classes :type-prescription))

(local
 (defthm cg-proof-step-keeps-state
   (implies (and (guard-world-p w)
                 (guard-proof-context-p ctx)
                 (equal (car ctx) :proof)
                 (not (stringp (proof-step line ctx w))))
            (let ((r (proof-step line ctx w)))
              (and (guard-proof-context-p (car r))
                   (guard-world-p (cdr r)))))
   :hints (("Goal" :in-theory (disable check-step sum member-p)))))

(defthm cg-proof-line-keeps-state
  (implies (and (guard-world-p w)
                (guard-proof-context-p ctx)
                (consp ctx)
                (true-listp line)
                (not (stringp (proof-line line ctx w))))
           (let ((r (proof-line line ctx w)))
             (and (guard-proof-context-p (car r))
                  (guard-world-p (cdr r)))))
  :hints (("Goal" :expand ((guard-proof-context-p ctx))
           :in-theory (disable proof-step entry-head pending-entry))))

(local
 (defthm cg-context-is-cons
   (implies (and (guard-proof-context-p ctx) ctx)
            (consp ctx))
   :rule-classes :forward-chaining))

(local
 (defthm cg-empty-context
   (guard-proof-context-p nil)))

(local
 (defthm cg-entry-context
   (implies (guard-pending-p p)
            (guard-proof-context-p (list :entry p)))))

(local
 (defthm cg-rejection-is-rejected
   (rejected-p (rejection input n reason))))

(defthm cg-run-keeps-world
  (implies (and (guard-world-p w)
                (guard-proof-context-p ctx)
                (not (rejected-p (run slines sn plines pn ctx w))))
           (guard-world-p (run slines sn plines pn ctx w)))
  :hints (("Goal" :induct (run slines sn plines pn ctx w)
           :expand ((run slines sn plines pn ctx w)
                    (run slines sn plines pn nil w))
           :in-theory (disable (:definition run) admit parse-line proof-line
                               guard-proof-context-p rejected-p rejection))))
