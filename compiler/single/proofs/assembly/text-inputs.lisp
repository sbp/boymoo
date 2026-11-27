(in-package "BOYMOO-PROOFS")

(include-book "compiler-layout")
(include-book "index-uniqueness")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-read-compiler-inputs (text)
  (let ((lines (boymoo-compiler::read-program text)))
    (mv-let (defs names attachments sources packages entry target)
      (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)
      (and entry
           (let ((resolved (boymoo-compiler::resolve-attachments sources attachments nil (length sources))))
             (mv-let (data constants)
               (boymoo-compiler::data-build lines packages)
               (let ((context (list names resolved constants)))
                 (list entry (boymoo-compiler::compile-entry-definitions entry defs context)
                       context data target))))))))

(defun assembly-entry-arity-p (entry context)
  (mv-let (target arity routine)
    (boymoo-compiler::gen-call-info entry context)
    (declare (ignore target routine))
    (or (not arity) (equal arity 1))))

(local (in-theory (disable boymoo-compiler::index-get boymoo-compiler::gen-call-info
                           boymoo-compiler::reverse-onto assembly-arity-tree-covered-p
                           assembly-arity-index-covered-p)))

(local
 (defthm assembly-member-of-subset
   (implies (and (subsetp-equal names more) (member-equal key names))
            (member-equal key more))
   :rule-classes nil))

(local
 (defthm assembly-arity-cover-tree-subset
   (implies (and (assembly-arity-tree-covered-p tree names) (subsetp-equal names more))
            (assembly-arity-tree-covered-p tree more))
   :hints (("Goal"
            :induct (assembly-arity-tree-covered-p tree names)
            :in-theory (enable assembly-arity-tree-covered-p))
           ("Subgoal *1/2" :use ((:instance assembly-member-of-subset (key (cadar tree))))))))

(local
 (defthm assembly-arity-cover-index-subset
   (implies (and (assembly-arity-index-covered-p index bits names) (subsetp-equal names more))
            (assembly-arity-index-covered-p index bits more))
   :hints (("Goal" :induct (assembly-arity-index-covered-p index bits names)
                   :in-theory (enable assembly-arity-index-covered-p)))
   :rule-classes nil))

(local
 (defthm assembly-definition-names-of-revappend
   (equal (strip-cars (revappend defs rest))
          (revappend (strip-cars defs) (strip-cars rest)))
   :hints (("Goal" :induct (revappend defs rest)))))

(local
 (defthm assembly-definition-names-after-removing-entry
   (equal (strip-cars (boymoo-compiler::remove-entry-definition entry defs prefix))
          (revappend (strip-cars prefix) (remove1-equal entry (strip-cars defs))))
   :hints (("Goal" :induct (boymoo-compiler::remove-entry-definition entry defs prefix)))))

(local
 (defthm assembly-remove-entry-definition-list-type
   (implies (true-listp defs)
            (true-listp (boymoo-compiler::remove-entry-definition entry defs prefix)))
   :hints (("Goal" :induct (boymoo-compiler::remove-entry-definition entry defs prefix)
                   :in-theory (enable boymoo-compiler::reverse-onto)))))

(local
 (defthm assembly-member-after-remove-one
   (implies (member-equal key (remove1-equal name names))
            (member-equal key names))))

(local
 (defthm assembly-remove-one-keeps-other-members
   (implies (not (equal key name))
            (iff (member-equal key (remove1-equal name names))
                 (member-equal key names)))))

(local
 (defthm assembly-remove-one-from-distinct-list
   (implies (no-duplicatesp-equal names)
            (and (no-duplicatesp-equal (remove1-equal name names))
                 (not (member-equal name (remove1-equal name names)))))))

(local
 (defthm assembly-remove-one-keeps-string-list
   (implies (string-listp names)
            (string-listp (remove1-equal name names)))))

(local
 (defthm assembly-member-if-replaced-or-retained
   (implies (member-equal key names)
            (member-equal key (cons name (remove1-equal name names))))))

(local
 (defthm assembly-subset-if-one-is-replaced
   (implies (subsetp-equal old names)
            (subsetp-equal old (cons name (remove1-equal name names))))
   :hints (("Goal" :induct (len old))
           ("Subgoal *1/2" :use ((:instance assembly-member-of-subset (key (car old))
                                            (names old) (more names)))))))

(local
 (defthm assembly-names-covered-after-entry-replacement
   (implies (assembly-arity-index-covered-p index bits names)
            (assembly-arity-index-covered-p index bits (cons entry (remove1-equal entry names))))
   :hints (("Goal"
            :use ((:instance assembly-arity-cover-index-subset
                             (more (cons entry (remove1-equal entry names)))))))))

(local
 (defthm assembly-entry-definitions-layout-inputs
   (let* ((names (strip-cars defs))
          (out (boymoo-compiler::compile-entry-definitions entry defs context))
          (out-names (strip-cars out)))
     (implies (and (assembly-entry-arity-p entry context)
                   (stringp entry) (true-listp defs)
                   (string-listp names) (no-duplicatesp-equal names)
                   (assembly-arity-index-covered-p (car context) 12 names))
              (and (true-listp out)
                   (string-listp out-names)
                   (no-duplicatesp-equal out-names)
                   (member-equal entry out-names)
                   (assembly-arity-index-covered-p (car context) 12 out-names))))
   :hints (("Goal"
            :use ((:instance assembly-gen-call-info-index-for-non-routine (head entry))
                  (:instance assembly-covered-arity-index-lookup
                             (key entry) (names (strip-cars defs)) (index (car context))))
            :in-theory (disable boymoo-compiler::remove-entry-definition)))
   :rule-classes nil))

(local
 (defthm assembly-index-lines-string-entry
   (let ((result (mv-nth 5 (boymoo-compiler::index-lines lines defs names attachments sources
                                                        packages entry target))))
     (implies (and (or (not entry) (stringp entry)) result)
              (stringp result)))
   :hints (("Goal"
            :induct (boymoo-compiler::index-lines lines defs names attachments sources packages entry target)
            :in-theory (disable boymoo-compiler::index-definitions revappend)))))

(local (in-theory (disable boymoo-compiler::index-lines boymoo-compiler::read-program
                           boymoo-compiler::resolve-attachments boymoo-compiler::data-build
                           boymoo-compiler::compile-entry-definitions)))

(local
 (defmacro assembly-index-text-lines (text)
   `(boymoo-compiler::index-lines (boymoo-compiler::read-program ,text)
                                  nil nil nil nil nil nil nil)))

(defthm assembly-read-compiler-inputs-definition-checks
  (let* ((inputs (assembly-read-compiler-inputs text))
         (entry (car inputs))
         (defs (cadr inputs))
         (context (caddr inputs))
         (names (strip-cars defs)))
    (implies (and inputs (assembly-entry-arity-p entry context))
             (and (stringp entry) (true-listp defs)
                  (string-listp names) (no-duplicatesp-equal names)
                  (member-equal entry names)
                  (assembly-arity-index-covered-p (car context) 12 names))))
  :hints (("Goal"
           :use ((:instance assembly-index-lines-cover-arity-lookups
                            (lines (boymoo-compiler::read-program text)) (defs nil)
                            (index nil) (attachments nil) (sources nil) (packages nil)
                            (entry nil) (target nil))
                 (:instance assembly-index-lines-returns-distinct-definition-names
                            (lines (boymoo-compiler::read-program text)))
                 (:instance assembly-index-lines-string-entry
                            (lines (boymoo-compiler::read-program text)) (defs nil)
                            (names nil) (attachments nil) (sources nil) (packages nil)
                            (entry nil) (target nil))
                 (:instance assembly-entry-definitions-layout-inputs
                            (entry (mv-nth 5 (assembly-index-text-lines text)))
                            (defs (mv-nth 0 (assembly-index-text-lines text)))
                            (context
                             (list (mv-nth 1 (assembly-index-text-lines text))
                                   (boymoo-compiler::resolve-attachments
                                    (mv-nth 3 (assembly-index-text-lines text))
                                    (mv-nth 2 (assembly-index-text-lines text)) nil
                                    (length (mv-nth 3 (assembly-index-text-lines text))))
                                   (mv-nth 1 (boymoo-compiler::data-build
                                              (boymoo-compiler::read-program text)
                                              (mv-nth 4 (assembly-index-text-lines text))))))))
           :in-theory (disable assembly-entry-arity-p assembly-index-lines-string-entry length)
           :do-not-induct t))
  :rule-classes nil)
