(in-package "BOYMOO-PROOFS")

(include-book "definition-labels")
(include-book "generator-references")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-compiler::gen-prologue boymoo-compiler::gen-term
                           boymoo-compiler::bind-formals boymoo-compiler::declaration-list
                           boymoo-compiler::reverse-onto length mv-nth revappend
                           assembly-allowed-generated-reference-p)))

(defthm assembly-gen-functions-retain-labels
  (implies (member-equal key (assembly-label-names code))
           (member-equal key
                         (assembly-label-names
                          (boymoo-compiler::gen-functions defs entry context serial code))))
  :hints (("Goal" :induct (boymoo-compiler::gen-functions defs entry context serial code))))

(defthm assembly-gen-functions-reference-origin
  (let ((out (boymoo-compiler::gen-functions defs entry context serial code)))
    (implies (and (not (assembly-allowed-generated-reference-p key context))
                  (not (equal key "rt:grow")) (not (equal key "rt:deep"))
                  (member-equal key (assembly-references out))
                  (not (member-equal key (assembly-label-names out))))
             (and (member-equal key (assembly-references code))
                  (not (member-equal key (assembly-label-names code))))))
  :hints (("Goal" :induct (boymoo-compiler::gen-functions defs entry context serial code))
           ("Subgoal *1/2"
            :use ((:instance assembly-gen-term-reference-origin
                             (term (caddar defs)) (code nil) (tail t)
                             (scope (boymoo-compiler::bind-formals
                                     (boymoo-compiler::declaration-list (cadar defs)) 0 nil))
                             (depth (length (boymoo-compiler::declaration-list (cadar defs))))
                             (high (length (boymoo-compiler::declaration-list (cadar defs))))
                             (serial (+ 2 serial))))))
  :rule-classes nil)
