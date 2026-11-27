(in-package "BOYMOO-PROOFS")

(include-book "generator-size")
(include-book "bounded-entry")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-source-definitions-weight (definitions)
  (if (atom definitions)
      0
    (+ 1 (assembly-source-tree-weight (caddar definitions))
       (assembly-source-definitions-weight (cdr definitions)))))

(local (in-theory (disable boymoo-compiler::gen-term boymoo-compiler::gen-prologue
                           boymoo-compiler::bind-formals boymoo-compiler::declaration-list
                           assembly-source-tree-weight length mv-nth
                           boymoo-compiler::reverse-onto revappend)))

(local
 (defthm assembly-size-of-generator-label
   (equal (assembly-size (cons (list :label name) code))
          (assembly-size code))))

(local (in-theory (disable assembly-size)))

(local
 (defthm assembly-prologue-preserves-image-free-code
   (equal (assembly-no-image-items-p (boymoo-compiler::gen-prologue arity high serial code))
          (assembly-no-image-items-p code))
   :hints (("Goal" :use (assembly-projections-of-gen-prologue)))))

(local
 (defthm assembly-generator-body-no-images-and-size
   (let ((body (mv-nth 0 (assembly-definition-body definition context serial))))
     (and (assembly-no-image-items-p body)
          (<= (assembly-size body)
              (* 128 (assembly-source-tree-weight (caddr definition))))))
   :hints (("Goal"
            :use ((:instance assembly-generation-size-from-source-tree
                             (term (caddr definition))
                             (scope (boymoo-compiler::bind-formals
                                     (boymoo-compiler::declaration-list (cadr definition)) 0 nil))
                             (depth (length (boymoo-compiler::declaration-list (cadr definition))))
                             (tail t) (code nil)
                             (high (length (boymoo-compiler::declaration-list (cadr definition))))
                             (serial (+ 2 serial))))))))

(defthm assembly-generation-size-from-definitions
  (let ((out (boymoo-compiler::gen-functions defs entry context serial code)))
    (implies (assembly-no-image-items-p code)
             (and (assembly-no-image-items-p out)
                  (<= (assembly-size out)
                      (+ (assembly-size code) (* 128 (assembly-source-definitions-weight defs)))))))
  :hints (("Goal" :induct (boymoo-compiler::gen-functions defs entry context serial code))
          ("Subgoal *1/2"
           :use ((:instance assembly-generator-body-no-images-and-size (definition (car defs)))
                 (:instance assembly-generator-prologue-size
                            (arity (length (boymoo-compiler::declaration-list (cadar defs))))
                            (high (mv-nth 1 (assembly-definition-body (car defs) context serial)))
                            (code (cons (list :label (list :fn (caar defs)))
                                        (if (equal (caar defs) entry)
                                            (cons '(:label "rt:entry") code)
                                          code)))))
           :in-theory (disable assembly-generator-body-no-images-and-size)))
  :rule-classes nil)

(defun assembly-source-prefix-upper-bound (defs system)
  (+ (assembly-size (assembly-system-items system))
     (* 128 (assembly-source-definitions-weight defs))))

(local (in-theory (disable boymoo-compiler::gen-functions boymoo-compiler::runtime-code
                           (:executable-counterpart boymoo-compiler::runtime-code))))

(local
 (defthm assembly-size-of-system-and-runtime
   (and (equal (assembly-size (assembly-initial-code system))
               (assembly-size (assembly-system-items system)))
        (equal (assembly-no-image-items-p (assembly-initial-code system))
               (assembly-no-image-items-p (assembly-system-items system))))))

(defthm assembly-compile-prefix-size-from-definitions
  (implies (assembly-system-layout-p system)
           (<= (assembly-size (assembly-compile-prefix entry defs context system))
               (assembly-source-prefix-upper-bound defs system)))
  :hints (("Goal"
           :use ((:instance assembly-generation-size-from-definitions
                            (serial 0) (code (assembly-initial-code system))))
           :in-theory (disable assembly-initial-code assembly-system-items)))
  :rule-classes nil)

(defun assembly-source-prefix-bound-for-text (text)
  (mv-let (defs names attachments sources packages entry target)
    (boymoo-compiler::index-lines (boymoo-compiler::read-program text)
                                  nil nil nil nil nil nil nil)
    (declare (ignore packages))
    (let ((resolved (boymoo-compiler::resolve-attachments sources attachments nil
                                                          (length sources))))
      (assembly-source-prefix-upper-bound
       (boymoo-compiler::compile-entry-definitions entry defs (list names resolved nil))
       (assembly-system-for-target target)))))

(local
 (defthm assembly-entry-definitions-independent-of-constants
   (implies (syntaxp (not (equal constants ''nil)))
            (equal (boymoo-compiler::compile-entry-definitions entry defs (list names resolved constants))
                   (boymoo-compiler::compile-entry-definitions entry defs (list names resolved nil))))
   :hints (("Goal" :in-theory (disable boymoo-compiler::remove-entry-definition
                                       boymoo-compiler::index-get assoc-equal)))))

(local
 (defthm assembly-source-bound-target-layout
   (assembly-system-layout-p (assembly-system-for-target target))
   :hints (("Goal" :use (assembly-system-and-runtime-layout)
                   :in-theory (disable assembly-system-layout-p
                                       boymoo-compiler::linux-system-code boymoo-compiler::system-code
                                       (:executable-counterpart boymoo-compiler::linux-system-code)
                                       (:executable-counterpart boymoo-compiler::system-code))))))

(local (in-theory (disable boymoo-compiler::index-lines boymoo-compiler::read-program
                           boymoo-compiler::resolve-attachments boymoo-compiler::data-build
                           boymoo-compiler::compile-entry-definitions assembly-compile-prefix
                           assembly-system-layout-p assembly-source-prefix-upper-bound
                           assembly-system-for-target assembly-size)))

(defthm assembly-compiler-text-prefix-size-from-source
  (let* ((inputs (assembly-read-compiler-inputs text))
         (prefix (assembly-compile-prefix (car inputs) (cadr inputs) (caddr inputs)
                                          (assembly-system-for-target (nth 4 inputs)))))
    (implies inputs
             (<= (assembly-size prefix) (assembly-source-prefix-bound-for-text text))))
  :hints (("Goal"
           :use ((:instance assembly-compile-prefix-size-from-definitions
                            (entry (car (assembly-read-compiler-inputs text)))
                            (defs (cadr (assembly-read-compiler-inputs text)))
                            (context (caddr (assembly-read-compiler-inputs text)))
                            (system (assembly-system-for-target
                                     (nth 4 (assembly-read-compiler-inputs text))))))
           :do-not-induct t))
  :rule-classes nil)

(defun assembly-source-bounded-compiler-text-p (text)
  (let* ((inputs (assembly-read-compiler-inputs text))
         (entry (car inputs))
         (context (caddr inputs)))
    (and inputs
         (assembly-entry-arity-p entry context)
         (assembly-constant-index-p (caddr context) 12)
         (proof-image-p (cadddr inputs))
         (< (assembly-source-prefix-bound-for-text text) (expt 2 20)))))

(defthm assembly-source-bound-implies-compiler-bound
  (implies (assembly-source-bounded-compiler-text-p text)
           (assembly-bounded-compiler-text-p text))
  :hints (("Goal" :use (assembly-compiler-text-prefix-size-from-source)
                  :in-theory (disable assembly-read-compiler-inputs
                                      assembly-source-prefix-bound-for-text
                                      assembly-entry-arity-p assembly-constant-index-p proof-image-p))))
