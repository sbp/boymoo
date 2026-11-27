(in-package "BOYMOO-PROOFS")

(include-book "arity-index")
(include-book "definition-references")
(include-book "generator-fields")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-system-items (system)
  (append system (boymoo-compiler::runtime-code)))

(defun assembly-system-layout-p (system)
  (let* ((items (assembly-system-items system))
         (keys (assembly-label-names items)))
    (and (assembly-fixed-item-list-p system)
         (assembly-no-image-items-p items)
         (string-listp keys)
         (no-duplicatesp-equal keys)
         (not (member-equal "rt:entry" keys))
         (not (member-equal "data:static" keys))
         (member-equal "os:main" keys)
         (member-equal "rt:deep" keys)
         (member-equal "rt:grow" keys)
         (member-equal "rt:undefined" keys)
         (subsetp-equal (assembly-routine-destinations boymoo-compiler::*jets*) keys)
         (subsetp-equal (assembly-routine-destinations boymoo-compiler::*primitives*) keys)
         (subsetp-equal (assembly-references items)
                        (list* "rt:entry" "data:static" keys)))))

(defthm assembly-system-and-runtime-layout
  (and (assembly-system-layout-p (boymoo-compiler::linux-system-code))
       (assembly-system-layout-p (boymoo-compiler::system-code)))
  :hints (("Goal" :in-theory (union-theories
                            (theory 'acl2::minimal-theory)
                            '((:executable-counterpart assembly-system-layout-p)
                              (:executable-counterpart boymoo-compiler::linux-system-code)
                              (:executable-counterpart boymoo-compiler::system-code)))))
  :rule-classes nil)

(defun assembly-initial-code (system)
  (boymoo-compiler::gen-emit (boymoo-compiler::runtime-code)
                             (boymoo-compiler::gen-emit system nil)))

(defun assembly-compile-prefix (entry defs context system)
  (revappend (boymoo-compiler::gen-functions defs entry context 0
                                               (assembly-initial-code system))
             '((:label "data:static"))))

(local (in-theory (disable boymoo-compiler::runtime-code
                           boymoo-compiler::linux-system-code
                           boymoo-compiler::system-code
                           (:executable-counterpart boymoo-compiler::runtime-code)
                           (:executable-counterpart boymoo-compiler::system-code)
                           (:executable-counterpart boymoo-compiler::linux-system-code)
                           boymoo-compiler::reverse-onto boymoo-compiler::gen-functions
                           revappend)))

(local
 (defthm assembly-revappend-of-append
   (equal (revappend (append first rest) suffix)
          (revappend rest (revappend first suffix)))
   :hints (("Goal" :induct (revappend first suffix)
                   :in-theory (enable revappend)))))

(local
 (defthm assembly-append-to-revappend
   (equal (append (revappend items code) suffix)
          (revappend items (append code suffix)))
   :hints (("Goal" :induct (revappend items code)
                   :in-theory (enable revappend)))))

(defthm assembly-compile-items-add-static-image
  (equal (boymoo-compiler::compile-items entry defs context data system)
         (append (assembly-compile-prefix entry defs context system)
                 (list (list :image (car data) (cdr data)))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-emit)))
  :rule-classes nil)

(local
 (defthm assembly-initial-code-is-reversed
   (equal (assembly-initial-code system) (revappend (assembly-system-items system) nil))))

(local
 (defthm assembly-member-subsetp
   (implies (and (subsetp-equal first rest) (member-equal key first))
            (member-equal key rest))
   :hints (("Goal" :induct (len first)))
   :rule-classes nil))

(defthm assembly-definition-label-membership
  (iff (member-equal key (assembly-definition-labels defs entry))
       (or (and (equal key "rt:entry") (member-equal entry (strip-cars defs)))
           (and (equal key (list :fn (cadr key))) (member-equal (cadr key) (strip-cars defs)))))
  :hints (("Goal" :induct (assembly-definition-labels defs entry))))

(local
 (defthm assembly-labels-belong-to-one-namespace
   (implies (string-listp keys)
            (and (equal (assembly-local-labels keys) nil)
                 (equal (assembly-global-labels keys) keys)
                 (assembly-labels-before-serial-p keys serial)))
   :hints (("Goal" :induct (len keys)))))

(local
 (defthm assembly-labels-before-serial-of-revappend
   (equal (assembly-labels-before-serial-p (revappend keys tail) serial)
          (and (assembly-labels-before-serial-p keys serial)
               (assembly-labels-before-serial-p tail serial)))
   :hints (("Goal" :induct (revappend keys tail) :in-theory (enable revappend)))))

(local
 (in-theory (disable assembly-initial-code assembly-system-items assembly-system-layout-p
                     assembly-local-labels assembly-global-labels
                     assembly-labels-before-serial-p assembly-definition-labels)))

(local
 (defthm assembly-initial-code-layout
   (implies (assembly-system-layout-p system)
            (let ((keys (assembly-label-names (assembly-initial-code system))))
              (and (assembly-labels-before-serial-p keys 0)
                   (equal (assembly-local-labels keys) nil)
                   (equal (assembly-global-labels keys)
                          (revappend (assembly-label-names (assembly-system-items system)) nil))
                   (assembly-no-image-items-p (assembly-initial-code system)))))
   :hints (("Goal" :in-theory (enable assembly-system-layout-p
                                     assembly-labels-before-serial-p)))))

(local
 (defun assembly-label-lists-disjoint-p (first rest)
   (if (atom first)
       t
     (and (not (member-equal (car first) rest))
          (assembly-label-lists-disjoint-p (cdr first) rest)))))

(local
 (defthm assembly-distinct-labels-of-append
   (implies (and (no-duplicatesp-equal first)
                 (no-duplicatesp-equal rest)
                 (assembly-label-lists-disjoint-p first rest))
            (no-duplicatesp-equal (append first rest)))
   :hints (("Goal" :induct (append first rest)))))

(local
 (defthm assembly-labels-disjoint-from-cons
   (equal (assembly-label-lists-disjoint-p first (cons key rest))
          (and (not (member-equal key first)) (assembly-label-lists-disjoint-p first rest)))
   :hints (("Goal" :induct (len first)))))

(local
 (defthm assembly-distinct-labels-of-revappend
   (equal (no-duplicatesp-equal (revappend first rest))
          (and (no-duplicatesp-equal first)
               (no-duplicatesp-equal rest)
               (assembly-label-lists-disjoint-p first rest)))
   :hints (("Goal" :induct (revappend first rest)
                   :in-theory (enable revappend)))))

(local
 (defthm assembly-labels-disjoint-from-nil
   (assembly-label-lists-disjoint-p first nil)
   :hints (("Goal" :induct (len first)))))

(defthm assembly-compile-prefix-local-layout
  (implies (assembly-system-layout-p system)
           (let ((prefix (assembly-compile-prefix entry defs context system)))
             (and (assembly-no-image-items-p prefix)
                  (no-duplicatesp-equal (assembly-local-labels (assembly-label-names prefix))))))
  :hints (("Goal"
           :use ((:instance assembly-gen-functions-local-layout (serial 0) (code (assembly-initial-code system))))
           :in-theory (disable assembly-initial-code-is-reversed)))
  :rule-classes nil)

(defthm assembly-compile-prefix-global-labels
  (implies (assembly-system-layout-p system)
           (equal (assembly-global-labels
                   (assembly-label-names (assembly-compile-prefix entry defs context system)))
                  (append (assembly-label-names (assembly-system-items system))
                          (assembly-definition-labels defs entry)
                          '("data:static"))))
  :hints (("Goal"
           :use ((:instance assembly-gen-functions-global-labels (serial 0) (code (assembly-initial-code system))))
           :in-theory (disable assembly-initial-code-is-reversed)))
  :rule-classes nil)

(local
 (defthm assembly-definition-labels-are-distinct
   (implies (no-duplicatesp-equal (strip-cars defs))
            (no-duplicatesp-equal (assembly-definition-labels defs entry)))
   :hints (("Goal" :induct (assembly-definition-labels defs entry)
                   :in-theory (enable assembly-definition-labels)))))

(local
 (defthm assembly-definitions-disjoint-from-static-label
   (assembly-label-lists-disjoint-p (assembly-definition-labels defs entry) '("data:static"))
   :hints (("Goal" :induct (assembly-definition-labels defs entry)
                   :in-theory (enable assembly-definition-labels)))))

(local
 (defthm assembly-system-label-names-are-disjoint
   (implies (and (string-listp keys)
                 (not (member-equal "rt:entry" keys))
                 (not (member-equal "data:static" keys)))
            (assembly-label-lists-disjoint-p
             keys (append (assembly-definition-labels defs entry) '("data:static"))))
   :hints (("Goal" :induct (len keys)))))

(defthm assembly-compile-prefix-distinct-labels
  (implies (and (assembly-system-layout-p system)
                (no-duplicatesp-equal (strip-cars defs)))
           (no-duplicatesp-equal (assembly-label-names (assembly-compile-prefix entry defs context system))))
  :hints (("Goal"
           :use (assembly-compile-prefix-local-layout
                 assembly-compile-prefix-global-labels
                 (:instance assembly-labels-by-namespace-are-distinct
                            (keys (assembly-label-names (assembly-compile-prefix entry defs context system)))))
           :in-theory (e/d (assembly-system-layout-p)
                           (assembly-compile-prefix assembly-initial-code-is-reversed))))
  :rule-classes nil)

(defthm assembly-compile-prefix-has-public-labels
  (implies (and (assembly-system-layout-p system)
                (or (equal key "data:static")
                    (member-equal key (assembly-label-names (assembly-system-items system)))
                    (member-equal key (assembly-definition-labels defs entry))))
           (member-equal key (assembly-label-names (assembly-compile-prefix entry defs context system))))
  :hints (("Goal"
           :use (assembly-compile-prefix-global-labels
                 (:instance assembly-labels-by-namespace-membership
                            (keys (assembly-label-names (assembly-compile-prefix entry defs context system)))))
           :in-theory (disable assembly-labels-by-namespace-membership assembly-compile-prefix)))
  :rule-classes nil)

(local
 (defthm assembly-primitive-reference-in-template
   (implies (and (assembly-system-layout-p system)
                 (or (member-equal key (assembly-routine-destinations boymoo-compiler::*jets*))
                     (member-equal key (assembly-routine-destinations boymoo-compiler::*primitives*))))
            (member-equal key (assembly-label-names (assembly-system-items system))))
   :hints (("Goal"
            :use ((:instance assembly-member-subsetp
                             (first (assembly-routine-destinations boymoo-compiler::*jets*))
                             (rest (assembly-label-names (assembly-system-items system))))
                  (:instance assembly-member-subsetp
                             (first (assembly-routine-destinations boymoo-compiler::*primitives*))
                             (rest (assembly-label-names (assembly-system-items system)))))
            :in-theory (e/d (assembly-system-layout-p)
                            (member-equal assembly-routine-destinations
                             (:executable-counterpart assembly-routine-destinations)))))
   :rule-classes nil))

(local
 (defthm assembly-compile-prefix-has-allowed-reference
   (implies (and (assembly-system-layout-p system)
                 (assembly-arity-index-covered-p (car context) 12 (strip-cars defs))
                 (or (assembly-allowed-generated-reference-p key context)
                     (equal key "rt:grow") (equal key "rt:deep")))
            (member-equal key (assembly-label-names (assembly-compile-prefix entry defs context system))))
   :hints (("Goal"
            :use (assembly-compile-prefix-has-public-labels assembly-primitive-reference-in-template
                  (:instance assembly-covered-arity-index-lookup
                             (key (cadr key)) (index (car context)) (names (strip-cars defs))))
            :in-theory (e/d (assembly-system-layout-p)
                            (assembly-compile-prefix assembly-arity-index-covered-p
                             boymoo-compiler::index-get member-equal assembly-routine-destinations
                             (:executable-counterpart assembly-routine-destinations)))))
   :rule-classes nil))

(local
 (defthm assembly-compile-prefix-has-template-reference
   (implies (and (assembly-system-layout-p system)
                 (member-equal entry (strip-cars defs))
                 (member-equal key (assembly-references (assembly-initial-code system))))
            (member-equal key (assembly-label-names (assembly-compile-prefix entry defs context system))))
   :hints (("Goal"
            :use (assembly-compile-prefix-has-public-labels
                  (:instance assembly-member-subsetp
                             (first (assembly-references (assembly-system-items system)))
                             (rest (list* "rt:entry" "data:static"
                                          (assembly-label-names (assembly-system-items system))))))
            :in-theory (e/d (assembly-system-layout-p) (assembly-compile-prefix))))
   :rule-classes nil))

(defthm assembly-compile-prefix-resolves-reference
  (let ((prefix (assembly-compile-prefix entry defs context system)))
    (implies (and (assembly-system-layout-p system)
                  (member-equal entry (strip-cars defs))
                  (assembly-arity-index-covered-p (car context) 12 (strip-cars defs))
                  (member-equal key (assembly-references prefix)))
             (member-equal key (assembly-label-names prefix))))
  :hints (("Goal"
           :use (assembly-compile-prefix-has-allowed-reference
                 assembly-compile-prefix-has-template-reference
                 (:instance assembly-gen-functions-reference-origin
                            (serial 0) (code (assembly-initial-code system))))
           :in-theory (disable assembly-initial-code-is-reversed
                               assembly-allowed-generated-reference-p
                               assembly-arity-index-covered-p assembly-references
                               assembly-label-names)))
  :rule-classes nil)

(local
 (defun assembly-unresolved-reference (targets keys)
   (if (atom targets)
       nil
     (if (member-equal (car targets) keys)
         (assembly-unresolved-reference (cdr targets) keys)
       (car targets)))))

(local
 (defthm assembly-unresolved-reference-is-witness
   (let ((key (assembly-unresolved-reference targets keys)))
     (implies (not (subsetp-equal targets keys))
              (and (member-equal key targets) (not (member-equal key keys)))))
   :hints (("Goal" :induct (assembly-unresolved-reference targets keys)))
   :rule-classes nil))

(defthm assembly-compile-prefix-resolves-references
  (let ((prefix (assembly-compile-prefix entry defs context system)))
    (implies (and (assembly-system-layout-p system)
                  (member-equal entry (strip-cars defs))
                  (assembly-arity-index-covered-p (car context) 12 (strip-cars defs)))
             (subsetp-equal (assembly-references prefix) (assembly-label-names prefix))))
  :hints (("Goal"
           :use ((:instance assembly-compile-prefix-resolves-reference
                            (key (assembly-unresolved-reference
                                  (assembly-references (assembly-compile-prefix entry defs context system))
                                  (assembly-label-names (assembly-compile-prefix entry defs context system)))))
                 (:instance assembly-unresolved-reference-is-witness
                            (targets (assembly-references (assembly-compile-prefix entry defs context system)))
                            (keys (assembly-label-names (assembly-compile-prefix entry defs context system)))))
           :in-theory (disable assembly-compile-prefix assembly-arity-index-covered-p)))
  :rule-classes nil)

(local
 (defthm assembly-fixed-items-of-append
   (equal (assembly-fixed-item-list-p (append first rest))
          (and (assembly-fixed-item-list-p (true-list-fix first))
               (assembly-fixed-item-list-p rest)))
   :hints (("Goal" :induct (append first rest) :in-theory (disable assembly-fixed-item-p)))))

(local
 (defthm assembly-compile-prefix-is-true-list
   (true-listp (assembly-compile-prefix entry defs context system))
   :hints (("Goal" :in-theory (enable revappend)))
   :rule-classes :type-prescription))

(local
 (defthm assembly-true-list-fix-of-true-list
   (implies (true-listp items)
            (equal (true-list-fix items) items))))

(defthm assembly-compile-prefix-fixed-fields
  (implies (and (assembly-system-layout-p system)
                (true-listp defs) (string-listp (strip-cars defs))
                (assembly-constant-index-p (caddr context) 12))
           (assembly-fixed-item-list-p (assembly-compile-prefix entry defs context system)))
  :hints (("Goal"
           :use ((:instance assembly-compiled-items-fixed-fields (data '(0)))
                 (:instance assembly-compile-items-add-static-image (data '(0)))
                 (:instance assembly-generated-bodies-for-typed-constants (serial 0)))
           :in-theory (e/d (assembly-system-layout-p)
                           (assembly-compile-prefix boymoo-compiler::compile-items
                            assembly-fixed-item-list-p assembly-generated-bodies-p
                            assembly-compiled-items-fixed-fields assembly-constant-index-p))
           :do-not-induct t))
  :rule-classes nil)

(defun assembly-compilation-inputs-p (entry defs context data system)
  (and (assembly-system-layout-p system)
       (true-listp defs) (string-listp (strip-cars defs))
       (no-duplicatesp-equal (strip-cars defs))
       (member-equal entry (strip-cars defs))
       (assembly-constant-index-p (caddr context) 12)
       (assembly-arity-index-covered-p (car context) 12 (strip-cars defs))
       (proof-image-p data)))

(defthm assembly-compile-items-pass-image-checks
  (implies (and (assembly-compilation-inputs-p entry defs context data system)
                (< (assembly-size (assembly-compile-prefix entry defs context system)) (expt 2 20)))
           (assembly-image-program-p (boymoo-compiler::compile-items entry defs context data system)))
  :hints (("Goal"
           :use (assembly-compile-items-add-static-image
                 assembly-compile-prefix-local-layout assembly-compile-prefix-distinct-labels
                 assembly-compile-prefix-resolves-references assembly-compile-prefix-fixed-fields
                 (:instance assembly-image-program-with-final-data
                            (prefix (assembly-compile-prefix entry defs context system))))
           :in-theory (disable assembly-compile-prefix boymoo-compiler::compile-items
                               assembly-fixed-item-list-p assembly-image-program-p
                               assembly-size assembly-no-image-items-p assembly-arity-index-covered-p
                               assembly-constant-index-p proof-image-p)))
  :rule-classes nil)
