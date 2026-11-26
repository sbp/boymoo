(in-package "BOYMOO-PROOFS")

(include-book "generator-labels")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-local-labels (keys)
  (if (atom keys)
      nil
    (if (assembly-local-label-p (car keys))
        (cons (car keys) (assembly-local-labels (cdr keys)))
      (assembly-local-labels (cdr keys)))))

(defun assembly-global-labels (keys)
  (if (atom keys)
      nil
    (if (assembly-local-label-p (car keys))
        (assembly-global-labels (cdr keys))
      (cons (car keys) (assembly-global-labels (cdr keys))))))

(defun assembly-definition-labels (defs entry)
  (if (atom defs)
      nil
    (let ((name (caar defs))
          (rest (assembly-definition-labels (cdr defs) entry)))
      (if (equal name entry)
          (list* "rt:entry" (list :fn name) rest)
        (cons (list :fn name) rest)))))

(defmacro assembly-definition-body (definition context serial)
  (let* ((formals `(boymoo-compiler::declaration-list (cadr ,definition)))
         (arity `(length ,formals))
         (scope `(boymoo-compiler::bind-formals ,formals 0 nil)))
    `(boymoo-compiler::gen-term (caddr ,definition) ,scope ,arity t ,context nil
                                ,arity (+ 2 ,serial))))

(defthm assembly-labels-by-namespace-membership
  (and (iff (member-equal key (assembly-local-labels keys))
            (and (assembly-local-label-p key) (member-equal key keys)))
       (iff (member-equal key (assembly-global-labels keys))
            (and (not (assembly-local-label-p key)) (member-equal key keys))))
  :hints (("Goal" :induct (len keys) :in-theory (disable assembly-local-label-p))))

(defthm assembly-labels-by-namespace-are-distinct
  (equal (no-duplicatesp-equal keys)
         (and (no-duplicatesp-equal (assembly-local-labels keys))
              (no-duplicatesp-equal (assembly-global-labels keys))))
  :hints (("Goal" :induct (len keys) :in-theory (disable assembly-local-label-p)))
  :rule-classes nil)

(defthm assembly-labels-by-namespace-of-append
  (and (equal (assembly-local-labels (append first rest))
              (append (assembly-local-labels first) (assembly-local-labels rest)))
       (equal (assembly-global-labels (append first rest))
              (append (assembly-global-labels first) (assembly-global-labels rest))))
  :hints (("Goal" :induct (append first rest) :in-theory (disable assembly-local-label-p))))

(defthm assembly-membership-of-append
  (iff (member-equal key (append first rest))
       (or (member-equal key first) (member-equal key rest)))
  :hints (("Goal" :induct (append first rest))))

(defthm assembly-membership-of-revappend
  (iff (member-equal key (revappend first rest))
       (or (member-equal key first) (member-equal key rest)))
  :hints (("Goal" :induct (revappend first rest))))

(defthm assembly-revappend-of-nil
  (equal (revappend nil suffix) suffix))

(defthm assembly-double-revappend
  (equal (revappend (revappend first rest) suffix)
         (revappend rest (append first suffix)))
  :hints (("Goal" :induct (revappend first rest))))

(defthm assembly-labels-by-namespace-of-revappend
  (and (equal (assembly-local-labels (revappend first rest))
              (revappend (assembly-local-labels first) (assembly-local-labels rest)))
       (equal (assembly-global-labels (revappend first rest))
              (revappend (assembly-global-labels first) (assembly-global-labels rest))))
  :hints (("Goal" :induct (revappend first rest) :in-theory (disable assembly-local-label-p))))

(local
 (defthm assembly-labels-before-serial-of-append
   (equal (assembly-labels-before-serial-p (append first rest) serial)
          (and (assembly-labels-before-serial-p first serial)
               (assembly-labels-before-serial-p rest serial)))
   :hints (("Goal" :induct (append first rest) :in-theory (disable assembly-local-label-p)))))

(local
 (defthm assembly-label-before-serial-from-member
   (implies (and (member-equal key keys)
                 (assembly-local-label-p key)
                 (assembly-labels-before-serial-p keys serial))
            (< (cadr key) serial))
   :hints (("Goal" :induct (len keys) :in-theory (disable assembly-local-label-p)))
   :rule-classes nil))

(local
 (defthm assembly-local-label-not-at-or-after-serial
   (implies (and (assembly-labels-before-serial-p keys serial)
                 (natp number) (<= serial number))
            (not (member-equal (list :local number) keys)))
   :hints (("Goal"
            :use ((:instance assembly-label-before-serial-from-member (key (list :local number))))))
   :rule-classes ((:rewrite :match-free :all))))

(local
 (defthm assembly-labels-before-serial-monotone
   (implies (and (assembly-labels-before-serial-p keys lo) (<= lo hi))
            (assembly-labels-before-serial-p keys hi))
   :hints (("Goal" :induct (len keys) :in-theory (disable assembly-local-label-p)))
   :rule-classes ((:rewrite :match-free :all :backchain-limit-lst (0 nil)))))

(local
 (defthm assembly-label-range-projections
   (implies (assembly-local-labels-in-range-p keys first next)
            (and (implies (true-listp keys) (equal (assembly-local-labels keys) keys))
                 (equal (assembly-global-labels keys) nil)
                 (assembly-labels-before-serial-p keys next)))
   :hints (("Goal" :induct (len keys) :in-theory (disable assembly-local-label-p)))))

(local
 (defthm assembly-label-name-list-type
   (true-listp (assembly-label-names items))
   :rule-classes :type-prescription))

(local
 (defthm assembly-labels-bounded-in-each-namespace
   (implies (assembly-labels-before-serial-p keys serial)
            (assembly-labels-before-serial-p (assembly-local-labels keys) serial))
   :hints (("Goal" :induct (len keys) :in-theory (disable assembly-local-label-p)))))

(local
 (defthm assembly-combine-disjoint-local-labels
   (implies (and (assembly-local-labels-in-range-p keys first next)
                 (assembly-labels-before-serial-p suffix first)
                 (no-duplicatesp-equal keys)
                 (no-duplicatesp-equal suffix))
            (no-duplicatesp-equal (append keys suffix)))
   :hints (("Goal" :induct (len keys))
           ("Subgoal *1/2"
            :use ((:instance assembly-label-before-serial-from-member
                             (key (car keys)) (keys suffix) (serial first))))
           )))

(local
 (defthm assembly-combine-local-label-names
   (implies (and (true-listp body)
                 (assembly-local-labels-in-range-p body first next)
                 (assembly-labels-before-serial-p keys first)
                 (no-duplicatesp-equal body)
                 (no-duplicatesp-equal (assembly-local-labels keys)))
            (no-duplicatesp-equal (append body (assembly-local-labels keys))))
   :hints (("Goal"
            :use ((:instance assembly-combine-disjoint-local-labels
                             (keys body) (suffix (assembly-local-labels keys))))
            :in-theory (disable assembly-combine-disjoint-local-labels
                                assembly-local-labels-in-range-p
                                assembly-labels-before-serial-p)))))

(local (in-theory (disable boymoo-compiler::gen-prologue
                           boymoo-compiler::gen-term boymoo-compiler::bind-formals
                           boymoo-compiler::declaration-list length
                           boymoo-compiler::reverse-onto
                           assembly-local-labels-in-range-p)))

(local
 (defthm assembly-gen-prologue-keeps-local-labels-valid
   (let* ((keys (assembly-label-names code))
          (generated (assembly-label-names (boymoo-compiler::gen-prologue arity high serial code))))
     (implies (and (natp serial) (assembly-labels-before-serial-p keys serial)
                   (no-duplicatesp-equal (assembly-local-labels keys)))
              (and (assembly-labels-before-serial-p generated (+ 2 serial))
                   (no-duplicatesp-equal (assembly-local-labels generated)))))
   :hints (("Goal"
            :use ((:instance assembly-local-label-not-at-or-after-serial
                             (keys (assembly-label-names code)) (number serial))
                  (:instance assembly-local-label-not-at-or-after-serial
                             (keys (assembly-label-names code)) (number (+ serial 1)))
                  (:instance assembly-labels-before-serial-monotone
                             (keys (assembly-label-names code)) (lo serial) (hi (+ 2 serial))))
            :in-theory (disable assembly-local-label-not-at-or-after-serial
                                assembly-labels-before-serial-monotone)))
   :rule-classes nil))

(local
 (defthm assembly-definition-body-labels
   (mv-let (out high next)
     (assembly-definition-body definition context serial)
     (declare (ignore high))
     (implies (natp serial)
              (let ((keys (assembly-label-names out)))
                (and (natp next) (<= (+ 2 serial) next)
                     (no-duplicatesp-equal keys)
                     (assembly-local-labels-in-range-p keys (+ 2 serial) next)
                     (assembly-no-image-items-p out)))))
   :hints (("Goal"
            :use ((:instance assembly-new-term-labels-are-local
                             (term (caddr definition)) (tail t)
                             (scope (boymoo-compiler::bind-formals
                                     (boymoo-compiler::declaration-list (cadr definition)) 0 nil))
                             (depth (length (boymoo-compiler::declaration-list (cadr definition))))
                             (high (length (boymoo-compiler::declaration-list (cadr definition))))
                             (serial (+ 2 serial)))
                  (:instance assembly-gen-term-label-origin
                             (term (caddr definition)) (tail t) (code nil) (key nil)
                             (scope (boymoo-compiler::bind-formals
                                     (boymoo-compiler::declaration-list (cadr definition)) 0 nil))
                             (depth (length (boymoo-compiler::declaration-list (cadr definition))))
                             (high (length (boymoo-compiler::declaration-list (cadr definition))))
                             (serial (+ 2 serial)))
                  (:instance assembly-gen-term-keeps-labels-distinct
                             (term (caddr definition)) (tail t) (code nil)
                             (scope (boymoo-compiler::bind-formals
                                     (boymoo-compiler::declaration-list (cadr definition)) 0 nil))
                             (depth (length (boymoo-compiler::declaration-list (cadr definition))))
                             (high (length (boymoo-compiler::declaration-list (cadr definition))))
                             (serial (+ 2 serial))))
            :in-theory (disable mv-nth)))
   :rule-classes nil))

(defthm assembly-gen-functions-local-layout
  (let ((out (boymoo-compiler::gen-functions defs entry context serial code)))
    (implies (and (natp serial)
                  (assembly-labels-before-serial-p (assembly-label-names code) serial)
                  (no-duplicatesp-equal (assembly-local-labels (assembly-label-names code)))
                  (assembly-no-image-items-p code))
             (and (no-duplicatesp-equal (assembly-local-labels (assembly-label-names out)))
                  (assembly-no-image-items-p out))))
  :hints (("Goal" :induct (boymoo-compiler::gen-functions defs entry context serial code)
                  :in-theory (disable revappend mv-nth))
           ("Subgoal *1/2"
            :use ((:instance assembly-definition-body-labels (definition (car defs)))
                  (:instance assembly-gen-prologue-keeps-local-labels-valid
                             (arity (length (boymoo-compiler::declaration-list (cadar defs))))
                             (high (mv-nth 1 (assembly-definition-body (car defs) context serial)))
                             (code (cons (list :label (list :fn (caar defs)))
                                         (if (equal (caar defs) entry)
                                             (cons '(:label "rt:entry") code)
                                           code)))))))
  :rule-classes nil)

(defthm assembly-gen-functions-global-labels
  (implies (natp serial)
           (equal
            (assembly-global-labels
             (assembly-label-names (boymoo-compiler::gen-functions defs entry context serial code)))
            (revappend (assembly-definition-labels defs entry)
                       (assembly-global-labels (assembly-label-names code)))))
  :hints (("Goal" :induct (boymoo-compiler::gen-functions defs entry context serial code)
                  :in-theory (disable mv-nth))
           ("Subgoal *1/2"
            :use ((:instance assembly-definition-body-labels (definition (car defs))))))
  :rule-classes nil)
