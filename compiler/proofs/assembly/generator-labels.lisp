(in-package "BOYMOO-PROOFS")

(include-book "generator-emission")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-local-label-p (key)
  (and (equal key (list :local (cadr key))) (natp (cadr key))))

(defun assembly-local-label-in-range-p (key first next)
  (and (assembly-local-label-p key)
       (<= first (cadr key)) (< (cadr key) next)))

(local
 (defthm assembly-gen-routine-next-serial
   (implies (natp serial)
            (equal (mv-nth 1 (boymoo-compiler::gen-routine name label serial code))
                   (+ serial
                      (cond ((member-equal name '("COMMON-LISP::CAR" "COMMON-LISP::CDR")) 1)
                            ((equal name "COMMON-LISP::EQUAL") 3)
                            ((member-equal name '("ACL2::BINARY-+" "ACL2::UNARY--" "COMMON-LISP::<")) 2)
                            (t 0)))))
   :hints (("Goal" :in-theory (disable boymoo-compiler::gen-car-cdr boymoo-compiler::gen-equal
                                       boymoo-compiler::gen-arithmetic boymoo-compiler::gen-boolean)))))

(local
 (defthm assembly-generator-result-component-of-cons
   (equal (mv-nth n (cons first rest))
          (if (zp n) first (mv-nth (1- n) rest)))))

(local
 (defthm assembly-reference-membership-of-append
   (iff (member-equal key (append first rest))
        (or (member-equal key first) (member-equal key rest)))))

(local
 (defthm assembly-gen-routine-natural-serial
   (implies (natp serial)
            (natp (mv-nth 1 (boymoo-compiler::gen-routine name label serial code))))
   :hints (("Goal" :use (assembly-gen-routine-serial)
                   :in-theory (disable boymoo-compiler::gen-routine)))))

(local
 (defthm assembly-gen-routine-serial-lower-bound
   (implies (natp serial)
            (<= serial (mv-nth 1 (boymoo-compiler::gen-routine name label serial code))))
   :hints (("Goal" :use (assembly-gen-routine-serial)
                   :in-theory (disable boymoo-compiler::gen-routine)))
   :rule-classes :linear))

(local (in-theory (disable mv-nth length
                           boymoo-compiler::gen-term boymoo-compiler::gen-args
                           boymoo-compiler::gen-lambda-args boymoo-compiler::gen-simple
                           boymoo-compiler::gen-simple-p boymoo-compiler::gen-simple-args
                           boymoo-compiler::gen-simple-args-p boymoo-compiler::gen-frame-word
                           boymoo-compiler::gen-mbe-p boymoo-compiler::gen-slot
                           boymoo-compiler::gen-datum boymoo-compiler::gen-argument-registers
                           boymoo-compiler::gen-copy-arguments boymoo-compiler::gen-defined-call
                           boymoo-compiler::gen-address boymoo-compiler::gen-load-high
                           boymoo-compiler::gen-load-word boymoo-compiler::gen-load-datum
                           boymoo-compiler::gen-car-cdr boymoo-compiler::gen-equal
                           boymoo-compiler::gen-arithmetic boymoo-compiler::gen-boolean
                           boymoo-compiler::gen-routine boymoo-compiler::gen-call-info
                           boymoo-compiler::gen-prologue boymoo-compiler::gen-push
                           boymoo-compiler::gen-drop boymoo-compiler::gen-finish
                           boymoo-compiler::bind-formal boymoo-compiler::declaration-list
                           boymoo-compiler::reverse-onto
                           assembly-item-refers-to-label-p assembly-item-target-label
                           assembly-simple-form-p assembly-simple-forms-p)))

(local
 (defmacro assembly-prove-generator-property (name formula &rest hints)
   `(defthm ,name ,formula
      :hints (("Goal"
               :induct (assembly-generator-induction kind term formals scope body-scope depth
                                                     tail context code high serial)
               :expand ((:free (scope depth tail context code high serial)
                               (boymoo-compiler::gen-term term scope depth tail context code high serial))
                        (:free (scope depth context code high serial)
                               (boymoo-compiler::gen-args term scope depth context code high serial))
                        (:free (formals scope body-scope depth context code high serial)
                               (boymoo-compiler::gen-lambda-args term formals scope body-scope depth
                                                                context code high serial))))
              ,@hints)
      :rule-classes nil)))

(local
 (assembly-prove-generator-property
  assembly-generator-serial-monotone
  (let ((next (mv-nth 2 (assembly-generator-result kind term formals scope body-scope depth
                                                    tail context code high serial))))
    (implies (natp serial)
             (and (natp next) (<= serial next))))))

(local
 (defmacro assembly-generator-serial-rule (name call &rest bindings)
   `(defthm ,name
      (implies (natp serial)
               (and (natp (mv-nth 2 ,call))
                    (<= serial (mv-nth 2 ,call))))
      :hints (("Goal" :use ((:instance assembly-generator-serial-monotone ,@bindings))))
      :rule-classes
      ((:type-prescription :corollary (implies (natp serial) (natp (mv-nth 2 ,call))))
       (:rewrite :corollary (implies (natp serial) (integerp (mv-nth 2 ,call))))
       (:linear :corollary (implies (natp serial) (<= serial (mv-nth 2 ,call))))))))

(local
 (assembly-generator-serial-rule assembly-gen-term-serial
  (boymoo-compiler::gen-term term scope depth tail context code high serial)
  (kind :term) (formals nil) (body-scope nil)))

(local
 (assembly-generator-serial-rule assembly-gen-args-serial
  (boymoo-compiler::gen-args term scope depth context code high serial)
  (kind :args) (formals nil) (body-scope nil) (tail nil)))

(local
 (assembly-generator-serial-rule assembly-gen-lambda-args-serial
  (boymoo-compiler::gen-lambda-args term formals scope body-scope depth context code high serial)
  (kind :lambda-args) (tail nil)))

(local
 (assembly-prove-generator-property
  assembly-generator-label-origin
  (let* ((result (assembly-generator-result kind term formals scope body-scope depth
                                            tail context code high serial))
         (out (mv-nth 0 result))
         (next (mv-nth 2 result)))
    (implies (and (natp serial)
                  (member-equal key (assembly-label-names out))
                  (not (member-equal key (assembly-label-names code))))
             (assembly-local-label-in-range-p key serial next)))))

(local
 (assembly-prove-generator-property
  assembly-generator-preserves-image-free
  (implies (assembly-no-image-items-p code)
           (assembly-no-image-items-p
            (mv-nth 0 (assembly-generator-result kind term formals scope body-scope depth
                                                 tail context code high serial))))))

(defthm assembly-gen-term-label-origin
  (mv-let (out out-high next)
    (boymoo-compiler::gen-term term scope depth tail context code high serial)
    (declare (ignore out-high))
    (implies (natp serial)
             (and (natp next) (<= serial next)
                  (implies (and (member-equal key (assembly-label-names out))
                                (not (member-equal key (assembly-label-names code))))
                           (assembly-local-label-in-range-p key serial next))
                  (implies (assembly-no-image-items-p code)
                           (assembly-no-image-items-p out)))))
  :hints (("Goal" :use ((:instance assembly-generator-label-origin
                                   (kind :term) (formals nil) (body-scope nil))
                        (:instance assembly-generator-preserves-image-free
                                   (kind :term) (formals nil) (body-scope nil)))))
  :rule-classes nil)

(defun assembly-labels-before-serial-p (keys serial)
  (if (atom keys)
      t
    (and (implies (assembly-local-label-p (car keys)) (< (cadar keys) serial))
         (assembly-labels-before-serial-p (cdr keys) serial))))

(local
 (defun assembly-label-at-or-after-serial (keys serial)
   (if (atom keys)
       nil
     (if (and (assembly-local-label-p (car keys)) (<= serial (cadar keys)))
         (car keys)
       (assembly-label-at-or-after-serial (cdr keys) serial)))))

(local
 (defthm assembly-label-bound-for-member
   (implies (and (assembly-labels-before-serial-p keys serial)
                 (member-equal key keys) (assembly-local-label-p key))
            (< (cadr key) serial))
   :hints (("Goal" :induct (assembly-labels-before-serial-p keys serial)))
   :rule-classes nil))

(local
 (defthm assembly-label-bound-violation
   (let ((key (assembly-label-at-or-after-serial keys serial)))
     (implies (not (assembly-labels-before-serial-p keys serial))
              (and (member-equal key keys) (assembly-local-label-p key)
                   (<= serial (cadr key)))))
   :hints (("Goal" :induct (assembly-label-at-or-after-serial keys serial)))
   :rule-classes nil))

(local
 (defthm assembly-generator-respects-serial-bound
   (let* ((result (assembly-generator-result kind term formals scope body-scope depth
                                             tail context code high serial))
          (keys (assembly-label-names (mv-nth 0 result)))
          (next (mv-nth 2 result)))
     (implies (and (natp serial) (assembly-labels-before-serial-p (assembly-label-names code) serial))
              (assembly-labels-before-serial-p keys next)))
   :hints (("Goal"
            :use ((:instance assembly-generator-label-origin
                             (key (assembly-label-at-or-after-serial
                                   (assembly-label-names
                                    (mv-nth 0 (assembly-generator-result
                                               kind term formals scope body-scope depth
                                               tail context code high serial)))
                                   (mv-nth 2 (assembly-generator-result
                                              kind term formals scope body-scope depth
                                              tail context code high serial)))))
                  assembly-generator-serial-monotone
                  (:instance assembly-label-bound-violation
                             (keys (assembly-label-names
                                    (mv-nth 0 (assembly-generator-result
                                               kind term formals scope body-scope depth
                                               tail context code high serial))))
                             (serial (mv-nth 2 (assembly-generator-result
                                                kind term formals scope body-scope depth
                                                tail context code high serial))))
                  (:instance assembly-label-bound-for-member
                             (keys (assembly-label-names code))
                             (key (assembly-label-at-or-after-serial
                                   (assembly-label-names
                                    (mv-nth 0 (assembly-generator-result
                                               kind term formals scope body-scope depth
                                               tail context code high serial)))
                                   (mv-nth 2 (assembly-generator-result
                                              kind term formals scope body-scope depth
                                              tail context code high serial))))))
            :in-theory (disable assembly-generator-result assembly-label-names
                                assembly-label-at-or-after-serial assembly-labels-before-serial-p)))
   :rule-classes nil))

(local
 (defmacro assembly-generator-label-bound-rule (name call &rest bindings)
   `(defthm ,name
      (implies (and (natp serial)
                    (assembly-labels-before-serial-p (assembly-label-names code) serial))
               (assembly-labels-before-serial-p
                (assembly-label-names (mv-nth 0 ,call)) (mv-nth 2 ,call)))
      :hints (("Goal" :use ((:instance assembly-generator-respects-serial-bound ,@bindings)))))))

(local
 (assembly-generator-label-bound-rule assembly-gen-term-labels-bounded
  (boymoo-compiler::gen-term term scope depth tail context code high serial)
  (kind :term) (formals nil) (body-scope nil)))

(local
 (assembly-generator-label-bound-rule assembly-gen-args-labels-bounded
  (boymoo-compiler::gen-args term scope depth context code high serial)
  (kind :args) (formals nil) (body-scope nil) (tail nil)))

(local
 (assembly-generator-label-bound-rule assembly-gen-lambda-args-labels-bounded
  (boymoo-compiler::gen-lambda-args term formals scope body-scope depth context code high serial)
  (kind :lambda-args) (tail nil)))

(local
 (defthm assembly-local-key-at-or-after-absent
   (implies (and (assembly-labels-before-serial-p keys serial)
                 (assembly-local-label-p key)
                 (<= serial (cadr key)))
            (not (member-equal key keys)))
   :hints (("Goal" :use (assembly-label-bound-for-member)))
   :rule-classes ((:rewrite :match-free :all :backchain-limit-lst (0 nil nil)))))

(local
 (defthm assembly-gen-term-cannot-introduce-earlier-label
   (let ((out (mv-nth 0 (boymoo-compiler::gen-term term scope depth tail context code high serial))))
     (implies (and (natp serial) (< (cadr key) serial)
                   (not (member-equal key (assembly-label-names code))))
              (not (member-equal key (assembly-label-names out)))))
   :hints (("Goal" :use (assembly-gen-term-label-origin)))
   :rule-classes ((:rewrite :backchain-limit-lst (nil nil 3)))))

(local
 (defthm assembly-label-bound-monotone
   (implies (and (assembly-labels-before-serial-p keys first) (<= first next))
            (assembly-labels-before-serial-p keys next))
   :hints (("Goal" :induct (assembly-labels-before-serial-p keys first)))
   :rule-classes ((:rewrite :match-free :all :backchain-limit-lst (0 nil)))))

(local
 (defthm assembly-label-bound-of-cons
   (equal (assembly-labels-before-serial-p (cons key keys) serial)
          (and (implies (assembly-local-label-p key) (< (cadr key) serial))
               (assembly-labels-before-serial-p keys serial)))))

(local (in-theory (disable assembly-labels-before-serial-p)))

(local
 (defthm assembly-gen-term-future-label-is-absent
   (mv-let (out out-high next)
     (boymoo-compiler::gen-term term scope depth tail context code high serial)
     (declare (ignore out-high))
     (implies (and (natp serial)
                   (assembly-labels-before-serial-p (assembly-label-names code) serial)
                   (natp number) (<= next number))
              (not (member-equal (list :local number) (assembly-label-names out)))))
   :hints (("Goal"
            :use (assembly-gen-term-labels-bounded
                  (:instance assembly-local-key-at-or-after-absent
                             (keys (assembly-label-names
                                    (mv-nth 0 (boymoo-compiler::gen-term
                                               term scope depth tail context code high serial))))
                             (serial (mv-nth 2 (boymoo-compiler::gen-term
                                                term scope depth tail context code high serial)))
                             (key (list :local number))))
            :in-theory (disable assembly-gen-term-labels-bounded
                                assembly-local-key-at-or-after-absent)))))

(local
 (defthm assembly-gen-term-labels-before-later-serial
   (mv-let (out out-high next)
     (boymoo-compiler::gen-term term scope depth tail context code high serial)
     (declare (ignore out-high))
     (implies (and (natp serial)
                   (assembly-labels-before-serial-p (assembly-label-names code) serial)
                   (<= next bound))
              (assembly-labels-before-serial-p (assembly-label-names out) bound)))
   :hints (("Goal"
            :use (assembly-gen-term-labels-bounded
                  (:instance assembly-label-bound-monotone
                             (keys (assembly-label-names
                                    (mv-nth 0 (boymoo-compiler::gen-term
                                               term scope depth tail context code high serial))))
                             (first (mv-nth 2 (boymoo-compiler::gen-term
                                               term scope depth tail context code high serial)))
                             (next bound)))
            :in-theory (disable assembly-gen-term-labels-bounded
                                assembly-label-bound-monotone)))
   :rule-classes ((:rewrite :backchain-limit-lst (nil 3 nil)))))

(local
 (defthm assembly-routine-keeps-labels-distinct
   (implies (and (natp serial)
                 (assembly-labels-before-serial-p keys serial)
                 (no-duplicatesp-equal keys))
            (no-duplicatesp-equal (append (assembly-routine-labels name serial) keys)))
   :hints (("Goal"
            :use ((:instance assembly-local-key-at-or-after-absent (key (list :local serial)))
                  (:instance assembly-local-key-at-or-after-absent (key (list :local (+ serial 1))))
                  (:instance assembly-local-key-at-or-after-absent (key (list :local (+ serial 2)))))
            :in-theory (disable assembly-local-key-at-or-after-absent)))))

(local
 (defthm assembly-routine-labels-distinct
   (implies (natp serial)
            (no-duplicatesp-equal (assembly-routine-labels name serial)))
   :hints (("Goal"
            :use ((:instance assembly-routine-keeps-labels-distinct (keys nil)))
            :in-theory (disable assembly-routine-keeps-labels-distinct)))))

(local (in-theory (disable assembly-routine-labels)))

(local
 (assembly-prove-generator-property
  assembly-generator-preserves-distinct-labels
  (implies (and (natp serial)
                (assembly-labels-before-serial-p (assembly-label-names code) serial)
                (no-duplicatesp-equal (assembly-label-names code)))
           (no-duplicatesp-equal
            (assembly-label-names
             (mv-nth 0 (assembly-generator-result kind term formals scope body-scope depth
                                                 tail context code high serial)))))))

(defthm assembly-gen-term-keeps-labels-distinct
  (mv-let (out out-high next)
    (boymoo-compiler::gen-term term scope depth tail context code high serial)
    (declare (ignore out-high))
    (implies (and (natp serial)
                  (assembly-labels-before-serial-p (assembly-label-names code) serial)
                  (no-duplicatesp-equal (assembly-label-names code)))
             (and (no-duplicatesp-equal (assembly-label-names out))
                  (assembly-labels-before-serial-p (assembly-label-names out) next))))
  :hints (("Goal" :use ((:instance assembly-generator-preserves-distinct-labels
                                   (kind :term) (formals nil) (body-scope nil))
                        (:instance assembly-generator-respects-serial-bound
                                   (kind :term) (formals nil) (body-scope nil)))))
  :rule-classes nil)

(defun assembly-local-labels-in-range-p (keys first next)
  (if (atom keys)
      t
    (and (assembly-local-label-in-range-p (car keys) first next)
         (assembly-local-labels-in-range-p (cdr keys) first next))))

(local
 (defun assembly-label-outside-range (keys first next)
   (if (atom keys)
       nil
     (if (assembly-local-label-in-range-p (car keys) first next)
         (assembly-label-outside-range (cdr keys) first next)
       (car keys)))))

(local
 (defthm assembly-label-range-violation
   (let ((key (assembly-label-outside-range keys first next)))
     (implies (not (assembly-local-labels-in-range-p keys first next))
              (and (member-equal key keys)
                   (not (assembly-local-label-in-range-p key first next)))))
   :hints (("Goal" :induct (assembly-label-outside-range keys first next)
                   :in-theory (disable assembly-local-label-in-range-p)))
   :rule-classes nil))

(defthm assembly-new-term-labels-are-local
  (mv-let (out out-high next)
    (boymoo-compiler::gen-term term scope depth tail context nil high serial)
    (declare (ignore out-high))
    (implies (natp serial)
             (assembly-local-labels-in-range-p (assembly-label-names out) serial next)))
  :hints (("Goal"
           :use ((:instance assembly-gen-term-label-origin
                            (code nil)
                            (key (assembly-label-outside-range
                                  (assembly-label-names
                                   (mv-nth 0 (boymoo-compiler::gen-term
                                              term scope depth tail context nil high serial)))
                                  serial
                                  (mv-nth 2 (boymoo-compiler::gen-term
                                             term scope depth tail context nil high serial)))))
                 (:instance assembly-label-range-violation
                            (keys (assembly-label-names
                                   (mv-nth 0 (boymoo-compiler::gen-term
                                              term scope depth tail context nil high serial))))
                            (first serial)
                            (next (mv-nth 2 (boymoo-compiler::gen-term
                                             term scope depth tail context nil high serial)))))
           :in-theory (disable assembly-label-names assembly-local-label-in-range-p
                               assembly-label-outside-range assembly-local-labels-in-range-p)))
  :rule-classes nil)
