(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::gen-call-info
                    boymoo-compiler::gen-simple-p
                    boymoo-compiler::gen-mbe-p
                    boymoo-compiler::gen-simple-args-p
                    boymoo-compiler::gen-local
                    boymoo-compiler::gen-emit
                    boymoo-compiler::gen-push
                    boymoo-compiler::gen-drop
                    boymoo-compiler::gen-simple
                    boymoo-compiler::gen-slot
                    boymoo-compiler::gen-finish
                    boymoo-compiler::gen-routine
                    boymoo-compiler::gen-defined-call
                    boymoo-compiler::gen-load-datum
                    boymoo-compiler::gen-argument-registers
                    boymoo-compiler::bind-formal
                    boymoo-compiler::declaration-list))

(local
 (defthm generated-simple-on-atom
   (implies (not (consp input))
            (boymoo-compiler::gen-simple-p input))
   :hints (("Goal" :in-theory (enable boymoo-compiler::gen-simple-p)))))

; The first component records the occupied depth just after each emitted
; push. It counts both conditional arms and the logical half of an MBE.
; The second component gives the depth at the end of argument evaluation.
(defun generated-push-schedule (kind input formals depth context)
  (declare (xargs :measure (+ (* 2 (acl2-count input))
                              (if (eq kind :term) 1 0))
                  :ruler-extenders :all))
  (case kind
    (:args
     (if (atom input)
         (cons nil depth)
       (let ((first (generated-push-schedule :term (car input) nil depth context))
             (rest (generated-push-schedule :args (cdr input) nil (1+ depth) context)))
         (cons (append (car first) (cons (1+ depth) (car rest))) (cdr rest)))))
    (:lambda-args
     (cond ((or (atom input) (atom formals)) (cons nil depth))
           ((atom (car input))
            (generated-push-schedule :lambda-args (cdr input) (cdr formals)
                                     depth context))
           (t
            (let ((first (generated-push-schedule :term (car input) nil depth context))
                  (rest (generated-push-schedule :lambda-args (cdr input) (cdr formals)
                                                  (1+ depth) context)))
              (cons (append (car first) (cons (1+ depth) (car rest))) (cdr rest))))))
    (:term
     (let ((head (car input)) (args (cdr input)))
       (cond
        ((boymoo-compiler::gen-simple-p input) (cons nil depth))
        ((equal head boymoo-compiler::*if-name*)
         (if (equal (length args) 3)
             (cons (append
                    (car (generated-push-schedule :term (car args) nil depth context))
                    (car (generated-push-schedule :term (cadr args) nil depth context))
                    (car (generated-push-schedule :term (caddr args) nil depth context)))
                   depth)
           (cons nil depth)))
        ((and (boymoo-compiler::gen-mbe-p head args) (equal (length args) 3))
         (generated-push-schedule :term (caddr args) nil depth context))
        ((consp head)
         (if (and (equal (car head) "COMMON-LISP::LAMBDA")
                  (consp (cddr head)) (null (cdddr head))
                  (or (consp (cadr head))
                      (equal (cadr head) boymoo-compiler::*nil-name*)))
             (let ((actuals (generated-push-schedule
                             :lambda-args args (boymoo-compiler::declaration-list (cadr head))
                             depth context)))
               (cons (append (car actuals)
                             (car (generated-push-schedule :term (caddr head) nil
                                                            (cdr actuals) context)))
                     depth))
           (cons nil depth)))
        (t
         (mv-let (target expected routine)
           (boymoo-compiler::gen-call-info head context)
           (declare (ignore target))
           (if (or (and expected (not (equal (length args) expected)))
                   (and routine (boymoo-compiler::gen-simple-args-p args)))
               (cons nil depth)
             (cons (car (generated-push-schedule :args args nil depth context))
                   depth)))))))
    (otherwise (cons nil depth))))

(defun generated-max-push (tops high)
  (if (atom tops)
      high
    (generated-max-push (cdr tops) (boymoo-compiler::gen-max high (car tops)))))

(defthm generated-max-push-over-append
  (equal (generated-max-push (append first second) high)
         (generated-max-push second (generated-max-push first high)))
  :hints (("Goal" :induct (generated-max-push first high))))

(defthm generated-max-push-keeps-initial
  (implies (and (rationalp high) (rational-listp tops))
           (<= high (generated-max-push tops high)))
  :hints (("Goal" :induct (generated-max-push tops high)))
  :rule-classes :linear)

(defthm generated-max-push-bounds-member
  (implies (and (rational-listp tops)
                (rationalp high)
                (member-equal requested tops))
           (<= requested (generated-max-push tops high)))
  :hints (("Goal" :induct (generated-max-push tops high)))
  :rule-classes nil)

(set-irrelevant-formals-ok t)

(local
 (defun generated-stack-induction (kind input formals scope body-scope depth
                                        tail context code high serial)
   (declare (xargs :measure (+ (* 2 (acl2-count input))
                               (if (eq kind :term) 1 0))
                   :ruler-extenders :all))
   (case kind
     (:args
      (if (atom input)
          nil
        (mv-let (next-code next-high next-serial)
          (boymoo-compiler::gen-term (car input) scope depth nil context code high serial)
          (list
           (generated-stack-induction :term (car input) nil scope nil depth
                                      nil context code high serial)
           (generated-stack-induction :args (cdr input) nil scope nil (1+ depth)
                                      nil context (boymoo-compiler::gen-push next-code)
                                      (boymoo-compiler::gen-max next-high (1+ depth))
                                      next-serial)))))
     (:lambda-args
      (cond ((or (atom input) (atom formals)) nil)
            ((atom (car input))
             (generated-stack-induction
              :lambda-args (cdr input) (cdr formals) scope
              (boymoo-compiler::bind-formal
               (car formals) (boymoo-compiler::gen-slot (car input) scope) body-scope)
              depth nil context code high serial))
            (t
             (mv-let (next-code next-high next-serial)
               (boymoo-compiler::gen-term (car input) scope depth nil context code high serial)
               (list
                (generated-stack-induction :term (car input) nil scope nil depth
                                           nil context code high serial)
                (generated-stack-induction
                 :lambda-args (cdr input) (cdr formals) scope
                 (boymoo-compiler::bind-formal (car formals) depth body-scope)
                 (1+ depth) nil context (boymoo-compiler::gen-push next-code)
                 (boymoo-compiler::gen-max next-high (1+ depth)) next-serial))))))
     (otherwise
      (if (or (not (eq kind :term)) (boymoo-compiler::gen-simple-p input))
          nil
        (let ((head (car input)) (args (cdr input)))
          (cond
           ((equal head boymoo-compiler::*if-name*)
            (if (not (equal (length args) 3))
                nil
              (mv-let (test-code test-high test-serial)
                (boymoo-compiler::gen-term (car args) scope depth nil context code high serial)
                (let* ((yes (boymoo-compiler::gen-local test-serial))
                       (no (boymoo-compiler::gen-local (+ test-serial 1)))
                       (done (boymoo-compiler::gen-local (+ test-serial 2)))
                       (branch-code
                        (boymoo-compiler::gen-emit
                         (list '(:cmp 0 34) (list :b-cond :ne yes)
                               (list :b no) (list :label yes)) test-code)))
                  (mv-let (then-code then-high then-serial)
                    (boymoo-compiler::gen-term
                     (cadr args) scope depth tail context branch-code test-high
                     (+ test-serial 3))
                    (list
                     (generated-stack-induction :term (car args) nil scope nil depth
                                                nil context code high serial)
                     (generated-stack-induction
                      :term (cadr args) nil scope nil depth tail context
                      branch-code test-high (+ test-serial 3))
                     (generated-stack-induction
                      :term (caddr args) nil scope nil depth tail context
                      (cons (list :label no)
                            (if tail then-code (cons (list :b done) then-code)))
                      then-high then-serial)))))))
           ((and (boymoo-compiler::gen-mbe-p head args) (equal (length args) 3))
            (generated-stack-induction :term (caddr args) nil scope nil depth
                                       tail context code high serial))
           ((consp head)
            (if (and (equal (car head) "COMMON-LISP::LAMBDA")
                     (consp (cddr head)) (null (cdddr head))
                     (or (consp (cadr head))
                         (equal (cadr head) boymoo-compiler::*nil-name*)))
                (let ((formals (boymoo-compiler::declaration-list (cadr head))))
                  (mv-let (next-code next-high next-serial next-scope top)
                    (boymoo-compiler::gen-lambda-args
                     args formals scope nil depth context code high serial)
                    (list
                     (generated-stack-induction :lambda-args args formals scope nil depth
                                                nil context code high serial)
                     (generated-stack-induction :term (caddr head) nil next-scope nil top
                                                tail context next-code next-high next-serial))))
              nil))
           (t
            (mv-let (target expected routine)
              (boymoo-compiler::gen-call-info head context)
              (declare (ignore target))
              (if (or (and expected (not (equal (length args) expected)))
                      (and routine (boymoo-compiler::gen-simple-args-p args)))
                  nil
                (generated-stack-induction :args args nil scope nil depth
                                           nil context code high serial)))))))))))

(set-irrelevant-formals-ok nil)

(local
 (defthm generated-generator-high-and-top
   (let* ((schedule (generated-push-schedule kind input formals depth context))
          (peak (generated-max-push (car schedule) high)))
       (case kind
         (:term
          (equal (mv-nth 1 (boymoo-compiler::gen-term
                           input scope depth tail context code high serial))
                 peak))
         (:args
          (equal (mv-nth 1 (boymoo-compiler::gen-args
                           input scope depth context code high serial))
                 peak))
         (:lambda-args
          (mv-let (next-code next-high next-serial next-scope top)
            (boymoo-compiler::gen-lambda-args
             input formals scope body-scope depth context code high serial)
            (declare (ignore next-code next-serial next-scope))
            (and (equal next-high peak) (equal top (cdr schedule)))))
         (otherwise t)))
   :hints (("Goal"
            :induct (generated-stack-induction kind input formals scope body-scope depth
                                               tail context code high serial)
            :in-theory (disable boymoo-compiler::gen-call-info
                                boymoo-compiler::gen-simple-p
                                boymoo-compiler::gen-mbe-p
                                boymoo-compiler::gen-simple-args-p
                                boymoo-compiler::gen-local
                                boymoo-compiler::gen-emit
                                boymoo-compiler::gen-max
                                boymoo-compiler::gen-push
                                boymoo-compiler::gen-prologue
                                boymoo-compiler::gen-drop
                                boymoo-compiler::gen-simple
                                boymoo-compiler::gen-slot
                                boymoo-compiler::gen-finish
                                boymoo-compiler::gen-routine
                                boymoo-compiler::gen-defined-call
                                boymoo-compiler::gen-load-datum
                                boymoo-compiler::gen-argument-registers
                                boymoo-compiler::bind-formal
                                boymoo-compiler::declaration-list)))
   :rule-classes nil))

(defthm generated-term-high
  (equal (mv-nth 1 (boymoo-compiler::gen-term
                   term scope depth tail context code high serial))
         (generated-max-push (car (generated-push-schedule :term term nil depth context))
                             high))
  :hints (("Goal" :use (:instance generated-generator-high-and-top
                                  (kind :term) (input term) (formals nil) (body-scope nil))))
  :rule-classes nil)

(defthm generated-args-high
  (equal (mv-nth 1 (boymoo-compiler::gen-args args scope depth context code high serial))
         (generated-max-push (car (generated-push-schedule :args args nil depth context))
                             high))
  :hints (("Goal" :use (:instance generated-generator-high-and-top
                                  (kind :args) (input args) (formals nil)
                                  (tail nil) (body-scope nil))))
  :rule-classes nil)

(defthm generated-lambda-high-and-top
  (mv-let (next-code next-high next-serial next-scope top)
    (boymoo-compiler::gen-lambda-args
     args formals scope body-scope depth context code high serial)
    (declare (ignore next-code next-serial next-scope))
    (and (equal next-high
                (generated-max-push (car (generated-push-schedule
                                          :lambda-args args formals depth context))
                                    high))
         (equal top
                (cdr (generated-push-schedule :lambda-args args formals depth context)))))
  :hints (("Goal" :use (:instance generated-generator-high-and-top
                                  (kind :lambda-args) (input args) (tail nil))))
  :rule-classes nil)

(local
 (defun generated-args-schedule-induction (args depth)
   (if (atom args) depth
     (generated-args-schedule-induction (cdr args) (1+ depth)))))

(defthm generated-args-scheduled-top
  (implies (natp depth)
           (equal (cdr (generated-push-schedule :args args nil depth context))
                  (+ depth (len args))))
  :hints (("Goal" :induct (generated-args-schedule-induction args depth))))

(local
 (defthm generated-rational-listp-of-append
   (implies (and (rational-listp first) (rational-listp second))
            (rational-listp (append first second)))))

(defthm generated-push-schedule-type
  (implies (natp depth)
           (let ((schedule (generated-push-schedule kind input formals depth context)))
             (and (rational-listp (car schedule)) (natp (cdr schedule)))))
  :hints (("Goal" :induct (generated-push-schedule kind input formals depth context))))

(defthm generated-term-high-bounds-pushes
  (implies (and (natp depth) (natp high)
                (member-equal pushed
                              (car (generated-push-schedule :term term nil depth context))))
           (<= pushed (mv-nth 1 (boymoo-compiler::gen-term
                                  term scope depth tail context code high serial))))
  :hints (("Goal" :use (generated-term-high
                        (:instance generated-max-push-bounds-member
                                   (tops (car (generated-push-schedule
                                               :term term nil depth context)))
                                   (requested pushed)))
                  :in-theory (disable boymoo-compiler::gen-term generated-push-schedule)))
  :rule-classes nil)
