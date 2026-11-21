(in-package "BOYMOO")

(include-book "check")

; The logical equations of the functions with executable alternatives
; for calls of total ACL2 primitives.

(defthm cg-sum-logical-equation
  (equal (sum l)
         (if (consp l)
             (+ (car l) (sum (cdr l)))
           0))
  :rule-classes nil
  :hints (("Goal" :expand ((sum l)))))

(defthm cg-calls-p-logical-equation
  (equal (calls-p x fns)
         (if (consp x)
              (if (equal (car x) '|COMMON-LISP::QUOTE|)
                  nil
                (if (consp (car x))
                    (if (calls-p (car (cdr (cdr (car x)))) fns)
                        t
                      (calls-list-p (cdr x) fns))
                  (if (mbe-p x)
                      (calls-p (car (cdr (cdr (cdr x)))) fns)
                    (if (member-p (car x) fns)
                        t
                      (calls-list-p (cdr x) fns)))))
            nil))
  :rule-classes nil
  :hints (("Goal" :expand ((calls-p x fns)))))

(defthm cg-rename-calls-logical-equation
  (equal (rename-calls x ren)
         (if (consp x)
              (if (equal (car x) '|COMMON-LISP::QUOTE|)
                  x
                (if (consp (car x))
                    (cons (list '|COMMON-LISP::LAMBDA|
                                (car (cdr (car x)))
                                (rename-calls (car (cdr (cdr (car x)))) ren))
                          (rename-list (cdr x) ren))
                  (let ((p (pair-of (car x) ren)))
                    (cons (if p (cdr p) (car x)) (rename-list (cdr x) ren)))))
            x))
  :rule-classes nil
  :hints (("Goal" :expand ((rename-calls x ren)))))

(defthm cg-args-subst-size-logical-equation
  (equal (args-subst-size xs ss)
         (if (consp xs)
              (+ 1 (subst-size (car xs) ss) (args-subst-size (cdr xs) ss))
            1))
  :rule-classes nil
  :hints (("Goal" :expand ((args-subst-size xs ss)))))

(defthm cg-prim-value-logical-equation
  (equal (prim-value f args w)
         (let ((x (car args))
               (y (car (cdr args))))
           (cond
            ((equal f '|ACL2::ACL2-NUMBERP|) (list (acl2-numberp x)))
            ((equal f '|ACL2::BAD-ATOM<=|) (list nil))
            ((equal f '|ACL2::BINARY-*|) (list (* x y)))
            ((equal f '|ACL2::BINARY-+|) (list (+ x y)))
            ((equal f '|ACL2::UNARY--|) (list (- x)))
            ((equal f '|ACL2::UNARY-/|) (list (/ x)))
            ((equal f '|COMMON-LISP::<|) (list (< x y)))
            ((equal f '|COMMON-LISP::CAR|) (list (car x)))
            ((equal f '|COMMON-LISP::CDR|) (list (cdr x)))
            ((equal f '|COMMON-LISP::CHAR-CODE|) (list (char-code x)))
            ((equal f '|COMMON-LISP::CHARACTERP|) (list (characterp x)))
            ((equal f '|COMMON-LISP::CODE-CHAR|) (list (code-char x)))
            ((equal f '|COMMON-LISP::COMPLEX|) (list (complex x y)))
            ((equal f '|ACL2::COMPLEX-RATIONALP|) (list (complex-rationalp x)))
            ((equal f '|COMMON-LISP::COERCE|)
             (list (if (equal y '|COMMON-LISP::LIST|)
                       (coerce x 'list)
                     (coerce x 'string))))
            ((equal f '|COMMON-LISP::CONS|) (list (cons x y)))
            ((equal f '|COMMON-LISP::CONSP|) (list (consp x)))
            ((equal f '|COMMON-LISP::DENOMINATOR|) (list (denominator x)))
            ((equal f '|COMMON-LISP::EQUAL|) (list (equal x y)))
            ((equal f '|COMMON-LISP::IF|) (list (if x y (car (cdr (cdr args))))))
            ((equal f '|COMMON-LISP::IMAGPART|) (list (imagpart x)))
            ((equal f '|COMMON-LISP::INTEGERP|) (list (integerp x)))
            ((equal f '|ACL2::INTERN-IN-PACKAGE-OF-SYMBOL|)
             (list (if (and (stringp x) (symbolp y))
                       (intern-sym (coerce x 'list) (car (sym-parts y)) w)
                     nil)))
            ((equal f '|COMMON-LISP::NUMERATOR|) (list (numerator x)))
            ((equal f '|ACL2::PKG-IMPORTS|)
             (if (stringp x)
                 (let ((rec (trie-get (coerce x 'list) (w-pkgs w))))
                   (if (and rec (not (prec-hidden rec)))
                       (list (prec-imports rec))
                     nil))
               (list nil)))
            ((equal f '|ACL2::PKG-WITNESS|)
             (if (stringp x)
                 (let ((rec (trie-get (coerce x 'list) (w-pkgs w))))
                   (if (and rec (not (prec-hidden rec)))
                       (list (make-sym (coerce x 'list)
                                       (coerce "ACL2-PKG-WITNESS" 'list)))
                     nil))
               (list '|ACL2::ACL2-PKG-WITNESS|)))
            ((equal f '|COMMON-LISP::RATIONALP|) (list (rationalp x)))
            ((equal f '|COMMON-LISP::REALPART|) (list (realpart x)))
            ((equal f '|COMMON-LISP::STRINGP|) (list (stringp x)))
            ((equal f '|COMMON-LISP::SYMBOL-NAME|)
             (list (if (symbolp x) (coerce (sym-name x) 'string) "")))
            ((equal f '|ACL2::SYMBOL-PACKAGE-NAME|)
             (if (symbolp x)
                 (let* ((pkg (car (sym-parts x)))
                        (rec (trie-get pkg (w-pkgs w))))
                   (if (prec-hidden rec)
                       nil
                     (list (coerce pkg 'string))))
               (list "")))
            ((equal f '|COMMON-LISP::SYMBOLP|) (list (symbolp x)))
            (t nil))))
  :rule-classes nil
  :hints (("Goal" :expand ((prim-value f args w)))))

(defthm cg-step-substitute-logical-equation
  (equal (step-substitute data steps count room)
         (if (and (consp data) (consp (cdr data)) (consp (cdr (cdr data))))
             (let ((c1 (premise (car data) steps count))
                   (c2 (premise (car (cdr data)) steps count))
                   (i (car (cdr (cdr data))))
                   (js (cdr (cdr (cdr data)))))
               (if (and c1 c2 (consp (car c1)) (true-listp js))
                   (let ((eq (car (car c1))))
                     (if (and (consp eq) (equal (car eq) '|COMMON-LISP::EQUAL|)
                              (consp (cdr eq)) (consp (cdr (cdr eq)))
                              (equal (cdr (cdr (cdr eq))) nil)
                              (integerp i) (< 0 i) (not (< (len (car c2)) i)))
                       (let* ((a (car (cdr eq)))
                              (b (car (cdr (cdr eq))))
                              (new (replace-at (nth-elem i (car c2)) js a b)))
                         (if (equal new :fail)
                             nil
                           (let ((new-sizes
                                  (app (replace-nth i (cdr c2)
                                                    (+ (nth-elem i (cdr c2))
                                                       (- (size b) (size a))))
                                       (cdr (cdr c1)))))
                             (if (fits new-sizes room)
                                 (cons (app (replace-nth i (car c2) new) (cdr (car c1)))
                                       new-sizes)
                               nil))))
                       nil))
                 nil))
           nil))
  :rule-classes nil
  :hints (("Goal" :expand ((step-substitute data steps count room)))))

(defthm cg-step-beta-logical-equation
  (equal (step-beta data room w)
         (if (and (consp data) (equal (cdr data) nil))
             (let ((x (car data)))
               (if (and (term-p x :any nil w) (lambda-application-p x))
                   (let* ((formals (car (cdr (car x))))
                          (body (car (cdr (cdr (car x)))))
                          (actuals (cdr x))
                          (n (+ 5 (size x)
                                (subst-size body (pair-up formals (sizes actuals))))))
                     (if (fits (list n) room)
                         (cons (list (list '|COMMON-LISP::EQUAL| x
                                           (subst-term body (pair-up formals actuals))))
                               (list n))
                       nil))
                 nil))
           nil))
  :rule-classes nil
  :hints (("Goal" :expand ((step-beta data room w)))))

(defthm cg-unquote-all-logical-equation
  (equal (unquote-all xs)
         (if (consp xs)
             (cons (car (cdr (car xs))) (unquote-all (cdr xs)))
           nil))
  :rule-classes nil
  :hints (("Goal" :expand ((unquote-all xs)))))

(defthm cg-induct-sizes-logical-equation
  (equal (induct-sizes phi m ss)
         (if (consp ss)
             (let ((sa (subst-size-alist (car ss))))
               (cons (+ 20 (subst-size m sa) (size m) (subst-size phi sa))
                     (induct-sizes phi m (cdr ss))))
           nil))
  :rule-classes nil
  :hints (("Goal" :expand ((induct-sizes phi m ss)))))

(defthm cg-first-name-logical-equation
  (equal (first-name line)
         (let ((word (car line))
               (data (cdr line)))
           (cond ((equal word :define) (car (car (cdr data))))
                 ((equal word :constrain) (car (car (car data))))
                 (t (car data)))))
  :rule-classes nil
  :hints (("Goal" :expand ((first-name line)))))

(defthm cg-call-clause-logical-equation
  (equal (call-clause x rl rs st ss ctx)
         (let* ((fn (cdr (pair-of (car x) (car ctx))))
                (formals (car fn))
                (mj (car (cdr fn)))
                (mj2 (subst-term mj (pair-up formals (subst-terms (cdr x) st))))
                (size (subst-size mj (pair-up formals (subst-sizes (cdr x) ss)))))
           (cons (rev-onto rl (list (list '|ACL2::O<| mj2 (car (cdr (cdr ctx))))))
                 (rev-onto rs (list (+ 5 size (car (cdr (cdr (cdr ctx))))))))))
  :rule-classes nil
  :hints (("Goal" :expand ((call-clause x rl rs st ss ctx)))))

(defthm cg-walk-logical-equation
  (equal (walk x rl rs st ss ctx acc)
         (if (consp x)
              (let ((ext (car (cdr ctx))))
                (if (equal (car x) '|COMMON-LISP::QUOTE|)
                    acc
                  (if (consp (car x))
                      (let ((acc (if (lambdas-extend-p ext)
                                     (walk-list (cdr x) rl rs st ss ctx acc)
                                   (record-list (cdr x) rl rs st ss ctx acc)))
                            (formals (car (cdr (car x)))))
                        (walk (car (cdr (cdr (car x)))) rl rs
                              (pair-up formals (subst-terms (cdr x) st))
                              (pair-up formals (subst-sizes (cdr x) ss))
                              ctx acc))
                    (if (equal (car x) '|COMMON-LISP::IF|)
                        (let* ((a (car (cdr x)))
                               (acc (if (extends-p '|COMMON-LISP::IF| ext)
                                        (walk a rl rs st ss ctx acc)
                                      (record a rl rs st ss ctx acc)))
                               (a2 (subst-term a st))
                               (n (subst-size a ss)))
                          (walk (car (cdr (cdr (cdr x))))
                                (cons a2 rl) (cons n rs) st ss ctx
                                (walk (car (cdr (cdr x)))
                                      (cons (list '|COMMON-LISP::NOT| a2) rl)
                                      (cons (+ 4 n) rs) st ss ctx acc)))
                      (if (mbe-p x)
                          (walk (car (cdr (cdr (cdr x)))) rl rs st ss ctx acc)
                        (if (extends-p (car x) ext)
                            (walk-list (cdr x) rl rs st ss ctx
                                       (record-call-if x rl rs st ss ctx acc))
                          (record x rl rs st ss ctx acc)))))))
            acc))
  :rule-classes nil
  :hints (("Goal" :expand ((walk x rl rs st ss ctx acc)))))

(defthm cg-record-logical-equation
  (equal (record x rl rs st ss ctx acc)
         (if (consp x)
              (if (equal (car x) '|COMMON-LISP::QUOTE|)
                  acc
                (if (consp (car x))
                    (let ((formals (car (cdr (car x)))))
                      (record (car (cdr (cdr (car x)))) rl rs
                              (pair-up formals (subst-terms (cdr x) st))
                              (pair-up formals (subst-sizes (cdr x) ss))
                              ctx
                              (record-list (cdr x) rl rs st ss ctx acc)))
                  (if (mbe-p x)
                      (record (car (cdr (cdr (cdr x)))) rl rs st ss ctx acc)
                    (record-list (cdr x) rl rs st ss ctx
                                 (record-call-if x rl rs st ss ctx acc)))))
            acc))
  :rule-classes nil
  :hints (("Goal" :expand ((record x rl rs st ss ctx acc)))))

; On a successful read, every line has the shape required by ground-line.
(defun cg-ground-lines-world (lines w)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp lines)
      (let ((line (parse-line (car lines) *ground-words* (w-pkgs w))))
        (if line
            (cg-ground-lines-world (cdr lines) (ground-line line w))
          :bad))
    w))

(defthm cg-load-ground-on-success
  (implies (not (equal (load-ground lines w) :bad))
           (equal (load-ground lines w) (cg-ground-lines-world lines w)))
  :rule-classes nil
  :hints (("Goal" :induct (load-ground lines w)
           :in-theory (disable parse-line guard-ground-line-p ground-line))))
