(in-package "BOYMOO-MODEL")

(logic)

(defun core-program (definitions attachments visible-packages hidden-witnesses)
  (list definitions attachments visible-packages hidden-witnesses))

(defun core-definition (name program)
  (assoc-eq name (car program)))

(defun core-attachment (name program)
  (assoc-eq name (cadr program)))

(defun core-visible-package-p (name program)
  (or (member-equal name '("COMMON-LISP" "KEYWORD" "ACL2"
                          "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL"))
      (member-equal name (caddr program))))

(defun core-hidden-symbol-p (x program)
  (and (symbolp x)
       (cadddr program)
       (member-eq (acl2::intern-in-package-of-symbol "ACL2-PKG-WITNESS" x)
                  (cadddr program))))

(defun core-value (datum)
  (cons :value datum))

(defun core-value-p (result)
  (eq (car result) :value))

(defun core-datum (result)
  (cdr result))

(defund core-primitive (name args program)
  (let ((x (car args))
        (y (cadr args)))
    (case name
      (acl2-numberp (core-value (acl2-numberp x)))
      (acl2::bad-atom<= (core-value (acl2::bad-atom<= x y)))
      (acl2::binary-* (core-value (acl2::binary-* x y)))
      (acl2::binary-+ (core-value (acl2::binary-+ x y)))
      (acl2::unary-- (core-value (acl2::unary-- x)))
      (acl2::unary-/ (core-value (acl2::unary-/ x)))
      (< (core-value (< x y)))
      (car (core-value (car x)))
      (cdr (core-value (cdr x)))
      (char-code (core-value (char-code x)))
      (characterp (core-value (characterp x)))
      (code-char (core-value (code-char x)))
      (complex (core-value (complex x y)))
      (complex-rationalp (core-value (complex-rationalp x)))
      (coerce (core-value (coerce x y)))
      (cons (core-value (cons x y)))
      (consp (core-value (consp x)))
      (denominator (core-value (denominator x)))
      (equal (core-value (equal x y)))
      (if (core-value (if x y (caddr args))))
      (imagpart (core-value (imagpart x)))
      (integerp (core-value (integerp x)))
      (acl2::intern-in-package-of-symbol
       (core-value (acl2::intern-in-package-of-symbol x y)))
      (numerator (core-value (numerator x)))
      (acl2::pkg-imports
       (if (and (stringp x) (not (core-visible-package-p x program)))
           :no-value
         (core-value (acl2::pkg-imports x))))
      (acl2::pkg-witness
       (if (and (stringp x) (not (core-visible-package-p x program)))
           :no-value
         (core-value (acl2::pkg-witness x))))
      (rationalp (core-value (rationalp x)))
      (realpart (core-value (realpart x)))
      (stringp (core-value (stringp x)))
      (symbol-name (core-value (symbol-name x)))
      (acl2::symbol-package-name
       (if (core-hidden-symbol-p x program)
           :no-value
         (core-value (acl2::symbol-package-name x))))
      (symbolp (core-value (symbolp x)))
      (otherwise nil))))

(defund core-ash (i count)
  (if (equal (ifix i) 0) 0 (ash i count)))

(local
 (defthm core-ash-of-zero
   (implies (equal (ifix i) 0)
            (equal (ash i count) 0))
   :hints (("Goal" :in-theory (enable ash)))))

(defthm core-ash-is-ash
  (equal (core-ash i count) (ash i count))
  :hints (("Goal" :in-theory (enable core-ash))))

(defund core-nthcdr (n x)
  (declare (xargs :measure (acl2-count x)))
  (cond ((zp n) x)
        ((consp x) (core-nthcdr (1- n) (cdr x)))
        (t nil)))

(local
 (defthm core-nthcdr-of-atom
   (implies (and (not (consp x)) (not (zp n)))
            (equal (nthcdr n x) nil))
   :hints (("Goal" :induct (nthcdr n x)))))

(local
 (defthm core-nthcdr-is-nthcdr
   (equal (core-nthcdr n x) (nthcdr n x))
   :hints (("Goal"
            :induct (core-nthcdr n x)
            :in-theory (enable core-nthcdr)))))

(defund core-subseq (seq start end)
  (let* ((string (stringp seq))
         (elements (if string (coerce seq 'list) seq))
         (limit (or end (len elements)))
         (result (take (- limit start) (core-nthcdr start elements))))
    (if string (coerce result 'string) result)))

(defthm core-subseq-is-subseq
  (equal (core-subseq seq start end) (subseq seq start end))
  :hints (("Goal"
           :in-theory (enable core-subseq subseq acl2::subseq-list length))))

(defund core-prelude (name args)
  (case name
    (ash (core-value (core-ash (car args) (cadr args))))
    (acl2::binary-logxor
     (core-value (acl2::binary-logxor (car args) (cadr args))))
    (length (core-value (length (car args))))
    (char (core-value (char (car args) (cadr args))))
    (subseq (core-value (core-subseq (car args) (cadr args) (caddr args))))
    (otherwise nil)))

(defun core-mbe-call-p (term)
  (and (eq (car term) 'acl2::return-last)
       (equal (cadr term) '(quote acl2::mbe1-raw))
       (consp (cdddr term))
       (null (cddddr term))))

(defund core-eval-step (kind input env program fuel)
  (declare (xargs :measure (nfix fuel)
                  :ruler-extenders :all
                  :verify-guards nil))
  (if (zp fuel)
      :out-of-fuel
    (let ((next (1- fuel)))
      (case kind
        (:term
         (cond
          ((symbolp input)
           (let ((binding (assoc-eq input env)))
             (if binding (core-value (cdr binding)) :no-value)))
          ((eq (car input) 'quote) (core-value (cadr input)))
          ((eq (car input) 'if)
           (let ((test (core-eval-step :term (cadr input) env program next)))
             (if (core-value-p test)
                 (core-eval-step :term
                                 (if (core-datum test)
                                     (caddr input)
                                   (cadddr input))
                                 env program next)
               test)))
          ((core-mbe-call-p input)
           (core-eval-step :term (cadddr input) env program next))
          (t
           (let ((args (core-eval-step :terms (cdr input) env program next))
                 (head (car input)))
             (cond ((not (core-value-p args)) args)
                   ((consp head)
                    (core-eval-step :term (caddr head)
                                    (pairlis$ (cadr head) (core-datum args))
                                    program next))
                   (t (core-eval-step :call head (core-datum args)
                                      program next)))))))
        (:terms
         (if (atom input)
             (core-value nil)
           (let ((first (core-eval-step :term (car input) env program next)))
             (if (core-value-p first)
                 (let ((rest (core-eval-step :terms (cdr input)
                                             env program next)))
                   (if (core-value-p rest)
                       (core-value (cons (core-datum first) (core-datum rest)))
                     rest))
               first))))
        (:call
         (or (core-primitive input env program)
             (let ((attachment (core-attachment input program)))
               (if attachment
                   (core-eval-step :call (cadr attachment) env program next)
                 (or (core-prelude input env)
                     (let ((definition (core-definition input program)))
                       (if definition
                           (core-eval-step :term (caddr definition)
                                           (pairlis$ (cadr definition) env)
                                           program next)
                         :no-value)))))))
        (otherwise :no-value)))))

(defun core-eval (term env program fuel)
  (core-eval-step :term term env program fuel))

(defun core-eval-args (terms env program fuel)
  (core-eval-step :terms terms env program fuel))

(defun core-call (name args program fuel)
  (core-eval-step :call name args program fuel))

(defthmd core-eval-step-more-fuel
  (implies (not (eq (core-eval-step kind input env program fuel)
                    :out-of-fuel))
           (equal (core-eval-step kind input env program
                                  (+ (nfix extra) (nfix fuel)))
                  (core-eval-step kind input env program fuel)))
  :hints (("Goal"
           :induct (core-eval-step kind input env program fuel)
           :in-theory (enable core-eval-step))))

(local
 (defthmd core-add-fuel-difference
   (implies (and (natp fuel) (natp more) (<= fuel more))
            (equal (+ (nfix (- more fuel)) fuel) more))))

(defthmd core-eval-more-fuel
  (implies (and (natp fuel)
                (natp more)
                (<= fuel more)
                (not (equal (core-eval term env program fuel) :out-of-fuel)))
           (equal (core-eval term env program more)
                  (core-eval term env program fuel)))
  :hints (("Goal" :use (core-add-fuel-difference
                        (:instance core-eval-step-more-fuel
                                   (kind :term) (input term)
                                   (extra (- more fuel)))))))

(defthmd core-call-more-fuel
  (implies (and (natp fuel)
                (natp more)
                (<= fuel more)
                (not (equal (core-call name args program fuel) :out-of-fuel)))
           (equal (core-call name args program more)
                  (core-call name args program fuel)))
  :hints (("Goal" :use (core-add-fuel-difference
                        (:instance core-eval-step-more-fuel
                                   (kind :call) (input name) (env args)
                                   (extra (- more fuel)))))))

(defthm core-call-of-prelude
  (implies (and (not (zp fuel))
                (not (core-attachment name program))
                (core-prelude name args))
           (equal (core-call name args program fuel)
                  (core-prelude name args)))
  :hints (("Goal" :in-theory
           (enable core-eval-step core-prelude core-primitive))))

(defthm core-prelude-values
  (and (equal (core-prelude 'ash (list x y))
              (core-value (ash x y)))
       (equal (core-prelude 'acl2::binary-logxor (list x y))
              (core-value (acl2::binary-logxor x y)))
       (equal (core-prelude 'length (list x))
              (core-value (length x)))
       (equal (core-prelude 'char (list x y))
              (core-value (char x y)))
       (equal (core-prelude 'subseq (list x y z))
              (core-value (subseq x y z))))
  :hints (("Goal" :in-theory (enable core-prelude))))

(defthm core-defined-call-result
  (let ((definition (core-definition name program)))
    (implies (and (not (zp fuel))
                  (not (core-primitive name args program))
                  (not (core-attachment name program))
                  (not (core-prelude name args))
                  definition)
             (equal (core-call name args program fuel)
                    (core-eval (caddr definition)
                               (pairlis$ (cadr definition) args)
                               program (1- fuel)))))
  :hints (("Goal"
           :expand ((core-eval-step :call name args program fuel)))))

(defthm core-tail-call-result
  (let ((args (core-eval-args terms env program fuel)))
    (implies (and (natp fuel)
                  (symbolp name)
                  (not (member-eq name '(quote if)))
                  (not (core-mbe-call-p (cons name terms)))
                  (core-value-p args))
             (equal (core-eval (cons name terms) env program (1+ fuel))
                    (core-call name (core-datum args) program fuel))))
  :hints (("Goal" :expand
           ((core-eval-step :term (cons name terms) env program (1+ fuel))))))
