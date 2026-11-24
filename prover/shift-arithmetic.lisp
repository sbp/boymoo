(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *shift-arithmetic-ash* (proof-cl "ASH"))
(defconst *shift-arithmetic-expt* (proof-cl "EXPT"))
(defconst *shift-arithmetic-fix* (proof-sym "FIX" "ACL2"))
(defconst *shift-arithmetic-zip* (proof-sym "ZIP" "ACL2"))
(defconst *shift-arithmetic-two* (proof-quote 2))

(defun shift-arithmetic-inverse-power-step (lib count definitions half value)
  (quotient-proofs-let*
   ((opened (quotient-proofs-proof-call proof-proof-unfold lib
                                       (list *shift-arithmetic-expt* *shift-arithmetic-two*
                                             (proof-quote (- count)))))
    (first (proof-step-first opened))
    (simplified (quotient-proofs-proof-call proof-proof-simplify lib (caddr first) nil definitions))
    (proof (quotient-proofs-proof-call proof-proof-chain lib opened (list simplified)))
    (proof (quotient-proofs-proof-call proof-proof-rewrite lib proof half '(1 2 1)))
    (proof (quotient-proofs-proof-call proof-proof-rewrite lib proof value '(1 2 2)))
    (first (proof-step-first proof))
    (computed (quotient-proofs-proof-call proof-proof-compute lib (caddr first)
                                         (list "ratio" 1 (expt 2 count)))))
   (quotient-proofs-proof-call proof-proof-chain lib proof (list computed))))

(defun shift-arithmetic-inverse-power-loop (remaining lib count definitions half value)
  (declare (xargs :measure (nfix remaining)))
  (if (or (zp remaining) (failure-p value))
      value
    (shift-arithmetic-inverse-power-loop
     (1- remaining) lib (1+ count) definitions half
     (shift-arithmetic-inverse-power-step lib count definitions half value))))

(defun shift-arithmetic-inverse-power (lib shifts)
  (quotient-proofs-let*
   ((definitions (list *shift-arithmetic-zip* *shift-arithmetic-fix* *subtraction-numeric-equal*))
    (zero (quotient-proofs-proof-call proof-proof-unfold lib
                                     (list *shift-arithmetic-expt* *shift-arithmetic-two*
                                           *proof-zero*)))
    (first (proof-step-first zero))
    (simplified (quotient-proofs-proof-call proof-proof-simplify lib (caddr first) nil definitions))
    (value (quotient-proofs-proof-call proof-proof-chain lib zero (list simplified)))
    (half (quotient-proofs-proof-call proof-proof-compute lib
                                     (list *quotient-proofs-reciprocal* *shift-arithmetic-two*)
                                     '("ratio" 1 2))))
   (shift-arithmetic-inverse-power-loop shifts lib 1 definitions half value)))

(defun shift-arithmetic-unscaled-floor (lib term integral shifts radix)
  (if (/= (len term) 3)
      (proof-list-of-length term 3)
    (let ((value (cadr term)))
      (quotient-proofs-let*
       ((equation (quotient-proofs-proof-call proof-proof-unfold lib term))
        (ifix (quotient-proofs-proof-call proof-proof-simplify lib (list *subtraction-ifix* value)
                                        (list integral) (list *subtraction-ifix*)))
        (equation (quotient-proofs-proof-call proof-proof-rewrite lib equation ifix '(1 2 1 1)))
        (power (shift-arithmetic-inverse-power lib shifts))
        (power-first (proof-step-first power))
        (reciprocal (quotient-proofs-proof-call proof-proof-compute lib
                                              (list *quotient-proofs-reciprocal* radix)
                                              (cadr (caddr power-first))))
        (reciprocal (quotient-proofs-proof-call proof-proof-symmetric lib reciprocal))
        (power (quotient-proofs-proof-call proof-proof-chain lib power (list reciprocal)))
        (equation (quotient-proofs-proof-call proof-proof-rewrite lib equation power '(1 2 1 2)))
        (equation (quotient-proofs-proof-call proof-proof-tidy lib equation))
        (scaled (product-arithmetic-product value (list *quotient-proofs-reciprocal* radix)))
        (floor (quotient-proofs-proof-call proof-proof-unfold lib
                                          (list *quotient-proofs-floor* scaled *proof-one*)))
        (closure (library-library-axiom lib "CLOSURE" (cdr scaled)))
        (closures (quotient-proofs-proof-call proof-proof-conjunct lib closure))
        (numeric (quotient-proofs-proof-call proof-proof-conjunct lib (cadr closures)))
        (unity-law (library-library-axiom lib "UNICITY-OF-1" (list scaled)))
        (fixed (quotient-proofs-proof-call proof-proof-simplify lib (list *shift-arithmetic-fix* scaled)
                                         (list (car numeric)) (list *shift-arithmetic-fix*)))
        (identity (quotient-proofs-proof-call proof-proof-chain lib unity-law (list fixed)))
        (unity (quotient-proofs-proof-call proof-proof-compute lib
                                          (list *quotient-proofs-reciprocal* *proof-one*) 1))
        (multiplied (quotient-proofs-proof-call proof-proof-reflexive lib
                                              (product-arithmetic-product
                                               scaled (list *quotient-proofs-reciprocal* *proof-one*))))
        (multiplied (quotient-proofs-proof-call proof-proof-rewrite lib multiplied unity '(1 2 2)))
        (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list scaled *proof-one*)))
        (divided (quotient-proofs-proof-call proof-proof-chain lib multiplied (list commute identity)))
        (floor (quotient-proofs-proof-call proof-proof-rewrite lib floor divided '(1 2 1)))
        (floor (quotient-proofs-proof-call proof-proof-tidy lib floor))
        (unscaled (quotient-proofs-proof-call proof-proof-unfold lib
                                             (list *quotient-proofs-floor* value radix)))
        (reverse (quotient-proofs-proof-call proof-proof-symmetric lib unscaled)))
       (quotient-proofs-proof-call proof-proof-chain lib equation (list floor reverse))))))

(defun shift-arithmetic-shift-decrease-proof (lib parent rulers shift opened shifts)
  (quotient-proofs-let*
   ((value (cadr parent))
    (radix (proof-quote (expt 2 shifts)))
    ((hypotheses lib) (quotient-proofs-dividend-rulers-with-rulers lib value radix rulers))
    (rulers (cdr hypotheses)))
   (if (not (car hypotheses))
       (cons (list nil rulers) lib)
     (quotient-proofs-let*
      ((floor (list *proof-ordinal-less*
                    (list *library-count* (list *quotient-proofs-floor* value radix))
                    parent))
       ((result lib) (quotient-proofs-quotient-decrease-with-rulers lib floor rulers))
       (proof (car result))
       (rulers (cadr result)))
      (if (not proof)
          (cons (list nil rulers) lib)
        (quotient-proofs-let*
         ((identity (shift-arithmetic-unscaled-floor lib shift (caar hypotheses) shifts radix))
          (identity (if opened
                        (quotient-proofs-proof-call proof-proof-chain lib opened (list identity))
                      identity))
          (reverse (quotient-proofs-proof-call proof-proof-symmetric lib identity))
          (proof (quotient-proofs-proof-call proof-proof-rewrite lib proof reverse '(1 1 1)))
          (proof (quotient-proofs-proof-call proof-proof-tidy lib proof)))
         (cons (list proof rulers) lib)))))))

(defun shift-arithmetic-shift-decrease-term (lib term parent rulers)
  (cond
   ((not (proof-compound term)) (cons (list nil rulers) lib))
   ((endp term) '(:failure "failure" ""))
   ((or (proof-is-call term *shift-arithmetic-ash*)
        (proof-compound (car term))
        (member-equal (car term) *countdowns-counter-wrappers*))
    (quotient-proofs-let*
     ((definitions (quotient-proofs-counter-definitions lib *countdowns-counter-wrappers*))
      (opened (quotient-proofs-proof-call proof-proof-simplify lib term nil definitions))
      (shift (if opened
                 (quotient-proofs-let* ((first (proof-step-first opened))) (caddr first))
               term)))
     (cond
      ((not (proof-is-call shift *shift-arithmetic-ash*)) (cons (list nil rulers) lib))
      ((or (endp (cdr shift)) (endp (cdr parent))) '(:failure "failure" ""))
      ((not (equal (cadr shift) (cadr parent))) (cons (list nil rulers) lib))
      ((endp (cddr shift)) '(:failure "failure" ""))
      (t
       (let ((amount (caddr shift)))
         (cond
          ((not (proof-is-call amount *proof-quote*)) (cons (list nil rulers) lib))
          ((endp (cdr amount)) '(:failure "failure" ""))
          ((and (integerp (cadr amount)) (<= -64 (cadr amount)) (< (cadr amount) 0))
           (shift-arithmetic-shift-decrease-proof lib parent rulers shift opened (- (cadr amount))))
          (t (cons (list nil rulers) lib))))))))
   (t (cons (list nil rulers) lib))))

(defun shift-arithmetic-shift-decrease-with-rulers (lib goal rulers)
  (quotient-proofs-let*
   ((goal (proof-list-of-length goal 3)))
   (let ((child (cadr goal))
         (parent (caddr goal)))
     (if (and (proof-is-call child *library-count*) (proof-is-call parent *library-count*))
         (quotient-proofs-let*
          ((term (proof-term-at child 1)))
          (shift-arithmetic-shift-decrease-term lib term parent rulers))
       (cons (list nil rulers) lib)))))

(defun shift-arithmetic-shift-decrease (lib goal rulers)
  (quotient-proofs-let*
   (((result lib) (shift-arithmetic-shift-decrease-with-rulers lib goal rulers)))
   (cons (car result) lib)))
