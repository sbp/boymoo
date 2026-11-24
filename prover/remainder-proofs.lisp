(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *remainder-proofs-mod* (proof-cl "MOD"))
(defconst *remainder-proofs-remainder-bounds* "RADIX-REMAINDER-BOUNDS")

(defun remainder-proofs-remainder-lemma (lib)
  (if (quotient-proofs-has-lemma lib *remainder-proofs-remainder-bounds*)
      lib
    (quotient-proofs-let*
     ((radix (quotient-proofs-radix-assumptions lib))
      (assumptions (car radix))
      (quotient (list *quotient-proofs-floor* *library-x* *library-y*))
      ((name lib) (quotient-proofs-radix-product-lemma lib *quotient-proofs-floor*))
      (bounds (library-library-cite lib name (list *library-x* *library-y*) assumptions))
      (parts (quotient-proofs-bound-parts lib bounds))
      (iq (library-library-cite lib "NATURAL-INTEGER" (list quotient) (list (car parts))))
      (types (list (car assumptions) (cadr assumptions) iq))
      (scaled (product-arithmetic-product *library-y* quotient))
      (remainder (library-diff *library-x* scaled))
      (subtraction (library-library-axiom lib "<-ON-OTHERS" (list *library-x* scaled)))
      (nonnegative (quotient-proofs-proof-call proof-proof-rewrite lib (cadr parts)
                                               subtraction '(1 1)))
      (nonnegative (quotient-proofs-proof-call proof-proof-tidy lib nonnegative))
      ((integral lib) (lemmas-slice-library-type-of lib remainder types))
      (natural (library-library-cite lib "NATURAL-FROM-BOUNDS" (list remainder)
                                     (list integral nonnegative)))
      ((successor lib) (quotient-proofs-product-successor lib *library-y* quotient types))
      (upper (quotient-proofs-proof-call proof-proof-rewrite lib (caddr parts) successor '(1 2)))
      (upper (quotient-proofs-proof-call proof-proof-tidy lib upper))
      (comparison (library-library-comparison lib *library-x* (library-plus *library-y* scaled)
                                               types))
      (gap (quotient-proofs-proof-call proof-proof-rewrite lib upper comparison '(1)))
      (gap (quotient-proofs-proof-call proof-proof-tidy lib gap))
      (strict (library-library-less-from-difference lib remainder *library-y* gap types))
      (statement (list *remainder-proofs-mod* *library-x* *library-y*))
      (equation (quotient-proofs-proof-call proof-proof-unfold lib statement))
      (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list quotient *library-y*)))
      (equation (quotient-proofs-proof-call proof-proof-rewrite lib equation commute '(1 2 2 1)))
      (equation (quotient-proofs-proof-call proof-proof-tidy lib equation))
      (template (product-arithmetic-conjunction
                 (list (list *library-natp* *proof-result*)
                       (library-lt *proof-result* *library-y*))))
      (result (product-arithmetic-conjoin lib (list natural strict)))
      (reverse-equation (quotient-proofs-proof-call proof-proof-symmetric lib equation))
      (result (quotient-proofs-proof-call proof-proof-rewrite-result lib result reverse-equation
                                         template *proof-result*))
      (first (proof-step-first result))
      (conditions (quotient-proofs-lemma-conditions assumptions)))
     (library-library-lemma lib *remainder-proofs-remainder-bounds* first result conditions))))

(defun remainder-proofs-premise-remainder (goal)
  (cond
   ((or (proof-is-call goal *library-natp*)
        (proof-is-call goal *proof-integerp*)
        (proof-is-call goal *proof-less*))
    (if (consp (cdr goal))
        (cadr goal)
      '(:failure "failure" "")))
   ((proof-is-call goal *proof-not*)
    (cond ((endp (cdr goal)) '(:failure "failure" ""))
          ((not (proof-is-call (cadr goal) *proof-less*)) nil)
          ((endp (cddr (cadr goal))) '(:failure "failure" ""))
          ((equal (caddr (cadr goal)) *proof-zero*) (cadr (cadr goal)))
          (t nil)))
   (t nil)))

(defun remainder-proofs-premise-integral (lib number known)
  (let ((integral (cdr (assoc-equal (library-integer number) known)))
        (natural (assoc-equal (list *library-natp* number) known)))
    (cond
     (integral (cons integral lib))
     (natural
      (quotient-proofs-let*
       ((integral (library-library-cite lib "NATURAL-INTEGER" (list number) (list (cdr natural)))))
       (cons integral lib)))
     (t
      (let* ((result (countdowns-type-of lib number (strip-cdrs known)))
             (integral (car result)))
        (cond ((terms-proof-fallback-p integral)
               (cons nil (cdr result)))
              ((failure-p integral) integral)
              (t result)))))))

(defun remainder-proofs-premise-bounds (lib goal remainder number divisor positive-number integral)
  (quotient-proofs-let*
   ((lib (remainder-proofs-remainder-lemma lib))
    (i-divisor (library-library-type-of lib divisor nil))
    (large-divisor (quotient-proofs-proof-call proof-proof-prove lib
                                              (library-lt *proof-one* divisor) nil nil))
    (bounds (library-library-cite lib *remainder-proofs-remainder-bounds* (list number divisor)
                                  (list integral i-divisor positive-number large-divisor)))
    (parts (quotient-proofs-proof-call proof-proof-conjunct lib bounds))
    (natural (car parts))
    (step (cond ((proof-is-call goal *proof-less*) (cadr parts))
                ((proof-is-call goal *proof-integerp*)
                 (library-library-cite lib "NATURAL-INTEGER" (list remainder) (list natural)))
                ((proof-is-call goal *proof-not*)
                 (library-library-cite lib "NATURAL-NONNEGATIVE" (list remainder) (list natural)))
                (t natural))))
   (cons step lib)))

(defun remainder-proofs-remainder-premise (lib goal known)
  (quotient-proofs-let*
   ((remainder (remainder-proofs-premise-remainder goal)))
   (cond
    ((not (proof-is-call remainder *remainder-proofs-mod*)) (cons nil lib))
    ((/= (len remainder) 3) (proof-list-of-length remainder 3))
    (t
     (let ((number (cadr remainder))
           (divisor (caddr remainder)))
       (cond
        ((not (proof-is-call divisor *proof-quote*)) (cons nil lib))
        ((endp (cdr divisor)) '(:failure "failure" ""))
        ((not (and (integerp (cadr divisor)) (<= 2 (cadr divisor)))) (cons nil lib))
        ((and (proof-is-call goal *proof-less*) (endp (cddr goal)))
         '(:failure "failure" ""))
        ((and (proof-is-call goal *proof-less*) (not (equal (caddr goal) divisor)))
         (cons nil lib))
        (t
         (quotient-proofs-let*
          ((positive (library-positive number))
           (positive-number (cdr (assoc-equal positive known)))
           (positive-number
            (cond (positive-number positive-number)
                  ((not (proof-is-call number *proof-quote*)) nil)
                  ((endp (cdr number)) '(:failure "failure" ""))
                  ((and (integerp (cadr number)) (< 0 (cadr number)))
                   (quotient-proofs-proof-call proof-proof-prove lib positive nil nil))
                  (t nil))))
          (if (not positive-number)
              (cons nil lib)
            (quotient-proofs-let*
             (((integral lib) (remainder-proofs-premise-integral lib number known)))
             (if integral
                 (remainder-proofs-premise-bounds lib goal remainder number divisor
                                                   positive-number integral)
               (cons nil lib))))))))))))
