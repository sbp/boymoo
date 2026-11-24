(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-symbolic-order-string-lt* (proof-cl "STRING<"))
(defconst *h3-symbolic-order-string-le* (proof-cl "STRING<="))
(defconst *h3-symbolic-order-coerce* (proof-cl "COERCE"))
(defconst *h3-symbolic-order-symbol-lt* (proof-sym "SYMBOL<" "ACL2"))
(defconst *h3-symbolic-order-iff* (proof-sym "IFF" "ACL2"))
(defconst *h3-symbolic-order-list* (proof-quote (proof-cl "LIST")))

(defun h3-symbolic-order-guarded (lib fact evidence)
  (let ((proof (library-library-proof lib))
        (search (h3-rewrite-search-init lib nil nil nil 150 nil)))
    (proof-with-checked-results
        ((literal (proof-step-first fact))
         (test (proof-term-at literal 1))
         (guard (car (h3-rewrite-search-prove search test evidence))))
      (proof-proof-modus-ponens proof fact guard))))

(defun h3-symbolic-order-char-lists (lib terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((step (proof-proof-fact
                (library-library-proof lib) (proof-sym "CHARACTER-LISTP-COERCE" "ACL2")
                (list (list (proof-sym "STR" "ACL2") (car terms)))))
         (rest (h3-symbolic-order-char-lists lib (cdr terms))))
      (cons step rest))))

(defun h3-symbolic-order-unsigned-list-comparison (lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (head (proof-term-at literal 0))
         (negative (equal head *proof-not*))
         (call (if negative (proof-term-at literal 1) literal))
         (opened (proof-proof-unfold proof call))
         (step (proof-proof-rewrite proof step opened (if negative '(1 1) '(1)))))
      (proof-proof-tidy proof step))))

(defun h3-symbolic-order-eqlable-lists (lib lists)
  (if (endp lists)
      nil
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((literal (proof-step-first (car lists)))
           (value (proof-term-at literal 1))
           (axiom (library-library-axiom
                   lib "CHARACTER-LISTP-FORWARD-TO-EQLABLE-LISTP" (list value)))
           (step (proof-proof-modus-ponens proof axiom (car lists)))
           (rest (h3-symbolic-order-eqlable-lists lib (cdr lists))))
        (cons step rest)))))

(defun h3-symbolic-order-step-arguments (steps)
  (if (endp steps)
      nil
    (proof-with-checked-results
        ((literal (proof-step-first (car steps)))
         (argument (proof-term-at literal 1))
         (rest (h3-symbolic-order-step-arguments (cdr steps))))
      (cons argument rest))))

(defun h3-symbolic-order-pair-operands (literal)
  (if (integerp literal)
      '(:failure "MalformedTacticInput" "")
    (proof-list-of-length (cdr literal) 2)))

(defun h3-symbolic-order-string-asymmetric (lib forward)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first forward))
         (operands (h3-symbolic-order-pair-operands literal))
         (a (car operands))
         (b (cadr operands))
         (lists (h3-symbolic-order-char-lists lib (list a b)))
         (eqlable (h3-symbolic-order-eqlable-lists lib lists))
         (actuals (h3-symbolic-order-step-arguments lists))
         (theorem (proof-proof-fact
                   proof (proof-sym "STRING<-L-ASYMMETRIC" "ACL2")
                   (list (list (proof-sym "X1" "ACL2") (car actuals))
                         (list (proof-sym "X2" "ACL2") (cadr actuals))
                         (list (proof-sym "I" "ACL2") *proof-zero*))))
         (zero-int (library-library-type-of lib *proof-zero* nil))
         (comparison (h3-symbolic-order-unsigned-list-comparison lib forward))
         (no-reverse (h3-symbolic-order-guarded lib theorem
                                                (append eqlable (list zero-int comparison))))
         (opened (proof-proof-unfold proof (list *h3-symbolic-order-string-lt* b a))))
      (library-library-transport-argument lib no-reverse opened 1))))

(defun h3-symbolic-order-asymmetry (lib forward)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first forward))
         (parts (proof-list-of-length literal 3)))
      (if (equal (car parts) *h3-symbolic-order-string-lt*)
          (h3-symbolic-order-string-asymmetric lib forward)
        (proof-with-checked-results
            ((theorem (proof-proof-fact
                       proof (proof-sym "SYMBOL<-ASYMMETRIC" "ACL2")
                       (list (list (proof-sym "SYM1" "ACL2") (cadr parts))
                             (list (proof-sym "SYM2" "ACL2") (caddr parts))))))
          (proof-proof-modus-ponens proof theorem forward))))))

(defun h3-symbolic-order-string-trichotomy (lib a b not-forward)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((lists (h3-symbolic-order-char-lists lib (list a b)))
         (variables (list *library-x* *library-y*
                          (proof-sym "I" "ACL2") (proof-sym "J" "ACL2")))
         (actuals (h3-symbolic-order-step-arguments lists))
         (theorem (proof-proof-fact
                   proof (proof-sym "STRING<-L-TRICHOTOMY" "ACL2")
                   (seq-zip variables (append actuals (list *proof-zero* *proof-zero*)))))
         (zero-int (library-library-type-of lib *proof-zero* nil))
         (comparison (h3-symbolic-order-unsigned-list-comparison lib not-forward)))
      (h3-symbolic-order-guarded lib theorem (append lists (list zero-int comparison))))))

(defun h3-symbolic-order-coerce-inverses (lib terms types)
  (if (or (endp terms) (endp types))
      nil
    (proof-with-checked-results
        ((theorem (library-library-axiom lib "COERCE-INVERSE-2" (list (car terms))))
         (step (proof-proof-modus-ponens (library-library-proof lib) theorem (car types)))
         (rest (h3-symbolic-order-coerce-inverses lib (cdr terms) (cdr types))))
      (cons step rest))))

(defun h3-symbolic-order-coerce-injectivity (lib a b types equal-lists)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((steps (h3-symbolic-order-coerce-inverses lib (list a b) types))
         (steps (proof-list-of-length steps 2))
         (reversed (proof-proof-symmetric proof (car steps)))
         (start (proof-proof-rewrite proof reversed equal-lists '(1 2 1))))
      (proof-proof-chain proof start (list (cadr steps))))))

(defun h3-symbolic-order-iff-left (lib fact right-proof)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first fact))
         (parts (h3-symbolic-order-pair-operands literal))
         (left (car parts))
         (right (cadr parts))
         (proved (proof-step-first right-proof)))
      (if (not (equal proved right))
          '(:failure "ProofMismatch" "")
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof literal))
             (opened (proof-proof-rewrite proof fact opened '(1)))
             (no (proof-proof-assume proof left nil))
             (false-left (proof-proof-prove-if proof opened no))
             (selected (proof-proof-prove-if proof false-left right-proof)))
          (proof-proof-front proof selected left))))))

(defun h3-symbolic-order-iff-deny-right (lib fact denial)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first fact))
         (parts (h3-symbolic-order-pair-operands literal))
         (right (cadr parts))
         (opened (proof-proof-unfold proof literal))
         (opened (proof-proof-rewrite proof fact opened '(1)))
         (false-left (proof-proof-prove-if proof opened denial))
         (yes (proof-proof-assume proof right t))
         (selected (proof-proof-prove-if proof false-left yes)))
      (proof-proof-front proof selected (proof-neg right)))))

(defun h3-symbolic-order-antisymmetry (lib head a b types a-le-b b-le-a)
  (if (equal head *h3-symbolic-order-string-lt*)
      (proof-with-checked-results
          ((trichotomy (h3-symbolic-order-string-trichotomy lib a b b-le-a))
           (no-reverse (h3-symbolic-order-unsigned-list-comparison lib a-le-b))
           (denial (h3-symbolic-order-iff-deny-right lib trichotomy no-reverse))
           (equality (h3-rewrite-double-negation lib denial)))
        (h3-symbolic-order-coerce-injectivity lib a b types equality))
    (proof-with-checked-results
        ((theorem (library-library-axiom lib "SYMBOL<-TRICHOTOMY" (list a b)))
         (tri (h3-symbolic-order-guarded lib theorem (append types (list b-le-a))))
         (denial (h3-symbolic-order-iff-deny-right lib tri a-le-b)))
      (h3-rewrite-double-negation lib denial))))

(defun h3-symbolic-order-strict-transitive (lib head a b c types first second)
  (if (equal head *h3-symbolic-order-symbol-lt*)
      (proof-with-checked-results
          ((theorem (library-library-axiom lib "SYMBOL<-TRANSITIVE" (list a b c))))
        (h3-symbolic-order-guarded lib theorem (append types (list first second))))
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((lists (h3-symbolic-order-char-lists lib (list a b c)))
           (variables (list *library-x* *library-y* *library-z*
                            (proof-sym "I" "ACL2") (proof-sym "J" "ACL2")
                            (proof-sym "K" "ACL2")))
           (actuals (h3-symbolic-order-step-arguments lists))
           (theorem (proof-proof-fact
                     proof (proof-sym "STRING<-L-TRANSITIVE" "ACL2")
                     (seq-zip variables (append actuals (list *proof-zero* *proof-zero*
                                                             *proof-zero*)))))
           (first-list (h3-symbolic-order-unsigned-list-comparison lib first))
           (second-list (h3-symbolic-order-unsigned-list-comparison lib second))
           (zero-int (library-library-type-of lib *proof-zero* nil))
           (guarded (h3-symbolic-order-guarded
                     lib theorem (append lists (list zero-int first-list second-list))))
           (opened (proof-proof-unfold proof (list *h3-symbolic-order-string-lt* a c))))
        (proof-proof-transport proof guarded opened)))))

(defun h3-symbolic-order-transitivity (lib head a b c types left right)
  (let ((proof (library-library-proof lib))
        (first (list head a b))
        (second (list head b c)))
    (proof-with-checked-results
        ((yes-first (proof-proof-assume proof first t))
         (yes-second (proof-proof-assume proof second t))
         (joined (h3-symbolic-order-strict-transitive
                  lib head a b c types yes-first yes-second))
         (yes (h3-symbolic-order-asymmetry lib joined))
         (not-second (proof-proof-assume proof second nil))
         (equal-right (h3-symbolic-order-antisymmetry
                       lib head b c (cdr types) right not-second))
         (no (proof-proof-rewrite-first proof left equal-right))
         (yes (proof-proof-cases proof second yes no))
         (not-first (proof-proof-assume proof first nil))
         (equal-left (h3-symbolic-order-antisymmetry
                      lib head a b (seq-slice types 0 2) left not-first))
         (equal-left (proof-proof-symmetric proof equal-left))
         (no (proof-proof-rewrite-first proof right equal-left)))
      (proof-proof-cases proof first yes no))))

(defun h3-symbolic-order-boolean-string-order-prove (steps lib rules wanted)
  (let ((search (h3-rewrite-search-init lib (list *h3-symbolic-order-string-le* *proof-not*)
                                       nil rules 25 nil)))
    (car (h3-rewrite-search-prove search wanted steps))))

(defun h3-symbolic-order-boolean-string-order (lib types length-name)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((actuals (h3-symbolic-order-step-arguments (seq-slice types 0 3)))
         (actuals (proof-list-of-length actuals 2))
         (a (car actuals))
         (b (cadr actuals))
         (first (list *h3-symbolic-order-string-lt* a b))
         (reverse (list *h3-symbolic-order-string-lt* b a))
         (equal (proof-eq a b))
         (wanted (proof-eq (proof-ite (list *h3-symbolic-order-string-le* a b)
                                      *proof-true* *proof-false*)
                           (proof-neg reverse)))
         (names (list length-name (proof-sym "STRING<-IRREFLEXIVE" "ACL2")))
         (rules (h3-rewrite-rules-init lib names nil))
         (equal-proof (proof-proof-assume proof equal t))
         (same (h3-symbolic-order-boolean-string-order-prove
                (list equal-proof) lib rules wanted))
         (distinct (proof-proof-assume proof equal nil))
         (ascending (proof-proof-assume proof first t))
         (asymmetry (h3-symbolic-order-asymmetry lib ascending))
         (yes (h3-symbolic-order-boolean-string-order-prove
               (list distinct ascending asymmetry) lib rules wanted))
         (not-first (proof-proof-assume proof first nil))
         (trichotomy (h3-symbolic-order-string-trichotomy lib a b not-first))
         (equal-lists
          (proof-eq (list *h3-symbolic-order-coerce* a *h3-symbolic-order-list*)
                    (list *h3-symbolic-order-coerce* b *h3-symbolic-order-list*)))
         (equal-lists-proof (proof-proof-assume proof equal-lists t))
         (reconstructed (h3-symbolic-order-coerce-injectivity
                         lib a b types equal-lists-proof))
         (unequal-lists (proof-proof-cut proof reconstructed distinct))
         (unequal-lists (proof-proof-front proof unequal-lists (proof-neg equal-lists)))
         (reversed-call (proof-proof-unfold proof reverse))
         (descending (h3-symbolic-order-iff-left lib trichotomy unequal-lists))
         (descending (proof-proof-transport proof descending reversed-call))
         (no (h3-symbolic-order-boolean-string-order-prove
              (list distinct not-first descending) lib rules wanted))
         (ordered (proof-proof-cases proof first yes no)))
      (proof-proof-cases proof equal same ordered))))
