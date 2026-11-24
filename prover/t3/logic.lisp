(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-logic-atom* (proof-cl "ATOM"))
(defconst *t3-logic-consp* *proof-consp*)
(defconst *t3-logic-endp* (proof-cl "ENDP"))
(defconst *t3-logic-length* (proof-cl "LENGTH"))
(defconst *t3-logic-the-check* (proof-sym "THE-CHECK" "ACL2"))
(defconst *t3-logic-zp* (proof-sym "ZP" "ACL2"))
(defconst *t3-logic-zpf* (proof-sym "ZPF" "ACL2"))
(defconst *t3-logic-wrappers* *t3-book-lemmas-wrappers*)
(defconst *t3-logic-reciprocal* *t3-book-lemmas-reciprocal*)
(defconst *t3-logic-ppr-predicates*
  (list (proof-sym "PPR-TUPLE-P" "ACL2") (proof-sym "PPR-TUPLE-LST-P" "ACL2")))
(defconst *t3-logic-legal-constantp* (proof-sym "LEGAL-CONSTANTP1" "ACL2"))
(defconst *t3-logic-natural-template* (list *library-natp* *proof-result*))

(defun t3-logic-rational-value (datum)
  (t3-book-lemmas-rational-value datum))

(defun t3-logic-rational-result (head values)
  (t3-book-lemmas-rational-result head values))

(defun t3-logic-libraryproofs-constant (lib term)
  (t3-book-lemmas-constant lib term))

(defun t3-logic-libraryproofs-for-book (lib)
  (library-library-with-proof lib
                              (proof-proof-with-kind (library-library-proof lib) :t3-book)))

(defun t3-logic-book-natural-p (lib term)
  (and (eq (proof-proof-kind (library-library-proof lib)) :t3-book)
       (or (proof-is-call term *library-nfix*)
           (proof-is-call term *t3-book-lemmas-exported-nfix*))))

(defun t3-logic-book-natural (lib term)
  (proof-with-checked-results ((step (library-library-cite lib "NFIX-NATURAL" (cdr term) nil)))
    (if (proof-is-call term *library-nfix*)
        step
      (proof-with-checked-results ((opened (library-library-cite lib "T3-EXPORTED-NFIX" (cdr term) nil)))
        (library-library-transport-argument lib step opened 1)))))

(defund t3-logic-libraryproofs-simplify (lib term evidence definitions)
  (t3-book-lemmas-simplify lib term evidence definitions))

(defun t3-logic-libraryproofs-simplify-first (lib step evidence definitions)
  (t3-book-lemmas-simplify-first lib step evidence definitions))

(defund t3-logic-libraryproofs-normalize (lib term evidence definitions)
  (t3-book-lemmas-normalize lib term evidence definitions))

(defund t3-logic-prove-plan (lib term evidence definitions)
  (let ((proof (library-library-proof lib)))
    (cond
     ((equal term *proof-true*) (proof-proof-prove proof term nil nil))
     (t
      (proof-with-checked-results ((premise (proof-find-evidence evidence (list term))))
        (if premise
            premise
          (proof-with-checked-results
              ((equality (t3-logic-libraryproofs-simplify lib term evidence definitions))
               (right (and equality (proof-rewritten-term equality))))
            (cond
             ((or (not equality) (equal right term)) (proof-prove-unproved-term term))
             ((equal right *proof-true*) (proof-proof-true-from-eq proof equality))
             (t (list :transport right equality))))))))))

(defun t3-logic-prove-visit (n lib term evidence definitions)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-logic-libraryproofs-prove")
    (let ((result (t3-logic-prove-plan lib term evidence definitions)))
      (if (eq (car result) :transport)
          (proof-with-checked-results
              ((step (t3-logic-prove-visit (1- n) lib (cadr result) evidence definitions)))
            (proof-proof-transport (library-library-proof lib) step (caddr result)))
        result))))

(defun t3-logic-libraryproofs-prove (lib term evidence definitions)
  (t3-logic-prove-visit 1000000 lib term evidence definitions))

(defund t3-logic-by-value-unfold (proof value)
  (cond ((not (proof-compound value)) nil)
        ((endp value) '(:failure "MissingProofInput" ""))
        ((member-equal (car value) *t3-logic-wrappers*) (proof-proof-unfold proof value))
        ((proof-compound (car value)) (proof-proof-beta proof value))
        (t nil)))

(defun t3-logic-by-value-leaves-visit (n proof value tests)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "t3-logic-libraryproofs-by-value-leaves"))
   ((proof-is-call value *proof-if*)
    (proof-with-checked-results
        ((branches (proof-list-of-length (cdr value) 3))
         (yes (t3-logic-by-value-leaves-visit
               (1- n) proof (cadr branches) (append tests (list (list (car branches) t)))))
         (no (t3-logic-by-value-leaves-visit
              (1- n) proof (caddr branches) (append tests (list (list (car branches) nil))))))
      (append yes no)))
   (t
    (proof-with-checked-results ((equality (t3-logic-by-value-unfold proof value)))
      (if equality
          (proof-with-checked-results ((opened (proof-rewritten-term equality)))
            (t3-logic-by-value-leaves-visit (1- n) proof opened tests))
        (list (list value tests)))))))

(defun t3-logic-libraryproofs-by-value-leaves (lib value tests)
  (t3-logic-by-value-leaves-visit 1000000 (library-library-proof lib) value tests))

(defun t3-logic-by-value-leaf (value tests leaf)
  (let ((entry (assoc-equal (list value tests) leaf)))
    (if entry
        (cdr entry)
      '(:failure "Unproved" ""))))

(defun t3-logic-by-value-check-leaf (step value template)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (target (proof-subst template (list (cons *proof-result* value)))))
    (if (equal literal target)
        step
      '(:failure "ProofMismatch" ""))))

(defun t3-logic-natural-gap (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof term))
         (body (proof-rewritten-term opened))
         (arg (proof-term-at body 1))
         (step (library-library-cite lib "NFIX-NATURAL" (list arg) nil)))
      (library-library-transport-argument lib step opened 1))))

(defun t3-logic-natural-default (lib term)
  (t3-logic-libraryproofs-prove lib (list *library-natp* term) nil
                               (list *library-natp* *proof-not*)))

(mutual-recursion
 (defun t3-logic-natural-visit (n lib term)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t3-logic-libraryproofs-natural"))
    ((t3-logic-book-natural-p lib term) (t3-logic-book-natural lib term))
    ((proof-is-call term *t3-logic-length*)
     (library-library-cite lib "T3-LENGTH-NATURAL" (cdr term) nil))
    ((proof-is-call term *library-gap*) (t3-logic-natural-gap lib term))
    ((proof-is-call term *proof-if*)
     (t3-logic-by-value-visit (1- n) lib term *t3-logic-natural-template* nil nil t))
    ((proof-is-call term *proof-times*)
     (proof-with-checked-results ((multiplier (proof-term-at term 1)))
       (if (equal multiplier (proof-quote 2))
           (proof-with-checked-results
               ((arg (proof-term-at term 2))
                (step (t3-logic-natural-visit (1- n) lib arg)))
             (library-library-cite lib "T3-NATURAL-DOUBLE" (cddr term) (list step)))
         (t3-logic-natural-default lib term))))
    ((proof-is-call term *library-count*)
     (library-library-cite lib "COUNT-NATURAL" (cdr term) nil))
    ((proof-is-call term *library-len*)
     (library-library-cite lib "LEN-NATURAL" (cdr term) nil))
    ((proof-is-call term *proof-plus*)
     (proof-with-checked-results ((steps (t3-logic-natural-arguments (1- n) lib (cdr term))))
       (library-library-cite lib "NATURAL-SUM" (cdr term) steps)))
    (t (t3-logic-natural-default lib term))))

 (defun t3-logic-natural-arguments (n lib args)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "t3-logic-libraryproofs-natural"))
         ((endp args) nil)
         (t (proof-with-checked-results
                ((step (t3-logic-natural-visit (1- n) lib (car args)))
                 (rest (t3-logic-natural-arguments (1- n) lib (cdr args))))
              (cons step rest)))))

 (defun t3-logic-by-value-visit (n lib value template leaf tests natural)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof lib)))
     (cond
      ((zp n) '(:failure "Fuel" "t3-logic-libraryproofs-by-value"))
      ((proof-is-call value *proof-if*)
       (proof-with-checked-results
           ((branches (proof-list-of-length (cdr value) 3))
            (yes (t3-logic-by-value-visit (1- n) lib (cadr branches) template leaf
                                         (append tests (list (list (car branches) t))) natural))
            (no (t3-logic-by-value-visit (1- n) lib (caddr branches) template leaf
                                        (append tests (list (list (car branches) nil))) natural)))
         (proof-by-value-join proof value template yes no)))
      (t
       (proof-with-checked-results ((equality (t3-logic-by-value-unfold proof value)))
         (if equality
             (proof-with-checked-results
                 ((opened (proof-rewritten-term equality))
                  (step (t3-logic-by-value-visit (1- n) lib opened template leaf tests natural))
                  (symmetric (proof-proof-symmetric proof equality)))
               (proof-proof-rewrite-result proof step symmetric template *proof-result*))
           (proof-with-checked-results
               ((step (if natural
                          (t3-logic-natural-visit (1- n) lib value)
                        (t3-logic-by-value-leaf value tests leaf))))
             (t3-logic-by-value-check-leaf step value template)))))))))

(defun t3-logic-libraryproofs-by-value (lib value template leaf tests)
  (t3-logic-by-value-visit 1000000 lib value template leaf tests nil))

(defun t3-logic-libraryproofs-natural (lib term)
  (t3-logic-natural-visit 1000000 lib term))

(defun t3-logic-naturally-integer (lib term)
  (proof-with-checked-results ((natural (t3-logic-libraryproofs-natural lib term)))
    (library-library-cite lib "NATURAL-INTEGER" (list term) (list natural))))

(mutual-recursion
 (defun t3-logic-libraryproofs-type-of (lib term evidence)
   (declare (xargs :measure (acl2-count term)))
   (if (or (t3-logic-book-natural-p lib term)
           (proof-is-call term *t3-logic-length*)
           (proof-is-call term *library-gap*)
           (proof-is-call term *proof-if*))
       (t3-logic-naturally-integer lib term)
     (let ((literal (library-integer term)))
       (proof-with-checked-results ((premise (proof-find-evidence evidence (list literal))))
         (cond
          (premise premise)
          ((and (proof-is-call term *proof-quote*) (endp (cdr term)))
           '(:failure "MissingProofInput" ""))
          ((and (proof-is-call term *proof-quote*)
                (or (integerp (cadr term)) (eq (cadr term) t)))
           (t3-logic-libraryproofs-prove lib literal nil nil))
          ((and (consp term)
                (or (proof-is-call term *proof-plus*) (proof-is-call term *proof-times*)))
           (proof-with-checked-results
               ((steps (t3-logic-type-arguments lib (cdr term) evidence)))
             (library-library-cite lib
                                   (if (equal (car term) *proof-plus*)
                                       "INTEGER-SUM" "INTEGER-PRODUCT")
                                   (cdr term) steps)))
          ((and (consp term) (proof-is-call term *proof-minus*))
           (if (endp (cdr term))
               '(:failure "MissingProofInput" "")
             (proof-with-checked-results
                 ((step (t3-logic-libraryproofs-type-of lib (cadr term) evidence)))
               (library-library-cite lib "INTEGER-NEGATION" (cdr term) (list step)))))
          (t (library-library-type-of lib term nil)))))))

 (defun t3-logic-type-arguments (lib args evidence)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((first (t3-logic-libraryproofs-type-of lib (car args) evidence))
          (rest (t3-logic-type-arguments lib (cdr args) evidence)))
       (cons first rest)))))

(defun t3-logic-libraryproofs-rational (lib term evidence)
  (proof-with-checked-results
      ((axiom (library-library-axiom lib "INTEGER-IMPLIES-RATIONAL" (list term)))
       (type-step (t3-logic-libraryproofs-type-of lib term evidence)))
    (proof-proof-modus-ponens (library-library-proof lib) axiom type-step)))

(defun t3-logic-libraryproofs-number (lib term evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof "rationalp-acl2-numberp" (list (list *library-x* term))))
         (rational (t3-logic-libraryproofs-rational lib term evidence)))
      (proof-proof-modus-ponens proof fact rational))))

(defun t3-logic-unsupported (term)
  (proof-with-checked-results ((text (proof-write term)))
    '(:failure "Unsupported" "")))

(defund t3-logic-prove-formula-plan (lib term definitions evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((premise (proof-find-evidence evidence (list term))))
      (cond
       (premise premise)
       ((equal term *proof-true*) (proof-proof-prove proof term nil nil))
       (t
        (proof-with-checked-results
            ((opened (t3-logic-libraryproofs-normalize lib term evidence definitions))
             (right (and opened (proof-rewritten-term opened))))
          (cond
           ((and opened (not (equal right term))) (list :transport right opened))
           ((proof-is-call term *proof-if*)
            (proof-with-checked-results ((branches (proof-list-of-length (cdr term) 3)))
              (cons :split branches)))
           (t (t3-logic-unsupported term)))))))))

(defund t3-logic-prove-formula-evidence (proof test holds evidence)
  (proof-with-checked-results ((assumed (proof-proof-assume proof test holds)))
    (append evidence (list assumed))))

(defun t3-logic-prove-formula-cases (proof term test yes no)
  (proof-with-checked-results
      ((if-true (proof-proof-if-true proof term))
       (when-true (proof-proof-transport proof yes if-true))
       (if-false (proof-proof-if-false proof term))
       (when-false (proof-proof-transport proof no if-false)))
    (proof-proof-cases proof test when-true when-false)))

(defun t3-logic-prove-formula-visit (n lib term definitions evidence)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-logic-libraryproofs-prove-formula")
    (let ((proof (library-library-proof lib))
          (plan (t3-logic-prove-formula-plan lib term definitions evidence)))
      (case (car plan)
        (:transport
         (proof-with-checked-results
             ((step (t3-logic-prove-formula-visit (1- n) lib (cadr plan) definitions evidence)))
           (proof-proof-transport proof step (caddr plan))))
        (:split
         (let ((test (cadr plan)))
           (proof-with-checked-results
               ((positive (t3-logic-prove-formula-evidence proof test t evidence))
                (yes (t3-logic-prove-formula-visit (1- n) lib (caddr plan) definitions positive))
                (negative (t3-logic-prove-formula-evidence proof test nil evidence))
                (no (t3-logic-prove-formula-visit (1- n) lib (cadddr plan) definitions negative)))
             (t3-logic-prove-formula-cases proof term test yes no))))
        (otherwise plan)))))

(defun t3-logic-libraryproofs-prove-formula (lib term definitions evidence)
  (t3-logic-prove-formula-visit 1000000 lib term definitions evidence))

; An auxiliary entry can be named by a quoted string or a qualified symbol.
(defconst *t3-logic-token-punctuation* (coerce "+*/<=>!?$%&_^~.@-" 'list))

(defun t3-logic-token-plain-p (token-char)
  (let ((code (char-code token-char)))
    (or (and (<= 65 code) (<= code 90))
        (and (<= 48 code) (<= code 57))
        (member-eq token-char *t3-logic-token-punctuation*))))

(defund t3-logic-token-plain-end (source size index)
  (declare (xargs :measure (nfix (- size index))))
  (if (and (integerp index) (integerp size) (< index size)
           (t3-logic-token-plain-p (char source index)))
      (t3-logic-token-plain-end source size (1+ index))
    index))

(defun t3-logic-token-delimited-end (source size index delimiter)
  (declare (xargs :measure (nfix (- size index))))
  (cond ((or (not (integerp index)) (not (integerp size)) (<= size index)) nil)
        ((eql (char source index) delimiter) (1+ index))
        (t (t3-logic-token-delimited-end source size (1+ index) delimiter))))

(defun t3-logic-token-symbol-end (source size index)
  (cond ((<= size index) nil)
        ((eql (char source index) #\|)
         (t3-logic-token-delimited-end source size (1+ index) #\|))
        (t (let ((end (t3-logic-token-plain-end source size index)))
             (and (< index end) end)))))

(defund t3-logic-token-end (source size index plain-end)
  (if (eql (char source index) #\")
      (t3-logic-token-delimited-end source size (1+ index) #\")
    (let ((package-end (if (< index plain-end)
                           plain-end
                         (t3-logic-token-symbol-end source size index))))
      (and package-end
           (< (1+ package-end) size)
           (eql (char source package-end) #\:)
           (eql (char source (1+ package-end)) #\:)
           (t3-logic-token-symbol-end source size (+ 2 package-end))))))

(defun t3-logic-token-plain-chars (chars reversed)
  (if (and (consp chars) (t3-logic-token-plain-p (car chars)))
      (t3-logic-token-plain-chars (cdr chars) (cons (car chars) reversed))
    (cons reversed chars)))

(defun t3-logic-token-delimited-chars (chars delimiter reversed)
  (if (endp chars)
      nil
    (let ((next (cons (car chars) reversed)))
      (if (eql (car chars) delimiter)
          (cons next (cdr chars))
        (t3-logic-token-delimited-chars (cdr chars) delimiter next)))))

(defun t3-logic-token-part-chars (chars reversed)
  (cond
   ((endp chars) nil)
   ((eql (car chars) #\|)
    (t3-logic-token-delimited-chars (cdr chars) #\| (cons #\| reversed)))
   ((t3-logic-token-plain-p (car chars))
    (t3-logic-token-plain-chars chars reversed))
   (t nil)))

(defun t3-logic-token-qualified-chars (part)
  (let ((tail (cdr part)))
    (and part
         (eql (car tail) #\:)
         (eql (cadr tail) #\:)
         (t3-logic-token-part-chars (cddr tail) (list* #\: #\: (car part))))))

; A chunk gives a match flag, the consumed characters in reverse order,
; and the rest of the input.
(defund t3-logic-token-chunk (chars)
  (let* ((first (car chars))
         (plain (and (t3-logic-token-plain-p first)
                     (t3-logic-token-plain-chars chars nil)))
         (match (if (eql first #\")
                    (t3-logic-token-delimited-chars (cdr chars) #\" (list first))
                  (t3-logic-token-qualified-chars
                   (or plain (t3-logic-token-part-chars chars nil))))))
    (cond (match (list t (car match) (cdr match)))
          (plain (list nil (car plain) (cdr plain)))
          (t (list nil (list first) (cdr chars))))))

(defun t3-logic-collect-tokens (remaining chars required)
  (declare (xargs :measure (nfix remaining)))
  (if (or (zp remaining) (endp chars))
      required
    (let* ((chunk (t3-logic-token-chunk chars))
           (raw (cadr chunk))
           (width (max 1 (len raw)))
           (required (if (car chunk)
                         (let ((token (coerce (reverse raw) 'string)))
                           (if (member-equal token required)
                               required
                             (cons token required)))
                       required)))
      (t3-logic-collect-tokens (- remaining width) (caddr chunk) required))))

(defun t3-logic-tokens (source size index required)
  (if (or (not (integerp index)) (not (integerp size)) (<= size index))
      required
    (let* ((remaining (- size index))
           (chars (nthcdr (nfix index) (coerce source 'list)))
           (chars (if (< size (length source)) (take remaining chars) chars)))
      (t3-logic-collect-tokens remaining chars required))))

(defun t3-logic-required-from-entries (entries required result)
  (if (endp entries)
      result
    (let ((entry (car entries)))
      (proof-with-checked-results
          ((fields (proof-list-of-length entry 4))
           (name (proof-write (cadr fields))))
        (if (member-equal name required)
            (let ((source (cadddr fields)))
              (t3-logic-required-from-entries (cdr entries)
                                              (t3-logic-tokens source (length source) 0 required)
                                              (cons entry result)))
          (t3-logic-required-from-entries (cdr entries) required result))))))

(defun t3-logic-libraryproofs-required-entries (lib source)
  (t3-logic-required-from-entries (reverse (library-library-entries lib))
                                  (t3-logic-tokens source (length source) 0 nil) nil))

(defun t3-logic-delete-name (entries name)
  (if (assoc-equal name entries)
      (table-delete entries name)
    '(:failure "failure" "")))

(defun t3-logic-discard-names (entries facts definitions)
  (if (endp entries)
      (cons facts definitions)
    (proof-with-checked-results
        ((fields (proof-list-of-length (car entries) 4))
         (name (cadr fields))
         (facts (t3-logic-delete-name facts name))
         (definitions (if (equal (car fields) "define")
                          (t3-logic-delete-name definitions name)
                        definitions)))
      (t3-logic-discard-names (cdr entries) facts definitions))))

(defun t3-logic-slice-start (start size)
  (cond ((integerp start)
         (if (< start 0) (max 0 (+ size start)) (min size start)))
        ((eq start t) (min 1 size))
        ((or (not start) (eq start :none)) 0)
        (t '(:failure "failure" ""))))

(defun t3-logic-libraryproofs-discard-entries (lib start)
  (let ((entries (library-library-entries lib))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((start (t3-logic-slice-start start (len entries)))
         (maps (t3-logic-discard-names (nthcdr start entries)
                                      (proof-proof-facts proof) (proof-proof-definitions proof))))
      (library-make-library
       (proof-proof-with-kind
        (proof-make-proof (car maps) (cdr maps) (proof-proof-primitives proof))
        (proof-proof-kind proof))
       (take start entries)))))

(defun t3-logic-make-evidence (lib tests facts definitions expanded)
  (list :t3-evidence lib tests facts definitions expanded))

(defun t3-logic-evidence-lib (evidence)
  (cadr evidence))

(defun t3-logic-evidence-tests (evidence)
  (caddr evidence))

(defun t3-logic-evidence-facts (evidence)
  (cadddr evidence))

(defun t3-logic-evidence-definitions (evidence)
  (car (cddddr evidence)))

(defun t3-logic-evidence-expanded (evidence)
  (cadr (cddddr evidence)))

(defun t3-logic-evidence-with-facts (evidence facts)
  (t3-logic-make-evidence (t3-logic-evidence-lib evidence)
                          (t3-logic-evidence-tests evidence)
                          facts
                          (t3-logic-evidence-definitions evidence)
                          (t3-logic-evidence-expanded evidence)))

(defun t3-logic-evidence-with-lib (evidence lib)
  (t3-logic-make-evidence lib
                          (t3-logic-evidence-tests evidence)
                          (t3-logic-evidence-facts evidence)
                          (t3-logic-evidence-definitions evidence)
                          (t3-logic-evidence-expanded evidence)))

(defun t3-logic-evidence-with-expanded (evidence)
  (t3-logic-make-evidence (t3-logic-evidence-lib evidence)
                          (t3-logic-evidence-tests evidence)
                          (t3-logic-evidence-facts evidence)
                          (t3-logic-evidence-definitions evidence)
                          t))

(defun t3-logic-evidence-extra-facts (extra facts)
  (if (endp extra)
      facts
    (proof-with-checked-results ((literal (proof-step-first (car extra))))
      (t3-logic-evidence-extra-facts (cdr extra) (table-put facts literal (car extra))))))

(defun t3-logic-evidence-init (lib tests extra definitions)
  (proof-with-checked-results ((facts (t3-logic-evidence-extra-facts extra nil)))
    (t3-logic-make-evidence lib tests facts
                            (append (list *t3-logic-atom* *t3-logic-endp* (proof-cl "=")
                                          (proof-cl "EQ") (proof-cl "NULL")
                                          (proof-sym "QUOTEP" "ACL2"))
                                    definitions)
                            nil)))

(defund t3-logic-evidence-default (evidence step)
  (let ((facts (t3-logic-evidence-facts evidence)))
    (proof-with-checked-results ((literal (proof-step-first step)))
      (if (assoc-equal literal facts)
          evidence
        (t3-logic-evidence-with-facts evidence (table-put facts literal step))))))

(defun t3-logic-evidence-test-assumption (proof tests term)
  (if (endp tests)
      nil
    (proof-with-checked-results ((signed (proof-list-of-length (car tests) 2)))
      (let ((test (car signed))
            (holds (cadr signed)))
        (if (equal term (if holds test (proof-neg test)))
            (proof-proof-assume proof test holds)
          (t3-logic-evidence-test-assumption proof (cdr tests) term))))))

(defun t3-logic-evidence-selector (term holds)
  (cond ((and holds (proof-is-call term *t3-logic-consp*))
         (proof-term-at term 1))
        ((and (not holds) (proof-is-call term *proof-equal*))
         (proof-with-checked-results ((right (proof-term-at term 2)))
           (if (equal right *proof-false*)
               (proof-term-at term 1)
             term)))
        (t term)))

(defund t3-logic-evidence-selector-proof (lib term holds step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((selector (t3-logic-evidence-selector term holds)))
      (if (and (or holds (not (equal selector term))) (proof-compound selector))
          (proof-with-checked-results ((head (proof-term-at selector 0)))
            (if (not (member-equal head (list *library-car* *library-cdr*)))
                nil
              (proof-with-checked-results
                  ((parent (proof-term-at selector 1))
                   (completion (library-library-axiom
                                lib (concatenate 'string "COMPLETION-OF-" (caddr head))
                                (list parent)))
                   (body (proof-rewritten-term completion))
                   (if-false (proof-proof-if-false proof body))
                   (absent (proof-proof-chain proof completion (list if-false)))
                   (place (cond ((equal selector term) '(1))
                                (holds '(1 1))
                                (t '(1 1 1))))
                   (contradiction (proof-proof-rewrite proof step absent place))
                   (simplified (t3-logic-libraryproofs-simplify-first lib contradiction
                                                                     nil (list *proof-not*))))
                (proof-proof-front proof simplified (list *t3-logic-consp* parent)))))
        nil))))

(defund t3-logic-evidence-double-negative (lib term step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof term))
         (body (proof-rewritten-term opened))
         (if-false (proof-proof-if-false proof body))
         (reduced (proof-proof-chain proof opened (list if-false)))
         (opposite (proof-proof-rewrite proof step reduced '(1 1)))
         (simplified (t3-logic-libraryproofs-simplify-first lib opposite nil (list *proof-not*)))
         (arg (proof-term-at term 1)))
      (proof-proof-front proof simplified arg))))

(defund t3-logic-evidence-simplify-lost (lib lost holds)
  (if (and (not holds) (consp (proof-step-clause lost)))
      (proof-with-checked-results ((literal (proof-step-first lost)))
        (if (equal literal (proof-neg *proof-true*))
            (t3-logic-libraryproofs-simplify-first lib lost nil (list *proof-not*))
          lost))
    lost))

(defund t3-logic-evidence-rewrite-test (proof step equation holds)
  (proof-with-checked-results
      ((rewritten (proof-proof-rewrite proof step equation (if holds '(1) '(1 1)))))
    (proof-proof-tidy proof rewritten)))

(defund t3-logic-evidence-conditional-guard (lib term holds step test branch)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((other (if branch (proof-proof-if-false proof term) (proof-proof-if-true proof term)))
         (lost (t3-logic-evidence-rewrite-test proof step other holds))
         (simplified (t3-logic-evidence-simplify-lost lib lost holds)))
      (proof-proof-front proof simplified (if branch test (proof-neg test))))))

(defund t3-logic-evidence-conditional-proof (proof term holds step guard)
  (proof-with-checked-results ((equality (proof-proof-select proof term guard)))
    (t3-logic-evidence-rewrite-test proof step equality holds)))

(mutual-recursion
 (defun t3-logic-evidence-record-visit (n evidence term holds step)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-logic-evidence-record")
     (proof-with-checked-results
         ((updated (t3-logic-evidence-default evidence step))
          (result (if (proof-is-call term *proof-if*)
                      (t3-logic-evidence-conditional-visit (1- n) updated term holds step)
                    (cons nil updated))))
       (if (car result)
           (cdr result)
         (t3-logic-evidence-record-normalized (1- n) (cdr result) term holds step)))))

 (defun t3-logic-evidence-record-normalized (n evidence term holds step)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-logic-evidence-record")
     (let ((lib (t3-logic-evidence-lib evidence))
           (definitions (t3-logic-evidence-definitions evidence)))
       (proof-with-checked-results
           ((equation (t3-logic-libraryproofs-normalize lib term nil definitions))
            (right (and equation (proof-rewritten-term equation))))
         (if (and equation (not (equal right term)))
             (proof-with-checked-results
                 ((tidied (t3-logic-evidence-rewrite-test (library-library-proof lib) step equation holds)))
               (t3-logic-evidence-record-visit (1- n) evidence right holds tidied))
           (t3-logic-evidence-record-related (1- n) evidence term holds step))))))

 (defun t3-logic-evidence-record-related (n evidence term holds step)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-logic-evidence-record")
     (let ((lib (t3-logic-evidence-lib evidence)))
       (proof-with-checked-results
           ((cons-proof (t3-logic-evidence-selector-proof lib term holds step))
            (updated (if cons-proof
                         (proof-with-checked-results ((literal (proof-step-first cons-proof)))
                           (t3-logic-evidence-record-visit (1- n) evidence literal t cons-proof))
                       evidence)))
         (cond ((not (proof-is-call term *proof-not*)) updated)
               (holds
                (proof-with-checked-results ((arg (proof-term-at term 1)))
                  (t3-logic-evidence-record-visit (1- n) updated arg nil step)))
               (t
                (proof-with-checked-results
                    ((opposite (t3-logic-evidence-double-negative lib term step))
                     (arg (proof-term-at term 1)))
                  (t3-logic-evidence-record-visit (1- n) updated arg t opposite))))))))

 (defun t3-logic-evidence-conditional-visit (n evidence term holds step)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-logic-evidence-conditional")
     (proof-with-checked-results ((branches (proof-list-of-length (cdr term) 3)))
       (let* ((test (car branches))
              (yes (cadr branches))
              (no (caddr branches))
              (impossible (if holds *proof-false* *proof-true*))
              (branch (equal no impossible)))
         (if (or branch (equal yes impossible) (and (not holds) (equal yes test)))
             (t3-logic-evidence-conditional-selected (1- n) evidence term holds step
                                                    test branch (if branch yes no))
           (cons nil evidence))))))

 (defun t3-logic-evidence-conditional-selected (n evidence term holds step test branch selected)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-logic-evidence-conditional")
     (let* ((lib (t3-logic-evidence-lib evidence))
            (proof (library-library-proof lib)))
       (proof-with-checked-results
           ((guard (t3-logic-evidence-conditional-guard lib term holds step test branch))
            (updated (t3-logic-evidence-record-visit (1- n) evidence test branch guard))
            (selected-proof (t3-logic-evidence-conditional-proof proof term holds step guard))
            (updated (if (and (equal selected test) (equal holds branch))
                         updated
                       (t3-logic-evidence-record-visit (1- n) updated selected holds selected-proof))))
         (cons t updated))))))

(defun t3-logic-evidence-record (evidence term holds step)
  (t3-logic-evidence-record-visit 1000000 evidence term holds step))

(defun t3-logic-evidence-conditional (evidence term holds step)
  (t3-logic-evidence-conditional-visit 1000000 evidence term holds step))

(defund t3-logic-evidence-expand-one (evidence signed-test)
  (let ((proof (library-library-proof (t3-logic-evidence-lib evidence))))
    (proof-with-checked-results
        ((signed (proof-list-of-length signed-test 2))
         (test (car signed))
         (holds (cadr signed))
         (step (proof-proof-assume proof test holds)))
      (t3-logic-evidence-record evidence test holds step))))

(defun t3-logic-evidence-expand-tests (evidence tests)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      evidence
    (proof-with-checked-results ((updated (t3-logic-evidence-expand-one evidence (car tests))))
      (t3-logic-evidence-expand-tests updated (cdr tests)))))

(defun t3-logic-evidence-expand (evidence)
  (if (t3-logic-evidence-expanded evidence)
      evidence
    (t3-logic-evidence-expand-tests (t3-logic-evidence-with-expanded evidence)
                                    (t3-logic-evidence-tests evidence))))

(defund t3-logic-evidence-positive-recognizer (lib predicate recognized atom cons-test facts)
  (let ((proof (library-library-proof lib))
        (defs (list predicate *t3-logic-atom* *t3-logic-endp* (proof-cl "NULL") (proof-cl "EQ"))))
    (proof-with-checked-results
        ((literal (proof-step-first recognized))
         (equation (t3-logic-libraryproofs-simplify lib literal (list atom) defs)))
      (if (not equation)
          nil
        (proof-with-checked-results
            ((rewritten (proof-proof-rewrite proof recognized equation '(1)))
             (check (proof-proof-tidy proof rewritten)))
          (if (not (member-equal cons-test (proof-step-clause check)))
              nil
            (proof-with-checked-results ((right (proof-rewritten-term equation)))
              (if (equal right *proof-false*)
                  (proof-proof-front proof check cons-test)
                (proof-with-checked-results
                    ((first (proof-step-first check))
                     (reject (table-get facts (proof-neg first) nil)))
                  (if reject
                      (proof-with-checked-results ((cut (proof-proof-cut proof check reject)))
                        (proof-proof-front proof cut cons-test))
                    nil))))))))))

(defun t3-logic-evidence-positive-recognizers (lib predicates term atom cons-test facts)
  (declare (xargs :measure (acl2-count predicates)))
  (if (endp predicates)
      nil
    (let* ((predicate (car predicates))
           (recognized (table-get facts (list predicate term) nil)))
      (proof-with-checked-results
          ((step (and recognized (t3-logic-evidence-positive-recognizer
                                 lib predicate recognized atom cons-test facts))))
        (or step (t3-logic-evidence-positive-recognizers
                  lib (cdr predicates) term atom cons-test facts))))))

(defun t3-logic-evidence-illegal-car (lib term atom cons-test facts)
  (let* ((proof (library-library-proof lib))
         (car-term (list *library-car* term))
         (legal (list *t3-logic-legal-constantp* car-term))
         (forbidden (table-get facts (proof-neg legal) nil)))
    (and forbidden
         (proof-with-checked-results
             ((completion (library-library-axiom lib "COMPLETION-OF-CAR" (list term)))
              (body (proof-rewritten-term completion))
              (selected (proof-proof-select proof body atom))
              (absent (proof-proof-chain proof completion (list selected)))
              (reduced (proof-proof-rewrite proof forbidden absent '(1 1 1)))
              (contradiction (t3-logic-libraryproofs-simplify-first
                              lib reduced nil (list *t3-logic-legal-constantp*
                                                    *proof-not* (proof-cl "EQ")))))
           (proof-proof-front proof contradiction cons-test)))))

(defun t3-logic-evidence-positive-consp (evidence term)
  (let* ((lib (t3-logic-evidence-lib evidence))
         (proof (library-library-proof lib))
         (facts (t3-logic-evidence-facts evidence))
         (cons-test (list *t3-logic-consp* term)))
    (proof-with-checked-results
        ((atom (proof-proof-assume proof cons-test nil))
         (step (t3-logic-evidence-positive-recognizers
                lib *t3-logic-ppr-predicates* term atom cons-test facts)))
      (or step (t3-logic-evidence-illegal-car lib term atom cons-test facts)))))

(defun t3-logic-evidence-find-expanded (evidence term)
  (let ((step (table-get (t3-logic-evidence-facts evidence) term nil)))
    (if (or step (not (proof-is-call term *t3-logic-consp*)))
        (cons step evidence)
      (proof-with-checked-results
          ((arg (proof-term-at term 1))
           (step (t3-logic-evidence-positive-consp evidence arg)))
        (cons step
              (if step
                  (t3-logic-evidence-with-facts
                   evidence (table-put (t3-logic-evidence-facts evidence) term step))
                evidence))))))

(defund t3-logic-evidence-find (evidence term)
  (let ((entry (assoc-equal term (t3-logic-evidence-facts evidence)))
        (proof (library-library-proof (t3-logic-evidence-lib evidence))))
    (if entry
        (cons (cdr entry) evidence)
      (proof-with-checked-results
          ((direct (t3-logic-evidence-test-assumption proof (t3-logic-evidence-tests evidence) term)))
        (if direct
            (cons direct evidence)
          (proof-with-checked-results ((expanded (t3-logic-evidence-expand evidence)))
            (t3-logic-evidence-find-expanded expanded term)))))))

(defun t3-logic-evidence-require (evidence term)
  (proof-with-checked-results ((result (t3-logic-evidence-find evidence term)))
    (if (car result)
        result
      (t3-logic-unsupported term))))

(mutual-recursion
 (defun t3-logic-evidence-integer (evidence term)
   (declare (xargs :measure (acl2-count term)))
   (proof-with-checked-results ((direct (t3-logic-evidence-find evidence (library-integer term))))
     (if (car direct)
         direct
       (proof-with-checked-results ((natural (t3-logic-evidence-find (cdr direct)
                                                                   (list *library-natp* term))))
         (let* ((updated (cdr natural))
                (lib (t3-logic-evidence-lib updated)))
           (cond
            ((car natural)
             (proof-with-checked-results
                 ((step (library-library-cite lib "NATURAL-INTEGER" (list term) (list (car natural)))))
               (cons step updated)))
            ((not term) '(:failure "MissingProofInput" ""))
            ((and (consp term) (proof-compound term)
                  (member-equal (car term) (list *proof-plus* *proof-times* *proof-minus*)))
             (proof-with-checked-results
                 ((arguments (t3-logic-evidence-integer-args updated (cdr term)))
                  (step (t3-logic-libraryproofs-type-of (t3-logic-evidence-lib (cdr arguments))
                                                       term (car arguments))))
               (cons step (cdr arguments))))
            (t (proof-with-checked-results ((step (t3-logic-libraryproofs-type-of lib term nil)))
                 (cons step updated)))))))))

 (defun t3-logic-evidence-integer-args (evidence args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       (cons nil evidence)
     (proof-with-checked-results
         ((first (t3-logic-evidence-integer evidence (car args)))
          (rest (t3-logic-evidence-integer-args (cdr first) (cdr args))))
       (cons (cons (car first) (car rest)) (cdr rest))))))

(defun t3-logic-evidence-nonnegative (evidence term)
  (proof-with-checked-results
      ((direct (t3-logic-evidence-find evidence (proof-neg (library-lt term *proof-zero*)))))
    (if (car direct)
        direct
      (proof-with-checked-results
          ((known (t3-logic-evidence-find (cdr direct) (list *library-natp* term)))
           (lib (t3-logic-evidence-lib (cdr known)))
           (natural (or (car known) (t3-logic-libraryproofs-natural lib term)))
           (step (library-library-cite lib "NATURAL-NONNEGATIVE" (list term) (list natural))))
        (cons step (cdr known))))))
