(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-api-prefix* "H3")
(defconst *h3-api-newline* (coerce (list #\Newline) 'string))
(defconst *h3-api-line-ends* (coerce (list #\Return #\Newline) 'string))

(defun h3-api-sequence-failure (value)
  (and (or (rationalp value) (eq value t))
       '(:failure "failure" "")))

(defun h3-api-unpack-pair (value)
  (if (stringp value)
      (if (= (length value) 2)
          (list (subseq value 0 1) (subseq value 1 2))
        '(:failure "failure" ""))
    (proof-list-of-length value 2)))

(defun h3-api-read (raw)
  (if (not (stringp raw))
      '(:failure "failure" "")
    (let* ((text (text-strip-right raw *h3-api-line-ends*))
           (result (reader-reader-line (reader-reader-init text))))
      (if (failure-p result)
          result
        (proof-freeze (car result))))))

(defun h3-api-admit-fact (lib name formula)
  (let* ((proof (library-library-proof lib))
         (facts (table-put (proof-proof-facts proof) name (list formula))))
    (library-library-with-proof lib (proof-proof-with-facts proof facts))))

(defun h3-api-admit-definitions (lib definitions)
  (if (endp definitions)
      lib
    (let* ((definition (car definitions))
           (size (len definition)))
      (if (or (integerp definition) (/= size 3))
          '(:failure "failure" "")
        (let ((formals (cadr definition)))
          (if (or (integerp formals) (stringp formals))
              '(:failure "failure" "")
            (h3-api-admit-definitions
             (library-library-with-proof
              lib (proof-proof-add-definition (library-library-proof lib)
                                              (car definition) formals (caddr definition)))
             (cdr definitions))))))))

(defun h3-api-admit-constraints (lib constraints)
  (cond
   ((h3-api-sequence-failure constraints))
   ((endp constraints) lib)
   (t
    (proof-with-checked-results
     ((pair (h3-api-unpack-pair (car constraints))))
     (h3-api-admit-constraints
      (h3-api-admit-fact lib (car pair) (cadr pair)) (cdr constraints))))))

(defun h3-api-admit (lib kind fields)
  (cond
   ((equal kind "define")
    (if (integerp fields)
        '(:failure "failure" "")
      (h3-api-admit-definitions lib (cdr fields))))
   ((equal kind "constrain")
    (proof-with-checked-results
     ((constraints (proof-term-at fields 1)))
     (if (equal constraints *proof-nil*)
         lib
       (h3-api-admit-constraints lib constraints))))
   ((member-equal kind '("theorem" "axiom"))
    (proof-with-checked-results
     ((name (proof-term-at fields 0))
      (formula (proof-term-at fields 1)))
     (h3-api-admit-fact lib name formula)))
   (t lib)))

(defun h3-api-read-declaration (raw)
  (cond ((not (stringp raw)) '(:failure "failure" ""))
        ((text-starts-with raw '("(define " "(constrain " "(theorem " "(axiom "))
         (h3-api-read raw))
        (t nil)))

(defun h3-api-admitted-definition-names (definitions)
  (if (endp definitions)
      nil
    (cons (caar definitions) (h3-api-admitted-definition-names (cdr definitions)))))

(defun h3-api-admitted-constraint-names (constraints)
  (if (or (equal constraints *proof-nil*) (endp constraints))
      nil
    (cons (car (h3-api-unpack-pair (car constraints)))
          (h3-api-admitted-constraint-names (cdr constraints)))))

(defun h3-api-admitted-names (kind fields)
  (cond ((equal kind "define") (h3-api-admitted-definition-names (cdr fields)))
        ((equal kind "constrain") (h3-api-admitted-constraint-names (cadr fields)))
        ((member-equal kind '("theorem" "axiom")) (list (car fields)))
        (t nil)))

(defun h3-api-admit-lines (lib lines)
  (cond
   ((h3-api-sequence-failure lines))
   ((endp lines) lib)
   (t
    (proof-with-checked-results
     ((parsed (h3-api-read-declaration (car lines))))
     (if parsed
         (proof-with-checked-results
          ((next (h3-api-admit lib (car parsed) (cadr parsed))))
          (h3-api-admit-lines next (cdr lines)))
       (h3-api-admit-lines lib (cdr lines)))))))

(defun h3-api-library (lines)
  (h3-api-admit-lines (library-library-init (proof-proof-init)) lines))

(defun h3-api-world (library earlier)
  (proof-with-checked-results
   ((base (h3-api-library library)))
   (h3-api-admit-lines (library-library-with-entries base nil) earlier)))

(defun h3-api-measures (aids)
  (cond
   ((h3-api-sequence-failure aids))
   ((endp aids) nil)
   (t
    (let ((raw (car aids)))
      (cond
       ((not (stringp raw)) '(:failure "failure" ""))
       ((text-starts-with raw "(measure ")
        (proof-with-checked-results
         ((parsed (h3-api-read raw))
          (rest (h3-api-measures (cdr aids))))
         (cons parsed rest)))
       (t (h3-api-measures (cdr aids))))))))

(defun h3-api-make-entries (entries tokens reserved names output active)
  (list :h3-api-entries entries tokens reserved names output active))

(defun h3-api-entries-sources (object)
  (nth 1 object))

(defun h3-api-entries-tokens (object)
  (nth 2 object))

(defun h3-api-entries-reserved (object)
  (nth 3 object))

(defun h3-api-entries-names (object)
  (nth 4 object))

(defun h3-api-entries-output (object)
  (nth 5 object))

(defun h3-api-entries-active (object)
  (nth 6 object))

(defun h3-api-entries-with-progress (object names output active)
  (h3-api-make-entries (h3-api-entries-sources object)
                      (h3-api-entries-tokens object)
                      (h3-api-entries-reserved object)
                      names output active))

(defun h3-api-entry-sources (entries sources)
  (if (endp entries)
      sources
    (let ((entry (car entries)))
      (h3-api-entry-sources (cdr entries)
                           (table-put sources (cadr entry) (cadddr entry))))))

(defun h3-api-reserved-names (facts sources)
  (cond ((endp facts) nil)
        ((assoc-equal (caar facts) sources)
         (h3-api-reserved-names (cdr facts) sources))
        (t (cons (caar facts) (h3-api-reserved-names (cdr facts) sources)))))

(defun h3-api-remove-local-names (sources names)
  (if (endp sources)
      names
    (let ((name (caar sources)))
      (h3-api-remove-local-names (cdr sources)
                                (if (member-equal name names) (remove-equal name names) names)))))

(defun h3-api-entries-init-using (lib prepared)
  (let ((sources (h3-api-entry-sources (library-library-entries lib) nil))
        (facts (proof-proof-facts (library-library-proof lib))))
    (proof-with-checked-results
     ((tokens (proof-write-list (table-keys sources))))
     (h3-api-make-entries sources tokens
                         (if prepared
                             ; Every fact added by a tactic has a local entry.
                             (h3-api-remove-local-names
                              sources (h3-book-tactics-prepared-fact-names prepared))
                           (h3-api-reserved-names facts sources))
                         nil nil nil))))

(defun h3-api-token-present-p (tokens text)
  (and (consp tokens)
       (or (<= 0 (text-find text (car tokens)))
           (h3-api-token-present-p (cdr tokens) text))))

(defun h3-api-proof-lines (chars reversed)
  (cond
   ((endp chars)
    (and reversed (list (coerce (reverse reversed) 'string))))
   ((eql (car chars) #\Newline)
    (cons (coerce (reverse (cons #\Newline reversed)) 'string)
          (h3-api-proof-lines (cdr chars) nil)))
   ((eql (car chars) #\Return)
    (if (eql (cadr chars) #\Newline)
        (cons (coerce (reverse (list* #\Newline #\Return reversed)) 'string)
              (h3-api-proof-lines (cddr chars) nil))
      (cons (coerce (reverse (cons #\Return reversed)) 'string)
            (h3-api-proof-lines (cdr chars) nil))))
   (t (h3-api-proof-lines (cdr chars) (cons (car chars) reversed)))))

(defun h3-api-local-name (source symbol)
  (let ((digest (text-upper (siphash-hexdigest source))))
    (proof-with-checked-results
     ((label (proof-term-at symbol 2)))
     (if (stringp label)
         (proof-sym (concatenate 'string "PROVER-" *h3-api-prefix* "-"
                                 (if (text-starts-with label "SELF-")
                                     (subseq label 5 nil)
                                   label)
                                 "-" digest)
                    (cadr symbol))
       '(:failure "failure" "")))))

(mutual-recursion
 (defun h3-api-entries-name (n object symbol)
   (declare (xargs :measure (nfix n)))
   (let ((local (assoc-equal symbol (h3-api-entries-sources object)))
         (named (assoc-equal symbol (h3-api-entries-names object))))
     (cond
      ((zp n) '(:failure "fuel" "h3-api-entries-name"))
      ((not local) (cons symbol object))
      (named (cons (cdr named) object))
      ((member-equal symbol (h3-api-entries-active object))
       '(:failure "failure" ""))
      (t
       (let ((object (h3-api-entries-with-progress
                      object (h3-api-entries-names object) (h3-api-entries-output object)
                      (cons symbol (h3-api-entries-active object)))))
         (proof-with-checked-results
          ((rewritten (h3-api-entries-rewrite (1- n) object (cdr local) symbol))
           (renamed (h3-api-local-name (car rewritten) symbol))
           (published (h3-api-entries-publish (1- n) (cdr rewritten)
                                             (car rewritten) symbol renamed)))
          (cons renamed published)))))))

 (defun h3-api-entries-publish (n object source symbol renamed)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h3-api-entries-publish"))
    ((member-equal renamed (h3-api-entries-reserved object))
     '(:failure "failure" ""))
    (t
     (let* ((object (h3-api-entries-with-progress
                     object (table-put (h3-api-entries-names object) symbol renamed)
                     (h3-api-entries-output object) (h3-api-entries-active object)))
            (split (text-find source *h3-api-newline*))
            (end (if (< split 0) (length source) split)))
       (proof-with-checked-results
        ((head (h3-api-read (subseq source 0 end)))
         (fields (h3-api-entries-fields (1- n) object (car head) (cadr head) nil))
         (line (proof-line (car head) (car fields))))
        (let* ((object (cdr fields))
               (text (concatenate 'string (text-strip-right line *h3-api-newline*)
                                  (subseq source end nil))))
          (h3-api-entries-with-progress
           object (h3-api-entries-names object)
           (append (h3-api-entries-output object) (list text))
           (remove-equal symbol (h3-api-entries-active object)))))))))

 (defun h3-api-entries-term (n object term)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h3-api-entries-term"))
    ((or (not (proof-compound term)) (endp term) (proof-is-call term *proof-quote*))
     (cons term object))
    (t
     (let ((head (car term)))
       (proof-with-checked-results
        ((head (if (proof-compound head)
                   (proof-with-checked-results
                    ((body (proof-term-at head 2))
                     (body (h3-api-entries-term (1- n) object body)))
                    (cons (list (car head) (cadr head) (car body)) (cdr body)))
                 (h3-api-entries-name (1- n) object head)))
         (args (h3-api-entries-map (1- n) (cdr head) :term (cdr term) nil)))
        (cons (cons (car head) (car args)) (cdr args)))))))

 (defun h3-api-entries-substitution (n object bindings)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "h3-api-entries-substitution"))
         ((equal bindings *proof-nil*) (cons bindings object))
         (t (h3-api-entries-map (1- n) object :binding bindings nil))))

 (defun h3-api-entries-fields (n object kind fields own)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h3-api-entries-fields"))
    ((equal kind "fact")
     (proof-with-checked-results
      ((name (proof-term-at fields 0))
       (named (h3-api-entries-name (1- n) object name)))
      (cons (list (car named)) (cdr named))))
    ((equal kind "lemma")
     (proof-with-checked-results
      ((name (proof-term-at fields 0))
       (named (if (equal name own)
                  (cons name object)
                (h3-api-entries-name (1- n) object name)))
       (terms (h3-api-entries-map (1- n) (cdr named) :term (cdr fields) nil)))
      (cons (cons (car named) (car terms)) (cdr terms))))
    ((equal kind "define")
     (proof-with-checked-results
      ((rulers (proof-term-at fields 0))
       (rulers (if (proof-compound rulers)
                   (h3-api-entries-map (1- n) object :name rulers nil)
                 (cons rulers object)))
       (definitions (h3-api-entries-map (1- n) (cdr rulers) :definition (cdr fields) own)))
      (cons (cons (car rulers) (car definitions)) (cdr definitions))))
    ((member-equal kind '("witness" "measure" "subsume"))
     (proof-with-checked-results
      ((items (h3-api-entries-map (1- n) object
                                  (if (equal kind "witness") :name :term) (cdr fields) nil)))
      (cons (append (seq-slice fields 0 1) (car items)) (cdr items))))
    ((equal kind "instantiate")
     (proof-with-checked-results
      ((bindings (proof-term-at fields 1))
       (bindings (h3-api-entries-substitution (1- n) object bindings)))
      (cons (list (car fields) (car bindings)) (cdr bindings))))
    ((member-equal kind '("beta" "compute"))
     (proof-with-checked-results
      ((term (proof-term-at fields 0))
       (term (h3-api-entries-term (1- n) object term)))
      (cons (list (car term)) (cdr term))))
    ((equal kind "induct")
     (proof-with-checked-results
      ((substitutions (proof-term-at fields 4))
       (substitutions (if (equal substitutions *proof-nil*)
                          (cons substitutions object)
                        (h3-api-entries-map (1- n) object :substitution substitutions nil)))
       (formula (h3-api-entries-term (1- n) (cdr substitutions) (nth 2 fields)))
       (measure (h3-api-entries-term (1- n) (cdr formula) (nth 3 fields))))
      (cons (list (car fields) (cadr fields) (car formula) (car measure) (car substitutions))
            (cdr measure))))
    (t (cons fields object))))

 (defun h3-api-entries-rewrite (n object text own)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "h3-api-entries-rewrite"))
         ((not (h3-api-entries-tokens object)) (cons text object))
         (t (h3-api-entries-rewrite-lines (1- n) object
                                          (h3-api-proof-lines (coerce text 'list) nil)
                                          own nil))))

 (defun h3-api-entries-map (n object method values own)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h3-api-entries-map"))
    ((h3-api-sequence-failure values))
    ((endp values) (cons nil object))
    (t
     (proof-with-checked-results
      ((first (case method
                (:name (h3-api-entries-name (1- n) object (car values)))
                (:term (h3-api-entries-term (1- n) object (car values)))
                (:binding (h3-api-entries-binding (1- n) object (car values)))
                (:definition (h3-api-entries-definition (1- n) object (car values) own))
                (:substitution (h3-api-entries-substitution (1- n) object (car values)))))
       (rest (h3-api-entries-map (1- n) (cdr first) method (cdr values) own)))
      (cons (cons (car first) (car rest)) (cdr rest))))))

 (defun h3-api-entries-binding (n object binding)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "h3-api-entries-binding")
     (proof-with-checked-results
      ((pair (h3-api-unpack-pair binding))
       (value (h3-api-entries-term (1- n) object (cadr pair))))
      (cons (list (car pair) (car value)) (cdr value)))))

 (defun h3-api-entries-definition (n object definition own)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "h3-api-entries-definition")
     (proof-with-checked-results
      ((definition (proof-list-of-length definition 3))
       (name (if (equal (car definition) own)
                 (cons own object)
               (h3-api-entries-name (1- n) object (car definition))))
       (body (h3-api-entries-term (1- n) (cdr name) (caddr definition))))
      (cons (list (car name) (cadr definition) (car body)) (cdr body)))))

 (defun h3-api-entries-rewrite-lines (n object lines own reversed)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h3-api-entries-rewrite-lines"))
    ((endp lines) (cons (text-join "" (reverse reversed)) object))
    (t
     (let ((raw (car lines)))
       (proof-with-checked-results
        ((rewritten
          (if (h3-api-token-present-p (h3-api-entries-tokens object) raw)
              (proof-with-checked-results
               ((parsed (h3-api-read raw))
                (fields (h3-api-entries-fields (1- n) object (car parsed) (cadr parsed) own))
                (line (proof-line (car parsed) (car fields))))
               (cons line (cdr fields)))
            (cons raw object))))
        (h3-api-entries-rewrite-lines (1- n) (cdr rewritten) (cdr lines) own
                                      (cons (car rewritten) reversed))))))))

(defun h3-api-book-entry-prepared (lib kind fields aids prepared)
  (let ((result (h3-book-tactics-solve-book-statement-prepared lib kind fields aids prepared)))
    (cond ((failure-p result) result)
          ((failure-p (car result)) (car result))
          (t result))))

(defun h3-api-slice-entry (result name formula)
  (cond ((failure-p result) result)
        ((or (not (proof-step-p result))
             (not (equal (proof-step-clause result) (list formula))))
         '(:failure "proof-mismatch" ""))
        (t (proof-proof-entry "theorem" name (list name) (list result)))))

(defun h3-api-ascii-characters-p (chars)
  (or (endp chars)
      (and (< (char-code (car chars)) 128)
           (h3-api-ascii-characters-p (cdr chars)))))

(defun h3-api-theorem-entry-using (lib fields rebuild prepared)
  (proof-with-checked-results
   ((theorem (proof-list-of-length fields 2)))
   (let* ((name (car theorem))
          (formula (cadr theorem))
          (solved (proof-with-checked-results
                   ((label (proof-term-at name 2)))
                   (if (and (stringp label) (h3-api-ascii-characters-p (coerce label 'list)))
                       (h3-tactics-solve lib label formula)
                     '(:failure "malformed-tactic-input" ""))))
          (current (if (failure-p solved) lib (cdr solved)))
          (step (if (failure-p solved) solved (car solved)))
          (entry (h3-api-slice-entry step name formula)))
     (cond ((not (failure-p entry)) (cons entry current))
           ((member-equal (cadr entry) '("unproved" "malformed-tactic-input" "missing-proof-data"
                                        "proof-mismatch" "different-normal-forms"
                                        "value" "assertion" "key" "index" "type" "attribute"))
            (proof-with-checked-results
             ((fresh (cond ((not (library-library-entries current)) current)
                           (rebuild (h3-api-world (car rebuild) (cadr rebuild)))
                           (t lib))))
             (h3-api-book-entry-prepared fresh "theorem" fields nil prepared)))
           (t entry)))))

(defun h3-api-prove-admitted-using (parsed lib measures rebuild prepared)
  (let ((kind (car parsed))
        (fields (cadr parsed)))
    (proof-with-checked-results
     ((result (if (equal kind "theorem")
                  (h3-api-theorem-entry-using lib fields rebuild prepared)
                (proof-with-checked-results ((measures measures))
                  (h3-api-book-entry-prepared lib kind fields measures prepared))))
      (named (h3-api-entries-init-using (cdr result) prepared))
      (source (proof-term-at (car result) 3))
      (rewritten (h3-api-entries-rewrite 1000000 named source nil)))
     (list (h3-api-entries-output (cdr rewritten)) (car rewritten)))))

(defun h3-api-prove-admitted (parsed lib aids rebuild)
  (let ((measures (and (equal (car parsed) "define") (h3-api-measures aids))))
    (h3-api-prove-admitted-using parsed lib measures rebuild nil)))

(defun h3-api-prove-with-prepared-facts (parsed lib measures prepared)
  (h3-api-prove-admitted-using parsed lib measures nil prepared))

(defun h3-api-prove-core (statement earlier library aids)
  (proof-with-checked-results
   ((parsed (h3-api-read statement)))
   (if (not (member-equal (car parsed) '("theorem" "define" "constrain")))
       nil
     (proof-with-checked-results
      ((earlier (or (h3-api-sequence-failure earlier) earlier))
       (library (or (h3-api-sequence-failure library) library))
       (lib (h3-api-world library earlier)))
      (h3-api-prove-admitted parsed lib aids (list library earlier))))))

(defun h3-api-prove (statement earlier library aids)
  (let ((result (h3-api-prove-core statement earlier library aids)))
    (if (failure-p result) nil result)))
