(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-run-tab* (coerce (list (code-char 9)) 'string))
(defconst *h4-book-run-newline* (coerce (list #\Newline) 'string))

(defun h4-book-run-make-statement (kind fields name calls)
  (list :h4-statement kind fields name calls))

(defun h4-book-run-statement-kind (statement)
  (cadr statement))

(defun h4-book-run-statement-fields (statement)
  (caddr statement))

(defun h4-book-run-statement-name (statement)
  (cadddr statement))

(defun h4-book-run-statement-calls (statement)
  (car (cddddr statement)))

(defun h4-book-run-make-certificate (proof steps support reason)
  (list :h4-certificate proof steps support reason))

(defun h4-book-run-certificate-proof (certificate)
  (cadr certificate))

(defun h4-book-run-certificate-steps (certificate)
  (caddr certificate))

(defun h4-book-run-certificate-support (certificate)
  (cadddr certificate))

(defun h4-book-run-certificate-reason (certificate)
  (car (cddddr certificate)))

(defun h4-book-run-constrained-name (fields)
  (proof-with-checked-results ((constraints (proof-term-at fields 1)))
    (if (equal constraints *proof-nil*)
        nil
      (proof-with-checked-results
          ((signatures (proof-term-at fields 0))
           (signature (proof-term-at signatures 0)))
        (if (stringp signature)
            (seq-slice signature 0 1)
          (proof-term-at signature 0))))))

(defun h4-book-run-read-line (raw)
  (proof-with-checked-results
      ((parsed (reader-reader-line
                (reader-reader-init (seq-slice raw 0 -1)))))
    (list (caar parsed) (proof-freeze (cadar parsed)))))

(defun h4-book-run-parse-statement (raw)
  (proof-with-checked-results ((parsed (h4-book-run-read-line raw)))
    (let ((kind (car parsed))
          (fields (cadr parsed)))
      (cond
       ((equal kind "theorem")
        (proof-with-checked-results ((name (proof-term-at fields 0)))
          (h4-book-run-make-statement kind fields name nil)))
       ((equal kind "constrain")
        (proof-with-checked-results ((name (h4-book-run-constrained-name fields)))
          (h4-book-run-make-statement kind fields name nil)))
       ((equal kind "define")
        (proof-with-checked-results
            ((rulers (proof-term-at fields 0))
             (calls (termination-recursive-calls rulers (cdr fields))))
          (h4-book-run-make-statement kind fields
                                      (and calls (caadr fields)) calls)))
       (t (h4-book-run-make-statement kind fields nil nil))))))

(defun h4-book-run-witness-formals (indices)
  (if (endp indices)
      nil
    (cons (proof-sym (concatenate 'string "H4-WITNESS-ARGUMENT-"
                                  (decimal-text (car indices)))
                     "ACL2")
          (h4-book-run-witness-formals (cdr indices)))))

(defund h4-book-run-witness-constants (p count formals models)
  (let* ((arity (decimal-text count))
         (nil-name (proof-sym (string-append "H4-CONSTANT-NIL-" arity) "ACL2"))
         (t-name (proof-sym (string-append "H4-CONSTANT-T-" arity) "ACL2")))
    (proof-with-checked-results
        ((p (library-library-definition p nil-name formals *proof-false*))
         (p (library-library-definition p t-name formals *proof-true*)))
      (let ((models (table-put (table-put models (list count "NIL") nil-name)
                                 (list count "T") t-name)))
        (if (endp formals)
            (cons models p)
          (let ((name (proof-sym (string-append "H4-FIRST-ARGUMENT-" arity) "ACL2")))
            (proof-with-checked-results
                ((p (library-library-definition p name formals (car formals))))
              (cons (table-put models (list count "first argument") name) p))))))))

(defun h4-book-run-witness-definitions-arities (p arities models)
  (declare (xargs :measure (acl2-count arities)))
  (if (endp arities)
      (cons models p)
    (proof-with-checked-results
        ((indices (seq-range 0 (car arities) 1))
         (defined (h4-book-run-witness-constants
                   p (car arities) (h4-book-run-witness-formals indices) models)))
      (h4-book-run-witness-definitions-arities
       (cdr defined) (cdr arities) (car defined)))))

(defun h4-book-run-witness-definitions (p arities)
  (h4-book-run-witness-definitions-arities
   p (seq-sorted (proof-unique arities)) nil))

(mutual-recursion
 (defun h4-book-run-replace-functions (term witnesses)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) term)
    ((atom term) '(:failure "failure" ""))
    (t
     (proof-with-checked-results
         ((head
           (if (not (proof-compound (car term)))
               (table-get witnesses (car term) (car term))
             (if (and (consp (car term)) (consp (cdar term)) (consp (cddar term)))
                 (proof-with-checked-results
                     ((body (h4-book-run-replace-functions (caddar term) witnesses)))
                   (list (caar term) (cadar term) body))
               '(:failure "failure" ""))))
          (args (h4-book-run-replace-arguments (cdr term) witnesses)))
       (cons head args)))))
 (defun h4-book-run-replace-arguments (args witnesses)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((argument (h4-book-run-replace-functions (car args) witnesses))
          (rest (h4-book-run-replace-arguments (cdr args) witnesses)))
       (cons argument rest)))))

(defun h4-book-run-add-proof-dependencies (data pending)
  (declare (xargs :measure (acl2-count data)))
  (if (endp data)
      pending
    (h4-book-run-add-proof-dependencies
     (cdr data) (if (proof-step-p (car data)) (cons (car data) pending) pending))))

(defun h4-book-run-proof-dependencies-walk (n pending seen names)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-book-run-proof-dependencies-walk"))
   ((endp pending) (reverse names))
   ((member-equal (car pending) seen)
    (h4-book-run-proof-dependencies-walk (1- n) (cdr pending) seen names))
   (t
    (let* ((step (car pending))
           (data (proof-step-data step))
           (next (h4-book-run-add-proof-dependencies data (cdr pending))))
      (if (equal (proof-step-word step) "fact")
          (proof-with-checked-results ((name (proof-term-at data 0)))
            (h4-book-run-proof-dependencies-walk
             (1- n) next (cons step seen)
             (if (member-equal name names) names (cons name names))))
        (h4-book-run-proof-dependencies-walk (1- n) next (cons step seen) names))))))

(defun h4-book-run-proof-dependencies (last)
  (h4-book-run-proof-dependencies-walk 1000000 (list last) nil nil))

(defun h4-book-run-sum-counts (counts)
  (if (endp counts)
      0
    (+ (car counts) (h4-book-run-sum-counts (cdr counts)))))

(defun h4-book-run-mentions-definition (written selected)
  (and (consp selected)
       (or (<= 0 (text-find (cadar selected) written))
           (h4-book-run-mentions-definition written (cdr selected)))))

(defun h4-book-run-entry-needed (kind name needed final-source selected)
  (or (member-equal name needed)
      (and (equal kind "define")
           (proof-with-checked-results ((written (proof-write name)))
             (or (<= 0 (text-find final-source written))
                 (h4-book-run-mentions-definition written (reverse selected)))))))

(defun h4-book-run-entry-facts (entries source needed)
  (declare (xargs :measure (acl2-count entries)))
  (if (endp entries)
      needed
    (let ((name (cadar entries)))
      (proof-with-checked-results ((written (proof-write name)))
        (h4-book-run-entry-facts
         (cdr entries) source
         (if (and (<= 0 (text-find source (concatenate 'string "(fact " written ")")))
                  (not (member-equal name needed)))
             (cons name needed)
           needed))))))

(defun h4-book-run-entry-sources-select
    (remaining entries needed final-source selected)
  (declare (xargs :measure (acl2-count remaining)))
  (if (endp remaining)
      selected
    (proof-with-checked-results
        ((entry (proof-list-of-length (car remaining) 4))
         (include (h4-book-run-entry-needed
                   (car entry) (cadr entry) needed final-source selected)))
      (if include
          (let ((source (cadddr entry))
                (counts (h4-book-run-sum-counts (caddr entry))))
            (proof-with-checked-results
                ((needed (h4-book-run-entry-facts entries source needed)))
              (h4-book-run-entry-sources-select
               (cdr remaining) entries needed final-source
               (cons (list counts source) selected))))
        (h4-book-run-entry-sources-select
         (cdr remaining) entries needed final-source selected)))))

(defun h4-book-run-entry-sources (p last final-source)
  (proof-with-checked-results ((needed (h4-book-run-proof-dependencies last)))
    (let ((entries (library-library-entries p)))
      (h4-book-run-entry-sources-select
       (reverse entries) entries needed final-source nil))))

(defun h4-book-run-line-chars (chars reversed mode)
  (declare (xargs :measure (acl2-count chars)))
  (cond
   ((endp chars) (and reversed (list (coerce (reverse reversed) 'string))))
   ((and (not (eq mode :file)) (eql (car chars) #\Return))
    (let ((crlf (eql (cadr chars) #\Newline)))
      (cons (coerce (reverse (cond ((eq mode :text) (cons #\Newline reversed))
                                   (crlf (list* #\Newline #\Return reversed))
                                   (t (cons #\Return reversed))))
                    'string)
            (if crlf
                (h4-book-run-line-chars (cddr chars) nil mode)
              (h4-book-run-line-chars (cdr chars) nil mode)))))
   ((or (eql (car chars) #\Newline)
        (and (eq mode :text) (member-equal (char-code (car chars)) '(11 12 28 29 30))))
    (cons (coerce (reverse (cons (car chars) reversed)) 'string)
          (h4-book-run-line-chars (cdr chars) nil mode)))
   (t (h4-book-run-line-chars
       (cdr chars) (cons (car chars) reversed) mode))))

(defun h4-book-run-lines (source mode)
  (h4-book-run-line-chars (coerce source 'list) nil mode))

(defund h4-book-run-catalogue-intern (raw catalogue)
  (let ((cached (assoc-equal raw (cadr catalogue))))
    (if cached
        (cons (cdr cached) catalogue)
      (proof-with-checked-results ((statement (h4-book-run-parse-statement raw)))
        (let* ((index (caddr catalogue))
               (indexed (list index statement)))
          (cons indexed (list (cons statement (car catalogue))
                              (table-put (cadr catalogue) raw indexed)
                              (1+ index) (cadddr catalogue))))))))

(defun h4-book-run-earlier-intersection (old earlier)
  (cond
   ((endp old) nil)
   ((member-equal (car old) earlier)
    (cons (car old) (h4-book-run-earlier-intersection (cdr old) earlier)))
   (t (h4-book-run-earlier-intersection (cdr old) earlier))))

(defun h4-book-run-catalogue-add-earlier (index earlier catalogue)
  (let* ((common (cadddr catalogue))
         (entry (assoc-equal index common))
         (shared (if entry (h4-book-run-earlier-intersection (cdr entry) earlier)
                   earlier)))
    (list (car catalogue) (cadr catalogue) (caddr catalogue)
          (table-put common index shared))))

(defund h4-book-run-catalogue-lines (lines library earlier obligations catalogue)
  (declare (xargs :measure (acl2-count lines)))
  (cond
   ((endp lines) (list (reverse earlier) obligations catalogue))
   ((member-equal (car lines) library)
    (h4-book-run-catalogue-lines (cdr lines) library earlier obligations catalogue))
   (t
    (proof-with-checked-results
        ((interned (h4-book-run-catalogue-intern (car lines) catalogue)))
      (let* ((index (caar interned))
             (name (h4-book-run-statement-name (cadar interned)))
             (catalogue (cdr interned)))
        (cond
         ((member-equal index earlier)
          (h4-book-run-catalogue-lines (cdr lines) library earlier obligations catalogue))
         (name
          (h4-book-run-catalogue-lines
           (cdr lines) library (cons index earlier) (1+ obligations)
           (h4-book-run-catalogue-add-earlier index earlier catalogue)))
         (t
          (h4-book-run-catalogue-lines
           (cdr lines) library (cons index earlier) obligations catalogue))))))))

(defun h4-book-run-aid-add (aids name value)
  (let ((previous (table-get aids name nil)))
    (if (member-equal value previous)
        aids
      (table-put aids name (append previous (list value))))))

(defund h4-book-run-aid-measures (lines measures)
  (declare (xargs :measure (acl2-count lines)))
  (cond
   ((endp lines) measures)
   ((text-starts-with (car lines) "(measure ")
    (proof-with-checked-results
        ((parsed (h4-book-run-read-line (car lines)))
         (fields (proof-list-of-length (cadr parsed) 4)))
      (h4-book-run-aid-measures
       (cdr lines) (h4-book-run-aid-add measures (car fields)
                                        (list (cadr fields) (caddr fields))))))
   (t (h4-book-run-aid-measures (cdr lines) measures))))

(defun h4-book-run-aid-hints (uses hints)
  (declare (xargs :measure (acl2-count uses)))
  (if (endp uses)
      hints
    (h4-book-run-aid-hints
     (cdr uses) (h4-book-run-aid-add hints (caar uses) (cadar uses)))))

(defun h4-book-run-model (arity label models)
  (let* ((key (list arity label))
         (entry (assoc-equal key models)))
    (if entry (cdr entry) '(:failure "failure" ""))))

(defun h4-book-run-witness-functions (signatures)
  (if (endp signatures)
      nil
    (proof-with-checked-results
        ((signature (proof-list-of-length (car signatures) 2))
         (names (h4-book-run-witness-functions (cdr signatures))))
      (cons (car signature) names))))

(defun h4-book-run-witness-choice (signatures label models)
  (if (endp signatures)
      nil
    (proof-with-checked-results
        ((name (h4-book-run-model (cadar signatures) label models))
         (names (h4-book-run-witness-choice (cdr signatures) label models)))
      (cons name names))))

(defun h4-book-run-witness-alternatives (signatures models)
  (if (endp signatures)
      nil
    (let ((arity (cadar signatures)))
      (proof-with-checked-results
          ((yes (h4-book-run-model arity "T" models))
           (no (h4-book-run-model arity "NIL" models))
           (rest (h4-book-run-witness-alternatives (cdr signatures) models)))
        (cons (list yes no) rest)))))

(defun h4-book-run-product-prefix (name tails)
  (if (endp tails)
      nil
    (cons (cons name (car tails))
          (h4-book-run-product-prefix name (cdr tails)))))

(defun h4-book-run-product-choices (names tails)
  (if (endp names)
      nil
    (append (h4-book-run-product-prefix (car names) tails)
            (h4-book-run-product-choices (cdr names) tails))))

(defun h4-book-run-witness-product (alternatives)
  (if (endp alternatives)
      (list nil)
    (h4-book-run-product-choices
     (car alternatives) (h4-book-run-witness-product (cdr alternatives)))))

(defun h4-book-run-witness-choices (signatures models)
  (proof-with-checked-results
      ((yes (h4-book-run-witness-choice signatures "T" models))
       (no (h4-book-run-witness-choice signatures "NIL" models))
       (alternatives (and (<= (len signatures) 4)
                          (h4-book-run-witness-alternatives signatures models))))
    (let ((choices (cons yes (cons no (and (<= (len signatures) 4)
                                          (h4-book-run-witness-product alternatives))))))
      (if (and (equal (len signatures) 1) (< 0 (cadar signatures)))
          (proof-with-checked-results
              ((first (h4-book-run-model (cadar signatures) "first argument" models)))
            (append choices (list (list first))))
        choices))))

(defun h4-book-run-witness-assignment (functions witnesses assignment)
  (declare (xargs :measure (acl2-count functions)))
  (if (or (endp functions) (endp witnesses))
      assignment
    (h4-book-run-witness-assignment
     (cdr functions) (cdr witnesses)
     (table-put assignment (car functions) (car witnesses)))))

(defun h4-book-run-unproved-p (result)
  (and (failure-p result) (equal (cadr result) "unproved")))

; Proof production calls the book tactics on the parsed inputs.

(defund h4-book-run-collect-aids (manifest sources measures hints)
  (declare (xargs :measure (acl2-count manifest)))
  (if (endp manifest)
      (list measures hints)
    (proof-with-checked-results ((item (proof-list-of-length (car manifest) 2)))
      (let ((source (assoc-equal (car item) sources)))
        (if source
            (let ((lines (h4-book-run-lines (cdr source) :file)))
              (proof-with-checked-results
                  ((measures (h4-book-run-aid-measures lines measures))
                   (uses (h4-book-hints-hint-uses lines)))
                (h4-book-run-collect-aids
                 (cdr manifest) sources measures (h4-book-run-aid-hints uses hints))))
          (h4-book-run-collect-aids (cdr manifest) sources measures hints))))))

(defun h4-book-run-book-search-prove (search formula induction given)
  (let ((result (h4-book-tactics-book-search-prove search formula induction given)))
    (if (failure-p result) (cons result search) result)))

(defun h4-book-run-witness-proof-evaluation (p target witnesses)
  (proof-with-checked-results ((fits (h4-book-tactics-fits target 2400)))
    (if (not fits)
        '(:failure "unproved" "")
      (proof-with-checked-results
          ((equality (h4-tactics-tactics-normalize
                      p target nil (append *h4-book-tactics-logic* witnesses) nil nil))
           (literal (proof-step-first equality))
           (value (proof-term-at literal 2)))
        (and (proof-is-call value *proof-quote*)
             (not (equal value *proof-false*))
             (h4-tactics-tactics-non-nil p equality))))))

(defund h4-book-run-witness-proof-prove (formula p search assignment witnesses)
  (let ((target (h4-book-run-replace-functions formula assignment)))
    (if (failure-p target)
        (cons target search)
      (let ((proof (h4-book-run-witness-proof-evaluation p target witnesses)))
        (if proof
            (cons proof search)
          (h4-book-run-book-search-prove search target nil nil))))))

(defund h4-book-run-witness-constraints
    (constraints p search assignment witnesses reversed)
  (declare (xargs :measure (acl2-count constraints)))
  (if (endp constraints)
      (cons (reverse reversed) search)
    (let ((constraint (proof-list-of-length (car constraints) 2)))
      (if (failure-p constraint)
          (cons constraint search)
        (let ((proved (h4-book-run-witness-proof-prove
                       (cadr constraint) p search assignment witnesses)))
          (if (failure-p (car proved))
              proved
            (h4-book-run-witness-constraints
             (cdr constraints) p (cdr proved) assignment witnesses
             (cons (car proved) reversed))))))))

(defun h4-book-run-witness-attempts (choices functions constraints p search)
  (declare (xargs :measure (acl2-count choices)))
  (if (endp choices)
      '(:failure "unproved" "")
    (let* ((witnesses (car choices))
           (assignment (h4-book-run-witness-assignment functions witnesses nil))
           (attempted (h4-book-run-witness-constraints
                       constraints p search assignment witnesses nil))
           (proofs (car attempted)))
      (cond
       ((h4-book-run-unproved-p proofs)
        (h4-book-run-witness-attempts (cdr choices) functions constraints p (cdr attempted)))
       ((failure-p proofs) proofs)
       (t (list witnesses proofs))))))

(defun h4-book-run-witness-proof-with-templates (p fields models tables)
  (proof-with-checked-results
      ((parts (proof-list-of-length fields 2))
       (functions (h4-book-run-witness-functions (car parts)))
       (choices (h4-book-run-witness-choices (car parts) models))
       (search (h4-book-tactics-book-search-init-with-templates p tables)))
    (h4-book-run-witness-attempts (proof-unique choices) functions (cadr parts) p search)))

(defun h4-book-run-search-theorem-with-templates (p formula name hints book-functions tables)
  (proof-with-checked-results
      ((search (h4-book-tactics-book-search-init-with-templates p tables))
       (explicit (h4-book-hints-hint-facts p (table-get hints name nil) book-functions))
       (setoid (h4-book-equivalence-setoid-proof search formula))
       (proof (car setoid)))
    (cond
     (proof proof)
     (explicit
      (let* ((attempted (h4-book-run-book-search-prove (cdr setoid) formula t explicit))
             (result (car attempted)))
        (if (or (null result) (h4-book-run-unproved-p result))
            (car (h4-book-run-book-search-prove (cdr attempted) formula t nil))
          result)))
     (t (car (h4-book-run-book-search-prove (cdr setoid) formula t nil))))))

(defun h4-book-run-theorem-after-conversions-with-templates
    (p formula name hints conversions book-functions tables)
  (proof-with-checked-results
      ((step (or (h4-book-arity-arity-proof p formula)
                 (h4-book-hanoi-hanoi-proof-with-book-functions
                  p formula (table-get hints name nil) book-functions)
                 (h4-book-run-search-theorem-with-templates p formula name hints book-functions tables))))
    (list step p conversions)))

(defun h4-book-run-theorem-conversions-with-templates
    (p formula name hints ordering conversions book-functions tables)
  (proof-with-checked-results
      ((expanded (h4-book-expansion-expansion-proofs-prove
                  (car conversions) p formula ordering)))
    (let* ((expansions (cadr expanded))
           (inverse (h4-book-inverse-inversion-proofs-with-expansions (cadr conversions) expansions))
           (p (caddr expanded)))
      (if (car expanded)
          (list (car expanded) p (list expansions inverse))
        (proof-with-checked-results
            ((inverted (h4-book-inverse-inversion-proofs-prove inverse p formula ordering)))
          (let* ((inverse (cadr inverted))
                 (conversions
                  (list (h4-book-inverse-inversion-proofs-expansions inverse) inverse))
                 (p (caddr inverted)))
            (if (car inverted)
                (list (car inverted) p conversions)
              (h4-book-run-theorem-after-conversions-with-templates
               p formula name hints conversions book-functions tables))))))))

(defun h4-book-run-theorem-with-templates
    (p formula name hints printing ordering conversions book-functions tables)
  (proof-with-checked-results ((packed (h4-book-printing-packing-proof p formula printing)))
    (let ((p (cdr packed)))
      (proof-with-checked-results
          ((proof
            (or (car packed)
                (h4-book-alists-keyed-removal-proof-with-templates p formula tables)
                (h4-book-updates-list-update-proof p formula)
                (h4-book-updates-swap-proof p formula)
                (h4-book-updates-append-suffix-proof p formula)
                (h4-book-flatten-append-map-proof p formula)
                (h4-book-sets-set-proof p formula)
                (h4-book-list-types-member-type-proof p formula)
                (h4-book-finite-finite-comparison-proof p formula)
                (h4-book-evaluation-closed-proof p formula)
                (h4-book-folds-fold-proof p formula)
                (h4-book-accumulator-reverse-accumulator-proof p formula)
                (h4-book-order-ordinal-proof p formula ordering)
                (h4-book-compression-compression-proof p formula ordering))))
        (if proof
            (list proof p conversions)
          (h4-book-run-theorem-conversions-with-templates
           p formula name hints ordering conversions book-functions tables))))))

(defun h4-book-run-find-proof-with-templates
    (p statement measures hints models printing ordering conversions book-functions tables)
  (let ((kind (h4-book-run-statement-kind statement))
        (fields (h4-book-run-statement-fields statement)))
    (cond
     ((equal kind "define")
      (let ((definitions (cdr fields))
            (calls (h4-book-run-statement-calls statement)))
        (proof-with-checked-results
            ((explicit (h4-book-numeric-measures-numeric-termination
                        p definitions calls printing))
             (measured
              (or (car explicit)
                  (h4-book-measures-termination-proof
                   (cdr explicit) definitions calls measures book-functions))))
          (list (cons "measure" measured) (cdr explicit) conversions))))
     ((equal kind "constrain")
      (proof-with-checked-results
          ((witnessed (h4-book-run-witness-proof-with-templates p fields models tables)))
        (list (cons "witness" witnessed) p conversions)))
     (t
      (proof-with-checked-results
          ((formula (proof-term-at fields 1))
           (theorem
            (h4-book-run-theorem-with-templates
             p formula (h4-book-run-statement-name statement) hints
             printing ordering conversions book-functions tables)))
        (cons (list "theorem" nil (list (car theorem))) (cdr theorem)))))))

(defun h4-book-run-find-proof-with-context
    (p statement measures hints models printing ordering conversions book-functions)
  (h4-book-run-find-proof-with-templates
   p statement measures hints models printing ordering conversions book-functions nil))

(defun h4-book-run-selected-sources (selected)
  (if (endp selected)
      nil
    (cons (cadar selected) (h4-book-run-selected-sources (cdr selected)))))

(defun h4-book-run-proof-sources (p proofs source)
  (declare (xargs :measure (acl2-count proofs)))
  (if (endp proofs)
      nil
    (proof-with-checked-results
        ((selected (h4-book-run-entry-sources p (car proofs) source))
         (remaining (h4-book-run-proof-sources p (cdr proofs) source)))
      (append (h4-book-run-selected-sources selected) remaining))))

(defun h4-book-run-entry-support (entries relevant)
  (cond
   ((endp entries) nil)
   ((member-equal (cadddr (car entries)) relevant)
    (cons (cadddr (car entries)) (h4-book-run-entry-support (cdr entries) relevant)))
   (t (h4-book-run-entry-support (cdr entries) relevant))))

(defun h4-book-run-prove-statement-with-context
    (p statement measures hints models printing ordering conversions book-functions)
  (proof-with-checked-results
      ((closed (and (equal (h4-book-run-statement-kind statement) "theorem")
                    (proof-with-checked-results
                        ((formula (proof-term-at (h4-book-run-statement-fields statement) 1)))
                      (h4-book-evaluation-closed-goal formula))))
       (result (h4-book-run-find-proof-with-context
                p statement measures hints models printing ordering conversions book-functions)))
    (let* ((proof (car result))
           (proofs (caddr proof))
           (p (cadr result))
           (conversions (caddr result)))
      (proof-with-checked-results
          ((entry (h4-book-encoding-book-entry
                   (car proof) (h4-book-run-statement-name statement) (cadr proof) proofs))
           (relevant (h4-book-run-proof-sources p proofs (cadr entry))))
        (let ((support (h4-book-run-entry-support (library-library-entries p) relevant)))
          (list (h4-book-run-make-certificate (cadr entry) (car entry) support "")
                p conversions))))))

(defund h4-book-run-generate-books-admit (kind fields p book-functions)
  (proof-with-checked-results ((p (h4-tactics-tactics-add-statement p kind fields)))
    (cond
     ((equal kind "constrain")
      (proof-with-checked-results
          ((signatures (proof-term-at fields 0))
           (names (h4-book-run-witness-functions signatures)))
        (cons p (union-equal names book-functions))))
     ((equal kind "choose")
      (proof-with-checked-results ((name (proof-term-at fields 0)))
        (cons p (add-to-set-equal name book-functions))))
     (t (cons p book-functions)))))

(defun h4-book-run-admit-earlier (indices common statements p book-functions)
  (declare (xargs :measure (acl2-count indices)))
  (cond
   ((endp indices) (cons p book-functions))
   ((member-equal (car indices) common)
    (let ((item (nth (car indices) statements)))
      (proof-with-checked-results
          ((admitted (h4-book-run-generate-books-admit
                      (h4-book-run-statement-kind item)
                      (h4-book-run-statement-fields item)
                      p book-functions)))
        (h4-book-run-admit-earlier
         (cdr indices) common statements (car admitted) (cdr admitted)))))
   (t (h4-book-run-admit-earlier (cdr indices) common statements p book-functions))))

(defund h4-book-run-statement-needs-support (statement mode)
  (proof-with-checked-results
      ((theoremp (equal (h4-book-run-statement-kind statement) "theorem"))
       (formula (and theoremp (proof-term-at (h4-book-run-statement-fields statement) 1))))
    (if (eq mode :printing)
        (or (and theoremp (h4-book-printing-packing-formula formula))
            (h4-book-numeric-measures-uses-floor-measure
             (h4-book-run-statement-calls statement)))
      (and theoremp
           (or (h4-book-order-ordinal-candidate formula)
               (h4-book-compression-compression-shape formula)
               (h4-book-expansion-expansion-shape formula)
               (h4-book-inverse-inverse-shape formula))))))

(defund h4-book-run-book-needs-support (indices statements mode)
  (declare (xargs :measure (acl2-count indices)))
  (and (consp indices)
       (or (h4-book-run-statement-needs-support (nth (car indices) statements) mode)
           (h4-book-run-book-needs-support (cdr indices) statements mode))))

(defun h4-book-run-skip-certificate (statement reason)
  (proof-with-checked-results
      ((source (proof-line "skip" (list (h4-book-run-statement-name statement)))))
    (h4-book-run-make-certificate source 0 nil reason)))

(defun h4-book-run-attempt-certificate (p statement options conversions book-functions)
  (let ((result (h4-book-run-prove-statement-with-context
                 p statement (car options) (cadr options) (caddr options)
                 (cadddr options) (nth 4 options) conversions book-functions)))
    (if (h4-book-run-unproved-p result)
        (proof-with-checked-results
            ((certificate (h4-book-run-skip-certificate statement "unproved")))
          (list certificate p conversions))
      result)))

(defund h4-book-run-certificate-for-index
    (index statement catalogued origins prepared progress)
  (let* ((cache (caddr progress))
         (entry (assoc-equal index cache)))
    (if entry
        (cons (cdr entry) progress)
      (let* ((origin (table-get origins index nil))
             (previous (take (cadr origin) (table-get (cadr catalogued) (car origin) nil)))
             (common (table-get (caddr catalogued) index nil))
             (base (cadr prepared))
             (p (library-library-with-proof (car progress) (car base)))
             (conversions (cadr progress)))
        (proof-with-checked-results
            ((admitted (h4-book-run-admit-earlier
                        previous common (car catalogued) p (cadr base)))
             (result (h4-book-run-attempt-certificate
                      (car admitted) statement (caddr prepared) conversions (cdr admitted))))
          (let ((certificate (car result)))
            (cons certificate
                  (list (cadr result) (caddr result)
                        (table-put cache index certificate)))))))))

(defun h4-book-run-certificate-extras (support prelude used)
  (cond
   ((endp support) nil)
   ((or (member-equal (car support) prelude) (member-equal (car support) used))
    (h4-book-run-certificate-extras (cdr support) prelude used))
   (t (cons (car support) (h4-book-run-certificate-extras (cdr support) prelude used)))))

(defun h4-book-run-used-prelude (prelude used)
  (cond
   ((endp prelude) nil)
   ((member-equal (car prelude) used)
    (cons (car prelude) (h4-book-run-used-prelude (cdr prelude) used)))
   (t (h4-book-run-used-prelude (cdr prelude) used))))

(defund h4-book-run-certificate-row (book statement certificate)
  (proof-with-checked-results
      ((name (proof-write (h4-book-run-statement-name statement))))
    (let ((reason (h4-book-run-certificate-reason certificate)))
      (string-append
       (text-join *h4-book-run-tab*
                (list book name (if (equal reason "") "proved" "skipped")
                      (decimal-text (h4-book-run-certificate-steps certificate))
                      (decimal-text (length (h4-book-run-certificate-proof certificate))) reason))
       *h4-book-run-newline*))))

(defun h4-book-run-count-skipped-rows (rows)
  (if (endp rows)
      0
    (+ (if (<= 0 (text-find (car rows)
                          (concatenate 'string *h4-book-run-tab* "skipped" *h4-book-run-tab*)))
           1
         0)
       (h4-book-run-count-skipped-rows (cdr rows)))))

(defund h4-book-run-assemble-book
    (indices book catalogued origins prepared progress pieces rows used)
  (declare (xargs :measure (acl2-count indices)))
  (let ((prelude (cadddr prepared)))
    (if (endp indices)
        (cons (list book
                    (text-join "" (append (h4-book-run-used-prelude prelude used) (reverse pieces)))
                    (reverse rows) (h4-book-run-count-skipped-rows rows))
              progress)
      (let ((statement (nth (car indices) (car catalogued))))
        (if (null (h4-book-run-statement-name statement))
            (h4-book-run-assemble-book
             (cdr indices) book catalogued origins prepared progress pieces rows used)
          (proof-with-checked-results
              ((result (h4-book-run-certificate-for-index
                        (car indices) statement catalogued origins prepared progress))
               (row (h4-book-run-certificate-row book statement (car result))))
            (let* ((certificate (car result))
                   (support (h4-book-run-certificate-support certificate))
                   (extras (h4-book-run-certificate-extras support prelude used)))
              (h4-book-run-assemble-book
               (cdr indices) book catalogued origins prepared (cdr result)
               (cons (h4-book-run-certificate-proof certificate) (revappend extras pieces))
               (cons row rows) (union-equal support used)))))))))

