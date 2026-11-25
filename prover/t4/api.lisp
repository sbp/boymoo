(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-api-prefix* "T4")
(defconst *t4-api-newline* (coerce (list #\Newline) 'string))

(defconst *t4-api-ground-recursive*
  '(("sym" "ACL2" "ACL2-COUNT")
    ("sym" "ACL2" "CHARACTER-LISTP")
    ("sym" "ACL2" "LEN")
    ("sym" "ACL2" "MAKE-CHARACTER-LIST")
    ("sym" "ACL2" "MEMBER-EQ-EXEC")
    ("sym" "ACL2" "MEMBER-EQUAL")
    ("sym" "ACL2" "MEMBER-SYMBOL-NAME")
    ("sym" "ACL2" "MV-NTH")
    ("sym" "ACL2" "NO-DUPLICATESP-EQ-EXEC")
    ("sym" "ACL2" "NO-DUPLICATESP-EQUAL")
    ("sym" "ACL2" "O-P")
    ("sym" "ACL2" "O<")
    ("sym" "ACL2" "SYMBOL-LISTP")
    ("sym" "ACL2" "TRUE-LISTP")))

(defconst *t4-api-ground-packages*
  '("ACL2" "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL" "COMMON-LISP" "KEYWORD"))

(defun t4-api-ground ()
  (list (proof-proof-init) *t4-api-ground-recursive* *t4-api-ground-packages*))

(defun t4-api-init-proof (instance)
  (proof-proof-with-kind (proof-proof-init) (proof-proof-kind instance)))

(defun t4-api-line (value)
  (if (stringp value)
      (if (text-ends-with value *t4-api-newline*)
          value
        (string-append value *t4-api-newline*))
    '(:failure "failure" "")))

(defun t4-api-read (raw)
  (proof-with-checked-results
      ((result (reader-reader-line (reader-reader (seq-slice raw 0 -1)))))
    (list (caar result) (proof-freeze (cadar result)))))

(defun t4-api-obligation (kind data)
  (t4-bookrun-obligation kind data))

(defun t4-api-recursive-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3))
                                 (rest (t4-api-recursive-names (cdr definitions))))
      (cons (car definition) rest))))

(defun t4-api-recursive (kind data)
  (if (equal kind "define")
      (proof-with-checked-results ((name (t4-api-obligation kind data)))
        (if name
            (t4-api-recursive-names (cdr data))
          nil))
    nil))

(defun t4-api-statement-from-read (parsed)
  (proof-with-checked-results ((recursive (t4-api-recursive (car parsed) (cadr parsed))))
    (list (car parsed) (cadr parsed) recursive)))

(defun t4-api-statement (raw)
  (proof-with-checked-results ((parsed (t4-api-read raw)))
    (t4-api-statement-from-read parsed)))

(defun t4-api-enabled-functions (hints)
  (t4-bookrun-enabled-functions hints))

(defun t4-api-aids-lines (lines stored hints)
  (if (endp lines)
      (list stored hints)
    (proof-with-checked-results ((parsed (t4-api-read (t4-api-line (car lines)))))
      (let ((kind (car parsed))
            (data (cadr parsed)))
        (cond
         ((equal kind "measure")
          (proof-with-checked-results ((name (proof-term-at data 0)))
            (t4-api-aids-lines (cdr lines)
                              (table-put stored name (seq-slice data 1 3))
                              hints)))
         ((equal kind "hints")
          (proof-with-checked-results ((forms (proof-term-at data 1))
                                       (name (proof-term-at data 0)))
            (t4-api-aids-lines (cdr lines) stored
                              (table-put hints name (t4-api-enabled-functions forms)))))
         (t (t4-api-aids-lines (cdr lines) stored hints)))))))

(defun t4-api-aids (lines)
  (t4-api-aids-lines lines nil nil))

(defun t4-api-byte-space-p (c)
  (let ((code (char-code c)))
    (or (= code 32) (and (<= 9 code) (<= code 13)))))

(defun t4-api-first-byte-line (chars reversed)
  (cond
   ((endp chars) (coerce (reverse reversed) 'string))
   ((eql (car chars) #\Newline)
    (coerce (revappend reversed (list #\Newline)) 'string))
   ((eql (car chars) #\Return)
    (coerce (revappend reversed (if (and (consp (cdr chars))
                                         (eql (cadr chars) #\Newline))
                                    (list #\Return #\Newline)
                                  (list #\Return)))
            'string))
   (t (t4-api-first-byte-line (cdr chars) (cons (car chars) reversed)))))

(defun t4-api-sections (source)
  (t4-bookrun-sections source))

(defun t4-api-hex-digit-p (c)
  (let ((code (char-code c)))
    (or (and (<= 48 code) (<= code 57))
        (and (<= 65 code) (<= code 70)))))

; A successful token scan pairs the reversed token with the unread characters.
(defun t4-api-quoted-token (chars close reversed)
  (cond
   ((endp chars) nil)
   ((eql (car chars) close) (cons (cons close reversed) (cdr chars)))
   ((eql (car chars) #\\)
    (if (and (consp (cdr chars)) (consp (cddr chars))
             (t4-api-hex-digit-p (cadr chars)) (t4-api-hex-digit-p (caddr chars)))
        (t4-api-quoted-token (cdddr chars) close
                             (list* (caddr chars) (cadr chars) #\\ reversed))
      nil))
   (t (t4-api-quoted-token (cdr chars) close (cons (car chars) reversed)))))

(defun t4-api-symbol-token (n chars reversed)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "t4-api-symbol-token"))
   ((endp chars) (if reversed (cons reversed chars) nil))
   ((eql (car chars) #\|)
    (let ((part (t4-api-quoted-token (cdr chars) #\| (cons #\| reversed))))
      (if part
          (t4-api-symbol-token (1- n) (cdr part) (car part))
        (if reversed (cons reversed chars) nil))))
   ((or (member-equal (car chars) '(#\( #\) #\"))
        (t4-api-byte-space-p (car chars)))
    (if reversed (cons reversed chars) nil))
   (t (t4-api-symbol-token (1- n) (cdr chars) (cons (car chars) reversed)))))

(defun t4-api-rename-characters (n chars names reversed)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "t4-api-rename-characters"))
   ((endp chars) (coerce (reverse reversed) 'string))
   (t
    (proof-with-checked-results
        ((token (if (eql (car chars) #\")
                    (t4-api-quoted-token (cdr chars) #\" (list #\"))
                  (t4-api-symbol-token 1000000 chars nil))))
      (if (not token)
          (t4-api-rename-characters (1- n) (cdr chars) names (cons (car chars) reversed))
        (let ((replacement (assoc-equal (coerce (reverse (car token)) 'string) names)))
          (t4-api-rename-characters
           (1- n) (cdr token) names
           (if replacement
               (revappend (coerce (cdr replacement) 'list) reversed)
             (append (car token) reversed)))))))))

(defun t4-api-rename (source names)
  (if (endp names)
      source
    (t4-api-rename-characters 1000000 (coerce source 'list) names nil)))

(defun t4-api-join-sections (sections)
  (if (endp sections)
      nil
    (cons (text-join "" (car sections)) (t4-api-join-sections (cdr sections)))))

(defun t4-api-block-head (block)
  (let ((newline (text-find block *t4-api-newline*)))
    (if (< newline 0)
        (string-append block *t4-api-newline*)
      (seq-slice block 0 (1+ newline)))))

(defun t4-api-entry-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results ((name (proof-term-at (car definitions) 0))
                                 (rest (t4-api-entry-definition-names (cdr definitions))))
      (cons name rest))))

(defun t4-api-auxiliary-measure (blocks raw head declared)
  (if (and (consp (cddr blocks)) (text-starts-with (cadr blocks) "(measure "))
      (proof-with-checked-results
          ((measure (t4-api-read (t4-api-first-byte-line (coerce (cadr blocks) 'list) nil)))
           (measured (proof-term-at (cadr measure) 0))
           (first (proof-term-at declared 0)))
        (if (equal measured first)
            (list (string-append raw (cadr blocks)) head declared (cddr blocks))
          (list raw head declared (cdr blocks))))
    (list raw head declared (cdr blocks))))

(defun t4-api-auxiliary-block (blocks)
  (let* ((raw (car blocks))
         (head (t4-api-block-head raw)))
    (proof-with-checked-results ((parsed (t4-api-read head)))
      (let ((kind (car parsed))
            (data (cadr parsed)))
        (cond
         ((equal kind "define")
          (proof-with-checked-results
              ((declared (t4-api-entry-definition-names (cdr data))))
            (t4-api-auxiliary-measure blocks raw head declared)))
         ((equal kind "lemma")
          (proof-with-checked-results ((name (proof-term-at data 0)))
            (list raw head (list name) (cdr blocks))))
         (t '(:failure "failure" "")))))))

(defun t4-api-declarations-have-name-p (declared declarations)
  (and (consp declared)
       (or (if (assoc-equal (car declared) declarations) t nil)
           (t4-api-declarations-have-name-p (cdr declared) declarations))))

(defun t4-api-declarations-agree-p (declared declarations head)
  (or (endp declared)
      (and (equal (table-get declarations (car declared) nil) head)
           (t4-api-declarations-agree-p (cdr declared) declarations head))))

(defun t4-api-auxiliary-name (name suffix)
  (proof-with-checked-results ((parts (proof-list-of-length name 3)))
    (let ((package (cadr parts))
          (old (caddr parts)))
      (if (not (stringp old))
          (if (integerp old)
              '(:failure "failure" "")
            '(:failure "failure" ""))
        (let ((stem (cond ((text-starts-with old "SELF-") (seq-slice old 5 :none))
                          ((text-starts-with old "T4-") (seq-slice old 3 :none))
                          (t old))))
          (proof-sym (text-join "" (list "PROVER-T4-" stem "-" suffix)) package))))))

(defun t4-api-auxiliary-declarations (declared head occupied suffix names declarations)
  (if (endp declared)
      (list names declarations)
    (let ((name (car declared)))
      (proof-with-checked-results ((replacement (t4-api-auxiliary-name name suffix)))
        (if (assoc-equal replacement occupied)
            '(:failure "failure" "")
          (proof-with-checked-results ((old-token (proof-write name))
                                       (new-token (proof-write replacement)))
            (t4-api-auxiliary-declarations
             (cdr declared) head occupied suffix
             (table-put names old-token new-token)
             (table-put declarations name head))))))))

(defun t4-api-target-entry (target names)
  (proof-with-checked-results ((parsed (t4-api-read (t4-api-block-head target)))
                               (name (proof-term-at (cadr parsed) 0))
                               (written (proof-write name)))
    (let ((opening (text-join "" (list "(" (car parsed) " " written))))
      (if (not (text-starts-with target opening))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((rest (t4-api-rename (seq-slice target (length opening) :none) names)))
          (string-append opening rest))))))

(defund t4-api-export-auxiliary (blocks occupied names declarations lemmas)
  (proof-with-checked-results ((block (t4-api-auxiliary-block blocks)))
    (let ((raw (car block))
          (head (cadr block))
          (declared (caddr block))
          (rest (cadddr block)))
      (if (t4-api-declarations-have-name-p declared declarations)
          (if (t4-api-declarations-agree-p declared declarations head)
              (list rest names declarations lemmas)
            '(:failure "failure" ""))
        (proof-with-checked-results
            ((contextual (t4-api-rename raw names))
             (bindings (t4-api-auxiliary-declarations
                        declared head occupied (text-upper (siphash-hexdigest contextual))
                        names declarations))
             (published (t4-api-rename contextual (car bindings))))
          (list rest (car bindings) (cadr bindings) (cons published lemmas)))))))

(defun t4-api-export-blocks (n blocks occupied names declarations lemmas)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "t4-api-export-blocks"))
   ((endp blocks) '(:failure "failure" ""))
   ((endp (cdr blocks))
    (proof-with-checked-results ((entry (t4-api-target-entry (car blocks) names)))
      (list (reverse lemmas) entry)))
   (t
    (proof-with-checked-results ((next (t4-api-export-auxiliary blocks occupied names declarations lemmas)))
      (t4-api-export-blocks (1- n) (car next) occupied (cadr next) (caddr next) (cadddr next))))))

(defun t4-api-entries (source occupied)
  (proof-with-checked-results ((sections (t4-api-sections source)))
    (t4-api-export-blocks 1000000 (t4-api-join-sections sections) occupied nil nil nil)))

(defun t4-api-admitted-definitions (proof definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      proof
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (t4-api-admitted-definitions
       (proof-proof-add-definition proof (car definition) (cadr definition) (caddr definition))
       (cdr definitions)))))

(defun t4-api-admitted-formulas (proof formulas)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      proof
    (proof-with-checked-results ((formula (proof-list-of-length (car formulas) 2)))
      (t4-api-admitted-formulas
       (proof-proof-with-facts
        proof (table-put (proof-proof-facts proof) (car formula) (cdr formula)))
       (cdr formulas)))))

(defun t4-api-admitted-proof (proof kind data)
  (cond ((equal kind "define")
         (t4-api-admitted-definitions proof (cdr data)))
        ((member-equal kind '("theorem" "axiom"))
         (t4-api-admitted-formulas proof (list data)))
        ((equal kind "constrain")
         (proof-with-checked-results ((formulas (proof-term-at data 1)))
           (if (proof-compound formulas)
               (t4-api-admitted-formulas proof formulas)
             proof)))
        (t proof)))

(defun t4-api-admitted-facts (proof kind data choices)
  (proof-with-checked-results ((proof (t4-api-admitted-proof proof kind data)))
    (if (eq choices :none)
        (list proof choices)
      (proof-with-checked-results ((available (t4-witness-available-choice proof kind data)))
        (list (cdr available)
              (if (car available) (append choices (list (car available))) choices))))))

(defun t4-api-update-set (set values)
  (declare (xargs :measure (acl2-count values)))
  (if (endp values)
      set
    (let ((value (car values)))
      (t4-api-update-set (if (member-equal value set) set (append set (list value)))
                         (cdr values)))))

(defun t4-api-unary-definitions-p (definitions)
  (if (endp definitions)
      t
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (let ((formals (cadr definition)))
        (and (proof-compound formals)
             (equal (len formals) 1)
             (t4-api-unary-definitions-p (cdr definitions)))))))

(defun t4-api-mutual-group (names group mutual)
  (if (endp names)
      mutual
    (t4-api-mutual-group (cdr names) group (table-put mutual (car names) group))))

(defun t4-api-register-package (tactic kind data)
  (if (member-equal kind '("package" "hidden-package"))
      (proof-with-checked-results ((field (proof-term-at data 0))
                                   (package (proof-term-at field 1)))
        (t4-booklogic-booklogic-with-packages
         tactic (t4-api-update-set (t4-booklogic-booklogic-packages tactic) (list package))))
    tactic))

(defun t4-api-register-evaluators (tactic kind data)
  (if (equal kind "constrain")
      (proof-with-checked-results ((formulas (proof-term-at data 1)))
        (if (proof-compound formulas)
            (proof-with-checked-results
                ((rules (t4-evaluation-evaluation-rules-register
                         (t4-booklogic-booklogic-evaluators tactic) data)))
              (t4-booklogic-booklogic-with-evaluators tactic rules))
          tactic))
    tactic))

(defun t4-api-register (tactic kind data recursive)
  (let ((tactic (t4-booklogic-booklogic-with-recursive
                 tactic (t4-api-update-set (t4-booklogic-booklogic-recursive tactic) recursive))))
    (proof-with-checked-results ((tactic (t4-api-register-package tactic kind data))
                                 (mutual (and (consp (cdr recursive))
                                              (t4-api-unary-definitions-p (cdr data)))))
      (let ((tactic
             (if mutual
                 (t4-booklogic-booklogic-with-mutual
                  tactic (t4-api-mutual-group recursive recursive
                                              (t4-booklogic-booklogic-mutual tactic)))
               tactic)))
        (t4-api-register-evaluators tactic kind data)))))

(defun t4-api-index-fact (tactic name)
  (let ((fact (assoc-equal name (proof-proof-facts (t4-booklogic-booklogic-proof tactic)))))
    (if fact
        (t4-booklogic-booklogic-index-fact tactic name (cdr fact))
      '(:failure "failure" ""))))

(defun t4-api-index-formulas (tactic formulas)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      tactic
    (proof-with-checked-results ((formula (proof-list-of-length (car formulas) 2))
                                 (tactic (t4-api-index-fact tactic (car formula))))
      (t4-api-index-formulas tactic (cdr formulas)))))

(defun t4-api-index-statement (tactic kind data)
  (cond ((member-equal kind '("theorem" "axiom"))
         (proof-with-checked-results ((name (proof-term-at data 0)))
           (t4-api-index-fact tactic name)))
        ((equal kind "constrain")
         (proof-with-checked-results ((formulas (proof-term-at data 1)))
           (if (proof-compound formulas)
               (t4-api-index-formulas tactic formulas)
             tactic)))
        (t tactic)))

(defun t4-api-admit-statement (tactic choices parsed)
  (proof-with-checked-results
      ((added (t4-api-admitted-facts (t4-booklogic-booklogic-proof tactic)
                                    (car parsed) (cadr parsed) choices))
       (tactic (t4-api-register (t4-booklogic-booklogic-with-proof tactic (car added))
                                (car parsed) (cadr parsed) (caddr parsed)))
       (tactic (t4-api-index-statement tactic (car parsed) (cadr parsed))))
    (list tactic (cadr added))))

(defun t4-api-admit (tactic choices raw)
  (proof-with-checked-results ((parsed (t4-api-statement raw)))
    (t4-api-admit-statement tactic choices parsed)))

(defun t4-api-normalize-lines (lines)
  (if (endp lines)
      nil
    (proof-with-checked-results ((raw (t4-api-line (car lines)))
                                 (rest (t4-api-normalize-lines (cdr lines))))
      (cons raw rest))))

(defun t4-api-given-proof-loop (lines proof seen choices keep-records records)
  (declare (xargs :measure (acl2-count lines)))
  (cond
   ((endp lines)
    (if keep-records
        (list proof (reverse seen) choices (reverse records))
      (list proof (reverse seen) choices)))
   ((member-equal (car lines) seen)
    (t4-api-given-proof-loop (cdr lines) proof seen choices keep-records records))
   (t
    (proof-with-checked-results
        ((parsed (t4-api-read (car lines)))
         (added (t4-api-admitted-facts proof (car parsed) (cadr parsed) choices)))
      (t4-api-given-proof-loop (cdr lines) (car added) (cons (car lines) seen) (cadr added)
                              keep-records (if keep-records (cons parsed records) records))))))

(defun t4-api-given-proof (lines proof seen choices)
  (t4-api-given-proof-loop lines proof seen choices nil nil))

(defun t4-api-register-line-sequence (tactic lines parsed-p)
  (declare (xargs :measure (acl2-count lines)))
  (if (endp lines)
      tactic
    (proof-with-checked-results
        ((parsed (if parsed-p
                     (t4-api-statement-from-read (car lines))
                   (t4-api-statement (car lines))))
         (tactic (t4-api-register tactic (car parsed) (cadr parsed) (caddr parsed))))
      (t4-api-register-line-sequence tactic (cdr lines) parsed-p))))

(defun t4-api-register-lines (tactic lines)
  (t4-api-register-line-sequence tactic lines nil))

(defun t4-api-sexp-string-chars (chars reversed)
  (if (endp chars)
      (coerce (revappend reversed (list #\")) 'string)
    (let ((c (car chars)))
      (t4-api-sexp-string-chars
       (cdr chars)
       (if (or (eql c #\\) (eql c #\"))
           (list* c #\\ reversed)
         (cons c reversed))))))

(defun t4-api-sexp-line-keys (lines)
  (if (endp lines)
      nil
    (let ((key (t4-api-sexp-string-chars (coerce (car lines) 'list) (list #\"))))
      (cons (cons key (car lines)) (t4-api-sexp-line-keys (cdr lines))))))

(defun t4-api-sorted-lines (lines)
  (table-values (seq-sorted (t4-api-sexp-line-keys lines))))

(defun t4-api-register-ground (tactic ground)
  (let ((tactic (t4-booklogic-booklogic-with-recursive
                 tactic (t4-api-update-set (t4-booklogic-booklogic-recursive tactic)
                                           (cadr ground)))))
    (t4-booklogic-booklogic-with-packages
     tactic (t4-api-update-set (t4-booklogic-booklogic-packages tactic) (caddr ground)))))

(defun t4-api-given (lines)
  (let ((ground (t4-api-ground)))
    (proof-with-checked-results
        ((lines (t4-api-normalize-lines lines))
         (given (t4-api-given-proof lines (t4-api-init-proof nil) nil nil))
         (tactic (t4-booklogic-booklogic-init (car given)))
         (tactic (t4-api-register-lines (t4-api-register-ground tactic ground) (cadr given))))
      (list tactic (t4-api-sorted-lines (cadr given)) (caddr given)))))

(defun t4-api-prepared-given (lines)
  (let ((ground (t4-api-ground)))
    (proof-with-checked-results
        ((lines (t4-api-normalize-lines lines))
         (given (t4-api-given-proof-loop lines (car ground) nil nil t nil))
         (tactic (t4-booklogic-booklogic-init-with-proof (car given)))
         (tactic (t4-api-register-line-sequence (t4-api-register-ground tactic ground)
                                               (cadddr given) t)))
      (list tactic (cadr given) (caddr given)))))

(defun t4-api-clone (base)
  base)

(defun t4-api-earlier (lines tactic seen choices)
  (declare (xargs :measure (acl2-count lines)))
  (if (endp lines)
      (list tactic seen choices)
    (proof-with-checked-results ((raw (t4-api-line (car lines))))
      (if (member-equal raw seen)
          (t4-api-earlier (cdr lines) tactic seen choices)
        (proof-with-checked-results ((admitted (t4-api-admit tactic choices raw)))
          (t4-api-earlier (cdr lines) (car admitted) (cons raw seen) (cadr admitted)))))))

(defun t4-api-prefix-proof (tactic)
  (let ((ground (t4-api-init-proof nil))
        (source (t4-booklogic-booklogic-proof tactic)))
    (proof-make-proof
     (table-update (proof-proof-facts ground) (proof-proof-facts source))
     (table-update (proof-proof-definitions ground) (proof-proof-definitions source))
     (proof-proof-primitives ground))))

(defun t4-api-line-sequence (value)
  (cond ((true-listp value) value)
        ((equal value "") nil)
        (t '(:failure "failure" ""))))

(defun t4-api-proof-answer (prefix tactic choices raw parsed name supplied)
  (proof-with-checked-results
      ((result (t4-slice-book-entry prefix tactic choices raw (car parsed) (cadr parsed) name
                                   (car supplied) (cadr supplied))))
    (let ((entry (car result)))
      (if (equal (t4-bookrun-entry-reason entry) "")
          (t4-api-entries (t4-bookrun-entry-source entry) (proof-proof-facts (cdr result)))
        nil))))

(defun t4-api-prove-core (statement earlier library aids)
  (proof-with-checked-results ((raw (t4-api-line statement))
                               (parsed (t4-api-read raw))
                               (name (t4-api-obligation (car parsed) (cadr parsed))))
    (if (not name)
        nil
      (proof-with-checked-results
          ((library (t4-api-line-sequence library))
           (given (t4-api-given library))
           (tactic (t4-api-clone (car given)))
           (earlier (t4-api-line-sequence earlier))
           (extended (t4-api-earlier earlier tactic (cadr given) (caddr given))))
        (if (member-equal raw (cadr extended))
            nil
          (proof-with-checked-results
              ((aids (t4-api-line-sequence aids))
               (supplied (t4-api-aids aids)))
            (t4-api-proof-answer (t4-api-prefix-proof (car extended)) (car extended)
                                 (caddr extended) raw parsed name supplied)))))))

(defun t4-api-prove (statement earlier library aids)
  (let ((result (t4-api-prove-core statement earlier library aids)))
    (if (failure-p result) nil result)))
