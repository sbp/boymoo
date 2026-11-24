(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t2-api-names-token* '(#\Space #\( #\) #\Return #\Newline))

(defun t2-api-names-parsed (raw)
  (proof-with-checked-results
   ((text (text-strip-right raw (coerce (list #\Newline) 'string)))
    (line (reader-reader-line (reader-reader text))))
   (list (caar line) (proof-freeze (cadar line)))))

(mutual-recursion
 (defun t2-api-names-term-with-names (term names)
   (declare (xargs :measure (acl2-count term)))
   (if (or (not (proof-compound term)) (endp term) (equal (car term) *proof-quote*))
       term
     (let ((operator (car term)))
       (proof-with-checked-results
        ((operator (if (proof-compound operator)
                       (if (equal (len operator) 3)
                           (proof-with-checked-results
                            ((body (t2-api-names-term-with-names (caddr operator) names)))
                            (list (car operator) (cadr operator) body))
                         (proof-list-of-length operator 3))
                     (table-get names operator operator)))
         (arguments (t2-api-names-terms-with-names (cdr term) names)))
        (cons operator arguments)))))
 (defun t2-api-names-terms-with-names (terms names)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
      ((first (t2-api-names-term-with-names (car terms) names))
       (rest (t2-api-names-terms-with-names (cdr terms) names)))
      (cons first rest)))))

(defun t2-api-names-name-list (items names)
  (if (endp items)
      nil
    (cons (table-get names (car items) (car items))
          (t2-api-names-name-list (cdr items) names))))

(defun t2-api-names-character-strings (characters)
  (if (endp characters)
      nil
    (cons (coerce (list (car characters)) 'string)
          (t2-api-names-character-strings (cdr characters)))))

(defun t2-api-names-fields (value size)
  (proof-list-of-length (if (stringp value)
                           (t2-api-names-character-strings (coerce value 'list))
                         value)
                      size))

(defun t2-api-names-definitions (definitions names)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((parts (t2-api-names-fields (car definitions) 3))
      (name (table-get names (car parts) (car parts)))
      (body (t2-api-names-term-with-names (caddr parts) names))
      (rest (t2-api-names-definitions (cdr definitions) names)))
     (cons (list name (cadr parts) body) rest))))

(defun t2-api-names-substitution-pairs (pairs names)
  (if (endp pairs)
      nil
    (proof-with-checked-results
     ((parts (t2-api-names-fields (car pairs) 2))
      (value (t2-api-names-term-with-names (cadr parts) names))
      (rest (t2-api-names-substitution-pairs (cdr pairs) names)))
     (cons (list (car parts) value) rest))))

(defun t2-api-names-substitutions (pairs names)
  (cond ((equal pairs *proof-nil*) *proof-nil*)
        ((integerp pairs) '(:failure "failure" ""))
        (t (t2-api-names-substitution-pairs pairs names))))

(defun t2-api-names-substitution-choices (choices names)
  (if (endp choices)
      nil
    (proof-with-checked-results
     ((first (t2-api-names-substitutions (car choices) names))
      (rest (t2-api-names-substitution-choices (cdr choices) names)))
     (cons first rest))))

(defun t2-api-names-rewrite-fields (word data names private)
  (cond
   ((equal word "fact")
    (proof-with-checked-results ((name (proof-term-at data 0)))
      (list (table-get names name name))))
   ((or (equal word "lemma") (equal word "measure") (equal word "subsume"))
    (proof-with-checked-results
     ((name (proof-term-at data 0))
      (target (if (or (equal word "lemma") (and (equal word "measure") private))
                  (table-get names name name)
                name))
      (terms (t2-api-names-terms-with-names (cdr data) names)))
     (cons target terms)))
   ((equal word "define")
    (proof-with-checked-results
     ((rulers (proof-term-at data 0))
      (rulers (if (proof-compound rulers) (t2-api-names-name-list rulers names) rulers))
      (definitions (t2-api-names-definitions (cdr data) names)))
     (cons rulers definitions)))
   ((equal word "witness")
    (proof-with-checked-results ((name (proof-term-at data 0)))
      (cons name (t2-api-names-name-list (cdr data) names))))
   ((equal word "instantiate")
    (proof-with-checked-results
     ((step (proof-term-at data 0))
      (pairs (proof-term-at data 1))
      (result (t2-api-names-substitutions pairs names)))
     (list step result)))
   ((equal word "induct")
    (proof-with-checked-results
     ((choices (proof-term-at data 4))
      (choices (cond ((equal choices *proof-nil*) *proof-nil*)
                     ((integerp choices) '(:failure "failure" ""))
                     (t (t2-api-names-substitution-choices choices names))))
      (formula (t2-api-names-term-with-names (nth 2 data) names))
      (measure (t2-api-names-term-with-names (nth 3 data) names)))
     (list (car data) (cadr data) formula measure choices)))
   ((or (equal word "beta") (equal word "compute"))
    (proof-with-checked-results
     ((term (proof-term-at data 0))
      (result (t2-api-names-term-with-names term names)))
     (list result)))
   (t data)))

(defun t2-api-names-rewrite-line (raw names private)
  (proof-with-checked-results
   ((line (t2-api-names-parsed raw))
    (changed (t2-api-names-rewrite-fields (car line) (cadr line) names private)))
   (if (equal changed (cadr line)) raw (proof-line (car line) changed))))

(defun t2-api-names-token-separator-p (ch)
  (member-equal ch *t2-api-names-token*))

(defun t2-api-names-scan-tokens (characters reversed tokens)
  (cond ((endp characters)
         (reverse (if reversed (cons (coerce (reverse reversed) 'string) tokens) tokens)))
        ((t2-api-names-token-separator-p (car characters))
         (t2-api-names-scan-tokens
          (cdr characters) nil
          (if reversed (cons (coerce (reverse reversed) 'string) tokens) tokens)))
        (t (t2-api-names-scan-tokens (cdr characters) (cons (car characters) reversed) tokens))))

(defun t2-api-names-split-lines (characters line lines)
  (cond ((endp characters)
         (reverse (if line (cons (coerce (reverse line) 'string) lines) lines)))
        ((and (eql (car characters) #\Return) (eql (cadr characters) #\Newline))
         (t2-api-names-split-lines
          (cddr characters) nil
          (cons (coerce (revappend line (list #\Return #\Newline)) 'string) lines)))
        ((or (eql (car characters) #\Newline) (eql (car characters) #\Return))
         (t2-api-names-split-lines
          (cdr characters) nil
          (cons (coerce (reverse (cons (car characters) line)) 'string) lines)))
        (t (t2-api-names-split-lines (cdr characters) (cons (car characters) line) lines))))

(defun t2-api-names-binding-map (bindings names)
  (if (endp bindings)
      names
    (let* ((entry (car bindings))
           (pair (if (stringp entry)
                     (t2-api-names-character-strings (coerce entry 'list))
                   entry)))
      (if (equal (len pair) 2)
          (t2-api-names-binding-map (cdr bindings) (table-put names (car pair) (cadr pair)))
        '(:failure "failure" "")))))

(defun t2-api-names-written-keys (names)
  (if (endp names)
      nil
    (proof-with-checked-results
     ((first (proof-write (caar names)))
      (rest (t2-api-names-written-keys (cdr names))))
     (cons first rest))))

(defun t2-api-names-intersection-p (tokens found)
  (and (consp tokens)
       (or (member-equal (car tokens) found) (t2-api-names-intersection-p (cdr tokens) found))))

(defun t2-api-names-rename-lines (lines names tokens private reversed)
  (if (endp lines)
      (text-join "" (reverse reversed))
    (let* ((raw (car lines))
           (matches (t2-api-names-scan-tokens (coerce raw 'list) nil nil)))
      (proof-with-checked-results
       ((changed (if (t2-api-names-intersection-p matches tokens)
                     (t2-api-names-rewrite-line raw names private)
                   raw)))
       (t2-api-names-rename-lines (cdr lines) names tokens private (cons changed reversed))))))

(defun t2-api-names-rename (source bindings private)
  (if (endp bindings)
      source
    (proof-with-checked-results
     ((names (t2-api-names-binding-map bindings nil))
      (tokens (t2-api-names-written-keys names)))
     (t2-api-names-rename-lines
      (t2-api-names-split-lines (coerce source 'list) nil nil) names tokens private nil))))

(defun t2-api-names-qualified-tokens (tokens seen)
  (cond ((endp tokens) (reverse seen))
        ((and (<= 0 (text-find (car tokens) "::")) (not (member-equal (car tokens) seen)))
         (t2-api-names-qualified-tokens (cdr tokens) (cons (car tokens) seen)))
        (t (t2-api-names-qualified-tokens (cdr tokens) seen))))

(defun t2-api-names-source-tokens (source)
  (t2-api-names-qualified-tokens (t2-api-names-scan-tokens (coerce source 'list) nil nil) nil))

(defun t2-api-names-present-names (names present)
  (if (endp names)
      nil
    (proof-with-checked-results
     ((token (proof-write (caar names)))
      (rest (t2-api-names-present-names (cdr names) present)))
     (if (member-equal token present)
         (cons (list (caar names) (cdar names)) rest)
       rest))))

(defun t2-api-names-dependencies (source names)
  (t2-api-names-present-names names (t2-api-names-source-tokens source)))

(defun t2-api-names-digest (source)
  (text-upper (siphash-hexdigest source)))

(defun t2-api-names-placeholder-bindings (declared index)
  (if (endp declared)
      nil
    (proof-with-checked-results
     ((package (proof-term-at (car declared) 1))
      (name (if (stringp package)
                (proof-sym (concatenate 'string "PROVER-PRIVATE-" (decimal-text index)) package)
              '(:failure "failure" "")))
      (rest (t2-api-names-placeholder-bindings (cdr declared) (1+ index))))
     (cons (list (car declared) name) rest))))

(defun t2-api-names-digit-chars-p (chars)
  (or (endp chars)
      (and (<= 48 (char-code (car chars))) (<= (char-code (car chars)) 57)
           (t2-api-names-digit-chars-p (cdr chars)))))

(defun t2-api-names-private-stem (name)
  (let* ((stem (if (text-starts-with name "SELF-") (seq-slice name 5 :none) name))
         (decrease "CALL-DECREASE-")
         (digits (and (text-starts-with stem decrease) (seq-slice stem (length decrease) :none))))
    (if (and digits (not (equal digits "")) (t2-api-names-digit-chars-p (coerce digits 'list)))
        "CALL-DECREASE"
      stem)))

(defun t2-api-names-private-labels (declared prefix key)
  (if (endp declared)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car declared) 2))
      (stem (if (stringp name)
                (t2-api-names-private-stem name)
              '(:failure "failure" "")))
      (label (proof-sym (concatenate 'string prefix stem "-" key) (cadar declared)))
      (rest (t2-api-names-private-labels (cdr declared) prefix key)))
     (cons (list (car declared) label) rest))))

(defun t2-api-names-private-entry (source declared before prefix)
  (proof-with-checked-results
   ((normalized (t2-api-names-rename source before t))
    (placeholders (t2-api-names-placeholder-bindings declared 0))
    (generic (t2-api-names-rename normalized placeholders t))
    (key (t2-api-names-digest generic))
    (own (t2-api-names-private-labels declared prefix key))
    (changed (t2-api-names-rename normalized own t)))
   (list own changed)))

(defun t2-api-names-declared-functions (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((definition (t2-api-names-fields (car definitions) 3))
      (rest (t2-api-names-declared-functions (cdr definitions))))
     (cons (car definition) rest))))

(defun t2-api-names-declared (kind name source)
  (cond ((equal kind "lemma") (list name))
        ((equal kind "define")
         (proof-with-checked-results
          ((newline (text-find source (coerce (list #\Newline) 'string)))
           (line (t2-api-names-parsed (if (< newline 0) source (seq-slice source 0 newline)))))
          (t2-api-names-declared-functions (cdr (cadr line)))))
        (t '(:failure "failure" ""))))

(defun t2-api-names-occupied-p (own used)
  (and (consp own)
       (or (assoc-equal (cadar own) used) (t2-api-names-occupied-p (cdr own) used))))

(defun t2-api-names-namespace-entries (helpers entry prefix used names sources)
  (if (endp helpers)
      (proof-with-checked-results
       ((before (t2-api-names-dependencies entry names))
        (changed (t2-api-names-rename entry before nil)))
       (list (reverse sources) changed))
    (proof-with-checked-results
     ((helper (t2-api-names-fields (car helpers) 4))
      (source (cadddr helper))
      (declared (t2-api-names-declared (car helper) (cadr helper) source))
      (before (t2-api-names-dependencies source names))
      (private (t2-api-names-private-entry source declared before prefix))
      (own (car private)))
     (if (t2-api-names-occupied-p own used)
         '(:failure "failure" "")
       (proof-with-checked-results ((names (t2-api-names-binding-map own names)))
         (t2-api-names-namespace-entries
          (cdr helpers) entry prefix used names (cons (cadr private) sources)))))))

(defun t2-api-names-namespace (helpers entry prefix used)
  (t2-api-names-namespace-entries helpers entry (concatenate 'string "PROVER-" prefix "-")
                                  used nil nil))
