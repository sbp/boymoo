(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-api-entries-newline* (coerce (list #\Newline) 'string))

(defun b2-api-entries-group-add (entry reversed)
  (proof-with-checked-results ((entry (proof-list-of-length entry 4)))
    (let ((kind (car entry))
          (name (cadr entry))
          (source (cadddr entry)))
      (cond
       ((equal kind "measure")
        (if (endp reversed)
            '(:failure "failure" "")
          (let ((names (caar reversed))
                (definition (cadar reversed)))
            (proof-with-checked-results ((first (proof-term-at names 0)))
              (if (equal name first)
                  (cons (list names (string-append definition source)) (cdr reversed))
                '(:failure "failure" ""))))))
       (t
        (proof-with-checked-results ((names (b2-reuse-declares entry)))
          (if names
              (cons (list names source) reversed)
            '(:failure "failure" ""))))))))

(defun b2-api-entries-groups-collect (entries reversed)
  (if (endp entries)
      (reverse reversed)
    (proof-with-checked-results ((reversed (b2-api-entries-group-add (car entries) reversed)))
      (b2-api-entries-groups-collect (cdr entries) reversed))))

(defun b2-api-entries-groups (entries)
  (b2-api-entries-groups-collect entries nil))

(defun b2-api-entries-dependency-in-sources (name sources)
  (if (endp sources)
      nil
    (proof-with-checked-results ((text (proof-write name)))
      (if (<= 0 (text-find (car sources) text))
          t
        (b2-api-entries-dependency-in-sources name (cdr sources))))))

(defun b2-api-entries-dependency-names (names sources)
  (if (endp names)
      nil
    (proof-with-checked-results ((present (b2-api-entries-dependency-in-sources (car names) sources)))
      (if present t (b2-api-entries-dependency-names (cdr names) sources)))))

(defun b2-api-entries-dependencies-walk (entries sources needed)
  (if (endp entries)
      needed
    (proof-with-checked-results
        ((entry (proof-list-of-length (car entries) 2))
         (present (b2-api-entries-dependency-names (car entry) sources)))
      (if present
          (b2-api-entries-dependencies-walk (cdr entries) (append sources (list (cadr entry)))
                                             (cons entry needed))
        (b2-api-entries-dependencies-walk (cdr entries) sources needed)))))

(defun b2-api-entries-dependencies (entries entry)
  (b2-api-entries-dependencies-walk (reverse entries) (list entry) nil))

(defun b2-api-entries-rename-symbol (name names)
  (table-get names name name))

(defun b2-api-entries-rename-term (value names)
  (b2-tactics-rename-calls value names))

(defun b2-api-entries-rename-terms (terms names)
  (if (endp terms)
      nil
    (proof-with-checked-results ((term (b2-api-entries-rename-term (car terms) names))
                                 (rest (b2-api-entries-rename-terms (cdr terms) names)))
      (cons term rest))))

(defun b2-api-entries-rename-symbols (values names)
  (if (endp values)
      nil
    (cons (b2-api-entries-rename-symbol (car values) names)
          (b2-api-entries-rename-symbols (cdr values) names))))

(defun b2-api-entries-rename-subst-pairs (pairs names)
  (if (endp pairs)
      nil
    (proof-with-checked-results ((pair (proof-list-of-length (car pairs) 2))
                                 (value (b2-api-entries-rename-term (cadr pair) names))
                                 (rest (b2-api-entries-rename-subst-pairs (cdr pairs) names)))
      (cons (list (car pair) value) rest))))

(defun b2-api-entries-rename-subst (pairs names)
  (if (proof-compound pairs) (b2-api-entries-rename-subst-pairs pairs names) pairs))

(defun b2-api-entries-rename-substitutions (substitutions names)
  (if (endp substitutions)
      nil
    (proof-with-checked-results ((pairs (b2-api-entries-rename-subst (car substitutions) names))
                                 (rest (b2-api-entries-rename-substitutions (cdr substitutions) names)))
      (cons pairs rest))))

(defun b2-api-entries-rename-definition (fields names)
  (proof-with-checked-results ((fields (proof-list-of-length fields 3))
                               (name (b2-api-entries-rename-symbol (car fields) names))
                               (body (b2-api-entries-rename-term (caddr fields) names)))
    (list name (cadr fields) body)))

(defun b2-api-entries-rename-definitions (definitions names)
  (if (endp definitions)
      nil
    (proof-with-checked-results ((definition (b2-api-entries-rename-definition (car definitions) names))
                                 (rest (b2-api-entries-rename-definitions (cdr definitions) names)))
      (cons definition rest))))

(defun b2-api-entries-rename-candidates (names)
  (if (endp names)
      nil
    (proof-with-checked-results ((text (proof-write (caar names)))
                                 (rest (b2-api-entries-rename-candidates (cdr names))))
      (cons text rest))))

; Each candidate is a literal byte string, including its package prefix.
(defun b2-api-entries-rename-candidate-p (raw candidates)
  (and (consp candidates)
       (or (<= 0 (text-find raw (car candidates)))
           (b2-api-entries-rename-candidate-p raw (cdr candidates)))))

(defun b2-api-entries-rename-induct (word first rest names)
  (proof-with-checked-results
      ((parts (proof-list-of-length rest 4))
       (formula (b2-api-entries-rename-term (cadr parts) names))
       (measure (b2-api-entries-rename-term (caddr parts) names))
       (substitutions (b2-api-entries-rename-substitutions (cadddr parts) names)))
    (proof-line word (list first (car parts) formula measure substitutions))))

(defun b2-api-entries-rename-line (raw word fields names)
  (let ((first (car fields))
        (rest (cdr fields)))
    (cond
     ((equal word "define")
      (let ((rulers (if (proof-compound first) (b2-api-entries-rename-symbols first names) first)))
        (proof-with-checked-results ((definitions (b2-api-entries-rename-definitions rest names)))
          (proof-line word (cons rulers definitions)))))
     ((member-equal word '("lemma" "measure"))
      (proof-with-checked-results ((name (b2-api-entries-rename-symbol first names))
                                   (terms (b2-api-entries-rename-terms rest names)))
        (proof-line word (cons name terms))))
     ((equal word "witness")
      (proof-line word (cons first (b2-api-entries-rename-symbols rest names))))
     ((equal word "fact") (proof-line word (list (b2-api-entries-rename-symbol first names))))
     ((equal word "instantiate")
      (proof-with-checked-results ((pairs (proof-term-at rest 0))
                                   (substitution (b2-api-entries-rename-subst pairs names)))
        (proof-line word (list first substitution))))
     ((equal word "subsume")
      (proof-with-checked-results ((terms (b2-api-entries-rename-terms rest names)))
        (proof-line word (cons first terms))))
     ((member-equal word '("beta" "compute"))
      (proof-with-checked-results ((term (b2-api-entries-rename-term first names)))
        (proof-line word (list term))))
     ((equal word "induct") (b2-api-entries-rename-induct word first rest names))
     (t (string-append raw *b2-api-entries-newline*)))))

(defun b2-api-entries-rename-rewrite (raw names candidates)
  (if (not (b2-api-entries-rename-candidate-p raw candidates))
      (string-append raw *b2-api-entries-newline*)
    (proof-with-checked-results ((parsed (b2-reuse-parse raw)))
      (if (endp (cadr parsed))
          '(:failure "failure" "")
        (b2-api-entries-rename-line raw (car parsed) (cadr parsed) names)))))

(defun b2-api-entries-rename-lines (lines names candidates)
  (if (or (endp lines) (endp (cdr lines)))
      nil
    (proof-with-checked-results ((line (b2-api-entries-rename-rewrite (car lines) names candidates))
                                 (rest (b2-api-entries-rename-lines (cdr lines) names candidates)))
      (cons line rest))))

(defun b2-api-entries-rename (source names)
  (if (endp names)
      source
    (proof-with-checked-results ((candidates (b2-api-entries-rename-candidates names))
                                 (lines (text-split source *b2-api-entries-newline*))
                                 (lines (b2-api-entries-rename-lines lines names candidates)))
      (text-join "" lines))))

(defun b2-api-entries-assemble-name (old digest)
  (proof-with-checked-results ((name (proof-term-at old 2)))
    (list (car old) (cadr old) (concatenate 'string "PROVER-B2-" name "-" digest))))

(defun b2-api-entries-assemble-names (names digest renamed public-facts public-definitions)
  (if (endp names)
      renamed
    (let ((old (car names)))
      (proof-with-checked-results ((new (b2-api-entries-assemble-name old digest)))
        (cond
         ((or (assoc-equal old public-facts) (assoc-equal old public-definitions)
              (assoc-equal new public-facts) (assoc-equal new public-definitions))
          '(:failure "failure" ""))
         ((assoc-equal old renamed) '(:failure "failure" ""))
         (t (b2-api-entries-assemble-names (cdr names) digest (table-put renamed old new)
                                           public-facts public-definitions)))))))

(defun b2-api-entries-assemble-groups (groups entry renamed lemmas public-facts public-definitions)
  (if (endp groups)
      (proof-with-checked-results ((entry (b2-api-entries-rename entry renamed)))
        (list (reverse lemmas) entry))
    (let ((names (caar groups))
          (source (cadar groups)))
      (proof-with-checked-results
          ((text (b2-api-entries-rename source renamed))
           (digest (text-upper (siphash-hexdigest text)))
           (renamed (b2-api-entries-assemble-names names digest renamed public-facts public-definitions))
           (lemma (b2-api-entries-rename source renamed)))
        (b2-api-entries-assemble-groups (cdr groups) entry renamed (cons lemma lemmas)
                                         public-facts public-definitions)))))

(defun b2-api-entries-assemble (prelude entries entry public-facts public-definitions)
  (proof-with-checked-results ((groups (b2-api-entries-groups entries))
                               (needed (b2-api-entries-dependencies (append prelude groups) entry)))
    (b2-api-entries-assemble-groups needed entry nil nil public-facts public-definitions)))
