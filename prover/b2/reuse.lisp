(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-reuse-fact* '("(fact " 1 ")"))

(defun b2-reuse-parse (raw)
  (proof-with-checked-results
   ((line (reader-reader-line (reader-reader raw))))
   (list (caar line) (proof-freeze (cadar line)))))

(defun b2-reuse-head (entry)
  (proof-with-checked-results
   ((source (proof-term-at entry 3)))
   (let ((newline (text-find source (coerce (list #\Newline) 'string))))
     (if (< newline 0)
         source
       (seq-slice source 0 newline)))))

(defun b2-reuse-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car definitions) 0))
      (rest (b2-reuse-definition-names (cdr definitions))))
     (cons name rest))))

(defun b2-reuse-declares (entry)
  (proof-with-checked-results
   ((kind (proof-term-at entry 0)))
   (cond
    ((equal kind "define")
     (proof-with-checked-results
      ((header (b2-reuse-head entry))
       (line (b2-reuse-parse header)))
      (b2-reuse-definition-names (cdr (cadr line)))))
    ((equal kind "lemma")
     (proof-with-checked-results
      ((name (proof-term-at entry 1)))
      (list name)))
    (t nil))))

(defun b2-reuse-mentions-name (names source)
  (if (endp names)
      nil
    (proof-with-checked-results
     ((printed (proof-write (car names))))
     (if (<= 0 (text-find source printed))
         t
       (b2-reuse-mentions-name (cdr names) source)))))

(defun b2-reuse-supporting-backward (entries source start index kept)
  (if (endp entries)
      (list kept source)
    (let ((entry (car entries)))
      (proof-with-checked-results
       ((declared (b2-reuse-declares entry))
        (names (if declared
                   declared
                 (proof-with-checked-results
                  ((name (proof-term-at entry 1)))
                  (list name))))
        (keep (if (and (not (eq start :none)) (<= start index))
                  t
                (b2-reuse-mentions-name names source))))
       (if keep
           (proof-with-checked-results
            ((entry-source (proof-term-at entry 3)))
            (b2-reuse-supporting-backward
             (cdr entries) (string-append source entry-source)
             start (1- index) (cons entry kept)))
         (b2-reuse-supporting-backward
          (cdr entries) source start (1- index) kept))))))

(defun b2-reuse-supporting (entries source start)
  (b2-reuse-supporting-backward
   (reverse entries) source start (1- (len entries)) nil))

(defun b2-reuse-compiled (entry support facts)
  (list :compiled entry support facts))

(defun b2-reuse-compiled-entry (compiled)
  (cadr compiled))

(defun b2-reuse-compiled-support (compiled)
  (caddr compiled))

(defun b2-reuse-compiled-facts (compiled)
  (cadddr compiled))

(defun b2-reuse-required-present (required available)
  (if (endp required)
      t
    (let ((current (assoc-equal (caar required) available)))
      (and current
           (equal (cdr current) (cdar required))
           (b2-reuse-required-present (cdr required) available)))))

(defun b2-reuse-available-entries (entries available)
  (if (endp entries)
      available
    (let ((entry (car entries)))
      (proof-with-checked-results
       ((kind (proof-term-at entry 0))
        (name (proof-term-at entry 1)))
       (b2-reuse-available-entries
        (cdr entries) (table-put available (list kind name) entry))))))

(defun b2-reuse-declared-present (names facts)
  (if (endp names)
      nil
    (or (assoc-equal (car names) facts)
        (b2-reuse-declared-present (cdr names) facts))))

(defun b2-reuse-replay-missing (support available facts)
  (if (endp support)
      nil
    (let ((entry (car support)))
      (proof-with-checked-results
       ((fields (proof-list-of-length entry 4)))
       (let* ((kind (car fields))
              (name (cadr fields))
              (old (table-get available (list kind name) nil)))
         (cond
          (old
           (proof-with-checked-results
            ((matches (if (member-equal kind '("define" "lemma"))
                          (proof-with-checked-results
                           ((old-head (b2-reuse-head old))
                            (new-head (b2-reuse-head entry)))
                           (equal old-head new-head))
                        t)))
            (if matches
                (b2-reuse-replay-missing (cdr support) available facts)
              :conflict)))
          (t
           (proof-with-checked-results
            ((names (b2-reuse-declares entry)))
            (if (b2-reuse-declared-present names facts)
                :conflict
              (proof-with-checked-results
               ((rest (b2-reuse-replay-missing (cdr support) available facts)))
               (if (eq rest :conflict) rest (cons entry rest))))))))))))

(defun b2-reuse-replay-definitions (definitions proof)
  (if (endp definitions)
      proof
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3))
      (next (proof-proof-add-definition
             proof (car definition) (cadr definition) (caddr definition))))
     (b2-reuse-replay-definitions (cdr definitions) next))))

(defun b2-reuse-replay-install (entry proof)
  (let ((kind (car entry))
        (name (cadr entry)))
    (if (member-equal kind '("define" "lemma"))
        (proof-with-checked-results
         ((header (b2-reuse-head entry))
          (line (b2-reuse-parse header)))
         (let ((declarations (cdr (cadr line))))
           (if (equal kind "define")
               (b2-reuse-replay-definitions declarations proof)
             (proof-proof-with-facts
              proof (table-put (proof-proof-facts proof) name declarations)))))
      proof)))

(defun b2-reuse-replay-install-all (entries lib)
  (if (endp entries)
      lib
    (let ((entry (car entries)))
      (proof-with-checked-results
       ((proof (b2-reuse-replay-install entry (library-library-proof lib))))
       (b2-reuse-replay-install-all
        (cdr entries)
        (library-library-with-entries
         (library-library-with-proof lib proof)
         (append (library-library-entries lib) (list entry))))))))

(defun b2-reuse-compiled-replay (compiled lib)
  (let ((facts (proof-proof-facts (library-library-proof lib))))
    (if (b2-reuse-required-present (b2-reuse-compiled-facts compiled) facts)
        (proof-with-checked-results
         ((available (b2-reuse-available-entries (library-library-entries lib) nil))
          (missing (b2-reuse-replay-missing
                    (b2-reuse-compiled-support compiled) available facts)))
         (if (eq missing :conflict)
             (cons nil lib)
           (proof-with-checked-results
            ((after (b2-reuse-replay-install-all missing lib)))
            (cons (b2-reuse-compiled-entry compiled) after))))
      (cons nil lib))))

(defun b2-reuse-reuse-compiled (reuse)
  (cadr reuse))

(defun b2-reuse-reuse-hits (reuse)
  (caddr reuse))

(defun b2-reuse-reuse-init ()
  (list :b2-reuse nil 0))

(defun b2-reuse-lookup-examples (examples lib)
  (if (endp examples)
      (cons nil lib)
    (proof-with-checked-results
     ((result (b2-reuse-compiled-replay (car examples) lib)))
     (if (car result)
         result
       (b2-reuse-lookup-examples (cdr examples) (cdr result))))))

(defun b2-reuse-reuse-lookup (reuse raw lib)
  (let ((compiled (b2-reuse-reuse-compiled reuse)))
    (proof-with-checked-results
     ((result (b2-reuse-lookup-examples (table-get compiled raw nil) lib)))
     (let ((entry (car result))
           (after (cdr result)))
       (if entry
           (list entry (list :b2-reuse compiled (1+ (b2-reuse-reuse-hits reuse))) after)
         (list nil reuse after))))))

(defun b2-reuse-support-names (support)
  (if (endp support)
      nil
    (proof-with-checked-results
     ((names (b2-reuse-declares (car support)))
      (rest (b2-reuse-support-names (cdr support))))
     (append names rest))))

(defun b2-reuse-fact-line-p (line)
  (let ((prefix (car *b2-reuse-fact*))
        (body-length (cadr *b2-reuse-fact*))
        (suffix (caddr *b2-reuse-fact*)))
    (and (<= (+ (length prefix) body-length (length suffix)) (length line))
         (text-starts-with line prefix)
         (text-ends-with line suffix))))

(defun b2-reuse-cited-names (lines)
  (if (endp lines)
      nil
    (if (b2-reuse-fact-line-p (car lines))
        (proof-with-checked-results
         ((line (b2-reuse-parse (car lines)))
          (name (proof-term-at (cadr line) 0))
          (rest (b2-reuse-cited-names (cdr lines))))
         (cons name rest))
      (b2-reuse-cited-names (cdr lines)))))

(defun b2-reuse-required-facts (names local facts)
  (if (endp names)
      nil
    (let ((name (car names)))
      (if (member-equal name local)
          (b2-reuse-required-facts (cdr names) local facts)
        (let ((available (assoc-equal name facts)))
          (if available
              (proof-with-checked-results
               ((rest (b2-reuse-required-facts (cdr names) local facts)))
               (cons available rest))
            '(:failure "failure" "")))))))

(defun b2-reuse-reuse-remember (reuse raw lib entry mark)
  (proof-with-checked-results
   ((source (proof-term-at entry 3))
    (kept (b2-reuse-supporting (library-library-entries lib) source mark))
    (local (b2-reuse-support-names (car kept)))
    (names (b2-reuse-cited-names (text-split (cadr kept) (coerce (list #\Newline) 'string))))
    (facts (b2-reuse-required-facts
            (proof-unique names) local
            (proof-proof-facts (library-library-proof lib)))))
   (let* ((compiled (b2-reuse-reuse-compiled reuse))
          (examples (table-get compiled raw nil))
          (next (b2-reuse-compiled entry (car kept) facts)))
     (list :b2-reuse (table-put compiled raw (append examples (list next)))
           (b2-reuse-reuse-hits reuse)))))
