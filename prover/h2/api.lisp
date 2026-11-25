(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-api-prefix* "H2")
(defconst *h2-api-newline* (coerce (list #\Newline) 'string))
(defconst *h2-api-line-endings* (coerce (list #\Return #\Newline) 'string))
(defconst *h2-api-private-prefix* (coerce "ACL2::SELF-" 'list))
(defconst *h2-api-private-blockers*
  (coerce "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789:|" 'list))
(defconst *h2-api-private-tail*
  (coerce "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+*/<=>!?$%&_^~.@-" 'list))

(defun h2-api-decode-ascii (source)
  (if (h2-computation-ascii-chars-p (coerce source 'list))
      source
    '(:failure "failure" "")))

(defun h2-api-parse (raw)
  (if (and (stringp raw) (h2-computation-ascii-chars-p (coerce raw 'list)))
      (let ((source (text-strip-right raw *h2-api-line-endings*)))
        (proof-with-checked-results ((parsed (reader-reader-line (reader-reader source))))
          (list (concatenate 'string source *h2-api-newline*)
                (caar parsed)
                (proof-freeze (cadar parsed)))))
    '(:failure "failure" "")))

(defun h2-api-parse-lines (lines reversed)
  (if (endp lines)
      (reverse reversed)
    (proof-with-checked-results ((parsed (h2-api-parse (car lines))))
      (h2-api-parse-lines (cdr lines) (cons parsed reversed)))))

(defun h2-api-prefix-chars-p (prefix chars)
  (or (endp prefix)
      (and (consp chars)
           (eql (car prefix) (car chars))
           (h2-api-prefix-chars-p (cdr prefix) (cdr chars)))))

(defun h2-api-namespaced-replace (match names)
  (table-get names match match))

(defun h2-api-private-emit (token replacep names reversed)
  (if (endp token)
      reversed
    (let ((name (coerce (reverse token) 'string)))
      (if replacep
          (revappend (coerce (h2-api-namespaced-replace name names) 'list) reversed)
        (cons name reversed)))))

; A nonempty token holds a match in reverse up to the current character.
; A character that ends a match cannot start one because A is a tail character.
(defun h2-api-private-scan (chars previous token replacep names reversed)
  (declare (xargs :measure (acl2-count chars)))
  (cond ((endp chars)
         (reverse (h2-api-private-emit token replacep names reversed)))
        ((and (consp token) (member-equal (car chars) *h2-api-private-tail*))
         (h2-api-private-scan (cdr chars) (car chars) (cons (car chars) token)
                              replacep names reversed))
        ((and (endp token) (eql (car chars) #\A)
              (not (member-equal previous *h2-api-private-blockers*))
              (h2-api-prefix-chars-p *h2-api-private-prefix* chars)
              (member-equal (nth (len *h2-api-private-prefix*) chars) *h2-api-private-tail*))
         (h2-api-private-scan (nthcdr (len *h2-api-private-prefix*) chars)
                              #\- (reverse *h2-api-private-prefix*) replacep names reversed))
        (t
         (let ((output (h2-api-private-emit token replacep names reversed)))
           (h2-api-private-scan (cdr chars) (car chars) nil replacep names
                                (if replacep (cons (car chars) output) output))))))

(defun h2-api-private-findall (source)
  (h2-api-private-scan (coerce source 'list) nil nil nil nil nil))

(defun h2-api-private-sub (source names)
  (coerce (h2-api-private-scan (coerce source 'list) nil nil t names nil) 'string))

(defun h2-api-string-key (chars reversed)
  (if (endp chars)
      (coerce (reverse (cons #\" reversed)) 'string)
    (let ((ch (car chars)))
      (h2-api-string-key
       (cdr chars)
       (cons ch (if (or (eql ch #\\) (eql ch #\"))
                    (cons #\\ reversed)
                  reversed))))))

(defun h2-api-string-set-keys (strings)
  (if (endp strings)
      nil
    (cons (cons (h2-api-string-key (coerce (car strings) 'list) (list #\"))
                (car strings))
          (h2-api-string-set-keys (cdr strings)))))

(defun h2-api-string-set-values (records previous)
  (cond ((endp records) nil)
        ((equal (cdar records) previous)
         (h2-api-string-set-values (cdr records) previous))
        (t (cons (cdar records) (h2-api-string-set-values (cdr records) (cdar records))))))

(defun h2-api-string-set (strings)
  (h2-api-string-set-values
   (acl2::merge-sort-lexorder (h2-api-string-set-keys strings)) nil))

(defun h2-api-private-names (lines names)
  (if (endp lines)
      (h2-api-string-set names)
    (h2-api-private-names (cdr lines)
                          (revappend (h2-api-private-findall (car lines)) names))))

(defun h2-api-string-tree-find (key tree)
  (cond ((endp tree) nil)
        ((equal key (car tree)) tree)
        ((string< key (car tree)) (h2-api-string-tree-find key (caddr tree)))
        (t (h2-api-string-tree-find key (cadddr tree)))))

(defun h2-api-string-tree-has-p (key tree)
  (if (h2-api-string-tree-find key tree) t nil))

(defun h2-api-namespaced-tree-entries (entries private tree names reversed-lemmas)
  (cond ((endp entries) '(:failure "failure" ""))
        ((endp (cdr entries))
         (proof-with-checked-results
             ((source (proof-term-at (car entries) 3))
              (entry (h2-api-decode-ascii (h2-api-private-sub source names))))
           (list (reverse reversed-lemmas) entry)))
        (t
         (proof-with-checked-results ((record (proof-list-of-length (car entries) 4))
                                      (old (proof-write (cadr record))))
           (let ((kind (car record))
                 (name (cadr record))
                 (source (cadddr record)))
             (if (or (not (member-equal kind '("lemma" "define")))
                     (member-equal old private)
                     (h2-api-string-tree-has-p old tree)
                     (not (equal (h2-api-private-findall old) (list old))))
                 '(:failure "failure" "")
               (let* ((certificate (h2-api-private-sub source names))
                      (digest (text-upper (siphash-hexdigest certificate)))
                      (stem (seq-slice (caddr name) 5 :none))
                      (stem (if (text-starts-with stem "H2-")
                                (seq-slice stem 3 :none)
                              stem))
                      (new (concatenate 'string (cadr name) "::PROVER-H2-" stem "-" digest))
                      (names (table-put names old new)))
                 (proof-with-checked-results
                     ((lemma (h2-api-decode-ascii (h2-api-private-sub source names))))
                   (h2-api-namespaced-tree-entries (cdr entries) private tree names
                                                  (cons lemma reversed-lemmas))))))))))

(defun h2-api-namespaced-entries (entries private names reversed-lemmas)
  (h2-api-namespaced-tree-entries entries private nil names reversed-lemmas))

(defun h2-api-namespaced (entries private)
  (h2-api-namespaced-entries entries private nil nil))

(defun h2-api-namespaced-with-tree (entries private tree)
  (h2-api-namespaced-tree-entries entries private tree nil nil))

(defun h2-api-library-raw (parsed)
  (if (endp parsed)
      nil
    (cons (caar parsed) (h2-api-library-raw (cdr parsed)))))

(defun h2-api-library (lines)
  (proof-with-checked-results ((parsed (h2-api-parse-lines lines nil))
                               (base (h2-books-book-proof-init parsed)))
    (let ((raw (h2-api-string-set (h2-api-library-raw parsed))))
      (list base raw (h2-api-private-names raw nil)))))

(defun h2-api-aids-lines (lines measures hints)
  (if (endp lines)
      (list measures hints)
    (let ((line (car lines)))
      (cond
       ((not (stringp line)) '(:failure "failure" ""))
       ((text-starts-with line '("(measure " "(hints " "(instructions "))
        (proof-with-checked-results ((parsed (h2-api-parse line))
                                     (name (proof-term-at (caddr parsed) 0)))
          (let ((data (caddr parsed)))
            (if (equal (cadr parsed) "measure")
                (h2-api-aids-lines (cdr lines) (table-put measures name (cdr data)) hints)
              (proof-with-checked-results ((value (proof-term-at data 1)))
                (h2-api-aids-lines (cdr lines) measures
                                  (table-put hints name (proof-unique (h2-books-symbols value)))))))))
       (t (h2-api-aids-lines (cdr lines) measures hints))))))

(defun h2-api-aids (lines)
  (h2-api-aids-lines lines nil nil))

(defun h2-api-make-world (library proof not-nil seen private earlier)
  (list :h2-world library proof not-nil seen private earlier))

(defun h2-api-world-library (world)
  (nth 1 world))

(defun h2-api-world-proof (world)
  (nth 2 world))

(defun h2-api-world-not-nil (world)
  (nth 3 world))

(defun h2-api-world-seen (world)
  (nth 4 world))

(defun h2-api-world-private (world)
  (nth 5 world))

(defun h2-api-world-earlier (world)
  (nth 6 world))

(defun h2-api-world-init (library)
  (proof-with-checked-results ((loaded (h2-api-library library)))
    (let* ((base (car loaded))
           (proof (h2-books-book-proof-fork base))
           (not-nil (library-library-proof (h2-books-book-proof-library base))))
      (h2-api-make-world library proof not-nil (cadr loaded) (caddr loaded) nil))))

(defun h2-api-world-advance-lines (lines proof seen private)
  (if (endp lines)
      (list proof (h2-api-string-set seen) (h2-api-string-set private))
    (proof-with-checked-results ((parsed (h2-api-parse (car lines))))
      (let ((raw (car parsed)))
        (if (member-equal raw seen)
            (h2-api-world-advance-lines (cdr lines) proof seen private)
          (proof-with-checked-results
              ((proof (h2-books-book-proof-add-statement proof (cadr parsed) (caddr parsed))))
            (h2-api-world-advance-lines (cdr lines) proof (cons raw seen)
                                       (revappend (h2-api-private-findall raw) private))))))))

(defun h2-api-world-advance (world earlier)
  (proof-with-checked-results
      ((advanced (h2-api-world-advance-lines (nthcdr (len (h2-api-world-earlier world)) earlier)
                                           (h2-api-world-proof world)
                                           (h2-api-world-seen world)
                                           (h2-api-world-private world))))
    (h2-api-make-world (h2-api-world-library world) (car advanced)
                       (h2-api-world-not-nil world) (cadr advanced) (caddr advanced) earlier)))

(defun h2-api-world-with-indexed-prefix (library earlier)
  (proof-with-checked-results
      ((world (h2-api-world-init library))
       (proof (h2-books-book-proof-index-prefix-names (h2-api-world-proof world) earlier))
       (world (h2-api-world-advance (update-nth 2 proof world) earlier)))
    (update-nth 2 (h2-books-book-proof-restore-written-names (h2-api-world-proof world)) world)))

(defun h2-api-proof-trial (book-proof)
  (let* ((trial (h2-books-book-proof-fork book-proof))
         (trial (h2-books-book-proof-with-book-rules trial (h2-books-book-proof-book-rules book-proof)))
         (proof (library-library-proof (h2-books-book-proof-library trial))))
    (if (and (assoc-equal (proof-sym "NFIX" "ACL2") (proof-proof-definitions proof))
             (not (assoc-equal (proof-sym "SELF-H2-NFIX-WHEN-ZP" "ACL2") (proof-proof-facts proof))))
        (h2-books-book-proof-index-lemmas trial)
      trial)))

(defun h2-api-world-trial (world)
  (h2-api-proof-trial (h2-api-world-proof world)))

(defun h2-api-theorem-label (name)
  (proof-with-checked-results ((label (proof-term-at name 2)))
    (cond ((not (stringp label)) '(:failure "failure" ""))
          ((h2-computation-ascii-chars-p (coerce label 'list)) label)
          (t '(:failure "tactic-inapplicable" "")))))

(defun h2-api-special-theorem (trial name data)
  (let ((trial (h2-books-book-proof-with-fuel trial 150000)))
    (proof-with-checked-results
        ((label (h2-api-theorem-label name))
         (formula (proof-term-at data 1)))
      (h2-books-book-proof-prove-theorem trial label formula))))

(defun h2-api-special-fallback-p (value)
  (and (failure-p value)
       (member-equal (cadr value)
                     '("unproved" "tactic-inapplicable" "arithmetic-inapplicable"
                       "assertion" "key" "value" "index" "type"
                       "encoding" "decoding" "translating"))))

(defun h2-api-find-entries (trial kind data name measures hints)
  (proof-with-checked-results ((result (h2-books-find-certificate trial kind data name measures hints)))
    (h2-books-certificate-entries (car result))))

(defun h2-api-theorem-entries-from-proof (proof trial data name measures hints)
  (let ((special (h2-api-special-theorem trial name data)))
    (cond ((h2-api-special-fallback-p special)
           (proof-with-checked-results ((trial (h2-api-proof-trial proof)))
             (h2-api-find-entries trial "theorem" data name measures hints)))
          ((failure-p special) special)
          ((and (car special) (equal (proof-step-clause (car special)) (list (cadr data))))
           (proof-with-checked-results
               ((entry (proof-proof-entry "theorem" name (list name) (list (car special)))))
             (h2-recipes-recipes-dependencies (h2-books-book-proof-recipes (cdr special)) entry)))
          (t (h2-api-find-entries (cdr special) "theorem" data name measures hints)))))

(defun h2-api-theorem-entries (world trial data name measures hints)
  (h2-api-theorem-entries-from-proof (h2-api-world-proof world) trial data name measures hints))

(defun h2-api-prove-internal (statement earlier library aids)
  (proof-with-checked-results ((parsed (h2-api-parse statement)))
    (let ((raw (car parsed))
          (kind (cadr parsed))
          (data (caddr parsed)))
      (if (member-equal kind '("define" "constrain" "theorem"))
          (proof-with-checked-results ((name (h2-books-statement-name kind data)))
            (if (null name)
                nil
              (proof-with-checked-results ((world (h2-api-world-with-indexed-prefix library earlier)))
                (if (member-equal raw (h2-api-world-seen world))
                    nil
                  (proof-with-checked-results
                      ((aids (h2-api-aids aids))
                       (trial (h2-api-world-trial world))
                       (entries (if (equal kind "theorem")
                                    (h2-api-theorem-entries world trial data name (car aids) (cadr aids))
                                  (h2-api-find-entries trial kind data name (car aids) (cadr aids)))))
                    (let ((private (h2-api-string-set (append (h2-api-world-private world)
                                                            (h2-api-private-findall raw)))))
                      (if entries (h2-api-namespaced entries private) nil)))))))
        nil))))

(defun h2-api-character-lines (chars)
  (if (endp chars)
      nil
    (cons (coerce (list (car chars)) 'string)
          (h2-api-character-lines (cdr chars)))))

(defun h2-api-input-sequence (value)
  (cond ((true-listp value) value)
        ((stringp value) (h2-api-character-lines (coerce value 'list)))
        (t '(:failure "failure" ""))))

(defun h2-api-prove (statement earlier library aids)
  (let ((result
         (proof-with-checked-results
             ((earlier (h2-api-input-sequence earlier))
              (library (h2-api-input-sequence library))
              (aids (h2-api-input-sequence aids)))
           (h2-api-prove-internal statement earlier library aids))))
    (if (failure-p result) nil result)))
