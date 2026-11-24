(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-api-prefix* "L1")
(defconst *l1-api-symbol-prefix* "ACL2::PROVER-L1-")
(defconst *l1-api-newline* (coerce (list #\Newline) 'string))

(defun l1-api-prefix-characters (prefixes)
  (if (endp prefixes)
      nil
    (cons (coerce (car prefixes) 'list) (l1-api-prefix-characters (cdr prefixes)))))

(defconst *l1-api-definition-head* (coerce "(define " 'list))
(defconst *l1-api-measure-head* (coerce "(measure " 'list))
(defconst *l1-api-choice-head* (coerce "(choose " 'list))
(defconst *l1-api-heads*
  (l1-api-prefix-characters '("(lemma " "(define " "(choose " "(theorem " "(measure " "(witness ")))
(defconst *l1-api-original-symbol-prefixes* '("ACL2::L1-" "ACL2::SELF-"))
(defconst *l1-api-original-prefixes*
  (l1-api-prefix-characters *l1-api-original-symbol-prefixes*))
(defconst *l1-api-helper-prefixes*
  (append *l1-api-original-prefixes* (list (coerce *l1-api-symbol-prefix* 'list))))
(defconst *l1-api-badge-absence-prefix*
  (string-append "ACL2::" *l1-primitive-absence-prefix*))

(defun l1-api-parse (line)
  (proof-with-checked-results ((parsed (reader-reader-line (reader-reader line))))
    (list (caar parsed) (proof-freeze (cadar parsed)))))

(defun l1-api-ascii-characters-p (chars)
  (or (endp chars)
      (and (<= (char-code (car chars)) 127)
           (l1-api-ascii-characters-p (cdr chars)))))

(defun l1-api-ascii-text (text)
  (if (l1-api-ascii-characters-p (coerce text 'list))
      text
    '(:failure "failure" "")))

(defun l1-api-raw (line)
  (if (not (stringp line))
      '(:failure "failure" "")
    (l1-api-ascii-text (text-strip-right line *l1-api-newline*))))

; A set is presented in the order of its printed ACL2 string literals.
(defun l1-api-string-key (chars reversed)
  (if (endp chars)
      (coerce (reverse (cons #\" reversed)) 'string)
    (let ((ch (car chars)))
      (l1-api-string-key (cdr chars)
                         (cons ch (if (or (eql ch #\") (eql ch #\\))
                                      (cons #\\ reversed)
                                    reversed))))))

(defun l1-api-string-set-keys (strings keys)
  (if (endp strings)
      keys
    (let* ((value (car strings))
           (key (l1-api-string-key (coerce value 'list) (list #\"))))
      (l1-api-string-set-keys (cdr strings) (cons (cons key value) keys)))))

(defun l1-api-string-set-values (records previous reversed)
  (cond ((endp records) (reverse reversed))
        ((equal (cdar records) previous)
         (l1-api-string-set-values (cdr records) previous reversed))
        (t (l1-api-string-set-values (cdr records) (cdar records)
                                      (cons (cdar records) reversed)))))

(defun l1-api-string-set (strings)
  (l1-api-string-set-values
   (acl2::merge-sort-lexorder (l1-api-string-set-keys strings nil)) nil nil))

(defun l1-api-byte-prefix-p (prefix chars)
  (or (endp prefix)
      (and (consp chars) (eql (car prefix) (car chars))
           (l1-api-byte-prefix-p (cdr prefix) (cdr chars)))))

(defun l1-api-byte-prefixes-p (prefixes chars)
  (and (consp prefixes)
       (or (l1-api-byte-prefix-p (car prefixes) chars)
           (l1-api-byte-prefixes-p (cdr prefixes) chars))))

(defun l1-api-prefix-present-p (chars prefixes)
  (and (consp chars)
       (or (and (eql (car chars) #\A)
                (l1-api-byte-prefixes-p prefixes chars))
           (l1-api-prefix-present-p (cdr chars) prefixes))))

; An escape covers the next byte unless it is LF.
(defun l1-api-atom-literal-length (chars delimiter escaped size)
  (if (endp chars)
      nil
    (let ((ch (car chars)))
      (cond (escaped
             (and (not (eql ch #\Newline))
                  (l1-api-atom-literal-length (cdr chars) delimiter nil (1+ size))))
            ((eql ch delimiter) (1+ size))
            (t (l1-api-atom-literal-length (cdr chars) delimiter (eql ch #\\) (1+ size)))))))

(defun l1-api-atom-name (chars reversed)
  (if (endp chars)
      nil
    (let* ((ch (car chars))
           (code (char-code ch)))
      (cond ((or (and (<= 65 code) (<= code 90))
                 (and (<= 48 code) (<= code 57))
                 (= code 45))
             (l1-api-atom-name (cdr chars) (cons ch reversed)))
            ((member-equal ch '(#\Space #\) #\Newline))
             (reverse reversed))
            (t nil)))))

(defun l1-api-atom-token (chars prefixes)
  (if (endp prefixes)
      nil
    (let ((prefix (car prefixes)))
      (if (l1-api-byte-prefix-p prefix chars)
          (let ((name (l1-api-atom-name (nthcdr (len prefix) chars) nil)))
            (and name (append prefix name)))
        (l1-api-atom-token chars (cdr prefixes))))))

; Each match gives its start, its exclusive end, and its serialized symbol.
(defun l1-api-atom-matches (chars previous index skip reversed)
  (declare (xargs :measure (acl2-count chars)))
  (if (endp chars)
      (reverse reversed)
    (let ((ch (car chars)))
      (cond ((posp skip)
             (l1-api-atom-matches (cdr chars) ch (1+ index) (1- skip) reversed))
            ((or (eql ch #\") (eql ch #\|))
             (l1-api-atom-matches (cdr chars) ch (1+ index)
                                  (l1-api-atom-literal-length (cdr chars) ch nil 0) reversed))
            (t
             (let ((token (and (eql ch #\A)
                               (member-equal previous '(#\Space #\())
                               (l1-api-atom-token chars *l1-api-helper-prefixes*))))
               (if token
                   (let* ((size (len token))
                          (match (list index (+ index size) (coerce token 'string))))
                     (l1-api-atom-matches (cdr chars) ch (1+ index) (1- size) (cons match reversed)))
                 (l1-api-atom-matches (cdr chars) ch (1+ index) 0 reversed))))))))

(defun l1-api-match-names (matches names)
  (if (endp matches)
      names
    (l1-api-match-names (cdr matches) (cons (caddar matches) names))))

(defun l1-api-context-names-scan (rows occupied)
  (if (endp rows)
      (l1-api-string-set occupied)
    (let ((row (car rows)))
      (cond ((not (stringp row))
             '(:failure "failure" ""))
            ((l1-api-prefix-present-p (coerce row 'list) *l1-api-helper-prefixes*)
             (proof-with-checked-results ((raw (l1-api-raw row)))
               (let ((matches (l1-api-atom-matches (coerce raw 'list) nil 0 0 nil)))
                 (l1-api-context-names-scan (cdr rows)
                                            (l1-api-match-names matches occupied)))))
            (t (l1-api-context-names-scan (cdr rows) occupied))))))

(defun l1-api-context-names (rows)
  (l1-api-context-names-scan rows nil))

(defun l1-api-namespace-copy (chars index skip matches names reversed)
  (declare (xargs :measure (acl2-count chars)))
  (cond ((endp chars) reversed)
        ((posp skip)
         (l1-api-namespace-copy (cdr chars) (1+ index) (1- skip) matches names reversed))
        ((and (consp matches) (equal (caar matches) index))
         (let* ((match (car matches))
                (token (caddr match))
                (alias (table-get names token token)))
           (l1-api-namespace-copy (cdr chars) (1+ index) (- (- (cadr match) index) 1)
                                  (cdr matches) names
                                  (revappend (coerce alias 'list) reversed))))
        (t (l1-api-namespace-copy (cdr chars) (1+ index) 0 matches names
                                  (cons (car chars) reversed)))))

(defun l1-api-namespace-line (line names reversed)
  (let ((chars (reverse line)))
    (if (l1-api-prefix-present-p chars *l1-api-original-prefixes*)
        (l1-api-namespace-copy chars 0 0 (l1-api-atom-matches chars nil 0 0 nil) names reversed)
      (append line reversed))))

; Byte strings split at LF, CR, and CRLF, with the terminators kept.
(defun l1-api-namespace-lines (chars names line reversed)
  (declare (xargs :measure (acl2-count chars)))
  (cond ((endp chars) (l1-api-namespace-line line names reversed))
        ((and (eql (car chars) #\Return) (consp (cdr chars)) (eql (cadr chars) #\Newline))
         (l1-api-namespace-lines
          (cddr chars) names nil (l1-api-namespace-line (list* #\Newline #\Return line) names reversed)))
        ((member-equal (car chars) '(#\Newline #\Return))
         (l1-api-namespace-lines
          (cdr chars) names nil (l1-api-namespace-line (cons (car chars) line) names reversed)))
        (t (l1-api-namespace-lines (cdr chars) names (cons (car chars) line) reversed))))

(defun l1-api-namespace-replace (text names)
  (if (endp names)
      text
    (coerce (reverse (l1-api-namespace-lines (coerce text 'list) names nil nil)) 'string)))

; An entry begins at the saved offset and shares the unread character tail.
(defun l1-api-namespace-heads (chars index line-start reversed)
  (declare (xargs :measure (acl2-count chars)))
  (if (endp chars)
      (reverse reversed)
    (l1-api-namespace-heads
     (cdr chars) (1+ index) (eql (car chars) #\Newline)
     (if (and line-start (eql (car chars) #\()
              (l1-api-byte-prefixes-p *l1-api-heads* chars))
         (cons (cons index chars) reversed)
       reversed))))

(defun l1-api-lf-index (chars index)
  (if (or (endp chars) (eql (car chars) #\Newline))
      index
    (l1-api-lf-index (cdr chars) (1+ index))))

(defun l1-api-first-line (chars)
  (coerce (take (l1-api-lf-index chars 0) chars) 'string))

(defun l1-api-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
        ((name (proof-term-at (car definitions) 0))
         (text (proof-write name))
         (rest (l1-api-definition-names (cdr definitions))))
      (cons text rest))))

(defun l1-api-helper-names (head)
  (cond ((text-starts-with head '("(lemma " "(choose "))
         (proof-with-checked-results
             ((cursor (reader-reader-take
                       (reader-reader head)
                       (if (text-starts-with head "(lemma ") "(lemma " "(choose ")))
              (datum (reader-reader-datum cursor))
              (name (proof-write (car datum))))
           (list name)))
        ((text-starts-with head "(define ")
         (proof-with-checked-results ((parsed (l1-api-parse head)))
           (l1-api-definition-names (cdadr parsed))))
        (t '(:failure "failure" ""))))

(defun l1-api-invalid-helper-name-p (names aliases)
  (and (consp names)
       (or (assoc-equal (car names) aliases)
           (not (text-starts-with (car names) *l1-api-original-symbol-prefixes*))
           (l1-api-invalid-helper-name-p (cdr names) aliases))))

(defun l1-api-numbered-names (names stem index result)
  (if (endp names)
      result
    (l1-api-numbered-names
     (cdr names) stem (1+ index)
     (table-put result (car names) (concatenate 'string stem (decimal-text index))))))

(defun l1-api-namespace-helper-key (raw head names aliases)
  ;; The badge block proof is determined by its generic conclusion and
  ;; the preceding support lemmas.
  (if (and (endp (cdr names))
           (text-starts-with (car names) *l1-api-badge-absence-prefix*))
      (concatenate 'string "badge lookup" *l1-api-newline* head *l1-api-newline*
                   (text-join " " (table-values aliases)))
    raw))

(defun l1-api-namespace-helper (raw head names occupied aliases)
  (if (l1-api-invalid-helper-name-p names aliases)
      '(:failure "failure" "")
    (let* ((placeholders (l1-api-numbered-names names "ACL2::PROVER-L1-HELPER-" 0 nil))
           (key (l1-api-namespace-helper-key raw head names aliases))
           (canonical (l1-api-namespace-replace key (table-update aliases placeholders)))
           (digest (text-upper (siphash-hexdigest canonical)))
           (stem (concatenate 'string *l1-api-symbol-prefix* digest "-"))
           (renamed (l1-api-numbered-names names stem 0 nil)))
      (if (or (intersectp-equal occupied names)
              (intersectp-equal occupied (table-values renamed))
              (intersectp-equal (table-values aliases) (table-values renamed)))
          '(:failure "failure" "")
        (let ((aliases (table-update aliases renamed)))
          (proof-with-checked-results
              ((lemma (l1-api-ascii-text (l1-api-namespace-replace raw aliases))))
            (cons lemma aliases)))))))

(defun l1-api-namespace-entry (chars aliases)
  (let* ((cut (l1-api-lf-index chars 0))
         (head (coerce (take cut chars) 'string)))
    (proof-with-checked-results ((parsed (l1-api-parse head)))
      (let ((kind (car parsed)))
        (if (not (member-equal kind '("theorem" "measure" "witness")))
            '(:failure "failure" "")
          (proof-with-checked-results
              ((name (proof-term-at (cadr parsed) 0))
               (written (proof-write name)))
            (let* ((first (+ (length kind) 2))
                   (index (text-find (subseq head first cut) written)))
              (if (< index 0)
                  '(:failure "failure" "")
                (let* ((target (+ index first (length written)))
                       (tail (coerce (nthcdr target chars) 'string))
                       (tail (if (consp (nthcdr cut chars))
                                 tail
                               (string-append tail *l1-api-newline*))))
                  (l1-api-ascii-text
                   (concatenate 'string (subseq head 0 target)
                                (l1-api-namespace-replace tail aliases))))))))))))

(defun l1-api-namespace-read-helper (source start joined next occupied aliases)
  (let* ((chars (cdr start))
         (head (l1-api-first-line chars))
         (choice (and joined (l1-api-byte-prefix-p *l1-api-choice-head* (cdr joined)))))
    (proof-with-checked-results
        ((names (l1-api-helper-names head))
         (names (if choice
                    (proof-with-checked-results
                        ((chosen (l1-api-helper-names (l1-api-first-line (cdr joined)))))
                      (append names chosen))
                  names)))
      (if (and joined (not choice)
               (not (l1-api-byte-prefix-p
                     (coerce (concatenate 'string "(measure " (car names) " ") 'list)
                     (cdr joined))))
          '(:failure "failure" "")
        (let ((raw (cond (next (coerce (take (- (car next) (car start)) chars) 'string))
                         ((eql (car start) 0) source)
                         (t (coerce chars 'string)))))
          (l1-api-namespace-helper raw head names occupied aliases))))))

(defun l1-api-namespace-entries (entries source final occupied aliases helpers skip-head)
  (declare (xargs :measure (acl2-count entries)))
  (cond
   ((endp entries) (list helpers aliases nil))
   (skip-head
    (l1-api-namespace-entries (cdr entries) source final occupied aliases helpers nil))
   ((and final (endp (cdr entries)))
    (proof-with-checked-results ((entry (l1-api-namespace-entry (cdar entries) aliases)))
      (list helpers aliases entry)))
   (t
    (let* ((start (car entries))
           (next (cadr entries))
           (joined (and (consp (cdr entries))
                        (or (not final) (consp (cddr entries)))
                        (l1-api-byte-prefix-p *l1-api-definition-head* (cdr start))
                        (or (l1-api-byte-prefix-p *l1-api-measure-head* (cdr next))
                            (l1-api-byte-prefix-p *l1-api-choice-head* (cdr next)))))
           (following (if joined (caddr entries) next)))
      (proof-with-checked-results
          ((helper (l1-api-namespace-read-helper source start (and joined next)
                                                following occupied aliases)))
        (l1-api-namespace-entries (cdr entries) source final occupied
                                  (cdr helper) (cons (car helper) helpers) joined))))))

; A fragment ends between entries. Keep only the current fragment's characters.
(defun l1-api-namespace-fragment (source final occupied aliases helpers)
  (let ((entries (l1-api-namespace-heads (coerce source 'list) 0 t nil)))
    (if (or (endp entries) (not (eql (caar entries) 0)))
        '(:failure "failure" "")
      (l1-api-namespace-entries entries source final occupied aliases helpers nil))))

(defun l1-api-namespace-fragments (sources occupied aliases helpers)
  (if (endp sources)
      '(:failure "failure" "")
    (let ((final (endp (cdr sources))))
      (proof-with-checked-results
          ((result (l1-api-namespace-fragment (car sources) final occupied aliases helpers)))
        (if final
            (list (reverse (car result)) (caddr result))
          (l1-api-namespace-fragments (cdr sources) occupied (cadr result) (car result)))))))

(defun l1-api-namespace-helpers-p (sources)
  (or (consp (cdr sources))
      (text-starts-with (car sources) '("(define " "(lemma " "(choose "))))

(defun l1-api-namespace (source context)
  (let ((sources (if (stringp source) (list source) source)))
    (proof-with-checked-results
        ((occupied (and (l1-api-namespace-helpers-p sources) (l1-api-context-names context))))
      (l1-api-namespace-fragments sources occupied nil nil))))

(defun l1-api-extend-row (context row)
  (let ((choices (cadr context))
        (seen (caddr context)))
    (proof-with-checked-results ((raw (l1-api-raw row)))
      (if (member-equal raw seen)
          context
        (proof-with-checked-results
            ((parsed (l1-api-parse raw))
             (admitted (l1-witness-admit (car context) (car parsed) (cadr parsed))))
          (list (cdr admitted)
                (if (car admitted) (cons (car admitted) choices) choices)
                (cons raw seen)))))))

(defun l1-api-extend-rows (context rows)
  (declare (xargs :measure (acl2-count rows)))
  (cond ((failure-p context) context)
        ((endp rows) (list (car context) (reverse (cadr context))
                          (l1-api-string-set (caddr context))))
        (t (l1-api-extend-rows (l1-api-extend-row context (car rows)) (cdr rows)))))

(defun l1-api-extend (proof choices seen rows)
  (l1-api-extend-rows (list proof (reverse choices) seen) rows))

(defun l1-api-library (rows)
  (l1-api-extend (l1-warrant-warrant-proof-init) nil nil rows))

(defun l1-api-common-lisp-definition-p (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
        ((definition (proof-list-of-length (car definitions) 3))
         (package (proof-term-at (car definition) 1)))
      (if (equal package "COMMON-LISP")
          t
        (l1-api-common-lisp-definition-p (cdr definitions))))))

(defun l1-api-aid-measure (line stored)
  (cond ((not (stringp line)) '(:failure "failure" ""))
        ((text-starts-with line "(measure ")
         (proof-with-checked-results
             ((raw (l1-api-raw line))
              (parsed (l1-api-parse raw))
              (name (proof-term-at (cadr parsed) 0)))
           (table-put stored name (seq-slice (cadr parsed) 1 3))))
        (t stored)))

(defun l1-api-aid-measures (aids stored)
  (declare (xargs :measure (acl2-count aids)))
  (if (or (failure-p stored) (endp aids))
      stored
    (l1-api-aid-measures (cdr aids) (l1-api-aid-measure (car aids) stored))))

(defun l1-api-helper-sources (helpers)
  (if (endp helpers)
      nil
    (let ((entry (car helpers)))
      (cons (cadddr entry) (l1-api-helper-sources (cdr helpers))))))

(defun l1-api-certificate-sources-prepared (proof choices raw kind data name calls stored preparation)
  (proof-with-checked-results
      ((generated (l1-books-generate-prepared proof choices
                                              (concatenate 'string raw *l1-api-newline*)
                                              kind data name calls stored preparation)))
    (cond ((equal (l1-books-certificate-reason generated) "")
           (append (l1-api-helper-sources (l1-books-certificate-helpers generated))
                   (l1-books-certificate-sources generated)))
          ((equal kind "constrain")
           (proof-with-checked-results ((parts (l1-warrant-warrant-parts data)))
             (and parts (eq (caddr parts) :none)
                  (proof-with-checked-results
                      ((result (l1-warrant-warrant-lemmas proof data choices t)))
                    (and result (equal (caddr result) "") (list (cadr result)))))))
          (t nil))))

(defun l1-api-parsed-obligation (raw parsed)
  (proof-with-checked-results ((parsed parsed))
    (let ((kind (car parsed))
          (data (cadr parsed)))
      (if (not (member-equal kind '("define" "constrain" "theorem")))
          nil
        (proof-with-checked-results
            ((protected (and (equal kind "define")
                             (l1-api-common-lisp-definition-p (cdr data))))
             (obligation (and (not protected) (l1-books-obligation kind data))))
          (and (car obligation)
               (list* raw kind data obligation)))))))

(defun l1-api-obligation-sources (proof choices obligation stored preparation)
  (l1-api-certificate-sources-prepared
   proof choices (car obligation) (cadr obligation) (caddr obligation)
   (cadddr obligation) (car (cddddr obligation)) stored preparation))

(defun l1-api-context-sources (proof choices obligation aids)
  (proof-with-checked-results
      ((stored (and (equal (cadr obligation) "define") (l1-api-aid-measures aids nil))))
    (l1-api-obligation-sources proof choices obligation stored nil)))

(defun l1-api-certificate-sources (statement earlier library aids)
  (proof-with-checked-results ((raw (l1-api-raw statement))
                               (obligation (l1-api-parsed-obligation raw (l1-api-parse raw))))
    (and obligation
         (proof-with-checked-results
             ((given (l1-api-library library))
              (context (l1-api-extend (car given) (cadr given) (caddr given) earlier)))
           (and (not (member-equal raw (caddr context)))
                (l1-api-context-sources (car context) (cadr context) obligation aids))))))

(defun l1-api-certificate (statement earlier library aids)
  (proof-with-checked-results ((sources (l1-api-certificate-sources statement earlier library aids)))
    (and sources (l1-warrant-join-sources 1000000 sources))))

(defun l1-api-prove (statement earlier library aids)
  (let ((sources (l1-api-certificate-sources statement earlier library aids)))
    (if (or (null sources) (failure-p sources))
        nil
      (let ((result (l1-api-namespace sources (append library earlier (cons statement aids)))))
        (if (failure-p result) nil result)))))
