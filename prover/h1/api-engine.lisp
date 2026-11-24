(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-api-engine-newlines* (coerce (list #\Return #\Newline) 'string))
(defconst *h1-api-engine-quotation* "(COMMON-LISP::QUOTE ")
(defconst *h1-api-engine-quotation-chars* (coerce *h1-api-engine-quotation* 'list))
(defconst *h1-api-engine-quotation-width* (length *h1-api-engine-quotation*))
(defconst *h1-api-engine-symbol-punctuation*
  (coerce "+*/<=>!?$%&_^~.@-" 'list))

(defun h1-api-engine-line-break-p (char)
  (let ((code (char-code char)))
    (or (and (<= 10 code) (<= code 13))
        (and (<= 28 code) (<= code 30)))))

(defun h1-api-engine-split-lines (characters line)
  (cond ((endp characters)
         (and (consp line) (list (coerce (reverse line) 'string))))
        ((and (eql (car characters) #\Return)
              (eql (cadr characters) #\Newline))
         (cons (coerce (reverse (list* #\Newline #\Return line)) 'string)
               (h1-api-engine-split-lines (cddr characters) nil)))
        ((h1-api-engine-line-break-p (car characters))
         (cons (coerce (reverse (cons (car characters) line)) 'string)
               (h1-api-engine-split-lines (cdr characters) nil)))
        (t (h1-api-engine-split-lines (cdr characters)
                                      (cons (car characters) line)))))

(defun h1-api-engine-as-lines (source)
  (cond ((stringp source) (h1-api-engine-split-lines (coerce source 'list) nil))
        ((true-listp source) source)
        (t '(:failure "failure" ""))))

(defun h1-api-engine-strip-line (raw)
  (if (stringp raw)
      (text-strip-right raw *h1-api-engine-newlines*)
    '(:failure "failure" "")))

(defun h1-api-engine-parse (raw)
  (proof-with-checked-results
   ((raw (h1-api-engine-strip-line raw))
    (parsed (reader-reader-line (reader-reader raw))))
   (list (caar parsed) (proof-freeze (cadar parsed)))))

(defun h1-api-engine-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car definitions) 0))
      (rest (h1-api-engine-definition-names (cdr definitions))))
     (cons name rest))))

(defun h1-api-engine-pair-names (declarations)
  (cond ((integerp declarations) '(:failure "failure" ""))
        ((endp declarations) nil)
        (t (proof-with-checked-results
            ((declaration (proof-list-of-length (car declarations) 2))
             (rest (h1-api-engine-pair-names (cdr declarations))))
            (cons (car declaration) rest)))))

(defun h1-api-engine-statement-names (kind fields)
  (cond
   ((equal kind "define")
    (if (integerp fields)
        '(:failure "failure" "")
      (h1-api-engine-definition-names (cdr fields))))
   ((equal kind "constrain")
    (proof-with-checked-results
     ((facts (proof-term-at fields 1))
      (fact-names (if (equal facts *proof-nil*) nil (h1-api-engine-pair-names facts)))
      (function-names (h1-api-engine-pair-names (car fields))))
     (append function-names fact-names)))
   ((member-equal kind '("theorem" "axiom" "choose" "reserve"))
    (proof-with-checked-results ((name (proof-term-at fields 0)))
      (list name)))
   (t nil)))

(defun h1-api-engine-make-world (earlier proof seen names)
  (list :h1-api-engine-world earlier proof seen names))

(defun h1-api-engine-world-earlier (world)
  (cadr world))

(defun h1-api-engine-world-proof (world)
  (caddr world))

(defun h1-api-engine-world-seen (world)
  (cadddr world))

(defun h1-api-engine-world-names (world)
  (car (cddddr world)))

(defun h1-api-engine-write-atom (datum)
  (if (null datum)
      '(:failure "failure" "")
    (reader-write datum)))

(mutual-recursion
 (defun h1-api-engine-write-frozen-into (datum reversed)
   (declare (xargs :measure (1+ (* 2 (acl2-count datum)))))
   (if (and (consp datum) (proof-compound datum))
       (h1-api-engine-write-frozen-items datum t (cons #\( reversed))
     (proof-with-checked-results
      ((text (cond ((null datum) (h1-api-engine-write-atom *proof-nil*))
                   ((or (integerp datum) (eq datum t) (consp datum))
                    (h1-api-engine-write-atom datum))
                   (t (proof-write datum)))))
      (revappend (coerce text 'list) reversed))))
 (defun h1-api-engine-write-frozen-items (items first reversed)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (cond
    ((endp items) (cons #\) reversed))
    ((and (endp (cdr items)) (consp (car items)) (equal (caar items) "dot"))
     (if (endp (cdar items))
         '(:failure "failure" "")
       (proof-with-checked-results
        ((tail (h1-api-engine-write-frozen-into (cadar items)
                                             (list* #\Space #\. #\Space reversed))))
        (cons #\) tail))))
    (t (proof-with-checked-results
        ((reversed (h1-api-engine-write-frozen-into
                    (car items) (if first reversed (cons #\Space reversed)))))
        (h1-api-engine-write-frozen-items (cdr items) nil reversed))))))

(defun h1-api-engine-write-frozen (datum)
  (proof-with-checked-results ((written (h1-api-engine-write-frozen-into datum nil)))
    (coerce (reverse written) 'string)))

(defun h1-api-engine-hex-digit-p (char)
  (and (characterp char)
       (let ((code (char-code char)))
         (or (and (<= 48 code) (<= code 57))
             (and (<= 65 code) (<= code 70))))))

(defun h1-api-engine-escaped-width (characters delimiter width)
  (cond ((endp characters) 0)
        ((eql (car characters) delimiter) (1+ width))
        ((eql (car characters) #\\)
         (if (and (h1-api-engine-hex-digit-p (cadr characters))
                  (h1-api-engine-hex-digit-p (caddr characters)))
             (h1-api-engine-escaped-width (cdddr characters) delimiter (+ 3 width))
           0))
        (t (h1-api-engine-escaped-width (cdr characters) delimiter (1+ width)))))

(defun h1-api-engine-escaped-token-width (characters)
  (if (member-equal (car characters) '(#\" #\|))
      (h1-api-engine-escaped-width (cdr characters) (car characters) 1)
    0))

(defun h1-api-engine-quotation-end-chars (characters offset depth skip)
  (cond
   ((endp characters) '(:failure "failure" ""))
   ((not (zp skip))
    (h1-api-engine-quotation-end-chars (cdr characters) (1+ offset) depth (1- skip)))
   ((eql (car characters) #\))
    (if (= depth 1)
        (1+ offset)
      (h1-api-engine-quotation-end-chars (cdr characters) (1+ offset) (1- depth) 0)))
   ((eql (car characters) #\()
    (h1-api-engine-quotation-end-chars (cdr characters) (1+ offset) (1+ depth) 0))
   (t (let ((width (h1-api-engine-escaped-token-width characters)))
        (h1-api-engine-quotation-end-chars (cdr characters) (1+ offset) depth
                                           (if (= width 0) 0 (1- width)))))))

(defun h1-api-engine-quotation-end (source start)
  (let ((start (min (nfix start) (length source))))
    (h1-api-engine-quotation-end-chars (nthcdr start (coerce source 'list)) start 1 0)))

(defun h1-api-engine-prefix-p (prefix characters)
  (or (endp prefix)
      (and (eql (car prefix) (car characters))
           (h1-api-engine-prefix-p (cdr prefix) (cdr characters)))))

(defun h1-api-engine-quoted-atom-width (characters width)
  (cond ((endp characters) 0)
        ((eql (car characters) #\)) (if (= width 0) 0 (1+ width)))
        ((member-equal (car characters) '(#\Space #\" #\| #\()) 0)
        (t (h1-api-engine-quoted-atom-width (cdr characters) (1+ width)))))

; Escaped text and complete quotations occupy spans in which names are data.
(defun h1-api-engine-unscoped-width (characters offset)
  (if (and (eql (car characters) #\()
           (h1-api-engine-prefix-p *h1-api-engine-quotation-chars* characters))
      (let* ((prefix-width *h1-api-engine-quotation-width*)
             (body (nthcdr prefix-width characters))
             (atom-width (h1-api-engine-quoted-atom-width body 0)))
        (if (= atom-width 0)
            (proof-with-checked-results
             ((end (h1-api-engine-quotation-end-chars body (+ offset prefix-width) 1 0)))
             (- end offset))
          (+ prefix-width atom-width)))
    (h1-api-engine-escaped-token-width characters)))

(defun h1-api-engine-symbol-char-p (char)
  (and (characterp char)
       (let ((code (char-code char)))
         (or (and (<= 65 code) (<= code 90))
             (and (<= 48 code) (<= code 57))
             (member-equal char *h1-api-engine-symbol-punctuation*)))))

(defun h1-api-engine-symbol-suffix-width (characters width)
  (if (and (consp characters) (h1-api-engine-symbol-char-p (car characters)))
      (h1-api-engine-symbol-suffix-width (cdr characters) (1+ width))
    width))

(defun h1-api-engine-local-prefix-width (characters)
  (cond ((h1-api-engine-prefix-p '(#\A #\C #\L #\2 #\: #\: #\S #\E #\L #\F #\-)
                                 characters)
         11)
        ((h1-api-engine-prefix-p '(#\A #\C #\L #\2 #\: #\: #\H #\1 #\-)
                                 characters)
         9)
        (t 0)))

(defun h1-api-engine-scoped-width (characters previous)
  (if (and (eql (car characters) #\A)
           (not (h1-api-engine-symbol-char-p previous)))
      (let* ((prefix-width (h1-api-engine-local-prefix-width characters))
             (suffix-width (if (= prefix-width 0) 0
                             (h1-api-engine-symbol-suffix-width
                              (nthcdr prefix-width characters) 0))))
        (if (= suffix-width 0) 0 (+ prefix-width suffix-width)))
    0))

(defun h1-api-engine-scoped-scan (characters offset previous skip source names copied pieces)
  (cond
   ((endp characters)
    (if (endp pieces)
        source
      (text-join "" (reverse (cons (seq-slice source copied :none) pieces)))))
   ((not (zp skip))
    (h1-api-engine-scoped-scan (cdr characters) (1+ offset) (car characters)
                               (1- skip) source names copied pieces))
   (t (proof-with-checked-results
       ((width (h1-api-engine-unscoped-width characters offset)))
       (if (not (= width 0))
           (h1-api-engine-scoped-scan (cdr characters) (1+ offset) (car characters)
                                      (1- width) source names copied pieces)
         (let* ((width (h1-api-engine-scoped-width characters previous))
                (end (+ offset width))
                (new (and (not (= width 0))
                          (table-get names (coerce (take width characters) 'string) nil))))
           (h1-api-engine-scoped-scan
            (cdr characters) (1+ offset) (car characters) (if (= width 0) 0 (1- width))
            source names (if new end copied)
            (if new (list* new (seq-slice source copied offset) pieces) pieces))))))))

(defun h1-api-engine-scoped-symbols (source names)
  (if (endp names)
      source
    (h1-api-engine-scoped-scan (coerce source 'list) 0 nil 0 source names 0 nil)))

(defun h1-api-engine-first-auxiliary-group (entries)
  (proof-with-checked-results ((kind (proof-term-at (car entries) 0)))
    (cond ((and (equal kind "define") (consp (cdr entries)))
           (proof-with-checked-results ((name (proof-term-at (car entries) 1)))
             (if (equal (take 2 (cadr entries)) (list "measure" name))
                 (list (car entries) (cadr entries))
               (list (car entries)))))
          ((member-equal kind '("define" "lemma")) (list (car entries)))
          (t '(:failure "failure" "")))))

(defun h1-api-engine-auxiliary-groups (entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (endp entries)
      nil
    (proof-with-checked-results
     ((group (h1-api-engine-first-auxiliary-group entries))
      (rest (h1-api-engine-auxiliary-groups (if (consp (cdr group)) (cddr entries) (cdr entries)))))
     (cons group rest))))

(defun h1-api-engine-attempt-install (proof install)
  (let* ((extended (h1-books-book-prover-fork proof))
         (installed (h1-books-install extended install)))
    (if (failure-p installed) proof installed)))

(defun h1-api-engine-attempt-installs (proof installers)
  (if (endp installers)
      proof
    (h1-api-engine-attempt-installs
     (h1-api-engine-attempt-install proof (car installers)) (cdr installers))))

(defun h1-api-engine-extend-set (items reversed)
  (if (endp items)
      reversed
    (h1-api-engine-extend-set (cdr items)
                             (if (member-equal (car items) reversed)
                                 reversed
                               (cons (car items) reversed)))))

(defun h1-api-engine-raw-line (source)
  (h1-api-engine-strip-line source))

(defun h1-api-engine-admit-line (raw proof)
  (proof-with-checked-results
   ((parsed (h1-api-engine-parse raw))
    (proof (h1-books-admit proof (car parsed) (cadr parsed) :register-theorem))
    (declared (h1-api-engine-statement-names (car parsed) (cadr parsed))))
   (list proof parsed declared)))

(defun h1-api-engine-admit-lines (lines proof seen names deferred installers)
  (if (endp lines)
      (list proof seen names installers)
    (proof-with-checked-results ((raw (h1-api-engine-raw-line (car lines))))
      (if (member-equal raw seen)
          (h1-api-engine-admit-lines (cdr lines) proof seen names deferred installers)
        (proof-with-checked-results
         ((admitted (h1-api-engine-admit-line raw proof))
          (names (h1-api-engine-extend-set (caddr admitted) names))
          (tactics (h1-books-declaration-tactics (caadr admitted) (cadadr admitted))))
         (let ((proof (car admitted)))
           (h1-api-engine-admit-lines
            (cdr lines) (if deferred proof (h1-api-engine-attempt-installs proof tactics))
            (cons raw seen) names deferred
            (if deferred (revappend tactics installers) installers))))))))

(defun h1-api-engine-given-proof ()
  (proof-with-checked-results
   ((proof (h1-books-book-prover-init))
    (proof (h1-tactics-prover-setup-rules proof))
    (proof (h1-books-book-prover-build proof)))
   (h1-book-termination-install-selector-tests proof)))

(defun h1-api-engine-install-given (proof installers)
  (h1-api-engine-attempt-installs
   (h1-api-engine-attempt-installs proof *h1-books-base-tactics*)
   (reverse installers)))

(defun h1-api-engine-given-world (library)
  (proof-with-checked-results
   ((proof (h1-api-engine-given-proof))
    (admitted (h1-api-engine-admit-lines library proof nil nil t nil)))
   (let ((proof (h1-api-engine-install-given (car admitted) (cadddr admitted))))
     (h1-api-engine-make-world nil proof (reverse (cadr admitted)) (reverse (caddr admitted))))))

(defun h1-api-engine-statement-world (earlier library)
  (proof-with-checked-results
   ((world (h1-api-engine-given-world library)))
   (if (equal earlier (h1-api-engine-world-earlier world))
       world
     (proof-with-checked-results
      ((admitted (h1-api-engine-admit-lines
                  earlier (h1-books-book-prover-fork (h1-api-engine-world-proof world))
                  (reverse (h1-api-engine-world-seen world))
                  (reverse (h1-api-engine-world-names world)) nil nil)))
      (h1-api-engine-make-world earlier (car admitted)
                               (reverse (cadr admitted)) (reverse (caddr admitted)))))))

(defun h1-api-engine-measures (aids)
  (h1-books-parse-measures aids))

(defun h1-api-engine-entry-sources (entries)
  (if (endp entries)
      nil
    (cons (cadddr (car entries)) (h1-api-engine-entry-sources (cdr entries)))))

(defun h1-api-engine-export-names (declared source public additions)
  (if (endp declared)
      (cons t additions)
    (proof-with-checked-results
     ((old (proof-write (car declared))))
     (let* ((digest (siphash-hexdigest
                     (concatenate 'string source (coerce (list (code-char 0)) 'string) old)))
            (digest (text-upper digest))
            (new (list (caar declared) (cadar declared)
                       (concatenate 'string "PROVER-H1-" digest))))
       (if (or (member-equal new public)
               (not (text-starts-with old '("ACL2::SELF-" "ACL2::H1-"))))
           nil
         (proof-with-checked-results
          ((written (proof-write new)))
          (h1-api-engine-export-names (cdr declared) source public
                                     (table-put additions old written))))))))

(defun h1-api-engine-export-group (group public names)
  (proof-with-checked-results
   ((declared (h1-books-entry-names (car group))))
   (if (intersectp-equal declared public)
       nil
     (proof-with-checked-results
      ((source (h1-api-engine-scoped-symbols
                (text-join "" (h1-api-engine-entry-sources group)) names))
       (added (h1-api-engine-export-names declared source public nil)))
      (if (not added)
          nil
        (proof-with-checked-results
         ((source (h1-api-engine-scoped-symbols source (cdr added))))
         (cons source (table-update names (cdr added)))))))))

(defun h1-api-engine-export-auxiliaries (entries entry public names auxiliaries in-group)
  (declare (xargs :measure (acl2-count entries)))
  (cond
   ((endp entries)
    (proof-with-checked-results
     ((source (h1-api-engine-scoped-symbols (cadddr entry) names)))
     (list (reverse auxiliaries) source)))
   (in-group
    (h1-api-engine-export-auxiliaries (cdr entries) entry public names auxiliaries nil))
   (t (proof-with-checked-results
       ((group (h1-api-engine-first-auxiliary-group entries))
        (exported (h1-api-engine-export-group group public names)))
       (and exported
            (h1-api-engine-export-auxiliaries
             (cdr entries) entry public (cdr exported)
             (cons (car exported) auxiliaries) (consp (cdr group))))))))

(defun h1-api-engine-export (proof entry public)
  (proof-with-checked-results
   ((needed (h1-books-used-entries
             (library-library-entries (h1-tactics-prover-library proof)) entry)))
   (h1-api-engine-export-auxiliaries (butlast needed 1) entry public nil nil nil)))

(defun h1-api-engine-theorem-entry (proof original fields)
  (proof-with-checked-results
   ((fields (proof-list-of-length fields 2)))
   (let ((entry (h1-books-theorem-entry proof fields)))
     (if (failure-p entry)
         (let* ((proof (h1-books-book-prover-fork original))
                (proof (h1-books-book-prover-with-case-limit proof 160))
                (proof (h1-books-book-prover-with-search-work proof 20000))
                (name (car fields))
                (formula (cadr fields)))
           (proof-with-checked-results
            ((final (h1-recipes-prove-by-shape proof formula))
             (step (proof-proof-subsume (h1-tactics-prover-proof (cdr final))
                                        (car final) (list formula)))
             (entry (proof-proof-entry "theorem" name (list name) (list step))))
            (cons entry (cdr final))))
       entry))))

(defun h1-api-engine-define-entry (proof fields calls measures)
  (proof-with-checked-results
   ((entry (h1-book-termination-termination-entry proof (cdr fields) calls measures)))
   (cons entry proof)))

(defun h1-api-engine-construct-entry (proof original raw kind fields calls aids)
  (cond
   ((equal kind "define")
    (proof-with-checked-results
     ((aids (h1-api-engine-as-lines aids))
      (stored (h1-api-engine-measures aids)))
     (h1-api-engine-define-entry proof fields calls stored)))
   ((equal kind "constrain")
    (h1-book-witness-witness-entry proof (concatenate 'string raw (coerce (list #\Newline) 'string))
                                  fields))
   (t (h1-api-engine-theorem-entry proof original fields))))

(defun h1-api-engine-finish-entry (built kind fields names)
  (proof-with-checked-results
   ((built built)
    (declared (h1-api-engine-statement-names kind fields)))
   (h1-api-engine-export (cdr built) (car built)
                         (h1-api-engine-extend-set declared names))))

(defun h1-api-engine-prove-statement (raw kind fields calls earlier library aids)
  (proof-with-checked-results
   ((earlier (h1-api-engine-as-lines earlier))
    (library (h1-api-engine-as-lines library))
    (world (h1-api-engine-statement-world earlier library)))
   (if (member-equal raw (h1-api-engine-world-seen world))
       nil
     (let ((original (h1-api-engine-world-proof world)))
       (h1-api-engine-finish-entry
        (h1-api-engine-construct-entry (h1-books-book-prover-fork original) original
                                       raw kind fields calls aids)
        kind fields (h1-api-engine-world-names world))))))

(defun h1-api-engine-proof-target (statement)
  (proof-with-checked-results
   ((raw (h1-api-engine-raw-line statement))
    (parsed (h1-api-engine-parse raw)))
   (let ((kind (car parsed)) (fields (cadr parsed)))
     (cond ((equal kind "define")
            (proof-with-checked-results
             ((rulers (proof-term-at fields 0))
              (calls (termination-recursive-calls rulers (cdr fields))))
             (and (consp calls) (list raw kind fields calls))))
           ((equal kind "constrain")
            (proof-with-checked-results
             ((facts (proof-term-at fields 1)))
             (and (not (equal facts *proof-nil*)) (list raw kind fields nil))))
           ((equal kind "theorem")
            (list raw kind fields nil))
           (t nil)))))

(defun h1-api-engine-prove (statement earlier library aids)
  (proof-with-checked-results ((target (h1-api-engine-proof-target statement)))
    (and target
         (h1-api-engine-prove-statement (car target) (cadr target) (caddr target)
                                        (cadddr target) earlier library aids))))
