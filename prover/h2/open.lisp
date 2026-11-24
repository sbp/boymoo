(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h2-open-tree-height (tree)
  (nfix (cadr tree)))

(defun h2-open-tree-rebuild (node left right)
  (list (car node) (1+ (max (h2-open-tree-height left) (h2-open-tree-height right)))
        left right (nth 4 node)))

(defun h2-open-tree-rotate-left (node left right)
  (h2-open-tree-rebuild right (h2-open-tree-rebuild node left (caddr right)) (cadddr right)))

(defun h2-open-tree-rotate-right (node left right)
  (h2-open-tree-rebuild left (caddr left) (h2-open-tree-rebuild node (cadddr left) right)))

(defun h2-open-tree-balance (node left right)
  (let ((left-height (h2-open-tree-height left))
        (right-height (h2-open-tree-height right)))
    (cond ((> left-height (1+ right-height))
           (h2-open-tree-rotate-right
            node (if (< (h2-open-tree-height (caddr left)) (h2-open-tree-height (cadddr left)))
                    (h2-open-tree-rotate-left left (caddr left) (cadddr left))
                  left)
            right))
          ((> right-height (1+ left-height))
           (h2-open-tree-rotate-left
            node left
            (if (> (h2-open-tree-height (caddr right)) (h2-open-tree-height (cadddr right)))
                (h2-open-tree-rotate-right right (caddr right) (cadddr right))
              right)))
          (t (h2-open-tree-rebuild node left right)))))

(defun h2-open-tree-add (key value tree)
  (cond ((endp tree) (list key 1 nil nil value))
        ((equal key (car tree)) tree)
        ((string< key (car tree))
         (h2-open-tree-balance tree (h2-open-tree-add key value (caddr tree)) (cadddr tree)))
        (t (h2-open-tree-balance tree (caddr tree) (h2-open-tree-add key value (cadddr tree))))))

(defun h2-open-tree-add-lines (lines tree)
  (if (endp lines)
      tree
    (h2-open-tree-add-lines (cdr lines) (h2-open-tree-add (car lines) nil tree))))

(defun h2-open-index-library (parsed seen private)
  (if (endp parsed)
      (list seen private)
    (let ((raw (caar parsed)))
      (h2-open-index-library
       (cdr parsed) (h2-open-tree-add raw (car parsed) seen)
       (h2-open-tree-add-lines (h2-api-private-findall raw) private)))))

(defun h2-open-make-context (proof seen private trial)
  (list :h2-session-context proof seen private trial))

(defun h2-open-context-proof (context) (cadr context))
(defun h2-open-context-seen (context) (caddr context))
(defun h2-open-context-private (context) (cadddr context))
(defun h2-open-context-trial (context) (nth 4 context))

(defun h2-open-make-session (base earlier context aids-cache)
  (list :h2-session base earlier context aids-cache))

(defun h2-open-session-base (session) (cadr session))
(defun h2-open-session-earlier (session) (caddr session))
(defun h2-open-session-context (session) (cadddr session))
(defun h2-open-session-aids-cache (session) (nth 4 session))

(defun h2-open-library-context (library)
  (proof-with-checked-results
      ((lines (h2-api-input-sequence library))
       (parsed (h2-api-parse-lines lines nil))
       (proof (h2-books-book-proof-init parsed)))
    (let* ((indexes (h2-open-index-library parsed nil nil))
           (proof (h2-books-book-proof-prepare-calls (h2-books-book-proof-fork proof)))
           (search (h2-search-search-prepare-not-nil (h2-books-book-proof-search proof)))
           (proof (h2-books-book-proof-with-search proof search)))
      (h2-open-make-context proof (car indexes) (cadr indexes) :unprepared))))

(defun h2-api-open (library)
  (let ((base (h2-open-library-context library)))
    (h2-open-make-session base nil base nil)))

; A successful comparison returns the suffix, including a successful empty suffix.
(defun h2-open-prefix-suffix (prefix lines)
  (cond ((endp prefix) (cons t lines))
        ((or (endp lines) (not (equal (car prefix) (car lines)))) nil)
        (t (h2-open-prefix-suffix (cdr prefix) (cdr lines)))))

(defun h2-open-line-end (line length)
  (declare (xargs :measure (nfix length)))
  (if (and (not (zp length))
           (member-equal (char line (1- length)) '(#\Return #\Newline)))
      (h2-open-line-end line (1- length))
    (nfix length)))

(defun h2-open-line-key (line)
  (if (stringp line)
      (let* ((length (length line))
             (end (h2-open-line-end line length)))
        (if (and (= (1+ end) length) (eql (char line end) #\Newline))
            line
          (concatenate 'string (subseq line 0 end) *h2-api-newline*)))
    nil))

(defun h2-open-parse-line (line key known)
  (let ((node (and key (h2-api-string-tree-find key known))))
    (if node (nth 4 node) (h2-api-parse line))))

(defun h2-open-advance-lines (lines context known)
  (if (endp lines)
      context
    (let* ((line (car lines))
           (key (h2-open-line-key line))
           (seen (h2-open-context-seen context)))
      (if (and key (h2-api-string-tree-has-p key seen))
          (h2-open-advance-lines (cdr lines) context known)
        (proof-with-checked-results
            ((parsed (h2-open-parse-line line key known))
             (proof (h2-books-book-proof-add-statement (h2-open-context-proof context)
                                                      (cadr parsed) (caddr parsed))))
          (let* ((raw (car parsed))
                 (proof (if (equal (cadr parsed) "define")
                            (h2-books-book-proof-note-definition-calls proof (cdr (caddr parsed)))
                          proof))
                 (private (h2-open-tree-add-lines (h2-api-private-findall raw)
                                                  (h2-open-context-private context))))
            (h2-open-advance-lines
             (cdr lines)
             (h2-open-make-context proof (h2-open-tree-add raw parsed seen) private :unprepared)
             known)))))))

(defun h2-open-advance-prefix (session earlier index-names)
  (let* ((suffix (h2-open-prefix-suffix (h2-open-session-earlier session) earlier))
         (base (h2-open-session-base session))
         (previous (h2-open-session-context session))
         (context (if suffix previous base))
         (known (and (not suffix) (h2-open-context-seen previous)))
         (lines (if suffix (cdr suffix) earlier))
         (context (if index-names
                      (update-nth 1
                                  (h2-books-book-proof-index-prefix-names (h2-open-context-proof context) lines)
                                  context)
                    context)))
    (proof-with-checked-results
        ((context (h2-open-advance-lines lines context known)))
      (let ((context (if index-names
                         (update-nth 1
                                     (h2-books-book-proof-restore-written-names (h2-open-context-proof context))
                                     context)
                       context)))
        (h2-open-make-session base earlier context (h2-open-session-aids-cache session))))))

(defun h2-open-advance (session earlier)
  (h2-open-advance-prefix session earlier nil))

(defun h2-open-prove-trial (trial parsed name aids private)
  (proof-with-checked-results
      ((trial trial)
       (entries (if (equal (cadr parsed) "theorem")
                    (h2-api-theorem-entries-from-proof trial trial (caddr parsed) name
                                                      (car aids) (cadr aids))
                  (h2-api-find-entries trial (cadr parsed) (caddr parsed) name
                                       (car aids) (cadr aids)))))
    (and entries (h2-api-namespaced-with-tree entries (h2-api-private-findall (car parsed)) private))))

(defun h2-open-prove-current (session parsed name lines)
  (let* ((context (h2-open-session-context session))
         (cache (h2-open-session-aids-cache session))
         (found (assoc-equal lines cache))
         (aids (if found (cdr found) (h2-api-aids lines))))
    (if (failure-p aids)
        (cons nil session)
      (let* ((cache (cons (cons lines aids) (seq-slice (remove-assoc-equal lines cache) 0 3)))
             (trial (h2-open-context-trial context))
             (trial (if (eq trial :unprepared)
                        (h2-api-proof-trial (h2-open-context-proof context))
                      trial))
             (answer (h2-open-prove-trial trial parsed name aids (h2-open-context-private context)))
             (session (h2-open-make-session (h2-open-session-base session)
                                           (h2-open-session-earlier session)
                                           (update-nth 4 trial context) cache)))
        (cons (if (failure-p answer) nil answer) session)))))

(defun h2-open-request (statement earlier aids known)
  (proof-with-checked-results
      ((earlier (h2-api-input-sequence earlier))
       (aids (h2-api-input-sequence aids))
       (parsed (h2-open-parse-line statement (h2-open-line-key statement) known)))
    (if (member-equal (cadr parsed) '("define" "constrain" "theorem"))
        (proof-with-checked-results ((name (h2-books-statement-name (cadr parsed) (caddr parsed))))
          (and name (list parsed name earlier aids)))
      nil)))

(defun h2-api-prove-open (session statement earlier aids)
  (if (failure-p (h2-open-session-base session))
      (cons nil session)
    (let* ((known (h2-open-context-seen (h2-open-session-context session)))
           (request (h2-open-request statement earlier aids known)))
      (if (or (null request) (failure-p request))
          (cons nil session)
        (let* ((parsed (car request))
               (next (h2-open-advance-prefix session (caddr request) t)))
          (cond ((failure-p next) (cons nil session))
                ((h2-api-string-tree-has-p (car parsed)
                                           (h2-open-context-seen (h2-open-session-context next)))
                 (cons nil next))
                (t (h2-open-prove-current next parsed (cadr request) (cadddr request)))))))))

(defun h2-open-prove-all (session cases reversed)
  (if (endp cases)
      (reverse reversed)
    (let* ((case (car cases))
           (result (h2-api-prove-open session (car case) (cadr case) (caddr case))))
      (h2-open-prove-all (cdr result) (cdr cases) (cons (car result) reversed)))))

(defun h2-api-prove-all (library cases)
  (h2-open-prove-all (h2-api-open library) cases nil))

(defun h2-api-prove-all-loop (library cases)
  (h2-api-prove-all library cases))
