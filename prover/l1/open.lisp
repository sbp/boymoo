(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

; The row index is an AVL tree keyed by the ASCII line without trailing LFs.
(defun l1-api-row-index-node (row left right)
  (list row (1+ (max (nfix (cadr left)) (nfix (cadr right)))) left right))

(defun l1-api-row-index-rotate-left (row left right)
  (l1-api-row-index-node (car right)
                        (l1-api-row-index-node row left (caddr right))
                        (cadddr right)))

(defun l1-api-row-index-rotate-right (row left right)
  (l1-api-row-index-node (car left) (caddr left)
                        (l1-api-row-index-node row (cadddr left) right)))

(defun l1-api-row-index-balance (row left right)
  (let ((left-height (nfix (cadr left)))
        (right-height (nfix (cadr right))))
    (cond ((> left-height (1+ right-height))
           (let ((outer (caddr left)) (inner (cadddr left)))
             (l1-api-row-index-rotate-right
              row (if (< (nfix (cadr outer)) (nfix (cadr inner)))
                      (l1-api-row-index-rotate-left (car left) outer inner)
                    left)
              right)))
          ((> right-height (1+ left-height))
           (let ((inner (caddr right)) (outer (cadddr right)))
             (l1-api-row-index-rotate-left
              row left (if (< (nfix (cadr outer)) (nfix (cadr inner)))
                           (l1-api-row-index-rotate-right (car right) inner outer)
                         right))))
          (t (l1-api-row-index-node row left right)))))

(defun l1-api-row-index-insert (row tree)
  (declare (xargs :measure (acl2-count tree)))
  (cond ((endp tree) (l1-api-row-index-node row nil nil))
        ((equal row (car tree)) tree)
        ((string< row (car tree))
         (l1-api-row-index-balance (car tree)
                                   (l1-api-row-index-insert row (caddr tree))
                                   (cadddr tree)))
        (t (l1-api-row-index-balance (car tree) (caddr tree)
                                    (l1-api-row-index-insert row (cadddr tree))))))

(defun l1-api-row-index-member-p (row tree)
  (declare (xargs :measure (acl2-count tree)))
  (and (consp tree)
       (or (equal row (car tree))
           (if (string< row (car tree))
               (l1-api-row-index-member-p row (caddr tree))
             (l1-api-row-index-member-p row (cadddr tree))))))

(defun l1-api-session-parse (raw parsed-rows)
  (let ((row (assoc-equal raw parsed-rows)))
    (if row (cdr row) (l1-api-parse raw))))

(defun l1-api-session-row-names (raw names)
  (let ((chars (coerce raw 'list)))
    (if (l1-api-prefix-present-p chars *l1-api-helper-prefixes*)
        (l1-api-match-names (l1-api-atom-matches chars nil 0 0 nil) names)
      names)))

; An admitted context holds the proof, choices in admission order, the row
; index, the helper names, and the rewrite index once the library is admitted.
(defun l1-api-make-context (proof choices rows names rewrites)
  (list proof choices rows names rewrites))

(defun l1-api-session-admit-row (context row parsed-rows)
  (proof-with-checked-results ((raw (l1-api-raw row)))
    (let ((rows (caddr context)))
      (if (l1-api-row-index-member-p raw rows)
          context
        (proof-with-checked-results
            ((parsed (l1-api-session-parse raw parsed-rows))
             (admitted (l1-witness-admit (car context) (car parsed) (cadr parsed))))
          (let ((choices (cadr context))
                (choice (car admitted))
                (proof (cdr admitted))
                (rewrites (nth 4 context)))
            (l1-api-make-context
             proof (if choice (append choices (list choice)) choices)
             (l1-api-row-index-insert raw rows)
             (l1-api-session-row-names raw (cadddr context))
             (and rewrites
                  (l1-rewriting-update-prepared
                   rewrites proof (l1-witness-admitted-fact-names
                                   (car parsed) (cadr parsed) choice))))))))))

(defun l1-api-session-admit-rows (context rows parsed-rows)
  (declare (xargs :measure (acl2-count rows)))
  (if (or (failure-p context) (endp rows))
      context
    (l1-api-session-admit-rows
     (l1-api-session-admit-row context (car rows) parsed-rows) (cdr rows) parsed-rows)))

; On a match, return a pair even when the suffix is empty.
(defun l1-api-session-prefix-suffix (prefix rows)
  (cond ((endp prefix) (cons t rows))
        ((and (consp rows) (equal (car prefix) (car rows)))
         (l1-api-session-prefix-suffix (cdr prefix) (cdr rows)))
        (t nil)))

(defun l1-api-session-context (session earlier parsed-rows)
  (let ((suffix (l1-api-session-prefix-suffix (cadr session) earlier)))
    (if suffix
        (l1-api-session-admit-rows (caddr session) (cdr suffix) parsed-rows)
      (l1-api-session-admit-rows (car session) earlier parsed-rows))))

(defun l1-api-session-namespace (sources names statement aids)
  (proof-with-checked-results
      ((occupied (and (l1-api-namespace-helpers-p sources)
                      (l1-api-context-names (cons statement aids)))))
    (l1-api-namespace-fragments sources (append occupied names) nil nil)))

(defun l1-api-session-measures (aids previous)
  (if (and previous (equal aids (car previous)))
      previous
    (cons aids (l1-api-aid-measures aids nil))))

(defun l1-api-session-answer (context obligation statement aids arithmetic previous-measures)
  (if (l1-api-row-index-member-p (car obligation) (caddr context))
      (cons nil previous-measures)
    (let* ((kind (cadr obligation))
           (proof (car context))
           (definition (equal kind "define"))
           (measures (if definition (l1-api-session-measures aids previous-measures)
                       previous-measures))
           (rewriter (and (equal kind "theorem")
                          (l1-rewriting-rewriter-prepared proof (nth 4 context))))
           (answer
            (proof-with-checked-results
                ((stored (and definition (cdr measures)))
                 (sources (l1-api-obligation-sources proof (cadr context) obligation stored
                                                     (list arithmetic rewriter))))
              (and sources (l1-api-session-namespace sources (cadddr context) statement aids)))))
      (cons (if (failure-p answer) nil answer) measures))))

; The prefix context shares the immutable data of the base context.
(defun l1-api-make-session (base earlier context statement arithmetic measures)
  (list base earlier context statement arithmetic measures))

(defun l1-api-open (library)
  (let* ((ground (l1-api-make-context (l1-warrant-warrant-proof-init) nil nil nil nil))
         (admitted (l1-api-session-admit-rows ground library nil))
         (base (if (failure-p admitted)
                   admitted
                 (l1-api-make-context (car admitted) (cadr admitted)
                                      (caddr admitted) (cadddr admitted)
                                      (l1-rewriting-prepare (car admitted))))))
    (l1-api-make-session base nil base nil (l1-books-arithmetic-library) nil)))

(defun l1-api-prove-open (session statement earlier aids)
  (let ((raw (l1-api-raw statement)))
    (if (failure-p raw)
        (cons nil session)
      (let* ((base (car session))
             (previous (cadddr session))
             (arithmetic (nth 4 session))
             (measures (nth 5 session))
             (parsed (l1-api-session-parse raw (list previous)))
             (row (cons raw parsed))
             (obligation (l1-api-parsed-obligation raw parsed))
             (context (and obligation (not (failure-p obligation))
                           (l1-api-session-context session earlier (list row previous)))))
        (if (or (not context) (failure-p context))
            (cons nil (l1-api-make-session base (cadr session) (caddr session)
                                          row arithmetic measures))
          (let ((result (l1-api-session-answer context obligation statement aids arithmetic measures)))
            (cons (car result)
                  (l1-api-make-session base earlier context row arithmetic (cdr result)))))))))

(defun l1-api-prove-all-answers (session cases answers)
  (declare (xargs :measure (acl2-count cases)))
  (if (endp cases)
      (reverse answers)
    (let* ((case (car cases))
           (result (l1-api-prove-open session (car case) (cadr case) (caddr case))))
      (l1-api-prove-all-answers (cdr result) (cdr cases) (cons (car result) answers)))))

(defun l1-api-prove-all-loop (session cases)
  (l1-api-prove-all-answers session cases nil))

(defun l1-api-prove-all (library cases)
  (l1-api-prove-all-loop (l1-api-open library) cases))
