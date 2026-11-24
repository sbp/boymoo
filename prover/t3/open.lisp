(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-open-ground* (t3-api-ground))

; A persistent AVL tree maps normalized lines to parsed lines.
(defun t3-open-seen-height (tree)
  (nfix (cadddr tree)))

(defun t3-open-seen-node (entry left right)
  (list entry left right
        (1+ (max (t3-open-seen-height left) (t3-open-seen-height right)))))

(defun t3-open-seen-rotate-left (tree)
  (let ((right (caddr tree)))
    (t3-open-seen-node (car right)
                       (t3-open-seen-node (car tree) (cadr tree) (cadr right))
                       (caddr right))))

(defun t3-open-seen-rotate-right (tree)
  (let ((left (cadr tree)))
    (t3-open-seen-node (car left) (cadr left)
                       (t3-open-seen-node (car tree) (caddr left) (caddr tree)))))

(defun t3-open-seen-balance (entry left right)
  (let ((difference (- (t3-open-seen-height left) (t3-open-seen-height right))))
    (cond ((> difference 1)
           (t3-open-seen-rotate-right
            (t3-open-seen-node
             entry
             (if (> (t3-open-seen-height (caddr left)) (t3-open-seen-height (cadr left)))
                 (t3-open-seen-rotate-left left)
               left)
             right)))
          ((< difference -1)
           (t3-open-seen-rotate-left
            (t3-open-seen-node
             entry left
             (if (> (t3-open-seen-height (cadr right)) (t3-open-seen-height (caddr right)))
                 (t3-open-seen-rotate-right right)
               right))))
          (t (t3-open-seen-node entry left right)))))

(defun t3-open-seen-insert (entry tree)
  (cond ((endp tree) (t3-open-seen-node entry nil nil))
        ((equal (car entry) (caar tree)) tree)
        ((string< (car entry) (caar tree))
         (t3-open-seen-balance
          (car tree) (t3-open-seen-insert entry (cadr tree)) (caddr tree)))
        (t (t3-open-seen-balance
            (car tree) (cadr tree) (t3-open-seen-insert entry (caddr tree))))))

(defun t3-open-seen-entry (line tree)
  (and (consp tree)
       (cond ((equal line (caar tree)) (car tree))
             ((string< line (caar tree)) (t3-open-seen-entry line (cadr tree)))
             (t (t3-open-seen-entry line (caddr tree))))))

(defun t3-open-parsed-entry (raw seen recent)
  (or (t3-open-seen-entry raw seen)
      (assoc-equal raw recent)
      (proof-with-checked-results ((parsed (t3-api-parse raw)))
        (cons raw parsed))))

; Each scope pairs the search object with the index of admitted lines.
(defun t3-open-admit-library (lines lib seen)
  (if (endp lines)
      (proof-with-checked-results
          ((lib (t3-api-library-helpers lib))
           (search (t3-book-theorems-theorems-init lib)))
        (cons (t3-book-theorems-prepare-definitions search) seen))
    (proof-with-checked-results ((raw (t3-api-normalize-line (car lines))))
      (if (t3-open-seen-entry raw seen)
          (t3-open-admit-library (cdr lines) lib seen)
        (proof-with-checked-results
            ((parsed (t3-api-parse raw))
             (lib (t3-books-admit lib (car parsed) (cadr parsed))))
          (t3-open-admit-library (cdr lines) lib
                                 (t3-open-seen-insert (cons raw parsed) seen)))))))

(defun t3-open-base-scope (library)
  (proof-with-checked-results
      ((lines (t3-api-text-lines library))
       (ground *t3-open-ground*))
    (t3-open-admit-library lines ground nil)))

(defun t3-open-make-session (base scope earlier measures recent)
  (list :t3-api-session base scope earlier measures recent))

(defun t3-open-session-base (session)
  (cadr session))

(defun t3-open-session-scope (session)
  (caddr session))

(defun t3-open-session-earlier (session)
  (cadddr session))

(defun t3-open-session-measures (session)
  (nth 4 session))

(defun t3-open-session-recent (session)
  (nth 5 session))

(defun t3-api-open (library)
  (let ((base (t3-open-base-scope library)))
    (t3-open-make-session base base nil nil nil)))

(defun t3-open-prefix-suffix (prefix earlier)
  (cond ((endp prefix) earlier)
        ((and (consp earlier) (equal (car prefix) (car earlier)))
         (t3-open-prefix-suffix (cdr prefix) (cdr earlier)))
        (t :different)))

(defun t3-open-scope-extend (lines scope previous-seen recent)
  (if (endp lines)
      scope
    (proof-with-checked-results ((raw (t3-api-normalize-line (car lines))))
      (let ((search (car scope))
            (seen (cdr scope)))
        (if (t3-open-seen-entry raw seen)
            (t3-open-scope-extend (cdr lines) scope previous-seen recent)
          (proof-with-checked-results
              ((entry (t3-open-parsed-entry raw previous-seen recent))
               (search (t3-api-admit-prefix-line
                        (t3-book-theorems-theorems-lib search) search
                        (cadr entry) (caddr entry))))
            (t3-open-scope-extend
             (cdr lines) (cons search (t3-open-seen-insert entry seen))
             previous-seen recent)))))))

(defun t3-open-case-scope (session earlier recent)
  (let ((suffix (t3-open-prefix-suffix (t3-open-session-earlier session) earlier))
        (scope (t3-open-session-scope session)))
    (if (eq suffix :different)
        (t3-open-scope-extend earlier (t3-open-session-base session) (cdr scope) recent)
      (t3-open-scope-extend suffix scope nil recent))))

(defun t3-open-statement-entry (session statement)
  (proof-with-checked-results ((raw (t3-api-normalize-line statement)))
    (t3-open-parsed-entry raw (cdr (t3-open-session-scope session))
                          (t3-open-session-recent session))))

; A cache entry pairs the complete aid sequence with its measure map.
(defun t3-open-case-measures (aids cache)
  (let ((hit (assoc-equal aids cache)))
    (if hit
        (cons (cdr hit) (cons hit (remove1-equal hit cache)))
      (let ((measures (t3-api-measures aids)))
        (cons measures
              (if (failure-p measures)
                  cache
                (cons (cons aids measures)
                      (if (= (len cache) 4) (take 3 cache) cache))))))))

(defun t3-open-answer (scope request aids cache)
  (if (t3-open-seen-entry (car request) (cdr scope))
      (cons nil cache)
    (let* ((kind (cadr request))
           (prepared (if (equal kind "define") (t3-open-case-measures aids cache) (cons nil cache)))
           (measures (car prepared))
           (search (car scope))
           (answer (if (failure-p measures)
                       measures
                     (t3-api-prove-prepared (t3-book-theorems-theorems-lib search) search
                                            kind (caddr request) (cadddr request) measures))))
      (cons (if (failure-p answer) nil answer) (cdr prepared)))))

(defun t3-open-prove-entry (session entry earlier aids)
  (let* ((base (t3-open-session-base session))
         (measures (t3-open-session-measures session))
         (request (t3-api-proof-request-from-parsed (car entry) (cdr entry)))
         (scope (and request (not (failure-p request))
                     (t3-open-case-scope session earlier (cons entry (t3-open-session-recent session)))))
         (recent (list entry)))
    (if (and scope (not (failure-p scope)))
        (let ((result (t3-open-answer scope request aids measures)))
          (cons (car result) (t3-open-make-session base scope earlier (cdr result) recent)))
      (cons nil (t3-open-make-session base (t3-open-session-scope session)
                                      (t3-open-session-earlier session) measures recent)))))

(defun t3-api-prove-open (session statement earlier aids)
  (let ((earlier (t3-api-text-lines earlier))
        (aids (t3-api-text-lines aids))
        (base (t3-open-session-base session)))
    (if (or (failure-p earlier) (failure-p aids) (failure-p base))
        (cons nil session)
      (let ((entry (t3-open-statement-entry session statement)))
        (if (failure-p entry)
            (cons nil session)
          (t3-open-prove-entry session entry earlier aids))))))

(defun t3-open-prove-cases (session cases reversed)
  (if (endp cases)
      (reverse reversed)
    (let* ((item (car cases))
           (result (t3-api-prove-open session (car item) (cadr item) (caddr item))))
      (t3-open-prove-cases (cdr result) (cdr cases) (cons (car result) reversed)))))

(defun t3-api-prove-all-loop (session cases)
  (t3-open-prove-cases session cases nil))

(defun t3-api-prove-all (library cases)
  (t3-api-prove-all-loop (t3-api-open library) cases))
