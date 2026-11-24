(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

; A persistent search tree indexes complete lines after stripping terminators.
; Its height keeps membership tests independent of declaration order.
(defun h1-open-line-height (tree)
  (nfix (cadr tree)))

(defun h1-open-line-node (line left right)
  (list line (1+ (max (h1-open-line-height left) (h1-open-line-height right)))
        left right))

(defun h1-open-line-rotate-right (line left right)
  (let ((outer (caddr left)) (inner (cadddr left)))
    (if (< (h1-open-line-height outer) (h1-open-line-height inner))
        (h1-open-line-node (car inner)
                           (h1-open-line-node (car left) outer (caddr inner))
                           (h1-open-line-node line (cadddr inner) right))
      (h1-open-line-node (car left) outer (h1-open-line-node line inner right)))))

(defun h1-open-line-rotate-left (line left right)
  (let ((outer (cadddr right)) (inner (caddr right)))
    (if (< (h1-open-line-height outer) (h1-open-line-height inner))
        (h1-open-line-node (car inner)
                           (h1-open-line-node line left (caddr inner))
                           (h1-open-line-node (car right) (cadddr inner) outer))
      (h1-open-line-node (car right) (h1-open-line-node line left inner) outer))))

(defun h1-open-line-balance (line left right)
  (let ((left-height (h1-open-line-height left))
        (right-height (h1-open-line-height right)))
    (cond ((> (- left-height right-height) 1) (h1-open-line-rotate-right line left right))
          ((> (- right-height left-height) 1) (h1-open-line-rotate-left line left right))
          (t (h1-open-line-node line left right)))))

(defun h1-open-line-member (line tree)
  (cond ((endp tree) nil)
        ((equal line (car tree)) t)
        ((string< line (car tree)) (h1-open-line-member line (caddr tree)))
        (t (h1-open-line-member line (cadddr tree)))))

(defun h1-open-line-insert (line tree)
  (cond ((endp tree) (h1-open-line-node line nil nil))
        ((equal line (car tree)) tree)
        ((string< line (car tree))
         (h1-open-line-balance (car tree) (h1-open-line-insert line (caddr tree)) (cadddr tree)))
        (t (h1-open-line-balance (car tree) (caddr tree) (h1-open-line-insert line (cadddr tree))))))

(defun h1-open-make-world (earlier proof seen names)
  (list :h1-open-world earlier proof seen names))

(defun h1-open-world-earlier (world)
  (cadr world))

(defun h1-open-world-proof (world)
  (caddr world))

(defun h1-open-world-seen (world)
  (cadddr world))

(defun h1-open-world-names (world)
  (car (cddddr world)))

; A nonempty result distinguishes a matching prefix with an empty suffix.
(defun h1-open-prefix-suffix (prefix earlier)
  (cond ((endp prefix) (cons t earlier))
        ((and (consp earlier) (equal (car prefix) (car earlier)))
         (h1-open-prefix-suffix (cdr prefix) (cdr earlier)))
        (t nil)))

(defun h1-open-admit-lines (lines proof seen names deferred installers)
  (if (endp lines)
      (list proof seen names installers)
    (proof-with-checked-results ((raw (h1-api-engine-raw-line (car lines))))
      (if (h1-open-line-member raw seen)
          (h1-open-admit-lines (cdr lines) proof seen names deferred installers)
        (proof-with-checked-results
         ((admitted (h1-api-engine-admit-line raw proof))
          (names (h1-api-engine-extend-set (caddr admitted) names))
          (tactics (h1-books-declaration-tactics (caadr admitted) (cadadr admitted))))
         (let ((proof (car admitted)))
           (h1-open-admit-lines
            (cdr lines) (if deferred proof (h1-api-engine-attempt-installs proof tactics))
            (h1-open-line-insert raw seen) names deferred
            (if deferred (revappend tactics installers) installers))))))))

(defun h1-open-given-world (library)
  (proof-with-checked-results
   ((library (h1-api-engine-as-lines library))
    (proof (h1-api-engine-given-proof))
    (admitted (h1-open-admit-lines library proof nil nil t nil)))
   (h1-open-make-world nil (h1-api-engine-install-given (car admitted) (cadddr admitted))
                       (cadr admitted) (caddr admitted))))

(defun h1-open-statement-world (base prefix earlier)
  (proof-with-checked-results ((earlier (h1-api-engine-as-lines earlier)))
    (let* ((extension (h1-open-prefix-suffix (h1-open-world-earlier prefix) earlier))
           (world (if extension prefix base))
           (suffix (if extension (cdr extension) earlier)))
      (if (endp suffix)
          world
        (proof-with-checked-results
         ((admitted (h1-open-admit-lines suffix (h1-open-world-proof world)
                                         (h1-open-world-seen world)
                                         (h1-open-world-names world) nil nil)))
         (h1-open-make-world earlier (car admitted) (cadr admitted) (caddr admitted)))))))

; The most recently used lists of aid lines are at the front.
(defun h1-open-measures (aids cache)
  (proof-with-checked-results ((aids (h1-api-engine-as-lines aids)))
    (let ((cached (assoc-equal aids cache)))
      (proof-with-checked-results
       ((measures (if cached (cdr cached) (h1-api-engine-measures aids))))
       (let ((cache (acons aids measures (table-without cache aids))))
         (cons measures (take (min 4 (len cache)) cache)))))))

(defun h1-open-prove-target (world target aids cache)
  (let ((raw (car target))
        (kind (cadr target))
        (fields (caddr target))
        (calls (cadddr target))
        (proof (h1-open-world-proof world)))
    (if (h1-open-line-member raw (h1-open-world-seen world))
        (cons nil cache)
      (let* ((definition (equal kind "define"))
             (prepared (if definition (h1-open-measures aids cache) (cons nil cache))))
        (if (failure-p prepared)
            (cons nil cache)
          (let* ((attempt (h1-books-book-prover-fork proof))
                 (entry (if definition
                            (h1-api-engine-define-entry attempt fields calls (car prepared))
                          (h1-api-engine-construct-entry attempt proof raw kind fields calls aids)))
                 (answer (h1-api-engine-finish-entry entry kind fields
                                                     (h1-open-world-names world))))
            (cons (if (failure-p answer) nil answer) (cdr prepared))))))))

(defun h1-open-make-session (base prefix measures)
  (list :h1-open-session base prefix measures))

(defun h1-api-open (library)
  (let ((base (h1-open-given-world library)))
    (h1-open-make-session base base nil)))

(defun h1-api-prove-open (session statement earlier aids)
  (let ((target (h1-api-engine-proof-target statement))
        (base (cadr session))
        (prefix (caddr session)))
    (if (or (not target) (failure-p target) (failure-p base))
        (cons nil session)
      (let ((world (h1-open-statement-world base prefix earlier)))
        (if (failure-p world)
            (cons nil session)
          (let* ((result (h1-open-prove-target world target aids (cadddr session)))
                 (prefix (if (h1-open-world-earlier world) world prefix)))
            (cons (car result) (h1-open-make-session base prefix (cdr result)))))))))

(defun h1-api-prove-all-loop (session cases)
  (if (endp cases)
      nil
    (let ((result (h1-api-prove-open session (car (car cases)) (cadr (car cases))
                                     (caddr (car cases)))))
      (cons (car result)
            (h1-api-prove-all-loop (cdr result) (cdr cases))))))

(defun h1-api-prove-all (library cases)
  (h1-api-prove-all-loop (h1-api-open library) cases))
