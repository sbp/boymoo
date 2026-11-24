(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h4-open-remember-constraints (constraints templates)
  (if (endp constraints)
      templates
    (h4-open-remember-constraints
     (cdr constraints)
     (h4-book-tactics-remember-template (caar constraints) (list (cadar constraints)) templates))))

(defun h4-open-remember-statement (statement templates)
  (let ((kind (h4-book-run-statement-kind statement))
        (fields (h4-book-run-statement-fields statement)))
    (cond ((member-equal kind '("theorem" "axiom"))
           (h4-book-tactics-remember-template (car fields) (list (cadr fields)) templates))
          ((and (equal kind "constrain") (not (equal (cadr fields) *proof-nil*)))
           (h4-open-remember-constraints (cadr fields) templates))
          (t templates))))

; A prepared world stores the admitted world, parsed lines, and rule templates.
; The exact source line is the key for parsing and admission.
(defun h4-open-admit-lines (source prepared old-lines last-target)
  (if (endp source)
      prepared
    (let ((line (car source))
          (lines (cadr prepared)))
      (if (h4-book-tactics-tree-entry line lines)
          (h4-open-admit-lines (cdr source) prepared old-lines last-target)
        (let ((cached (if (and last-target (equal line (car last-target)))
                          last-target
                        (h4-book-tactics-tree-entry line old-lines))))
          (proof-with-checked-results
              ((statement (if cached (cdr cached) (h4-api-parsed line)))
               (world (h4-api-admit (car prepared) statement)))
            (h4-open-admit-lines
             (cdr source)
             (list world (h4-book-tactics-tree-put line statement lines)
                   (h4-open-remember-statement statement (caddr prepared)))
             old-lines last-target)))))))

(defun h4-open-prefix-tail (prefix earlier)
  (cond ((endp prefix) earlier)
        ((or (endp earlier) (not (equal (car prefix) (car earlier)))) :different)
        (t (h4-open-prefix-tail (cdr prefix) (cdr earlier)))))

(defun h4-api-open (library)
  (let* ((ground (h4-api-ground-world))
         (proof (library-library-proof (h4-api-world-library ground)))
         (templates (h4-book-tactics-prepare-templates
                     (proof-proof-facts proof) (proof-proof-definitions proof) nil)))
    ; The session holds the ground, library, prefix, core support, aid tables,
    ; pointwise and warrant support, the latest parsed target, and renamed entries.
    (list :h4-session ground
          (h4-open-admit-lines (h4-api-lines library) (list ground nil templates) nil nil)
          nil :unprepared nil nil nil nil nil)))

(defun h4-open-answer (result session)
  (cons (if (failure-p result) nil result) session))

(defun h4-open-build-proof (world statement measures hints session pointwise)
  (let* ((prefix (cdr (cadddr session)))
         (core (nth 4 session))
         (result (h4-api-build-proof-ready-with-cache
                  world statement measures hints
                  (list (caddr prefix) (cdr core) pointwise) (nth 9 session))))
    (h4-open-answer (car result) (update-nth 9 (cdr result) session))))

(defun h4-open-prepare-pointwise (key session)
  (let ((support (h4-api-pointwise-support-from-ground
                  (car key) (cadr key) (cadr session) (car (nth 4 session)))))
    (cons support
          (and (not (failure-p support))
               (h4-book-tactics-remember-template (cadr support) (caddr support) nil)))))

(defun h4-open-prove-pointwise (session world statement measures hints)
  (let ((key (h4-api-pointwise-key world)))
    (if (not key)
        (h4-open-build-proof world statement measures hints session nil)
      (let* ((cache (nth 6 session))
             (hit (assoc-equal key cache))
             (prepared (if hit (cdr hit) (h4-open-prepare-pointwise key session)))
             (session (update-nth 6 (h4-api-encoding-remember key prepared cache 4) session))
             (world (h4-api-install-pointwise-support world (car prepared))))
        (if (failure-p world)
            (cons nil session)
          (h4-open-build-proof world statement measures hints session (cdr prepared)))))))

(defun h4-open-prepare-core (ground)
  (let ((support (h4-api-prepare-core-installation (h4-api-core-support-from-ground ground))))
    (cons support
          (and (not (failure-p support))
               (h4-book-tactics-prepare-templates (cadr support) (caddr support) nil)))))

(defun h4-open-prove-core (session world statement measures hints)
  (let* ((ground (cadr session))
         (saved (nth 4 session))
         (core (if (eq saved :unprepared) (h4-open-prepare-core ground) saved))
         (session (update-nth 4 core session))
         (world (h4-api-install-core-support-prepared world (car core))))
    (if (failure-p world)
        (cons nil session)
      (h4-open-prove-pointwise session world statement measures hints))))

(defun h4-open-finish-special (session statement plan prepared)
  (let ((result (h4-api-special-prepared-with-cache statement plan prepared (nth 9 session))))
    (cons (car result) (update-nth 9 (cdr result) session))))

(defun h4-open-attempt-warrant (session world statement plan)
  (let ((input (h4-api-warrant-input world (cdr plan))))
    (if (failure-p input)
        (cons input session)
      (let* ((cached (nth 7 session))
             (support (if (and cached (equal input (car cached)))
                          (cdr cached)
                        (h4-api-warrant-support-from-ground input (cadr session))))
             (session (update-nth 7 (cons input support) session)))
        (h4-open-finish-special session statement plan (h4-api-install-warrant-support world support))))))

(defun h4-open-attempt-special (session world statement)
  (let ((plan (h4-api-special-plan statement)))
    (if (or (not plan) (failure-p plan))
        (cons plan session)
      (let ((world (h4-api-copy-world world)))
        (if (eq (car plan) :warrant-recipe)
            (h4-open-attempt-warrant session world statement plan)
          (h4-open-finish-special session statement plan (cons (list nil nil) world)))))))

(defun h4-open-prove-world (session world statement measures hints)
  (if (h4-api-statement-known-p world statement)
      (cons nil session)
    (let* ((attempted (h4-open-attempt-special session world statement))
           (first (h4-api-optional (car attempted)))
           (session (cdr attempted)))
      (if first
          (h4-open-answer first session)
        (h4-open-prove-core session world statement measures hints)))))

(defun h4-open-prove-prefix (session statement earlier measures hints)
  (let* ((previous (cadddr session))
         (suffix (h4-open-prefix-tail (car previous) earlier))
         (extends (and previous (not (eq suffix :different))))
         (prepared (h4-open-admit-lines
                    (if extends suffix earlier)
                    (if extends (cdr previous) (caddr session))
                    (and (not extends) (cadr (cdr previous)))
                    (nth 8 session))))
    (if (failure-p prepared)
        (cons nil session)
      (h4-open-prove-world (update-nth 3 (cons earlier prepared) session)
                          (car prepared) statement measures hints))))

(defun h4-open-prove-target (session statement earlier aids)
  (let* ((aids (h4-api-lines aids))
         (cache (nth 5 session))
         (hit (assoc-equal aids cache))
         (aid-info (if hit (cdr hit) (h4-api-aid-info aids)))
         (session (update-nth 5 (h4-api-encoding-remember aids aid-info cache 16) session)))
    (if (failure-p aid-info)
        (cons nil session)
      (let* ((name (h4-book-run-statement-name statement))
             (measures (and (equal (h4-book-run-statement-kind statement) "define")
                            (h4-api-relevant-measures
                             (cdr (h4-book-run-statement-fields statement)) (car aid-info) nil)))
             (hints (list (cons name (table-get (cadr aid-info) name nil)))))
        (if (failure-p measures)
            (cons nil session)
          (h4-open-prove-prefix session statement (h4-api-lines earlier) measures hints))))))

(defun h4-open-parse-target (session statement)
  (let* ((previous (cadddr session))
         (prepared (if previous (cdr previous) (caddr session)))
         (last-target (nth 8 session))
         (cached (if (and last-target (equal statement (car last-target)))
                     last-target
                   (h4-book-tactics-tree-entry statement (cadr prepared)))))
    (if cached (cdr cached) (h4-api-parsed statement))))

(defun h4-api-prove-open (session statement earlier aids)
  (let* ((parsed (h4-open-parse-target session statement))
         (result (if (or (failure-p parsed)
                         (not (h4-book-run-statement-name parsed))
                         (failure-p (caddr session)))
                     (cons nil session)
                   (h4-open-prove-target session parsed earlier aids))))
    (cons (car result) (update-nth 8 (cons statement parsed) (cdr result)))))

(defun h4-open-collect-answers (session cases answers)
  (if (endp cases)
      (reverse answers)
    (let* ((case (car cases))
           (result (h4-api-prove-open session (car case) (cadr case) (caddr case))))
      (h4-open-collect-answers (cdr result) (cdr cases) (cons (car result) answers)))))

(defun h4-api-prove-all-loop (library cases)
  (h4-open-collect-answers (h4-api-open library) cases nil))

(defun h4-api-prove-all (library cases)
  (h4-api-prove-all-loop library cases))
