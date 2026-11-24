(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun b2-open-seen (raw seen)
  (assoc-equal raw (table-get seen (length raw) nil)))

(defun b2-open-see (raw parsed seen)
  (let ((size (length raw)))
    (table-put seen size (cons (cons raw parsed) (table-get seen size nil)))))

(defun b2-open-parse (raw statement-record seen)
  (let ((known (if (and statement-record (equal raw (car statement-record)))
                   statement-record
                 (b2-open-seen raw seen))))
    (if known (cdr known) (b2-api-parse raw))))

(defun b2-open-fill (lib lines seen statement-record old-seen)
  (if (endp lines)
      (cons lib seen)
    (let ((raw (b2-api-raw-line (car lines))))
      (if (b2-open-seen raw seen)
          (b2-open-fill lib (cdr lines) seen statement-record old-seen)
        (proof-with-checked-results
         ((parsed (b2-open-parse raw statement-record old-seen))
          (next (b2-run-admit lib (car parsed) (cadr parsed))))
         (b2-open-fill next (cdr lines) (b2-open-see raw parsed seen)
                       statement-record old-seen))))))

; Support replaces any public value with the same name at its public
; position. The remaining support entries follow in declaration order.
(defun b2-open-overlay (public support)
  (cond ((endp support) public)
        ((endp public) support)
        (t (let* ((row (car public))
                  (replacement (assoc-equal (car row) support)))
             (if replacement
                 (cons replacement
                       (b2-open-overlay (cdr public) (table-without support (car row))))
               (cons row (b2-open-overlay (cdr public) support)))))))

(defun b2-open-add-support (lib support)
  (let ((proof (library-library-proof lib))
        (prelude (library-library-proof support)))
    (library-library-with-proof
     lib
     (proof-make-proof
      (b2-open-overlay (proof-proof-facts proof) (proof-proof-facts prelude))
      (b2-open-overlay (proof-proof-definitions proof) (proof-proof-definitions prelude))
      (proof-proof-primitives proof)))))

; A prefix holds its input lines, public Library, seen index and working
; Library with prelude support. The empty prefix belongs to the library.
(defun b2-open-make-prefix (lines public seen support)
  (list lines public seen (b2-open-add-support public support)))

; A session holds the empty prefix, the prelude, the current prefix, the
; most recent parsed statement and up to four measure tables.
(defun b2-api-open (library)
  (let* ((given (b2-open-fill (b2-api-ground) library nil nil nil))
         (prelude (if (failure-p given) nil (b2-api-prelude)))
         (root (cond ((failure-p given) given)
                     ((failure-p prelude) prelude)
                     (t (b2-open-make-prefix nil (car given) (cdr given) (car prelude))))))
    (list root prelude root nil nil)))

(defun b2-open-prefix-tail (prefix lines)
  (cond ((endp prefix) (cons t lines))
        ((or (endp lines) (not (equal (car prefix) (car lines)))) nil)
        (t (b2-open-prefix-tail (cdr prefix) (cdr lines)))))

(defun b2-open-extend-prefix (root prefix earlier support statement-record)
  (let* ((suffix (b2-open-prefix-tail (car prefix) earlier))
         (start (if suffix prefix root))
         (old-seen (if suffix nil (caddr prefix)))
         (lines (if suffix (cdr suffix) earlier)))
    (if (endp lines)
        start
      (proof-with-checked-results
       ((public (b2-open-fill (cadr start) lines (caddr start) statement-record old-seen)))
       (b2-open-make-prefix earlier (car public) (cdr public) support)))))

(defun b2-open-measures (aids cache)
  (let* ((hit (assoc-equal aids cache))
         (measures (if hit (cdr hit) (b2-api-measures aids))))
    (if (failure-p measures)
        (cons measures cache)
      (let ((rest (table-without cache aids)))
        (cons measures (cons (cons aids measures) (take (min 3 (len rest)) rest)))))))

(defun b2-open-compile (lib kind data aids cache)
  (if (equal kind "define")
      (let ((calls (b2-api-definition-calls data)))
        (cond ((failure-p calls) (cons calls cache))
              ((endp calls) (cons nil cache))
              (t (let* ((prepared (b2-open-measures aids cache))
                        (measures (car prepared)))
                   (cons (if (failure-p measures)
                             measures
                           (b2-api-compile-measured lib (cdr data) calls measures))
                         (cdr prepared))))))
    (cons (b2-api-compile lib kind data aids) cache)))

(defun b2-open-prove-parsed (session raw parsed earlier aids)
  (let* ((root (car session))
         (prelude (cadr session))
         (prefix (caddr session))
         (cache (car (cddddr session)))
         (kind (car parsed))
         (obligation (member-equal kind '("theorem" "define" "constrain")))
         (extended (if obligation
                       (b2-open-extend-prefix root prefix earlier (car prelude) (cadddr session))
                     prefix))
         (admitted (not (failure-p extended)))
         (next-prefix (if admitted extended prefix))
         (compiled (if (and obligation admitted (not (b2-open-seen raw (caddr extended))))
                       (b2-open-compile (cadddr extended) kind (cadr parsed) aids cache)
                     (cons nil cache)))
         (answer (b2-api-assemble-compiled (cadr next-prefix) (cadr prelude) (car compiled))))
    (cons (if (failure-p answer) nil answer)
          (list root prelude next-prefix (cons raw parsed) (cdr compiled)))))

(defun b2-api-prove-open (session statement earlier aids)
  (let* ((root (car session))
         (raw (b2-api-raw-line statement)))
    (if (or (failure-p root) (b2-open-seen raw (caddr root)))
        (cons nil session)
      (let ((parsed (b2-open-parse raw (cadddr session) (caddr (caddr session)))))
        (if (failure-p parsed)
            (cons nil session)
          (b2-open-prove-parsed session raw parsed earlier aids))))))

(defun b2-open-prove-cases (session cases answers)
  (if (endp cases)
      (reverse answers)
    (let ((result (b2-api-prove-open session (caar cases) (cadar cases) (caddar cases))))
      (b2-open-prove-cases (cdr result) (cdr cases) (cons (car result) answers)))))

(defun b2-api-prove-all-loop (session cases)
  (b2-open-prove-cases session cases nil))

(defun b2-api-prove-all (library cases)
  (b2-api-prove-all-loop (b2-api-open library) cases))
