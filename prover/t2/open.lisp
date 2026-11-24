(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

; A session holds the admitted and enriched bases, the current earlier
; prefix, recent aids, the last statement event, the private helper
; caches, the prepared rules and the parsed library events.

(defconst *t2-open-private-prefix* (concatenate 'string "PROVER-" *t2-api-prefix* "-"))

; Bucket selection uses the text length. The key comparison uses the
; complete source string, including its terminator.
(defun t2-open-library-event (source events)
  (and (stringp source)
       (assoc-equal source (table-get events (mod (length source) 257) nil))))

(defun t2-open-add-library-event (source event events)
  (let* ((bucket (mod (length source) 257))
         (rows (table-get events bucket nil)))
    (table-put events bucket (acons source event rows))))

(defun t2-open-admit-event (generator event)
  (proof-with-checked-results ((event event))
    (t2-tactics-generator-admit-given generator (car event) (cadr event))))

(defun t2-open-admit-library (lines generator events)
  (declare (xargs :measure (acl2-count lines)))
  (if (or (failure-p generator) (endp lines))
      (cons generator events)
    (let* ((source (car lines))
           (found (t2-open-library-event source events))
           (event (if found (cdr found) (t2-api-engine-event source)))
           (generator (t2-open-admit-event generator event))
           (events (if (or found (failure-p generator) (not (stringp source)))
                       events
                     (t2-open-add-library-event source event events))))
      (t2-open-admit-library (cdr lines) generator events))))

(defun t2-api-open (library)
  (let* ((given (t2-open-admit-library (t2-api-engine-lines library) (t2-api-engine-core) nil))
         (generator (car given))
         (base (if (failure-p generator) generator (list generator nil))))
    (list base nil nil nil nil nil nil (cdr given))))

(defun t2-open-with-book-base (session)
  (if (cadr session)
      session
    (let* ((base (car session))
           (enriched (if (failure-p base)
                         base
                       (t2-api-engine-enrich (car base))))
           (book-base (if (failure-p enriched)
                          enriched
                        (list (cdr enriched) (car enriched)))))
      (update-nth 1 book-base session))))

(defun t2-open-remember (entry found cache capacity)
  (if (equal entry (car cache))
      cache
    (let ((recent (cons entry (if found (remove-equal found cache) cache))))
      (take (min capacity (len recent)) recent))))

(defun t2-open-event (line previous-event library-events)
  (if (and previous-event (equal line (car previous-event)))
      (cdr previous-event)
    (let ((found (t2-open-library-event line library-events)))
      (if found (cdr found) (t2-api-engine-event line)))))

(defun t2-open-aid-lines (lines parsed previous-event library-events)
  (declare (xargs :measure (acl2-count lines)))
  (if (or (failure-p parsed) (endp lines))
      parsed
    (t2-open-aid-lines
     (cdr lines)
     (proof-with-checked-results ((event (t2-open-event (car lines) previous-event library-events)))
       (t2-books-parse-aid (car event) (cadr event) (car parsed) (cadr parsed)))
     previous-event library-events)))

(defun t2-open-with-aids (aids session)
  (let* ((cache (cadddr session))
         (found (assoc-equal aids cache))
         (entry (or found
                    (let ((parsed (t2-open-aid-lines (t2-api-engine-lines aids) (list nil nil)
                                                     (nth 4 session) (nth 7 session))))
                      (list aids parsed
                            (and (not (failure-p parsed))
                                 (table-update (t2-api-engine-library-measures) (car parsed))))))))
    (cons (cdr entry) (update-nth 3 (t2-open-remember entry found cache 8) session))))

(defun t2-open-parse-events (lines previous-event library-events)
  (if (endp lines)
      nil
    (cons (t2-open-event (car lines) previous-event library-events)
          (t2-open-parse-events (cdr lines) previous-event library-events))))

(defun t2-open-admit-events (generator events)
  (declare (xargs :measure (acl2-count events)))
  (if (or (failure-p generator) (endp events))
      generator
    (t2-open-admit-events (t2-open-admit-event generator (car events)) (cdr events))))

; A prefix contains its source lines and parsed events, followed by the
; two admission snapshots. Each snapshot pairs an event count with a
; Generator or a failure. Both snapshots use the same list of parsed events.
(defun t2-open-update-prefix (prefix earlier previous-event library-events)
  (let ((extension (t2-book-logic-prefix-suffix (car prefix) earlier)))
    (cond ((not extension)
           (list earlier (t2-open-parse-events earlier previous-event library-events) nil nil))
          ((endp (cdr extension)) prefix)
          (t (list* earlier
                    (append (cadr prefix)
                            (t2-open-parse-events (cdr extension) previous-event library-events))
                    (cddr prefix))))))

(defun t2-open-context (earlier book session)
  (let* ((session (if book (t2-open-with-book-base session) session))
         (base (if book (cadr session) (car session))))
    (if (failure-p base)
        (cons base session)
      (let* ((prefix (t2-open-update-prefix (caddr session) earlier (nth 4 session) (nth 7 session)))
             (events (cadr prefix))
             (snapshot (if book (cadddr prefix) (caddr prefix)))
             (generator (if snapshot (cdr snapshot) (car base)))
             (suffix (if snapshot (nthcdr (car snapshot) events) events))
             (admitted (t2-open-admit-events generator suffix))
             (snapshot (cons (len events) admitted))
             (prefix (list (car prefix) events
                           (if book (caddr prefix) snapshot)
                           (if book snapshot (cadddr prefix)))))
        (cons (if (failure-p admitted) admitted (list admitted (cadr base)))
              (update-nth 2 prefix session))))))

(defun t2-open-helper-tokens (source cache)
  (let* ((found (assoc-equal source cache))
         (entry (or found (cons source (t2-api-names-source-tokens source)))))
    (cons (cdr entry) (t2-open-remember entry found cache 512))))

(defun t2-open-private-entry (source declared before cache)
  (let* ((key (list source declared before))
         (found (assoc-equal key cache)))
    (proof-with-checked-results
        ((value (if found
                    (cdr found)
                  (t2-api-names-private-entry source declared before *t2-open-private-prefix*))))
      (cons value (t2-open-remember (cons key value) found cache 512)))))

; Private names depend on the bindings already chosen for this proof.
; The current fact dictionary is checked for conflicts even on a cache hit.
(defun t2-open-namespace (helpers entry used names sources cache)
  (declare (xargs :measure (acl2-count helpers)))
  (if (endp helpers)
      (proof-with-checked-results
          ((before (t2-api-names-dependencies entry names))
           (changed (t2-api-names-rename entry before nil)))
        (cons (list (reverse sources) changed) cache))
    (proof-with-checked-results
        ((helper (t2-api-names-fields (car helpers) 4))
         (source (cadddr helper))
         (declared (t2-api-names-declared (car helper) (cadr helper) source))
         (tokens (t2-open-helper-tokens source (car cache)))
         (before (t2-api-names-present-names names (car tokens)))
         (private (t2-open-private-entry source declared before (cdr cache)))
         (own (caar private)))
      (if (t2-api-names-occupied-p own used)
          '(:failure "failure" "")
        (proof-with-checked-results ((names (t2-api-names-binding-map own names)))
          (t2-open-namespace (cdr helpers) entry used names (cons (cadar private) sources)
                             (cons (cdr tokens) (cdr private))))))))

(defun t2-open-answer (result session)
  (let* ((parts (t2-api-engine-proof-text-parts result))
         (named (if (failure-p parts)
                    parts
                  (t2-open-namespace (car parts) (cadr parts) (caddr parts) nil nil (nth 5 session)))))
    (if (failure-p named)
        (cons nil session)
      (cons (car named) (update-nth 5 (cdr named) session)))))

(defun t2-open-with-rules (session)
  (if (nth 6 session)
      session
    (let* ((base (cadr session))
           (lib (t2-tactics-generator-lib (car base))))
      (update-nth 6 (t2-book-logic-rules-prepare lib) session))))

(defun t2-open-generate (generator target hints stored session)
  (if (equal (t2-books-obligation-kind target) "define")
      (t2-api-engine-generate generator target hints stored)
    (car (t2-books-statement-prover-generate-with-prepared-rules
          (t2-books-statement-prover-init generator) target hints (nth 6 session)))))

(defun t2-open-retry (target hints stored earlier session)
  ; With an empty prefix, enriching after admission gives the book base.
  (let* ((empty (endp earlier))
         (prepared (t2-open-context earlier empty session))
         (context (car prepared))
         (session (cdr prepared)))
    (if (failure-p context)
        (cons nil session)
      (let* ((generator (if empty (car context) (cdr (t2-api-engine-enrich (car context)))))
             (result (t2-open-generate generator target hints stored session)))
        (if (t2-books-failure-kind-p result *t2-api-engine-failures*)
            (cons nil session)
          (t2-open-answer result session))))))

(defun t2-open-prove-target (target earlier aids session)
  (let* ((prepared (t2-open-with-aids aids session))
         (parsed (car prepared))
         (aids (car parsed))
         (session (cdr prepared)))
    (if (failure-p aids)
        (cons nil session)
      (let* ((define-p (equal (t2-books-obligation-kind target) "define"))
             (stored (and define-p (cadr parsed)))
             (hints (cadr aids))
             (earlier (t2-api-engine-lines earlier))
             (book (or (not define-p) (not (endp hints))))
             (prepared (t2-open-context earlier book session))
             (context (car prepared))
             (session (cdr prepared)))
        (if (failure-p context)
            (cons nil session)
          (let* ((session (if define-p session (t2-open-with-rules session)))
                 (result (t2-open-generate (car context) target hints stored session)))
            (cond ((not (t2-books-failure-kind-p result *t2-api-engine-failures*))
                   (t2-open-answer result session))
                  ((or (cadr context) (and book (endp earlier))) (cons nil session))
                  (t (t2-open-retry target hints stored earlier session)))))))))

(defun t2-api-prove-open (session statement earlier aids)
  (let* ((event (t2-open-event statement (nth 4 session) (nth 7 session)))
         (target (t2-api-engine-obligation statement event))
         (result (if (or (not target) (failure-p target))
                     (cons nil session)
                   (t2-open-prove-target target earlier aids session))))
    (cons (car result) (update-nth 4 (cons statement event) (cdr result)))))

(defun t2-open-prove-cases (session cases answers)
  (declare (xargs :measure (acl2-count cases)))
  (if (endp cases)
      (reverse answers)
    (let* ((case (car cases))
           (result (t2-api-prove-open session (car case) (cadr case) (caddr case))))
      (t2-open-prove-cases (cdr result) (cdr cases) (cons (car result) answers)))))

(defun t2-api-prove-all-loop (session cases)
  (t2-open-prove-cases session cases nil))

(defun t2-api-prove-all (library cases)
  (t2-api-prove-all-loop (t2-api-open library) cases))
