(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun t4-open-library-line-p (raw index)
  (if (t4-booklogic-lookup-entry raw index) t nil))

(defun t4-open-context (tactic seen choices)
  (list tactic seen choices))

(defun t4-open-session (base index prefix aids statement)
  (list :t4-session base index prefix aids statement))

(defun t4-open-remember (session prefix aids statement)
  (t4-open-session (cadr session) (caddr session) prefix aids statement))

(defun t4-open-prepare (library)
  (proof-with-checked-results
      ((lines (t4-api-line-sequence library))
       (given (t4-api-prepared-given lines))
       (tactic (t4-booklogic-booklogic-cache-definition-sizes (car given)))
       (index (t4-booklogic-lookup-tree (acl2::pairlis$ (cadr given) nil))))
    (list (t4-open-context tactic nil (caddr given)) index)))

(defun t4-api-open (library)
  (let ((prepared (t4-open-prepare library)))
    (if (failure-p prepared)
        (t4-open-session prepared nil nil nil nil)
      (t4-open-session (car prepared) (cadr prepared) nil nil nil))))

(defun t4-open-seen-p (raw context index)
  (or (member-equal raw (cadr context))
      (t4-open-library-line-p raw index)))

(defun t4-open-earlier-statement (raw previous)
  (if (and previous (equal raw (car previous)))
      (let* ((parsed (cadr previous))
             (kind (car parsed))
             (data (cadr parsed)))
        (proof-with-checked-results
            ((recursive (and (equal kind "define") (caddr previous)
                             (t4-api-recursive-names (cdr data)))))
          (list kind data recursive)))
    (t4-api-statement raw)))

(defun t4-open-earlier (lines context index previous)
  (declare (xargs :measure (acl2-count lines)))
  (if (endp lines)
      context
    (proof-with-checked-results ((raw (t4-api-line (car lines))))
      (if (t4-open-seen-p raw context index)
          (t4-open-earlier (cdr lines) context index previous)
        (proof-with-checked-results
            ((parsed (t4-open-earlier-statement raw previous))
             (added (t4-api-admit-statement (car context) (caddr context) parsed)))
          (let ((tactic (if (equal (car parsed) "define")
                            (t4-booklogic-booklogic-extend-definition-sizes
                             (car added) (cdr (cadr parsed)))
                          (car added))))
            (t4-open-earlier (cdr lines)
                             (t4-open-context tactic (cons raw (cadr context)) (cadr added))
                             index previous)))))))

(defun t4-open-prefix-suffix (previous earlier)
  (cond ((endp previous) (cons t earlier))
        ((and (consp earlier) (equal (car previous) (car earlier)))
         (t4-open-prefix-suffix (cdr previous) (cdr earlier)))
        (t nil)))

(defun t4-open-extend (earlier base session)
  (let* ((index (caddr session))
         (prefix (cadddr session))
         (previous (nth 5 session))
         (suffix (and prefix (t4-open-prefix-suffix (car prefix) earlier))))
    (if suffix
        (t4-open-earlier (cdr suffix) (cdr prefix) index previous)
      (t4-open-earlier earlier base index previous))))

(defun t4-open-supplied (aids cache)
  (proof-with-checked-results ((aids (t4-api-line-sequence aids)))
    (let ((hit (assoc-equal aids cache)))
      (if hit
          (cons (cdr hit) (cons hit (remove1-assoc-equal aids cache)))
        (proof-with-checked-results ((supplied (t4-api-aids aids)))
          (let ((updated (acons aids supplied cache)))
            (cons supplied (take (min 4 (len updated)) updated))))))))

(defun t4-open-prove-with-context (session statement earlier context aids)
  (let* ((prefix (cons earlier context))
         (cache (nth 4 session))
         (raw (car statement))
         (supplied (and (not (member-equal raw (cadr context)))
                        (t4-open-supplied aids cache))))
    (if (or (not supplied) (failure-p supplied))
        (cons nil (t4-open-remember session prefix cache statement))
      ; The admitted proof already contains the ground theory.
      (let* ((tactic (car context))
             (answer (t4-api-proof-answer
                      (t4-booklogic-booklogic-proof tactic) tactic (caddr context) raw
                      (cadr statement) (caddr statement) (car supplied))))
        (cons (if (failure-p answer) nil answer)
              (t4-open-remember session prefix (cdr supplied) statement))))))

(defun t4-open-statement (raw previous)
  (if (and previous (equal raw (car previous)))
      previous
    (proof-with-checked-results
        ((parsed (t4-api-read raw))
         (name (t4-api-obligation (car parsed) (cadr parsed))))
      (list raw parsed name))))

(defun t4-open-prove (session statement earlier aids)
  (proof-with-checked-results ((base (cadr session))
                               (raw (t4-api-line statement)))
    (if (t4-open-library-line-p raw (caddr session))
        (cons nil session)
      (proof-with-checked-results
          ((statement (t4-open-statement raw (nth 5 session))))
        (if (not (caddr statement))
            (cons nil (t4-open-remember session (cadddr session) (nth 4 session) statement))
          (proof-with-checked-results
              ((earlier (t4-api-line-sequence earlier))
               (context (t4-open-extend earlier base session)))
            (t4-open-prove-with-context session statement earlier context aids)))))))

(defun t4-api-prove-open (session statement earlier aids)
  (let ((result (t4-open-prove session statement earlier aids)))
    (if (failure-p result) (cons nil session) result)))

(defun t4-open-collect-answers (session cases answers)
  (if (endp cases)
      (reverse answers)
    (let* ((case (car cases))
           (result (t4-api-prove-open session (car case) (cadr case) (caddr case))))
      (t4-open-collect-answers (cdr result) (cdr cases) (cons (car result) answers)))))

(defun t4-api-prove-all-loop (library cases)
  (t4-open-collect-answers (t4-api-open library) cases nil))

(defun t4-api-prove-all (library cases)
  (t4-api-prove-all-loop library cases))
