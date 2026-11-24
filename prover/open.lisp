(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun open-session (base given-lines earlier context last-parse hints)
  (list base given-lines earlier context last-parse hints))

(defun open-session-base (session)
  (car session))

(defun open-session-given-lines (session)
  (cadr session))

(defun open-session-earlier (session)
  (caddr session))

(defun open-session-context (session)
  (cadddr session))

(defun open-session-last-parse (session)
  (car (cddddr session)))

(defun open-session-hints (session)
  (cadr (cddddr session)))

(defun open-update-session (session earlier context last-parse hints)
  (open-session (open-session-base session) (open-session-given-lines session)
                earlier context last-parse hints))

; Consume the first N sorted records and return the tree and unused records.
(defun open-line-tree (n records)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons nil records)
    (let* ((half (min (nfix (floor n 2)) (1- n)))
           (left (open-line-tree half records))
           (middle (cdr left))
           (right (open-line-tree (1- (- n half)) (cdr middle))))
      (cons (list (car middle) (car left) (car right))
            (cdr right)))))

(defun open-given-line (raw tree)
  (if (endp tree)
      nil
    (let* ((record (car tree))
           (key (car record)))
      (cond ((equal raw key) record)
            ((acl2::lexorder raw key) (open-given-line raw (cadr tree)))
            (t (open-given-line raw (caddr tree)))))))

(defun open-read-library (lines context records)
  (if (endp lines)
      (cons context records)
    (let ((raw (api-raw-line (car lines))))
      (if (member-equal raw (api-context-seen context))
          (open-read-library (cdr lines) context records)
        (let* ((parsed (api-context-parse-line raw nil))
               (context (api-context-append-record context raw parsed)))
          (if (failure-p context)
              (cons context nil)
            (open-read-library (cdr lines) context (acons raw parsed records))))))))

(defun api-open (library)
  (let ((ground (api-context-init)))
    (if (failure-p ground)
        (open-session ground nil nil ground nil nil)
      (let* ((prepared (open-read-library (api-as-lines library) ground nil))
             (context (car prepared)))
        (if (failure-p context)
            (open-session context nil nil context nil nil)
          (let* ((records (acl2::merge-sort-lexorder (cdr prepared)))
                 (lines (car (open-line-tree (len records) records)))
                 (base (api-context-with-seen context nil)))
            (open-session base lines nil base nil nil)))))))

; A successful match is tagged because its remaining lines can be empty.
(defun open-prefix-tail (prefix lines)
  (cond ((endp prefix) (cons t lines))
        ((and (consp lines) (equal (car prefix) (car lines)))
         (open-prefix-tail (cdr prefix) (cdr lines)))
        (t nil)))

(defun open-append-earlier (lines context given-lines last-parse)
  (if (endp lines)
      context
    (let ((raw (api-raw-line (car lines))))
      (if (or (open-given-line raw given-lines)
              (member-equal raw (api-context-seen context)))
          (open-append-earlier (cdr lines) context given-lines last-parse)
        (book-proofs-let* ((context (api-context-append-record
                                    context raw (api-context-parse-line raw last-parse))))
          (open-append-earlier (cdr lines) context given-lines last-parse))))))

(defun open-context-for (session earlier)
  (let* ((tail (open-prefix-tail (open-session-earlier session) earlier))
         (context (if tail (open-session-context session) (open-session-base session))))
    (open-append-earlier (if tail (cdr tail) earlier) context
                         (open-session-given-lines session) (open-session-last-parse session))))

(defun open-measure-aids (aids cache)
  (let* ((lines (api-as-lines aids))
         (stored (assoc-equal lines cache))
         (hints (if stored (cdr stored) (api-hints lines))))
    (if (failure-p hints)
        (cons hints cache)
      (let ((rest (remove1-assoc-equal lines cache)))
        (cons hints (acons lines hints (take (min 3 (len rest)) rest)))))))

(defun open-prove-obligation (obligation context aids cache)
  (let* ((kind (cadr obligation))
         (prepared (if (equal kind "define") (open-measure-aids aids cache) (cons nil cache)))
         (answer (api-prove-context-with-hints
                  context kind (caddr obligation) (cadddr obligation) (car prepared))))
    (cons (if (failure-p answer) nil answer) (cdr prepared))))

(defun open-answer (session obligation given earlier aids last-parse)
  (let* ((earlier (api-as-lines earlier))
         (context (open-context-for session earlier))
         (cache (open-session-hints session)))
    (if (failure-p context)
        (cons nil (open-update-session session (open-session-earlier session)
                                       (open-session-context session) last-parse cache))
      (let ((result (if (or given (member-equal (car obligation) (api-context-seen context)))
                        (cons nil cache)
                      (open-prove-obligation obligation context aids cache))))
        (cons (car result) (open-update-session session earlier context last-parse (cdr result)))))))

(defun api-prove-open (session statement earlier aids)
  (if (failure-p (open-session-base session))
      (cons nil session)
    (let* ((raw (api-raw-line statement))
           (given (open-given-line raw (open-session-given-lines session)))
           (previous (open-session-last-parse session))
           (parsed (cond (given (cdr given))
                         ((and previous (equal raw (car previous))) (cdr previous))
                         (t (api-parse raw))))
           (obligation (api-proof-obligation-parsed raw parsed))
           (last-parse (if (or given (failure-p parsed)) previous (cons raw parsed))))
      (if (or (not obligation) (failure-p obligation))
          (cons nil (open-update-session session (open-session-earlier session)
                                         (open-session-context session) last-parse
                                         (open-session-hints session)))
        (open-answer session obligation given earlier aids last-parse)))))

(defun api-prove-all-loop (session cases)
  (if (endp cases)
      nil
    (let ((result (api-prove-open session (car (car cases)) (cadr (car cases))
                                     (caddr (car cases)))))
      (cons (car result)
            (api-prove-all-loop (cdr result) (cdr cases))))))

(defun api-prove-all (library cases)
  (api-prove-all-loop (api-open library) cases))
