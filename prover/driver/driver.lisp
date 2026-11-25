(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

; The build stages this book under build/prover/driver/acl2.
(add-include-book-dir :prover-books "../../acl2")
(include-book "open" :dir :prover-books :uncertified-okp nil)
(include-book "t2/open" :dir :prover-books :uncertified-okp nil)
(include-book "t3/open" :dir :prover-books :uncertified-okp nil)
(include-book "t4/open" :dir :prover-books :uncertified-okp nil)
(include-book "h1/open" :dir :prover-books :uncertified-okp nil)
(include-book "h2/open" :dir :prover-books :uncertified-okp nil)
(include-book "h3/open" :dir :prover-books :uncertified-okp nil)
(include-book "h4/open" :dir :prover-books :uncertified-okp nil)
(include-book "b1/open" :dir :prover-books :uncertified-okp nil)
(include-book "b2/open" :dir :prover-books :uncertified-okp nil)
(include-book "l1/open" :dir :prover-books :uncertified-okp nil)
(include-book "worklist" :uncertified-okp nil)
(include-book "prove" :uncertified-okp nil)
(include-book "checker/check" :uncertified-okp nil)

(defun driver-open (set library)
  (cond ((equal set "T1") (api-open library))
        ((equal set "T2") (t2-api-open library))
        ((equal set "T3") (t3-api-open library))
        ((equal set "T4") (t4-api-open library))
        ((equal set "H1") (h1-api-open library))
        ((equal set "H2") (h2-api-open library))
        ((equal set "H3") (h3-api-open library))
        ((equal set "H4") (h4-api-open library))
        ((equal set "B1") (b1-api-open library))
        ((equal set "B2") (b2-api-open library))
        ((equal set "L1") (l1-api-open library))))

(defun driver-prove-open (set session line earlier aids)
  (cond ((equal set "T1") (api-prove-open session line earlier aids))
        ((equal set "T2") (t2-api-prove-open session line earlier aids))
        ((equal set "T3") (t3-api-prove-open session line earlier aids))
        ((equal set "T4") (t4-api-prove-open session line earlier aids))
        ((equal set "H1") (h1-api-prove-open session line earlier aids))
        ((equal set "H2") (h2-api-prove-open session line earlier aids))
        ((equal set "H3") (h3-api-prove-open session line earlier aids))
        ((equal set "H4") (h4-api-prove-open session line earlier aids))
        ((equal set "B1") (b1-api-prove-open session line earlier aids))
        ((equal set "B2") (b2-api-prove-open session line earlier aids))
        ((equal set "L1") (l1-api-prove-open session line earlier aids))
        (t (cons nil session))))

(defun driver-attempt (set session statement line earlier aids)
  (if (failure-p session)
      (cons nil session)
    (let ((result (driver-prove-open set session line earlier aids)))
      (if (failure-p result)
          (cons nil session)
        (let* ((answer (car result))
               (blocks (and (not (failure-p answer))
                            (prove-valid-blocks answer statement))))
          (cons (and (not (failure-p blocks)) blocks) (cdr result)))))))

; Split at line feeds and keep each line feed with its line.
(defun driver-source-lines-chars (chars line lines)
  (cond ((endp chars)
         (reverse (if (consp line)
                      (cons (coerce (reverse line) 'string) lines)
                    lines)))
        ((eql (car chars) #\Newline)
         (driver-source-lines-chars
          (cdr chars) nil
          (cons (coerce (reverse (cons (car chars) line)) 'string) lines)))
        (t (driver-source-lines-chars (cdr chars) (cons (car chars) line) lines))))

(defun driver-source-lines (text)
  (driver-source-lines-chars (coerce text 'list) nil nil))

(defun driver-input (library statements aids options)
  (let* ((sets (cdr (assoc-eq :sets options)))
         (selection (assoc-eq :selected options))
         (library-lines (driver-source-lines library))
         (aid-index (prove-aids (driver-source-lines aids))))
    (if (failure-p aid-index)
        aid-index
      (let ((work (prove-prover-run
                   (prove-options (or sets :none)
                                  (cdr (assoc-eq :library-order options)) nil)
                   library-lines (driver-source-lines statements) aid-index
                   (if selection (cdr selection) :none))))
        (if (failure-p work) work (cons library-lines work))))))

(defun driver-target-number (target)
  (prove-entry-number (prove-target-entry target)))

; Each context holds (number target prefix). Consecutive prefixes share
; the list of lines they have in common, stored in reverse order.
(defun driver-contexts (rows prefix contexts)
  (if (endp rows)
      (reverse contexts)
    (let* ((row (car rows))
           (target (prove-row-target row)))
      (driver-contexts (cdr rows)
                       (prove-prefix-add prefix (prove-row-line row)
                                         (prove-row-statement row))
                       (if target
                           (cons (list (driver-target-number target) target prefix)
                                 contexts)
                         contexts)))))

(defun driver-context-attempt (set context library sessions)
  (let* ((target (cadr context))
         (saved (assoc-equal set sessions))
         (session (if saved (cdr saved) (driver-open set library)))
         (result (driver-attempt set session
                                 (prove-target-statement target)
                                 (prove-target-line target)
                                 (prove-prefix-lines (caddr context))
                                 (prove-target-aids target))))
    (cons (car result) (table-put sessions set (cdr result)))))

(defun driver-target-set (target rank)
  (and (prove-target-pending target)
       (car (nth rank (prove-target-order target)))))

(defun driver-order-width (targets)
  (if (endp targets)
      0
    (max (len (prove-target-order (car targets)))
         (driver-order-width (cdr targets)))))

(defun driver-rank-count (targets options)
  (let ((width (driver-order-width targets))
        (limit (cdr (assoc-eq :ranks options))))
    (if (natp limit) (min limit width) width)))

(defun driver-search-pass (contexts rank library sessions answers pending)
  (if (endp contexts)
      (list (reverse pending) sessions answers)
    (let* ((context (car contexts))
           (set (driver-target-set (cadr context) rank)))
      (if (not set)
          (driver-search-pass (cdr contexts) rank library sessions answers pending)
        (let* ((attempt (driver-context-attempt set context library sessions))
               (blocks (car attempt)))
          (driver-search-pass (cdr contexts) rank library (cdr attempt)
                              (if blocks (acons (car context) blocks answers) answers)
                              (if blocks pending (cons context pending))))))))

(defun driver-search-ranks (remaining rank contexts library sessions answers)
  (declare (xargs :measure (nfix remaining)))
  (if (or (zp remaining) (endp contexts))
      answers
    (let ((pass (driver-search-pass contexts rank library sessions answers nil)))
      (driver-search-ranks (1- remaining) (1+ rank) (car pass)
                           library (cadr pass) (caddr pass)))))

(defun driver-entry-answers (entries answers)
  (if (endp entries)
      nil
    (let* ((entry (car entries))
           (blocks (cdr (assoc-equal (prove-entry-number entry) answers))))
      (cons (if blocks (prove-entry-with-blocks entry blocks) entry)
            (driver-entry-answers (cdr entries) answers)))))

(defun driver-search (library statements aids options)
  (let ((input (driver-input library statements aids options)))
    (if (failure-p input)
        input
      (let* ((remaining (driver-rank-count (cadddr input) options))
             (contexts (and (not (zp remaining))
                            (driver-contexts (cadr input) (prove-prefix) nil)))
             (answers (driver-search-ranks remaining 0 contexts (car input) nil nil)))
        (driver-entry-answers (caddr input) answers)))))

(defun driver-prove (library statements aids options)
  (let ((entries (driver-search library statements aids options)))
    (if (failure-p entries)
        entries
      (car (prove-prover-assemble entries nil)))))

(defun driver-entry-numbers (entries)
  (if (endp entries)
      nil
    (cons (prove-entry-number (car entries))
          (driver-entry-numbers (cdr entries)))))

(defun driver-without-certificate (entries index)
  (cond ((endp entries) nil)
        ((zp index) (cons (prove-entry-with-blocks (car entries) nil) (cdr entries)))
        (t (cons (car entries) (driver-without-certificate (cdr entries) (1- index))))))

(defun driver-check (n ground library statements entries numbers baseline-checked)
  (if (zp n)
      '(:failure "fuel" "driver-check")
    (let* ((assembled (prove-prover-assemble entries nil))
           (text (car assembled))
           (verdict (car (boymoo::check ground library statements text)))
           (choice (prove-prover-checked entries (cadr assembled) numbers verdict)))
      (cond ((not choice) (list text verdict))
            ((failure-p choice)
             (if (prove-rejected verdict) (list text verdict) choice))
            (t
             (let* ((baseline-needed (and (not baseline-checked)
                                          (not (equal (car (prove-rejected verdict)) "proofs"))))
                    (baseline-text (and baseline-needed
                                        (car (prove-prover-assemble entries t))))
                    (baseline-verdict
                     (and baseline-needed
                          (car (boymoo::check ground library statements baseline-text)))))
               (cond ((or (not baseline-needed)
                          (equal (prove-skip-count baseline-verdict) (len entries)))
                      (driver-check (1- n) ground library statements
                                    (driver-without-certificate entries choice) numbers
                                    (or baseline-needed baseline-checked)))
                     ((prove-rejected baseline-verdict)
                      (list baseline-text baseline-verdict))
                     (t '(:failure "failure" "")))))))))

(defun driver-prove-checked (ground library statements aids options)
  (let ((entries (driver-search library statements aids options)))
    (if (failure-p entries)
        entries
      (driver-check 1000000 ground library statements entries
                    (driver-entry-numbers entries) nil))))

(defun driver-attempt-numbers (numbers set library contexts sessions answers)
  (if (endp numbers)
      (reverse answers)
    (let* ((number (car numbers))
           (context (assoc-equal number contexts))
           (attempt (if context
                        (driver-context-attempt set context library sessions)
                      (cons nil sessions))))
      (driver-attempt-numbers (cdr numbers) set library contexts (cdr attempt)
                              (acons number (car attempt) answers)))))

(defun driver-attempts (set library statements aids numbers)
  (let ((input (driver-input library statements aids
                             (list (cons :selected numbers) (list :sets set)))))
    (if (failure-p input)
        input
      (driver-attempt-numbers numbers set (car input)
                              (driver-contexts (cadr input) (prove-prefix) nil)
                              nil nil))))

(defun driver-entries-from-answers (library statements answers)
  (let ((input (driver-input library statements "" '((:selected)))))
    (if (failure-p input)
        input
      (driver-entry-answers (caddr input) answers))))

(defun driver-assemble-answers (library statements answers)
  (let ((entries (driver-entries-from-answers library statements answers)))
    (if (failure-p entries)
        entries
      (car (prove-prover-assemble entries nil)))))

(defun driver-refuse-answers (library statements answers verdict)
  (let ((entries (driver-entries-from-answers library statements answers)))
    (if (failure-p entries)
        entries
      (let* ((ends (cadr (prove-prover-assemble entries nil)))
             (numbers (driver-entry-numbers entries))
             (choice (prove-prover-checked entries ends numbers verdict)))
        (cond ((failure-p choice) choice)
              (choice (table-delete answers (nth choice numbers)))
              (t answers))))))

(defun driver-plan-rank (targets rank plan)
  (if (endp targets)
      plan
    (let* ((target (car targets))
           (set (driver-target-set target rank)))
      (driver-plan-rank (cdr targets) rank
                        (if set (cons (list rank (driver-target-number target) set) plan)
                          plan)))))

(defun driver-plan-ranks (remaining rank targets plan)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (reverse plan)
    (driver-plan-ranks (1- remaining) (1+ rank) targets
                       (driver-plan-rank targets rank plan))))

(defun driver-plan (library statements aids options)
  (let ((input (driver-input library statements aids options)))
    (if (failure-p input)
        input
      (let ((targets (cadddr input)))
        (driver-plan-ranks (driver-rank-count targets options) 0 targets nil)))))
