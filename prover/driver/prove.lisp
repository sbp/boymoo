(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *prove-sets* '("T1" "T2" "T3" "T4" "H1" "H2" "H3" "H4" "B1" "B2" "L1"))

(defconst *prove-order*
  '(("define" "T1" "B2" "H3" "T3" "H4" "L1" "B1" "T4" "T2" "H2" "H1")
    ("constrain" "H4" "T4" "T3" "B1" "H2" "H3" "B2" "L1" "T1" "H1" "T2")
    ("theorem" "H3" "B2" "T1" "T3" "B1" "H4" "T2" "T4" "L1" "H2" "H1")))

(defconst *prove-library-order*
  '(("define" "H4" "B2" "B1" "T2" "L1" "T4" "T3" "T1" "H3" "H2" "H1")
    ("constrain" "T4" "T1" "B1" "B2" "T2" "H4" "L1" "T3" "H3" "H1" "H2")
    ("theorem" "B1" "T3" "B2" "H4" "T4" "T1" "L1" "H2" "H3" "T2" "H1")))

(defconst *prove-entry-word*
  '(("theorem" . "theorem") ("define" . "measure") ("constrain" . "witness")))

(defconst *prove-aid-words* '("(hints " "(instructions " "(measure "))
(defconst *prove-warrant* "(ACL2::FORCE (ACL2::APPLY$-WARRANT-")
(defconst *prove-newline* (string (code-char 10)))

(defun prove-entry (number name blocks failure)
  (list :entry number name blocks failure))

(defun prove-entry-number (entry) (second entry))
(defun prove-entry-name (entry) (third entry))
(defun prove-entry-blocks (entry) (fourth entry))
(defun prove-entry-failure (entry) (fifth entry))

(defun prove-entry-with-blocks (entry blocks)
  (prove-entry (prove-entry-number entry) (prove-entry-name entry)
               blocks (prove-entry-failure entry)))

(defun prove-target (entry statement line aids order)
  (list :target entry statement line aids order))

(defun prove-target-entry (target) (second target))
(defun prove-target-statement (target) (third target))
(defun prove-target-line (target) (fourth target))
(defun prove-target-aids (target) (fifth target))
(defun prove-target-order (target) (sixth target))

(defun prove-target-pending (target)
  (let ((entry (prove-target-entry target)))
    (and (null (prove-entry-blocks entry))
         (equal (prove-entry-failure entry) ""))))

(defun prove-row (line statement target) (list line statement target))
(defun prove-row-line (row) (first row))
(defun prove-row-statement (row) (second row))
(defun prove-row-target (row) (third row))

(defun prove-options (sets library-order tactic-seconds)
  (list :options sets library-order tactic-seconds))

(defun prove-options-sets (options) (second options))
(defun prove-options-library-order (options) (third options))
(defun prove-options-tactic-seconds (options) (fourth options))

(defun prove-ascii-chars-p (chars)
  (or (endp chars)
      (and (< (char-code (car chars)) 128)
           (prove-ascii-chars-p (cdr chars)))))

(defun prove-block-content-p (block)
  (and (stringp block)
       (text-ends-with block *prove-newline*)
       (not (text-starts-with block "(skip "))
       (< (text-find block (string-append *prove-newline* "(skip ")) 0)
       (prove-ascii-chars-p (coerce block 'list))))

(defun prove-support-blocks-p (support)
  (or (endp support)
      (and (prove-block-content-p (car support))
           (text-starts-with (car support) '("(define " "(lemma " "(choose "))
           (prove-support-blocks-p (cdr support)))))

(defun prove-valid-blocks (answer statement)
  (if (null answer)
      nil
    (let* ((kind (worklist-statement-kind statement))
           (word (cdr (assoc-equal kind *prove-entry-word*)))
           (name (worklist-statement-obligation statement)))
      (cond ((null word) '(:failure "failure" ""))
            ((null name) nil)
            (t (let* ((support (first answer))
                      (entry (second answer))
                      (opening (text-join "" (list "(" word " " name))))
                 (and (stringp entry)
                      (text-starts-with entry (list (string-append opening ")")
                                               (string-append opening " ")))
                      (prove-block-content-p entry)
                      (prove-support-blocks-p support)
                      (append support (list entry)))))))))

(defun prove-aid-opening (line words)
  (cond ((endp words) nil)
        ((text-starts-with line (car words)) (car words))
        (t (prove-aid-opening line (cdr words)))))

(defun prove-aid-name (line opening)
  (let ((reader (reader-reader-take (reader-reader line) opening)))
    (if (failure-p reader)
        reader
      (let ((result (reader-reader-datum reader)))
        (if (failure-p result) result (worklist-name-text (car result)))))))

(defun prove-aids-add-row (rows name row)
  (cond ((endp rows) (list (list name row)))
        ((equal name (caar rows)) (cons (cons name (cons row (cdar rows))) (cdr rows)))
        (t (cons (car rows) (prove-aids-add-row (cdr rows) name row)))))

(defun prove-aids-reverse-rows (rows)
  (if (endp rows)
      nil
    (cons (cons (caar rows) (reverse (cdar rows)))
          (prove-aids-reverse-rows (cdr rows)))))

(defun prove-aids-index (lines index rows)
  (if (endp lines)
      (prove-aids-reverse-rows rows)
    (let* ((line (car lines))
           (opening (prove-aid-opening line *prove-aid-words*))
           (name (and opening (prove-aid-name line opening))))
      (cond ((stringp name)
             (prove-aids-index (cdr lines) (1+ index)
                               (prove-aids-add-row rows name (list index line))))
            ((and (failure-p name) (equal (cadr name) "fuel")) name)
            (t (prove-aids-index (cdr lines) (1+ index) rows))))))

(defun prove-aids (lines)
  (let ((rows (prove-aids-index lines 0 nil)))
    (if (failure-p rows) rows (list :aids rows))))

(defun prove-aids-rows (aids) (second aids))

(defun prove-aids-merge-rows (left right)
  (declare (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond ((endp left) right)
        ((endp right) left)
        ((<= (caar left) (caar right))
         (cons (car left) (prove-aids-merge-rows (cdr left) right)))
        (t (cons (car right) (prove-aids-merge-rows left (cdr right))))))

(defun prove-aids-name-rows (names rows)
  (if (endp names)
      nil
    (prove-aids-merge-rows (cdr (assoc-equal (car names) rows))
                          (prove-aids-name-rows (cdr names) rows))))

(defun prove-aids-row-lines (rows)
  (if (endp rows)
      nil
    (cons (cadar rows) (prove-aids-row-lines (cdr rows)))))

(defun prove-aids-for-statement (aids statement)
  (let ((names (if (equal (worklist-statement-kind statement) "define")
                   (worklist-statement-names statement)
                 (list (worklist-statement-obligation statement)))))
    (prove-aids-row-lines (prove-aids-name-rows names (prove-aids-rows aids)))))

(defun prove-prefix () (list :prefix nil))

(defun prove-prefix-add (prefix line statement)
  (declare (ignore statement))
  (list :prefix (cons line (second prefix))))

(defun prove-prefix-lines (prefix) (reverse (second prefix)))

(defun prove-preferred-set (kind obligation line)
  (cond ((and (equal kind "theorem") (<= 0 (text-find line *prove-warrant*))) "H4")
        ((and (equal kind "constrain") (text-starts-with obligation "ACL2::APPLY$-WARRANT-")) "L1")
        (t nil)))

(defun prove-order-with-budgets (order preferred seconds)
  (if (endp order)
      nil
    (let* ((name (car order))
           (budget (if (and seconds (not (equal seconds 0))) seconds
                     (if (equal name preferred) 16 2))))
      (cons (list name budget) (prove-order-with-budgets (cdr order) preferred seconds)))))

(defun prove-prover-order (options statement line)
  (let* ((sets (prove-options-sets options))
         (automaticp (eq sets :none))
         (kind (worklist-statement-kind statement))
         (obligation (worklist-statement-obligation statement))
         (orders (if (prove-options-library-order options) *prove-library-order* *prove-order*))
         (default (and automaticp (assoc-equal kind orders)))
         (order (if automaticp (cdr default) sets)))
    (cond ((and automaticp (null default)) '(:failure "failure" ""))
          ((and (equal kind "constrain") (null obligation))
           ; A constraint without formulas has no witness obligation.
           '(:failure "failure" ""))
          (t (let* ((preferred (prove-preferred-set kind obligation line))
                    (ordered (if (and automaticp (member-equal preferred order))
                                 (cons preferred (remove-equal preferred order))
                               order)))
               (prove-order-with-budgets ordered preferred (prove-options-tactic-seconds options)))))))

(defun prove-run-target (options entry statement line aids selected)
  (if (and entry
           (or (eq selected :none) (member-equal (prove-entry-number entry) selected)))
      (let* ((relevant (prove-aids-for-statement aids statement))
             (order (prove-prover-order options statement line)))
        (if (failure-p order) order (prove-target entry statement line relevant order)))
    nil))

(defun prove-run-rows (lines number seen options aids selected rows entries targets)
  (if (endp lines)
      (list (reverse rows) (reverse entries) (reverse targets))
    (let ((line (car lines)))
      (if (member-equal line seen)
          (prove-run-rows (cdr lines) (1+ number) seen options aids selected rows entries targets)
        (let ((statement (worklist-statement-info line)))
          (if (failure-p statement)
              statement
            (let* ((name (worklist-statement-obligation statement))
                   (entry (and name (prove-entry number name nil "")))
                   (target (prove-run-target options entry statement line aids selected)))
              (if (failure-p target)
                  target
                (prove-run-rows (cdr lines) (1+ number) (cons line seen) options aids selected
                                (cons (prove-row line statement target) rows)
                                (if entry (cons entry entries) entries)
                                (if target (cons target targets) targets))))))))))

(defun prove-prover-run (options library statements aids selected)
  (prove-run-rows statements 1 library options aids selected nil nil nil))

(defun prove-count-newlines (chars count)
  (if (endp chars)
      count
    (prove-count-newlines (cdr chars) (if (eql (car chars) (code-char 10)) (1+ count) count))))

(defun prove-assemble-blocks (blocks seen count reversed-text)
  (let ((block (car blocks)))
    (cond
     ((endp blocks) (list seen count reversed-text))
     ((endp (cdr blocks))
      (list seen (prove-count-newlines (coerce block 'list) count) (cons block reversed-text)))
     ((member-equal block seen) (prove-assemble-blocks (cdr blocks) seen count reversed-text))
     (t (prove-assemble-blocks (cdr blocks) (cons block seen)
                               (prove-count-newlines (coerce block 'list) count)
                               (cons block reversed-text))))))

(defun prove-skip-line (name)
  (text-join "" (list "(skip " name ")" *prove-newline*)))

(defun prove-assemble-entries (entries all-skips seen count reversed-text reversed-ends)
  (if (endp entries)
      (list (text-join "" (reverse reversed-text)) (reverse reversed-ends))
    (let* ((entry (car entries))
           (blocks (prove-entry-blocks entry)))
      (if (or all-skips (null blocks))
          (let ((next (1+ count)))
            (prove-assemble-entries (cdr entries) all-skips seen next
                                    (cons (prove-skip-line (prove-entry-name entry)) reversed-text)
                                    (cons next reversed-ends)))
        (let* ((written (prove-assemble-blocks blocks seen count reversed-text))
               (next (second written)))
          (prove-assemble-entries (cdr entries) all-skips (first written) next (third written)
                                  (cons next reversed-ends)))))))

(defun prove-prover-assemble (entries all-skips)
  (prove-assemble-entries entries all-skips nil 0 nil nil))

(defun prove-decimal-string-p (text)
  (and (not (equal text "")) (reader-all-digits-p (coerce text 'list))))

(defun prove-provisional (verdict)
  (let ((parts (text-split-max verdict " " 8)))
    (and (equal (len parts) 9)
         (equal (first parts) "provisional")
         (equal (second parts) "skipped")
         (prove-decimal-string-p (third parts))
         (equal (fourth parts) "assumed")
         (prove-decimal-string-p (fifth parts))
         (equal (sixth parts) "given-definitions")
         (prove-decimal-string-p (seventh parts))
         (equal (eighth parts) "given-facts")
         (prove-decimal-string-p (ninth parts))
         (list (third parts)))))

(defun prove-rejected (verdict)
  (let ((parts (text-split-max verdict " " 2)))
    (and (equal (len parts) 3)
         (equal (first parts) "rejected")
         (member-equal (second parts) '("library" "statements" "proofs"))
         (prove-decimal-string-p (third parts))
         (cdr parts))))

(defun prove-verdict-number (digits)
  (let ((number (reader-decimal-value (coerce digits 'list))))
    (if (failure-p number) '(:failure "failure" "") number)))

(defun prove-skip-count (verdict)
  (if (equal verdict "accepted")
      0
    (let ((match (prove-provisional verdict)))
      (and match (prove-verdict-number (car match))))))

(defun prove-count-certificates (entries)
  (if (endp entries)
      0
    (+ (if (prove-entry-blocks (car entries)) 1 0) (prove-count-certificates (cdr entries)))))

(defun prove-certificate-size (blocks size)
  (if (endp blocks)
      size
    (prove-certificate-size (cdr blocks) (+ size (length (car blocks))))))

(defun prove-checked-sizes (entries index)
  (if (endp entries)
      nil
    (let ((blocks (prove-entry-blocks (car entries)))
          (rest (prove-checked-sizes (cdr entries) (1+ index))))
      (if blocks
          (cons (list (- (prove-certificate-size blocks 0)) index) rest)
        rest))))

(defun prove-checked-largest (sizes best)
  (cond ((endp sizes) (second best))
        ((or (null best) (< (caar sizes) (car best)))
         (prove-checked-largest (cdr sizes) (car sizes)))
        (t (prove-checked-largest (cdr sizes) best))))

(defun prove-checked-proof-index (ends location index)
  (if (and (consp ends) (< (car ends) location))
      (prove-checked-proof-index (cdr ends) location (1+ index))
    index))

(defun prove-checked-statement-index (numbers location index)
  (if (and (consp numbers) (<= (car numbers) location))
      (prove-checked-statement-index (cdr numbers) location (1+ index))
    (1- index)))

(defun prove-checked-last-certificate (entries index last-index)
  (if (endp entries)
      last-index
    (prove-checked-last-certificate
     (cdr entries) (1+ index)
     (if (prove-entry-blocks (car entries)) index last-index))))

(defun prove-prover-checked (entries ends numbers verdict)
  (let* ((proved (prove-count-certificates entries))
         (skips (and (stringp verdict) (prove-skip-count verdict))))
    (cond
     ((failure-p skips) skips)
     ((equal skips (- (len entries) proved)) nil)
     (t (let* ((match (and (stringp verdict) (prove-rejected verdict)))
               (where (first match))
               (location (and match (prove-verdict-number (second match)))))
          (cond
           ((failure-p location) location)
           ((or (equal where "library") (zp proved)) '(:failure "failure" ""))
           ((null match) (prove-checked-largest (prove-checked-sizes entries 0) nil))
           (t (let* ((index (if (equal where "proofs")
                                (prove-checked-proof-index ends location 0)
                              (prove-checked-statement-index numbers location 0)))
                     (candidate (prove-checked-last-certificate (take (min (len entries) (1+ index)) entries)
                                                                0 nil)))
                (or candidate (prove-checked-last-certificate entries 0 nil))))))))))

(defun prove-checked-total-size (sizes)
  (if (endp sizes)
      0
    (+ (- (caar sizes)) (prove-checked-total-size (cdr sizes)))))

(defun prove-checked-drop-to-size (sizes remaining target)
  (if (or (endp sizes) (<= remaining target))
      nil
    (cons (cadar sizes) (prove-checked-drop-to-size (cdr sizes) (+ remaining (caar sizes)) target))))

(defun prove-prover-checked-halve (entries)
  (let* ((sizes (prove-checked-sizes entries 0))
         (total (prove-checked-total-size sizes)))
    (prove-checked-drop-to-size (seq-sorted sizes) total (floor total 2))))

(defconst *cache-package-operations*
  '("PKG-IMPORTS" "PKG-WITNESS" "SYMBOL-PACKAGE-NAME" "INTERN-IN-PACKAGE-OF-SYMBOL"))

(defun cache-dependency-escaped-part (chars close reversed)
  (cond ((endp chars) nil)
        ((eql (car chars) close)
         (cons (coerce (reverse (cons close reversed)) 'string) (cdr chars)))
        ((eql (car chars) #\\)
         (and (consp (cddr chars))
              (<= 0 (reader-hex-byte (cdr chars)))
              (cache-dependency-escaped-part (cdddr chars) close
                                             (list* (caddr chars) (cadr chars) #\\ reversed))))
        (t (cache-dependency-escaped-part (cdr chars) close (cons (car chars) reversed)))))

(defun cache-dependency-plain-part (chars reversed)
  (if (and (consp chars) (reader-plain-code-p (char-code (car chars))))
      (cache-dependency-plain-part (cdr chars) (cons (car chars) reversed))
    (and reversed (cons (coerce (reverse reversed) 'string) chars))))

(defun cache-dependency-part (chars)
  (if (eql (car chars) #\|)
      (cache-dependency-escaped-part (cdr chars) #\| (list #\|))
    (cache-dependency-plain-part chars nil)))

(defun cache-dependency-add (digest needed)
  (if (member-equal digest needed) needed (cons digest needed)))

(defun cache-dependency-add-all (digests needed)
  (if (endp digests)
      needed
    (cache-dependency-add-all (cdr digests) (cache-dependency-add (car digests) needed))))

(defun cache-dependency-add-packages (packages needed)
  (if (endp packages)
      needed
    (cache-dependency-add-packages (cdr packages) (cache-dependency-add-all (cdar packages) needed))))

(defun cache-dependency-symbol (package name names packages needed)
  (let* ((package-declarations (cdr (assoc-equal package packages)))
         (qualified (and names (string-append package (string-append "::" name))))
         (name-declaration (and qualified (assoc-equal qualified names)))
         (needed (cache-dependency-add-all package-declarations needed)))
    (if name-declaration (cache-dependency-add (cdr name-declaration) needed) needed)))

(defun cache-dependency-scan (n chars names packages needed)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "cache-dependency-scan"))
   ((endp chars) needed)
   ((eql (car chars) #\")
    (let ((quoted (cache-dependency-escaped-part (cdr chars) #\" (list #\"))))
      (cache-dependency-scan (1- n) (if quoted (cdr quoted) (cdr chars)) names packages needed)))
   (t (let* ((package (cache-dependency-part chars))
             (rest (cdr package))
             (name (and (eql (car rest) #\:) (eql (cadr rest) #\:)
                        (cache-dependency-part (cddr rest)))))
        (if name
            (cache-dependency-scan (1- n) (cdr name) names packages
                                   (cache-dependency-symbol (car package) (car name) names packages needed))
          ; No suffix of the same plain part can have a different name after it.
          (cache-dependency-scan (1- n) (if (and package (not (eql (car chars) #\|))) rest (cdr chars))
                                 names packages needed))))))

(defun cache-dependency-operation-p (text operations)
  (and (consp operations)
       (or (<= 0 (text-find text (car operations)))
           (cache-dependency-operation-p text (cdr operations)))))

(defun cache-dependency-texts (texts names packages needed)
  (if (endp texts)
      needed
    (let* ((text (car texts))
           (needed (if (and packages (cache-dependency-operation-p text *cache-package-operations*))
                       (cache-dependency-add-packages packages needed)
                     needed))
           (next (cache-dependency-scan 1000000 (coerce text 'list) names packages needed)))
      (if (failure-p next)
          next
        (cache-dependency-texts (cdr texts) names packages next)))))

(defun cache-subset-dependencies (blocks statement names packages)
  (if (and (endp names) (endp packages))
      ""
    (let ((needed (cache-dependency-texts (append blocks (list statement)) names packages nil)))
      (if (failure-p needed) needed (text-join "" (seq-sorted needed))))))
