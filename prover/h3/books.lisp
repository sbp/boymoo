(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-books-newline* (coerce (list #\Newline) 'string))
(defconst *h3-books-tab* (coerce (list #\Tab) 'string))

(defun h3-books-statement-name (kind data)
  (cond ((equal kind "define")
         (proof-with-checked-results ((definition (proof-term-at data 1)))
           (proof-term-at definition 0)))
        ((equal kind "constrain")
         (proof-with-checked-results ((definitions (proof-term-at data 0))
                                      (definition (proof-term-at definitions 0)))
           (proof-term-at definition 0)))
        ((equal kind "theorem") (proof-term-at data 0))
        (t nil)))

(defun h3-books-header (source)
  (let ((newline (text-find source *h3-books-newline*)))
    (if (< newline 0)
        source
      (seq-slice source 0 newline))))

; Byte strings split on LF, CR and CRLF. Keep the complete terminator.
(defun h3-books-source-lines (chars reversed-line reversed-lines)
  (cond ((endp chars)
         (reverse (if (consp reversed-line)
                      (cons (coerce (reverse reversed-line) 'string) reversed-lines)
                    reversed-lines)))
        ((and (eql (car chars) #\Return) (eql (cadr chars) #\Newline))
         (h3-books-source-lines
          (cddr chars) nil
          (cons (coerce (revappend reversed-line (list #\Return #\Newline)) 'string)
                reversed-lines)))
        ((member-equal (car chars) '(#\Return #\Newline))
         (h3-books-source-lines
          (cdr chars) nil
          (cons (coerce (revappend reversed-line (list (car chars))) 'string)
                reversed-lines)))
        (t (h3-books-source-lines (cdr chars) (cons (car chars) reversed-line)
                                  reversed-lines))))

(defun h3-books-entry-map (entries by-name)
  (if (endp entries)
      by-name
    (proof-with-checked-results ((name (proof-term-at (car entries) 1)))
      (h3-books-entry-map (cdr entries) (table-put by-name name (car entries))))))

(mutual-recursion
 (defun h3-books-proof-dependencies-include (n name entries facts needed external)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "h3-books-proof-dependencies-include"))
         ((member-equal name needed) (list needed external))
         (t (let ((entry (assoc-equal name entries)))
              (if entry
                  (h3-books-proof-dependencies-visit
                   (1- n) (cdr entry) entries facts (append needed (list name)) external)
                '(:failure "failure" ""))))))

 (defun h3-books-proof-dependencies-visit (n entry entries facts needed external)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "h3-books-proof-dependencies-visit")
     (proof-with-checked-results ((source (proof-term-at entry 3)))
       (h3-books-dependency-lines (1- n)
                                  (h3-books-source-lines (coerce source 'list) nil nil)
                                  entries facts needed external))))

 (defun h3-books-dependency-lines (n steps entries facts needed external)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "h3-books-dependency-lines"))
    ((endp steps) (list needed external))
    ((not (text-starts-with (car steps) "(fact "))
     (h3-books-dependency-lines (1- n) (cdr steps) entries facts needed external))
    (t
     (proof-with-checked-results
         ((parsed (reader-reader-line
                   (reader-reader (seq-slice (car steps) 0 -1)))))
       (let ((name (proof-freeze (car (cadar parsed)))))
         (if (assoc-equal name entries)
             (proof-with-checked-results
                 ((updated (h3-books-proof-dependencies-include
                            (1- n) name entries facts needed external)))
               (h3-books-dependency-lines (1- n) (cdr steps) entries facts
                                          (car updated) (cadr updated)))
           (let ((fact (assoc-equal name facts)))
             (if fact
                 (h3-books-dependency-lines (1- n) (cdr steps) entries facts needed
                                            (table-put external name (cdr fact)))
               '(:failure "failure" ""))))))))))

(defun h3-books-witness-dependencies (fields entries facts needed external)
  (if (endp fields)
      (list needed external)
    (let ((name (proof-freeze (car fields))))
      (if (assoc-equal name entries)
          (proof-with-checked-results
              ((updated (h3-books-proof-dependencies-include
                         1000000 name entries facts needed external)))
            (h3-books-witness-dependencies (cdr fields) entries facts
                                           (car updated) (cadr updated)))
        (h3-books-witness-dependencies (cdr fields) entries facts needed external)))))

(defun h3-books-select-entries (entries needed)
  (cond ((endp entries) nil)
        ((member-equal (cadar entries) needed)
         (cons (car entries) (h3-books-select-entries (cdr entries) needed)))
        (t (h3-books-select-entries (cdr entries) needed))))

(defun h3-books-proof-dependencies (lib proof)
  (let ((entries (library-library-entries lib))
        (facts (proof-proof-facts (library-library-proof lib))))
    (proof-with-checked-results
        ((by-name (h3-books-entry-map entries nil))
         (visited (h3-books-proof-dependencies-visit 1000000 proof by-name facts nil nil))
         (kind (proof-term-at proof 0))
         (selected
          (if (equal kind "witness")
              (proof-with-checked-results
                  ((parsed (reader-reader-line (reader-reader (h3-books-header (cadddr proof))))))
                (h3-books-witness-dependencies (cdr (cadar parsed)) by-name facts
                                               (car visited) (cadr visited)))
            visited)))
      (list (h3-books-select-entries entries (car selected))
            (table-items (cadr selected))))))

(defun h3-books-sum-counts (counts total)
  (if (endp counts)
      total
    (h3-books-sum-counts (cdr counts) (+ total (car counts)))))

(defun h3-books-count-newlines (chars total)
  (if (endp chars)
      total
    (h3-books-count-newlines (cdr chars)
                            (if (eql (car chars) #\Newline) (1+ total) total))))

(defun h3-books-assemble-prelude (prelude emitted reversed-payload count)
  (if (endp prelude)
      (list reversed-payload count emitted)
    (let ((entry (car prelude)))
      (proof-with-checked-results ((head (proof-term-at entry 1))
                                   (source (proof-term-at entry 3)))
        (let ((statement (h3-books-header source))
              (previous (assoc-equal head emitted)))
          (cond ((not previous)
                 (proof-with-checked-results ((counts (proof-term-at entry 2)))
                   (let ((total (+ count (h3-books-sum-counts counts 0))))
                     (h3-books-assemble-prelude
                      (cdr prelude) (table-put emitted head statement)
                      (cons source reversed-payload) total))))
                ((equal (cdr previous) statement)
                 (h3-books-assemble-prelude (cdr prelude) emitted reversed-payload count))
                (t '(:failure "failure" ""))))))))

(defun h3-books-assemble-payload (name proof prelude emitted)
  (if (null proof)
      (proof-with-checked-results ((data (proof-line "skip" (list name))))
        (list "skipped" 0 data emitted))
    (proof-with-checked-results
        ((local (h3-books-assemble-prelude prelude emitted nil 0))
         (counts (proof-term-at proof 2))
         (count (+ (cadr local) (h3-books-sum-counts counts 0)))
         (source (proof-term-at proof 3)))
      (list "proved" count (text-join "" (revappend (car local) (list source))) (caddr local)))))

(defun h3-books-assemble-obligations
    (book obligations omitted emitted lines reversed-entries reversed-rows reversed-ends)
  (if (endp obligations)
      (list (text-join "" (reverse reversed-entries)) (reverse reversed-rows)
            (reverse reversed-ends))
    (proof-with-checked-results ((obligation (proof-list-of-length (car obligations) 4)))
      (let* ((name (car obligation))
             (omission (assoc-equal name omitted))
             (proof (if omission nil (cadr obligation)))
             (prelude (caddr obligation))
             (reason (if omission (cdr omission) (cadddr obligation))))
        (proof-with-checked-results ((payload (h3-books-assemble-payload name proof prelude emitted)))
          (let* ((status (car payload))
                 (count (cadr payload))
                 (data (caddr payload))
                 (last-line (h3-books-count-newlines (coerce data 'list) lines)))
            (proof-with-checked-results ((written-name (proof-write name)))
              (let ((row (text-join *h3-books-tab*
                                  (list book written-name status (decimal-text count)
                                        (decimal-text (length data)) reason))))
                (h3-books-assemble-obligations
                 book (cdr obligations) omitted (cadddr payload) last-line
                 (cons data reversed-entries)
                 (cons (string-append row *h3-books-newline*) reversed-rows)
                 (cons (list last-line name) reversed-ends))))))))))

(defun h3-books-assemble (book obligations omitted)
  (h3-books-assemble-obligations book obligations omitted nil 0 nil nil nil))
