(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-books-newline* (coerce (list #\Newline) 'string))
(defconst *h3-books-tab* (coerce (list #\Tab) 'string))

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

(mutual-recursion
 (defun h3-books-proof-dependencies-include (n name entries facts needed external)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "h3-books-proof-dependencies-include"))
         ((member-equal name needed) (list needed external))
         (t (let ((entry (assoc-equal name entries)))
              (if entry
                  (h3-books-proof-dependencies-visit
                   (1- n) (cdr entry) entries facts (append needed (list name)) external)
                '(:failure "failure" ""))))))

 (defun h3-books-proof-dependencies-visit (n entry entries facts needed external)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "h3-books-proof-dependencies-visit")
     (proof-with-checked-results ((source (proof-term-at entry 3)))
       (h3-books-dependency-lines (1- n)
                                  (h3-books-source-lines (coerce source 'list) nil nil)
                                  entries facts needed external))))

 (defun h3-books-dependency-lines (n steps entries facts needed external)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h3-books-dependency-lines"))
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

