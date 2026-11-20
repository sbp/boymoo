; The read-back check of the exporter.  ACL2 reads each file that
; export/export.lsp writes, in the formats of spec/formats.md, and confirms
; that every line is what its world holds: that each statement is the
; event of the world with that name, and each line of program text the
; definition or the attachment that the world holds.  The reading and the
; comparison are written here from the specification, and use neither the
; printer of checks/canon.lsp nor anything of export/export.lsp.
;
; Load this file, from the root of the repository, into the session in
; which the world to be checked is in place, and only after the number of
; the last event of that world has been recorded, since loading the file
; adds events of its own:
;
;   (ld "export/readback.lsp")
;   (rb-readback PREFIX KIND LO HI GROUND-FNS state)
;
; PREFIX is the prefix of the files, such as "build/export/library"; KIND
; is :library or :book; the range is the events numbered above LO and at
; most HI; GROUND-FNS is the list of the functions that spec/ground.txt
; defines.  RB-READBACK reads PREFIX.statements and PREFIX.program, checks
; every line, and writes PREFIX.readback, whose lines are
;
;   (readback FILE LINES CONFIRMED)   for "statements" and for "program";
;   (mismatch FILE N WHAT)            for each of the first 50 lines of a
;                                     file that are not confirmed: the
;                                     number of the line, counted from 1,
;                                     and why; N is 0 if the file cannot
;                                     be read;
;   (complete WHAT N M)               N of the M names of a kind that the
;                                     range introduces, or of its DEFPKG
;                                     events, are introduced by exactly
;                                     one line of the statements, and that
;                                     line is confirmed; and, for the
;                                     library, of the M functions that
;                                     have an attachment, the N that have
;                                     an attach line.
;
; It returns (value (list CONFIRMED MISMATCHES)): the number of statement
; lines confirmed, and the number of lines of both files that are not, a
; file that cannot be read counting as one.
;
; The library is ACL2's own world less the ground theory: for KIND
; :library, the functions of GROUND-FNS, ACL2's axioms and the constants T
; and NIL are not names of the range, except that the program text of the
; library begins with the definitions of the ground theory.

(in-package "ACL2")

(program)
(set-state-ok t)

;;; 1. Packages

; Reading a symbol PKG::NAME interns NAME in the package PKG, by way of a
; symbol of that package.  For a package that ACL2 knows and does not
; hide, PKG-WITNESS gives one.  ACL2 refuses PKG-WITNESS for a hidden
; package (the lines no-plain of checks/expected/facts.txt), so for those
; the symbol is found by the Common Lisp under ACL2, which holds every
; package of the world; that needs a trust tag.

(defun rb-hidden-witness (name)
  (declare (ignore name))
  nil)

(defttag :rb-readback)

(progn! (set-raw-mode t)
        (defun rb-hidden-witness (name)
          (let ((p (find-package name)))
            (and p (intern "ACL2-PKG-WITNESS" p)))))

(defttag nil)

; An alist from the name of each package of the world to a symbol of it.

(defun rb-witnesses (entries)
  (cond ((endp entries) nil)
        (t (let* ((name (package-entry-name (car entries)))
                  (sym (if (package-entry-hidden-p (car entries))
                           (rb-hidden-witness name)
                         (pkg-witness name))))
             (if sym
                 (cons (cons name sym) (rb-witnesses (cdr entries)))
               (rb-witnesses (cdr entries)))))))

;;; 2. Reading the format of spec/formats.md, sections 1 and 2

; S is the text of a whole file, I the position at which to read, and N
; the position of the line feed that ends the line.  A reading function
; returns (mv err value i): ERR is NIL, or a string that says why the text
; is not the one text of a datum; I is the position after what was read.

(defun rb-plain-p (c)
  (or (and (char<= #\A c) (char<= c #\Z))
      (and (char<= #\0 c) (char<= c #\9))
      (member c '(#\- #\+ #\* #\/ #\< #\= #\> #\! #\? #\$ #\% #\& #\_ #\^
                  #\~ #\. #\@))))

(defun rb-all-plain-p (str i n)
  (or (<= n i)
      (and (rb-plain-p (char str i))
           (rb-all-plain-p str (+ i 1) n))))

(defun rb-plain-end (s i n)
  (if (and (< i n) (rb-plain-p (char s i)))
      (rb-plain-end s (+ i 1) n)
    i))

(defun rb-hex-digit (c)
  (cond ((and (char<= #\0 c) (char<= c #\9)) (- (char-code c) 48))
        ((and (char<= #\A c) (char<= c #\F)) (- (char-code c) 55))
        (t nil)))

; The code written by two hexadecimal digits at I, or NIL.

(defun rb-hex2 (s i n)
  (and (< (+ i 1) n)
       (let ((a (rb-hex-digit (char s i)))
             (b (rb-hex-digit (char s (+ i 1)))))
         (and a b (+ (* 16 a) b)))))

; The characters of a string, or of a symbol part between bars, up to the
; closing DELIM, #\" or #\|.  A character from 32 to 126 other than DELIM
; and the backslash stands for itself, and every other character is
; written as a backslash and two hexadecimal digits; only such a character
; may be written so.  ACC holds the characters read, in reverse order.

(defun rb-escaped (s i n delim acc)
  (cond
   ((<= n i) (mv "a string or a name between bars is not closed" nil i))
   ((eql (char s i) delim) (mv nil (coerce (reverse acc) 'string) (+ i 1)))
   ((not (eql (char s i) #\\))
    (rb-escaped s (+ i 1) n delim (cons (char s i) acc)))
   (t (let ((k (rb-hex2 s (+ i 1) n)))
        (cond ((null k)
               (mv "a backslash is not followed by two upper case hexadecimal digits"
                   nil i))
              ((and (<= 32 k) (<= k 126)
                    (not (eql k 92))
                    (not (eql k (char-code delim))))
               (mv "a character that can be written as itself is written with a backslash"
                   nil i))
              (t (rb-escaped s (+ i 3) n delim (cons (code-char k) acc))))))))

; Numbers.  Each function looks at the text from I to J, a run of plain
; characters, and returns the number it is the one text of, or NIL.

(defun rb-digits (s i j v)
  (cond ((<= j i) v)
        ((and (char<= #\0 (char s i)) (char<= (char s i) #\9))
         (rb-digits s (+ i 1) j (+ (* 10 v) (- (char-code (char s i)) 48))))
        (t nil)))

; A positive number: a digit from 1 to 9, then digits.

(defun rb-positive (s i j)
  (and (< i j)
       (not (eql (char s i) #\0))
       (rb-digits s i j 0)))

(defun rb-integer (s i j)
  (cond ((and (= j (+ i 1)) (eql (char s i) #\0)) 0)
        ((and (< i j) (eql (char s i) #\-))
         (let ((p (rb-positive s (+ i 1) j)))
           (and p (- p))))
        (t (rb-positive s i j))))

(defun rb-slash (s i j)
  (cond ((<= j i) nil)
        ((eql (char s i) #\/) i)
        (t (rb-slash s (+ i 1) j))))

; A fraction is an integer other than 0, a slash, and a positive number
; greater than 1 with which it has no common factor: that is, the
; denominator of the fraction is that number.

(defun rb-rational (s i j)
  (let ((k (rb-slash s i j)))
    (if (null k)
        (rb-integer s i j)
      (let ((a (rb-integer s i k))
            (b (rb-positive s (+ k 1) j)))
        (and a b
             (not (eql a 0))
             (< 1 b)
             (eql (denominator (/ a b)) b)
             (/ a b))))))

; A character #\XX, or a complex rational #C(R I) with I not 0.

(defun rb-sharp (s i n)
  (cond
   ((and (< (+ i 1) n) (eql (char s (+ i 1)) #\\))
    (let ((k (rb-hex2 s (+ i 2) n)))
      (if k
          (mv nil (code-char k) (+ i 4))
        (mv "a character is not written with two upper case hexadecimal digits"
            nil i))))
   ((and (< (+ i 2) n)
         (eql (char s (+ i 1)) #\C)
         (eql (char s (+ i 2)) #\())
    (let* ((a (+ i 3))
           (b (rb-plain-end s a n))
           (re (rb-rational s a b))
           (c (+ b 1))
           (d (rb-plain-end s (min c n) n))
           (im (and (< c n) (rb-rational s c d))))
      (if (and re im
               (eql (char s b) #\Space)
               (not (eql im 0))
               (< d n)
               (eql (char s d) #\)))
          (mv nil (complex re im) (+ d 1))
        (mv "not the one text of a complex rational" nil i))))
   (t (mv "# begins neither a character nor a complex rational" nil i))))

; One part of a symbol, its package name or its name: plain characters,
; at least one; or characters between bars, if they are not all plain or
; there are none.

(defun rb-part (s i n)
  (cond
   ((and (< i n) (eql (char s i) #\|))
    (mv-let (err str j)
      (rb-escaped s (+ i 1) n #\| nil)
      (cond (err (mv err nil i))
            ((and (< 0 (length str))
                  (rb-all-plain-p str 0 (length str)))
             (mv "a symbol part that can be written plain is written between bars"
                 nil i))
            (t (mv nil str j)))))
   (t (let ((j (rb-plain-end s i n)))
        (if (= i j)
            (mv "no datum begins with this character" nil i)
          (mv nil (subseq s i j) j))))))

; The symbol PKG::NAME.  It exists when ACL2 knows the package PKG and
; the symbol that NAME gives in PKG is PKG's own, not an import.

(defun rb-intern (pkg name i pkgs)
  (let ((w (cdr (assoc-equal pkg pkgs))))
    (if (null w)
        (mv (concatenate 'string "ACL2 knows no package " pkg) nil i)
      (let ((sym (intern-in-package-of-symbol name w)))
        (if (equal (symbol-package-name sym) pkg)
            (mv nil sym i)
          (mv (concatenate 'string "the symbol " pkg "::" name
                           " does not exist: its package imports a symbol of that name")
              nil i))))))

(mutual-recursion

 (defun rb-datum (s i n pkgs)
   (cond
    ((<= n i) (mv "a datum is missing" nil i))
    ((eql (char s i) #\() (rb-list s (+ i 1) n pkgs))
    ((eql (char s i) #\") (rb-escaped s (+ i 1) n #\" nil))
    ((eql (char s i) #\#) (rb-sharp s i n))
    (t (mv-let (err part j)
         (rb-part s i n)
         (cond
          (err (mv err nil i))
          ((and (< (+ j 1) n) (eql (char s j) #\:) (eql (char s (+ j 1)) #\:))
           (mv-let (err name k)
             (rb-part s (+ j 2) n)
             (if err
                 (mv err nil k)
               (rb-intern part name k pkgs))))
          ((eql (char s i) #\|)
           (mv "a name between bars is not followed by ::" nil j))
          (t (let ((r (rb-rational s i j)))
               (if r
                   (mv nil r j)
                 (mv "plain characters that are neither a symbol nor the one text of a number"
                     nil i)))))))))

; A cons, after its opening parenthesis.  ACC holds the elements read, in
; reverse order.

 (defun rb-list (s i n pkgs)
   (if (and (< i n) (eql (char s i) #\)))
       (mv "() is written for COMMON-LISP::NIL" nil i)
     (mv-let (err x j)
       (rb-datum s i n pkgs)
       (if err
           (mv err nil j)
         (rb-rest s j n pkgs (list x))))))

 (defun rb-rest (s i n pkgs acc)
   (cond
    ((<= n i) (mv "a list is not closed" nil i))
    ((eql (char s i) #\)) (mv nil (reverse acc) (+ i 1)))
    ((not (eql (char s i) #\Space))
     (mv "the elements of a list are not separated by one space" nil i))
    ((and (< (+ i 2) n)
          (eql (char s (+ i 1)) #\.)
          (eql (char s (+ i 2)) #\Space))
     (mv-let (err x j)
       (rb-datum s (+ i 3) n pkgs)
       (cond (err (mv err nil j))
             ((consp x) (mv "a cons is written after a dot" nil i))
             ((null x) (mv "COMMON-LISP::NIL is written after a dot" nil i))
             ((not (and (< j n) (eql (char s j) #\))))
              (mv "a list does not end after its last cdr" nil j))
             (t (mv nil (revappend acc x) (+ j 1))))))
    (t (mv-let (err x j)
         (rb-datum s (+ i 1) n pkgs)
         (if err
             (mv err nil j)
           (rb-rest s j n pkgs (cons x acc))))))))

; A line: an opening parenthesis, a word of lower case letters and
; hyphens, data each after one space, and a closing parenthesis just
; before the line feed.  Returns (mv err word data).

(defun rb-word-end (s i n)
  (if (and (< i n)
           (or (and (char<= #\a (char s i)) (char<= (char s i) #\z))
               (eql (char s i) #\-)))
      (rb-word-end s (+ i 1) n)
    i))

(defun rb-data (s i n pkgs acc)
  (cond ((and (= (+ i 1) n) (eql (char s i) #\))) (mv nil (reverse acc)))
        ((and (< i n) (eql (char s i) #\Space))
         (mv-let (err x j)
           (rb-datum s (+ i 1) n pkgs)
           (if err
               (mv err nil)
             (rb-data s j n pkgs (cons x acc)))))
        (t (mv "the line does not end after its data" nil))))

(defun rb-read-line (s i n pkgs)
  (if (not (and (< i n) (eql (char s i) #\()))
      (mv "the line does not begin with (" nil nil)
    (let ((j (rb-word-end s (+ i 1) n)))
      (if (= j (+ i 1))
          (mv "the line has no word" nil nil)
        (mv-let (err data)
          (rb-data s j n pkgs nil)
          (if err
              (mv err nil nil)
            (mv nil (subseq s (+ i 1) j) data)))))))

; The position of the line feed that ends the line that begins at I, or
; LEN if there is none; and whether every character before it has a code
; from 32 to 126.

(defun rb-line-end (s i len ok)
  (cond ((<= len i) (mv len ok))
        ((eql (char s i) #\Newline) (mv i ok))
        (t (rb-line-end s (+ i 1) len
                        (and ok
                             (<= 32 (char-code (char s i)))
                             (<= (char-code (char s i)) 126))))))

;;; 3. What the world holds

; ENV is (KIND LO HI GROUND TYPES PACKAGES): KIND, LO, HI and GROUND are
; the arguments of RB-READBACK; TYPES is a fast alist that maps each name
; introduced by an event of the range to the type of that event; PACKAGES
; is the list of the states (NAME HIDDEN IMPORTS) in which the DEFPKG
; events of the range left the packages they declare.

(defmacro rb-kind (env) `(nth 0 ,env))
(defmacro rb-lo (env) `(nth 1 ,env))
(defmacro rb-hi (env) `(nth 2 ,env))
(defmacro rb-ground (env) `(nth 3 ,env))
(defmacro rb-types (env) `(nth 4 ,env))
(defmacro rb-packages (env) `(nth 5 ,env))

(defun rb-name (sym)
  (concatenate 'string (symbol-package-name sym) "::" (symbol-name sym)))

(defun rb-msg (sym text)
  (concatenate 'string (rb-name sym) " " text))

; A function of no arguments has the formals NIL, so a function is a
; symbol that has the property FORMALS at all.

(defun rb-has (name prop wrld)
  (not (eq (getpropc name prop :none wrld) :none)))

(defun rb-function-p (f wrld)
  (and (symbolp f) (rb-has f 'formals wrld)))

(defun rb-program-p (f wrld)
  (eq (getpropc f 'symbol-class nil wrld) :program))

(defun rb-reserve-kind-p (name wrld)
  (or (rb-has name 'macro-body wrld)
      (rb-has name 'const wrld)
      (rb-has name 'label wrld)
      (rb-has name 'theory wrld)
      (rb-has name 'stobj wrld)
      (rb-has name 'stobj-live-var wrld)))

(defun rb-held-p (name wrld)
  (or (rb-function-p name wrld)
      (rb-has name 'theorem wrld)
      (rb-reserve-kind-p name wrld)))

(defun rb-event-type (name env)
  (cdr (hons-get name (rb-types env))))

; The names that the library leaves to the ground theory.

(defun rb-ground-name-p (name env)
  (or (member-eq name (rb-ground env))
      (member-eq name '(t nil))
      (eq (rb-event-type name env) 'defaxiom)))

; Why NAME is not a name of the range, or NIL if it is.

(defun rb-range-msg (name env wrld)
  (let ((n (getpropc name 'absolute-event-number nil wrld)))
    (cond ((not (and (integerp n) (< (rb-lo env) n) (<= n (rb-hi env))))
           (rb-msg name "is not introduced by an event of the range"))
          ((and (eq (rb-kind env) :library) (rb-ground-name-p name env))
           (rb-msg name "belongs to the ground theory, not to the library"))
          (t nil))))

; The ruler-extenders of the justification that ACL2 stores for F, or NIL
; if it stores none.

(defun rb-rulers (f wrld)
  (let ((just (getpropc f 'justification nil wrld)))
    (if just (access justification just :ruler-extenders) nil)))

; The name and the list of the constraint that F shares.

(defun rb-constrainer (f wrld)
  (mv-let (c lst origins)
    (constraint-info f wrld)
    (declare (ignore lst origins))
    c))

(defun rb-constraint (c wrld)
  (mv-let (c1 lst origins)
    (constraint-info c wrld)
    (declare (ignore c1 origins))
    lst))

; Whether F shares the constraint of an encapsulate: ACL2 holds such a
; constraint as the property CONSTRAINT-LST-ETC, a pair whose first element
; is T for a function that has none.

(defun rb-constrained-p (f wrld)
  (not (eq (car (getpropc f 'constraint-lst-etc '(t . nil) wrld)) t)))

;;; 4. The statements

; Each check returns NIL if the line is what the world holds, or a string
; that says why not.

; A definition (F FORMALS BODY) in logic mode, with the ruler-extenders
; RULERS of its line.  F may be a function of the ground theory when
; GROUND-OK.

(defun rb-logic-def-msg (d rulers ground-ok env wrld)
  (let* ((f (car d))
         (range (if (and ground-ok (member-eq f (rb-ground env)))
                    nil
                  (rb-range-msg f env wrld)))
         (body (getpropc f 'unnormalized-body nil wrld)))
    (cond ((not (rb-function-p f wrld)) (rb-msg f "is not a function"))
          ((rb-program-p f wrld) (rb-msg f "is in program mode"))
          (range range)
          ((rb-constrained-p f wrld)
           (rb-msg f "is constrained"))
          ((not (equal (cadr d) (getpropc f 'formals nil wrld)))
           (rb-msg f "has other formals"))
          ((not (and body (equal (caddr d) body)))
           (rb-msg f "has another body"))
          ((not (equal rulers (rb-rulers f wrld)))
           (rb-msg f "has other ruler-extenders"))
          (t nil))))

; The program text of a function in program mode is the body ACL2 runs:
; its body with each mbe replaced by its executable half, that is, each
; call (return-last 'mbe1-raw EXEC LOGIC) by EXEC (spec/language.md,
; section 7).

(mutual-recursion

 (defun rb-exec (term)
   (cond ((variablep term) term)
         ((fquotep term) term)
         ((and (eq (ffn-symb term) 'return-last)
               (equal (fargn term 1) ''mbe1-raw))
          (rb-exec (fargn term 2)))
         ((flambda-applicationp term)
          (cons (list 'lambda (lambda-formals (ffn-symb term))
                      (rb-exec (lambda-body (ffn-symb term))))
                (rb-exec-lst (fargs term))))
         (t (cons (ffn-symb term) (rb-exec-lst (fargs term))))))

 (defun rb-exec-lst (terms)
   (cond ((endp terms) nil)
         (t (cons (rb-exec (car terms)) (rb-exec-lst (cdr terms)))))))

; A definition in program mode.  ACL2 stores no body for the functions in
; program mode that it starts with (spec/language.md, section 7), and the
; exporter translates the event that defined each: then the body must be a
; term of the world whose variables are formals, with no mbe left.

(defun rb-program-def-msg (d rulers env wrld)
  (let* ((f (car d))
         (range (rb-range-msg f env wrld))
         (body (getpropc f 'unnormalized-body nil wrld)))
    (cond ((not (rb-function-p f wrld)) (rb-msg f "is not a function"))
          ((not (rb-program-p f wrld)) (rb-msg f "is not in program mode"))
          (range range)
          ((not (equal (cadr d) (getpropc f 'formals nil wrld)))
           (rb-msg f "has other formals"))
          ((not (equal rulers (rb-rulers f wrld)))
           (rb-msg f "has other ruler-extenders"))
          (body (if (equal (caddr d) (rb-exec body))
                    nil
                  (rb-msg f "has another body")))
          ((not (termp (caddr d) wrld))
           (rb-msg f "has a body that is not a term"))
          ((not (equal (caddr d) (rb-exec (caddr d))))
           (rb-msg f "has a body in which an mbe remains"))
          ((not (subsetp-eq (all-vars (caddr d)) (cadr d)))
           (rb-msg f "has a body with a variable that is not a formal"))
          (t nil))))

(defun rb-defs-msg (defs rulers mode ground-ok env wrld)
  (cond ((endp defs) nil)
        (t (or (if (eq mode :logic)
                   (rb-logic-def-msg (car defs) rulers ground-ok env wrld)
                 (rb-program-def-msg (car defs) rulers env wrld))
               (rb-defs-msg (cdr defs) rulers mode ground-ok env wrld)))))

; The functions of one line were introduced by one event, and if ACL2
; holds a clique of several functions for one of them, they are that
; clique.

(defun rb-same-number (fns n wrld)
  (or (endp fns)
      (and (eql (getpropc (car fns) 'absolute-event-number nil wrld) n)
           (rb-same-number (cdr fns) n wrld))))

(defun rb-clique (fns wrld)
  (cond ((endp fns) nil)
        ((consp (cdr (getpropc (car fns) 'recursivep nil wrld)))
         (getpropc (car fns) 'recursivep nil wrld))
        (t (rb-clique (cdr fns) wrld))))

(defun rb-set-equal (a b)
  (and (subsetp-eq a b) (subsetp-eq b a)))

(defun rb-clique-msg (fns wrld)
  (let ((clique (rb-clique fns wrld)))
    (cond ((not (no-duplicatesp-eq fns))
           "a function stands twice on the line")
          ((not (rb-same-number (cdr fns)
                                (getpropc (car fns) 'absolute-event-number nil wrld)
                                wrld))
           "the functions of the line were not introduced by one event")
          ((and clique (not (rb-set-equal fns clique)))
           "the functions of the line are not the clique that ACL2 holds")
          (t nil))))

; The names that the exporter makes for a formula of a constraint that
; ACL2 holds under no name of its own: "G definition" or "G choice" in the
; package of G, or "C constraint I", each possibly followed by a space and
; a positive number, which the exporter adds when the name is in use.

(defun rb-numbered-p (str base)
  (let ((m (length base))
        (n (length str)))
    (and (<= m n)
         (equal (subseq str 0 m) base)
         (or (= m n)
             (and (eql (char str m) #\Space)
                  (rb-positive str (+ m 1) n)
                  t)))))

(defun rb-space (str i n)
  (cond ((<= n i) n)
        ((eql (char str i) #\Space) i)
        (t (rb-space str (+ i 1) n))))

; The number I of a name "C constraint I", or NIL.

(defun rb-constraint-index (str c)
  (let* ((base (concatenate 'string (symbol-name c) " constraint "))
         (m (length base))
         (n (length str)))
    (and (< m n)
         (equal (subseq str 0 m) base)
         (let ((k (rb-space str m n)))
           (and (rb-numbered-p (subseq str k n) "")
                (rb-positive str m k))))))

; TERM is (equal (G . formals) X).  When the constraint L is known, TERM
; is a member of it; when L is unknown, X is the body of G.

(defun rb-definition-term-p (g term l wrld)
  (let ((body (getpropc g 'unnormalized-body nil wrld)))
    (and (true-listp term)
         (= (len term) 3)
         (eq (car term) 'equal)
         (equal (cadr term) (cons g (getpropc g 'formals nil wrld)))
         (if (unknown-constraints-p l)
             (and body (equal (caddr term) body))
           (member-equal term l)))))

(defun rb-made-for-fn-p (name str term fns l wrld)
  (and (consp fns)
       (or (let ((g (car fns)))
             (and (eq name (intern-in-package-of-symbol str g))
                  (or (and (rb-numbered-p str (concatenate 'string (symbol-name g)
                                                           " definition"))
                           (rb-definition-term-p g term l wrld))
                      (and (rb-numbered-p str (concatenate 'string (symbol-name g)
                                                           " choice"))
                           (getpropc g 'defchoose-axiom nil wrld)
                           (equal term (getpropc g 'defchoose-axiom nil wrld))))))
           (rb-made-for-fn-p name str term (cdr fns) l wrld))))

(defun rb-made-name-p (name term fns c l wrld)
  (let ((str (symbol-name name)))
    (or (rb-made-for-fn-p name str term fns l wrld)
        (and (not (unknown-constraints-p l))
             (eq name (intern-in-package-of-symbol str c))
             (let ((i (rb-constraint-index str c)))
               (and i
                    (<= i (len l))
                    (equal term (nth (- i 1) l))))))))

; A formula (NAME TERM) of a constraint: a theorem of the range, or a name
; that ACL2 does not hold and that the exporter made for it.

(defun rb-formula-msg (pair fns c l env wrld)
  (let* ((name (car pair))
         (term (cadr pair))
         (thm (getpropc name 'theorem nil wrld)))
    (cond ((and thm
                (null (rb-range-msg name env wrld))
                (or (equal term thm)
                    (equal term (remove-guard-holders thm wrld))))
           nil)
          ((rb-held-p name wrld)
           (rb-msg name "is held by ACL2 but is not a theorem of the range with this formula"))
          ((rb-made-name-p name term fns c l wrld) nil)
          (t (rb-msg name "is neither a theorem of the range nor a name made for this formula")))))

(defun rb-formulas-msg (formulas fns c l env wrld)
  (cond ((endp formulas) nil)
        (t (or (rb-formula-msg (car formulas) fns c l env wrld)
               (rb-formulas-msg (cdr formulas) fns c l env wrld)))))

; ACL2 holds a known constraint L as the conjuncts of the formulas of the
; events that make it (its function FLATTEN-ANDS-IN-LIT), each conjunct
; once.  So the conjuncts of each formula of the line, taken as it stands
; or with its guard holders removed, are members of L, and together they
; are all of L.  RB-CONJUNCTS gives those that are members of L, or :NONE.

(defun rb-conjuncts (term l wrld)
  (let ((a (flatten-ands-in-lit term))
        (b (flatten-ands-in-lit (remove-guard-holders term wrld))))
    (cond ((subsetp-equal a l) (if (subsetp-equal b l) (append a b) a))
          ((subsetp-equal b l) b)
          (t :none))))

(defun rb-cover-msg (formulas l wrld acc)
  (cond ((endp formulas)
         (if (subsetp-equal l acc)
             nil
           "the formulas of the line do not give every conjunct of the constraint that ACL2 holds"))
        (t (let ((c (rb-conjuncts (cadr (car formulas)) l wrld)))
             (if (eq c :none)
                 (rb-msg (car (car formulas))
                         "has a conjunct that is not in the constraint that ACL2 holds")
               (rb-cover-msg (cdr formulas) l wrld (append c acc)))))))

; A function (F N) of a constraint, before what it shares is compared.

(defun rb-constrained-fn-msg (pair env wrld)
  (let* ((f (car pair))
         (range (rb-range-msg f env wrld)))
    (cond ((not (rb-function-p f wrld)) (rb-msg f "is not a function"))
          ((rb-program-p f wrld) (rb-msg f "is in program mode"))
          (range range)
          ((not (eql (cadr pair) (len (getpropc f 'formals nil wrld))))
           (rb-msg f "has another number of formals"))
          (t nil))))

(defun rb-constrained-fns-msg (pairs env wrld)
  (cond ((endp pairs) nil)
        (t (or (rb-constrained-fn-msg (car pairs) env wrld)
               (rb-constrained-fns-msg (cdr pairs) env wrld)))))

(defun rb-sharing-msg (fns c wrld)
  (cond ((endp fns) nil)
        ((eq (rb-constrainer (car fns) wrld) c)
         (rb-sharing-msg (cdr fns) c wrld))
        (t (rb-msg (car fns) "does not share the constraint of the first function"))))

(defun rb-constrain-msg (pairs formulas env wrld)
  (let* ((fns (strip-cars pairs))
         (c (rb-constrainer (car fns) wrld))
         (sibs (and c (getpropc c 'siblings nil wrld)))
         (l (and c (rb-constraint c wrld))))
    (or (rb-constrained-fns-msg pairs env wrld)
        (and (null c) (rb-msg (car fns) "is not constrained"))
        (rb-sharing-msg (cdr fns) c wrld)
        (and (not (no-duplicatesp-eq fns))
             "a function stands twice on the line")
        (and sibs (not (rb-set-equal fns sibs))
             "the functions of the line are not those that share the constraint")
        (and (not (unknown-constraints-p l))
             (rb-cover-msg formulas l wrld nil))
        (and (not (no-duplicatesp-eq (strip-cars formulas)))
             "a formula name stands twice on the line")
        (rb-formulas-msg formulas fns c l env wrld))))

; The axiom of (choose F BOUND FREE BODY FREE2), as spec/logic.md,
; section 6, builds it.

(defun rb-mv-nths (call i k)
  (if (<= k i)
      nil
    (cons (list 'mv-nth (list 'quote i) call)
          (rb-mv-nths call (+ i 1) k))))

(defun rb-choice-axiom (f bound free body free2)
  (let* ((call (cons f free))
         (s (if (cdr bound) (rb-mv-nths call 0 (len bound)) (list call)))
         (body/s (subcor-var bound s body))
         (basic (if (cdr bound)
                    (list 'if (list 'true-listp call)
                          (list 'implies body body/s)
                          ''nil)
                  (list 'implies body body/s))))
    (if (null free2)
        basic
      (let* ((call2 (cons f free2))
             (s2 (if (cdr bound) (rb-mv-nths call2 0 (len bound)) (list call2)))
             (body2 (subcor-var free free2 body))
             (d1 (list 'equal call call2))
             (d2 (list 'if body/s (list 'not (subcor-var bound s body2)) ''nil))
             (d3 (list 'if (subcor-var bound s2 body2)
                       (list 'not (subcor-var bound s2 body))
                       ''nil)))
        (list 'if basic (list 'if d1 d1 (list 'if d2 d2 d3)) ''nil)))))

; A term with every lambda application replaced by its body, with the
; actuals put for the formals.

(mutual-recursion

 (defun rb-beta (term)
   (cond ((variablep term) term)
         ((fquotep term) term)
         ((flambdap (ffn-symb term))
          (rb-beta (subcor-var (lambda-formals (ffn-symb term))
                               (rb-beta-list (fargs term))
                               (lambda-body (ffn-symb term)))))
         (t (cons (ffn-symb term) (rb-beta-list (fargs term))))))

 (defun rb-beta-list (terms)
   (if (endp terms)
       nil
     (cons (rb-beta (car terms)) (rb-beta-list (cdr terms))))))

(defun rb-all-variables-p (vars)
  (or (endp vars)
      (and (legal-variablep (car vars))
           (rb-all-variables-p (cdr vars)))))

(defun rb-variables-p (vars)
  (and (rb-all-variables-p vars) (no-duplicatesp-eq vars)))

(defun rb-choose-msg (f bound free body free2 env wrld)
  (let ((axiom (getpropc f 'defchoose-axiom nil wrld))
        (range (rb-range-msg f env wrld)))
    (cond ((not (rb-function-p f wrld)) (rb-msg f "is not a function"))
          ((null axiom) (rb-msg f "has no axiom of choice"))
          ((rb-program-p f wrld) (rb-msg f "is in program mode"))
          (range range)
          ((rb-constrained-p f wrld)
           (rb-msg f "is constrained"))
          ((not (equal free (getpropc f 'formals nil wrld)))
           (rb-msg f "has other formals"))
          ((not (and (rb-variables-p bound)
                     (rb-variables-p free)
                     (not (intersectp-eq bound free))))
           "the bound and the free variables are not distinct variables")
          ((not (and (termp body wrld)
                     (subsetp-eq (all-vars body) (append bound free))))
           "the body is not a term whose variables are bound or free")
          ((not (or (null free2)
                    (and (rb-variables-p free2)
                         (= (len free2) (len free))
                         (not (intersectp-eq free2 (append bound free))))))
           "the second free variables are not distinct new variables, one for each free variable")
          ((not (equal (rb-beta axiom)
                       (rb-beta (rb-choice-axiom f bound free body free2))))
           (rb-msg f "has another axiom than the one built from the line"))
          (t nil))))

(defun rb-theorem-msg (name term type env wrld)
  (let ((range (rb-range-msg name env wrld)))
    (cond (range range)
          ((not (eq (rb-event-type name env) type))
           (rb-msg name (if (eq type 'defthm)
                            "was not introduced by a DEFTHM event"
                          "was not introduced by a DEFAXIOM event")))
          ((not (equal term (getpropc name 'theorem nil wrld)))
           (rb-msg name "has another formula"))
          (t nil))))

(defun rb-reserve-msg (name env wrld)
  (let ((range (rb-range-msg name env wrld)))
    (cond (range range)
          ((not (rb-reserve-kind-p name wrld))
           (rb-msg name "is not a macro, a constant, a label, a theory or a single-threaded object"))
          ((rb-function-p name wrld) (rb-msg name "is a function"))
          ((rb-has name 'theorem wrld) (rb-msg name "is a theorem"))
          (t nil))))

; A package line: a DEFPKG event of the range declares the package.  An
; open package is not hidden in the world, and the axiom that ACL2 keeps
; under the name NAME-PACKAGE gives its imports.  A hidden package was left
; hidden, with these imports, by a DEFPKG event of the range.

(defun rb-package-why (name imports hidden env wrld)
  (let ((entry (find-package-entry name (global-val 'known-package-alist wrld)))
        (rule (intern-in-package-of-symbol (concatenate 'string name "-PACKAGE")
                                           'acl2::x)))
    (cond ((null entry) " is not known to ACL2")
          ((not (assoc-equal name (rb-packages env)))
           " is not declared by a DEFPKG event of the range")
          (hidden (if (member-equal (list name t imports) (rb-packages env))
                      nil
                    " was not left hidden with these imports by a DEFPKG event of the range"))
          ((package-entry-hidden-p entry) " is hidden")
          ((not (equal (getpropc rule 'theorem nil wrld)
                       (list 'equal
                             (list 'pkg-imports (list 'quote name))
                             (list 'quote imports))))
           " has another axiom of its imports")
          (t nil))))

(defun rb-package-msg (name imports hidden env wrld)
  (let ((why (rb-package-why name imports hidden env wrld)))
    (and why (concatenate 'string "the package " name why))))

; The shapes of the data of each kind of line, spec/formats.md, section 4.

(defun rb-defs-shape-p (defs)
  (if (atom defs)
      (null defs)
    (and (true-listp (car defs))
         (= (len (car defs)) 3)
         (symbolp (car (car defs)))
         (symbol-listp (cadr (car defs)))
         (rb-defs-shape-p (cdr defs)))))

(defun rb-define-shape-p (data)
  (and (consp (cdr data))
       (or (eq (car data) :all) (symbol-listp (car data)))
       (rb-defs-shape-p (cdr data))))

(defun rb-pairs-shape-p (x natp-second)
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (= (len (car x)) 2)
         (symbolp (car (car x)))
         (or (not natp-second) (natp (cadr (car x))))
         (rb-pairs-shape-p (cdr x) natp-second))))

; Checks a line of the statements.  Returns (mv msg intros): MSG is NIL
; if the line is confirmed, and INTROS is the names that it introduces,
; when its data have the shape of its kind.

(defun rb-check-statement (word data env wrld)
  (cond
   ((member-equal word '("package" "hidden-package"))
    (if (and (= (len data) 2) (stringp (car data)) (symbol-listp (cadr data)))
        (mv (rb-package-msg (car data) (cadr data)
                            (equal word "hidden-package") env wrld)
            (list (if (equal word "hidden-package")
                      (cons :hidden (car data))
                    (car data))))
      (mv "the data are not those of a package line" nil)))
   ((equal word "define")
    (if (rb-define-shape-p data)
        (let ((fns (strip-cars (cdr data))))
          (mv (or (rb-defs-msg (cdr data) (car data) :logic nil env wrld)
                  (rb-clique-msg fns wrld))
              fns))
      (mv "the data are not those of a define line" nil)))
   ((equal word "constrain")
    (if (and (= (len data) 2)
             (consp (car data))
             (rb-pairs-shape-p (car data) t)
             (rb-pairs-shape-p (cadr data) nil))
        (mv (rb-constrain-msg (car data) (cadr data) env wrld)
            (append (strip-cars (car data)) (strip-cars (cadr data))))
      (mv "the data are not those of a constrain line" nil)))
   ((equal word "choose")
    (if (and (= (len data) 5)
             (symbolp (nth 0 data))
             (consp (nth 1 data))
             (symbol-listp (nth 1 data))
             (symbol-listp (nth 2 data))
             (symbol-listp (nth 4 data)))
        (mv (rb-choose-msg (nth 0 data) (nth 1 data) (nth 2 data) (nth 3 data)
                           (nth 4 data) env wrld)
            (list (nth 0 data)))
      (mv "the data are not those of a choose line" nil)))
   ((member-equal word '("theorem" "axiom"))
    (if (and (= (len data) 2) (symbolp (car data)))
        (mv (rb-theorem-msg (car data) (cadr data)
                            (if (equal word "theorem") 'defthm 'defaxiom)
                            env wrld)
            (list (car data)))
      (mv "the data are not those of a theorem or an axiom line" nil)))
   ((equal word "reserve")
    (if (and (= (len data) 1) (symbolp (car data)))
        (mv (rb-reserve-msg (car data) env wrld) (list (car data)))
      (mv "the data are not those of a reserve line" nil)))
   (t (mv "the word may not stand in the statements" nil))))

;;; 5. The program text

(defun rb-all-program-p (fns wrld)
  (or (endp fns)
      (and (rb-program-p (car fns) wrld)
           (rb-all-program-p (cdr fns) wrld))))

(defun rb-check-program (word data env wrld)
  (cond
   ((equal word "define")
    (if (rb-define-shape-p data)
        (let ((fns (strip-cars (cdr data))))
          (or (and (intersectp-eq fns '(hard-error throw-nonexec-error))
                   "program text holds no definition of HARD-ERROR or THROW-NONEXEC-ERROR")
              (rb-defs-msg (cdr data) (car data)
                           (if (rb-all-program-p fns wrld) :program :logic)
                           (eq (rb-kind env) :library)
                           env wrld)
              (rb-clique-msg fns wrld)))
      "the data are not those of a define line"))
   ((equal word "attach")
    (if (and (= (len data) 2) (symbolp (car data)) (symbolp (cadr data)))
        (if (equal (attachment-pair (car data) wrld)
                   (cons (car data) (cadr data)))
            nil
          (rb-msg (car data) "does not have this attachment"))
      "the data are not those of an attach line"))
   (t "the word may not stand in program text")))

;;; 6. The files

; ITAB maps each name that a line of the statements introduces, the name
; NAME of each package that a package line declares, and (:HIDDEN . NAME)
; for each that a hidden-package line declares, to (TOTAL . CONFIRMED): the
; number of lines that introduce it, and how many of those are confirmed.

(defun rb-note-intros (keys ok itab)
  (if (endp keys)
      itab
    (let ((old (or (cdr (hons-get (car keys) itab)) '(0 . 0))))
      (rb-note-intros (cdr keys) ok
                      (hons-acons (car keys)
                                  (cons (+ 1 (car old))
                                        (+ (if ok 1 0) (cdr old)))
                                  itab)))))

; Checks the lines of S from position I on; LINENO is the number of the
; line at I.  COUNT and OK count the lines and the confirmed lines, and BAD
; holds (N . WHY) for the first 50 lines not confirmed, in reverse order.

(defun rb-lines (s i len lineno file env pkgs wrld count ok bad itab)
  (if (<= len i)
      (mv count ok (reverse bad) itab)
    (mv-let (n printable)
      (rb-line-end s i len t)
      (mv-let (msg intros)
        (cond ((= n len) (mv "the line does not end with a line feed" nil))
              ((not printable)
               (mv "the line has a character whose code is not from 32 to 126" nil))
              (t (mv-let (err word data)
                   (rb-read-line s i n pkgs)
                   (cond (err (mv err nil))
                         ((eq file :statements)
                          (rb-check-statement word data env wrld))
                         (t (mv (rb-check-program word data env wrld) nil))))))
        (rb-lines s (+ n 1) len (+ lineno 1) file env pkgs wrld
                  (+ count 1)
                  (if msg ok (+ ok 1))
                  (if (and msg (< (len bad) 50)) (cons (cons lineno msg) bad) bad)
                  (rb-note-intros intros (not msg) itab))))))

; Returns (mv count ok bad itab) for the file NAME.  COUNT is NIL if the
; file cannot be read.

(defun rb-check-file (name file env pkgs itab state)
  (let ((s (read-file-into-string name)))
    (if (null s)
        (mv nil 0 (list (cons 0 (concatenate 'string "cannot read " name))) itab)
      (rb-lines s 0 (length s) 1 file env pkgs (w state) 0 0 nil itab))))

;;; 7. Completeness

; The names that the events of the range introduce, with the type of the
; event: each name in the NAMEX of an event tuple whose number is the
; name's ABSOLUTE-EVENT-NUMBER, which ACL2 sets to the number of the last
; event that introduced the name (its function STORE-ABSOLUTE-EVENT-NUMBER).
; Returns (mv types packages).

(defun rb-namex-list (namex)
  (cond ((eql namex 0) nil)
        ((atom namex) (list namex))
        (t namex)))

(defun rb-add-types (names type n wrld tab)
  (cond ((endp names) tab)
        ((and (symbolp (car names))
              (eql (getpropc (car names) 'absolute-event-number nil wrld) n))
         (rb-add-types (cdr names) type n wrld (hons-acons (car names) type tab)))
        (t (rb-add-types (cdr names) type n wrld tab))))

; The state of each package that a DEFPKG event declares, as the event
; left it: (NAME HIDDEN IMPORTS).  A package that a book brings in hidden
; may be declared openly by a later event, so a hidden-package line is
; compared with the list of known packages just after its event.  TAIL is
; the world as it stood just after that event.

(defun rb-package-states (names tail acc)
  (cond ((endp names) acc)
        ((stringp (car names))
         (let ((entry (find-package-entry (car names)
                                          (global-val 'known-package-alist tail))))
           (rb-package-states (cdr names) tail
                              (cons (list (car names)
                                          (and entry (package-entry-hidden-p entry) t)
                                          (and entry (package-entry-imports entry)))
                                    acc))))
        (t (rb-package-states (cdr names) tail acc))))

; TAIL runs through the world WRLD, from its last event back.

(defun rb-range-events (tail lo hi wrld tab pkgs)
  (cond ((endp tail) (mv tab pkgs))
        ((and (eq (car (car tail)) 'event-landmark)
              (eq (cadr (car tail)) 'global-value))
         (let* ((ev (cddr (car tail)))
                (n (access-event-tuple-number ev)))
           (cond ((not (integerp n)) (rb-range-events (cdr tail) lo hi wrld tab pkgs))
                 ((<= n lo) (mv tab pkgs))
                 ((< hi n) (rb-range-events (cdr tail) lo hi wrld tab pkgs))
                 (t (let ((type (access-event-tuple-type ev))
                          (names (rb-namex-list (access-event-tuple-namex ev))))
                      (rb-range-events (cdr tail) lo hi wrld
                                       (rb-add-types names type n wrld tab)
                                       (if (eq type 'defpkg)
                                           (rb-package-states names tail pkgs)
                                         pkgs)))))))
        (t (rb-range-events (cdr tail) lo hi wrld tab pkgs))))

; (N . M) counted once more, and N once more if HIT.

(defun rb-tally (pair hit)
  (cons (+ (car pair) (if hit 1 0)) (+ 1 (cdr pair))))

(defun rb-once-p (key itab)
  (equal (cdr (hons-get key itab)) '(1 . 1)))

; Walks the alist TYPES and returns (mv fns thms names seen): the tallies
; of the functions in logic mode, the theorems and axioms, and the
; reserved names of the range.

(defun rb-complete (types env itab wrld fns thms names seen)
  (if (endp types)
      (mv fns thms names seen)
    (let ((name (car (car types)))
          (type (cdr (car types))))
      (cond
       ((or (hons-get name seen)
            (and (eq (rb-kind env) :library) (rb-ground-name-p name env)))
        (rb-complete (cdr types) env itab wrld fns thms names seen))
       ((and (rb-function-p name wrld) (not (rb-program-p name wrld)))
        (rb-complete (cdr types) env itab wrld
                     (rb-tally fns (rb-once-p name itab)) thms names
                     (hons-acons name t seen)))
       ((and (member-eq type '(defthm defaxiom)) (rb-has name 'theorem wrld))
        (rb-complete (cdr types) env itab wrld
                     fns (rb-tally thms (rb-once-p name itab)) names
                     (hons-acons name t seen)))
       ((and (rb-reserve-kind-p name wrld)
             (not (rb-function-p name wrld))
             (not (rb-has name 'theorem wrld)))
        (rb-complete (cdr types) env itab wrld
                     fns thms (rb-tally names (rb-once-p name itab))
                     (hons-acons name t seen)))
       (t (rb-complete (cdr types) env itab wrld fns thms names seen))))))

; The tally of the DEFPKG events of the range, each with the state (NAME
; HIDDEN IMPORTS) in which it left its package.  The library leaves the
; packages of the ground theory out.

(defun rb-complete-packages (states kind itab tally)
  (cond ((endp states) tally)
        ((and (eq kind :library)
              (member-equal (car (car states))
                            '("COMMON-LISP" "KEYWORD" "ACL2"
                              "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL")))
         (rb-complete-packages (cdr states) kind itab tally))
        (t (rb-complete-packages
            (cdr states) kind itab
            (rb-tally tally (rb-once-p (if (cadr (car states))
                                           (cons :hidden (car (car states)))
                                         (car (car states)))
                                       itab))))))

;;; 8. Writing the results

; A line of the format whose data are strings and natural numbers.  ACC
; holds characters in reverse order.

(defun rb-hex-chars (k)
  (list (char "0123456789ABCDEF" (floor k 16))
        (char "0123456789ABCDEF" (mod k 16))))

(defun rb-string-chars (chars acc)
  (cond ((endp chars) acc)
        (t (let ((k (char-code (car chars))))
             (rb-string-chars
              (cdr chars)
              (if (and (<= 32 k) (<= k 126) (not (eql k 34)) (not (eql k 92)))
                  (cons (car chars) acc)
                (revappend (cons #\\ (rb-hex-chars k)) acc)))))))

(defun rb-args-chars (args acc)
  (cond ((endp args) acc)
        ((stringp (car args))
         (rb-args-chars (cdr args)
                        (cons #\" (rb-string-chars (coerce (car args) 'list)
                                                   (list* #\" #\Space acc)))))
        (t (rb-args-chars (cdr args)
                          (revappend (explode-nonnegative-integer (car args) 10 nil)
                                     (cons #\Space acc))))))

(defun rb-text-line (word args)
  (coerce (reverse (cons #\) (rb-args-chars args
                                            (revappend (coerce word 'list)
                                                       (list #\()))))
          'string))

(defun rb-mismatch-lines (file bad)
  (if (endp bad)
      nil
    (cons (rb-text-line "mismatch" (list file (car (car bad)) (cdr (car bad))))
          (rb-mismatch-lines file (cdr bad)))))

(defun rb-write-lines (lines chan state)
  (if (endp lines)
      state
    (pprogn (princ$ (car lines) chan state)
            (newline chan state)
            (rb-write-lines (cdr lines) chan state))))

(defun rb-write-file (name lines state)
  (mv-let (chan state)
    (open-output-channel name :character state)
    (if (null chan)
        (prog2$ (er hard? 'rb-readback "Cannot write ~x0." name) state)
      (pprogn (rb-write-lines lines chan state)
              (close-output-channel chan state)))))

;;; 9. The check

; For the library: of the functions to which an attachment is attached in
; the world, those for which the program text has an attach line (each
; such line is itself checked above).

(defun rb-attached (tail wrld seen acc)
  (cond ((endp tail) (prog2$ (fast-alist-free seen) acc))
        ((and (eq (cadar tail) 'formals)
              (not (hons-get (caar tail) seen)))
         (rb-attached (cdr tail) wrld (hons-acons (caar tail) t seen)
                      (if (attachment-pair (caar tail) wrld)
                          (cons (caar tail) acc)
                        acc)))
        (t (rb-attached (cdr tail) wrld seen acc))))

(defun rb-count-prefix (s prefix i n count)

; The number of lines of S, from I, that begin with PREFIX.

  (if (<= n i)
      count
    (let ((j (search (coerce (list #\Newline) 'string) s :start2 i)))
      (rb-count-prefix s prefix (if j (+ j 1) n) n
                       (if (and (<= (+ i (length prefix)) n)
                                (equal (subseq s i (+ i (length prefix))) prefix))
                           (+ count 1)
                         count)))))

; ACL2 reads a file into a string only once at one value of its file
; clock, so the clock is moved on before the program text is read again.

(defun rb-attach-complete (prefix state)
  (let ((state (increment-file-clock state)))
    (let ((s (read-file-into-string (concatenate 'string prefix ".program"))))
      (mv (list (if (stringp s) (rb-count-prefix s "(attach " 0 (length s) 0) 0)
                (len (rb-attached (w state) (w state) nil nil)))
          state))))

; The lines of a file that are not confirmed; a file that cannot be read
; counts as one.

(defun rb-missed (count ok)
  (if count (- count ok) 1))

(defun rb-readback (prefix kind lo hi ground-fns state)
  (let* ((wrld (w state))
         (pkgs (rb-witnesses (global-val 'known-package-alist wrld))))
    (mv-let (types packages)
      (rb-range-events wrld lo hi wrld nil nil)
      (let ((env (list kind lo hi ground-fns types packages)))
        (mv-let (s-count s-ok s-bad itab)
          (rb-check-file (concatenate 'string prefix ".statements")
                         :statements env pkgs nil state)
          (mv-let (p-count p-ok p-bad itab)
            (rb-check-file (concatenate 'string prefix ".program")
                           :program env pkgs itab state)
            (mv-let (fns thms names seen)
              (rb-complete types env itab wrld '(0 . 0) '(0 . 0) '(0 . 0) nil)
              (mv-let (attached state)
                (if (eq kind :library)
                    (rb-attach-complete prefix state)
                  (mv nil state))
              (let* ((pk (rb-complete-packages packages kind itab '(0 . 0)))
                     (lines
                      (append
                       (list (rb-text-line "readback"
                                           (list "statements" (or s-count 0) s-ok))
                             (rb-text-line "readback"
                                           (list "program" (or p-count 0) p-ok)))
                       (rb-mismatch-lines "statements" s-bad)
                       (rb-mismatch-lines "program" p-bad)
                       (list
                        (rb-text-line "complete" (list "functions in logic mode"
                                                       (car fns) (cdr fns)))
                        (rb-text-line "complete" (list "theorems and axioms"
                                                       (car thms) (cdr thms)))
                        (rb-text-line "complete" (list "package declarations"
                                                       (car pk) (cdr pk)))
                        (rb-text-line "complete" (list "reserved names"
                                                       (car names) (cdr names))))
                       (if (eq kind :library)
                           (list (rb-text-line "complete"
                                               (cons "attachments in force"
                                                     attached)))
                         nil))))
                (prog2$
                 (progn$ (fast-alist-free types)
                         (fast-alist-free itab)
                         (fast-alist-free seen))
                 (pprogn
                  (rb-write-file (concatenate 'string prefix ".readback") lines state)
                  (value (list s-ok (+ (rb-missed s-count s-ok)
                                       (rb-missed p-count p-ok)))))))))))))))
