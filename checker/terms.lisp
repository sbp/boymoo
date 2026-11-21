; Boymoo, the checker: the world, symbols, variables and terms
; (spec/language.md, sections 2, 5 and 6), substitution and sizes
; (spec/formats.md, section 8).

(in-package "BOYMOO")

(include-book "read")

; ---------------------------------------------------------------------------
; The world: what the checker holds at a line.
;
;   PKGS      the table of packages (read.lisp);
;   NAMES     a trie from the text of each name in use to its entry;
;   SFACTS    an association list from the string names of the facts of the
;             ground theory to the facts;
;   SPECIALS  a trie from the text of each symbol of the specials line of
;             the ground theory to T;
;   COUNTS    the four counts of a provisional verdict, (S A D F);
;   ACL2      the trie of the imports of the package ACL2, by name.
;
; The entry of a name is (ARITY FACT LINE): ARITY is the number of
; arguments if the name is a function in use, and NIL otherwise; FACT is
; the fact of that name, or NIL; LINE is the line of the library or of the
; statements that introduced the name, or NIL.  A fact, like the conclusion
; of a step, is a clause with the sizes of its literals: (LITS . SIZES).

(defmacro w-pkgs (w) `(car ,w))
(defmacro w-names (w) `(car (cdr ,w)))
(defmacro w-sfacts (w) `(car (cdr (cdr ,w))))
(defmacro w-specials (w) `(car (cdr (cdr (cdr ,w)))))
(defmacro w-counts (w) `(car (cdr (cdr (cdr (cdr ,w))))))
(defmacro w-acl2 (w) `(car (cdr (cdr (cdr (cdr (cdr ,w)))))))

(defun guard-string-facts-p (alist)
  (declare (xargs :guard t))
  (if (consp alist)
      (and (consp (car alist))
           (stringp (car (car alist)))
           (guard-sized-clause-p (cdr (car alist)))
           (guard-string-facts-p (cdr alist)))
    (equal alist nil)))

(defun guard-world-p (w)
  (declare (xargs :guard t))
  (and (true-listp w)
       (equal (len w) 6)
       (guard-trie-p (w-pkgs w) :package)
       (guard-trie-p (w-names w) :name)
       (guard-string-facts-p (w-sfacts w))
       (guard-trie-p (w-specials w) :special)
       (guard-natural-list-p (w-counts w))
       (equal (len (w-counts w)) 4)
       (guard-trie-p (w-acl2 w) :import)))

(defun make-world (pkgs names sfacts specials counts acl2)
  (declare (xargs :guard t))
  (list pkgs names sfacts specials counts acl2))

(defun set-pkgs (v w)
  (declare (xargs :guard (true-listp w)))
  (make-world v (w-names w) (w-sfacts w) (w-specials w) (w-counts w) (w-acl2 w)))

(defun set-names (v w)
  (declare (xargs :guard (true-listp w)))
  (make-world (w-pkgs w) v (w-sfacts w) (w-specials w) (w-counts w) (w-acl2 w)))

(defun set-counts (v w)
  (declare (xargs :guard (true-listp w)))
  (make-world (w-pkgs w) (w-names w) (w-sfacts w) (w-specials w) v (w-acl2 w)))

(defmacro entry-arity (e) `(car ,e))
(defmacro entry-fact (e) `(car (cdr ,e)))
(defmacro entry-line (e) `(car (cdr (cdr ,e))))

(defun name-entry (s w)
  (declare (xargs :guard (and (symbolp s) (true-listp w))))
  (trie-get (sym-text s) (w-names w)))

(defun put-entry (s e w)
  (declare (xargs :guard (and (symbolp s) (true-listp w))))
  (set-names (trie-put (sym-text s) e (w-names w)) w))

; Adds 1 to the count at position I, from 0, of (S A D F).
(defun bump (i counts)
  (declare (xargs :guard (and (natp i) (guard-natural-list-p counts))))
  (if (consp counts)
      (if (zp i)
          (cons (+ 1 (car counts)) (cdr counts))
        (cons (car counts) (bump (+ -1 i) (cdr counts))))
    nil))

(defun count-one (i w)
  (declare (xargs :guard (and (natp i) (true-listp w) (guard-natural-list-p (w-counts w)))))
  (set-counts (bump i (w-counts w)) w))

; The number of arguments of the function F, if it is in use: EXTRA, an
; association list, gives the functions of a line that count as in use
; while the line is tested.
(defun fn-arity (f extra w)
  (declare (xargs :guard (and (symbolp f)
                             (true-listp w)
                             (or (pair-of f extra)
                                 (let ((e (name-entry f w)))
                                   (or (consp e) (equal e nil)))))
                  :verify-guards nil))
  (let ((p (pair-of f extra)))
    (if p
        (cdr p)
      (entry-arity (name-entry f w)))))

; ---------------------------------------------------------------------------
; Symbols

(defconst *keyword-chars* (coerce "KEYWORD" 'list))
(defconst *cl-chars* (coerce "COMMON-LISP" 'list))
(defconst *acl2-chars* (coerce "ACL2" 'list))
(defconst *keyword-prefix* (coerce "KEYWORD::" 'list))
(defconst *cl-prefix* (coerce "COMMON-LISP::" 'list))

; The package name and the name of the symbol S, as characters:
; (PACKAGE . NAME).  The text of a symbol held is always in the format.
(defun sym-parts (s)
  (declare (xargs :guard (symbolp s)
                  :verify-guards nil))
  (let* ((p (lex-part (sym-text s)))
         (rest (cdr (cdr p)))
         (n (lex-part (cdr (cdr rest)))))
    (cons (car p) (car n))))

(defun sym-name (s)
  (declare (xargs :guard (symbolp s)
                  :verify-guards nil))
  (cdr (sym-parts s)))

(defun keyword-sym-p (s)
  (declare (xargs :guard (symbolp s)))
  (prefix-p *keyword-prefix* (sym-text s)))

(defun cl-sym-p (s)
  (declare (xargs :guard (symbolp s)))
  (prefix-p *cl-prefix* (sym-text s)))

(defun hex-char (d)
  (declare (xargs :guard (and (natp d) (< d 16))))
  (code-char (if (< d 10) (+ 48 d) (+ 55 d))))

; The number of sixteens in N, which is below 256.
(defun sixteens (n h)
  (declare (xargs :guard t
                  :measure (nfix (- 15 (nfix h)))))
  (if (and (natp h) (< h 15) (integerp n) (not (< n 16)))
      (sixteens (- n 16) (+ 1 h))
    h))

; The characters CS written as between bars, reversed onto ACC.
(defun escape-part (cs acc)
  (declare (xargs :guard (character-listp cs)
                  :verify-guards nil))
  (if (consp cs)
      (let ((n (char-code (car cs))))
        (if (and (< 31 n) (< n 127) (not (equal n 124)) (not (equal n 92)))
            (escape-part (cdr cs) (cons (car cs) acc))
          (let ((h (sixteens n 0)))
            (escape-part (cdr cs)
                         (cons (hex-char (- n (* 16 h)))
                               (cons (hex-char h) (cons #\\ acc)))))))
    acc))

; The text of a part of a symbol (spec/formats.md, section 2).
(defun part-text (cs)
  (declare (xargs :guard (character-listp cs)
                  :verify-guards nil))
  (if (and (consp cs) (all-plain-p cs))
      cs
    (cons #\| (rev-onto (escape-part cs nil) (list #\|)))))

; The symbol whose package name is PKG and whose name is NAME, as
; characters.
(defun make-sym (pkg name)
  (declare (xargs :guard (and (character-listp pkg) (character-listp name))
                  :verify-guards nil))
  (text-symbol (app (part-text pkg) (cons #\: (cons #\: (part-text name))))))

; What (intern-in-package-of-symbol NAME S) gives for a symbol S whose
; package, named PKG, is declared: the import of that name, if there is
; one, and otherwise the symbol of PKG of that name.
(defun intern-sym (name pkg w)
  (declare (xargs :guard (and (character-listp name) (character-listp pkg)
                             (true-listp w)
                             (let ((rec (trie-get pkg (w-pkgs w))))
                               (and (true-listp rec)
                                    (let ((found (trie-get name (prec-trie rec))))
                                      (or (not found)
                                          (and (consp found) (symbolp (car found))))))))
                  :verify-guards nil))
  (let ((found (trie-get name (prec-trie (trie-get pkg (w-pkgs w))))))
    (if found (car found) (make-sym pkg name))))

; ---------------------------------------------------------------------------
; Variables (spec/language.md, section 5)

(defun variable-p (s w)
  (declare (xargs :guard (and (true-listp w)
                             (or (not (symbolp s))
                                 (let* ((parts (sym-parts s))
                                        (found (trie-get (cdr parts) (w-acl2 w))))
                                   (or (not (equal (car parts) *cl-chars*))
                                       (consp found)
                                       (equal found nil)))))
                  :verify-guards nil))
  (if (and (symbolp s) s (not (equal s t)))
      (let* ((parts (sym-parts s))
             (pkg (car parts))
             (name (cdr parts)))
        (if (equal pkg *keyword-chars*)
            nil
          (if (and (consp name) (equal (car name) #\*)
                   (equal (last-elem name) #\*))
              nil
            (if (and (consp name) (equal (car name) #\&))
                nil
              (if (equal pkg *cl-chars*)
                  (and (equal (car (trie-get name (w-acl2 w))) s)
                       (not (trie-get (sym-text s) (w-specials w))))
                t)))))
    nil))

(defun variable-list-p (l w)
  (declare (xargs :guard (guard-world-p w)
                  :verify-guards nil))
  (if (consp l)
      (and (variable-p (car l) w) (variable-list-p (cdr l) w))
    (equal l nil)))

; ---------------------------------------------------------------------------
; Terms
;
; VARS is the list of the variables that may occur, or :ANY.

(mutual-recursion
 (defun term-p (x vars extra w)
   (declare (xargs :guard (guard-world-p w)
                   :verify-guards nil
                   :measure (acl2-count x)))
   (if (consp x)
       (let ((f (car x)))
         (if (symbolp f)
             (if (equal f '|COMMON-LISP::QUOTE|)
                 (and (consp (cdr x)) (equal (cdr (cdr x)) nil))
               (let ((n (fn-arity f extra w)))
                 (and n
                      (equal (len (cdr x)) n)
                      (terms-p (cdr x) vars extra w))))
           (and (consp f)
                (equal (car f) '|COMMON-LISP::LAMBDA|)
                (consp (cdr f))
                (consp (cdr (cdr f)))
                (equal (cdr (cdr (cdr f))) nil)
                (variable-list-p (car (cdr f)) w)
                (distinct-p (car (cdr f)))
                (term-p (car (cdr (cdr f))) (car (cdr f)) extra w)
                (equal (len (cdr x)) (len (car (cdr f))))
                (terms-p (cdr x) vars extra w))))
     (and (variable-p x w)
          (if (equal vars :any) t (member-p x vars)))))
 (defun terms-p (xs vars extra w)
   (declare (xargs :guard (guard-world-p w)
                   :verify-guards nil
                   :measure (acl2-count xs)))
   (if (consp xs)
       (and (term-p (car xs) vars extra w)
            (terms-p (cdr xs) vars extra w))
     (equal xs nil))))

; (return-last 'mbe1-raw a b): an mbe, whose executable half is A.
(defun mbe-p (x)
  (declare (xargs :guard (or (consp x) (equal x nil))))
  (and (equal (car x) '|ACL2::RETURN-LAST|)
       (consp (cdr x))
       (equal (car (cdr x)) '(|COMMON-LISP::QUOTE| |ACL2::MBE1-RAW|))))

; The term X calls one of the functions FNS, at any depth outside a
; constant and outside the executable half of an mbe.  So ACL2 decides that
; a definition is recursive: a call in the executable half of an mbe alone
; does not make it so.
(mutual-recursion
 (defun calls-p (x fns)
   (declare (xargs :guard t
                   :verify-guards nil
                   :measure (acl2-count x)))
   (if (consp x)
       (if (equal (car x) '|COMMON-LISP::QUOTE|)
           nil
         (if (consp (car x))
             (if (calls-p (total-car (total-cdr (cdr (car x)))) fns)
                 t
               (calls-list-p (cdr x) fns))
           (if (mbe-p x)
               (calls-p (total-car (total-cdr (cdr (cdr x)))) fns)
             (if (member-p (car x) fns)
                 t
               (calls-list-p (cdr x) fns)))))
     nil))
 (defun calls-list-p (xs fns)
   (declare (xargs :guard t
                   :verify-guards nil
                   :measure (acl2-count xs)))
   (if (consp xs)
       (if (calls-p (car xs) fns) t (calls-list-p (cdr xs) fns))
     nil)))

; The association list of the elements of KEYS with those of VALS.
(defun pair-up (keys vals)
  (declare (xargs :guard t))
  (if (consp keys)
      (cons (cons (car keys) (if (consp vals) (car vals) nil))
            (pair-up (cdr keys) (if (consp vals) (cdr vals) nil)))
    nil))

; ---------------------------------------------------------------------------
; Substitution (spec/language.md, section 5): S is an association list
; from variables to terms.  Nothing inside a constant or the body of a
; lambda, which is closed, is replaced.

(mutual-recursion
 (defun subst-term (x s)
   (declare (xargs :guard t
                   :measure (acl2-count x)))
   (if (consp x)
       (if (equal (car x) '|COMMON-LISP::QUOTE|)
           x
         (cons (car x) (subst-terms (cdr x) s)))
     (let ((p (pair-of x s)))
       (if p (cdr p) x))))
 (defun subst-terms (xs s)
   (declare (xargs :guard t
                   :measure (acl2-count xs)))
   (if (consp xs)
       (cons (subst-term (car xs) s) (subst-terms (cdr xs) s))
     nil)))

; The term X with the name of every call of a function of REN, an
; association list, replaced by the function REN gives for it.
(mutual-recursion
 (defun rename-calls (x ren)
   (declare (xargs :guard t
                   :verify-guards nil
                   :measure (acl2-count x)))
   (if (consp x)
       (if (equal (car x) '|COMMON-LISP::QUOTE|)
           x
         (if (consp (car x))
             (cons (list '|COMMON-LISP::LAMBDA|
                         (total-car (cdr (car x)))
                         (rename-calls (total-car (total-cdr (cdr (car x)))) ren))
                   (rename-list (cdr x) ren))
           (let ((p (pair-of (car x) ren)))
             (cons (if p (cdr p) (car x)) (rename-list (cdr x) ren)))))
     x))
 (defun rename-list (xs ren)
   (declare (xargs :guard t
                   :verify-guards nil
                   :measure (acl2-count xs)))
   (if (consp xs)
       (cons (rename-calls (car xs) ren) (rename-list (cdr xs) ren))
     nil)))

; ---------------------------------------------------------------------------
; Sizes (spec/formats.md, section 8): 1 for an atom, and for a cons 1 more
; than the sizes of its car and its cdr.

(defun size-acc (x acc)
  (declare (xargs :guard (acl2-numberp acc)))
  (if (consp x)
      (size-acc (cdr x) (size-acc (car x) (+ 1 acc)))
    (+ 1 acc)))

(defun size (x)
  (declare (xargs :guard t))
  (size-acc x 0))

(defun sizes (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (size (car xs)) (sizes (cdr xs)))
    nil))

; Pairing formals with actual sizes can leave a NIL value if the list
; of actuals is shorter. Numeric use of such a value follows ACL2's
; completion of addition.
(defun size-bindings-p (ss)
  (declare (xargs :guard t))
  (if (consp ss)
      (and (consp (car ss))
           (size-value-p (cdar ss))
           (size-bindings-p (cdr ss)))
    (equal ss nil)))

; The size of X with a substitution applied, found without building it:
; SS is an association list from variables to the sizes of their terms.
(mutual-recursion
 (defun subst-size (x ss)
   (declare (xargs :guard (size-bindings-p ss)
                   :verify-guards nil
                   :measure (acl2-count x)))
   (if (consp x)
       (if (equal (car x) '|COMMON-LISP::QUOTE|)
           (size x)
         (+ 1 (size (car x)) (args-subst-size (cdr x) ss)))
     (let ((p (pair-of x ss)))
       (if p (cdr p) 1))))
 (defun args-subst-size (xs ss)
   (declare (xargs :guard (size-bindings-p ss)
                   :verify-guards nil
                   :measure (acl2-count xs)))
   (if (consp xs)
       (+ 1 (total-add (subst-size (car xs) ss) (args-subst-size (cdr xs) ss)))
     1)))

(defun subst-sizes (xs ss)
  (declare (xargs :guard (size-bindings-p ss)
                  :verify-guards nil))
  (if (consp xs)
      (cons (subst-size (car xs) ss) (subst-sizes (cdr xs) ss))
    nil))

; The largest sum of the sizes of the conclusions of one proof, and of the
; obligations of termination of one definition: 2 to the power 26.
(defconst *budget* 67108864)
