(in-package "ACL2")

(set-verify-guards-eagerness 0)

; The symbol facts of spec/ground.txt comprise the 80 symbol-named
; clauses and the rules of the four packages that give an axiom.

(defconst *structure-ground-axioms*
  '(car-cdr-elim car-cons cdr-cons cons-equal nonnegative-product closure
    associativity-of-+ commutativity-of-+ unicity-of-0 inverse-of-+
    associativity-of-* commutativity-of-* unicity-of-1 inverse-of-*
    distributivity <-on-others zero trichotomy positive rational-implies1
    rational-implies2 integer-implies-rational complex-implies1
    complex-definition nonzero-imagpart realpart-imagpart-elim
    realpart-complex imagpart-complex integer-0 integer-1 integer-step
    lowest-terms booleanp-characterp characterp-page characterp-tab
    characterp-rubout characterp-return coerce-inverse-1 coerce-inverse-2
    character-listp-coerce stringp-symbol-package-name
    symbolp-intern-in-package-of-symbol symbolp-pkg-witness
    intern-in-package-of-symbol-symbol-name symbol-name-pkg-witness
    symbol-package-name-pkg-witness-name
    symbol-name-intern-in-package-of-symbol
    symbol-package-name-intern-in-package-of-symbol
    intern-in-package-of-symbol-is-identity symbol-listp-pkg-imports
    no-duplicatesp-eq-pkg-imports completion-of-pkg-imports
    string-is-not-circular nil-is-not-circular char-code-linear
    code-char-type code-char-char-code-is-identity
    char-code-code-char-is-identity completion-of-symbol-name
    completion-of-symbol-package-name completion-of-+ completion-of-*
    completion-of-unary-minus completion-of-unary-/ completion-of-<
    completion-of-car completion-of-cdr completion-of-char-code
    completion-of-code-char completion-of-complex completion-of-coerce
    completion-of-denominator completion-of-imagpart
    completion-of-intern-in-package-of-symbol completion-of-numerator
    completion-of-realpart booleanp-bad-atom<= bad-atom<=-antisymmetric
    bad-atom<=-transitive bad-atom<=-total acl2-package keyword-package
    acl2-input-channel-package acl2-output-channel-package))

(defconst *structure-ground-packages*
  '("COMMON-LISP" "KEYWORD" "ACL2"
    "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL"))

; A statement is represented by (word arguments), as in the interchange
; format.  These definitions use the positions of fields in formats.md,
; section 4, and the effects of a statement in logic.md, section 6.

(defun structure-package-linep (line)
  (member-equal (car line) '("package" "hidden-package")))

(defun structure-package-rule (package)
  (intern-in-package-of-symbol (concatenate 'string package "-PACKAGE")
                               'acl2::x))

(defun structure-definition-signatures (definitions)
  (if (endp definitions)
      nil
    (let ((definition (car definitions)))
      (cons (cons (car definition) (len (cadr definition)))
            (structure-definition-signatures (cdr definitions))))))

(defun structure-declared-signatures (declarations)
  (if (endp declarations)
      nil
    (let ((declaration (car declarations)))
      (cons (cons (car declaration) (cadr declaration))
            (structure-declared-signatures (cdr declarations))))))

(defun structure-signatures (line)
  (let ((word (car line))
        (args (cadr line)))
    (cond ((equal word "define")
           (structure-definition-signatures (cdr args)))
          ((equal word "constrain")
           (structure-declared-signatures (car args)))
          ((equal word "choose")
           (list (cons (car args) (len (caddr args)))))
          (t nil))))

; Package identifiers are strings.  The symbol naming the package axiom is
; in the same namespace as the other symbols that statements introduce.

(defun structure-names (line)
  (let ((word (car line))
        (args (cadr line)))
    (cond ((equal word "package")
           (list (structure-package-rule (car args))))
          ((equal word "constrain")
           (append (strip-cars (car args)) (strip-cars (cadr args))))
          ((member-equal word '("choose" "theorem" "axiom" "reserve"))
           (list (car args)))
          ((equal word "define") (strip-cars (cdr args)))
          (t nil))))

(defun structure-line-supplies-p (name line)
  (if (stringp name)
      (and (structure-package-linep line)
           (equal name (car (cadr line))))
    (if (member-equal name (structure-names line)) t nil)))

(defun structure-lines-supply-p (name lines)
  (and (consp lines)
       (or (structure-line-supplies-p name (car lines))
           (structure-lines-supply-p name (cdr lines)))))

; Only the first occurrence of a line can introduce a name.  An open
; declaration after a hidden one introduces the rule, while the package
; identifier itself has been available since its first declaration.

(defun structure-introduces-p (name line earlier)
  (and (structure-line-supplies-p name line)
       (not (member-equal line earlier))
       (or (not (stringp name))
           (not (structure-lines-supply-p name earlier)))))

(defun structure-introduction-count (name lines earlier)
  (cond ((endp lines) 0)
        ((member-equal (car lines) earlier)
         (structure-introduction-count name (cdr lines) earlier))
        (t (+ (if (structure-introduces-p name (car lines) earlier) 1 0)
              (structure-introduction-count name (cdr lines)
                                            (cons (car lines) earlier))))))

; Count of arguments in a call, at any depth outside quoted data.  The
; body and the actuals of a lambda application may both contain calls.

(mutual-recursion
 (defun structure-calls (term)
   (cond ((atom term) nil)
         ((eq (car term) 'quote) nil)
         ((consp (car term))
          (append (structure-calls (caddar term))
                  (structure-calls-in-list (cdr term))))
         (t (cons (cons (car term) (len (cdr term)))
                  (structure-calls-in-list (cdr term))))))

 (defun structure-calls-in-list (terms)
   (if (endp terms)
       nil
     (append (structure-calls (car terms))
             (structure-calls-in-list (cdr terms))))))

(defun structure-definition-bodies (definitions)
  (if (endp definitions)
      nil
    (cons (caddr (car definitions))
          (structure-definition-bodies (cdr definitions)))))

(defun structure-terms (line)
  (let ((word (car line))
        (args (cadr line)))
    (cond ((equal word "define") (structure-definition-bodies (cdr args)))
          ((equal word "constrain") (strip-cadrs (cadr args)))
          ((equal word "choose") (list (cadddr args)))
          ((member-equal word '("theorem" "axiom")) (list (cadr args)))
          (t nil))))

(defun structure-calls-in-scopep (calls signatures own)
  (or (endp calls)
      (let* ((call (car calls))
             (signature (or (assoc-equal (car call) own)
                            (hons-get (car call) signatures))))
        (and signature
             (equal (cdr call) (cdr signature))
             (structure-calls-in-scopep (cdr calls) signatures own)))))

(defun structure-declared-packages-p (datum packages)
  (cond ((consp datum)
         (and (structure-declared-packages-p (car datum) packages)
              (structure-declared-packages-p (cdr datum) packages)))
        ((symbolp datum) (if (hons-get (symbol-package-name datum) packages) t nil))
        (t t)))

(defun structure-fresh-names-p (new names)
  (or (endp new)
      (and (not (hons-get (car new) names))
           (structure-fresh-names-p (cdr new) names))))

; An ordinary declaration can open a hidden package with the same imports.
; Otherwise the package identifier must be new.

(defun structure-package-newp (line packages)
  (let* ((args (cadr line))
         (old (hons-get (car args) packages)))
    (or (not old)
        (and (equal (car line) "package")
             (equal (cdr old) (cons :hidden (cadr args)))))))

; The package inventory records declarations under package strings.
; A pair (package . symbol-name) records an imported name.  A symbol on
; a line needs its own package and cannot have a name it imports.

(defun structure-unshadowed-symbols-p (datum packages)
  (cond ((consp datum)
         (and (structure-unshadowed-symbols-p (car datum) packages)
              (structure-unshadowed-symbols-p (cdr datum) packages)))
        ((symbolp datum)
         (not (hons-get (cons (symbol-package-name datum) (symbol-name datum))
                        packages)))
        (t t)))

; A define or constrain supplies its own signatures while its terms are
; checked.  Choice checks its body with the preceding signatures.

(defun structure-line-orderp (line signatures names packages)
  (let ((new (structure-names line))
        (args (cadr line)))
    (and (structure-declared-packages-p args packages)
         (structure-unshadowed-symbols-p args packages)
         (structure-fresh-names-p new names)
         (no-duplicatesp-equal new)
         (if (structure-package-linep line)
             (structure-package-newp line packages)
           (structure-calls-in-scopep
            (structure-calls-in-list (structure-terms line))
            signatures
            (if (equal (car line) "choose")
                nil
              (structure-signatures line)))))))

(defun structure-record-signatures (new signatures)
  (if (endp new)
      signatures
    (structure-record-signatures (cdr new)
                                 (hons-acons (caar new) (cdar new) signatures))))

(defun structure-record-names (new names)
  (if (endp new)
      names
    (structure-record-names (cdr new) (hons-acons (car new) t names))))

(defun structure-record-imports (package imports packages)
  (if (endp imports)
      packages
    (structure-record-imports
     package (cdr imports)
     (hons-acons (cons package (symbol-name (car imports))) t packages))))

(defun structure-record-package (line packages)
  (if (structure-package-linep line)
      (let ((args (cadr line)))
        (hons-acons (car args)
                    (if (equal (car line) "hidden-package")
                        (cons :hidden (cadr args))
                      t)
                    (structure-record-imports (car args) (cadr args) packages)))
    packages))

; A valid prefix can only repeat a package line or open a hidden package
; with the same imports.  Collecting each declaration's imports therefore
; gives exactly the imported names before the first failure.  The scan
; retains declarations after errors so it can report later violations.

(defun structure-order-scan (lines signatures names packages earlier)
  (cond ((endp lines) (mv nil signatures names packages earlier))
        ((member-equal (car lines) earlier)
         (structure-order-scan (cdr lines) signatures names packages earlier))
        (t
         (let* ((line (car lines))
                (ordered (structure-line-orderp line signatures names packages)))
           (mv-let (failures signatures1 names1 packages1 earlier1)
             (structure-order-scan
              (cdr lines)
              (structure-record-signatures (structure-signatures line) signatures)
              (structure-record-names (structure-names line) names)
              (structure-record-package line packages)
              (cons line earlier))
             (mv (if ordered failures (cons line failures))
                 signatures1 names1 packages1 earlier1))))))

(defun structure-orderp (lines signatures names packages)
  (mv-let (failures signatures1 names1 packages1 earlier)
    (structure-order-scan lines signatures names packages nil)
    (declare (ignore signatures1 names1 packages1 earlier))
    (not failures)))
