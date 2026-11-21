; These tests use the package declarations in the ACL2 session's world.

(in-package "ACL2")

(f-put-global 'rt-startup-packages (global-val 'known-package-alist (w state)) state)
(ld "package.lsp" :ld-error-action :error)
(include-book "core"
              :uncertified-okp nil :defaxioms-okp nil :skip-proofs-okp nil :ttags nil)
(include-book "round-trip-native"
              :uncertified-okp nil :defaxioms-okp nil :skip-proofs-okp nil :ttags nil)

; ACL2 records the annotations of the certificates it reads on inclusion.
(defun rt-test-book-annotations (name entries)
  (cond ((endp entries) nil)
        ((equal name (caddr (car entries))) (cadddr (car entries)))
        (t (rt-test-book-annotations name (cdr entries)))))

(defun rt-test-certificates-p (names entries)
  (if (endp names)
      t
    (and (equal (rt-test-book-annotations (car names) entries)
                '((:skipped-proofsp) (:axiomsp) (:ttags)))
         (rt-test-certificates-p (cdr names) entries))))

(assert-event
 (rt-test-certificates-p
  '("canon" "core" "base" "read" "round-trip-text" "round-trip-numbers"
    "round-trip-symbols" "round-trip-atoms" "round-trip" "round-trip-lexical"
    "round-trip-packages" "round-trip-converse" "round-trip-native")
  (global-val 'include-book-alist (w state))))
(value-triple (cw "~%ROUND-TRIP-OK certificates~%"))

(defun rt-test-guards-p (names wrld)
  (if (endp names)
      t
    (and (eq (getpropc (car names) 'symbol-class nil wrld)
             :common-lisp-compliant)
         (rt-test-guards-p (cdr names) wrld))))

(assert-event
 (rt-test-guards-p
  '(bm-hex2 bm-plain-charp bm-all-plain bm-escaped bm-part bm-nat bm-int
    bm-rat bm-obj bm-tail bm-args bm-line)
  (w state)))
(value-triple (cw "~%ROUND-TRIP-OK printer-guards~%"))

; Convert each package declaration to the reader's package record, with
; its imports in reader form and indexed by their names.
(defun rt-test-import-index (imports index)
  (if (consp imports)
      (rt-test-import-index (cdr imports)
                            (boymoo::trie-put
                             (coerce (symbol-name (car imports)) 'list)
                             (list (rt-datum-form (car imports)))
                             index))
    index))

(defun rt-test-package-table (entries)
  (if (consp entries)
      (let* ((entry (car entries))
             (imports (package-entry-imports entry))
             (record (list (rt-datum-form imports)
                           (rt-test-import-index imports nil)
                           (package-entry-hidden-p entry)
                           nil)))
        (boymoo::trie-put (coerce (package-entry-name entry) 'list)
                          record
                          (rt-test-package-table (cdr entries))))
    nil))

(defconst *rt-test-words*
  (list (cons (coerce "theorem" 'list) :theorem)
        (cons (coerce "hidden-package" 'list) :hidden-package)
        (cons (coerce "reserve" 'list) :reserve)))

(defun rt-test-line (word args pkgs)
  (and (rt-word-p word)
       (rt-word-admitted-p word *rt-test-words*)
       (true-listp args)
       (rt-format-datum-p args)
       (or (null args) (rt-declarations-cover-written-symbols-p args pkgs))
       (or (null args) (rt-written-symbols-pass-index-p args pkgs))
       (let* ((text (append (coerce (bm-line word args) 'list) '(#\Newline)))
              (read (boymoo::parse-line text *rt-test-words* pkgs))
              (read-args (cdr read)))
         (and (equal read (cons (cdr (boymoo::pair-of
                                       (coerce word 'list) *rt-test-words*))
                               (rt-datum-form args)))
              (equal (rt-line-word text) word)
              (equal (rt-reader-line-text word read-args) text)
              (rt-reader-list-in-table-p read-args pkgs)
              (rt-native-names-p read-args)
              (equal (rt-native-datum read-args) args)))))

; At startup, check every hypothesis on the native data of a line,
; and check equality and inequality of pairs in the datum domain.
(assert-event
 (let* ((pkgs (rt-test-package-table (@ rt-startup-packages)))
        (empty-name (intern-in-package-of-symbol "" 'len))
        (quoted-name (intern-in-package-of-symbol
                      (coerce (list #\| #\: #\\ (code-char 255)) 'string) 'len))
        (args (list 0 -19 3/7 #C(-1/2 3/7) (code-char 255)
                    (coerce (list #\" #\\ #\Newline (code-char 128)) 'string)
                    (list nil t 'len) (cons 17 quoted-name)
                    empty-name 'car))
        (other (cons 1 (cdr args))))
   (and (not (boymoo::pair-of nil *rt-test-words*))
        (rt-compatible-package-table-p pkgs)
        (rt-test-line "theorem" nil pkgs)
        (rt-test-line "theorem" args pkgs)
        (rt-test-line "hidden-package" (list "EXAMPLE" (list 'len)) pkgs)
        (rt-format-datum-p other)
        (equal (rt-datum-form args) (rt-datum-form (append args nil)))
        (not (equal (rt-datum-form args) (rt-datum-form other)))
        (not (equal (rt-datum-form 'len) (rt-datum-form 'car)))
        (equal (rt-datum-form 'car) 'boymoo::|COMMON-LISP::CAR|)
        (not (rt-declared-symbol-p "ACL2" "CAR" pkgs))
        (not (rt-symbol-passes-index-p "ACL2" "CAR" pkgs))
        (not (rt-declared-symbol-p "" "NIL" pkgs)))))
(value-triple (cw "~%ROUND-TRIP-OK startup-world~%"))

; With no line feed even a valid word and an empty argument list are
; refused. This is the interface between bm-line and the file writer.
(assert-event
 (let ((cs (coerce (bm-line "theorem" nil) 'list)))
   (and (equal (bm-line "theorem" nil) "(theorem)")
        (not (boymoo::parse-line cs *rt-test-words* nil))
        (equal (boymoo::parse-line (append cs '(#\Newline)) *rt-test-words* nil)
               '(:theorem)))))
(value-triple (cw "~%ROUND-TRIP-OK line-feed~%"))

; Empty keys can be supplied to the parser directly. Format words and
; package declarations have nonempty names.
(assert-event
 (let* ((empty-words (list (cons nil :theorem)))
        (empty-pkgs (boymoo::trie-put nil (list nil nil nil nil) nil))
        (empty-word '(#\( #\) #\Newline))
        (empty-package (append (coerce "(theorem ||::X)" 'list) '(#\Newline))))
   (and (not (rt-word-p (rt-line-word empty-word)))
        (equal (boymoo::parse-line empty-word empty-words nil) '(:theorem))
        (equal (boymoo::parse-line empty-package *rt-test-words* empty-pkgs)
               '(:theorem boymoo::|\|\|::X|))
        (not (rt-native-names-p '(boymoo::|\|\|::X|)))
        (not (rt-compatible-package-table-p empty-pkgs)))))
(value-triple (cw "~%ROUND-TRIP-OK empty-table-keys~%"))

(defun rt-test-refuses-lines-p (lines pkgs)
  (if (consp lines)
      (and (not (boymoo::parse-line (append (coerce (car lines) 'list) '(#\Newline))
                                    *rt-test-words* pkgs))
           (rt-test-refuses-lines-p (cdr lines) pkgs))
    t))

(assert-event
 (rt-test-refuses-lines-p
  '("(theorem -0)" "(theorem 01)" "(theorem 2/4)" "(theorem #C(3 0))"
    "(theorem \"\\41\")" "(theorem |ACL2|::LEN)" "(theorem ())"
    "(theorem (1 . COMMON-LISP::NIL))" "(theorem (1 . (2)))" "(theorem  1)")
  (rt-test-package-table (@ rt-startup-packages))))
(value-triple (cw "~%ROUND-TRIP-OK noncanonical-text~%"))

; The ACL2 declaration imports NIL and CAR. The two qualified names
; belong to COMMON-LISP, so both spellings with prefix ACL2 are refused.
(assert-event
 (let* ((pkgs (rt-test-package-table (@ rt-startup-packages)))
        (record (boymoo::trie-get (coerce "ACL2" 'list) pkgs)))
   (and (rt-package-index-of-its-imports-p "ACL2" pkgs)
        (equal (boymoo::trie-get (coerce "NIL" 'list) (boymoo::prec-trie record))
               (list nil))
        (not (rt-declared-symbol-p "ACL2" "NIL" pkgs))
        (not (rt-symbol-passes-index-p "ACL2" "NIL" pkgs))
        (rt-test-refuses-lines-p '("(theorem ACL2::NIL)" "(theorem ACL2::CAR)") pkgs)
        (rt-test-line "theorem" (list :nil nil 'car) pkgs))))
(value-triple (cw "~%ROUND-TRIP-OK acl2-package-imports~%"))

; A declaration in the reader's table can differ from the ACL2 package
; of the same name. This declaration has an empty import index.
(assert-event
 (let* ((pkgs (boymoo::trie-put (coerce "BOYMOO" 'list) (list nil nil nil nil) nil))
        (text (append (coerce "(reserve BOYMOO::CAR)" 'list) '(#\Newline)))
        (read (boymoo::parse-line text *rt-test-words* pkgs)))
   (and (rt-package-index-of-its-imports-p "BOYMOO" pkgs)
        (equal read '(:reserve boymoo::|BOYMOO::CAR|))
        (equal (rt-native-symbol "BOYMOO" "CAR") 'car)
        (not (rt-native-names-p (cdr read)))
        (not (rt-compatible-package-table-p pkgs)))))
(value-triple (cw "~%ROUND-TRIP-OK native-import-conflict~%"))

; These distributed books are listed in export/books.txt.
(include-book "arithmetic/rationals" :dir :system :uncertified-okp nil)
(include-book "std/osets/top" :dir :system :uncertified-okp nil)
(include-book "std/strings/pretty" :dir :system :uncertified-okp nil)

(assert-event
 (let* ((pkgs (rt-test-package-table (global-val 'known-package-alist (w state))))
        (args (list 'set::in (cons 'str::print-atom 'car)
                    (list (intern-in-package-of-symbol "A::B" 'str::print-atom)
                          #C(5/3 -4) #\Space))))
   (and (not (find-package-entry "SET" (@ rt-startup-packages)))
        (not (find-package-entry "STR" (@ rt-startup-packages)))
        (rt-compatible-package-table-p pkgs)
        (rt-test-line "theorem" args pkgs))))
(value-triple (cw "~%ROUND-TRIP-OK world-with-books~%"))

; A record declared by a hidden-package line permits a locally owned
; name but excludes the names it imports.
(assert-event
 (let* ((package (coerce "BM-HIDDEN" 'list))
        (imports (list 'boymoo::|COMMON-LISP::CAR|))
        (index (boymoo::trie-put (coerce "CAR" 'list) (list (car imports)) nil))
        (pkgs (boymoo::trie-put package (list imports index t nil) nil))
        (ok (append (coerce "(theorem BM-HIDDEN::FOO)" 'list) '(#\Newline)))
        (bad (append (coerce "(theorem BM-HIDDEN::CAR)" 'list) '(#\Newline))))
   (and (equal (boymoo::parse-line ok *rt-test-words* pkgs) '(:theorem boymoo::|BM-HIDDEN::FOO|))
        (not (boymoo::parse-line ok *rt-test-words* nil))
        (not (boymoo::parse-line bad *rt-test-words* pkgs)))))
(value-triple (cw "~%ROUND-TRIP-OK hidden-reader-package~%"))
