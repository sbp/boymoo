(in-package "BOYMOO-PROOFS")

(include-book "objects")
(include-book "entry")
(include-book "package-layout")
(include-book "elaboration")
(include-book "front-agreement")
(include-book "builder-map")
(include-book "attachment-graph")
(include-book "quote-elaboration")
(include-book "package-home-availability")

(logic)
(set-verify-guards-eagerness 0)

(defconst *data-example-quoted-text*
  "(COMMON-LISP::NIL COMMON-LISP::T \"a\\22\\5C\\00\\FF\" #\\FF 4611686018427387904 -4611686018427387905 4611686018427387903 -4611686018427387904 3/5 #C(5/7 -2/3) KEYWORD::|a\\7Cb| . KEYWORD::||)")

(defconst *data-example-program-text*
  (concatenate
   'string
   "(package \"COMMON-LISP\" COMMON-LISP::NIL)
(hidden-package \"KEYWORD\" COMMON-LISP::NIL)
(hidden-package \"ACL2-INPUT-CHANNEL\" COMMON-LISP::NIL)
(package \"KEYWORD\" COMMON-LISP::NIL)
(define COMMON-LISP::NIL (ACL2-INPUT-CHANNEL::F (ACL2-INPUT-CHANNEL::X) (COMMON-LISP::QUOTE "
   *data-example-quoted-text*
   ")))
(entry ACL2-INPUT-CHANNEL::F)
"))

(defun data-example-quoted-value ()
  (list* nil t (coerce (list #\a #\" #\\ (code-char 0) (code-char 255)) 'string)
         (code-char 255) (expt 2 62) (- -1 (expt 2 62)) (1- (expt 2 62)) (- (expt 2 62))
         3/5 #C(5/7 -2/3)
         (intern-in-package-of-symbol "a|b" :keyword)
         (intern-in-package-of-symbol "" :keyword)))

(defun data-example-package (name exemplar visible)
  (proof-package name (intern-in-package-of-symbol "ACL2-PKG-WITNESS" exemplar) visible nil))

(defun data-example-static-check ()
  (let* ((base #x100000)
         (lines (boymoo-compiler::read-program *data-example-program-text*))
         (packages (list (data-example-package "COMMON-LISP" nil t)
                         (data-example-package "KEYWORD" :keyword t)
                         (data-example-package "ACL2-INPUT-CHANNEL"
                                               'acl2-input-channel::f nil))))
    (mv-let (definitions arities attachments sources package-lines entry target)
      (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)
      (declare (ignore definitions arities attachments sources entry target))
      (mv-let (image constants) (boymoo-compiler::data-build lines package-lines)
        (let* ((machine (boymoo-model::a64-state nil 0 0 0 nil))
               (machine (proof-load-cleared-string (boymoo-compiler::image-string (cdr image))
                                                   base machine))
               (records (data-build-allocation-records lines package-lines base)))
          (mv-let (ok objects) (data-static-image-map base image constants machine)
            (and ok
                 (data-program-storage-input-p lines)
                 (data-package-lines-storage-input-p package-lines)
                 (data-build-allocation-check-p lines package-lines base)
                 (data-build-home-available-p package-lines (intern-in-package-of-symbol "a|b" :keyword))
                 (data-static-known-records-p objects records)
                 (data-static-views-p base records packages machine)
                 (proof-image-at-p image base machine)
                 (proof-static-initial-p base objects packages machine)
                 (proof-constant-map-p
                  (list (cons *data-example-quoted-text* (data-example-quoted-value))
                        (cons "COMMON-LISP::NIL" nil) (cons "COMMON-LISP::T" t)
                        (cons "#\\FF" (code-char 255))
                        (cons "4611686018427387903" (1- (expt 2 62)))
                        (cons "-4611686018427387904" (- (expt 2 62)))
                        (cons "KEYWORD::|a\\7Cb|" (intern-in-package-of-symbol "a|b" :keyword))
                        (cons "KEYWORD::||" (intern-in-package-of-symbol "" :keyword)))
                  constants base objects packages machine))))))))

(defthm data-escaped-dotted-list-example
  (data-example-static-check)
  :rule-classes nil)

(defconst *data-attachment-to-if-text*
  "(package \"COMMON-LISP\" COMMON-LISP::NIL)
(package \"ACL2\" COMMON-LISP::NIL)
(attach ACL2::F COMMON-LISP::IF)
(define COMMON-LISP::NIL (ACL2::E (ACL2::X) (ACL2::F ACL2::X ACL2::X ACL2::X)))
(entry ACL2::E)
")

; The line that attaches F to IF is read, and the indexing check refuses it.
(defthm data-attachment-to-if-is-refused
  (let ((lines (boymoo-compiler::read-program *data-attachment-to-if-text*)))
    (and (member-equal '("attach" "ACL2::F" "COMMON-LISP::IF") lines)
         (not (data-indexable-lines-p lines nil nil))))
  :rule-classes nil)

(defthm data-indexed-attachment-walks-detect-a-cycle
  (and (data-indexed-attachments-acyclic-p
        '(("attach" "ACL2::F" "ACL2::G") ("attach" "ACL2::G" "ACL2::H")))
       (not (data-indexed-attachments-acyclic-p
             '(("attach" "ACL2::F" "ACL2::G") ("attach" "ACL2::G" "ACL2::F")))))
  :rule-classes nil)

; Rules 3 and 4 of the variable rule of spec/language.md, section 5.
(defthm data-ampersand-and-starred-names-are-not-variables
  (and (equal (char (symbol-name 'acl2::&) 0) #\&)
       (not (boymoo-compiler::variable-name-p "ACL2::&"))
       (not (boymoo-compiler::variable-name-p "ACL2::|&x|"))
       (not (boymoo-compiler::variable-name-p "ACL2::*"))
       (not (boymoo-compiler::variable-name-p "ACL2::*X*"))
       (boymoo-compiler::variable-name-p "ACL2::X*")
       (boymoo-compiler::variable-name-p "ACL2::||"))
  :rule-classes nil)

(defconst *data-span-example-text*
  "(package \"COMMON-LISP\" COMMON-LISP::NIL)
(package \"ACL2-INPUT-CHANNEL\" COMMON-LISP::NIL)
(define COMMON-LISP::NIL (ACL2-INPUT-CHANNEL::F (ACL2-INPUT-CHANNEL::X) ((COMMON-LISP::LAMBDA (ACL2-INPUT-CHANNEL::Y) (COMMON-LISP::QUOTE (1 . #\\41))) ACL2-INPUT-CHANNEL::X)))
(entry ACL2-INPUT-CHANNEL::F)
(target linux)
")

(defconst *data-span-example-events*
  '((:open) (:atom 8) (:space) (:atom 22) (:space) (:atom 39) (:close) (:line-feed)
    (:open) (:atom 49) (:space) (:atom 70) (:space) (:atom 87) (:close) (:line-feed)
    (:open) (:atom 96) (:space) (:atom 113) (:space) (:open) (:atom 136) (:space)
    (:open) (:atom 159) (:close) (:space) (:open) (:open) (:atom 182) (:space)
    (:open) (:atom 205) (:close) (:space) (:open) (:atom 226) (:space)
    (:quote 237 (228 229 230 231 232 236 237)) (:close) (:close) (:space) (:atom 261)
    (:close) (:close) (:close) (:line-feed)
    (:open) (:atom 271) (:space) (:atom 293) (:close) (:line-feed)
    (:open) (:atom 302) (:space) (:atom 308) (:close) (:line-feed)))

(defconst *data-span-example-definition*
  '(acl2-input-channel::f (acl2-input-channel::x)
    ((lambda (acl2-input-channel::y) (quote (1 . #\A))) acl2-input-channel::x)))

(defun data-span-example-check ()
  (let* ((lines (boymoo-compiler::read-program *data-span-example-text*))
         (source-lines (list '(:target :linux) '(:entry acl2-input-channel::f)
                             (list :define nil (list *data-span-example-definition*))
                             '(:package "ACL2-INPUT-CHANNEL" nil t) '(:package "COMMON-LISP" nil t)))
         (bindings (list (cons "(1 . #\\41)" (cons 1 #\A))))
         (witnesses '((((:open) (:atom 2) (:space) (:atom 4) (:space) (:atom 9) (:close))
                        ("1" "." "#\\41"))))
         (term (caddr (caddr (nth 2 lines))))
         (packages (list (data-example-package "COMMON-LISP" nil t)
                         (data-example-package "ACL2-INPUT-CHANNEL" 'acl2-input-channel::f t))))
    (mv-let (ok source-term) (data-elaborate-term :term term packages bindings)
      (and (data-program-spans-p *data-span-example-text* *data-span-example-events* lines)
           (data-source-lines-spelled-p lines source-lines bindings nil nil)
           (data-quote-spellings-p bindings witnesses)
           (equal (mv-list 6 (data-elaborate-program-with-quotes *data-span-example-text* packages))
                  (list t *data-span-example-events* lines source-lines bindings witnesses))
           ok (equal source-term (caddr *data-span-example-definition*))))))

(defthm data-checked-span-and-lambda-example
  (data-span-example-check)
  :rule-classes nil)
