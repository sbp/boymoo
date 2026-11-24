(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-list-bounds-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *t3-list-bounds-char-list* (proof-sym "CHARACTER-LISTP" "ACL2"))
(defconst *t3-list-bounds-character* (proof-cl "CHARACTERP"))
(defconst *t3-list-bounds-coerce* (proof-cl "COERCE"))
(defconst *t3-list-bounds-stringp* (proof-cl "STRINGP"))
(defconst *t3-list-bounds-list-type* (proof-quote (proof-cl "LIST")))
(defconst *t3-list-bounds-string-type* (proof-quote (proof-cl "STRING")))
(defconst *t3-list-bounds-tail* (list *library-cdr* *library-x*))
(defconst *t3-list-bounds-cons-x* (list *proof-consp* *library-x*))
(defconst *t3-list-bounds-count-x* (list *library-count* *library-x*))

(defun t3-list-bounds-define-fold (lib name step base)
  (let* ((formals (list *library-x*))
         (body (proof-ite *t3-list-bounds-cons-x* step base))
         (proof (proof-proof-add-definition (library-library-proof lib)
                                            name formals body))
         (lib (library-library-with-proof lib proof)))
    (proof-with-checked-results
     ((source (proof-line "define" (list *proof-nil* (list name formals body))))
      (smaller (library-library-builtin lib 3 *library-x*))
      (first (proof-step-first smaller))
      (ordered (proof-proof-subsume proof smaller
                                    (list (proof-neg *t3-list-bounds-cons-x*) first)))
      (ordinal (library-library-builtin lib 1 *library-x*))
      (entry (proof-proof-entry "measure" name
                                (list name *t3-list-bounds-count-x*)
                                (list ordinal ordered))))
     (library-library-with-entries
      lib (append (library-library-entries lib)
                  (list (list "define" name (caddr entry)
                              (concatenate 'string source (cadddr entry)))))))))

(defun t3-list-bounds-tail-hypothesis (lib formula cons-step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((smaller (library-library-builtin lib 3 *library-x*))
      (decrease (proof-proof-discharge proof smaller cons-step))
      (child (proof-subst formula (list (cons *library-x* *t3-list-bounds-tail*))))
      (comparison (proof-step-first decrease))
      (hypothesis (proof-proof-assume proof (proof-ite comparison child *proof-true*) t)))
     (proof-proof-prove-if proof hypothesis decrease))))

(defun t3-list-bounds-tail-induction (lib formula step base)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((branch (proof-proof-cases proof *t3-list-bounds-cons-x* step base))
      (ordinal (library-library-builtin lib 1 *library-x*)))
     (proof-proof-induct proof ordinal branch formula *t3-list-bounds-count-x*
                         (list (list (list *library-x* *t3-list-bounds-tail*)))))))

(defun t3-list-bounds-endp-branch (lib call cons-step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((source (proof-proof-unfold proof call))
      (equality (proof-step-first source))
      (body (proof-term-at equality 2))
      (test (proof-term-at body 1))
      (first (proof-step-first cons-step))
      (signed (if (proof-is-call first *proof-consp*) (proof-neg test) test))
      (evidence (t3-logic-libraryproofs-prove-formula
                 lib signed (list *t3-logic-endp* *t3-logic-atom* *proof-not*)
                 (list cons-step)))
      (branch (proof-proof-select proof body evidence)))
     (proof-proof-chain proof source (list branch)))))

(defun t3-list-bounds-append-branch (lib left right cons-step)
  (t3-list-bounds-endp-branch lib (list *t3-list-bounds-append* left right) cons-step))

(defun t3-list-bounds-char-list-nil (lib)
  (t3-logic-libraryproofs-prove-formula
   lib (list *t3-list-bounds-char-list* *proof-false*)
   (list *t3-list-bounds-char-list* *t3-logic-atom* *proof-not*) nil))

(defun t3-list-bounds-char-list-components (lib step cons-step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((first (proof-step-first step))
      (argument (proof-term-at first 1))
      (opened (proof-proof-unfold proof (list *t3-list-bounds-char-list* argument)))
      (nonatom (t3-logic-libraryproofs-prove-formula
                lib (proof-neg (list *t3-logic-atom* argument))
                (list *t3-logic-atom* *proof-not*) (list cons-step)))
      (equality (proof-step-first opened))
      (body (proof-term-at equality 2))
      (selected (proof-proof-select proof body nonatom))
      (branch (proof-proof-chain proof opened (list selected)))
      (reduced (proof-proof-rewrite proof step branch '(1))))
     (proof-proof-conjunct proof reduced))))

(defun t3-list-bounds-char-cons (lib head tail)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((head-first (proof-step-first head))
      (car-term (proof-term-at head-first 1))
      (tail-first (proof-step-first tail))
      (cdr-term (proof-term-at tail-first 1))
      (call (list *t3-list-bounds-char-list* (list *proof-cons* car-term cdr-term)))
      (opened (proof-proof-unfold proof call))
      (equality (proof-step-first opened))
      (body (proof-term-at equality 2))
      (predicate (t3-logic-libraryproofs-normalize
                  lib body (list head) (list *t3-logic-atom* *proof-not*)))
      (reduced (proof-proof-chain proof opened (list predicate))))
     (proof-proof-transport proof tail reduced))))

(defun t3-list-bounds-append-character-lists (lib)
  (let* ((proof (library-library-proof lib))
         (premise (proof-ite (list *t3-list-bounds-char-list* *library-x*)
                            (list *t3-list-bounds-char-list* *library-y*) *proof-false*))
         (formula (proof-ite premise
                             (list *t3-list-bounds-char-list*
                                   (list *t3-list-bounds-append* *library-x* *library-y*))
                             *proof-true*)))
    (proof-with-checked-results
     ((assumed (proof-proof-assume proof premise t))
      (parts (proof-proof-conjunct proof assumed))
      (cons-step (proof-proof-assume proof *t3-list-bounds-cons-x* t))
      (components (t3-list-bounds-char-list-components lib (car parts) cons-step))
      (ih (t3-list-bounds-tail-hypothesis lib formula cons-step))
      (tail-types (t3-scan-typed-pair lib (cadr components) (cadr parts)))
      (append-tail (proof-proof-prove-if proof ih tail-types))
      (append-cons (t3-list-bounds-append-branch lib *library-x* *library-y* cons-step))
      (joined (t3-list-bounds-char-cons lib (car components) append-tail))
      (good (library-library-transport-argument lib joined append-cons 1))
      (atom-step (proof-proof-assume proof *t3-list-bounds-cons-x* nil))
      (append-atom (t3-list-bounds-append-branch lib *library-x* *library-y* atom-step))
      (base (library-library-transport-argument lib (cadr parts) append-atom 1))
      (yes (t3-scan-conclusion lib formula good))
      (no (t3-scan-conclusion lib formula base))
      (result (t3-list-bounds-tail-induction lib formula yes no)))
     (library-library-lemma lib "T3-CHARACTER-LIST-APPEND" formula result nil))))

(defun t3-list-bounds-string-list-inverse (lib characters)
  (proof-with-checked-results
   ((first (proof-step-first characters))
    (value (proof-term-at first 1))
    (axiom (library-library-axiom lib "COERCE-INVERSE-1" (list value))))
   (proof-proof-modus-ponens (library-library-proof lib) axiom characters)))

(defun t3-list-bounds-chars-to-string (characters)
  (list *t3-list-bounds-coerce* characters *t3-list-bounds-string-type*))

(defun t3-list-bounds-string-to-chars (string)
  (list *t3-list-bounds-coerce* string *t3-list-bounds-list-type*))

(defun t3-list-bounds-string-assertion (lib characters)
  (let ((proof (library-library-proof lib))
        (string (t3-list-bounds-chars-to-string characters)))
    (proof-with-checked-results
     ((step (proof-proof-fact proof "stringp-coerce"
                             (list (list *library-x* characters)
                                   (list *library-y* *t3-list-bounds-string-type*))))
      (first (proof-step-first step))
      (conclusion (proof-term-at first 2)))
     (if (not (equal conclusion (list *t3-list-bounds-stringp* string)))
         '(:failure "failure" "")
       (proof-with-checked-results
        ((premise (proof-term-at first 1))
         (different (t3-logic-libraryproofs-prove-formula lib premise (list *proof-not*) nil)))
        (proof-proof-modus-ponens proof step different))))))
