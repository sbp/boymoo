(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *api-prefix* "T1")
(defconst *api-line-endings* (coerce (list #\Return #\Newline) 'string))
(defconst *api-context-kinds*
  '("(define " "(theorem " "(axiom " "(constrain " "(choose " "(reserve "))

(defun api-raw-line (line)
  (text-strip-right line *api-line-endings*))

(defun api-as-lines (lines)
  (if (stringp lines) (text-lines lines) lines))

(defun api-parse (raw)
  (run-parse-line raw))

(defun api-hints-scan (lines measures)
  (if (endp lines)
      measures
    (let ((raw (api-raw-line (car lines))))
      (if (text-starts-with raw "(measure ")
          (book-proofs-let* ((parsed (api-parse raw)))
            (let ((data (cadr parsed)))
              (api-hints-scan (cdr lines) (table-put measures (car data) (cdr data)))))
        (api-hints-scan (cdr lines) measures)))))

(defun api-hints (lines)
  (api-hints-scan lines nil))

(defun api-constrained-names (pairs names)
  (if (endp pairs)
      (reverse names)
    (let ((pair (car pairs)))
      (if (equal (len pair) 2)
          (api-constrained-names (cdr pairs) (cons (car pair) names))
        (proof-list-of-length pair 2)))))

(defun api-statement-names (kind data)
  (cond ((equal kind "define")
         (book-proofs-let* ((names (run-definition-names (cdr data))))
           (seq-sorted (proof-unique names))))
        ((equal kind "constrain")
         (if (consp (cdr data))
             (let ((formulas (if (equal (cadr data) *proof-nil*) nil (cadr data))))
               (book-proofs-let* ((names (api-constrained-names (append (car data) formulas) nil)))
                 (seq-sorted (proof-unique names))))
           '(:failure "failure" "")))
        ((consp data) (list (car data)))
        (t '(:failure "failure" ""))))

(defun api-choice-numbered-values (bound actual index bindings)
  (if (endp bound)
      bindings
    (api-choice-numbered-values
     (cdr bound) actual (1+ index)
     (table-put bindings (car bound) (list (proof-sym "MV-NTH" "ACL2") (proof-quote index) actual)))))

(defun api-choice-axiom-values (actual bound)
  (if (equal (len bound) 1)
      (list (cons (car bound) actual))
    (api-choice-numbered-values bound actual 0 nil)))

(defun api-choice-free-bindings (free free2 bindings)
  (if (or (endp free) (endp free2))
      bindings
    (api-choice-free-bindings
     (cdr free) (cdr free2) (table-put bindings (car free) (car free2)))))

(defun api-choice-axiom (data)
  (if (not (equal (len data) 5))
      (proof-list-of-length data 5)
    (let* ((fn (car data))
           (bound (cadr data))
           (free (caddr data))
           (body (cadddr data))
           (free2 (car (cddddr data)))
           (call (cons fn (if (equal free *proof-nil*) nil free)))
           (first (api-choice-axiom-values call bound)))
      (book-proofs-let* ((entered (proof-subst body first)))
        (let* ((implication (list *library-implies* body entered))
               (basic (if (< 1 (len bound))
                          (proof-ite (list (proof-sym "TRUE-LISTP" "ACL2") call)
                                     implication *proof-false*)
                        implication)))
          (if (equal free2 *proof-nil*)
              basic
            (let ((call2 (cons fn free2)))
              (book-proofs-let* ((body2 (proof-subst body (api-choice-free-bindings free free2 nil)))
                                (second (api-choice-axiom-values call2 bound))
                                (body2-first (proof-subst body2 first))
                                (body2-second (proof-subst body2 second))
                                (body-second (proof-subst body second)))
                (let ((d1 (proof-eq call call2))
                      (d2 (proof-ite entered (proof-neg body2-first) *proof-false*))
                      (d3 (proof-ite body2-second (proof-neg body-second) *proof-false*)))
                  (proof-ite basic (proof-ite d1 d1 (proof-ite d2 d2 d3)) *proof-false*))))))))))

(defun api-context-make (lib index seen declared helpers)
  (list :context lib index seen declared helpers))

(defun api-context-lib (context)
  (cadr context))

(defun api-context-index (context)
  (caddr context))

(defun api-context-seen (context)
  (cadddr context))

(defun api-context-declared (context)
  (car (cddddr context)))

(defun api-context-helpers (context)
  (cadr (cddddr context)))

(defun api-context-with-seen (context seen)
  (api-context-make (api-context-lib context) (api-context-index context) seen
                    (api-context-declared context) (api-context-helpers context)))

(defun api-context-entry-names (entries names)
  (if (endp entries)
      (proof-unique names)
    (book-proofs-let* ((new-names (run-entry-names (car entries))))
      (api-context-entry-names (cdr entries) (append new-names names)))))

(defun api-context-init ()
  (book-proofs-let* ((lib (book-library-book-library-build (book-library-book-library-init (proof-proof-init))))
                    (index (proof-search-fact-index-init lib))
                    (helpers (api-context-entry-names (library-library-entries lib) nil)))
    (api-context-make lib index nil (table-keys (proof-proof-facts (library-library-proof lib))) helpers)))

(defun api-context-add-choice (lib data)
  (book-proofs-let* ((choice (api-choice-axiom data)))
    (let* ((proof (library-library-proof lib))
           (facts (table-put (proof-proof-facts proof) (car data) (list choice))))
      (library-library-with-proof lib (proof-proof-with-facts proof facts)))))

(defun api-context-append-parsed (context seen parsed)
  (book-proofs-let* ((parsed parsed)
                    (names (api-statement-names (car parsed) (cadr parsed))))
    (let* ((kind (car parsed))
           (data (cadr parsed))
           (lib (api-context-lib context))
           (index (api-context-index context))
           (helpers (api-context-helpers context))
           (declared (union-equal names (api-context-declared context))))
      (cond ((intersectp-equal names helpers) '(:failure "failure" ""))
            ((equal kind "reserve") (api-context-make lib index seen declared helpers))
            (t
             (book-proofs-let* ((lib (if (equal kind "choose")
                                        (api-context-add-choice lib data)
                                      (run-add-statement lib kind data)))
                               (names (run-statement-fact-names kind data))
                               (index (run-index-names (proof-search-fact-index-with-lib index lib) names)))
               (api-context-make lib index seen declared helpers)))))))

(defun api-context-parse-line (raw remembered)
  (and (text-starts-with raw *api-context-kinds*)
       (if (and remembered (equal raw (car remembered)))
           (cdr remembered)
         (api-parse raw))))

(defun api-context-append-record (context raw parsed)
  (let ((seen (cons raw (api-context-seen context))))
    (if parsed
        (api-context-append-parsed context seen parsed)
      (api-context-with-seen context seen))))

(defun api-context-append (context line)
  (let* ((raw (api-raw-line line))
         (seen (api-context-seen context)))
    (if (member-equal raw seen)
        context
      (api-context-append-record context raw (api-context-parse-line raw nil)))))

(defun api-context-working-copy (context)
  (let ((lib (api-context-lib context)))
    (list lib (proof-search-fact-index-with-lib (api-context-index context) lib))))

(defun api-context-append-lines (lines context)
  (if (endp lines)
      context
    (book-proofs-let* ((context (api-context-append context (car lines))))
      (api-context-append-lines (cdr lines) context))))

(defun api-context-for (earlier library)
  (book-proofs-let* ((context (api-context-init))
                    (context (api-context-append-lines library context)))
    (api-context-append-lines earlier context)))

(defun api-measure-choices-measured-p (definitions measured)
  (or (endp definitions)
      (book-proofs-let* ((definition (proof-list-of-length (car definitions) 3)))
        (and (assoc-equal (car definition) measured)
             (api-measure-choices-measured-p (cdr definitions) measured)))))

(defun api-measure-choices-formals (definitions formals)
  (if (endp definitions)
      formals
    (let ((definition (car definitions)))
      (if (equal (len definition) 3)
          (api-measure-choices-formals
           (cdr definitions) (table-put formals (car definition) (cadr definition)))
        (proof-list-of-length definition 3)))))

(defun api-measure-choices-arity (formals least)
  (if (endp formals)
      least
    (api-measure-choices-arity (cdr formals) (min least (len (cdar formals))))))

(defun api-measure-choices-setup (data defined)
  (book-proofs-let* ((calls (termination-recursive-calls (car data) (cdr data)))
                    (formals (api-measure-choices-formals (cdr data) nil)))
    (if (endp formals)
        '(:failure "failure" "")
      (let* ((nfix-name (proof-sym "NFIX" "ACL2"))
             (constructors (if (assoc-equal nfix-name defined)
                               (list *library-count* nfix-name)
                             (list *library-count*))))
        (list calls formals constructors (api-measure-choices-arity (cdr formals) (len (cdar formals))))))))

(defun api-measure-choices-changed-p (calls formals position unchanged)
  (if (endp calls)
      (not unchanged)
    (let* ((call (car calls))
           (args (cdr (assoc-equal (termination-call-caller call) formals)))
           (actuals (termination-call-actuals call)))
      (if (or (<= (len args) position) (<= (len actuals) position))
          '(:failure "failure" "")
        (api-measure-choices-changed-p
         (cdr calls) formals position (or unchanged (equal (nth position args) (nth position actuals))))))))

(defun api-measure-choices-make (formals function position)
  (if (endp formals)
      nil
    (acons (caar formals) (list (list function (nth position (cdar formals))) *proof-ordinal-less*)
           (api-measure-choices-make (cdr formals) function position))))

(defun api-measure-choices-new-p (proposed measured)
  (and (consp proposed)
       (or (not (equal (seq-slice (cdr (assoc-equal (caar proposed) measured)) 0 2) (cdar proposed)))
           (api-measure-choices-new-p (cdr proposed) measured))))

(defun api-measure-choices-for-position (constructors formals position measured)
  (if (endp constructors)
      nil
    (let ((proposed (api-measure-choices-make formals (car constructors) position)))
      (if (api-measure-choices-new-p proposed measured)
          (cons proposed (api-measure-choices-for-position (cdr constructors) formals position measured))
        (api-measure-choices-for-position (cdr constructors) formals position measured)))))

(defun api-measure-choices-at (position setup measured)
  (let ((calls (car setup))
        (formals (cadr setup))
        (constructors (caddr setup)))
    (if (endp calls)
        nil
      (book-proofs-let* ((changed (api-measure-choices-changed-p calls formals position nil)))
        (and changed (api-measure-choices-for-position constructors formals position measured))))))

(defun api-replace-names-alias (symbol aliases)
  (table-get aliases symbol symbol))

(defun api-replace-names-aliases (symbols aliases)
  (if (endp symbols)
      nil
    (cons (api-replace-names-alias (car symbols) aliases)
          (api-replace-names-aliases (cdr symbols) aliases))))

(mutual-recursion
 (defun api-replace-names-term (value aliases)
   (declare (xargs :measure (acl2-count value)))
   (cond ((or (not (proof-compound value)) (proof-is-call value *proof-quote*)) value)
         ((endp value) '(:failure "failure" ""))
         (t
          (let ((operator (car value)))
            (if (proof-compound operator)
                (if (and (consp operator) (consp (cdr operator))
                         (consp (cddr operator)) (endp (cdddr operator)))
                    (book-proofs-let* ((body (api-replace-names-term (caddr operator) aliases))
                                      (actuals (api-replace-names-terms (cdr value) aliases)))
                      (cons (list (car operator) (cadr operator) body) actuals))
                  (proof-list-of-length operator 3))
              (book-proofs-let* ((actuals (api-replace-names-terms (cdr value) aliases)))
                (cons (api-replace-names-alias operator aliases) actuals)))))))

 (defun api-replace-names-terms (values aliases)
   (declare (xargs :measure (acl2-count values)))
   (if (endp values)
       nil
     (book-proofs-let* ((first (api-replace-names-term (car values) aliases))
                       (rest (api-replace-names-terms (cdr values) aliases)))
       (cons first rest)))))

(defun api-replace-names-substitution-list (pairs aliases)
  (if (endp pairs)
      nil
    (let ((pair (car pairs)))
      (if (equal (len pair) 2)
          (book-proofs-let* ((rhs (api-replace-names-term (cadr pair) aliases))
                            (rest (api-replace-names-substitution-list (cdr pairs) aliases)))
            (cons (list (car pair) rhs) rest))
        (proof-list-of-length pair 2)))))

(defun api-replace-names-substitutions (values aliases)
  (if (equal values *proof-nil*)
      values
    (api-replace-names-substitution-list values aliases)))

(defun api-replace-names-instances (instances aliases)
  (cond ((equal instances *proof-nil*) instances)
        ((endp instances) nil)
        (t
         (book-proofs-let* ((first (api-replace-names-substitutions (car instances) aliases))
                           (rest (api-replace-names-instances (cdr instances) aliases)))
           (cons first rest)))))

(defun api-replace-names-definitions (definitions aliases)
  (if (endp definitions)
      nil
    (let ((definition (car definitions)))
      (if (equal (len definition) 3)
          (book-proofs-let* ((body (api-replace-names-term (caddr definition) aliases))
                            (rest (api-replace-names-definitions (cdr definitions) aliases)))
            (cons (list (api-replace-names-alias (car definition) aliases) (cadr definition) body) rest))
        (proof-list-of-length definition 3)))))

(defun api-replace-names-rename (word fields aliases statement-entry)
  (cond ((equal word "define")
         (if (endp fields)
             '(:failure "failure" "")
           (book-proofs-let* ((defs (api-replace-names-definitions (cdr fields) aliases)))
             (let ((rulers (car fields)))
               (cons (if (proof-compound rulers) (api-replace-names-aliases rulers aliases) rulers) defs)))))
        ((member-equal word '("lemma" "measure" "witness"))
         (if (endp fields)
             '(:failure "failure" "")
           (let ((name (if statement-entry (car fields) (api-replace-names-alias (car fields) aliases))))
             (book-proofs-let* ((data (if (equal word "witness")
                                         (api-replace-names-aliases (cdr fields) aliases)
                                       (api-replace-names-terms (cdr fields) aliases))))
               (cons name data)))))
        ((equal word "fact")
         (if (endp fields)
             '(:failure "failure" "")
           (list (api-replace-names-alias (car fields) aliases))))
        ((equal word "instantiate")
         (if (endp (cdr fields))
             '(:failure "failure" "")
           (book-proofs-let* ((substitutions (api-replace-names-substitutions (cadr fields) aliases)))
             (list (car fields) substitutions))))
        ((equal word "induct")
         (if (equal (len fields) 5)
             (book-proofs-let* ((instances (api-replace-names-instances (car (cddddr fields)) aliases))
                               (formula (api-replace-names-term (caddr fields) aliases))
                               (measure (api-replace-names-term (cadddr fields) aliases)))
               (list (car fields) (cadr fields) formula measure instances))
           (proof-list-of-length fields 5)))
        ((equal word "subsume")
         (and (consp fields)
              (book-proofs-let* ((terms (api-replace-names-terms (cdr fields) aliases)))
                (cons (car fields) terms))))
        ((member-equal word '("beta" "compute"))
         (if (endp fields)
             '(:failure "failure" "")
           (book-proofs-let* ((term (api-replace-names-term (car fields) aliases)))
             (list term))))
        (t fields)))

(defun api-replace-names-spellings (aliases spellings)
  (if (endp aliases)
      spellings
    (book-proofs-let* ((spelling (proof-write (caar aliases))))
      (api-replace-names-spellings (cdr aliases) (cons spelling spellings)))))

(defun api-replace-names-lines (lines aliases statement-entry spellings rewritten)
  (if (endp lines)
      (text-join "" (reverse rewritten))
    (let ((line (car lines)))
      (book-proofs-let* ((source (if (intersectp-equal spellings (run-helper-names line))
                                     (book-proofs-let* ((parsed (api-parse line))
                                                       (fields (api-replace-names-rename
                                                                (car parsed) (cadr parsed) aliases statement-entry)))
                                       (proof-line (car parsed) fields))
                                   (concatenate 'string line *book-proofs-newline*))))
        (api-replace-names-lines (cdr lines) aliases statement-entry spellings (cons source rewritten))))))

(defun api-replace-names (source aliases statement-entry)
  (if (endp aliases)
      source
    (book-proofs-let* ((spellings (api-replace-names-spellings aliases nil)))
      (api-replace-names-lines (run-split-byte-lines source) aliases statement-entry spellings nil))))

(defun api-exported-add-aliases (names base multiple number declared aliases)
  (if (endp names)
      aliases
    (let* ((name (car names))
           (label (if multiple (concatenate 'string base "-" (decimal-text number)) base))
           (renamed (proof-sym label (cadr name))))
      (if (member-equal renamed declared)
          :collision
        (api-exported-add-aliases (cdr names) base multiple (1+ number) declared
                                  (table-put aliases name renamed))))))

(defun api-exported-entries (entries declared aliases lemmas)
  (cond ((endp entries) '(:failure "failure" ""))
        ((endp (cdr entries))
         (book-proofs-let* ((entry (api-replace-names (cadddr (car entries)) aliases t)))
           (list (reverse lemmas) entry)))
        (t
         (let* ((block (car entries))
                (source (cadddr block)))
           (book-proofs-let* ((with-dependencies (api-replace-names source aliases nil)))
             (let* ((digest (text-upper (seq-slice (siphash-hexdigest with-dependencies) 0 24)))
                    (base (concatenate 'string "PROVER-" *api-prefix* "-" digest)))
               (book-proofs-let* ((names (run-entry-names block))
                                 (aliases (api-exported-add-aliases names base (consp (cdr names)) 1 declared aliases)))
                 (if (eq aliases :collision)
                     nil
                   (book-proofs-let* ((lemma (api-replace-names source aliases nil)))
                     (api-exported-entries (cdr entries) declared aliases (cons lemma lemmas)))))))))))

(defun api-exported (certificate declared)
  (api-exported-entries (book-proofs-certificate-entries certificate) declared nil nil))

(defun api-common-lisp-definition-p (definitions)
  (if (endp definitions)
      nil
    (book-proofs-let* ((definition (proof-list-of-length (car definitions) 3))
                      (package-name (proof-term-at (car definition) 1)))
      (or (equal package-name "COMMON-LISP")
          (api-common-lisp-definition-p (cdr definitions))))))

(defun api-collect-measures (definitions candidates measured)
  (if (endp definitions)
      measured
    (let* ((function (caar definitions))
           (stored (assoc-equal function candidates)))
      (api-collect-measures
       (cdr definitions) candidates (if stored (table-put measured function (cdr stored)) measured)))))

(defun api-prove-guess (guess context kind data name declared)
  (let* ((copy (api-context-working-copy context))
         (candidate (book-proofs-book-prover-prove (car copy) kind data name guess (cadr copy)))
         (certificate (car candidate)))
    (if (or (failure-p candidate) (failure-p certificate)
            (not (equal (book-proofs-certificate-reason certificate) "")))
        nil
      (api-exported certificate declared))))

(defund api-prove-guesses (guesses context kind data name declared)
  (if (endp guesses)
      nil
    (let ((solved (api-prove-guess (car guesses) context kind data name declared)))
      (or solved (api-prove-guesses (cdr guesses) context kind data name declared)))))

(defun api-prove-positions (remaining position setup measured context kind data name declared)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (book-proofs-let* ((guesses (api-measure-choices-at position setup measured)))
      (or (api-prove-guesses guesses context kind data name declared)
          (api-prove-positions (1- remaining) (1+ position) setup measured context kind data name declared)))))

(defun api-prove-definition (context kind data name measured declared)
  (book-proofs-let* ((measured-p (api-measure-choices-measured-p (cdr data) measured)))
    (let ((solved (and measured-p (api-prove-guess measured context kind data name declared))))
      (or solved
          (book-proofs-let* ((setup (api-measure-choices-setup
                                     data (proof-proof-definitions (library-library-proof (api-context-lib context))))))
            (api-prove-positions (cadddr setup) 0 setup measured context kind data name declared))))))

(defun api-prove-context-with-hints (context kind data name hints)
  (book-proofs-let* ((hints hints)
                    (measured (api-collect-measures (and hints (cdr data)) hints nil))
                    (names (api-statement-names kind data)))
    (let ((declared (union-equal (api-context-declared context) names)))
      (if (equal kind "define")
          (api-prove-definition context kind data name measured declared)
        (api-prove-guess nil context kind data name declared)))))

(defun api-prove-context-statement (raw context kind data name aids)
  (if (member-equal raw (api-context-seen context))
      nil
    (api-prove-context-with-hints
     context kind data name (and (equal kind "define") (api-hints (api-as-lines aids))))))

(defun api-proof-obligation-parsed (raw parsed)
  (book-proofs-let* ((parsed parsed))
    (let ((kind (car parsed))
          (data (cadr parsed)))
      (if (not (member-equal kind '("define" "constrain" "theorem")))
          nil
        (book-proofs-let* ((protected (and (equal kind "define") (api-common-lisp-definition-p (cdr data)))))
          (if protected
              nil
            (book-proofs-let* ((name (book-proofs-obligation-name kind data)))
              (and name (list raw kind data name)))))))))

(defun api-proof-obligation (statement)
  (let ((raw (api-raw-line statement)))
    (api-proof-obligation-parsed raw (api-parse raw))))

(defun api-prove-in-context (statement earlier library aids)
  (book-proofs-let* ((obligation (api-proof-obligation statement)))
    (and obligation
         (book-proofs-let* ((context (api-context-for (api-as-lines earlier) (api-as-lines library))))
           (api-prove-context-statement (car obligation) context (cadr obligation)
                                        (caddr obligation) (cadddr obligation) aids)))))

(defun api-prove (statement earlier library aids)
  (let ((solved (api-prove-in-context statement earlier library aids)))
    (if (failure-p solved) nil solved)))
