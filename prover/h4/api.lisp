(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h4-api-prefix* *h4-api-encoding-prefix*)
(defconst *h4-api-newline* (coerce (list #\Newline) 'string))
(defconst *h4-api-fact-opening* (coerce "(fact " 'list))

(defun h4-api-lines-chars (chars reversed output)
  (if (endp chars)
      (reverse
       (if (consp reversed)
           (cons (coerce (reverse reversed) 'string) output)
         output))
    (let ((code (char-code (car chars)))
          (current (cons (car chars) reversed)))
      (cond ((and (eql code 13)
                  (consp (cdr chars))
                  (eql (char-code (cadr chars)) 10))
             (h4-api-lines-chars
              (cddr chars) nil
              (cons (coerce (reverse (cons (cadr chars) current)) 'string)
                    output)))
            ((member-equal code '(10 11 12 13 28 29 30))
             (h4-api-lines-chars (cdr chars) nil
                                 (cons (coerce (reverse current) 'string)
                                       output)))
            (t (h4-api-lines-chars (cdr chars) current output))))))

(defun h4-api-lines (source)
  (if (stringp source)
      (h4-api-lines-chars (coerce source 'list) nil nil)
    source))

(defun h4-api-as-bytes (source)
  (if (text-ends-with source *h4-api-newline*)
      source
    (concatenate 'string source *h4-api-newline*)))

(defun h4-api-parsed (source)
  (h4-book-run-parse-statement (h4-api-as-bytes source)))

(defun h4-api-source-bytes (source)
  (if (endp source)
      nil
    (cons (h4-api-as-bytes (car source))
          (h4-api-source-bytes (cdr source)))))

(defun h4-api-add-aid (aids name value)
  (let ((values (table-get aids name nil)))
    (if (member-equal value values)
        aids
      (table-put aids name (append values (list value))))))

(defun h4-api-aid-measures (source measures)
  (if (endp source)
      measures
    (if (text-starts-with (car source) "(measure ")
        (proof-with-checked-results
            ((parsed (reader-reader-line
                      (reader-reader
                       (seq-slice (h4-api-as-bytes (car source)) 0 -1))))
             (parts (proof-list-of-length
                     (seq-slice (proof-freeze (cadar parsed)) 0 3) 3)))
          (h4-api-aid-measures
           (cdr source)
           (h4-api-add-aid measures (car parts)
                           (list (cadr parts) (caddr parts)))))
      (h4-api-aid-measures (cdr source) measures))))

(defun h4-api-aid-hints (uses hints)
  (if (endp uses)
      hints
    (h4-api-aid-hints
     (cdr uses)
     (h4-api-add-aid hints (caar uses) (cadar uses)))))

(defun h4-api-aid-info (source)
  (proof-with-checked-results
      ((measures (h4-api-aid-measures source nil))
       (uses (h4-book-hints-hint-uses (h4-api-source-bytes source))))
    (list measures (h4-api-aid-hints uses nil))))

(defun h4-api-make-world (library functions choices filters)
  (list :h4-api-world library functions choices filters))

(defun h4-api-world-library (world)
  (cadr world))

(defun h4-api-world-functions (world)
  (caddr world))

(defun h4-api-world-choices (world)
  (cadddr world))

(defun h4-api-world-filters (world)
  (car (cddddr world)))

(defun h4-api-world-with-library (world library)
  (h4-api-make-world library
                     (h4-api-world-functions world)
                     (h4-api-world-choices world)
                     (h4-api-world-filters world)))

(defun h4-api-add-function (name functions)
  (if (member-equal name functions)
      functions
    (append functions (list name))))

(defun h4-api-admit-functions (signatures functions)
  (if (endp signatures)
      functions
    (proof-with-checked-results
        ((signature (proof-list-of-length (car signatures) 2)))
      (h4-api-admit-functions (cdr signatures)
                              (h4-api-add-function (car signature) functions)))))

(defun h4-api-admit (world statement)
  (let ((kind (h4-book-run-statement-kind statement))
        (fields (h4-book-run-statement-fields statement))
        (functions (h4-api-world-functions world))
        (choices (h4-api-world-choices world))
        (filters (h4-api-world-filters world)))
    (proof-with-checked-results
        ((library (h4-tactics-tactics-add-statement
                   (h4-api-world-library world) kind fields)))
      (cond ((equal kind "constrain")
             (proof-with-checked-results
                 ((functions (h4-api-admit-functions (car fields) functions)))
               (h4-api-make-world library functions choices filters)))
            ((equal kind "choose")
             (proof-with-checked-results ((name (proof-term-at fields 0)))
               (h4-api-make-world library (h4-api-add-function name functions)
                                  (table-put choices name fields) filters)))
            (t (h4-api-world-with-library world library))))))

(defun h4-api-copy-world (world)
  world)

(defun h4-api-ground-world ()
  (h4-api-make-world (library-library-init (proof-proof-init)) nil nil nil))

(defun h4-api-admit-lines (world source excluded)
  (if (endp source)
      world
    (if (member-equal (car source) excluded)
        (h4-api-admit-lines world (cdr source) excluded)
      (proof-with-checked-results
          ((statement (h4-api-parsed (car source)))
           (world (h4-api-admit world statement)))
        (h4-api-admit-lines world (cdr source) excluded)))))

(defun h4-api-library-context-init (source)
  (let ((source (proof-unique source)))
    (proof-with-checked-results
        ((world (h4-api-ground-world))
         (world (h4-api-admit-lines (h4-api-copy-world world) source nil)))
      (list :h4-api-library-context source world))))

(defun h4-api-library-context-prefix (context earlier)
  (h4-api-admit-lines (h4-api-copy-world (caddr context))
                     (proof-unique earlier) (cadr context)))

(defun h4-api-library-context (source)
  (h4-api-library-context-init source))

(defun h4-run-proof-push-data (data pending)
  (if (endp data)
      pending
    (h4-run-proof-push-data
     (cdr data)
     (if (proof-step-p (car data))
         (cons (car data) pending)
       pending))))

(defun h4-run-proof-dependencies-loop (n pending seen facts)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "h4-run-proof-dependencies-loop"))
        ((endp pending) (reverse facts))
        ((member-equal (car pending) seen)
         (h4-run-proof-dependencies-loop (1- n) (cdr pending) seen facts))
        (t
         (let* ((step (car pending))
                (data (proof-step-data step)))
           (proof-with-checked-results
               ((facts (if (equal (proof-step-word step) "fact")
                           (proof-with-checked-results ((name (proof-term-at data 0)))
                             (if (member-equal name facts) facts (cons name facts)))
                         facts)))
             (h4-run-proof-dependencies-loop
              (1- n) (h4-run-proof-push-data data (cdr pending))
              (cons step seen) facts))))))

(defun h4-run-proof-dependencies (step)
  (h4-run-proof-dependencies-loop 1000000 (list step) nil nil))

(defun h4-run-source-mentions-name (name sources)
  (if (endp sources)
      nil
    (or (<= 0 (text-find (cadar sources) name))
        (h4-run-source-mentions-name name (cdr sources)))))

(defun h4-run-entry-needed-p (entry needed final-source selected)
  (let ((name (cadr entry)))
    (or (member-equal name needed)
        (and (equal (car entry) "define")
             (proof-with-checked-results ((written (proof-write name)))
               (or (<= 0 (text-find final-source written))
                   (h4-run-source-mentions-name written (reverse selected))))))))

(defun h4-run-source-fact-tails (chars tails)
  (if (endp chars)
      tails
    (h4-run-source-fact-tails
     (cdr chars)
     (if (and (eql (car chars) #\()
              (reader-prefix-p *h4-api-fact-opening* chars))
         (cons (nthcdr (len *h4-api-fact-opening*) chars) tails)
       tails))))

(defun h4-run-source-has-fact-p (tails name-and-close)
  (and (consp tails)
       (or (reader-prefix-p name-and-close (car tails))
           (h4-run-source-has-fact-p (cdr tails) name-and-close))))

(defun h4-run-entry-source-needs (entries fact-tails needed)
  (if (endp entries)
      needed
    (let ((name (cadar entries)))
      (proof-with-checked-results ((written (proof-write name)))
        (h4-run-entry-source-needs
         (cdr entries) fact-tails
         (if (and (h4-run-source-has-fact-p
                   fact-tails (coerce (concatenate 'string written ")") 'list))
                  (not (member-equal name needed)))
             (cons name needed)
           needed))))))

(defun h4-run-entry-step-count (counts)
  (if (endp counts)
      0
    (+ (car counts) (h4-run-entry-step-count (cdr counts)))))

(defun h4-run-entry-sources-loop (reversed entries needed final-source selected)
  (if (endp reversed)
      selected
    (let* ((entry (car reversed))
           (source (cadddr entry)))
      (proof-with-checked-results
          ((keep (h4-run-entry-needed-p entry needed final-source selected)))
        (if keep
            (let ((fact-tails (h4-run-source-fact-tails (coerce source 'list) nil)))
              (proof-with-checked-results
                  ((needed (h4-run-entry-source-needs entries fact-tails needed)))
                (h4-run-entry-sources-loop
                 (cdr reversed) entries needed final-source
                 (cons (list (h4-run-entry-step-count (caddr entry)) source)
                       selected))))
          (h4-run-entry-sources-loop (cdr reversed) entries needed
                                     final-source selected))))))

(defun h4-run-entry-sources (library last final-source)
  (let ((entries (library-library-entries library)))
    (proof-with-checked-results ((needed (h4-run-proof-dependencies last)))
      (h4-run-entry-sources-loop (reverse entries) entries needed final-source nil))))

(defun h4-api-support-sources (library proofs source)
  (if (endp proofs)
      nil
    (proof-with-checked-results
        ((selected (h4-run-entry-sources library (car proofs) source))
         (rest (h4-api-support-sources library (cdr proofs) source)))
      (append (strip-cars (strip-cdrs selected)) rest))))

(defun h4-api-select-entries (entries sources)
  (if (endp entries)
      nil
    (if (member-equal (cadddr (car entries)) sources)
        (cons (car entries) (h4-api-select-entries (cdr entries) sources))
      (h4-api-select-entries (cdr entries) sources))))

(defun h4-api-support-selection (world proofs source)
  (let ((library (h4-api-world-library world)))
    (proof-with-checked-results
        ((sources (h4-api-support-sources library proofs source)))
      (h4-api-select-entries (library-library-entries library) sources))))

(defun h4-api-alias-table (aliases)
  (if (endp aliases)
      nil
    (cons (cons (caar aliases) (cadar aliases))
          (h4-api-alias-table (cdr aliases)))))

(defun h4-api-finish-entry (name kind source inherited owned)
  (proof-with-checked-results ((owned owned)
                               (written (proof-write name)))
    (let* ((head (concatenate 'string "(" kind " " written))
           (tail (seq-slice source (length head) :none))
           (aliases (h4-api-alias-table (cadr owned))))
      (proof-with-checked-results ((renamed (h4-api-encoding-rename tail aliases nil)))
        (list (append (car inherited) (car owned))
              (concatenate 'string head renamed))))))

(defun h4-api-finish-with-cache (world statement kind arguments proofs inherited cache)
  (let* ((name (h4-book-run-statement-name statement))
         (prepared
          (proof-with-checked-results
              ((entry (h4-book-encoding-book-entry kind name arguments proofs))
               (entries (h4-api-support-selection world proofs (cadr entry))))
            (cons (cadr entry) entries))))
    (if (failure-p prepared)
        (cons prepared cache)
      (let ((encoded (h4-api-encoding-owned-entries-with-cache
                      (cdr prepared) (cadr inherited) nil cache)))
        (cons (h4-api-finish-entry name kind (car prepared) inherited (car encoded))
              (cdr encoded))))))

; A draft holds the world, entry kind, header arguments, proofs, and inherited prelude.
(defun h4-api-finish-draft (statement draft cache)
  (if (failure-p draft)
      (cons draft cache)
    (h4-api-finish-with-cache (car draft) statement (cadr draft) (caddr draft)
                              (cadddr draft) (nth 4 draft) cache)))

(defun h4-api-library-with-facts (library facts)
  (library-library-with-proof
   library (proof-proof-with-facts (library-library-proof library) facts)))

(defun h4-api-library-with-facts-and-definitions (library facts definitions)
  (let* ((proof (library-library-proof library))
         (updated (proof-make-proof facts definitions (proof-proof-primitives proof))))
    (library-library-with-proof
     library (proof-proof-with-kind updated (proof-proof-kind proof)))))

(defun h4-api-entry-facts (entries facts)
  (if (endp entries)
      nil
    (let* ((name (cadar entries))
           (fact (assoc-equal name facts)))
      (if fact
          (proof-with-checked-results
              ((rest (h4-api-entry-facts (cdr entries) facts)))
            (cons fact rest))
        '(:failure "failure" "")))))

(defun h4-api-entry-definitions (entries definitions)
  (if (endp entries)
      nil
    (let ((definition (assoc-equal (cadar entries) definitions)))
      (if definition
          (cons definition (h4-api-entry-definitions (cdr entries) definitions))
        (h4-api-entry-definitions (cdr entries) definitions)))))

(defun h4-api-core-support-from-ground (ground)
  (proof-with-checked-results
      ((world (h4-api-copy-world ground))
       (library (h4-tactics-tactics-propositional-lemmas (h4-api-world-library world)))
       (library (h4-terms-tactics-build library))
       (library (h4-book-arithmetic-countdown-lemmas library))
       (library (h4-book-tactics-equality-symmetry library)))
    (let ((entries (library-library-entries library))
          (proof (library-library-proof library)))
      (proof-with-checked-results ((facts (h4-api-entry-facts entries (proof-proof-facts proof))))
        (list entries facts (proof-proof-definitions proof))))))

(defun h4-api-core-support ()
  (h4-api-core-support-from-ground (h4-api-ground-world)))

(defun h4-api-facts-overlap-p (added facts)
  (if (endp added)
      nil
    (or (and (assoc-equal (caar added) facts) t)
        (h4-api-facts-overlap-p (cdr added) facts))))

(defun h4-api-prepare-core-installation (support)
  (proof-with-checked-results ((support support))
    (let ((entries (car support))
          (definitions (caddr support)))
      (list entries (table-update nil (cadr support)) definitions
            (table-update nil (h4-api-entry-definitions entries definitions))))))

(defun h4-api-install-core-support-prepared (world support)
  (proof-with-checked-results ((support support))
    (let* ((library (h4-api-world-library world))
           (proof (library-library-proof library))
           (entries (car support))
           (added (cadr support))
           (facts (proof-proof-facts proof))
           (definitions (proof-proof-definitions proof))
           (ready (consp (cdddr support))))
      (if (h4-api-facts-overlap-p added facts)
          '(:failure "failure" "")
        (h4-api-world-with-library
         world
         (h4-api-library-with-facts-and-definitions
          (library-library-with-entries library
                                        (append (library-library-entries library) entries))
          ; Admission gives each definition a fact. Disjoint additions can be appended.
          (if ready (append facts added) (table-update facts added))
          (if ready
              (append definitions (cadddr support))
            (table-update definitions (h4-api-entry-definitions entries (caddr support))))))))))

(defun h4-api-install-core-support (world)
  (h4-api-install-core-support-prepared world (h4-api-core-support)))

(defun h4-api-optional (result)
  (if (failure-p result) nil result))

(defun h4-api-pointwise-support-from-ground (definition necessity ground core)
  (proof-with-checked-results
      ((world (h4-api-copy-world ground))
       (definition (proof-list-of-length definition 2))
       (proof (proof-proof-add-definition
               (library-library-proof (h4-api-world-library world))
               *h4-function-equality-fn-equal* (car definition) (cadr definition))))
    (let* ((facts (table-put (proof-proof-facts proof)
                               *h4-function-equality-apply-necessity* necessity))
           (proof (proof-proof-with-facts proof facts))
           (world (h4-api-world-with-library
                   world
                   (library-library-with-proof (h4-api-world-library world) proof))))
      (proof-with-checked-results
          ((world (if (eq core :unprepared)
                      (h4-api-install-core-support world)
                    (h4-api-install-core-support-prepared world core)))
           (pointwise (h4-function-equality-pointwise-lemma (h4-api-world-library world))))
        (let* ((name (car pointwise))
               (library (cdr pointwise))
               (entries (library-library-entries library))
               (facts (proof-proof-facts (library-library-proof library))))
          (list (car (last entries)) name (table-get facts name nil)))))))

(defun h4-api-pointwise-key (world)
  (let* ((proof (library-library-proof (h4-api-world-library world)))
         (definition (assoc-equal *h4-function-equality-fn-equal*
                                  (proof-proof-definitions proof)))
         (necessity (assoc-equal *h4-function-equality-apply-necessity*
                                 (proof-proof-facts proof))))
    (and definition necessity (list (cdr definition) (cdr necessity)))))

(defun h4-api-install-pointwise-support (world support)
  (proof-with-checked-results ((support (h4-api-optional support)))
    (if (not support)
        world
      (let* ((library (h4-api-world-library world))
             (facts (proof-proof-facts (library-library-proof library)))
             (name (cadr support)))
        (if (assoc-equal name facts)
            '(:failure "failure" "")
          (h4-api-world-with-library
           world
           (library-library-with-entries
            (h4-api-library-with-facts library (table-put facts name (caddr support)))
            (append (library-library-entries library) (list (car support))))))))))

(defun h4-api-use-core-support-prepared (world ground core)
  (proof-with-checked-results
      ((world (if (eq core :unprepared)
                  (h4-api-install-core-support world)
                (h4-api-install-core-support-prepared world core))))
    (let ((key (h4-api-pointwise-key world)))
      (if key
          (h4-api-install-pointwise-support
           world (h4-api-pointwise-support-from-ground (car key) (cadr key) ground core))
        world))))

(defun h4-api-use-core-support (world)
  (h4-api-use-core-support-prepared world (h4-api-ground-world) :unprepared))

(defconst *h4-api-warrant-definitions*
  '(("sym" "ACL2" "APPLY$-PRIMP")
    ("sym" "ACL2" "HONS-GET")
    ("sym" "ACL2" "HONS-ASSOC-EQUAL")
    ("sym" "ACL2" "HONS-EQUAL")
    ("sym" "ACL2" "TAMEP-FUNCTIONP")
    ("sym" "ACL2" "TAMEP")
    ("sym" "ACL2" "LAMBDA-OBJECT-SHAPEP")
    ("sym" "ACL2" "LAMBDA-OBJECT-FORMALS")
    ("sym" "ACL2" "LAMBDA-OBJECT-BODY")
    ("sym" "ACL2" "SYMBOL-LISTP")))

(defun h4-api-add-definitions (proof definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      proof
    (proof-with-checked-results
        ((definition (proof-list-of-length (car definitions) 3))
         (proof (proof-proof-add-definition
                 proof (car definition) (cadr definition) (caddr definition))))
      (h4-api-add-definitions proof (cdr definitions)))))

(defun h4-api-names-only-p (definitions)
  (if (endp definitions)
      t
    (proof-with-checked-results ((text (proof-write (car definitions))))
      (if (or (<= 0 (text-find text "ACL2::H4-"))
              (<= 0 (text-find text "ACL2::SELF-")))
          nil
        (h4-api-names-only-p (cdr definitions))))))

(defun h4-api-warrant-support-from-ground (definitions ground)
  (proof-with-checked-results
      ((world (h4-api-copy-world ground))
       (proof (h4-api-add-definitions
               (library-library-proof (h4-api-world-library world)) definitions)))
    (let* ((library (library-library-with-proof (h4-api-world-library world) proof))
           (x *library-x*)
           (y *library-y*)
           (z *library-z*)
           (conditional (proof-ite x y z)))
      (proof-with-checked-results
          ((middle (proof-proof-excluded-middle proof x))
           (library (library-library-lemma library "EXCLUDED-MIDDLE" (proof-neg x) middle (list x)))
           (proof (library-library-proof library))
           (when-false (proof-proof-if-false proof conditional))
           (library (library-library-lemma library "IF-FALSE" (proof-eq conditional z)
                                           when-false (list x)))
           (proof (library-library-proof library))
           (when-true (proof-proof-if-true proof conditional))
           (library (library-library-lemma library "IF-TRUE" (proof-eq conditional y)
                                           when-true (list (proof-neg x))))
           (names-only (h4-api-names-only-p definitions))
           (certified (h4-badge-table-certify library :none)))
        (let* ((library (cdr certified))
               (entries (library-library-entries library))
               (proof (library-library-proof library)))
          (proof-with-checked-results
              ((facts (h4-api-entry-facts entries (proof-proof-facts proof)))
               (shared (h4-api-encoding-owned-entries entries nil names-only)))
            (list facts (h4-api-entry-definitions entries (proof-proof-definitions proof))
                  (car certified) shared)))))))

(defun h4-api-warrant-support (definitions)
  (h4-api-warrant-support-from-ground definitions (h4-api-ground-world)))

(defun h4-api-definition-names (table)
  (if (endp table)
      nil
    (proof-with-checked-results
        ((name (proof-term-at (car table) 0))
         (rest (h4-api-definition-names (cdr table))))
      (cons name rest))))

(defun h4-api-definitions-in-order (names definitions)
  (if (endp names)
      nil
    (let ((definition (assoc-equal (car names) definitions)))
      (if definition
          (cons definition (h4-api-definitions-in-order (cdr names) definitions))
        (h4-api-definitions-in-order (cdr names) definitions)))))

(defun h4-api-warrant-input (world formula)
  (let* ((library (h4-api-world-library world))
         (proof (library-library-proof library))
         (facts (proof-proof-facts proof))
         (definitions (proof-proof-definitions proof)))
    (proof-with-checked-results ((parts (h4-warrants-warrant-parts formula)))
      (let ((primitive (assoc-equal *h4-warrants-primitive* definitions)))
        (if (not (and parts (assoc-equal (cadr parts) facts) primitive))
            '(:failure "failure" "")
          (proof-with-checked-results
              ((body (proof-term-at (cdr primitive) 1))
               (getter (proof-term-at body 1))
               (quoted-table (proof-term-at getter 2))
               (table (proof-term-at quoted-table 1))
               (excluded (h4-api-definition-names table)))
            (if (member-equal (car parts) excluded)
                '(:failure "failure" "")
              (h4-api-definitions-in-order *h4-api-warrant-definitions* definitions))))))))

(defun h4-api-install-warrant-support (world support)
  (proof-with-checked-results ((support support))
    (let* ((library (h4-api-world-library world))
           (proof (library-library-proof library))
           (facts (proof-proof-facts proof))
           (definitions (proof-proof-definitions proof)))
      (if (h4-api-facts-overlap-p (car support) facts)
          '(:failure "failure" "")
        (let ((library (h4-api-library-with-facts-and-definitions
                        library (table-update facts (car support))
                        (table-update definitions (cadr support)))))
          (cons (cadddr support)
                (h4-api-make-world library (h4-api-world-functions world)
                                   (h4-api-world-choices world) (caddr support))))))))

(defun h4-api-prepare-warrant (world formula)
  (proof-with-checked-results ((input (h4-api-warrant-input world formula)))
    (h4-api-install-warrant-support world (h4-api-warrant-support input))))

(defun h4-api-special-plan (statement)
  (if (not (equal (h4-book-run-statement-kind statement) "theorem"))
      nil
    (proof-with-checked-results
        ((formula (proof-term-at (h4-book-run-statement-fields statement) 1))
         (tactic (h4-recipes-recipe formula)))
      (and tactic (cons tactic formula)))))

(defun h4-api-special-draft (plan prepared)
  (let ((tactic (car plan))
        (formula (cdr plan)))
    (proof-with-checked-results
        ((prepared prepared)
         (result (h4-recipes-apply tactic (h4-api-world-library (cdr prepared))
                                   formula
                                   (and (eq tactic :warrant-recipe)
                                        (h4-api-world-filters (cdr prepared)))))
         (proof (proof-proof-subsume (library-library-proof (cdr result))
                                     (car result) (list formula))))
      (list (h4-api-world-with-library (cdr prepared) (cdr result))
            "theorem" nil (list proof) (car prepared)))))

(defun h4-api-special-prepared-with-cache (statement plan prepared cache)
  (h4-api-finish-draft statement (h4-api-special-draft plan prepared) cache))

(defun h4-api-special-prepared (statement plan prepared)
  (car (h4-api-special-prepared-with-cache statement plan prepared :uncached)))

(defun h4-api-special-with-plan (world statement plan)
  (let ((world (h4-api-copy-world world)))
    (h4-api-special-prepared statement plan
                            (if (eq (car plan) :warrant-recipe)
                                (h4-api-prepare-warrant world (cdr plan))
                              (cons (list nil nil) world)))))

(defun h4-api-special (world statement)
  (proof-with-checked-results ((plan (h4-api-special-plan statement)))
    (and plan (h4-api-special-with-plan world statement plan))))

(defun h4-api-extra-theorem-attempt (library formula step)
  (proof-with-checked-results ((step step))
    (if step
        (proof-proof-subsume (library-library-proof library) step (list formula))
      nil)))

(defun h4-api-extra-theorem-finders (finders world formula)
  (if (endp finders)
      (cons nil world)
    (let ((library (h4-api-world-library world)))
      (proof-with-checked-results
          ((step
            (h4-api-optional
             (h4-api-extra-theorem-attempt
              library formula
              (case (car finders)
                (:projection (h4-book-projections-projection-proof library formula))
                (:projection-set (h4-book-projection-sets-projection-set-proof library formula))
                (:agreement (h4-book-agreement-agreement-proof-with-choices
                             library formula (h4-api-world-choices world)))
                (otherwise (h4-book-tactics-guarded-alias-proof library formula)))))))
        (if step
            (cons (list "theorem" nil (list step)) world)
          (h4-api-extra-theorem-finders (cdr finders) world formula))))))

(defun h4-api-extra-theorem (world statement)
  (if (not (equal (h4-book-run-statement-kind statement) "theorem"))
      (cons nil world)
    (proof-with-checked-results
        ((formula (proof-term-at (h4-book-run-statement-fields statement) 1)))
      (h4-api-extra-theorem-finders
       '(:projection :projection-set :agreement :guarded-alias) world formula))))

(defun h4-api-witness-arities (signatures)
  (if (endp signatures)
      nil
    (proof-with-checked-results
        ((signature (proof-list-of-length (car signatures) 2))
         (rest (h4-api-witness-arities (cdr signatures))))
      (cons (cadr signature) rest))))

(defun h4-api-proof-draft (world statement measures hints tables)
  (let* ((library (h4-api-world-library world))
         (kind (h4-book-run-statement-kind statement))
         (fields (h4-book-run-statement-fields statement))
         (theorem (equal kind "theorem"))
         (calls (h4-book-run-statement-calls statement)))
    (proof-with-checked-results
        ((formula (and theorem (proof-term-at fields 1)))
         (conversion (and theorem
                          (or (h4-book-compression-compression-shape formula)
                              (h4-book-expansion-expansion-shape formula)
                              (h4-book-inverse-inverse-shape formula))))
         (needs-order (or conversion (and theorem (h4-book-order-ordinal-candidate formula))))
         (needs-printing (or (and theorem (h4-book-printing-packing-formula formula))
                             (h4-book-numeric-measures-uses-floor-measure calls)))
         (modeled (if (equal kind "constrain")
                      (proof-with-checked-results
                          ((arities (h4-api-witness-arities (car fields))))
                        (h4-book-run-witness-definitions library arities))
                    (cons nil library))))
      (let* ((library (cdr modeled))
             (before (proof-proof-facts (library-library-proof library))))
        (proof-with-checked-results
            ((printing (if needs-printing
                           (h4-book-printing-printing-support library)
                         (cons nil library)))
             (ordering (if needs-order
                           (h4-book-order-order-support (cdr printing))
                         (cons nil (cdr printing)))))
          (let* ((library (h4-api-library-with-facts (cdr ordering) before))
                 (world (h4-api-world-with-library world library))
                 (expansions (h4-book-expansion-expansion-proofs-init))
                 (conversions (list expansions (h4-book-inverse-inversion-proofs-init expansions))))
            (proof-with-checked-results
                ((extra (h4-api-extra-theorem world statement))
                 (found
                  (if (car extra)
                      (cons (car extra) (h4-api-world-library (cdr extra)))
                    (let ((result
                           (h4-book-run-find-proof-with-templates
                            (h4-api-world-library (cdr extra)) statement
                            (table-update nil measures) (table-update nil hints)
                            (car modeled) (car printing) (car ordering)
                            conversions (h4-api-world-functions (cdr extra)) tables)))
                      (if (failure-p result) result (cons (car result) (cadr result)))))))
              (let ((result (car found)))
                (list (h4-api-world-with-library (cdr extra) (cdr found))
                      (car result) (cadr result) (caddr result) (list nil nil))))))))))

(defun h4-api-build-proof-ready-with-cache (world statement measures hints tables cache)
  (h4-api-finish-draft statement (h4-api-proof-draft world statement measures hints tables) cache))

(defun h4-api-build-proof-ready-with-templates (world statement measures hints tables)
  (car (h4-api-build-proof-ready-with-cache world statement measures hints tables :uncached)))

(defun h4-api-build-proof-ready (world statement measures hints)
  (h4-api-build-proof-ready-with-templates world statement measures hints nil))

(defun h4-api-build-proof-with-support (world statement measures hints)
  (proof-with-checked-results ((world (h4-api-use-core-support world)))
    (h4-api-build-proof-ready world statement measures hints)))

(defun h4-api-statement-known-p (world statement)
  (let* ((name (h4-book-run-statement-name statement))
         (proof (library-library-proof (h4-api-world-library world))))
    (or (assoc-equal name (proof-proof-facts proof))
        (assoc-equal name (proof-proof-definitions proof)))))

(defun h4-api-build-proof (context earlier statement measures hints)
  (proof-with-checked-results
      ((world (h4-api-library-context-prefix context earlier)))
    (if (h4-api-statement-known-p world statement)
        nil
      (proof-with-checked-results ((first (h4-api-optional (h4-api-special world statement))))
        (if first
            first
          (h4-api-build-proof-with-support world statement measures hints))))))

(defun h4-api-solve (context earlier statement measures hints)
  (h4-api-optional
   (proof-with-checked-results ((parsed (h4-api-parsed statement)))
     (h4-api-build-proof context earlier parsed measures hints))))

(defun h4-api-relevant-measures (definitions measures relevant)
  (if (endp definitions)
      relevant
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (let ((name (car definition)))
        (h4-api-relevant-measures (cdr definitions) measures
                                  (table-put relevant name (table-get measures name nil)))))))

(defun h4-api-prove-checked (statement earlier library aids)
  (proof-with-checked-results ((target (h4-api-parsed statement)))
    (let ((name (h4-book-run-statement-name target)))
      (if (not name)
          nil
        (proof-with-checked-results
            ((context (h4-api-library-context (h4-api-lines library)))
             (aid-info (h4-api-aid-info (h4-api-lines aids)))
             (previous (h4-api-lines earlier))
             (relevant (if (equal (h4-book-run-statement-kind target) "define")
                           (h4-api-relevant-measures
                            (cdr (h4-book-run-statement-fields target)) (car aid-info) nil)
                         nil)))
          (h4-api-solve context previous statement relevant
                        (list (cons name (table-get (cadr aid-info) name nil)))))))))

(defun h4-api-prove (statement earlier library aids)
  (let ((result (h4-api-prove-checked statement earlier library aids)))
    (if (failure-p result) nil result)))
