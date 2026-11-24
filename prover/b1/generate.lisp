(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun b1-generate-admit-definitions (proof definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      proof
    (let ((fields (car definitions)))
      (if (and (true-listp fields) (= (len fields) 3) (true-listp (cadr fields)))
        (proof-with-checked-results
         ((next (proof-proof-add-definition proof (car fields) (cadr fields) (caddr fields))))
         (b1-generate-admit-definitions next (cdr definitions)))
        '(:failure "failure" "")))))

(defun b1-generate-admit-fact (lib name formula formulas)
  (let* ((proof (library-library-proof lib))
         (facts (table-put (proof-proof-facts proof) name (list formula)))
         (lib (library-library-with-proof lib (proof-proof-with-facts proof facts))))
    (cons lib (if (assoc-equal formula formulas)
                  formulas
                (table-put formulas formula name)))))

(defun b1-generate-admit-constraints (lib constraints formulas)
  (declare (xargs :measure (acl2-count constraints)))
  (cond
   ((null constraints) (cons lib formulas))
   ((atom constraints)
    '(:failure "failure" ""))
   (t
    (proof-with-checked-results
     ((fields (proof-list-of-length (car constraints) 2)))
     (let ((admitted (b1-generate-admit-fact lib (car fields) (cadr fields) formulas)))
       (b1-generate-admit-constraints (car admitted) (cdr constraints) (cdr admitted)))))))

(defun b1-generate-admit (lib word data formulas)
  (cond
   ((equal word "define")
    (proof-with-checked-results
     ((proof (b1-generate-admit-definitions (library-library-proof lib) (cdr data))))
     (cons (library-library-with-proof lib proof) formulas)))
   ((or (equal word "theorem") (equal word "axiom"))
    (proof-with-checked-results ((fields (proof-list-of-length data 2)))
      (b1-generate-admit-fact lib (car fields) (cadr fields) formulas)))
   ((equal word "constrain")
    (proof-with-checked-results ((constraints (proof-term-at data 1)))
      (if (equal constraints *proof-nil*)
          (cons lib formulas)
        (b1-generate-admit-constraints lib constraints formulas))))
   (t (cons lib formulas))))

(defun b1-generate-parse-line (raw)
  (proof-with-checked-results
   ((result (reader-reader-line (reader-reader (seq-slice raw 0 -1)))))
   (car result)))

(defun b1-generate-initial-world-lines (lines lib seen-reversed formulas)
  (declare (xargs :measure (acl2-count lines)))
  (if (endp lines)
      (list lib (reverse seen-reversed) formulas)
    (let ((raw (car lines)))
      (proof-with-checked-results ((statement (b1-generate-parse-line raw)))
        (if (member-equal raw seen-reversed)
            (b1-generate-initial-world-lines (cdr lines) lib seen-reversed formulas)
          (proof-with-checked-results
           ((admitted (b1-generate-admit lib (car statement) (cadr statement) formulas)))
           (b1-generate-initial-world-lines (cdr lines) (car admitted)
                                            (cons raw seen-reversed) (cdr admitted))))))))

(defun b1-generate-initial-world (library-lines)
  (proof-with-checked-results
   ((lib (library-library-build (library-library-init (proof-proof-init)))))
   (b1-generate-initial-world-lines library-lines lib nil nil)))

(defun b1-generate-add-new-member (member members)
  (if (member-equal member members)
      members
    (append members (list member))))

(defun b1-generate-certificate-conflict-p (stored-facts current-facts)
  (declare (xargs :measure (acl2-count stored-facts)))
  (if (endp stored-facts)
      nil
    (let ((present (assoc-equal (caar stored-facts) current-facts)))
      (or (and present (not (equal (cdr present) (cdar stored-facts))))
          (b1-generate-certificate-conflict-p (cdr stored-facts) current-facts)))))

(defun b1-generate-certificate-entries (entries auxiliaries reversed)
  (declare (xargs :measure (acl2-count entries)))
  (if (endp entries)
      (cons (reverse reversed) auxiliaries)
    (proof-with-checked-results ((name (proof-term-at (car entries) 1)))
      (if (member-equal name auxiliaries)
          (b1-generate-certificate-entries (cdr entries) auxiliaries reversed)
        (b1-generate-certificate-entries (cdr entries) (append auxiliaries (list name))
                                         (cons (car entries) reversed))))))

(defun b1-generate-certificate-install (certificate lib context auxiliaries)
  (let* ((proof (library-library-proof lib))
         (facts (proof-proof-facts proof))
         (required-context (cadr certificate))
         (stored-entries (nth 4 certificate))
         (stored-facts (nth 5 certificate))
         (stored-definitions (nth 6 certificate)))
    (if (or (not (subsetp-equal required-context context))
            (b1-generate-certificate-conflict-p stored-facts facts))
        (list nil lib auxiliaries)
      (proof-with-checked-results
       ((added (b1-generate-certificate-entries stored-entries auxiliaries nil)))
       (let* ((definitions (proof-proof-definitions proof))
              (next-proof (proof-proof-with-kind
                           (proof-make-proof (table-update facts stored-facts)
                                             (table-update definitions stored-definitions)
                                             (proof-proof-primitives proof))
                           (proof-proof-kind proof)))
              (next-entries (append (library-library-entries lib) (car added))))
         (list t (library-make-library next-proof next-entries) (cdr added)))))))

(defun b1-generate-measure-line (raw measures)
  (if (not (text-starts-with raw "(measure "))
      measures
    (proof-with-checked-results
     ((statement (b1-generate-parse-line raw))
      (fields (proof-list-of-length (cadr statement) 4)))
     (if (equal (caddr fields) *proof-ordinal-less*)
         (table-put measures (car fields) (cadr fields))
       measures))))

(defun b1-generate-measures-from-aids-lines (lines measures)
  (declare (xargs :measure (acl2-count lines)))
  (if (endp lines)
      measures
    (proof-with-checked-results ((next (b1-generate-measure-line (car lines) measures)))
      (b1-generate-measures-from-aids-lines (cdr lines) next))))

(defun b1-generate-measures-from-aids (aid-lines)
  (b1-generate-measures-from-aids-lines aid-lines nil))

(defun b1-generate-obligations (word data)
  (cond
   ((equal word "theorem")
    (proof-with-checked-results ((name (proof-term-at data 0))) (list name nil)))
   ((equal word "define")
    (proof-with-checked-results
     ((rulers (proof-term-at data 0))
      (calls (termination-recursive-calls rulers (cdr data))))
     (if (endp calls)
         (list nil nil)
       (proof-with-checked-results ((name (proof-term-at (cadr data) 0)))
         (list name calls)))))
   ((equal word "constrain")
    (proof-with-checked-results ((constraints (proof-term-at data 1)))
      (if (equal constraints *proof-nil*)
          (list nil nil)
        (proof-with-checked-results
         ((definitions (proof-term-at data 0))
          (first (proof-term-at definitions 0))
          (name (proof-term-at first 0)))
         (list name nil)))))
   (t (list nil nil))))

(defun b1-generate-proof-name-char-p (char)
  (and (characterp char)
       (let ((code (char-code char)))
         (or (and (<= 65 code) (<= code 90))
             (and (<= 48 code) (<= code 57))
             (= code 45)))))

(defun b1-generate-proof-name-width (chars width)
  (declare (xargs :measure (acl2-count chars)))
  (if (and (consp chars) (b1-generate-proof-name-char-p (car chars)))
      (b1-generate-proof-name-width (cdr chars) (1+ width))
    width))

(defun b1-generate-proof-name-prefix-width (chars)
  (cond ((not (eql (car chars) #\A)) 0)
        ((equal (take 11 chars) '(#\A #\C #\L #\2 #\: #\: #\S #\E #\L #\F #\-)) 11)
        ((equal (take 9 chars) '(#\A #\C #\L #\2 #\: #\: #\B #\1 #\-)) 9)
        (t 0)))

(defun b1-generate-proof-names (chars skipped found)
  (declare (xargs :measure (acl2-count chars)))
  (cond
   ((endp chars) found)
   ((posp skipped) (b1-generate-proof-names (cdr chars) (1- skipped) found))
   (t
    (let* ((prefix-width (b1-generate-proof-name-prefix-width chars))
           (suffix (nthcdr prefix-width chars)))
      (if (and (posp prefix-width) (b1-generate-proof-name-char-p (car suffix)))
          (let* ((width (b1-generate-proof-name-width suffix prefix-width))
                 (name (coerce (take width chars) 'string)))
            (b1-generate-proof-names (cdr chars) (1- width) (add-to-set-equal name found)))
        (b1-generate-proof-names (cdr chars) 0 found))))))

(defun b1-generate-required-entries-reversed (entries emitted needed selected)
  (declare (xargs :measure (acl2-count entries)))
  (if (endp entries)
      (cons selected emitted)
    (proof-with-checked-results ((entry (proof-list-of-length (car entries) 4)))
      (let ((name (cadr entry)))
        (if (member-equal name emitted)
            (b1-generate-required-entries-reversed (cdr entries) emitted needed selected)
          (proof-with-checked-results ((written (proof-write name)))
            (if (member-equal written needed)
                (b1-generate-required-entries-reversed
                 (cdr entries) (append emitted (list name))
                 (b1-generate-proof-names (coerce (cadddr entry) 'list) 0 needed)
                 (cons entry selected))
              (b1-generate-required-entries-reversed (cdr entries) emitted needed selected))))))))

(defun b1-generate-required-entries (entries emitted proof)
  (b1-generate-required-entries-reversed
   (reverse entries) emitted (b1-generate-proof-names (coerce proof 'list) 0 nil) nil))

(defun b1-generate-label (name)
  (proof-with-checked-results ((label (proof-term-at name 2)))
    (if (and (stringp label) (b1-logic-ascii-characters-p (coerce label 'list)))
        label
      '(:failure "failure" ""))))

(defun b1-generate-with-library (result lib)
  (if (failure-p result) (cons result lib) result))

(defun b1-generate-other-literal-p (clause formula)
  (declare (xargs :measure (acl2-count clause)))
  (and (consp clause)
       (or (not (equal (car clause) formula))
           (b1-generate-other-literal-p (cdr clause) formula))))

(defun b1-generate-theorem-proof (lib label formula formulas facts)
  (let ((known (assoc-equal formula formulas))
        (unproved (member-equal label *b1-theorems-unproved*)))
    (cond
     (known (cons (proof-proof-fact (library-library-proof lib) (cdr known) nil) lib))
     ((assoc-equal label *b1-theorems-recipes*)
      (b1-generate-with-library (b1-theorems-apply-recipe label lib formula) lib))
     (unproved (cons '(:failure "Unproved" "") lib))
     (t
      (let ((wrapper (b1-xdoc-types-tree-tag-wrapper lib formula)))
        (if wrapper
            (cons wrapper lib)
          (let* ((attempt (b1-generate-with-library (b1-search-automatic lib facts formula) lib))
                 (proof (car attempt)))
            (if (and (not (failure-p proof))
                     (b1-generate-other-literal-p (proof-step-clause proof) formula))
                (cons '(:failure "Unproved" "")
                      (cdr attempt))
              attempt))))))))

(defun b1-generate-prove-theorem (lib label name data formulas facts)
  (let ((formula (proof-term-at data 1)))
    (if (failure-p formula)
        (cons formula lib)
      (let* ((result (b1-generate-theorem-proof lib label formula formulas facts))
             (step (car result))
             (lib (cdr result)))
        (if (failure-p step)
            result
          (cons (proof-with-checked-results
                 ((step (proof-proof-subsume (library-library-proof lib) step (list formula))))
                 (proof-proof-entry "theorem" name (list name) (list step)))
                lib))))))

(defun b1-generate-functions (declarations)
  (declare (xargs :measure (acl2-count declarations)))
  (if (endp declarations)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car declarations) 0))
      (rest (b1-generate-functions (cdr declarations))))
     (cons name rest))))

(defun b1-generate-named-witness (recipe lib names formulas)
  (case recipe
    (b1-witnesses-identity-witness (b1-witnesses-identity-witness lib names formulas))
    (b1-witnesses-successor-witness (b1-witnesses-successor-witness-with-library lib names formulas))
    (b1-witnesses-alist-type-witness (b1-witnesses-alist-type-witness-with-library lib names formulas))
    (b1-witnesses-list-type-witness (b1-witnesses-list-type-witness-with-library lib names formulas))
    (b1-witnesses-evaluator-witness (b1-witnesses-evaluator-witness-with-library lib names formulas))
    (otherwise '(:failure "Unproved" ""))))

(defun b1-generate-witness-proof (lib label data facts)
  (let ((recipe (assoc-equal label *b1-witnesses-witnesses*)))
    (proof-with-checked-results ((declarations (proof-term-at data 0)))
      (if recipe
          (proof-with-checked-results
           ((names (b1-generate-functions declarations))
            (formulas (proof-term-at data 1)))
           (b1-generate-named-witness (cdr recipe) lib names formulas))
        (proof-with-checked-results ((formulas (proof-term-at data 1)))
          (b1-witnesses-small-witnesses lib declarations formulas facts))))))

(defun b1-generate-prove-with-library (lib word data name calls aids formulas facts)
  (let ((label (b1-generate-label name)))
    (cond
     ((failure-p label) (cons label lib))
     ((equal word "define")
      (let ((unproved (member-equal label *b1-theorems-unproved*)))
        (if unproved
            (cons '(:failure "Unproved" "") lib)
          (let* ((result (b1-measures-termination-with-library lib (cdr data) calls aids))
                 (proofs (car result)))
            (if (failure-p proofs)
                result
              (cons (proof-proof-entry "measure" name (cons name (car proofs)) (cadr proofs))
                    (cdr result)))))))
     ((equal word "theorem") (b1-generate-prove-theorem lib label name data formulas facts))
     ((equal word "constrain")
      (let* ((result (b1-generate-with-library (b1-generate-witness-proof lib label data facts) lib))
             (proofs (car result)))
        (if (failure-p proofs)
            result
          (cons (proof-proof-entry "witness" name (cons name (car proofs)) (cadr proofs))
                (cdr result)))))
     (t (cons '(:failure "Unproved" "") lib)))))

(defun b1-generate-prove (lib word data name calls aids formulas facts)
  (let ((result (b1-generate-prove-with-library lib word data name calls aids formulas facts)))
    (if (failure-p (car result)) (car result) result)))

(defun b1-generate-sum-counts (counts total)
  (declare (xargs :measure (acl2-count counts)))
  (if (endp counts)
      total
    (b1-generate-sum-counts (cdr counts) (+ total (car counts)))))

(defun b1-generate-entry-names (entries names)
  (declare (xargs :measure (acl2-count entries)))
  (if (endp entries)
      names
    (proof-with-checked-results ((name (proof-term-at (car entries) 1)))
      (b1-generate-entry-names (cdr entries) (b1-generate-add-new-member name names)))))

(defun b1-generate-certificate-map (names table required)
  (declare (xargs :measure (acl2-count names)))
  (if (endp names)
      nil
    (let ((entry (assoc-equal (car names) table)))
      (if (and required (not entry))
          '(:failure "failure" "")
        (proof-with-checked-results
         ((rest (b1-generate-certificate-map (cdr names) table required)))
         (if entry (cons entry rest) rest))))))

(defun b1-generate-try-certificates (certificates lib context auxiliaries)
  (declare (xargs :measure (acl2-count certificates)))
  (if (endp certificates)
      nil
    (let ((certificate (car certificates)))
      (proof-with-checked-results
       ((installed (b1-generate-certificate-install certificate lib context auxiliaries)))
       (if (car installed)
           (list (list (caddr certificate) (cadddr certificate))
                 (cadr installed) (caddr installed))
         (b1-generate-try-certificates (cdr certificates) lib context auxiliaries))))))

(defun b1-generate-new-certificate (result raw context-reversed cache auxiliaries)
  (let ((entry (car result))
        (proved-lib (cdr result)))
    (if (failure-p entry)
        (list entry proved-lib cache auxiliaries)
      (let* ((steps (b1-generate-sum-counts (caddr entry) 0))
             (source (cadddr entry))
             (library-entries (library-library-entries proved-lib))
             (proof (library-library-proof proved-lib)))
        (proof-with-checked-results
         ((names (b1-generate-entry-names library-entries nil))
          (facts (b1-generate-certificate-map names (proof-proof-facts proof) t))
          (definitions (b1-generate-certificate-map names (proof-proof-definitions proof) nil)))
         (let* ((certificate (list :b1-certificate (reverse context-reversed) steps source
                                   library-entries facts definitions))
                (cache (table-put cache raw
                                    (append (table-get cache raw nil) (list certificate)))))
           (proof-with-checked-results
            ((auxiliaries (b1-generate-entry-names library-entries auxiliaries)))
            (list (list steps source) proved-lib cache auxiliaries))))))))

(defun b1-generate-build-proof (lib word data name calls measures formulas facts raw
                               context-reversed cache auxiliaries)
  (proof-with-checked-results
   ((cached (b1-generate-try-certificates (table-get cache raw nil)
                                          lib context-reversed auxiliaries)))
   (if cached
       (list (car cached) (cadr cached) cache (caddr cached))
     (b1-generate-new-certificate
      (b1-generate-prove-with-library lib word data name calls measures formulas facts)
      raw context-reversed cache auxiliaries))))

(defun b1-generate-unproved-p (result)
  (and (failure-p result) (member-equal (cadr result) '("Unproved" "SearchBudgetExhausted"))))

(defun b1-generate-part-data (entries steps reversed-sources)
  (declare (xargs :measure (acl2-count entries)))
  (if (endp entries)
      (cons steps (reverse reversed-sources))
    (let ((entry (car entries)))
      (b1-generate-part-data (cdr entries) (b1-generate-sum-counts (caddr entry) steps)
                             (cons (cadddr entry) reversed-sources)))))

(defun b1-generate-obligation-output (lib result emitted name)
  (cond
   ((b1-generate-unproved-p result)
    (proof-with-checked-results ((source (proof-line "skip" (list name))))
      (list "skipped" 0 source (caddr result) emitted)))
   ((failure-p result) result)
   (t
    (let ((source (cadr result)))
      (proof-with-checked-results
       ((required (b1-generate-required-entries (library-library-entries lib) emitted source)))
       (let* ((parts (b1-generate-part-data (car required) (car result) nil))
              (source (text-join "" (append (cdr parts) (list source)))))
         (list "proved" (car parts) source "" (cdr required))))))))

(defun b1-generate-obligation (book index raw word data obligation lib measures formulas facts
                               context-reversed emitted cache auxiliaries)
  (let ((name (car obligation)))
    (if (not name)
        (list nil nil lib emitted cache auxiliaries)
      (proof-with-checked-results
       ((built (b1-generate-build-proof lib word data name (cadr obligation) measures formulas facts
                                        raw context-reversed cache auxiliaries))
        (output (b1-generate-obligation-output (cadr built) (car built) emitted name))
        (written (proof-write name)))
       (let* ((source (nth 2 output))
              (row (list book (decimal-text index) word written (car output)
                         (decimal-text (cadr output)) (decimal-text (length source)) (nth 3 output))))
         (list row source (cadr built) (nth 4 output) (caddr built) (cadddr built)))))))

(defun b1-generate-index-fact (lib facts name)
  (let ((known (assoc-equal name (proof-proof-facts (library-library-proof lib)))))
    (if known
        (b1-search-fact-index-add facts name (cdr known))
      '(:failure "failure" ""))))

(defun b1-generate-index-constraints (lib facts constraints)
  (declare (xargs :measure (acl2-count constraints)))
  (if (endp constraints)
      facts
    (proof-with-checked-results ((next (b1-generate-index-fact lib facts (caar constraints))))
      (b1-generate-index-constraints lib next (cdr constraints)))))

(defun b1-generate-index-statement (lib facts word data)
  (cond ((or (equal word "theorem") (equal word "axiom"))
         (b1-generate-index-fact lib facts (car data)))
        ((and (equal word "constrain") (not (equal (cadr data) *proof-nil*)))
         (b1-generate-index-constraints lib facts (cadr data)))
        (t facts)))

(defun b1-generate-book-lines (lines book index lib measures seen formulas facts context-reversed
                               emitted cache auxiliaries rows-reversed sources-reversed)
  (declare (xargs :measure (acl2-count lines)))
  (if (endp lines)
      (cons (list (reverse rows-reversed) sources-reversed) cache)
    (let ((raw (car lines)))
      (proof-with-checked-results ((statement (b1-generate-parse-line raw)))
        (if (member-equal raw seen)
            (b1-generate-book-lines (cdr lines) book (1+ index) lib measures seen formulas facts
                                    context-reversed emitted cache auxiliaries rows-reversed
                                    sources-reversed)
          (let ((word (car statement))
                (data (cadr statement)))
            (proof-with-checked-results
             ((obligation (b1-generate-obligations word data))
              (generated (b1-generate-obligation book index raw word data obligation lib measures
                                                 formulas facts context-reversed emitted cache
                                                 auxiliaries))
              (admitted (b1-generate-admit (caddr generated) word data formulas))
              (facts (b1-generate-index-statement (car admitted) facts word data)))
             (b1-generate-book-lines
              (cdr lines) book (1+ index) (car admitted) measures (cons raw seen) (cdr admitted) facts
              (cons raw context-reversed) (nth 3 generated) (nth 4 generated) (nth 5 generated)
              (if (car generated) (cons (car generated) rows-reversed) rows-reversed)
              (if (car generated) (cons (cadr generated) sources-reversed) sources-reversed)))))))))

(defun b1-generate-generate (book count world cache statement-lines aid-lines)
  (let ((lib (car world)))
    (proof-with-checked-results
     ((measures (b1-generate-measures-from-aids aid-lines))
      (facts (b1-search-fact-index-init lib))
      (auxiliaries (b1-generate-entry-names (library-library-entries lib) nil))
      (result (b1-generate-book-lines statement-lines book 1 lib measures (cadr world) (caddr world)
                                       facts nil nil (if (eq cache :none) nil cache) auxiliaries
                                       nil nil)))
     (let* ((rows (caar result))
            (actual-count (len rows)))
       (if (equal actual-count count)
           (cons (list rows (text-join "" (reverse (cadar result)))) (cdr result))
         '(:failure "failure" ""))))))
