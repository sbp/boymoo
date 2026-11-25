(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-finite-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *h2-finite-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))

(defun h2-finite-truth (search term)
  (h2-book-logic-with-results search
      (((truth search)
        (h2-book-logic-search-call search :truth (list term (h2-search-context-init) nil))))
    (cons (or (car truth) '(:failure "failure" ""))
          search)))

(defun h2-finite-branch-select (search direct)
  (let ((proof (h2-book-logic-proof search)))
    (h2-book-logic-with-results search
        ((body (h2-book-logic-first-at direct 2))
         (test (proof-term-at body 1))
         ((normalized search)
          (h2-book-logic-search-call search :normalize
                                     (list test (h2-search-context-init) nil nil)))
         (equality (or (car normalized)
                       '(:failure "failure" "")))
         (direct (proof-proof-rewrite proof direct equality '(1 2 1)))
         (body (h2-book-logic-first-at direct 2))
         (test (proof-term-at body 1))
         ((truth search)
          (h2-book-logic-search-call search :truth (list test (cdr normalized) nil)))
         (evidence (or (car truth)
                       '(:failure "failure" ""))))
      (cons (h2-book-logic-select-body search direct evidence) search))))

(defun h2-finite-branch-assoc (proof direct element entry)
  (proof-with-checked-results
      ((pair (h2-book-logic-first-at element 2))
       (key (proof-term-at entry 0))
       (pair-car (proof-proof-compute proof (list *library-car* pair) key))
       (direct (proof-proof-rewrite proof direct pair-car '(1 2 1 2))))
    (proof-proof-rewrite proof direct element '(1 2 2))))

(defun h2-finite-branch (search function key data)
  (h2-book-logic-with-saved-result search
    (let* ((proof (h2-book-logic-proof search))
           (table (proof-quote data)))
      (h2-book-logic-with-results search
          ((direct (proof-proof-unfold proof (list function key table)))
           ((direct search) (h2-finite-branch-select search direct)))
        (if (equal data *proof-nil*)
            (cons direct search)
          (h2-book-logic-with-results search
              ((entry (proof-term-at data 0))
               (element (proof-proof-compute proof (list *library-car* table) entry))
               (place (if (equal function *h2-finite-member*) '(1 2 1 2) '(1 2 1 2 1)))
               (direct (proof-proof-rewrite proof direct element place))
               (direct (if (equal function *h2-finite-assoc*)
                           (h2-finite-branch-assoc proof direct element entry)
                         direct))
               (value (h2-book-logic-first-at direct 2))
               (if-true (proof-proof-if-true proof value))
               (yes (proof-proof-chain proof direct (list if-true)))
               (if-false (proof-proof-if-false proof value))
               (no (proof-proof-chain proof direct (list if-false)))
               (cdr-step (proof-proof-compute proof (list *library-cdr* table)
                                              (or (cdr data) *proof-nil*)))
               (no (proof-proof-rewrite proof no cdr-step '(1 2 2)))
               (test (proof-term-at value 1)))
            (cons (list test yes no) search)))))))

(defun h2-finite-empty-transport (search empty)
  (let ((proof (h2-book-logic-proof search)))
    (proof-with-checked-results ((not-nil (h2-search-not-nil-in-proof search proof)))
      (library-library-transport-argument (h2-search-search-library search) not-nil empty 1))))

(defun h2-finite-table-inclusion-call (fn data key)
  (list fn key (proof-quote (or data *proof-nil*))))

(defun h2-finite-table-inclusion-transport (search absent key required included)
  (if (not included)
      (cons absent search)
    (let ((proof (h2-book-logic-proof search)))
      (h2-book-logic-with-results search
          (((member-branch search) (h2-finite-branch search *h2-finite-member* key required))
           (member-tail (proof-proof-symmetric proof (caddr member-branch))))
        (cons (proof-proof-rewrite proof absent member-tail '(2 1)) search)))))

(defun h2-finite-table-inclusion (search key required available function)
  (declare (xargs :measure (acl2-count available)))
  (let* ((proof (h2-book-logic-proof search))
         (goal (h2-finite-table-inclusion-call function available key))
         (guard (proof-neg (h2-finite-table-inclusion-call *h2-finite-member* required key))))
    (cond
     ((endp required)
      (h2-book-logic-with-saved-result search
        (h2-book-logic-with-results search
            (((empty search) (h2-finite-branch search *h2-finite-member* key *proof-nil*))
             (step (h2-finite-empty-transport search empty)))
          (cons (proof-proof-subsume proof step (list goal guard)) search))))
     ((endp available)
      (cons '(:failure "tactic-inapplicable" "") search))
     (t
      (h2-book-logic-with-saved-result search
        (h2-book-logic-with-results search
            (((branch search) (h2-finite-branch search function key available))
             (test (car branch))
             (yes (cadr branch))
             (no (caddr branch))
             (quoted (proof-term-at test 2))
             (table-key (proof-term-at quoted 1))
             (included (equal (car required) table-key))
             ((smaller search)
              (h2-finite-table-inclusion search key (if included (cdr required) required)
                                         (cdr available) function))
             (absent (proof-proof-transport proof smaller no))
             ((absent search)
              (h2-finite-table-inclusion-transport search absent key required included))
             (present (h2-book-logic-first-at yes 2))
             ((truth search) (h2-finite-truth search present))
             (found (proof-proof-transport proof truth yes))
             (found (proof-proof-subsume proof found (list goal (proof-neg test) guard)))
             (result (proof-proof-cases proof test found absent)))
          (cons (proof-proof-subsume proof result (list goal guard)) search)))))))

(defun h2-finite-member-of-constant-walk (search key data cdr-step result)
  (declare (xargs :measure (acl2-count data)))
  (if (endp data)
      (cons '(:failure "tactic-inapplicable" "") search)
    (let* ((library (h2-search-search-library search))
           (proof (library-library-proof library)))
      (h2-book-logic-with-results search
          (((branch search) (h2-finite-branch search *h2-finite-member* key data))
           (test (car branch))
           (value (or (proof-proof-constant proof test)
                      '(:failure "failure" "")))
           (right (h2-book-logic-first-at value 2))
           (matches (not (equal right *proof-false*)))
           (evidence (if matches
                         (proof-proof-true-from-eq proof value)
                       (proof-with-checked-results ((false (h2-search-not-nil-in-proof search proof)))
                         (library-library-transport-argument library false value 1))))
           (step (proof-proof-discharge proof (if matches (cadr branch) (caddr branch)) evidence))
           (result (if result (proof-proof-chain proof result (list step)) step)))
        (if matches
            (h2-book-logic-with-results search
                ((right (h2-book-logic-first-at result 2))
                 ((truth search) (h2-finite-truth search right))
                 (present (proof-proof-transport proof truth result)))
              (cons (library-library-transport-argument library present cdr-step 1) search))
          (h2-finite-member-of-constant-walk search key (cdr data) cdr-step result))))))

(defun h2-finite-member-of-constant (search formula)
  (let ((proof (h2-book-logic-proof search)))
    (h2-book-logic-with-results search
        ((parts (proof-list-of-length formula 3))
         (selected (cadr parts))
         (table (caddr parts))
         (selected-arg (proof-term-at selected 1))
         (pair (proof-term-at selected-arg 1))
         (pair (proof-list-of-length pair 2))
         (tail (proof-term-at (cadr pair) 1))
         (cdr-step (proof-proof-compute proof selected tail))
         (key (h2-book-logic-first-at cdr-step 2))
         (data (proof-term-at table 1)))
      (h2-finite-member-of-constant-walk search key data cdr-step nil))))

(defun h2-finite-table-property-leaf (search formula leaf)
  (cond ((or (not leaf) (eq leaf :solve))
         (h2-book-logic-search-call search :solve (list formula nil nil)))
        ((eq leaf :member-of-constant) (h2-finite-member-of-constant search formula))
        ((consp (cdr leaf)) (cadr leaf))
        (t (cons (list :call :leaf search formula) search))))

(defun h2-finite-table-property-rewrite-leaf
    (proof function key template test yes formula proved)
  (if (equal function *h2-finite-member*)
      (proof-with-checked-results
          ((evidence (proof-proof-assume proof test t))
           (evidence (proof-proof-symmetric proof evidence)))
        (proof-proof-rewrite-result proof proved evidence formula key))
    (proof-with-checked-results ((evidence (proof-proof-symmetric proof yes)))
      (proof-proof-rewrite-result proof proved evidence template *proof-result*))))

(defun h2-finite-table-property-combine
    (search function key template test yes no parent formula proved previous)
  (let* ((proof (h2-book-logic-proof search))
         (parent-absent (proof-neg parent)))
    (proof-with-checked-results
        ((proved (h2-finite-table-property-rewrite-leaf
                  proof function key template test yes formula proved))
         (proved (proof-proof-subsume
                  proof proved (cons formula (append (cdr (proof-step-clause proved))
                                                     (list parent-absent)))))
         (tail (proof-proof-symmetric proof no))
         (absent (proof-proof-rewrite-result proof previous tail template *proof-result*))
         (absent (proof-proof-rewrite proof absent tail '(2 1)))
         (absent (proof-proof-subsume proof absent
                                      (list* formula parent-absent
                                             (proof-unique (cddr (proof-step-clause absent))))))
         (previous (proof-proof-cases proof test proved absent)))
      (proof-proof-subsume proof previous (list formula parent-absent)))))

(defun h2-finite-table-property-entry (search function key values template leaf previous)
  (h2-book-logic-with-results search
      (((branch search) (h2-finite-branch search function key values))
       (test (car branch))
       (yes (cadr branch))
       (no (caddr branch))
       (equality (proof-step-first yes))
       (parts (proof-list-of-length (cdr equality) 2))
       (parent (car parts))
       (present (cadr parts))
       (formula (proof-subst template (list (cons *proof-result* parent))))
       (leaf-goal
        (if (equal function *h2-finite-member*)
            (proof-with-checked-results ((value (proof-term-at test 2)))
              (proof-subst formula (list (cons key value))))
          (proof-subst template (list (cons *proof-result* present)))))
       ((proved search) (h2-finite-table-property-leaf search leaf-goal leaf)))
    (cons (h2-finite-table-property-combine
           search function key template test yes no parent formula proved previous)
          search)))

(defun h2-finite-table-property-walk (search function key values template leaf previous)
  (declare (xargs :measure (acl2-count values)))
  (if (endp values)
      (list previous search leaf)
    (let* ((tail (h2-finite-table-property-walk
                  search function key (cdr values) template leaf previous))
           (previous (car tail))
           (search (cadr tail))
           (leaf (caddr tail)))
      (if (h2-book-logic-stop-p previous)
          tail
        (let ((result (h2-book-logic-with-saved-result search
                        (h2-finite-table-property-entry
                         search function key values template leaf previous))))
          (list (car result) (cdr result)
                (if (consp leaf) (cons t (cddr leaf)) leaf)))))))

(defun h2-finite-table-property (search function key values template leaf)
  (h2-book-logic-with-saved-result search
    (let ((proof (h2-book-logic-proof search)))
      (h2-book-logic-with-results search
          (((empty search) (h2-finite-branch search function key *proof-nil*))
           (empty-call (h2-book-logic-first-at empty 1))
           (impossible (h2-finite-empty-transport search empty))
           (base (proof-subst template (list (cons *proof-result* empty-call))))
           (previous (proof-proof-subsume proof impossible (list base (proof-neg empty-call)))))
        (let ((result (h2-finite-table-property-walk
                       search function key values template leaf previous)))
          (cons (car result) (cadr result)))))))

(defun h2-finite-lookup-data-walk (n search term function key)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "fuel" "h2-finite-lookup-data-walk") search)
    (h2-book-logic-with-results search
        ((head (proof-term-at term 0)))
      (if (equal head function)
          (h2-book-logic-with-results search
              ((actual-key (proof-term-at term 1)))
            (if (not (equal actual-key key))
                (cons '(:failure "tactic-inapplicable" "") search)
              (h2-book-logic-with-results search
                  ((table (proof-term-at term 2)))
                (cons (proof-term-at table 1) search))))
        (h2-book-logic-with-results search
            (((normalized search)
              (h2-book-logic-search-call search :normalize
                                         (list term (h2-search-context-init) nil nil))))
          (if (not (car normalized))
              (cons '(:failure "tactic-inapplicable" "") search)
            (h2-book-logic-with-results search
                ((next (h2-book-logic-first-at (car normalized) 2)))
              (h2-finite-lookup-data-walk (1- n) search next function key))))))))

(defun h2-finite-lookup-data (search term function key)
  (h2-book-logic-with-saved-result search
    (h2-book-logic-with-results search
        ((search (h2-book-logic-set-rules search "" nil "" 80)))
      (h2-finite-lookup-data-walk 1000000 search term function key))))

(defun h2-finite-character-proof-member-table (predicate search standard key)
  (let ((proof (h2-book-logic-proof search)))
    (h2-book-logic-with-results search
        ((unfolded (proof-proof-unfold proof (list predicate key)))
         (body (h2-book-logic-first-at unfolded 2))
         (member-term
          (if (equal predicate standard)
              (proof-term-at body 1)
            (proof-with-checked-results ((interior (proof-term-at body 2)))
              (proof-term-at interior 1)))))
      (h2-finite-lookup-data search member-term *h2-finite-member* key))))

(defun h2-finite-character-proof-finite (name function data template leaf search key)
  (let ((label (concatenate 'string "SELF-H2-" name)))
    (if (h2-book-logic-has-fact search label)
        (cons label search)
      (h2-book-logic-with-results search
          ((search (h2-book-logic-set-rules search "" nil "" 80))
           ((step search)
            (h2-finite-table-property search function key data template (or leaf :solve)))
           (claim (proof-step-first step))
           (search (h2-book-logic-add-lemma search (concatenate 'string "H2-" name)
                                            claim step (cdr (proof-step-clause step)))))
        (cons label search)))))

(defun h2-finite-character-proof-inclusion (name required available function search key)
  (let ((label (concatenate 'string "SELF-H2-" name)))
    (if (h2-book-logic-has-fact search label)
        (cons label search)
      (h2-book-logic-with-results search
          ((search (h2-book-logic-set-rules search "" nil "" 80))
           ((step search) (h2-finite-table-inclusion search key required available function))
           (claim (proof-step-first step))
           (search (h2-book-logic-add-lemma search (concatenate 'string "H2-" name)
                                            claim step (cdr (proof-step-clause step)))))
        (cons label search)))))

(defun h2-finite-character-proof-conversion
    (search theorem formula standard characterp-head key test direction source target case-source case-target)
  (let* ((proof (h2-book-logic-proof search))
         (conversion-name (concatenate 'string "CHAR-" direction "CASE"))
         (convert (proof-cl conversion-name)))
    (h2-book-logic-with-results search
        ((opening (proof-proof-unfold proof (list convert key)))
         (body (h2-book-logic-first-at opening 2))
         (conversion (proof-term-at body 2))
         (lookup (proof-term-at conversion 1))
         ((data search) (h2-finite-lookup-data search lookup *h2-finite-assoc* key)))
      (if (member-equal theorem '("CHARACTERP-CHAR-DOWNCASE" "CHARACTERP-CHAR-UPCASE"))
          (h2-book-logic-with-results search
              (((label search)
                (h2-finite-character-proof-finite
                 (concatenate 'string direction "CASE-LOOKUP-CHARACTER") *h2-finite-assoc*
                 data (list characterp-head (list *library-cdr* *proof-result*)) nil search key)))
            (h2-book-logic-derive
             search formula conversion-name
             (list label "STANDARD-CHAR-P-FORWARD-TO-CHARACTERP"
                   (concatenate 'string "CHARACTERP-" conversion-name "-NON-STANDARD"))
             nil 1 "" nil (list test) 80))
        (h2-book-logic-with-results search
            (((range-table search)
              (h2-finite-character-proof-member-table case-target search standard key))
             ((source-table search)
              (h2-finite-character-proof-member-table case-source search standard key))
             ((found search)
              (h2-finite-character-proof-inclusion
               (concatenate 'string direction "CASE-DEFINED-FOR-CASE") source-table
               data *h2-finite-assoc* search key))
             ((standard-table search)
              (h2-finite-character-proof-member-table standard search standard key))
             ((standard-range search)
              (h2-finite-character-proof-inclusion
               (concatenate 'string target "-CASE-IN-STANDARD") range-table standard-table
               *h2-finite-member* search key))
             (ranged (list *h2-finite-member* (list *library-cdr* *proof-result*)
                           (proof-quote range-table)))
             ((label search)
              (h2-finite-character-proof-finite
               (concatenate 'string direction "CASE-RESULT-RANGE") *h2-finite-assoc* data ranged
               :member-of-constant search key)))
          (h2-book-logic-derive
           search formula (concatenate 'string source "-CASE-P " target "-CASE-P "
                                       conversion-name " STANDARD-CHAR-P")
           (list label found standard-range
                 (concatenate 'string source "-CASE-P-NON-STANDARD-IMPLIES-ALPHA-CHAR-P-NON-STANDARD")
                 "ALPHA-CHAR-P-NON-STANDARD-IMPLIES-CHARACTERP"
                 (concatenate 'string conversion-name "-MAPS-NON-STANDARD-TO-NON-STANDARD")
                 (concatenate 'string target "-CASE-P-NON-STANDARD-" conversion-name "-NON-STANDARD"))
           nil 1 "" nil (list test) 80))))))

(defun h2-finite-character-proof (search theorem formula)
  (let* ((standard (proof-cl "STANDARD-CHAR-P"))
         (characterp-head (proof-cl "CHARACTERP"))
         (alpha (proof-cl "ALPHA-CHAR-P"))
         (key *library-x*)
         (test (list standard key)))
    (if (equal theorem "STANDARD-CHAR-P-FORWARD-TO-CHARACTERP")
        (h2-book-logic-with-results search
            (((table search) (h2-finite-character-proof-member-table standard search standard key))
             ((label search)
              (h2-finite-character-proof-finite "STANDARD-CHARACTER-TABLE" *h2-finite-member*
                                                table (list characterp-head key) nil search key)))
          (h2-book-logic-derive search formula "STANDARD-CHAR-P" (list label) nil 1 "" nil nil 80))
      (let* ((up (member-equal theorem '("LOWER-CASE-P-FORWARD-TO-ALPHA-CHAR-P"
                                        "CHARACTERP-CHAR-UPCASE" "UPPER-CASE-P-CHAR-UPCASE")))
             (direction (if up "UP" "DOWN"))
             (source (if up "LOWER" "UPPER"))
             (target (if up "UPPER" "LOWER"))
             (source-name (concatenate 'string source "-CASE-P"))
             (case-source (proof-cl source-name))
             (case-target (proof-cl (concatenate 'string target "-CASE-P"))))
        (if (member-equal theorem '("LOWER-CASE-P-FORWARD-TO-ALPHA-CHAR-P"
                                    "UPPER-CASE-P-FORWARD-TO-ALPHA-CHAR-P"))
            (h2-book-logic-with-results search
                (((source-table search)
                  (h2-finite-character-proof-member-table case-source search standard key))
                 ((alpha-table search)
                  (h2-finite-character-proof-member-table alpha search standard key))
                 ((label search)
                  (h2-finite-character-proof-inclusion
                   (concatenate 'string source "-ALPHA-TABLE")
                   source-table alpha-table *h2-finite-member* search key))
                 (fact
                  (concatenate 'string source-name "-NON-STANDARD-IMPLIES-ALPHA-CHAR-P-NON-STANDARD")))
              (h2-book-logic-derive search formula (concatenate 'string source-name " ALPHA-CHAR-P")
                                    (list label fact) nil 1 "" nil (list test) 80))
          (h2-finite-character-proof-conversion search theorem formula standard characterp-head key test
                                                direction source target case-source case-target))))))
