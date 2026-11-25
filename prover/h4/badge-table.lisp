(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-badge-table-hons* (proof-sym "HONS-ASSOC-EQUAL" "ACL2"))
(defconst *h4-badge-table-hons-equal* (proof-sym "HONS-EQUAL" "ACL2"))
(defconst *h4-badge-table-miss* (proof-sym "H4-HONS-CONS-MISS" "ACL2"))
(defconst *h4-badge-table-chars* (proof-sym "CHARS" "ACL2"))
(defconst *h4-badge-table-name* (proof-sym "NAME" "ACL2"))
(defconst *h4-badge-table-badge-value* (proof-sym "H4-BADGE-VALUE" "ACL2"))
(defconst *h4-badge-table-rest* (proof-sym "H4-TAIL" "ACL2"))
(defconst *h4-badge-table-atom* (proof-cl "ATOM"))
(defconst *h4-badge-table-char-code* (proof-cl "CHAR-CODE"))
(defconst *h4-badge-table-less* (proof-cl "<"))
(defconst *h4-badge-table-chunk-size* 48)

(defun h4-badge-table-selector-tail (offset tail)
  (declare (xargs :measure (nfix offset)))
  (if (zp offset)
      tail
    (h4-badge-table-selector-tail (1- offset) (list *library-cdr* tail))))

(defun h4-badge-table-selector (offset)
  (list *library-car*
        (h4-badge-table-selector-tail (if (eq offset t) 1 offset) *h4-badge-table-chars*)))

(defun h4-badge-table-max-name-length (keys maximum)
  (if (endp keys)
      maximum
    (proof-with-checked-results
        ((name (proof-term-at (car keys) 2))
         (size (h4-warrants-datum-length name)))
      (h4-badge-table-max-name-length (cdr keys) (max maximum size)))))

(defun h4-badge-table-code (key index missing)
  (proof-with-checked-results
      ((name (proof-term-at key 2))
       (size (h4-warrants-datum-length name)))
    (let ((position (if (< index 0) (+ size index) index)))
      (cond ((<= size index) missing)
            ((stringp name)
             (if (< position 0)
                 '(:failure "failure" "")
               (char-code (char name position))))
            ((< position 0) '(:failure "failure" ""))
            (t (proof-term-at name position))))))

(defun h4-badge-table-name-filter-code (key index)
  (h4-badge-table-code key index -1))

(defun h4-badge-table-table-filter-code (key index)
  (h4-badge-table-code key index 0))

(defun h4-badge-table-codes (keys index missing)
  (if (endp keys)
      nil
    (proof-with-checked-results
        ((code (h4-badge-table-code (car keys) index missing))
         (rest (h4-badge-table-codes (cdr keys) index missing)))
      (cons code rest))))

(defun h4-badge-table-name-filter-partition (keys index groups)
  (if (endp keys)
      groups
    (proof-with-checked-results ((code (h4-badge-table-name-filter-code (car keys) index)))
      (h4-badge-table-name-filter-partition
       (cdr keys) index (table-put groups code (append (table-get groups code nil)
                                                        (list (car keys))))))))

(defun h4-badge-table-count-accepted (codes accepted count)
  (if (endp codes)
      count
    (h4-badge-table-count-accepted (cdr codes) accepted
                                   (if (member-equal (car codes) accepted) (1+ count) count))))

(defun h4-badge-table-name-filter-decision-rank (index positive negative)
  (proof-with-checked-results
      ((positive-codes (h4-badge-table-codes positive index -1))
       (accepted (proof-unique positive-codes))
       (negative-codes (h4-badge-table-codes negative index -1)))
    (list (h4-badge-table-count-accepted negative-codes accepted 0) (len accepted) index)))

(defun h4-badge-table-name-filter-min-rank (offsets positive negative best)
  (if (endp offsets)
      best
    (proof-with-checked-results
        ((rank (h4-badge-table-name-filter-decision-rank (car offsets) positive negative)))
      (h4-badge-table-name-filter-min-rank
       (cdr offsets) positive negative (if (or (not best) (value-less rank best)) rank best)))))

(defun h4-badge-table-key-decisions (keys matched body)
  (if (endp keys)
      body
    (h4-badge-table-key-decisions
     (cdr keys) matched (proof-ite (proof-eq *h4-warrants-key* (proof-quote (car keys))) matched body))))

(defund h4-badge-table-name-filter-branches (positive negative offsets)
  (proof-with-checked-results
      ((rank (h4-badge-table-name-filter-min-rank offsets positive negative nil))
       (index (caddr rank))
       (remaining (remove-equal index offsets))
       (positives (h4-badge-table-name-filter-partition positive index nil))
       (negatives (h4-badge-table-name-filter-partition negative index nil)))
    (list (reverse (seq-sorted (table-keys positives))) positives negatives index remaining)))

(mutual-recursion
 (defun h4-badge-table-name-filter-decision (n positive negative offsets p functions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h4-badge-table-name-filter-decision"))
    ((endp negative) (list *proof-true* p functions))
    ((endp offsets)
     (list (h4-badge-table-key-decisions positive *proof-true* *proof-false*) p functions))
    (t (proof-with-checked-results
           ((branches (h4-badge-table-name-filter-branches positive negative offsets))
            (result (h4-badge-table-name-filter-groups
                     (1- n) (car branches) (cadr branches) (caddr branches) (cadddr branches)
                     (nth 4 branches) p functions *proof-false*))
            (body (car result))
            (p (cadr result))
            (functions (caddr result))
            (name (proof-sym (concatenate 'string "H4-WARRANT-NAME-TEST-" (decimal-text (len functions))) "ACL2"))
            (p (library-library-definition p name (list *h4-warrants-key* *h4-badge-table-chars*) body)))
         (list (list name *h4-warrants-key* *h4-badge-table-chars*) p (append functions (list name)))))))
 (defun h4-badge-table-name-filter-groups (n chars positives negatives index offsets p functions body)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h4-badge-table-name-filter-groups"))
    ((endp chars) (list body p functions))
    (t (let* ((code (car chars))
              (pattern (proof-quote (if (<= 0 code) (list "char" code) *proof-nil*))))
         (proof-with-checked-results
             ((result (h4-badge-table-name-filter-decision
                       (1- n) (table-get positives code nil) (table-get negatives code nil)
                       offsets p functions)))
           (h4-badge-table-name-filter-groups
            (1- n) (cdr chars) positives negatives index offsets (cadr result) (caddr result)
            (proof-ite (proof-eq (h4-badge-table-selector index) pattern) (car result) body))))))))

(defun h4-badge-table-filter-definition (p body)
  (let ((chars (list *h4-tactics-coerce* (list *h4-tactics-symbol-name* *h4-warrants-key*)
                     (proof-quote (proof-cl "LIST")))))
    (proof-with-checked-results
        ((body (proof-subst body (list (cons *h4-badge-table-chars* chars)))))
      (library-library-definition p *h4-warrants-filter* (list *h4-warrants-key*) body))))

(defun h4-badge-table-name-filter (p wanted excluded)
  (cond
   ((or (not (equal (len (proof-unique wanted)) (len wanted)))
        (intersectp-equal wanted excluded))
    '(:failure "failure" ""))
   ((and (endp wanted) (endp excluded)) '(:failure "failure" ""))
   (t (proof-with-checked-results
          ((maximum (h4-badge-table-max-name-length (append wanted excluded) 0))
           (offsets (seq-range 0 maximum 1))
           (result (h4-badge-table-name-filter-decision 1000000 wanted excluded offsets p nil))
           (p (h4-badge-table-filter-definition (cadr result) (car result))))
        (cons (append (caddr result) (list *h4-warrants-filter*)) p)))))

(defun h4-badge-table-table-filter-rank-cuts (ordered count middle index best)
  (if (endp (cdr ordered))
      best
    (let* ((low (car ordered))
           (high (cadr ordered))
           (rank (list (+ (abs (- count (* 2 middle))) index) index high)))
      (h4-badge-table-table-filter-rank-cuts
       (cdr ordered) count (1+ middle) index
       (if (and (not (equal low high)) (or (not best) (value-less rank best))) rank best)))))

(defun h4-badge-table-table-filter-split (keys offsets best)
  (if (endp offsets)
      best
    (let ((index (car offsets)))
      (proof-with-checked-results
          ((codes (h4-badge-table-codes keys index 0))
           (rank (h4-badge-table-table-filter-rank-cuts (seq-sorted codes) (len keys) 1 index best)))
        (h4-badge-table-table-filter-split keys (cdr offsets) rank)))))

(defun h4-badge-table-table-filter-declare (body p functions)
  (let ((name (proof-sym (concatenate 'string "H4-WARRANT-TABLE-TEST-" (decimal-text (len functions))) "ACL2")))
    (proof-with-checked-results
        ((p (library-library-definition p name (list *h4-warrants-key* *h4-badge-table-chars*) body)))
      (list (list name *h4-warrants-key* *h4-badge-table-chars*) p (append functions (list name))))))

(defun h4-badge-table-table-filter-keys (keys index high below)
  (if (endp keys)
      nil
    (proof-with-checked-results
        ((code (h4-badge-table-table-filter-code (car keys) index))
         (rest (h4-badge-table-table-filter-keys (cdr keys) index high below)))
      (if (iff (< code high) below) (cons (car keys) rest) rest))))

(defund h4-badge-table-table-filter-branches (keys offsets)
  (proof-with-checked-results
      ((branch (if (< 3 (len keys)) (h4-badge-table-table-filter-split keys offsets nil) nil)))
    (if (not branch)
        nil
      (let ((index (cadr branch))
            (high (caddr branch)))
        (proof-with-checked-results
            ((below (h4-badge-table-table-filter-keys keys index high t))
             (above (h4-badge-table-table-filter-keys keys index high nil)))
          (list (list *h4-badge-table-less* (list *h4-badge-table-char-code* (h4-badge-table-selector index))
                      (proof-quote high))
                below above))))))

(defun h4-badge-table-table-filter-decision (n keys offsets p functions)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h4-badge-table-table-filter-decision")
    (proof-with-checked-results ((branches (h4-badge-table-table-filter-branches keys offsets)))
      (if (not branches)
          (list (h4-badge-table-key-decisions keys *proof-false* *proof-true*) p functions)
        (proof-with-checked-results
            ((yes (h4-badge-table-table-filter-decision (1- n) (cadr branches) offsets p functions))
             (no (h4-badge-table-table-filter-decision (1- n) (caddr branches) offsets (cadr yes) (caddr yes))))
          (h4-badge-table-table-filter-declare (proof-ite (car branches) (car yes) (car no))
                                              (cadr no) (caddr no)))))))

(defun h4-badge-table-table-filter (p excluded)
  (proof-with-checked-results
      ((maximum (h4-badge-table-max-name-length excluded 0))
       (offsets (seq-range 0 maximum 1))
       (result (h4-badge-table-table-filter-decision 1000000 excluded offsets p nil))
       (p (h4-badge-table-filter-definition (cadr result) (car result))))
    (cons (seq-sorted (cons *h4-warrants-filter* (caddr result))) p)))

(defun h4-badge-table-literal-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h4-badge-table-lookup-miss (p)
  (let* ((proof (library-library-proof p))
         (key *h4-warrants-key*)
         (name *h4-badge-table-name*)
         (value *h4-badge-table-badge-value*)
         (rest *h4-badge-table-rest*)
         (entry (list *proof-cons* name value))
         (test (proof-eq key name))
         (alist (list *proof-cons* entry rest)))
    (proof-with-checked-results
        ((different (proof-proof-assume proof test nil))
         (is-cons (proof-proof-fact proof "consp-cons" (list (list *library-x* entry) (list *library-y* rest))))
         (is-pair (proof-proof-fact proof "consp-cons" (list (list *library-x* name) (list *library-y* value))))
         (reduction (proof-proof-unfold proof (list *h4-badge-table-hons* key alist)))
         (body (h4-badge-table-literal-at reduction 2))
         (first (library-library-axiom p "CAR-CONS" (list entry rest)))
         (tail (library-library-axiom p "CDR-CONS" (list entry rest)))
         (head (library-library-axiom p "CAR-CONS" (list name value)))
         (value (h4-tactics-tactics-normalize
                 p body (list is-cons is-pair different)
                 (list *h4-badge-table-atom* *proof-not* *h4-badge-table-hons-equal*) (list first tail head) nil))
         (result (proof-proof-chain proof reduction (list value)))
         (result-value (h4-badge-table-literal-at result 2)))
      (if (equal result-value (list *h4-badge-table-hons* key rest))
          (h4-tactics-tactics-guarded p test result nil)
        '(:failure "failure" "")))))

(defund h4-badge-table-exclude-entry (p entry rest premise filters)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((entry-key (proof-term-at entry 0))
         (name (proof-quote entry-key))
         (equal-test (proof-eq *h4-warrants-key* name))
         (same (proof-proof-assume proof equal-test t))
         (closed (proof-proof-rewrite proof premise same '(1 1)))
         (literal (proof-step-first closed))
         (value (h4-tactics-tactics-evaluate-closed p literal filters))
         (result (h4-badge-table-literal-at value 2)))
      (if (not (equal result *proof-false*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((unequal (proof-proof-rewrite proof closed value '(1)))
             (unequal (proof-proof-tidy proof unequal))
             (unequal (proof-proof-front proof unequal (proof-neg equal-test)))
             (data (h4-tactics-cdr-data entry))
             (value (proof-quote data))
             (rule (proof-proof-fact proof *h4-badge-table-miss*
                                     (list (list *h4-badge-table-name* name) (list *h4-badge-table-badge-value* value))))
             (skipped (proof-proof-prove-if proof rule unequal))
             (built (proof-proof-compute proof (list *proof-cons* name value) entry))
             (step (proof-proof-rewrite proof skipped built '(1 1 2 1))))
          (proof-proof-instantiate proof step (list (list *h4-badge-table-rest* rest))))))))

(defun h4-badge-table-table-at (table index)
  (let ((position (if (< index 0) (+ (len table) index) index)))
    (if (< position 0)
        '(:failure "failure" "")
      (proof-term-at table position))))

(defund h4-badge-table-lookup-chunk-entry (offset p table filters premise rest result)
  (proof-with-checked-results
      ((item (h4-badge-table-table-at table offset))
       (step (h4-badge-table-exclude-entry p item rest premise filters))
       (result (if result (proof-proof-chain (library-library-proof p) step (list result)) step)))
    (cons item result)))

(defun h4-badge-table-lookup-chunk-entries (remaining offset p table filters premise rest result)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      result
    (proof-with-checked-results
        ((entry (h4-badge-table-lookup-chunk-entry offset p table filters premise rest result)))
      (h4-badge-table-lookup-chunk-entries
       (1- remaining) (1- offset) p table filters premise
       (list *proof-cons* (proof-quote (car entry)) rest) (cdr entry)))))

(defun h4-badge-table-lookup-chunk-tail-place (depth)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      nil
    (cons 2 (h4-badge-table-lookup-chunk-tail-place (1- depth)))))

(defund h4-badge-table-lookup-chunk-fold-step (offset proof table result depth)
  (proof-with-checked-results
      ((item (h4-badge-table-table-at table offset))
       (tail (seq-slice table (1+ offset) :none))
       (datum (seq-slice table offset :none))
       (folded (proof-proof-compute
                proof (list *proof-cons* (proof-quote item) (proof-quote (or tail *proof-nil*))) datum)))
    (proof-proof-rewrite proof result folded (append '(1 1 2) (h4-badge-table-lookup-chunk-tail-place depth)))))

(defun h4-badge-table-lookup-chunk-fold (remaining offset proof table result)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      result
    (proof-with-checked-results
        ((result (h4-badge-table-lookup-chunk-fold-step offset proof table result (1- remaining))))
      (h4-badge-table-lookup-chunk-fold (1- remaining) (1- offset) proof table result))))

(defun h4-badge-table-lookup-chunk (p table low high filters previous old-suffix new-suffix)
  (let* ((proof (library-library-proof p))
         (predicate (list *h4-warrants-filter* *h4-warrants-key*))
         (count (- high low))
         (offset (1- high)))
    (proof-with-checked-results
        ((premise (proof-proof-assume proof predicate t))
         (result (h4-badge-table-lookup-chunk-entries count offset p table filters premise *h4-badge-table-rest* nil)))
      (if (not result)
          '(:failure "failure" "")
        (proof-with-checked-results
            ((result (proof-proof-instantiate proof result
                                              (list (list *h4-badge-table-rest*
                                                          (if old-suffix (list old-suffix) *proof-false*)))))
             (result (if old-suffix
                         (proof-with-checked-results ((previous-suffix (proof-proof-fact proof old-suffix nil)))
                           (proof-proof-rewrite
                            proof result previous-suffix
                            (append '(1 1 2) (h4-badge-table-lookup-chunk-tail-place count))))
                       result))
             (result (h4-badge-table-lookup-chunk-fold count offset proof table result))
             (suffix (proof-proof-fact proof new-suffix nil))
             (unfolded (proof-proof-symmetric proof suffix))
             (result (proof-proof-rewrite proof result unfolded '(1 1 2)))
             (previous-fact (proof-proof-fact proof previous nil))
             (previous-lookup (proof-proof-prove-if proof previous-fact premise))
             (predicate (proof-step-first premise))
             (combined (proof-proof-chain proof result (list previous-lookup))))
          (h4-tactics-tactics-guarded p predicate combined t))))))

(defun h4-badge-table-emit (p name step)
  (let* ((proof (library-library-proof p))
         (facts (proof-proof-facts proof))
         (clause (proof-step-clause step)))
    (if (assoc-equal name facts)
        '(:failure "failure" "")
      (proof-with-checked-results
          ((steps (h4-book-encoding-proof-lines step))
           (header (proof-line "lemma" (cons name clause)))
           (qed (proof-line "qed" nil)))
        (let ((entry (list "lemma" name (list (len steps)) (text-join "" (cons header (append steps (list qed)))))))
          (library-make-library
           (proof-proof-with-facts proof (table-put facts name clause))
           (append (library-library-entries p) (list entry))))))))

(defun h4-badge-table-excluded-keys (table)
  (if (endp table)
      nil
    (proof-with-checked-results
        ((key (proof-term-at (car table) 0))
         (rest (h4-badge-table-excluded-keys (cdr table))))
      (cons key rest))))

(defun h4-badge-table-suffix-name (index)
  (proof-sym (concatenate 'string "H4-PRIMITIVE-TABLE-SUFFIX-" (decimal-text index)) "ACL2"))

(defund h4-badge-table-certify-chunk (p start end table filters latest suffix name alias)
  (proof-with-checked-results
      ((p (library-library-definition p alias nil (proof-quote (seq-slice table start :none))))
       (step (h4-badge-table-lookup-chunk p table start end filters latest suffix alias)))
    (h4-badge-table-emit p name step)))

(defun h4-badge-table-certify-chunks (end p table filters latest suffix)
  (declare (xargs :measure (nfix end)))
  (if (zp end)
      (list p latest suffix)
    (let* ((start (max 0 (- end *h4-badge-table-chunk-size*)))
           (name (h4-badge-table-suffix-name start))
           (alias (proof-sym (concatenate 'string "H4-BADGE-TABLE-TAIL-" (decimal-text start)) "ACL2")))
      (proof-with-checked-results
          ((p (h4-badge-table-certify-chunk p start end table filters latest suffix name alias)))
        (h4-badge-table-certify-chunks start p table filters name alias)))))

(defun h4-badge-table-certify-finish (p getter predicate latest suffix)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((known (proof-proof-assume proof predicate t))
         (previous (proof-proof-fact proof latest nil))
         (absence (proof-proof-prove-if proof previous known))
         (absence (if suffix
                      (proof-with-checked-results ((tail (proof-proof-fact proof suffix nil)))
                        (proof-proof-rewrite proof absence tail '(1 1 2)))
                    absence))
         (hons-call (h4-tactics-tactics-normalize
                     p getter nil (list (proof-sym "HONS-GET" "ACL2")) nil nil))
         (getter-is-nil (proof-proof-chain proof hons-call (list absence)))
         (absent (h4-tactics-tactics-establish
                  p (proof-neg (list *h4-warrants-primitive* *h4-warrants-key*)) nil
                  (list *h4-warrants-primitive* *proof-not*) (list getter-is-nil) nil))
         (absence-literal (proof-step-first absent))
         (implication (h4-tactics-tactics-imply p (list *library-implies* predicate absence-literal) absent))
         (p (h4-badge-table-emit p *h4-warrants-primitive-absence* implication))
         (example (h4-warrants-tame-example p)))
      (h4-badge-table-emit p *h4-warrants-tame-example* example))))

(defun h4-badge-table-certify (p wanted)
  (proof-with-checked-results
      ((opened (proof-proof-unfold (library-library-proof p) (list *h4-warrants-primitive* *h4-warrants-key*)))
       (definition (h4-badge-table-literal-at opened 2))
       (parts (proof-list-of-length definition 4))
       (getter (cadr parts))
       (quoted-table (proof-term-at getter 2))
       (table (proof-term-at quoted-table 1))
       (excluded (h4-badge-table-excluded-keys table))
       (result (if (eq wanted :none)
                   (h4-badge-table-table-filter p excluded)
                 (h4-badge-table-name-filter p wanted excluded)))
       (filters (car result))
       (p (cdr result))
       (miss (h4-badge-table-lookup-miss p))
       (p (h4-badge-table-emit p *h4-badge-table-miss* miss))
       (predicate (list *h4-warrants-filter* *h4-warrants-key*))
       (empty (h4-tactics-tactics-normalize
               p (list *h4-badge-table-hons* *h4-warrants-key* *proof-false*) nil
               (list *h4-badge-table-hons* *h4-badge-table-atom* *proof-not*) nil nil))
       (latest (h4-badge-table-suffix-name (len table)))
       (base (h4-tactics-tactics-guarded p predicate empty t))
       (p (h4-badge-table-emit p latest base))
       (chunks (h4-badge-table-certify-chunks (len table) p table filters latest nil))
       (p (h4-badge-table-certify-finish (car chunks) getter predicate (cadr chunks) (caddr chunks))))
    (cons filters p)))
