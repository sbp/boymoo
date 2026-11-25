(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-rewriting-atom* (proof-cl "ATOM"))
(defconst *l1-rewriting-endp* (proof-cl "ENDP"))
(defconst *l1-rewriting-descent*
  (list (cons *library-car* "built-in-clause-2")
        (cons *library-cdr* "built-in-clause-3")))

(mutual-recursion
 (defun l1-rewriting-match (pattern term bindings)
   (declare (xargs :measure (1+ (* 2 (acl2-count pattern)))))
   (cond ((not (proof-compound pattern))
          (let ((entry (assoc-equal pattern bindings)))
            (if entry
                (cons (equal (cdr entry) term) bindings)
              (cons t (table-put bindings pattern term)))))
         ((proof-is-call pattern *proof-quote*)
          (cons (equal pattern term) bindings))
         ((or (not (proof-compound term))
              (not (equal (len pattern) (len term))))
          (cons nil bindings))
         ((endp pattern) '(:failure "failure" ""))
         ((not (equal (car pattern) (car term))) (cons nil bindings))
         (t (l1-rewriting-match-arguments (cdr pattern) (cdr term) bindings))))
 (defun l1-rewriting-match-arguments (patterns terms bindings)
   (declare (xargs :measure (* 2 (acl2-count patterns))))
   (if (endp patterns)
       (cons t bindings)
     (proof-with-checked-results
         ((matched (l1-rewriting-match (car patterns) (car terms) bindings)))
       (if (car matched)
           (l1-rewriting-match-arguments (cdr patterns) (cdr terms) (cdr matched))
         matched)))))

(mutual-recursion
 (defun l1-rewriting-variable-set (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond ((not (proof-compound term)) (list term))
         ((proof-is-call term *proof-quote*) nil)
         (t (l1-rewriting-argument-variables (cdr term)))))
 (defun l1-rewriting-argument-variables (terms)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (if (endp terms)
       nil
     (union-equal (l1-rewriting-variable-set (car terms))
                  (l1-rewriting-argument-variables (cdr terms))))))

(mutual-recursion
 (defun l1-rewriting-dump-key (datum)
   (declare (xargs :measure (1+ (* 2 (acl2-count datum)))))
   (cond ((stringp datum)
          (concatenate 'string "\""
                       (text-replace (text-replace datum "\\" "\\\\") "\"" "\\\"")
                       "\""))
         ((consp datum)
          (concatenate 'string "("
                       (text-join " " (l1-rewriting-dump-keys datum)) ")"))
         ((integerp datum) (decimal-text datum))
         ((rationalp datum)
          (concatenate 'string (decimal-text (numerator datum)) "/"
                       (decimal-text (denominator datum))))
         ((eq datum t) "t")
         (t "()")))
 (defun l1-rewriting-dump-keys (data)
   (declare (xargs :measure (* 2 (acl2-count data))))
   (if (endp data)
       nil
     (cons (l1-rewriting-dump-key (car data))
           (l1-rewriting-dump-keys (cdr data))))))

(mutual-recursion
 (defun l1-rewriting-size (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
       1
     (1+ (l1-rewriting-argument-size (cdr term)))))
 (defun l1-rewriting-argument-size (terms)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (if (endp terms)
       0
     (+ (l1-rewriting-size (car terms))
        (l1-rewriting-argument-size (cdr terms))))))

(mutual-recursion
 (defun l1-rewriting-calls (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
       nil
     (cons term (l1-rewriting-argument-calls (cdr term)))))
 (defun l1-rewriting-argument-calls (terms)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (if (endp terms)
       nil
     (append (l1-rewriting-calls (car terms))
             (l1-rewriting-argument-calls (cdr terms))))))

(defun l1-rewriting-structural-value (n body)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "l1-rewriting-structural-value"))
        ((proof-is-call body *termination-return-last*)
         (l1-rewriting-structural-value (1- n) (car (last body))))
        (t body)))

(defun l1-rewriting-descending-calls (calls name position children)
  (if (endp calls)
      nil
    (let ((call (car calls)))
      (proof-with-checked-results
          ((actual (and (proof-is-call call name) (proof-term-at call position)))
           (descending (and (proof-is-call call name) (member-equal actual children)))
           (rest (l1-rewriting-descending-calls (cdr calls) name position children)))
        (if descending
            (cons call rest)
          rest)))))

(defun l1-rewriting-structural-argument (name definition)
  (proof-with-checked-results
      ((parts (proof-list-of-length definition 2))
       (body (l1-rewriting-structural-value 1000000 (cadr parts))))
    (and (proof-is-call body *proof-if*)
      (proof-with-checked-results ((test (proof-term-at body 1)))
        (and (or (proof-is-call test *proof-consp*)
                  (proof-is-call test *l1-rewriting-atom*)
                  (proof-is-call test *l1-rewriting-endp*))
          (proof-with-checked-results ((argument (proof-term-at test 1)))
            (and (member-equal argument (car parts))
              (proof-with-checked-results
                  ((index (seq-index (car parts) argument))
                   (descending
                    (l1-rewriting-descending-calls
                     (l1-rewriting-calls body) name (1+ index)
                     (list (list *library-car* argument)
                           (list *library-cdr* argument)))))
                (and descending (list (1+ index) (proof-unique descending)))))))))))

(defun l1-rewriting-pairs-to-map (pairs bindings)
  (if (endp pairs)
      bindings
    (l1-rewriting-pairs-to-map (cdr pairs)
                               (table-put bindings (caar pairs) (cadar pairs)))))

(defun l1-rewriting-changed-bindings (original actuals bindings)
  (if (or (endp original) (endp actuals))
      bindings
    (let ((old (car original))
          (new (car actuals)))
      (l1-rewriting-changed-bindings
       (cdr original) (cdr actuals)
       (if (or (proof-compound old) (equal old new))
           bindings
         (table-put bindings old new))))))

(defund l1-rewriting-recursive-substitution (formals call recursive-call)
  (proof-with-checked-results
      ((child (proof-subst recursive-call
                           (l1-rewriting-pairs-to-map (seq-zip formals (cdr call)) nil)))
       (bindings (l1-rewriting-changed-bindings (cdr call) (cdr child) nil))
       (applied (proof-subst call bindings)))
    (and (equal applied child) (table-items bindings))))

(defun l1-rewriting-equation-name (equation) (nth 1 equation))
(defun l1-rewriting-equation-pattern (equation) (nth 2 equation))
(defun l1-rewriting-equation-replacement (equation) (nth 3 equation))
(defun l1-rewriting-equation-hypothesis (equation) (nth 4 equation))
(defun l1-rewriting-equation-reverse (equation) (nth 5 equation))
(defun l1-rewriting-equation-can-expand (equation) (nth 6 equation))

(defun l1-rewriting-rewriter-proof (rewriter) (nth 1 rewriter))
(defun l1-rewriting-rewriter-equations (rewriter) (nth 2 rewriter))
(defun l1-rewriting-rewriter-propositions (rewriter) (nth 3 rewriter))
(defun l1-rewriting-rewriter-structural (rewriter) (nth 4 rewriter))

(defun l1-rewriting-append-to-index (index head value)
  (table-put index head (append (table-get index head nil) (list value))))

(defun l1-rewriting-index-proposition (propositions name proposition hypothesis)
  (if (and (proof-compound proposition)
           (not (proof-is-call proposition *proof-quote*))
           (or (eq hypothesis :none)
               (subsetp-equal (l1-rewriting-variable-set hypothesis)
                              (l1-rewriting-variable-set proposition))))
      (proof-with-checked-results ((head (proof-term-at proposition 0)))
        (l1-rewriting-append-to-index propositions head (list name proposition hypothesis)))
    propositions))

(defun l1-rewriting-index-equation (equations name pattern replacement
                                            hypothesis reverse can-expand)
  (if (and (proof-compound pattern) (not (proof-is-call pattern *proof-quote*)))
      (let* ((free (l1-rewriting-variable-set replacement))
             (free (if (eq hypothesis :none)
                       free
                     (union-equal free (l1-rewriting-variable-set hypothesis)))))
        (if (subsetp-equal free (l1-rewriting-variable-set pattern))
            (proof-with-checked-results ((head (proof-term-at pattern 0)))
              (l1-rewriting-append-to-index
               equations head (list :equation name pattern replacement
                                    hypothesis reverse (and can-expand (not reverse)))))
          equations))
    equations))

(defund l1-rewriting-index-fact (name clause definitions equations propositions structural)
  (if (not (equal (len clause) 1))
      (list equations propositions structural)
    (let* ((literal (car clause))
           (implies (proof-is-call literal *library-implies*)))
      (proof-with-checked-results
          ((parts (and implies (proof-list-of-length literal 3))))
        (let* ((hypothesis (if implies (cadr parts) :none))
               (equation (if implies (caddr parts) literal))
               (definition (assoc-equal name definitions)))
          (proof-with-checked-results
              ((propositions (if definition
                                 propositions
                               (l1-rewriting-index-proposition
                                propositions name equation hypothesis))))
            (if (not (proof-is-call equation *proof-equal*))
                (list equations propositions structural)
              (proof-with-checked-results
                  ((parts (proof-list-of-length equation 3))
                   (body (and definition (proof-term-at (cdr definition) 1)))
                   (dependencies (and definition (l1-witness-dependencies body)))
                   (can-expand (and definition (not (member-equal name dependencies))))
                   (argument (and definition (not can-expand)
                                  (l1-rewriting-structural-argument name (cdr definition))))
                   (structural (if argument (table-put structural name argument) structural))
                   (forward (l1-rewriting-index-equation
                             equations name (cadr parts) (caddr parts) hypothesis nil can-expand))
                   (equations (if definition
                                  forward
                                (l1-rewriting-index-equation
                                 forward name (caddr parts) (cadr parts) hypothesis t nil))))
                (list equations propositions structural)))))))))

(defun l1-rewriting-index-facts (facts definitions equations propositions structural)
  (if (endp facts)
      (list equations propositions structural)
    (proof-with-checked-results
        ((indices (l1-rewriting-index-fact
                   (caar facts) (cdar facts) definitions equations propositions structural)))
      (l1-rewriting-index-facts
       (cdr facts) definitions (car indices) (cadr indices) (caddr indices)))))

(defun l1-rewriting-rewriter-init (proof)
  (proof-with-checked-results
      ((indices (l1-rewriting-index-facts (proof-proof-facts proof)
                                         (proof-proof-definitions proof) nil nil nil)))
    (list* :rewriter proof indices)))

; Each fact retains its first position and the heads of the rules it supplied.
; An update visits only the buckets for those heads and for the new rules.
(defun l1-rewriting-replace-bucket-rules (rules replacements fact facts equationsp)
  (if (endp rules)
      replacements
    (let ((name (if equationsp (l1-rewriting-equation-name (car rules)) (caar rules))))
      (cond ((equal name (car fact))
             (l1-rewriting-replace-bucket-rules (cdr rules) replacements fact facts equationsp))
            ((and replacements (< (cadr fact) (cadr (assoc-equal name facts))))
             (append replacements rules))
            (t (cons (car rules)
                     (l1-rewriting-replace-bucket-rules
                      (cdr rules) replacements fact facts equationsp)))))))

(defun l1-rewriting-replace-buckets (heads index additions fact facts equationsp)
  (if (endp heads)
      index
    (let* ((head (car heads))
           (rules (l1-rewriting-replace-bucket-rules
                   (table-get index head nil) (table-get additions head nil)
                   fact facts equationsp)))
      (l1-rewriting-replace-buckets
       (cdr heads) (if rules (table-put index head rules) (table-without index head))
       additions fact facts equationsp))))

(defun l1-rewriting-append-buckets (additions index)
  (if (endp additions)
      index
    (let ((head (caar additions)))
      (l1-rewriting-append-buckets
       (cdr additions)
       (table-put index head (append (table-get index head nil) (cdar additions)))))))

; The prepared index holds the next position, fact records, the three rule
; maps, and any errors, keyed by fact name. An error matters at rewrite time.
(defun l1-rewriting-prepare-fact (name clause definitions index previous)
  (let* ((next (car index))
         (facts (cadr index))
         (position (if previous (cadr previous) next))
         (rules (l1-rewriting-index-fact name clause definitions nil nil nil))
         (error (and (failure-p rules) rules))
         (equations (and (not error) (car rules)))
         (propositions (and (not error) (cadr rules)))
         (structural (and (not error) (caddr rules)))
         (equation-heads (table-keys equations))
         (proposition-heads (table-keys propositions))
         (fact (list name position equation-heads proposition-heads))
         (errors (nth 5 index)))
    (list (if previous next (1+ next))
          (if previous (table-put facts name (cdr fact)) (cons fact facts))
          (if previous
              (l1-rewriting-replace-buckets
               (union-equal (caddr previous) equation-heads) (caddr index)
               equations fact facts t)
            (l1-rewriting-append-buckets equations (caddr index)))
          (if previous
              (l1-rewriting-replace-buckets
               (union-equal (cadddr previous) proposition-heads) (cadddr index)
               propositions fact facts nil)
            (l1-rewriting-append-buckets propositions (cadddr index)))
          (cond (structural (table-update (nth 4 index) structural))
                (previous (table-without (nth 4 index) name))
                (t (nth 4 index)))
          (if error (table-put errors name (cons position error))
            (table-without errors name)))))

(defun l1-rewriting-prepare-facts (facts definitions index)
  (declare (xargs :measure (acl2-count facts)))
  (if (endp facts)
      index
    (l1-rewriting-prepare-facts
     (cdr facts) definitions
     (l1-rewriting-prepare-fact (caar facts) (cdar facts) definitions index nil))))

(defun l1-rewriting-prepare (proof)
  (l1-rewriting-prepare-facts (proof-proof-facts proof) (proof-proof-definitions proof)
                             '(0 nil nil nil nil nil)))

(defun l1-rewriting-update-prepared (index proof names)
  (declare (xargs :measure (acl2-count names)))
  (if (endp names)
      index
    (let* ((name (car names))
           (clause (cdr (assoc-equal name (proof-proof-facts proof))))
           (previous (assoc-equal name (cadr index))))
      (l1-rewriting-update-prepared
       (l1-rewriting-prepare-fact name clause (proof-proof-definitions proof) index previous)
       proof (cdr names)))))

(defun l1-rewriting-first-index-error (errors first)
  (if (endp errors)
      (cdr first)
    (let ((error (cdar errors)))
      (l1-rewriting-first-index-error
       (cdr errors) (if (or (not first) (< (car error) (car first))) error first)))))

(defun l1-rewriting-rewriter-prepared (proof index)
  (or (l1-rewriting-first-index-error (nth 5 index) nil)
      (list :rewriter proof (caddr index) (cadddr index) (nth 4 index))))

(defund l1-rewriting-conjunction-p (term)
  (and (proof-is-call term *proof-if*)
       (proof-with-checked-results ((no (proof-term-at term 3)))
         (equal no *proof-false*))))

(defund l1-rewriting-derive-rule (rule proof term depth)
  (proof-with-checked-results ((matched (l1-rewriting-match (cadr rule) term nil)))
    (let ((hypothesis (caddr rule))
          (bindings (cdr matched)))
      (cond ((not (car matched)) nil)
            ((eq hypothesis :none)
             (proof-proof-fact proof (car rule) (table-items bindings)))
            ((or (null depth) (equal depth 0)) nil)
            (t (proof-with-checked-results ((condition (proof-subst hypothesis bindings)))
                 (list :hypothesis condition bindings)))))))

(mutual-recursion
 (defun l1-rewriting-derive-visit (n rewriter term evidence depth trail)
   (declare (xargs :measure (nfix n)))
   (let ((premise (assoc-equal term evidence))
         (proof (l1-rewriting-rewriter-proof rewriter)))
     (cond ((zp n) '(:failure "fuel" "l1-rewriting-derive-visit"))
           (premise (cdr premise))
           ((equal term *proof-true*) (l1-application-proof-prove proof term nil nil))
           ((or (member-equal term trail)
                (not (proof-compound term))
                (proof-is-call term *proof-quote*))
            nil)
           (t
            (let ((trail (cons term trail)))
              (proof-with-checked-results
                  ((conjunction (l1-rewriting-conjunction-p term))
                   (test (and conjunction
                              (l1-rewriting-derive-visit (1- n) rewriter (cadr term)
                                                          evidence depth trail)))
                   (result (and test
                                (l1-rewriting-derive-visit (1- n) rewriter (caddr term)
                                                            evidence depth trail))))
                (if result
                    (proof-with-checked-results ((selected (proof-proof-select proof term test)))
                      (proof-proof-transport proof result selected))
                  (proof-with-checked-results
                      ((head (proof-term-at term 0))
                       (rules (table-get (l1-rewriting-rewriter-propositions rewriter)
                                          head nil)))
                    (l1-rewriting-derive-rules (1- n) rules rewriter term
                                               evidence depth trail)))))))))
 (defun l1-rewriting-derive-rules (n rules rewriter term evidence depth trail)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "l1-rewriting-derive-rules"))
         ((endp rules) nil)
         (t
          (let ((proof (l1-rewriting-rewriter-proof rewriter)))
            (proof-with-checked-results
                ((result (l1-rewriting-derive-rule (car rules) proof term depth)))
              (cond ((not result)
                     (l1-rewriting-derive-rules (1- n) (cdr rules) rewriter term
                                                evidence depth trail))
                    ((not (eq (car result) :hypothesis)) result)
                    (t
                     (proof-with-checked-results
                         ((premise (l1-rewriting-derive-visit
                                    (1- n) rewriter (cadr result) evidence (1- depth) trail)))
                       (if premise
                           (proof-with-checked-results
                               ((fact (proof-proof-fact proof (caar rules)
                                                       (table-items (caddr result)))))
                             (proof-proof-modus-ponens proof fact premise))
                         (l1-rewriting-derive-rules (1- n) (cdr rules) rewriter term
                                                    evidence depth trail)))))))))))

(defund l1-rewriting-rewriter-derive (rewriter term evidence depth trail)
  (l1-rewriting-derive-visit 1000000 rewriter term evidence depth trail))

(defun l1-rewriting-rewriter-branch (rewriter term evidence)
  (let ((proof (l1-rewriting-rewriter-proof rewriter)))
    (proof-with-checked-results
        ((test (proof-term-at term 1))
         (premise (l1-application-consp-cons proof test))
         (premise (or premise (table-get evidence test nil)
                      (table-get evidence (proof-neg test) nil))))
      (cond (premise (proof-proof-select proof term premise))
            ((or (equal test *proof-true*) (equal test *proof-false*))
             (l1-application-proof-simplify proof term nil nil))
            (t
             (proof-with-checked-results
                 ((yes (l1-rewriting-rewriter-derive rewriter test evidence 3 nil))
                  (premise (or yes (l1-rewriting-rewriter-derive
                                    rewriter (proof-neg test) evidence 3 nil))))
               (and premise (proof-proof-select proof term premise))))))))

(defund l1-rewriting-structural-opening (proof opened)
  (proof-with-checked-results ((body (proof-rewritten-term opened)))
    (if (proof-is-call body *termination-return-last*)
        (proof-with-checked-results
            ((step (proof-proof-unfold proof body))
             (opened (proof-proof-chain proof opened (list step))))
          (list :continue opened))
      opened)))

(defun l1-rewriting-open-structural-body (n proof opened)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "l1-rewriting-open-structural-body")
    (let ((next (l1-rewriting-structural-opening proof opened)))
      (if (eq (car next) :continue)
          (l1-rewriting-open-structural-body (1- n) proof (cadr next))
        next))))

(defun l1-rewriting-rewriter-structural-branch (rewriter term evidence)
  (let ((proof (l1-rewriting-rewriter-proof rewriter)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof term))
         (opened (l1-rewriting-open-structural-body 1000000 proof opened))
         (head (proof-term-at term 0))
         (entry (or (assoc-equal head (l1-rewriting-rewriter-structural rewriter))
                    '(:failure "failure" "")))
         (position (cadr entry))
         (argument (proof-term-at term position))
         (constructor (l1-application-consp-cons proof (list *proof-consp* argument)))
         (literal (and constructor (proof-step-first constructor)))
         (evidence (if constructor (table-put evidence literal constructor) evidence))
         (body (proof-rewritten-term opened))
         (test (proof-term-at body 1))
         (simplified (l1-application-proof-simplify proof test (table-values evidence)
                                           (list *proof-not* *l1-rewriting-atom*
                                                 *l1-rewriting-endp*)))
         (opened (if simplified (proof-proof-rewrite proof opened simplified '(1 2 1))
                   opened))
         (body (proof-rewritten-term opened))
         (selected (l1-rewriting-rewriter-branch rewriter body evidence)))
      (and selected (proof-proof-chain proof opened (list selected))))))

(defund l1-rewriting-apply-equation (rule rewriter term evidence)
  (let ((proof (l1-rewriting-rewriter-proof rewriter)))
    (proof-with-checked-results
        ((matched (l1-rewriting-match (l1-rewriting-equation-pattern rule) term nil)))
      (and (car matched)
        (let ((bindings (cdr matched)))
          (proof-with-checked-results
              ((replacement (proof-subst (l1-rewriting-equation-replacement rule) bindings)))
            (and (not (or (equal replacement term)
                          (and (not (l1-rewriting-equation-can-expand rule))
                               (>= (l1-rewriting-size replacement) (l1-rewriting-size term)))))
              (let ((hypothesis (l1-rewriting-equation-hypothesis rule)))
                (proof-with-checked-results
                    ((condition (and (not (eq hypothesis :none))
                                     (proof-subst hypothesis bindings)))
                     (premise (and (not (eq hypothesis :none))
                                   (l1-rewriting-rewriter-derive
                                    rewriter condition evidence 3 nil))))
                  (and (or (eq hypothesis :none) premise)
                    (proof-with-checked-results
                        ((step (proof-proof-fact proof (l1-rewriting-equation-name rule)
                                                  (table-items bindings)))
                         (step (if premise (proof-proof-modus-ponens proof step premise) step)))
                      (if (l1-rewriting-equation-reverse rule)
                          (proof-proof-symmetric proof step)
                        step))))))))))))

(defun l1-rewriting-apply-equations (rules rewriter term evidence)
  (if (endp rules)
      nil
    (proof-with-checked-results
        ((step (l1-rewriting-apply-equation (car rules) rewriter term evidence)))
      (or step (l1-rewriting-apply-equations (cdr rules) rewriter term evidence)))))

(defund l1-rewriting-rewriter-at-root (rewriter term evidence)
  (let ((proof (l1-rewriting-rewriter-proof rewriter)))
    (proof-with-checked-results ((head (proof-term-at term 0)))
      (if (proof-compound head)
          (proof-proof-beta proof term)
        (proof-with-checked-results
            ((branch (and (proof-is-call term *proof-if*)
                          (l1-rewriting-rewriter-branch rewriter term evidence)))
             (structural (and (not branch)
                              (assoc-equal head (l1-rewriting-rewriter-structural rewriter))
                              (l1-rewriting-rewriter-structural-branch rewriter term evidence)))
             (constant (and (not (or branch structural))
                            (l1-application-proof-constant proof term))))
          (or branch structural constant
              (l1-rewriting-apply-equations
               (table-get (l1-rewriting-rewriter-equations rewriter) head nil)
               rewriter term evidence)))))))

(defund l1-rewriting-evidence-redex (entries proof term place)
  (if (endp entries)
      nil
    (let ((step (cdar entries)))
      (proof-with-checked-results
          ((first (proof-step-first step))
           (equality (and (proof-is-call first *proof-equal*) (proof-list-of-length first 3))))
        (cond ((and equality (equal (cadr equality) term) (not (equal (caddr equality) term)))
               (list place step))
              ((and equality (equal (caddr equality) term)
                    (proof-is-call (cadr equality) *proof-quote*))
               (proof-with-checked-results ((reversed (proof-proof-symmetric proof step)))
                 (list place reversed)))
              (t (l1-rewriting-evidence-redex (cdr entries) proof term place)))))))

(mutual-recursion
 (defun l1-rewriting-rewriter-redex (rewriter term evidence place)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (and (not (proof-is-call term *proof-quote*))
     (proof-with-checked-results
         ((known (l1-rewriting-evidence-redex
                  evidence (l1-rewriting-rewriter-proof rewriter) term place)))
       (or known
           (and (proof-compound term)
                (proof-with-checked-results ((root (l1-rewriting-rewriter-at-root
                                                  rewriter term evidence)))
                  (if root
                      (list place root)
                    (l1-rewriting-redex-arguments
                     rewriter (cdr term) evidence place 1
                     (if (proof-is-call term *proof-if*) 2 (len term))))))))))
 (defun l1-rewriting-redex-arguments (rewriter terms evidence place index last)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (and (consp terms) (< index last)
     (proof-with-checked-results
         ((found (l1-rewriting-rewriter-redex rewriter (car terms) evidence
                                             (append place (list index)))))
       (or found (l1-rewriting-redex-arguments
                  rewriter (cdr terms) evidence place (1+ index) last))))))

(mutual-recursion
 (defun l1-rewriting-first-conditional (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
         ((proof-is-call term *proof-if*) term)
         (t (l1-rewriting-first-conditional-arguments (cdr term)))))
 (defun l1-rewriting-first-conditional-arguments (terms)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (and (consp terms)
     (or (l1-rewriting-first-conditional (car terms))
         (l1-rewriting-first-conditional-arguments (cdr terms))))))

(defund l1-rewriting-split-test (test)
  (declare (xargs :measure (acl2-count test)))
  (if (proof-is-call test *proof-if*)
      (proof-with-checked-results ((no (proof-term-at test 3)))
        (if (or (equal no *proof-false*) (not (consp (cdr test))))
            test
          (l1-rewriting-split-test (cadr test))))
    test))

(defun l1-rewriting-retry-proof-p (result)
  (or (l1-application-unproved-p result)
      (and (failure-p result) (equal (cadr result) "unsupported-application"))))

(defun l1-rewriting-transport-if-changed (proof result chain)
  (if chain (proof-proof-transport proof result chain) result))

(defund l1-rewriting-apply-redex (proof formula change chain)
  (proof-with-checked-results
      ((prior (or chain (proof-proof-reflexive proof formula)))
       (rewritten (proof-proof-rewrite proof prior (cadr change) (car change))))
    (proof-proof-tidy proof rewritten)))

(defund l1-rewriting-rewrite-stopped (rewriter current premises chain)
  (proof-with-checked-results
      ((derived (l1-rewriting-rewriter-derive rewriter current premises 3 nil)))
    (if derived
        (l1-rewriting-transport-if-changed
         (l1-rewriting-rewriter-proof rewriter) derived chain)
      (list :unestablished current chain))))

(defund l1-rewriting-bounded-step (rewriter formula premises current chain visited)
  (if (> (l1-rewriting-size current) 1024)
      '(:failure "unproved" "")
    (let ((proof (l1-rewriting-rewriter-proof rewriter)))
      (proof-with-checked-results
          ((change (l1-rewriting-rewriter-redex rewriter current premises '(1 2))))
        (if (not change)
            (l1-rewriting-rewrite-stopped rewriter current premises chain)
          (proof-with-checked-results
              ((chain (l1-rewriting-apply-redex proof formula change chain))
               (current (proof-rewritten-term chain)))
            (let ((premise (assoc-equal current premises)))
              (cond ((member-equal current visited)
                     (l1-rewriting-rewrite-stopped rewriter current premises chain))
                    ((equal current *proof-true*) (proof-proof-true-from-eq proof chain))
                    (premise (proof-proof-transport proof (cdr premise) chain))
                    (t (list :continue current chain (cons current visited)))))))))))

(defun l1-rewriting-rewrite-steps (remaining rewriter formula premises current chain visited)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (l1-rewriting-rewrite-stopped rewriter current premises chain)
    (let ((result (l1-rewriting-bounded-step rewriter formula premises current chain visited)))
      (if (eq (car result) :continue)
          (l1-rewriting-rewrite-steps (1- remaining) rewriter formula premises
                                      (cadr result) (caddr result) (cadddr result))
        result))))

(defund l1-rewriting-rewrite-progress (rewriter formula premises)
  (let ((premise (assoc-equal formula premises)))
    (cond (premise (cdr premise))
          ((equal formula *proof-true*)
           (l1-application-proof-prove (l1-rewriting-rewriter-proof rewriter) formula nil nil))
          (t (l1-rewriting-rewrite-steps 64 rewriter formula premises
                                         formula nil (list formula))))))

(defund l1-rewriting-implied-step (rewriter implication rule known)
  (and (proof-is-call implication *library-implies*)
       (proof-with-checked-results ((consequent (proof-term-at implication 2)))
         (and (not (assoc-equal consequent known))
              (let ((antecedent (l1-rewriting-rewrite-progress rewriter (cadr implication) known)))
                (if (or (eq (car antecedent) :unestablished)
                        (l1-rewriting-retry-proof-p antecedent))
                    nil
                  (proof-with-checked-results ((antecedent antecedent))
                    (proof-proof-modus-ponens
                     (l1-rewriting-rewriter-proof rewriter) rule antecedent))))))))

(defun l1-rewriting-premises-implications (entries rewriter known pending)
  (if (endp entries)
      pending
    (proof-with-checked-results
        ((step (l1-rewriting-implied-step rewriter (caar entries) (cdar entries) known)))
      (l1-rewriting-premises-implications
       (cdr entries) rewriter known (if step (cons step pending) pending)))))

(defund l1-rewriting-enlarge-premises (rewriter pending known)
  (let ((step (car pending))
        (proof (l1-rewriting-rewriter-proof rewriter)))
    (proof-with-checked-results ((term (proof-step-first step)))
      (if (assoc-equal term known)
          (list (cdr pending) known)
        (proof-with-checked-results
            ((known (table-put known term step))
             (conjunction (l1-rewriting-conjunction-p term))
             (pair (and conjunction (proof-proof-conjunct proof step)))
             (pending (if pair (cons (cadr pair) (cons (car pair) (cdr pending)))
                        (cdr pending)))
             (pending (l1-rewriting-premises-implications known rewriter known pending)))
          (list pending known))))))

(defun l1-rewriting-premises-visit (n rewriter pending known)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "l1-rewriting-premises-visit"))
        ((endp pending) known)
        (t (proof-with-checked-results
               ((next (l1-rewriting-enlarge-premises rewriter pending known)))
             (l1-rewriting-premises-visit (1- n) rewriter (car next) (cadr next))))))

(defun l1-rewriting-rewriter-premises (rewriter evidence)
  (l1-rewriting-premises-visit 1000000 rewriter (reverse evidence) nil))

(defund l1-rewriting-split-conditional (current split)
  (and (not (or (null split) (equal split 0)))
       (l1-rewriting-first-conditional current)))

(defund l1-rewriting-split-premises (rewriter test holds premises)
  (let ((evidence (table-values premises)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume (l1-rewriting-rewriter-proof rewriter) test holds)))
      (l1-rewriting-rewriter-premises rewriter (append evidence (list assumed))))))

(defun l1-rewriting-rewrite-visit (n rewriter formula premises split)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "l1-rewriting-rewrite-visit")
    (let ((result (l1-rewriting-rewrite-progress rewriter formula premises)))
      (if (not (eq (car result) :unestablished))
          result
        (let* ((current (cadr result))
               (chain (caddr result))
               (conditional (l1-rewriting-split-conditional current split)))
          (if (not conditional)
              '(:failure "unproved" "")
            (let ((proof (l1-rewriting-rewriter-proof rewriter)))
              (proof-with-checked-results
                  ((test (proof-term-at conditional 1))
                   (test (l1-rewriting-split-test test))
                   (yes-premises (l1-rewriting-split-premises rewriter test t premises))
                   (yes (l1-rewriting-rewrite-visit (1- n) rewriter current yes-premises (1- split)))
                   (no-premises (l1-rewriting-split-premises rewriter test nil premises))
                   (no (l1-rewriting-rewrite-visit (1- n) rewriter current no-premises (1- split)))
                   (result (proof-proof-cases proof test yes no)))
                (l1-rewriting-transport-if-changed proof result chain)))))))))

(defun l1-rewriting-rewriter-rewrite (rewriter formula premises split)
  (l1-rewriting-rewrite-visit 1000000 rewriter formula premises split))

(defun l1-rewriting-rewriter-prove (rewriter formula evidence split)
  (proof-with-checked-results ((premises (l1-rewriting-rewriter-premises rewriter evidence)))
    (l1-rewriting-rewriter-rewrite rewriter formula premises split)))

(defund l1-rewriting-induction-hypothesis (proof formula variable measure bindings pairs)
  (let* ((substitution (l1-rewriting-pairs-to-map pairs nil))
         (entry (assoc-equal variable substitution)))
    (if (not entry)
        '(:failure "failure" "")
      (let* ((child (cdr entry))
             (smaller (list *proof-ordinal-less* (list *library-count* child) measure)))
        (proof-with-checked-results
            ((consequent (proof-subst formula substitution))
             (head (proof-term-at child 0))
             (descent (or (assoc-equal head *l1-rewriting-descent*)
                          '(:failure "failure" "")))
             (decrease (proof-proof-fact proof (cdr descent) bindings))
             (assumed (proof-proof-assume
                       proof (proof-ite smaller consequent *proof-true*) t)))
          (proof-proof-prove-if proof assumed decrease))))))

(defun l1-rewriting-induction-hypotheses (proof formula variable measure bindings substitutions)
  (declare (xargs :measure (acl2-count substitutions)))
  (if (endp substitutions)
      nil
    (proof-with-checked-results
        ((hypothesis (l1-rewriting-induction-hypothesis
                      proof formula variable measure bindings (car substitutions)))
         (rest (l1-rewriting-induction-hypotheses
                proof formula variable measure bindings (cdr substitutions))))
      (cons hypothesis rest))))

(defund l1-rewriting-rewriter-induct-on (rewriter formula variable substitutions)
  (let* ((proof (l1-rewriting-rewriter-proof rewriter))
         (cons-test (list *proof-consp* variable)))
    (proof-with-checked-results
        ((not-cons (proof-proof-assume proof cons-test nil))
         (atom-case (l1-rewriting-rewriter-prove rewriter formula (list not-cons) 4))
         (measure (list *library-count* variable))
         (bindings (list (list *library-x* variable)))
         (hypotheses (l1-rewriting-induction-hypotheses
                      proof formula variable measure bindings substitutions))
         (cons-proof (proof-proof-assume proof cons-test t))
         (cons-case (l1-rewriting-rewriter-prove rewriter formula
                                                 (cons cons-proof hypotheses) 4))
         (cases (proof-proof-cases proof cons-test cons-case atom-case))
         (ordinal (proof-proof-fact proof "built-in-clause-1" bindings)))
      (proof-proof-induct proof ordinal cases formula measure substitutions))))

(defund l1-rewriting-plan-descents (descending position variable formals call plans updates)
  (if (endp descending)
      (list plans updates)
    (let ((recursive-call (car descending)))
      (proof-with-checked-results
          ((child (proof-term-at recursive-call position))
           (selector (proof-term-at child 0))
           (selectors (table-get plans variable nil))
           (plans (table-put plans variable (add-to-set-equal selector selectors)))
           (substitution (l1-rewriting-recursive-substitution formals call recursive-call)))
        (l1-rewriting-plan-descents
         (cdr descending) position variable formals call plans
         (if substitution (l1-rewriting-append-to-index updates variable substitution)
           updates))))))

(defun l1-rewriting-induction-plans (calls rewriter plans updates)
  (if (endp calls)
      (list plans updates)
    (let ((call (car calls)))
      (proof-with-checked-results ((head (proof-term-at call 0)))
        (let ((structural (assoc-equal head (l1-rewriting-rewriter-structural rewriter))))
          (if (not structural)
              (l1-rewriting-induction-plans (cdr calls) rewriter plans updates)
            (proof-with-checked-results
                ((position (cadr structural))
                 (variable (proof-term-at call position)))
              (if (proof-compound variable)
                  (l1-rewriting-induction-plans (cdr calls) rewriter plans updates)
                (let* ((proof (l1-rewriting-rewriter-proof rewriter))
                       (definition (assoc-equal head (proof-proof-definitions proof))))
                  (proof-with-checked-results
                      ((parts (if definition
                                  (proof-list-of-length (cdr definition) 2)
                                '(:failure "failure" "")))
                       (next (l1-rewriting-plan-descents
                              (caddr structural) position variable (car parts) call plans updates)))
                    (l1-rewriting-induction-plans (cdr calls) rewriter
                                                  (car next) (cadr next))))))))))))

(defun l1-rewriting-plain-inductions (descent variable selectors)
  (if (endp descent)
      nil
    (let ((selector (caar descent))
          (rest (l1-rewriting-plain-inductions (cdr descent) variable selectors)))
      (if (member-equal selector selectors)
          (cons (list (list variable (list selector variable))) rest)
        rest))))

(defund l1-rewriting-try-inductions (substitutions rewriter formula variable)
  (if (endp substitutions)
      nil
    (let ((result (l1-rewriting-rewriter-induct-on
                   rewriter formula variable (car substitutions))))
      (if (l1-rewriting-retry-proof-p result)
          (l1-rewriting-try-inductions (cdr substitutions) rewriter formula variable)
        result))))

(defun l1-rewriting-try-plans (plans updates rewriter formula)
  (if (endp plans)
      '(:failure "unproved" "")
    (let* ((variable (caar plans))
           (plain (l1-rewriting-plain-inductions *l1-rewriting-descent* variable (cdar plans)))
           (updated (proof-unique (append plain (table-get updates variable nil)))))
      (proof-with-checked-results
          ((result (l1-rewriting-try-inductions (proof-unique (list plain updated))
                                               rewriter formula variable)))
        (or result (l1-rewriting-try-plans (cdr plans) updates rewriter formula))))))

(defun l1-rewriting-rewriter-induct (rewriter formula)
  (proof-with-checked-results
      ((indices (l1-rewriting-induction-plans (l1-rewriting-calls formula) rewriter nil nil)))
    (l1-rewriting-try-plans (car indices) (cadr indices) rewriter formula)))
