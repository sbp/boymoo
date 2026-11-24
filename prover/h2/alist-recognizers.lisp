(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-alist-recognizers-alist* (proof-sym "ALISTP" "ACL2"))
(defconst *h2-alist-recognizers-bounded* (proof-sym "BOUNDED-INTEGER-ALISTP" "ACL2"))
(defconst *h2-alist-recognizers-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *h2-alist-recognizers-key* (proof-sym "KEY" "ACL2"))
(defconst *h2-alist-recognizers-bound* (proof-sym "BOUND" "ACL2"))
(defconst *h2-alist-recognizers-endp* (proof-cl "ENDP"))
(defconst *h2-alist-recognizers-reverse* (proof-cl "REVERSE"))
(defconst *h2-alist-recognizers-revappend* (proof-cl "REVAPPEND"))
(defconst *h2-alist-recognizers-string* (proof-cl "STRINGP"))

(defun h2-alist-recognizers-accepted (recognizer value)
  (proof-with-checked-results ((predicate (proof-term-at recognizer 0)))
    (list* predicate value (cdr recognizer))))

(defun h2-alist-recognizers-label (recognizer)
  (proof-with-checked-results
   ((predicate (proof-term-at recognizer 0))
    (name (proof-term-at predicate 2)))
   (if (stringp name)
       name
     '(:failure "failure" ""))))

(defun h2-alist-recognizers-alist-fact (library name recognizer bindings)
  (proof-proof-fact (library-library-proof library) (proof-sym name "ACL2")
                    (append bindings (seq-zip (list *h2-alist-recognizers-bound*)
                                             (cdr recognizer)))))

(defun h2-alist-recognizers-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h2-alist-recognizers-modus (proof rule seeds)
  (proof-with-checked-results
   ((condition (h2-alist-recognizers-step-at rule 1))
    (proved (proof-proof-prove proof condition seeds nil)))
   (proof-proof-modus-ponens proof rule proved)))

(defun h2-alist-recognizers-cons-closed (library constructor entry tail recognizer)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((singleton (h2-alist-recognizers-step-at entry 1))
      (datum (proof-term-at singleton 1))
      (tail-term (h2-alist-recognizers-step-at tail 1))
      (equation (h2-alist-recognizers-alist-fact
                 library constructor recognizer (list (list *library-x* datum)
                                                        (list *library-y* tail-term))))
      (claim (h2-alist-recognizers-step-at equation 2))
      (proved (proof-proof-prove proof claim (list entry tail) nil)))
     (proof-proof-transport proof proved equation))))

(defun h2-alist-recognizers-request-p (value)
  (and (consp value) (eq (car value) :h2-alist-recognizers-derive)))

(defun h2-alist-recognizers-request-arguments (request)
  (cadr request))

(defun h2-alist-recognizers-request-folded (request)
  (caddr request))

(defun h2-alist-recognizers-derive (search replies formula definitions facts repeat seeds cases folded)
  (if (endp replies)
      (list (list :h2-alist-recognizers-derive
                  (list formula definitions facts nil 1 repeat seeds cases 80) folded)
            search nil)
    (let ((result (car replies)))
      (if (failure-p result)
          result
        (list (car result) (cdr result) (cdr replies))))))

(defun h2-alist-recognizers-has-fact (search name)
  (assoc-equal (proof-sym name "ACL2")
               (proof-proof-facts (library-library-proof (h2-search-search-library search)))))

(defun h2-alist-recognizers-lemma (search name formula step)
  (proof-with-checked-results
   ((library (library-library-lemma (h2-search-search-library search) name formula step nil)))
   (h2-search-search-with-library search library)))

(defmacro h2-alist-recognizers-with-derivations (search replies bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings))
          (form (cadar bindings)))
      `(let ((h2-alist-recognizers-result ,form))
         (cond
          ((failure-p h2-alist-recognizers-result) h2-alist-recognizers-result)
          ((failure-p (car h2-alist-recognizers-result)) (car h2-alist-recognizers-result))
          ((or (h2-alist-recognizers-request-p (car h2-alist-recognizers-result))
               (h2-search-request-p (car h2-alist-recognizers-result)))
           (cons (car h2-alist-recognizers-result) (cadr h2-alist-recognizers-result)))
          (t
           (let ((,name (car h2-alist-recognizers-result))
                 (,search (cadr h2-alist-recognizers-result))
                 (,replies (caddr h2-alist-recognizers-result)))
             (declare (ignorable ,name ,search ,replies))
             (h2-alist-recognizers-with-derivations ,search ,replies ,(cdr bindings) ,result))))))))

(defun h2-alist-recognizers-auxiliary (search replies name formula definitions facts repeat seeds cases folded)
  (let ((label (concatenate 'string "SELF-H2-" name)))
    (if (h2-alist-recognizers-has-fact search label)
        (list label search replies)
      (let ((result (h2-alist-recognizers-derive search replies formula definitions facts repeat seeds cases folded)))
        (if (or (failure-p result)
                (failure-p (car result))
                (h2-alist-recognizers-request-p (car result))
                (h2-search-request-p (car result)))
            result
          (proof-with-checked-results
           ((search (h2-alist-recognizers-lemma (cadr result) (concatenate 'string "H2-" name)
                                              formula (car result))))
           (list label search (caddr result))))))))

(defun h2-alist-recognizers-list-parts-with-replies (search recognizer replies)
  (let ((x *library-x*) (y *library-y*))
    (proof-with-checked-results
     ((definition (h2-alist-recognizers-label recognizer))
      (tail (h2-alist-recognizers-accepted recognizer y))
      (singleton (h2-alist-recognizers-accepted recognizer (list *proof-cons* x *proof-false*)))
      (pair (h2-alist-recognizers-accepted recognizer (list *proof-cons* x y))))
     (h2-alist-recognizers-with-derivations search replies
      ((constructor
        (h2-alist-recognizers-auxiliary
         search replies (concatenate 'string definition "-CONS-VIEW")
         (proof-eq pair (proof-ite singleton tail *proof-false*)) definition nil definition nil nil (list tail))))
      (proof-with-checked-results
       ((accepted (h2-alist-recognizers-accepted recognizer x))
        (guard (proof-ite (list *proof-consp* x) accepted *proof-false*))
        (head-term (h2-alist-recognizers-accepted recognizer
                                                 (list *proof-cons* (list *library-car* x) *proof-false*))))
       (h2-alist-recognizers-with-derivations search replies
        ((head (h2-alist-recognizers-auxiliary
                search replies (concatenate 'string definition "-HEAD-SINGLETON")
                (list *library-implies* guard head-term) definition nil definition nil nil nil)))
        (proof-with-checked-results
         ((tail-term (h2-alist-recognizers-accepted recognizer (list *library-cdr* x))))
         (h2-alist-recognizers-with-derivations search replies
          ((rest (h2-alist-recognizers-auxiliary
                  search replies (concatenate 'string definition "-TAIL")
                  (list *library-implies* guard tail-term) definition nil "" nil nil nil)))
          (cons (list constructor head rest) search)))))))))

(defun h2-alist-recognizers-list-parts (search recognizer)
  (h2-alist-recognizers-list-parts-with-replies search recognizer nil))

(defun h2-alist-recognizers-smaller (library formula updates cons-step)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((builtin (library-library-builtin library 3 *library-x*))
      (decrease (proof-proof-discharge proof builtin cons-step))
      (less (proof-step-first decrease))
      (substituted (proof-subst formula (proof-bindings-table updates nil)))
      (assumed (proof-proof-assume proof (proof-ite less substituted *proof-true*) t)))
     (proof-proof-prove-if proof assumed decrease))))

(defun h2-alist-recognizers-induct (search formula updates ordinal-before-intro case-step)
  (let ((proof (library-library-proof (h2-search-search-library search)))
        (library (h2-search-search-library search)))
    (proof-with-checked-results
     ((ordinal (if ordinal-before-intro (library-library-builtin library 1 *library-x*) nil))
      (introduced (h2-search-search-introduce search formula case-step))
      (ordinal (or ordinal (library-library-builtin library 1 *library-x*))))
     (proof-proof-induct proof ordinal introduced formula (list *library-count* *library-x*)
                         (list updates)))))

(defun h2-alist-recognizers-lookup-branches
    (search formula goal shape parts opening source lookup cons-step nonempty empty)
  (let* ((library (h2-search-search-library search))
         (proof (library-library-proof library))
         (updates (list (list *library-x* (list *library-cdr* *library-x*)))))
    (proof-with-checked-results
     ((selected (h2-book-logic-select-body search opening empty))
      (omitted (proof-proof-rewrite proof lookup selected '(1)))
      (no (proof-proof-subsume proof omitted (cons goal (cdr (proof-step-clause omitted)))))
      (view (h2-book-logic-select-body search opening nonempty))
      (body (h2-alist-recognizers-step-at view 2))
      (match (proof-term-at body 1))
      (assumed (proof-proof-assume proof match t))
      (found (h2-book-logic-select-body search view assumed))
      (assumed (proof-proof-assume proof match nil))
      (missed (h2-book-logic-select-body search view assumed))
      (rule (proof-proof-fact proof (proof-sym (cadr parts) "ACL2") nil))
      (entry (h2-alist-recognizers-modus proof rule (list cons-step source)))
      (reverse (proof-proof-symmetric proof found))
      (hit (proof-proof-rewrite proof entry reverse '(1 1 1)))
      (rule (proof-proof-fact proof (proof-sym (caddr parts) "ACL2") nil))
      (tail-ok (h2-alist-recognizers-modus proof rule (list cons-step source)))
      (tail-found (proof-proof-rewrite proof lookup missed '(1)))
      (smaller (h2-alist-recognizers-smaller library formula updates cons-step))
      (entry (h2-alist-recognizers-modus proof smaller (list tail-ok tail-found)))
      (reverse (proof-proof-symmetric proof missed))
      (miss (proof-proof-rewrite proof entry reverse '(1 1 1)))
      (yes (proof-proof-cases proof match hit miss))
      (case-step (proof-proof-cases proof shape yes no)))
     (h2-alist-recognizers-induct search formula updates t case-step))))

(defun h2-alist-recognizers-lookup-singleton-with-replies (search recognizer parts replies)
  (proof-with-checked-results ((definition (h2-alist-recognizers-label recognizer)))
    (let* ((stem (concatenate 'string definition "-LOOKUP-SINGLETON"))
           (name (concatenate 'string "SELF-H2-" stem)))
      (if (h2-alist-recognizers-has-fact search name)
          (cons name search)
        (let* ((x *library-x*)
               (proof (library-library-proof (h2-search-search-library search)))
               (assoc (list *h2-alist-recognizers-assoc* *h2-alist-recognizers-key* x))
               (shape (list *proof-consp* x))
               (end-test (list *h2-alist-recognizers-endp* x)))
          (proof-with-checked-results
           ((parts (proof-list-of-length parts 3))
            (accepted (h2-alist-recognizers-accepted recognizer x))
            (condition (proof-ite accepted assoc *proof-false*))
            (goal (h2-alist-recognizers-accepted recognizer (list *proof-cons* assoc *proof-false*)))
            (formula (list *library-implies* condition goal))
            (assumed (proof-proof-assume proof condition t))
            (conjuncts (proof-proof-conjunct proof assumed))
            (cons-step (proof-proof-assume proof shape t))
            (noncons (proof-proof-assume proof shape nil))
            (opening (proof-proof-unfold proof assoc)))
           (h2-alist-recognizers-with-derivations search replies
            ((nonempty (h2-alist-recognizers-derive search replies (proof-neg end-test) "" nil ""
                                                    (list cons-step) nil nil))
             (empty (h2-alist-recognizers-derive search replies end-test "" nil "" (list noncons) nil nil)))
            (proof-with-checked-results
             ((witness (h2-alist-recognizers-lookup-branches
                        search formula goal shape parts opening (car conjuncts) (cadr conjuncts)
                        cons-step nonempty empty))
              (search (h2-alist-recognizers-lemma search (concatenate 'string "H2-" stem) formula witness)))
             (cons name search)))))))))

(defun h2-alist-recognizers-lookup-singleton (search recognizer parts)
  (h2-alist-recognizers-lookup-singleton-with-replies search recognizer parts nil))

(defun h2-alist-recognizers-revappend-induction
    (search recognizer parts formula shape opening source target cons-step empty nonempty)
  (let* ((library (h2-search-search-library search))
         (proof (library-library-proof library))
         (x *library-x*)
         (updates (list (list x (list *library-cdr* x))
                        (list *library-y* (list *proof-cons* (list *library-car* x) *library-y*)))))
    (proof-with-checked-results
     ((selected (h2-book-logic-select-body search opening empty))
      (no (library-library-transport-argument library target selected 1))
      (rule (proof-proof-fact proof (proof-sym (cadr parts) "ACL2") nil))
      (prefix (h2-alist-recognizers-modus proof rule (list cons-step source)))
      (next-accum (h2-alist-recognizers-cons-closed library (car parts) prefix target recognizer))
      (rule (proof-proof-fact proof (proof-sym (caddr parts) "ACL2") nil))
      (remaining (h2-alist-recognizers-modus proof rule (list cons-step source)))
      (smaller (h2-alist-recognizers-smaller library formula updates cons-step))
      (next-value (h2-alist-recognizers-modus proof smaller (list remaining next-accum)))
      (selected (h2-book-logic-select-body search opening nonempty))
      (yes (library-library-transport-argument library next-value selected 1))
      (case-step (proof-proof-cases proof shape yes no)))
     (h2-alist-recognizers-induct search formula updates nil case-step))))

(defun h2-alist-recognizers-finish-reverse (search recognizer definition predicate replies)
  (let* ((x *library-x*)
         (proof (library-library-proof (h2-search-search-library search)))
         (reverse-term (list *h2-alist-recognizers-reverse* x)))
    (proof-with-checked-results ((source (proof-proof-assume proof predicate t)))
      (h2-alist-recognizers-with-derivations search replies
       ((not-string (h2-alist-recognizers-derive search replies (proof-neg (list *h2-alist-recognizers-string* x))
                                                definition '("consp-not-stringp") "" (list source) nil nil)))
       (let ((proof (library-library-proof (h2-search-search-library search))))
         (proof-with-checked-results
          ((opening (proof-proof-unfold proof reverse-term))
           (opened (h2-book-logic-select-body search opening not-string))
           (rev (proof-proof-fact proof (proof-sym (concatenate 'string "SELF-H2-" definition "-REVAPPEND")
                                                  "ACL2")
                                  (list (list *library-y* *proof-false*))))
           (nil-term (h2-alist-recognizers-accepted recognizer *proof-false*)))
          (h2-alist-recognizers-with-derivations search replies
           ((nil-recognized (h2-alist-recognizers-derive search replies nil-term definition nil "" nil nil nil)))
           (let* ((library (h2-search-search-library search))
                  (proof (library-library-proof library)))
             (proof-with-checked-results
              ((source (proof-proof-assume proof predicate t))
               (result (h2-alist-recognizers-modus proof rev (list source nil-recognized)))
               (goal (h2-alist-recognizers-accepted recognizer reverse-term))
               (claim (list *library-implies* predicate goal))
               (transported (library-library-transport-argument library result opened 1))
               (proved (h2-search-search-introduce search claim transported))
               (search (h2-alist-recognizers-lemma search (concatenate 'string "H2-" definition "-REVERSE")
                                                  claim proved)))
              (cons (concatenate 'string "SELF-H2-" definition "-REVERSE") search))))))))))

(defun h2-alist-recognizers-reverse-preserved-with-replies (search recognizer parts replies)
  (proof-with-checked-results ((definition (h2-alist-recognizers-label recognizer)))
    (let ((name (concatenate 'string "SELF-H2-" definition "-REVERSE")))
      (if (h2-alist-recognizers-has-fact search name)
          (cons name search)
        (let* ((x *library-x*) (y *library-y*)
               (proof (library-library-proof (h2-search-search-library search)))
               (revappend (list *h2-alist-recognizers-revappend* x y))
               (shape (list *proof-consp* x))
               (end-test (list *h2-alist-recognizers-endp* x)))
          (proof-with-checked-results
           ((parts (proof-list-of-length parts 3))
            (predicate (h2-alist-recognizers-accepted recognizer x))
            (accum (h2-alist-recognizers-accepted recognizer y))
            (condition (proof-ite predicate accum *proof-false*))
            (goal (h2-alist-recognizers-accepted recognizer revappend))
            (formula (list *library-implies* condition goal))
            (assumed (proof-proof-assume proof condition t))
            (conjuncts (proof-proof-conjunct proof assumed))
            (cons-step (proof-proof-assume proof shape t))
            (noncons (proof-proof-assume proof shape nil)))
           (h2-alist-recognizers-with-derivations search replies
            ((empty (h2-alist-recognizers-derive search replies end-test "" nil "" (list noncons) nil nil))
             (nonempty (h2-alist-recognizers-derive search replies (proof-neg end-test) "" nil ""
                                                    (list cons-step) nil nil)))
            (proof-with-checked-results
             ((opening (proof-proof-unfold (library-library-proof (h2-search-search-library search)) revappend))
              (induction (h2-alist-recognizers-revappend-induction
                          search recognizer parts formula shape opening (car conjuncts) (cadr conjuncts)
                          cons-step empty nonempty))
              (search (h2-alist-recognizers-lemma search (concatenate 'string "H2-" definition "-REVAPPEND")
                                                 formula induction)))
             (h2-alist-recognizers-finish-reverse search recognizer definition predicate replies)))))))))

(defun h2-alist-recognizers-reverse-preserved (search recognizer parts)
  (h2-alist-recognizers-reverse-preserved-with-replies search recognizer parts nil))
