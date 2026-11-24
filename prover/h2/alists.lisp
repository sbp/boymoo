(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h2-alists-alistp* (proof-sym "ALISTP" "ACL2"))
(defconst *h2-alists-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *h2-alists-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *h2-alists-ordered* (proof-sym "ORDERED-SYMBOL-ALISTP" "ACL2"))
(defconst *h2-alists-symbol-lt* (proof-sym "SYMBOL<" "ACL2"))
(defconst *h2-alists-symbolp* (proof-cl "SYMBOLP"))
(defconst *h2-alists-header* (proof-quote (proof-sym "HEADER" "KEYWORD")))
(defconst *h2-alists-heading-names*
  '("SELF-H2-ASSOC-OTHER-HEAD" "SELF-H2-INTEGER-NOT-HEADER"
    "SELF-H2-HEADER-NOT-INTEGER" "SELF-H2-CONS-NOT-HEADER"
    "SELF-H2-HEADER-NOT-CONS"))

(defun h2-alists-request-p (x)
  (and (consp x) (eq (car x) :h2-alists-derive-request)))

(defun h2-alists-request-arguments (x)
  (cdr x))

(defun h2-alists-derivation-result (value p replies)
  (if (failure-p value)
      value
    (list value p replies)))

(defmacro h2-alists-with-derivations (p replies bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings))
          (form (cadar bindings)))
      `(let ((h2-alists-derivation ,form))
         (cond ((failure-p h2-alists-derivation) h2-alists-derivation)
               ((h2-alists-request-p (car h2-alists-derivation))
                h2-alists-derivation)
               (t (let ((,name (car h2-alists-derivation))
                        (,p (cadr h2-alists-derivation))
                        (,replies (caddr h2-alists-derivation)))
                    (declare (ignorable ,name ,p ,replies))
                    (h2-alists-with-derivations ,p ,replies
                        ,(cdr bindings) ,result))))))))

(defun h2-alists-finish-derivations (result)
  (if (failure-p result)
      result
    (cons (car result) (cadr result))))

(defun h2-alists-derive (p replies formula definitions facts variable seeds cases split-limit)
  (if (endp replies)
      (list (list :h2-alists-derive-request formula definitions facts variable
                  1 "" seeds cases split-limit)
            p nil)
    (let ((reply (car replies)))
      (if (failure-p reply)
          reply
        (h2-alists-derivation-result (car reply) (cdr reply) (cdr replies))))))

(defun h2-alists-has-fact (p name)
  (if (assoc-equal (proof-sym name "ACL2")
                   (proof-proof-facts (library-library-proof p)))
      t
    nil))

(defun h2-alists-auxiliary (p replies name formula definitions facts variable cases split-limit)
  (let ((label (concatenate 'string "SELF-H2-" name)))
    (if (h2-alists-has-fact p label)
        (h2-alists-derivation-result label p replies)
      (h2-alists-with-derivations p replies
          ((step (h2-alists-derive p replies formula definitions facts variable nil cases split-limit)))
        (proof-with-checked-results
            ((p (library-library-lemma p (concatenate 'string "H2-" name) formula step nil)))
          (h2-alists-derivation-result label p replies))))))

(defun h2-alists-distinguish (p term present absent)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof term t))
         (aligned (proof-proof-rewrite proof present assumed '(1 1)))
         (denied (proof-proof-cut proof aligned absent)))
      (proof-proof-front proof denied (proof-neg term)))))

(defun h2-alists-heading-swap (p term no-equal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof term t))
         (reversed (proof-proof-symmetric proof assumed))
         (cut (proof-proof-cut proof reversed no-equal)))
      (proof-proof-front proof cut (proof-neg term)))))

(defun h2-alists-heading-integer (p replies)
  (let ((proof (library-library-proof p))
        (key *library-x*)
        (header *h2-alists-header*))
    (proof-with-checked-results
        ((key-integer (proof-proof-assume proof (library-integer key) t)))
      (h2-alists-with-derivations p replies
          ((header-int (h2-alists-derive p replies (proof-neg (library-integer header))
                                         "" nil nil nil nil 80)))
        (proof-with-checked-results
            ((no-equal (h2-alists-distinguish p (proof-eq key header) key-integer header-int))
             (no-equal-first (proof-step-first no-equal))
             (integer-first (proof-step-first key-integer))
             (conditions (list (proof-neg integer-first)))
             (p (library-library-lemma p "H2-INTEGER-NOT-HEADER"
                                       no-equal-first no-equal conditions))
             (swapped (h2-alists-heading-swap p (proof-eq header key) no-equal))
             (swapped-first (proof-step-first swapped))
             (p (library-library-lemma p "H2-HEADER-NOT-INTEGER"
                                       swapped-first swapped conditions)))
          (h2-alists-derivation-result nil p replies))))))

(defun h2-alists-heading-cons (p replies)
  (let ((proof (library-library-proof p))
        (pair (list *proof-cons* *library-x* *library-y*))
        (header *h2-alists-header*))
    (proof-with-checked-results
        ((pair-cons (proof-proof-fact proof "consp-cons" nil)))
      (h2-alists-with-derivations p replies
          ((header-cons (h2-alists-derive p replies (proof-neg (list *proof-consp* header))
                                          "" nil nil nil nil 80)))
        (proof-with-checked-results
            ((no-equal (h2-alists-distinguish p (proof-eq pair header) pair-cons header-cons))
             (no-equal-first (proof-step-first no-equal))
             (p (library-library-lemma p "H2-CONS-NOT-HEADER" no-equal-first no-equal nil))
             (swapped (h2-alists-heading-swap p (proof-eq header pair) no-equal))
             (swapped-first (proof-step-first swapped))
             (p (library-library-lemma p "H2-HEADER-NOT-CONS" swapped-first swapped nil)))
          (h2-alists-derivation-result nil p replies))))))

(defun h2-alists-heading-derivations (p replies)
  (if (h2-alists-has-fact p "SELF-H2-HEADER-NOT-CONS")
      (h2-alists-derivation-result *h2-alists-heading-names* p replies)
    (let* ((tail (proof-sym "L" "ACL2"))
           (other-key (proof-neg (proof-eq *library-x* *library-y*)))
           (pair (list *proof-cons* *library-y* *library-z*))
           (association (proof-eq
                         (list *h2-alists-assoc* *library-x* (list *proof-cons* pair tail))
                         (list *h2-alists-assoc* *library-x* tail))))
      (h2-alists-with-derivations p replies
          ((other-head (h2-alists-auxiliary p replies "ASSOC-OTHER-HEAD"
                                           (list *library-implies* other-key association)
                                           "ASSOC-EQUAL" nil nil nil 80))
           (integer-facts (if (h2-alists-has-fact p "SELF-H2-HEADER-NOT-INTEGER")
                              (h2-alists-derivation-result nil p replies)
                            (h2-alists-heading-integer p replies)))
           (cons-facts (h2-alists-heading-cons p replies)))
        (h2-alists-derivation-result *h2-alists-heading-names* p replies)))))

(defun h2-alists-heading-facts (p replies)
  (h2-alists-finish-derivations (h2-alists-heading-derivations p replies)))

(defun h2-alists-array-extension (p formula replies)
  (proof-with-checked-results
      ((conclusion (proof-term-at formula 2))
       (head (proof-term-at conclusion 0))
       (dimension (proof-term-at head 2)))
    (if (not (stringp dimension))
        '(:failure "failure" "")
      (let* ((bound (if (equal dimension "ARRAY2P")
                        "BOUNDED-INTEGER-ALISTP2"
                      "BOUNDED-INTEGER-ALISTP"))
             (definitions (concatenate 'string dimension " " bound " DIMENSIONS HEADER ALISTP")))
        (h2-alists-finish-derivations
         (h2-alists-with-derivations p replies
             ((facts (h2-alists-heading-derivations p replies)))
           (h2-alists-derive p replies formula definitions facts nil nil nil 30)))))))

(defun h2-alists-ordered-alist-derivations (p replies)
  (h2-alists-auxiliary p replies "ORDERED-ALISTP"
                       (list *library-implies* (list *h2-alists-ordered* *library-x*)
                             (list *h2-alists-alistp* *library-x*))
                       "ORDERED-SYMBOL-ALISTP ALISTP" nil "X" nil 80))

(defun h2-alists-ordered-alist (p replies)
  (h2-alists-finish-derivations (h2-alists-ordered-alist-derivations p replies)))

(defun h2-alists-first-key (alist)
  (list *library-car* (list *library-car* alist)))

(defun h2-alists-ordered-projection-derivations (p replies)
  (let* ((x *library-x*)
         (tail (list *library-cdr* x))
         (owner (proof-ite (list *h2-alists-ordered* x) (list *proof-consp* x) *proof-false*))
         (neighbor (proof-ite owner (list *proof-consp* tail) *proof-false*))
         (opened "ORDERED-SYMBOL-ALISTP"))
    (h2-alists-with-derivations p replies
        ((tail-fact (h2-alists-auxiliary p replies "ORDERED-TAIL"
                                        (list *library-implies* owner (list *h2-alists-ordered* tail))
                                        opened nil nil nil 80))
         (pair (h2-alists-auxiliary p replies "ORDERED-HEAD-PAIR"
                                   (list *library-implies* owner (list *proof-consp* (list *library-car* x)))
                                   opened nil nil nil 80))
         (symbol-fact (h2-alists-auxiliary p replies "ORDERED-HEAD-SYMBOL"
                                          (list *library-implies* owner
                                                (list *h2-alists-symbolp* (h2-alists-first-key x)))
                                          opened nil nil nil 80))
         (bound (h2-alists-auxiliary p replies "ORDERED-NEIGHBOR"
                                    (list *library-implies* neighbor
                                          (list *h2-alists-symbol-lt* (h2-alists-first-key x)
                                                (h2-alists-first-key tail)))
                                    opened nil nil nil 80)))
      (h2-alists-derivation-result (list tail-fact pair symbol-fact bound) p replies))))

(defun h2-alists-ordered-projections (p replies)
  (h2-alists-finish-derivations (h2-alists-ordered-projection-derivations p replies)))

(mutual-recursion
 (defun h2-alists-remove-wrappers (n proof term)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "h2-alists-remove-wrappers"))
         ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
         (t (proof-with-checked-results ((head (proof-term-at term 0)))
              (if (or (proof-compound head) (equal head (proof-sym "RETURN-LAST" "ACL2")))
                  (proof-with-checked-results
                      ((first (if (proof-compound head)
                                  (proof-proof-beta proof term)
                                (proof-proof-unfold proof term)))
                       (literal (proof-step-first first))
                       (value (proof-term-at literal 2))
                       (direct (h2-alists-remove-wrappers (1- n) proof value)))
                    (proof-proof-chain proof first (list direct)))
                (h2-alists-remove-wrapper-arguments (1- n) proof term (cdr term) 1 nil))))))
 (defun h2-alists-remove-wrapper-arguments (n proof term args index first)
   (declare (xargs :measure (nfix n)))
   (cond ((endp args) first)
         ((zp n) '(:failure "Fuel" "h2-alists-remove-wrapper-arguments"))
         (t (proof-with-checked-results
                 ((direct (h2-alists-remove-wrappers (1- n) proof (car args)))
                  (next (if direct
                            (proof-with-checked-results
                                ((identity (or first (proof-proof-reflexive proof term))))
                              (proof-proof-rewrite proof identity direct (list 1 2 index)))
                          first)))
               (h2-alists-remove-wrapper-arguments (1- n) proof term (cdr args) (1+ index) next))))))

(defun h2-alists-normalized-fact (p name)
  (if (not (stringp name))
      '(:failure "failure" "")
    (let ((label (concatenate 'string "SELF-H2-LOGICAL-" name))
          (proof (library-library-proof p)))
      (if (h2-alists-has-fact p label)
          (cons label p)
        (proof-with-checked-results
            ((step (proof-proof-fact proof (proof-sym name "ACL2") nil))
             (first (proof-step-first step))
             (direct (h2-alists-remove-wrappers 1000000 proof first)))
          (if (not direct)
              (cons name p)
            (proof-with-checked-results
                ((step (proof-proof-rewrite proof step direct '(1)))
                 (first (proof-step-first step))
                 (p (library-library-lemma p (concatenate 'string "H2-LOGICAL-" name) first step nil)))
              (cons label p))))))))

(defun h2-alists-logical-result (equality)
  (if (not equality)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first equality)))
      (proof-term-at literal 2))))

(defun h2-alists-introduce (proof formula conclusion)
  (proof-with-checked-results
      ((opening (proof-proof-unfold proof formula))
       (body (h2-alists-logical-result opening))
       (test (proof-term-at formula 1))
       (premise (proof-proof-assume proof test t))
       (yes (proof-proof-select proof body premise))
       (value (h2-alists-logical-result yes))
       (truth (proof-proof-select proof value conclusion))
       (affirmative (proof-proof-chain proof opening (list yes truth)))
       (affirmative (proof-proof-true-from-eq proof affirmative))
       (no (proof-proof-if-false proof body))
       (negative (proof-proof-chain proof opening (list no)))
       (negative (proof-proof-true-from-eq proof negative)))
    (proof-proof-cases proof test affirmative negative)))

(defun h2-alists-reverse-symbol-less (p replies label)
  (if (h2-alists-has-fact p label)
      (h2-alists-derivation-result nil p replies)
    (let* ((proof (library-library-proof p))
           (x *library-x*)
           (y *library-y*)
           (conditions (proof-ite (list *h2-alists-symbolp* x)
                                  (proof-ite (list *h2-alists-symbolp* y)
                                             (proof-neg (list *h2-alists-symbol-lt* x y)) *proof-false*)
                                  *proof-false*))
           (unequal (proof-neg (proof-eq x y)))
           (goal (list *h2-alists-symbol-lt* y x)))
      (proof-with-checked-results
          ((premise (proof-proof-assume proof (proof-ite conditions unequal *proof-false*) t))
           (pair (proof-proof-conjunct proof premise))
           (trichotomy (proof-proof-fact proof (proof-sym "SYMBOL<-TRICHOTOMY" "ACL2") nil))
           (iff (proof-proof-modus-ponens proof trichotomy (car pair))))
        (h2-alists-with-derivations p replies
            ((step (h2-alists-derive p replies goal "" nil nil (list iff (cadr pair)) (list goal) 80)))
          (let ((proof (library-library-proof p)))
            (proof-with-checked-results
                ((premise-first (proof-step-first premise))
                 (formula (list *library-implies* premise-first goal))
                 (step (h2-alists-introduce proof formula step))
                 (p (library-library-lemma p "H2-SYMBOL-REVERSE-LESS" formula step nil)))
              (h2-alists-derivation-result nil p replies))))))))

(defun h2-alists-ordered-changes-derivations (p theorem formula replies)
  (if (equal theorem "ORDERED-SYMBOL-ALISTP-GETPROPS")
      (proof-with-checked-results
          ((removal (h2-alists-normalized-fact p "ORDERED-SYMBOL-ALISTP-REMOVE1-ASSOC-EQ")))
        (h2-alists-with-derivations p replies
            ((empty (h2-alists-auxiliary (cdr removal) replies "ORDERED-EMPTY"
                                        (list *h2-alists-ordered* *proof-false*)
                                        "ORDERED-SYMBOL-ALISTP" nil nil nil 80)))
          (h2-alists-derive p replies formula "GETPROPS PLIST-WORLDP"
                            (list (car removal) "ORDERED-SYMBOL-ALISTP-ADD-PAIR" empty)
                            "W" nil nil 80)))
    (h2-alists-with-derivations p replies
        ((projections (h2-alists-ordered-projection-derivations p replies)))
      (if (equal theorem "ORDERED-SYMBOL-ALISTP-REMOVE1-ASSOC-EQ")
          (proof-with-checked-results
              ((equality (h2-alists-remove-wrappers 1000000 (library-library-proof p) formula))
               (logical (h2-alists-logical-result equality)))
            (h2-alists-with-derivations p replies
                ((step (h2-alists-derive p replies logical "ORDERED-SYMBOL-ALISTP REMOVE1-ASSOC-EQUAL"
                                         (append projections '("SYMBOL<-TRANSITIVE")) "L" nil nil 36)))
              (h2-alists-derivation-result
               (proof-proof-transport (library-library-proof p) step equality) p replies)))
        (let ((label "SELF-H2-SYMBOL-REVERSE-LESS"))
          (h2-alists-with-derivations p replies
              ((reverse-less (h2-alists-reverse-symbol-less p replies label)))
            (h2-alists-derive p replies formula "ORDERED-SYMBOL-ALISTP ADD-PAIR"
                              (append projections (list label "SYMBOL<-TRANSITIVE")) "GS" nil nil 45)))))))

(defun h2-alists-ordered-changes (p theorem formula replies)
  (h2-alists-finish-derivations (h2-alists-ordered-changes-derivations p theorem formula replies)))

(defun h2-alists-channel-headers (p formula replies)
  (let* ((channels (proof-sym "OPEN-CHANNEL-LISTP" "ACL2"))
         (key (proof-sym "KEY" "ACL2"))
         (x *library-x*)
         (premise (proof-ite (list *h2-alists-alistp* x) (list channels x) *proof-false*))
         (lookup (list *h2-alists-assoc* key x))
         (header (list *h2-alists-listp* (list *library-car* (list *library-cdr* lookup)))))
    (h2-alists-finish-derivations
     (h2-alists-with-derivations p replies
         ((lemma (h2-alists-auxiliary
                  p replies "CHANNEL-HEADER-LOOKUP" (list *library-implies* premise header)
                  "OPEN-CHANNEL-LISTP ALISTP ASSOC-EQUAL OPEN-CHANNEL1 CHANNEL-HEADERP TRUE-LISTP"
                  nil "X" nil 40))
          (ordered (h2-alists-ordered-alist-derivations p replies)))
       (h2-alists-derive p replies formula "OPEN-CHANNELS-P" (list lemma ordered) nil nil nil 80)))))

(defun h2-alists-cons-nonnil (p replies prop)
  (if (h2-alists-has-fact p prop)
      (h2-alists-derivation-result nil p replies)
    (let ((pair (list *proof-cons* *library-x* *library-y*)))
      (proof-with-checked-results
          ((pair-cons (proof-proof-fact (library-library-proof p) "consp-cons" nil)))
        (h2-alists-with-derivations p replies
            ((empty (h2-alists-derive p replies (proof-neg (list *proof-consp* *proof-false*))
                                      "" nil nil nil nil 80)))
          (let ((proof (library-library-proof p)))
            (proof-with-checked-results
                ((denied (h2-alists-distinguish p (proof-eq pair *proof-false*) pair-cons empty))
                 (nil-or-true (proof-proof-nil-or-true proof pair))
                 (cut (proof-proof-cut proof nil-or-true denied))
                 (p (library-library-lemma p "H2-CONS-NONNIL" pair cut nil)))
              (h2-alists-derivation-result nil p replies))))))))

(defun h2-alists-assoc-after-add (p theorem formula replies)
  (h2-alists-finish-derivations
   (if (equal theorem "ASSOC-ADD-PAIR")
       (proof-with-checked-results
           ((logical (h2-alists-remove-wrappers 1000000 (library-library-proof p) formula)))
         (let ((condition (proof-neg (list *proof-consp* *library-y*)))
               (claim (proof-eq (list *h2-alists-assoc* *library-x* *library-y*) *proof-false*)))
           (h2-alists-with-derivations p replies
               ((empty (h2-alists-auxiliary p replies "ASSOC-OF-NONCONS"
                                           (list *library-implies* condition claim)
                                           "ASSOC-EQUAL" nil nil nil 80)))
             (proof-with-checked-results ((term (h2-alists-logical-result logical)))
               (h2-alists-with-derivations p replies
                   ((step (h2-alists-derive p replies term "ADD-PAIR ASSOC-EQUAL"
                                            (list empty) "ALIST" nil nil 42)))
                 (h2-alists-derivation-result
                  (proof-proof-transport (library-library-proof p) step logical) p replies))))))
     (let ((prop "SELF-H2-CONS-NONNIL"))
       (h2-alists-with-derivations p replies ((nonnil (h2-alists-cons-nonnil p replies prop)))
         (proof-with-checked-results ((assoc (h2-alists-normalized-fact p "ASSOC-ADD-PAIR")))
           (h2-alists-derive (cdr assoc) replies formula "ALL-BOUNDP" (list (car assoc) prop)
                             "ALIST1" nil nil 80)))))))
