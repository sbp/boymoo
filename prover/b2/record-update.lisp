(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-record-update-rcdp* (proof-sym "RCDP" "ACL2"))
(defconst *b2-record-update-invalid* (proof-sym "IFRP" "ACL2"))
(defconst *b2-record-update-encode* (proof-sym "ACL2->RCD" "ACL2"))
(defconst *b2-record-update-decode* (proof-sym "RCD->ACL2" "ACL2"))
(defconst *b2-record-update-get-aux* (proof-sym "G-AUX" "ACL2"))
(defconst *b2-record-update-set-aux* (proof-sym "S-AUX" "ACL2"))
(defconst *b2-record-update-a* (proof-sym "A" "ACL2"))
(defconst *b2-record-update-b* (proof-sym "B" "ACL2"))
(defconst *b2-record-update-e* (proof-sym "E" "ACL2"))
(defconst *b2-record-update-r* (proof-sym "R" "ACL2"))
(defconst *b2-record-update-v* (proof-sym "V" "ACL2"))
(defconst *b2-record-update-z* (proof-sym "Z" "ACL2"))
(defconst *b2-record-update-record-laws*
  '(("sym" "ACL2" "G-DIFF-S") ("sym" "ACL2" "G-SAME-S")
    ("sym" "ACL2" "S-SAME-G")))

(defconst *b2-record-update-encode-record* (proof-sym "B2-ENCODE-RECORD" "ACL2"))
(defconst *b2-record-update-decode-encode* (proof-sym "B2-DECODE-ENCODE" "ACL2"))
(defconst *b2-record-update-encode-decode* (proof-sym "B2-ENCODE-DECODE" "ACL2"))
(defconst *b2-record-update-bound* (proof-sym "B2-RECORD-UPDATE-BOUND" "ACL2"))
(defconst *b2-record-update-type* (proof-sym "B2-RECORD-UPDATE-TYPE" "ACL2"))
(defconst *b2-record-update-lookup-update* (proof-sym "B2-RECORD-LOOKUP-UPDATE" "ACL2"))
(defconst *b2-record-update-restore* (proof-sym "B2-RECORD-RESTORE" "ACL2"))
(defconst *b2-record-update-other-key* (proof-sym "B2-RECORD-LOOKUP-OTHER-KEY" "ACL2"))

(defmacro b2-record-update-solve (lib goal &optional evidence unfold rules)
  `(b2-tactics-tactics-solve ,lib ,goal ,evidence ,unfold ,rules 0 nil))

(defmacro b2-record-update-normalize (lib term &optional evidence unfold)
  `(b2-tactics-tactics-normalize ,lib ,term ,evidence ,unfold nil 1500 nil))

(defmacro b2-record-update-from-impossible (lib goal premise &optional evidence unfold)
  `(b2-tactics-tactics-from-impossible
    ,lib ,goal ,premise ,evidence ,unfold nil 1500 nil))

(defmacro b2-record-update-use-fact (lib name target evidence)
  `(b2-tactics-tactics-use-fact ,lib ,name ,target ,evidence nil nil 0 nil))

(defmacro b2-record-update-with-library (lib bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (failure-p ,name)
             (cons ,name ,lib)
           (b2-record-update-with-library ,lib ,(cdr bindings) ,result))))))

(defun b2-record-update-result (result lib)
  (if (failure-p result) (cons result lib) result))

(defun b2-record-update-fact-present-p (lib name)
  (consp (assoc-equal name (proof-proof-facts (library-library-proof lib)))))

(defun b2-record-update-evidence-at (known term)
  (let ((entry (assoc-equal term known)))
    (if entry (cdr entry) '(:failure "tactic-rejected" ""))))

(defun b2-record-update-first (step)
  (if step
      (proof-step-first step)
    '(:failure "failure" "")))

(defun b2-record-update-request-p (value)
  (and (consp value) (eq (car value) :call)))

(defun b2-record-update-case-request (lib test evidence replies)
  (let* ((latest-lib (if replies (cdr (car (last replies))) lib))
         (result (b2-record-update-result
                  (b2-tactics-choose lib test evidence replies) latest-lib))
         (value (car result)))
    (if (b2-record-update-request-p value)
        (cons (list :call (nth 3 value) (list (nth 4 value))
                    (list lib test evidence replies))
              (cdr result))
      result)))

(defun b2-record-update-case-resume (lib continuation answer)
  (if (failure-p answer)
      (cons answer lib)
    (b2-record-update-case-request
     (car continuation) (cadr continuation) (caddr continuation)
     (append (cadddr continuation) (list (cons answer lib))))))

(defmacro b2-record-update-drive (resume result callback remaining &rest captures)
  (if (zp remaining)
      result
    `(let* ((record-update-result ,result)
            (record-update-value (car record-update-result))
            (record-update-lib (cdr record-update-result)))
       (if (b2-record-update-request-p record-update-value)
           (b2-record-update-drive
            ,resume
            (,resume record-update-lib (cadddr record-update-value)
                     (,callback (cadr record-update-value) (caddr record-update-value)
                                record-update-lib ,@captures))
            ,callback ,(1- remaining) ,@captures)
         record-update-result))))

(defmacro b2-record-update-choose (lib test evidence callback &rest captures)
  `(car (b2-record-update-drive
         b2-record-update-case-resume
         (b2-record-update-case-request ,lib ,test ,evidence nil)
         ,callback 2 ,@captures)))

(defmacro b2-record-update-implication (lib antecedent consequent callback &rest captures)
  `(let ((record-update-lib ,lib)
         (record-update-antecedent ,antecedent)
         (record-update-consequent ,consequent))
     (proof-with-checked-results
         ((record-update-premise
           (proof-proof-assume (library-library-proof record-update-lib)
                               record-update-antecedent t))
          (record-update-answer (,callback record-update-premise record-update-lib ,@captures)))
       (car (b2-record-update-result
             (b2-tactics-tactics-implication
              record-update-lib record-update-antecedent record-update-consequent
              (cons record-update-answer record-update-lib))
             record-update-lib)))))

(defun b2-record-update-key (record)
  (list *library-car* (list *library-car* record)))

(defun b2-record-update-value (record)
  (list *library-cdr* (list *library-car* record)))

(defun b2-record-update-insert (a v tail)
  (list *proof-cons* (list *proof-cons* a v) tail))

(defun b2-record-update-order-or-empty (limit record)
  (proof-ite (proof-eq record *proof-false*) *proof-true*
             (list *b2-strict-order-strict* limit (b2-record-update-key record))))

(defun b2-record-update-fields-bound (empty args lib record tail switched)
  (let ((facts (car args))
        (goal (b2-record-update-order-or-empty (b2-record-update-key record) tail)))
    (proof-with-checked-results
        ((evidence (if empty
                       facts
                     (proof-with-checked-results
                         ((order (proof-proof-prove-if (library-library-proof lib) switched
                                                      (car (last facts)))))
                       (append facts (list order))))))
      (b2-record-update-solve lib goal evidence))))

(defun b2-record-update-fields (lib record typed cons-step)
  (let* ((proof (library-library-proof lib))
         (type-term (list *b2-record-update-rcdp* record))
         (tail (list *library-cdr* record))
         (test (list (proof-cl "NULL") tail))
         (ordered (list *b2-strict-order-strict*
                        (b2-record-update-key record) (b2-record-update-key tail))))
    (proof-with-checked-results
        ((nonempty (b2-record-update-from-impossible
                    lib (proof-neg (proof-eq record *proof-false*)) cons-step))
         (opened (b2-record-update-normalize lib type-term (list cons-step nonempty)
                                             (list type-term)))
         (rewritten (proof-proof-rewrite proof typed opened '(1)))
         (tidied (proof-proof-tidy proof rewritten))
         (facts (b2-tactics-tactics-evidence lib (list tidied)))
         (assertion (b2-record-update-evidence-at facts (proof-ite test test ordered)))
         (opened-test (b2-record-update-normalize lib test))
         (switched (proof-proof-rewrite proof assertion opened-test '(1 1)))
         (switched (proof-proof-rewrite proof switched opened-test '(1 2)))
         (bound (b2-record-update-choose lib (proof-eq tail *proof-false*) nil
                                         b2-record-update-fields-bound record tail switched))
         (tail-type (b2-record-update-evidence-at facts (list *b2-record-update-rcdp* tail)))
         (head-cons (b2-record-update-evidence-at
                     facts (list *proof-consp* (list *library-car* record))))
         (head-value (b2-record-update-evidence-at facts (b2-record-update-value record))))
      (list nonempty tail-type head-cons head-value bound))))

(defun b2-record-update-head-order (lib limit record evidence)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib evidence))
       (order (b2-record-update-evidence-at known (b2-record-update-order-or-empty limit record)))
       (nonempty (b2-record-update-evidence-at known (proof-neg (proof-eq record *proof-false*)))))
    (proof-proof-prove-if (library-library-proof lib) order nonempty)))

(defun b2-record-update-smaller (lib a b different reverse)
  (proof-with-checked-results ((opposite (b2-strict-order-flipped-distinct lib a b different)))
    (b2-record-update-use-fact lib (proof-sym "<<-TRICHOTOMY" "ACL2")
                              (list *b2-strict-order-strict* b a) (list opposite reverse))))

(defun b2-record-update-ordered-after (lib start first second before after)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((transitive (proof-proof-fact proof (proof-sym "<<-TRANSITIVE" "ACL2")
                                     (list (list *library-x* start) (list *library-y* first)
                                           (list *b2-record-update-z* second))))
         (formula (proof-step-first transitive))
         (antecedent (proof-term-at formula 1))
         (premise (b2-record-update-solve lib antecedent (list before after))))
      (proof-proof-modus-ponens proof transitive premise))))

(defun b2-record-update-with-record-request (result record typed)
  (let ((value (car result))
        (lib (cdr result)))
    (if (b2-record-update-request-p value)
        (let* ((nonempty (cadr value))
               (evidence (car (caddr value)))
               (extra (if nonempty
                          (b2-record-update-fields lib record typed (cadr evidence))
                        (proof-with-checked-results
                            ((equality (b2-record-update-from-impossible
                                        lib (proof-eq record *proof-false*) typed (cdr evidence)
                                        (list (list *b2-record-update-rcdp* record)))))
                          (list equality)))))
          (if (failure-p extra)
              (cons extra lib)
            (cons (list :call (if nonempty :nonempty :empty)
                        (list (append evidence extra)) (list (cadddr value) record typed))
                  lib)))
      result)))

(defun b2-record-update-with-record (lib record typed)
  (b2-record-update-with-record-request
   (b2-record-update-case-request lib (list *proof-consp* record) (list typed) nil)
   record typed))

(defun b2-record-update-with-record-resume (lib continuation answer)
  (b2-record-update-with-record-request
   (b2-record-update-case-resume lib (car continuation) answer)
   (cadr continuation) (caddr continuation)))

(defun b2-record-update-prepend-type-branch (empty facts order lib a v tail)
  (let* ((record (b2-record-update-insert a v tail))
         (goal (list *b2-record-update-rcdp* record))
         (type-nil (list *b2-record-update-rcdp* *proof-false*)))
    (proof-with-checked-results
        ((branch-proof (if empty
                           (b2-record-update-solve lib type-nil nil (list type-nil))
                         (b2-record-update-solve
                          lib (list *b2-strict-order-strict* a (b2-record-update-key tail))
                          (append facts order))))
         (facts (append facts (list branch-proof)))
         (equation (b2-record-update-normalize lib record facts))
         (expanded (if equation
                       (proof-with-checked-results ((literal (proof-step-first equation)))
                         (proof-term-at literal 2))
                     record))
         (head (proof-term-at expanded 1))
         (rest (proof-term-at expanded 2))
         (cons-step (proof-proof-fact (library-library-proof lib) "consp-cons"
                                      (list (list *library-x* head) (list *library-y* rest))))
         (nonempty (b2-record-update-from-impossible
                    lib (proof-neg (proof-eq expanded *proof-false*)) cons-step)))
      (b2-record-update-solve lib goal (append facts (list nonempty)) (list goal)))))

(defun b2-record-update-prepend-type-order-request (result a v tail)
  (let ((value (car result)))
    (if (b2-record-update-request-p value)
        (let ((facts (car (caddr value))))
          (cons (list :call :order (last facts) (list (cadddr value) facts a v tail))
                (cdr result)))
      result)))

(defun b2-record-update-prepend-type (lib a v tail evidence)
  (let* ((result (b2-record-update-case-request lib (proof-eq tail *proof-false*) evidence nil))
         (value (car result)))
    (b2-record-update-prepend-type-order-request
     (if (and (b2-record-update-request-p value) (cadr value))
         (b2-record-update-case-resume
          (cdr result) (cadddr value)
          (b2-record-update-prepend-type-branch t (car (caddr value)) nil (cdr result) a v tail))
       result)
     a v tail)))

(defun b2-record-update-prepend-type-resume (lib continuation answer)
  (if (failure-p answer)
      (cons answer lib)
    (b2-record-update-case-resume
     lib (car continuation)
     (b2-record-update-prepend-type-branch
      nil (cadr continuation) answer lib (caddr continuation)
      (cadddr continuation) (nth 4 continuation)))))

(defun b2-record-update-no-order (branch args lib)
  (declare (ignore branch args lib))
  nil)

(defmacro b2-record-update-prove-prepend (lib a v tail evidence callback &rest captures)
  `(car (b2-record-update-drive
         b2-record-update-prepend-type-resume
         (b2-record-update-prepend-type ,lib ,a ,v ,tail ,evidence)
         ,callback 1 ,@captures)))

(defun b2-record-update-add-lemma (lib label step)
  (if (failure-p step)
      (cons step lib)
    (b2-record-update-result (b2-tactics-tactics-add-lemma lib label step :none) lib)))

(defun b2-record-update-encoding-lemmas-inverse (typed lib invalid malformed valid decoded chained target)
  (let ((proof (library-library-proof lib))
        (head (list *library-car* *library-x*))
        (tail (list *library-cdr* *library-x*))
        (data (b2-record-update-value *library-x*)))
    (proof-with-checked-results
        ((equation (b2-record-update-normalize lib invalid (list typed) (list invalid)))
         (shape (proof-proof-rewrite proof malformed equation '(1)))
         (shape (proof-proof-tidy proof shape))
         (shaped (b2-tactics-tactics-evidence lib (list shape)))
         (x-cons (b2-record-update-evidence-at shaped (list *proof-consp* *library-x*)))
         (whole (b2-tactics-rebuild lib *library-x* x-cons))
         (head-cons (b2-record-update-evidence-at shaped (list *proof-consp* head)))
         (pair (b2-tactics-rebuild lib head head-cons))
         (reverse-pair (proof-proof-symmetric proof pair))
         (whole (proof-proof-rewrite proof whole reverse-pair '(1 1 1)))
         (key-nil (b2-record-update-evidence-at
                   shaped (proof-eq (b2-record-update-key *library-x*) *proof-false*)))
         (whole (proof-proof-rewrite proof whole key-nil '(1 1 1 1)))
         (tail-nil (b2-record-update-evidence-at shaped (proof-eq tail *proof-false*)))
         (whole (proof-proof-rewrite proof whole tail-nil '(1 1 2)))
         (data-invalid (b2-record-update-evidence-at shaped (list *b2-record-update-invalid* data)))
         (whole (proof-proof-tidy proof whole))
         (yes (b2-record-update-solve lib target (list malformed data-invalid)
                                      (list decoded chained (list *b2-record-update-encode* data))
                                      (list whole)))
         (no (b2-record-update-solve lib target (list valid)
                                     (list decoded chained (list *b2-record-update-encode* *library-x*)))))
      (proof-proof-cases proof invalid yes no))))

(defun b2-record-update-encoding-lemmas-decode (lib invalid encoded wrapped malformed valid typed-wrap)
  (let* ((proof (library-library-proof lib))
         (chained (list *b2-record-update-decode* encoded))
         (target (proof-eq chained *library-x*))
         (invalid-wrapped (list *b2-record-update-invalid* wrapped)))
    (b2-record-update-with-library lib
        ((wrap-invalid (b2-record-update-solve lib invalid-wrapped (list typed-wrap malformed)
                                               (list invalid-wrapped)))
         (yes (b2-record-update-solve lib target (list malformed wrap-invalid)
                                      (list encoded chained (list *b2-record-update-decode* wrapped))))
         (no (b2-record-update-solve lib target (list valid)
                                     (list encoded chained (list *b2-record-update-decode* *library-x*))))
         (step (proof-proof-cases proof invalid yes no)))
      (let* ((result (b2-record-update-add-lemma lib "DECODE-ENCODE" step))
             (lib (cdr result)))
        (if (failure-p (car result))
            result
          (let* ((decoded (list *b2-record-update-decode* *library-x*))
                 (chained (list *b2-record-update-encode* decoded))
                 (target (proof-eq chained *library-x*))
                 (inverse (b2-record-update-implication
                           lib (list *b2-record-update-rcdp* *library-x*) target
                           b2-record-update-encoding-lemmas-inverse
                           invalid malformed valid decoded chained target))
                 (result (b2-record-update-add-lemma lib "ENCODE-DECODE" inverse)))
            (if (failure-p (car result)) result (cons nil (cdr result)))))))))

(defun b2-record-update-encoding-lemmas (lib)
  (if (b2-record-update-fact-present-p lib *b2-record-update-encode-record*)
      (cons nil lib)
    (let* ((proof (library-library-proof lib))
           (invalid (list *b2-record-update-invalid* *library-x*))
           (encoded (list *b2-record-update-encode* *library-x*))
           (wrapped (b2-record-update-insert *proof-false* *library-x* *proof-false*))
           (test (list *b2-record-update-rcdp* *library-x*))
           (type-nil (list *b2-record-update-rcdp* *proof-false*))
           (target (list *b2-record-update-rcdp* encoded)))
      (b2-record-update-with-library lib
          ((malformed (proof-proof-assume proof invalid t))
           (valid (proof-proof-assume proof invalid nil))
           (nonempty (b2-record-update-from-impossible
                      lib *library-x* malformed nil
                      (list invalid (list *b2-record-update-invalid* *proof-false*) type-nil)))
           (nil-type (b2-record-update-solve lib type-nil nil (list type-nil)))
           (typed-wrap (b2-record-update-prove-prepend
                        lib *proof-false* *library-x* *proof-false* (list nonempty nil-type)
                        b2-record-update-no-order))
           (valid-type (b2-record-update-from-impossible lib test valid nil (list invalid)))
           (yes (b2-record-update-solve lib target (list malformed typed-wrap) (list encoded)))
           (no (b2-record-update-solve lib target (list valid valid-type) (list encoded)))
           (step (proof-proof-cases proof invalid yes no)))
        (let* ((result (b2-record-update-add-lemma lib "ENCODE-RECORD" step))
               (lib (cdr result)))
          (if (failure-p (car result))
              result
            (b2-record-update-encoding-lemmas-decode
             lib invalid encoded wrapped malformed valid typed-wrap)))))))

(defun b2-record-update-set-bound-below (empty args lib tail target equation)
  (let ((facts (car args)))
    (proof-with-checked-results
        ((facts (if empty
                    facts
                  (proof-with-checked-results
                      ((head (b2-record-update-key *b2-record-update-r*))
                       (first (b2-record-update-head-order
                               lib *b2-record-update-e* *b2-record-update-r* facts))
                       (second (b2-record-update-head-order lib head tail facts))
                       (bound (b2-record-update-ordered-after
                               lib *b2-record-update-e* head (b2-record-update-key tail)
                               first second)))
                    (append facts (list bound))))))
      (b2-record-update-solve lib target facts nil (list equation)))))

(defun b2-record-update-set-bound-check (current lib known before-a update target tail)
  (let* ((r *b2-record-update-r*)
         (evidence (append (table-values known) current)))
    (proof-with-checked-results
        ((equation (b2-record-update-normalize lib update evidence (list update)))
         (literal (b2-record-update-first equation))
         (result (proof-term-at literal 2)))
      (cond ((or (equal result r) (equal result *proof-false*))
             (b2-record-update-solve lib target evidence nil (list equation)))
            ((equal result tail)
             (b2-record-update-choose lib (proof-eq tail *proof-false*) evidence
                                      b2-record-update-set-bound-below tail target equation))
            (t (proof-with-checked-results
                   ((head (proof-term-at result 1))
                    (rest (proof-term-at result 2))
                    (cons-step (proof-proof-fact (library-library-proof lib) "consp-cons"
                                                 (list (list *library-x* head) (list *library-y* rest))))
                    (nonempty (b2-record-update-from-impossible
                               lib (proof-neg (proof-eq result *proof-false*)) cons-step))
                    (bound (if (equal head (list *library-car* r))
                               (b2-record-update-head-order lib *b2-record-update-e* r evidence)
                             before-a)))
                 (b2-record-update-solve lib target (append evidence (list nonempty bound))
                                         nil (list equation))))))))

(defun b2-record-update-set-bound-check-value (present args lib known before-a update target tail)
  (declare (ignore present))
  (b2-record-update-set-bound-check (car args) lib known before-a update target tail))

(defun b2-record-update-set-bound-empty (current lib known before-a update target tail)
  (b2-record-update-choose lib *b2-record-update-v* current
                           b2-record-update-set-bound-check-value known before-a update target tail))

(defun b2-record-update-set-bound-equal (same args lib known before-a update target tail)
  (if same
      (b2-record-update-set-bound-empty (car args) lib known before-a update target tail)
    (b2-record-update-set-bound-check (car args) lib known before-a update target tail)))

(defun b2-record-update-set-bound-compare (earlier args lib known before-a update target tail)
  (if earlier
      (b2-record-update-set-bound-empty (car args) lib known before-a update target tail)
    (b2-record-update-choose
     lib (proof-eq *b2-record-update-a* (b2-record-update-key *b2-record-update-r*)) (car args)
     b2-record-update-set-bound-equal known before-a update target tail)))

(defun b2-record-update-set-bound-record-case (branch args lib known before-a update target tail)
  (let ((current (car args))
        (r *b2-record-update-r*))
    (if (eq branch :empty)
        (b2-record-update-set-bound-empty current lib known before-a update target tail)
      (proof-with-checked-results
          ((bound (b2-record-update-head-order
                   lib *b2-record-update-e* r (append (table-values known) current))))
        (b2-record-update-choose
         lib (list *b2-strict-order-strict* *b2-record-update-a* (b2-record-update-key r))
         (append current (list bound)) b2-record-update-set-bound-compare
         known before-a update target tail)))))

(defun b2-record-update-set-bound-prove (premise lib typed starts update target tail)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib (list premise)))
       (before-a (b2-record-update-evidence-at known starts))
       (record-type (b2-record-update-evidence-at known typed)))
    (car (b2-record-update-drive
          b2-record-update-with-record-resume
          (b2-record-update-with-record lib *b2-record-update-r* record-type)
          b2-record-update-set-bound-record-case 2 known before-a update target tail))))

(defun b2-record-update-set-bound (lib)
  (if (b2-record-update-fact-present-p lib *b2-record-update-bound*)
      (cons *b2-record-update-bound* lib)
    (let* ((r *b2-record-update-r*)
           (update (list *b2-record-update-set-aux* *b2-record-update-a* *b2-record-update-v* r))
           (typed (list *b2-record-update-rcdp* r))
           (starts (list *b2-strict-order-strict* *b2-record-update-e* *b2-record-update-a*))
           (input-bound (b2-record-update-order-or-empty *b2-record-update-e* r))
           (target (b2-record-update-order-or-empty *b2-record-update-e* update))
           (condition (b2-powers-and-terms (list typed starts input-bound)))
           (tail (list *library-cdr* r))
           (step (b2-record-update-implication lib condition target b2-record-update-set-bound-prove
                                               typed starts update target tail)))
      (b2-record-update-add-lemma lib "RECORD-UPDATE-BOUND" step))))

(defun b2-record-update-on-list-request (lib formula extra base advance)
  (let* ((result (b2-record-update-result
                  (b2-tactics-tactics-on-list lib formula *b2-record-update-r* base advance extra)
                  (cond (base (cdr base)) (advance (cdr advance)) (t lib))))
         (value (car result)))
    (if (b2-record-update-request-p value)
        (cons (list :call (cadr value) (cdddr value) (list lib formula extra advance)) (cdr result))
      result)))

(defun b2-record-update-on-list-resume (lib continuation answer)
  (if (failure-p answer)
      (cons answer lib)
    (let* ((reply (cons answer lib))
           (advance (cadddr continuation)))
      (b2-record-update-on-list-request
       (car continuation) (cadr continuation) (caddr continuation)
       (and advance reply) (or advance reply)))))

(defun b2-record-update-update-preserves-type-base (present args lib target update)
  (proof-with-checked-results
      ((facts (if present
                  (proof-with-checked-results
                      ((prepended (b2-record-update-prove-prepend
                                   lib *b2-record-update-a* *b2-record-update-v* *proof-false* (car args)
                                   b2-record-update-no-order)))
                    (append (car args) (list prepended)))
                (car args))))
    (b2-record-update-solve lib target facts (list update))))

(defun b2-record-update-update-preserves-type-empty-prove (premise lib atom-step typed update target)
  (let ((type-nil (list *b2-record-update-rcdp* *proof-false*)))
    (proof-with-checked-results
        ((equality (b2-record-update-from-impossible
                    lib (proof-eq *b2-record-update-r* *proof-false*) premise
                    (list atom-step) (list typed)))
         (nil-type (b2-record-update-solve lib type-nil nil (list type-nil))))
      (b2-record-update-choose lib *b2-record-update-v* (list premise atom-step equality nil-type)
                               b2-record-update-update-preserves-type-base target update))))

(defun b2-record-update-update-preserves-type-insert-new (present args lib target update)
  (proof-with-checked-results
      ((branch (if present
                   (proof-with-checked-results
                       ((made (b2-record-update-prove-prepend
                               lib *b2-record-update-a* *b2-record-update-v* *b2-record-update-r* (car args)
                               b2-record-update-no-order)))
                     (append (car args) (list made)))
                 (car args))))
    (b2-record-update-solve lib target branch (list update))))

(defun b2-record-update-update-preserves-type-replace-bound (branch args lib facts tail equal-head)
  (declare (ignore branch))
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((ordered (b2-record-update-head-order
                   lib (b2-record-update-key *b2-record-update-r*) tail (append facts args)))
         (reverse (proof-proof-symmetric proof equal-head))
         (rewritten (proof-proof-rewrite proof ordered reverse '(1 1)))
         (bound (proof-proof-tidy proof rewritten)))
      (list bound))))

(defun b2-record-update-update-preserves-type-replace (present args lib tail equal-head target update)
  (let ((facts (car args)))
    (proof-with-checked-results
        ((facts (if present
                    (proof-with-checked-results
                        ((made (b2-record-update-prove-prepend
                                lib *b2-record-update-a* *b2-record-update-v* tail facts
                                b2-record-update-update-preserves-type-replace-bound facts tail equal-head)))
                      (append facts (list made)))
                  facts)))
      (b2-record-update-solve lib target facts (list update)))))

(defun b2-record-update-update-preserves-type-after-bound (branch args lib newer facts tail-type after bound-name tail)
  (declare (ignore branch))
  (let* ((key (b2-record-update-key *b2-record-update-r*))
         (comparison (b2-record-update-order-or-empty key newer)))
    (proof-with-checked-results
        ((previous (b2-record-update-solve lib (b2-record-update-order-or-empty key tail) facts))
         (result (b2-record-update-use-fact lib bound-name comparison (list tail-type after previous)))
         (bound (proof-proof-prove-if (library-library-proof lib) result (car args))))
      (list bound))))

(defun b2-record-update-update-preserves-type-match (same args lib tail target update
                                                         evidence induction tail-type facts known bound-name)
  (let* ((branch (car args))
         (r *b2-record-update-r*)
         (a *b2-record-update-a*)
         (v *b2-record-update-v*)
         (head (list *library-car* r))
         (key (b2-record-update-key r))
         (proof (library-library-proof lib)))
    (if same
        (b2-record-update-choose lib v branch b2-record-update-update-preserves-type-replace
                                 tail (car (last branch)) target update)
      (proof-with-checked-results
          ((after (b2-record-update-smaller lib a key (car (last branch)) (car (last evidence))))
           (newer (list *b2-record-update-set-aux* a v tail))
           (made-tail (proof-proof-modus-ponens proof induction tail-type))
           (made (b2-record-update-prove-prepend
                  lib key (b2-record-update-value r) newer (append branch (list made-tail))
                  b2-record-update-update-preserves-type-after-bound
                  newer facts tail-type after bound-name tail))
           (head-cons (b2-record-update-evidence-at known (list *proof-consp* head)))
           (original (b2-tactics-rebuild lib head head-cons))
           (result (b2-record-update-normalize lib update branch (list update)))
           (original (proof-proof-symmetric proof original))
           (result (proof-proof-rewrite proof result original '(1 2 1))))
        (library-library-transport-argument lib made result 1)))))

(defun b2-record-update-update-preserves-type-before (negative args lib tail target update induction
                                                           tail-type facts known bound-name)
  (let ((evidence (car args)))
    (if negative
        (b2-record-update-choose lib *b2-record-update-v* evidence
                                 b2-record-update-update-preserves-type-insert-new target update)
      (b2-record-update-choose
       lib (proof-eq *b2-record-update-a* (b2-record-update-key *b2-record-update-r*)) evidence
       b2-record-update-update-preserves-type-match
       tail target update evidence induction tail-type facts known bound-name))))

(defun b2-record-update-update-preserves-type-advance-prove (premise lib cons-step induction
                                                                    tail target update bound-name)
  (let* ((r *b2-record-update-r*)
         (test (list *b2-strict-order-strict* *b2-record-update-a* (b2-record-update-key r))))
    (proof-with-checked-results
        ((fields-proof (b2-record-update-fields lib r premise cons-step))
         (facts (cons premise (cons cons-step fields-proof)))
         (known (b2-tactics-tactics-evidence lib facts))
         (tail-type (b2-record-update-evidence-at known (list *b2-record-update-rcdp* tail))))
      (b2-record-update-choose lib test facts b2-record-update-update-preserves-type-before
                               tail target update induction tail-type facts known bound-name))))

(defun b2-record-update-update-preserves-type-branch (branch args lib typed target update tail bound-name)
  (if (eq branch :advance)
      (b2-record-update-implication lib typed target b2-record-update-update-preserves-type-advance-prove
                                    (car args) (cadr args) tail target update bound-name)
    (b2-record-update-implication lib typed target b2-record-update-update-preserves-type-empty-prove
                                  (car args) typed update target)))

(defun b2-record-update-update-preserves-type (lib)
  (if (b2-record-update-fact-present-p lib *b2-record-update-type*)
      (cons *b2-record-update-type* lib)
    (let* ((bound (b2-record-update-set-bound lib))
           (bound-name (car bound))
           (lib (cdr bound)))
      (if (failure-p bound-name)
          bound
        (let* ((r *b2-record-update-r*)
               (typed (list *b2-record-update-rcdp* r))
               (update (list *b2-record-update-set-aux* *b2-record-update-a* *b2-record-update-v* r))
               (target (list *b2-record-update-rcdp* update))
               (tail (list *library-cdr* r))
               (formula (list *library-implies* typed target))
               (result (b2-record-update-drive
                        b2-record-update-on-list-resume
                        (b2-record-update-on-list-request lib formula nil nil nil)
                        b2-record-update-update-preserves-type-branch 2
                        typed target update tail bound-name)))
          (b2-record-update-add-lemma (cdr result) "RECORD-UPDATE-TYPE" (car result)))))))

(defun b2-record-update-key-cases-equal-request (result order-continuation)
  (let ((value (car result))
        (lib (cdr result)))
    (if (b2-record-update-request-p value)
        (cons (list :call (if (cadr value) :match :after) (caddr value)
                    (list :equal order-continuation (cadddr value)))
              lib)
      (b2-record-update-case-resume lib order-continuation value))))

(defun b2-record-update-key-cases-order-request (result a record)
  (let ((value (car result))
        (lib (cdr result)))
    (if (b2-record-update-request-p value)
        (if (cadr value)
            (cons (list :call :before (caddr value) (list :before (cadddr value) a record)) lib)
          (b2-record-update-key-cases-equal-request
           (b2-record-update-case-request lib (proof-eq a (b2-record-update-key record))
                                          (car (caddr value)) nil)
           (cadddr value)))
      result)))

(defun b2-record-update-key-cases (lib a record facts)
  (b2-record-update-key-cases-order-request
   (b2-record-update-case-request lib (list *b2-strict-order-strict* a (b2-record-update-key record))
                                  facts nil)
   a record))

(defun b2-record-update-key-cases-resume (lib continuation answer)
  (if (eq (car continuation) :before)
      (b2-record-update-key-cases-order-request
       (b2-record-update-case-resume lib (cadr continuation) answer)
       (caddr continuation) (cadddr continuation))
    (b2-record-update-key-cases-equal-request
     (b2-record-update-case-resume lib (caddr continuation) answer)
     (cadr continuation))))

(defmacro b2-record-update-prove-key-cases (lib a record facts callback &rest captures)
  `(car (b2-record-update-drive
         b2-record-update-key-cases-resume
         (b2-record-update-key-cases ,lib ,a ,record ,facts)
         ,callback 3 ,@captures)))

(defun b2-record-update-lookup-below-case (branch args lib a record bound lookup target)
  (let ((facts (car args)))
    (proof-with-checked-results
        ((evidence (if (eq branch :empty)
                       facts
                     (proof-with-checked-results
                         ((order (b2-record-update-head-order lib a record (append facts (list bound)))))
                       (append facts (list order))))))
      (b2-record-update-solve lib target evidence (list lookup)))))

(defun b2-record-update-lookup-below (lib a record typed bound)
  (let* ((lookup (list *b2-record-update-get-aux* a record))
         (target (proof-eq lookup *proof-false*)))
    (car (b2-record-update-drive
          b2-record-update-with-record-resume
          (b2-record-update-with-record lib record typed)
          b2-record-update-lookup-below-case 2 a record bound lookup target))))

(defun b2-record-update-record-induction-establish (lib condition signed advancing)
  (let* ((r *b2-record-update-r*)
         (typed (list *b2-record-update-rcdp* r)))
    (proof-with-checked-results
        ((premise (proof-proof-assume (library-library-proof lib) condition t))
         (known (b2-tactics-tactics-evidence lib (list premise)))
         (typed-record (b2-record-update-evidence-at known typed))
         (extra (if advancing
                    (b2-record-update-fields lib r typed-record signed)
                  (proof-with-checked-results
                      ((empty (b2-record-update-from-impossible
                               lib (proof-eq r *proof-false*) typed-record (list signed) (list typed))))
                    (list empty)))))
      (cons premise (cons signed extra)))))

(defun b2-record-update-record-induction-reply (lib initial condition target continuation answer)
  (if (failure-p answer)
      (cons answer lib)
    (let ((result (b2-record-update-result
                   (b2-tactics-tactics-implication initial condition target (cons answer lib)) lib)))
      (b2-record-update-on-list-resume (cdr result) continuation (car result)))))

(defun b2-record-update-record-induction-request (result label condition target openers on-empty-p)
  (let ((value (car result))
        (lib (cdr result)))
    (if (b2-record-update-request-p value)
        (let ((advancing (eq (cadr value) :advance))
              (args (caddr value))
              (continuation (cadddr value)))
          (b2-record-update-with-library lib
              ((evidence (b2-record-update-record-induction-establish lib condition (car args) advancing)))
            (if (or advancing on-empty-p)
                (cons (list :call (if advancing :advance :empty)
                            (if advancing (list evidence (cadr args)) (list evidence))
                            (list advancing continuation lib label condition target openers on-empty-p))
                      lib)
              (let ((finished (b2-record-update-record-induction-reply
                               lib lib condition target continuation
                               (b2-record-update-solve lib target evidence openers))))
                (b2-record-update-add-lemma (cdr finished) label (car finished))))))
      (b2-record-update-add-lemma lib label value))))

(defun b2-record-update-record-induction (lib label condition target openers on-empty-p extra)
  (b2-record-update-record-induction-request
   (b2-record-update-on-list-request lib (list *library-implies* condition target) extra nil nil)
   label condition target openers on-empty-p))

(defun b2-record-update-record-induction-resume (lib continuation answer)
  (let* ((advancing (car continuation))
         (initial (caddr continuation))
         (label (cadddr continuation))
         (condition (nth 4 continuation))
         (target (nth 5 continuation))
         (result (b2-record-update-record-induction-reply
                  lib initial condition target (cadr continuation) answer)))
    (if advancing
        (b2-record-update-record-induction-request
         result label condition target (nth 6 continuation) (nth 7 continuation))
      (b2-record-update-add-lemma (cdr result) label (car result)))))

(defmacro b2-record-update-prove-induction (lib label condition target openers on-empty-p callback &rest captures)
  `(b2-record-update-drive
    b2-record-update-record-induction-resume
    (b2-record-update-record-induction ,lib ,label ,condition ,target ,openers ,on-empty-p nil)
    ,callback 2 ,@captures))

(defun b2-record-update-lookup-after-update-present (present args lib target lookup update
                                                          irreflexive reflexive equal-head tail typed-tail)
  (let ((facts (car args)))
    (cond ((or present (not equal-head))
           (b2-record-update-solve lib target (append facts (list irreflexive reflexive)) (list lookup update)))
          (t (let ((proof (library-library-proof lib)))
               (proof-with-checked-results
                   ((head-bound (b2-record-update-solve
                                 lib (b2-record-update-order-or-empty (b2-record-update-key *b2-record-update-r*) tail)
                                 facts))
                    (reverse (proof-proof-symmetric proof equal-head))
                    (below (proof-proof-rewrite proof head-bound reverse '(1 3 1)))
                    (absent (b2-record-update-lookup-below lib *b2-record-update-a* tail typed-tail below)))
                 (b2-record-update-solve lib target facts (list lookup update) (list absent))))))))

(defun b2-record-update-lookup-after-update-key-case (branch args lib target lookup update
                                                             irreflexive reflexive tail typed-tail induction)
  (let ((facts (car args)))
    (if (eq branch :after)
        (proof-with-checked-results
            ((inherited (proof-proof-modus-ponens (library-library-proof lib) induction typed-tail)))
          (b2-record-update-solve lib target facts (list lookup update) (list inherited)))
      (b2-record-update-choose
       lib *b2-record-update-v* facts b2-record-update-lookup-after-update-present
       target lookup update irreflexive reflexive (and (eq branch :match) (car (last facts))) tail typed-tail))))

(defun b2-record-update-lookup-after-update-base-value (present args lib target lookup update)
  (declare (ignore present))
  (b2-record-update-solve lib target (car args) (list lookup update)))

(defun b2-record-update-lookup-after-update-branch (branch args lib target lookup update tail
                                                           irreflexive reflexive)
  (let ((evidence (car args)))
    (if (eq branch :empty)
        (b2-record-update-choose lib *b2-record-update-v* (append evidence (list irreflexive reflexive))
                                 b2-record-update-lookup-after-update-base-value target lookup update)
      (proof-with-checked-results
          ((typed-tail (b2-record-update-solve lib (list *b2-record-update-rcdp* tail) evidence)))
        (b2-record-update-prove-key-cases
         lib *b2-record-update-a* *b2-record-update-r* evidence b2-record-update-lookup-after-update-key-case
         target lookup update irreflexive reflexive tail typed-tail (cadr args))))))

(defun b2-record-update-lookup-after-update (lib)
  (if (b2-record-update-fact-present-p lib *b2-record-update-lookup-update*)
      (cons *b2-record-update-lookup-update* lib)
    (let* ((a *b2-record-update-a*)
           (v *b2-record-update-v*)
           (r *b2-record-update-r*)
           (proof (library-library-proof lib))
           (update (list *b2-record-update-set-aux* a v r))
           (lookup (list *b2-record-update-get-aux* a update))
           (target (proof-eq lookup v))
           (tail (list *library-cdr* r)))
      (b2-record-update-with-library lib
          ((irreflexive (proof-proof-fact proof (proof-sym "<<-IRREFLEXIVE" "ACL2") (list (list *library-x* a))))
           (reflexive (proof-proof-reflexive proof a)))
        (b2-record-update-prove-induction
         lib "RECORD-LOOKUP-UPDATE" (list *b2-record-update-rcdp* r) target (list lookup update) t
         b2-record-update-lookup-after-update-branch target lookup update tail irreflexive reflexive)))))

(defun b2-record-update-restore-from-lookup-match (facts lib known old target openers)
  (let* ((proof (library-library-proof lib))
         (head (list *library-car* *b2-record-update-r*)))
    (proof-with-checked-results
        ((head-cons (b2-record-update-evidence-at known (list *proof-consp* head)))
         (rebuilt (b2-tactics-rebuild lib head head-cons))
         (reverse (proof-proof-symmetric proof rebuilt))
         (reconstructed (proof-proof-rewrite proof old reverse '(1 1 1)))
         (reverse (proof-proof-symmetric proof (car (last facts))))
         (reconstructed (proof-proof-rewrite proof reconstructed reverse '(1 1 1 1))))
      (b2-record-update-solve lib target facts openers (list reconstructed)))))

(defun b2-record-update-restore-from-lookup-key-case (branch args lib target openers old known induction tail)
  (let ((facts (car args)))
    (case branch
      (:before (b2-record-update-solve lib target facts openers))
      (:match (b2-record-update-restore-from-lookup-match facts lib known old target openers))
      (otherwise
       (proof-with-checked-results
           ((type-tail (b2-record-update-evidence-at known (list *b2-record-update-rcdp* tail)))
            (inherited (proof-proof-modus-ponens (library-library-proof lib) induction type-tail)))
         (b2-record-update-solve lib target facts openers (list inherited old)))))))

(defun b2-record-update-restore-from-lookup-advance (branch args lib target tail openers)
  (declare (ignore branch))
  (let ((r *b2-record-update-r*)
        (evidence (car args))
        (induction (cadr args)))
    (proof-with-checked-results
        ((known (b2-tactics-tactics-evidence lib evidence))
         (record-cons (b2-record-update-evidence-at known (list *proof-consp* r)))
         (old (b2-tactics-rebuild lib r record-cons)))
      (b2-record-update-prove-key-cases
       lib *b2-record-update-a* r evidence b2-record-update-restore-from-lookup-key-case
       target openers old known induction tail))))

(defun b2-record-update-restore-from-lookup (lib)
  (if (b2-record-update-fact-present-p lib *b2-record-update-restore*)
      (cons *b2-record-update-restore* lib)
    (let* ((r *b2-record-update-r*)
           (lookup (list *b2-record-update-get-aux* *b2-record-update-a* r))
           (update (list *b2-record-update-set-aux* *b2-record-update-a* lookup r))
           (target (proof-eq update r))
           (tail (list *library-cdr* r))
           (openers (list lookup update)))
      (b2-record-update-prove-induction
       lib "RECORD-RESTORE" (list *b2-record-update-rcdp* r) target openers nil
       b2-record-update-restore-from-lookup-advance target tail openers))))

(defun b2-record-update-lookup-other-key-both (sign args lib target openers)
  (declare (ignore sign))
  (b2-record-update-solve lib target (car args) openers))

(defun b2-record-update-lookup-other-key-base (present args lib target openers)
  (if present
      (b2-record-update-choose lib (list *b2-strict-order-strict* *b2-record-update-a* *b2-record-update-b*)
                               (car args) b2-record-update-lookup-other-key-both target openers)
    (b2-record-update-solve lib target (car args) openers)))

(defun b2-record-update-lookup-other-key-earlier-compare (earlier-key args lib before-head head target openers)
  (let ((facts (car args)))
    (proof-with-checked-results
        ((facts (if earlier-key
                    (proof-with-checked-results
                        ((order (b2-record-update-ordered-after
                                 lib *b2-record-update-a* *b2-record-update-b* head (car (last facts)) before-head)))
                      (append facts (list order)))
                  facts)))
      (b2-record-update-solve lib target facts openers))))

(defun b2-record-update-lookup-other-key-earlier-present (has-value args lib before-head head target openers)
  (if has-value
      (b2-record-update-choose
       lib (list *b2-strict-order-strict* *b2-record-update-a* *b2-record-update-b*) (car args)
       b2-record-update-lookup-other-key-earlier-compare before-head head target openers)
    (b2-record-update-solve lib target (car args) openers)))

(defun b2-record-update-lookup-other-key-tail-bound (empty args lib tail head branch head-test)
  (let ((goal (b2-record-update-order-or-empty *b2-record-update-a* tail))
        (signed (car args)))
    (if empty
        (b2-record-update-solve lib goal signed)
      (proof-with-checked-results
          ((next-key (b2-record-update-head-order lib head tail (append branch signed)))
           (order (b2-record-update-ordered-after
                   lib *b2-record-update-a* head (b2-record-update-key tail) head-test next-key)))
        (b2-record-update-solve lib goal (append signed (list order)))))))

(defun b2-record-update-lookup-other-key-match-present (has-value args lib earlier-key tail head head-test
                                                               tail-type target openers)
  (let ((branch (car args)))
    (if (or has-value (not earlier-key))
        (b2-record-update-solve lib target branch openers)
      (proof-with-checked-results
          ((bound (b2-record-update-choose lib (proof-eq tail *proof-false*) nil
                                          b2-record-update-lookup-other-key-tail-bound tail head branch head-test))
           (absent (b2-record-update-lookup-below lib *b2-record-update-a* tail tail-type bound)))
        (b2-record-update-solve lib target branch openers (list absent))))))

(defun b2-record-update-lookup-other-key-match-compare (earlier-key args lib equal-head tail head
                                                               tail-type target openers)
  (let* ((facts (car args))
         (head-test (car (last facts)))
         (field (if earlier-key '(1 2) '(1 1 2)))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reverse (proof-proof-symmetric proof equal-head))
         (update-test (proof-proof-rewrite proof head-test reverse field))
         (update-test (proof-proof-tidy proof update-test)))
      (b2-record-update-choose
       lib *b2-record-update-v* (append facts (list update-test))
       b2-record-update-lookup-other-key-match-present earlier-key tail head head-test tail-type target openers))))

(defun b2-record-update-lookup-other-key-later-case (branch args lib target openers inherited)
  (b2-record-update-solve lib target (car args) openers (and (eq branch :after) (list inherited))))

(defun b2-record-update-lookup-other-key-key-case (branch args lib distinct tail-type induction tail head
                                                          target openers)
  (let* ((facts (car args))
         (proof (library-library-proof lib)))
    (case branch
      (:before (b2-record-update-choose lib *b2-record-update-v* facts
                                       b2-record-update-lookup-other-key-earlier-present
                                       (car (last facts)) head target openers))
      (:match (let ((equal-head (car (last facts))))
                (proof-with-checked-results
                    ((unequal-head (proof-proof-rewrite proof distinct equal-head '(1 1 2)))
                     (unequal-head (proof-proof-tidy proof unequal-head)))
                  (b2-record-update-choose
                   lib (list *b2-strict-order-strict* *b2-record-update-a* head) (append facts (list unequal-head))
                   b2-record-update-lookup-other-key-match-compare equal-head tail head tail-type target openers))))
      (otherwise
       (proof-with-checked-results
           ((literal (proof-step-first induction))
            (antecedent (proof-term-at literal 1))
            (guard (b2-record-update-solve lib antecedent (list tail-type distinct)))
            (inherited (proof-proof-modus-ponens proof induction guard)))
         (b2-record-update-prove-key-cases
          lib *b2-record-update-a* *b2-record-update-r* facts
          b2-record-update-lookup-other-key-later-case target openers inherited))))))

(defun b2-record-update-lookup-other-key-branch (branch args lib distinct tail head target openers)
  (let ((evidence (car args)))
    (if (eq branch :empty)
        (b2-record-update-choose lib *b2-record-update-v* evidence
                                 b2-record-update-lookup-other-key-base target openers)
      (proof-with-checked-results
          ((known (b2-tactics-tactics-evidence lib evidence))
           (different (b2-record-update-evidence-at known distinct))
           (tail-type (b2-record-update-evidence-at known (list *b2-record-update-rcdp* tail))))
        (b2-record-update-prove-key-cases
         lib *b2-record-update-b* *b2-record-update-r* evidence b2-record-update-lookup-other-key-key-case
         different tail-type (cadr args) tail head target openers)))))

(defun b2-record-update-lookup-other-key (lib)
  (if (b2-record-update-fact-present-p lib *b2-record-update-other-key*)
      (cons *b2-record-update-other-key* lib)
    (let* ((a *b2-record-update-a*)
           (b *b2-record-update-b*)
           (r *b2-record-update-r*)
           (update (list *b2-record-update-set-aux* b *b2-record-update-v* r))
           (lookup (list *b2-record-update-get-aux* a update))
           (original (list *b2-record-update-get-aux* a r))
           (target (proof-eq lookup original))
           (typed (list *b2-record-update-rcdp* r))
           (distinct (proof-neg (proof-eq a b)))
           (condition (b2-powers-and-terms (list typed distinct)))
           (tail (list *library-cdr* r))
           (head (b2-record-update-key r))
           (openers (list lookup update original (list *b2-record-update-get-aux* a tail)
                          (list *b2-record-update-get-aux* a *proof-false*))))
      (b2-record-update-prove-induction
       lib "RECORD-LOOKUP-OTHER-KEY" condition target openers t
       b2-record-update-lookup-other-key-branch distinct tail head target openers))))

(defun b2-record-update-get-set-prove (goal conditions lib typed record same-key preserves lookup-rule)
  (proof-with-checked-results
      ((goal-fields (if (integerp goal)
                        '(:failure "tactic-rejected" "")
                      (proof-list-of-length (cdr goal) 2)))
       (call (car goal-fields))
       (expected (cadr goal-fields))
       (set-call (proof-term-at call 2))
       (update-fields (proof-list-of-length set-call 4))
       (update (list *b2-record-update-set-aux* (cadr update-fields) (caddr update-fields) record))
       (valid (b2-record-update-use-fact lib preserves (list *b2-record-update-rcdp* update) (list typed)))
       (inverse (b2-record-update-use-fact
                 lib *b2-record-update-encode-decode*
                 (proof-eq (list *b2-record-update-encode* (list *b2-record-update-decode* update)) update)
                 (list valid)))
       (key (proof-term-at call 1))
       (goal-value (if same-key expected (list *b2-record-update-get-aux* key record)))
       (result (b2-record-update-use-fact lib lookup-rule (proof-eq (list *b2-record-update-get-aux* key update) goal-value)
                                         (append conditions (list typed)))))
    (b2-record-update-solve lib goal conditions (list call set-call expected) (list inverse result))))

(defun b2-record-update-get-set-consequent (premise lib goal typed record same-key preserves lookup-rule)
  (b2-record-update-get-set-prove goal (list premise) lib typed record same-key preserves lookup-rule))

(defun b2-record-update-get-set (lib formula typed record same-key)
  (let* ((type-result (b2-record-update-update-preserves-type lib))
         (preserves (car type-result))
         (lib (cdr type-result)))
    (if (failure-p preserves)
        type-result
      (let* ((lookup-result (if same-key
                                (b2-record-update-lookup-after-update lib)
                              (b2-record-update-lookup-other-key lib)))
             (lookup-rule (car lookup-result))
             (lib (cdr lookup-result)))
        (cond ((failure-p lookup-rule) lookup-result)
              (same-key (cons (b2-record-update-get-set-prove
                               formula nil lib typed record same-key preserves lookup-rule)
                              lib))
              (t (b2-record-update-with-library lib ((parts (proof-list-of-length formula 3)))
                   (cons (b2-record-update-implication
                          lib (cadr parts) (caddr parts) b2-record-update-get-set-consequent
                          (caddr parts) typed record same-key preserves lookup-rule)
                         lib))))))))

(defun b2-record-update-record-law-restore (lib formula call record typed)
  (let* ((restoration (b2-record-update-restore-from-lookup lib))
         (restored (car restoration))
         (lib (cdr restoration)))
    (if (failure-p restored)
        restoration
      (let* ((a *b2-record-update-a*)
             (body (list *b2-record-update-set-aux* a (list *b2-record-update-get-aux* a record) record)))
        (b2-record-update-with-library lib
            ((same (b2-record-update-use-fact lib restored (proof-eq body record) (list typed)))
             (decoded (proof-proof-fact (library-library-proof lib) *b2-record-update-decode-encode*
                                        (list (list *library-x* *b2-record-update-r*))))
             (inner (proof-term-at call 2)))
          (cons (b2-record-update-solve lib formula nil (list call inner) (list same decoded)) lib))))))

(defun b2-record-update-record-law (lib name formula)
  (let* ((encoding (b2-record-update-encoding-lemmas lib))
         (lib (cdr encoding)))
    (if (failure-p (car encoding))
        encoding
      (let ((record (list *b2-record-update-encode* *b2-record-update-r*))
            (same (proof-sym "G-SAME-S" "ACL2"))
            (different (proof-sym "G-DIFF-S" "ACL2")))
        (b2-record-update-with-library lib
            ((typed (proof-proof-fact (library-library-proof lib) *b2-record-update-encode-record*
                                      (list (list *library-x* *b2-record-update-r*)))))
          (if (or (equal name same) (equal name different))
              (b2-record-update-get-set lib formula typed record (equal name same))
            (b2-record-update-with-library lib ((call (proof-term-at formula 1)))
              (b2-record-update-record-law-restore lib formula call record typed))))))))
