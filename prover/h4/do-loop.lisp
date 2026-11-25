(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h4-do-loop-first-ruling (evidence)
  (if (endp evidence)
      '(:failure "failure" "")
    (proof-with-checked-results
      ((literal (proof-step-first (car evidence))))
      (if (proof-is-call literal *h4-lexicographic-l-less*)
          (car evidence)
        (h4-do-loop-first-ruling (cdr evidence))))))

(defun h4-do-loop-do-congruence-descends-restore
  (p ruling literal expected initial)
  (if (equal literal expected)
      ruling
    (if (not (equal (seq-slice literal :none 2) (seq-slice expected :none 2)))
        '(:failure "failure" "")
      (proof-with-checked-results
        ((fixed (proof-term-at literal 2))
         (old-measure (proof-term-at fixed 1)))
        (if (not (proof-is-call old-measure *proof-if*))
            '(:failure "failure" "")
          (let ((goal (proof-eq old-measure initial))
                (proof (library-library-proof p)))
            (proof-with-checked-results
              ((test (proof-term-at old-measure 1))
               (positive (proof-proof-assume proof test t))
               (yes (h4-tactics-tactics-normalize p old-measure (list positive) nil nil nil))
               (negative (proof-proof-assume proof test nil))
               (no (h4-tactics-tactics-normalize p old-measure (list negative) nil nil nil))
               (restored (h4-tactics-tactics-case-of p goal test yes no)))
              (proof-proof-rewrite proof ruling restored (list 1 2 1)))))))))

(defun h4-do-loop-do-congruence-descends (comparison evidence p embedding initial)
  (proof-with-checked-results
    ((left (proof-term-at comparison 1))
     (left-arg (proof-term-at left 1))
     (right (proof-term-at comparison 2))
     (right-arg (proof-term-at right 1))
     (ruling (h4-do-loop-first-ruling evidence))
     (literal (proof-step-first ruling)))
    (let ((expected (list *h4-lexicographic-l-less* left-arg right-arg)))
      (proof-with-checked-results
        ((ruling (h4-do-loop-do-congruence-descends-restore p ruling literal expected initial))
         (literal (proof-step-first ruling)))
        (if (equal literal expected)
            (h4-lexicographic-embedding-fixed-ordinal-order
             (h4-lexicographic-embedding-with-p embedding p) ruling)
          '(:failure "failure" ""))))))

(defun h4-do-loop-answer-descent-request
  (outcome p formula measure ordinal embedding initial replies)
  (let ((comparison (cadr outcome))
        (evidence (caddr outcome))
        (current (cadddr outcome)))
    (proof-with-checked-results
      ((step (h4-do-loop-do-congruence-descends comparison evidence current embedding initial))
       (replies (table-put replies (list comparison evidence) (cons step current)))
       (caller (h4-function-equality-caller-congruence-init
                p formula measure (list :callback replies))))
      (cons (h4-function-equality-caller-congruence-prove caller ordinal) replies))))

; Pending holds the result of the current proof attempt and its replies.
(defun h4-do-loop-prove-with-descent
  (n pending p formula measure ordinal embedding initial)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-do-loop-prove-with-descent"))
   ((failure-p pending) pending)
   ((failure-p (car pending)) (car pending))
   ((eq (caar pending) :h4-function-equality-descent-request)
    (h4-do-loop-prove-with-descent
     (1- n) (h4-do-loop-answer-descent-request
             (car pending) p formula measure ordinal embedding initial (cdr pending))
     p formula measure ordinal embedding initial))
   (t (cons (caar pending)
            (h4-function-equality-caller-congruence-p (cdar pending))))))

(defun h4-do-loop-do-congruence (p formula)
  (proof-with-checked-results
    ((p (h4-tactics-tactics-propositional-lemmas p))
     (embedding (h4-lexicographic-embedding-init p))
     (goal (proof-term-at formula 2))
     (sides (proof-list-of-length goal 3))
     (arguments (if (integerp (cadr sides))
                    '(:failure "failure" "")
                  (proof-list-of-length (seq-slice (cadr sides) 1 3) 2))))
    (let* ((initial (list *h4-function-equality-apply*
                          (car arguments) (list *proof-cons* (cadr arguments) *proof-false*)))
           (fixed (list *h4-lexicographic-lex-fix* initial))
           (measure (list *h4-lexicographic-lex-ordinal* fixed))
           (p (h4-lexicographic-embedding-p embedding)))
      (proof-with-checked-results
        ((caller (h4-function-equality-caller-congruence-init
                  p formula measure (list :callback nil)))
         (ordinal (h4-lexicographic-embedding-fact
                   embedding (h4-lexicographic-embedding-ordinal embedding) fixed :none)))
        (h4-do-loop-prove-with-descent
         1000000 (list (h4-function-equality-caller-congruence-prove caller ordinal))
         p formula measure ordinal embedding initial)))))
