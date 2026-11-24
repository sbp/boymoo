(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-completions-char-eq* (proof-sym "CHAREQV$INLINE" "ACL2"))
(defconst *b2-completions-str-eq* (proof-sym "STREQV$INLINE" "ACL2"))
(defconst *b2-completions-char-fix* (proof-sym "CHAR-FIX$INLINE" "ACL2"))
(defconst *b2-completions-str-fix* (proof-sym "STR-FIX$INLINE" "ACL2"))
(defconst *b2-completions-characterp* (proof-cl "CHARACTERP"))
(defconst *b2-completions-stringp* (proof-cl "STRINGP"))
(defconst *b2-completions-code* (proof-cl "CHAR-CODE"))
(defconst *b2-completions-coerce* (proof-cl "COERCE"))
(defconst *b2-completions-bitp* (proof-sym "BITP" "ACL2"))
(defconst *b2-completions-posp* (proof-sym "POSP" "ACL2"))
(defconst *b2-completions-bfix* (proof-sym "BFIX$INLINE" "ACL2"))
(defconst *b2-completions-list* (proof-quote (proof-cl "LIST")))

(defconst *b2-completions-fixes*
  (list (list *b2-completions-char-eq* *b2-completions-characterp*
              *b2-completions-char-fix* *b2-completions-code* nil "COMPLETION-OF-CHAR-CODE")
        (list *b2-completions-str-eq* *b2-completions-stringp* *b2-completions-str-fix*
              *b2-completions-coerce* (list *b2-completions-list*) "COMPLETION-OF-COERCE")))

(defconst *b2-completions-fixed-equivalence*
  '( ("sym" "ACL2" "CHAREQV-OF-CHAR-FIX")
     ("sym" "ACL2" "STREQV-OF-STR-FIX")))

(defconst *b2-completions-observation-congruence*
  '( ("sym" "ACL2" "CHAREQV-IMPLIES-EQUAL-CHAR-CODE-1")
     ("sym" "ACL2" "CHAREQV-IMPLIES-EQUAL-CHAR<-1")
     ("sym" "ACL2" "CHAREQV-IMPLIES-EQUAL-CHAR<-2")
     ("sym" "ACL2" "STREQV-IMPLIES-EQUAL-CHAR-1")
     ("sym" "ACL2" "STREQV-IMPLIES-EQUAL-STRING-APPEND-1")
     ("sym" "ACL2" "STREQV-IMPLIES-EQUAL-STRING-APPEND-2")))

(defconst *b2-completions-maybe-types*
  '( ("sym" "ACL2" "MAYBE-NATP-COMPOUND-RECOGNIZER")
     ("sym" "ACL2" "MAYBE-BITP-COMPOUND-RECOGNIZER")
     ("sym" "ACL2" "MAYBE-INTEGERP-COMPOUND-RECOGNIZER")
     ("sym" "ACL2" "MAYBE-POSP-COMPOUND-RECOGNIZER")))

(defconst *b2-completions-bit-identity* (proof-sym "BFIX-BITP" "ACL2"))
(defconst *b2-completions-mv-cons* (proof-sym "MV-NTH-OF-CONS" "ACL2"))

(defconst *b2-completions-completion-theorems*
  (append *b2-completions-fixed-equivalence* *b2-completions-observation-congruence*
          *b2-completions-maybe-types* (list *b2-completions-bit-identity* *b2-completions-mv-cons*)))

(defun b2-completions-fix (relation)
  (let ((entry (assoc-equal relation *b2-completions-fixes*)))
    (if entry (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-completions-observation-branch (valid evidence lib goal fix completion)
  (b2-tactics-tactics-solve lib goal evidence (list fix) (if valid nil (list completion)) 0 nil))

(defun b2-completions-choice-p (call)
  (and (eq (car call) :call) (eq (cadr call) :choose)))

(defun b2-completions-solve-branch (call goal unfold completion splits branches)
  (let ((lib (caddr call))
        (sign (cadddr call))
        (evidence (car (cddddr call))))
    (proof-with-checked-results
        ((step (if completion
                   (b2-completions-observation-branch sign evidence lib goal (car unfold) completion)
                 (b2-tactics-tactics-solve lib goal evidence unfold nil splits branches))))
      (cons step lib))))

(defun b2-completions-solve-choice (lib test evidence goal unfold completion splits branches)
  (proof-with-checked-results
      ((request (b2-tactics-choose lib test evidence nil))
       (call (car request)))
    (if (not (b2-completions-choice-p call)) request
      (proof-with-checked-results
          ((first (b2-completions-solve-branch call goal unfold completion splits branches))
           (answer (b2-tactics-choose lib test evidence (list first)))
           (next-call (car answer)))
        (if (not (b2-completions-choice-p next-call)) answer
          (proof-with-checked-results
              ((second (b2-completions-solve-branch next-call goal unfold completion splits branches)))
            (b2-tactics-choose lib test evidence (list first second))))))))

(defun b2-completions-observation-lemma (lib label kind fix reader extras rule)
  (let* ((before (list* reader *library-x* extras))
         (after (list* reader (list fix *library-x*) extras))
         (goal (proof-eq before after)))
    (proof-with-checked-results
        ((completion (library-library-axiom lib rule (cons *library-x* extras)))
         (proof (b2-completions-solve-choice lib (list kind *library-x*) nil goal (list fix) completion 0 nil))
         (step (car proof))
         (added (b2-tactics-tactics-add-lemma (cdr proof) label step :none)))
      (cdr added))))

(defun b2-completions-observation (lib relation value)
  (proof-with-checked-results ((recipe (b2-completions-fix relation)))
    (let* ((reader (caddr recipe))
           (label (concatenate 'string "FIXED-" (caddr reader)))
           (name (proof-sym (concatenate 'string "B2-" label) "ACL2"))
           (facts (proof-proof-facts (library-library-proof lib))))
      (proof-with-checked-results
          ((lib (if (assoc-equal name facts) lib
                  (b2-completions-observation-lemma lib label (car recipe) (cadr recipe) reader
                                                   (cadddr recipe) (car (cddddr recipe)))))
           (step (proof-proof-fact (library-library-proof lib) name (list (list *library-x* value)))))
        (cons step lib)))))

(defun b2-completions-completed-equivalence (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (recipe (b2-completions-fix (car parts)))
       (result (b2-completions-solve-choice lib (list (car recipe) (caddr parts)) nil
                                           formula (list formula (cadr recipe)) nil 0 nil)))
    (car result)))

(defun b2-completions-goal-openers (terms definitions)
  (if (endp terms) nil
    (proof-with-checked-results
        ((head (proof-term-at (car terms) 0))
         (rest (b2-completions-goal-openers (cdr terms) definitions)))
      (if (assoc-equal head definitions) (cons (car terms) rest) rest))))

(defun b2-completions-completion-theorem-prove (premise lib relation left right goal)
  (proof-with-checked-results
      ((fixed (b2-equivalences-equality-of-fixed lib premise))
       (first (b2-completions-observation lib relation left))
       (last (b2-completions-observation (cdr first) relation right))
       (lib (cdr last))
       (proof (library-library-proof lib))
       (first-literal (proof-step-first (car first)))
       (right-side (proof-term-at first-literal 2))
       (reflexive (proof-proof-reflexive proof right-side))
       (middle (proof-proof-rewrite proof reflexive fixed '(1 2 1)))
       (reverse-last (proof-proof-symmetric proof (car last)))
       (rule (proof-proof-chain proof (car first) (list middle reverse-last)))
       (opens (b2-completions-goal-openers (cdr goal) (proof-proof-definitions proof)))
       (step (b2-tactics-tactics-solve lib goal nil opens (list rule) 0 nil)))
    (cons step lib)))

(defun b2-completions-observation-congruence (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (condition (proof-list-of-length (cadr parts) 3))
       (goal (caddr parts))
       (answer (b2-tactics-tactics-implication lib condition goal nil))
       (request (car answer))
       (reply (b2-completions-completion-theorem-prove (cadddr request) (caddr request)
                                                       (car condition) (cadr condition) (caddr condition)
                                                       goal)))
    (b2-tactics-tactics-implication lib condition goal reply)))

(defun b2-completions-maybe-type (lib formula)
  (proof-with-checked-results
      ((call (proof-term-at formula 1))
       (test (proof-term-at call 1)))
    (b2-completions-solve-choice lib test nil formula
                                 (list call *library-natp* *b2-completions-posp* *b2-completions-bitp*)
                                 nil 4 t)))

(defun b2-completions-bit-branch (call value formula)
  (let ((lib (caddr call))
        (evidence (car (cddddr call)))
        (unfold (list *b2-completions-bitp* *b2-completions-bfix*)))
    (if (cadddr call)
        (proof-with-checked-results ((step (b2-tactics-tactics-solve lib formula evidence unfold nil 0 nil)))
          (cons step lib))
      (b2-completions-solve-choice lib (proof-eq value *proof-one*) evidence formula unfold nil 0 nil))))

(defun b2-completions-bit-cases (lib formula value)
  (let ((test (proof-eq value *proof-zero*)))
    (proof-with-checked-results
        ((request (b2-tactics-choose lib test nil nil))
         (call (car request)))
      (if (not (b2-completions-choice-p call)) request
        (proof-with-checked-results
            ((first (b2-completions-bit-branch call value formula))
             (answer (b2-tactics-choose lib test nil (list first)))
             (next-call (car answer)))
          (if (not (b2-completions-choice-p next-call)) answer
            (proof-with-checked-results ((second (b2-completions-bit-branch next-call value formula)))
              (b2-tactics-choose lib test nil (list first second)))))))))

(defun b2-completions-mv-cons (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length (cdr formula) 2))
       (condition (car parts))
       (selector (proof-term-at (cadr parts) 1))
       (argument (proof-term-at selector 1)))
    (b2-completions-solve-choice lib (list *b2-projections-zp* argument) nil
                                 formula (list condition selector) nil 0 nil)))

(defun b2-completions-completion-theorem (lib name formula)
  (cond
   ((member-equal name *b2-completions-fixed-equivalence*)
    (proof-with-checked-results ((step (b2-completions-completed-equivalence lib formula)))
      (cons step lib)))
   ((member-equal name *b2-completions-observation-congruence*)
    (b2-completions-observation-congruence lib formula))
   ((member-equal name *b2-completions-maybe-types*) (b2-completions-maybe-type lib formula))
   ((equal name *b2-completions-bit-identity*)
    (proof-with-checked-results
        ((call (proof-term-at formula 1))
         (value (proof-term-at call 1)))
      (b2-completions-bit-cases lib formula value)))
   (t (b2-completions-mv-cons lib formula))))
