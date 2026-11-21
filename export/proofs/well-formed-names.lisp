(in-package "ACL2")

(include-book "well-formed-items")

(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/strings/explode-nonnegative-integer" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(set-verify-guards-eagerness 0)

;;; A source for a made name consists of its function, its kind and,
;;; for an unnamed formula in a stored constraint, its position.

(defun wf-constraint-name-source-p (fn kind position)
  (and (symbolp fn)
       (case kind
         ((:definition :choice) (eql position 0))
         (:constraint (posp position))
         (otherwise nil))))

(defun wf-constraint-name-word (kind position)
  (case kind
    (:definition "definition")
    (:choice "choice")
    (otherwise
     (concatenate 'string "constraint "
                  (coerce (explode-nonnegative-integer position 10 nil) 'string)))))

(local
 (defthm wf-symbolp-of-constraint-name-source
   (implies (wf-constraint-name-source-p fn kind position) (symbolp fn))
   :rule-classes :forward-chaining))

;;; Read the spelling from its end. Every suffix field is separated
;;; by a space. The letters in the kind distinguish a kind from a
;;; decimal field, and any spaces in the source name are retained.

(local
 (defun wf-name-token (chars)
   (if (or (atom chars) (eql (car chars) #\Space))
       nil
     (cons (car chars) (wf-name-token (cdr chars))))))

(local
 (defun wf-after-name-token (chars)
   (cond ((atom chars) nil)
         ((eql (car chars) #\Space) (cdr chars))
         (t (wf-after-name-token (cdr chars))))))

(local (defconst *wf-definition-token* (rev (coerce "definition" 'list))))
(local (defconst *wf-choice-token* (rev (coerce "choice" 'list))))
(local (defconst *wf-constraint-token* (rev (coerce "constraint" 'list))))

(local
 (defun wf-source-from-reversed-name (chars)
   (let ((token (wf-name-token chars))
         (rest (wf-after-name-token chars)))
     (cond ((equal token *wf-definition-token*) (list rest :definition nil))
           ((equal token *wf-choice-token*) (list rest :choice nil))
           (t (let ((second (wf-name-token rest))
                    (rest (wf-after-name-token rest)))
                (cond ((equal second *wf-definition-token*) (list rest :definition nil))
                      ((equal second *wf-choice-token*) (list rest :choice nil))
                      ((equal second *wf-constraint-token*) (list rest :constraint token))
                      (t (list (wf-after-name-token rest) :constraint second)))))))))

;;; A token can be read without inspecting the text after its space.
;;; Decimal tokens contain no delimiter and differ from the kind words.

(local
 (defthm wf-split-name-at-delimiter
   (implies (not (member-equal #\Space prefix))
            (and (equal (wf-name-token (append prefix (cons #\Space tail)))
                        (list-fix prefix))
                 (equal (wf-after-name-token (append prefix (cons #\Space tail)))
                        tail)))
   :hints (("Goal" :induct (len prefix)))))

(local
 (defun wf-decimal-chars-p (chars)
   (if (consp chars)
       (and (member-equal (car chars) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
            (wf-decimal-chars-p (cdr chars)))
     (null chars))))

(local
 (defthm wf-decimal-chars-of-explode
   (implies (wf-decimal-chars-p acc)
            (wf-decimal-chars-p (explode-nonnegative-integer n 10 acc)))
   :hints (("Goal" :induct (explode-nonnegative-integer n 10 acc)
            :in-theory (e/d (digit-to-char) (floor mod))))))

(local
 (defthm wf-decimal-chars-of-append
   (implies (and (wf-decimal-chars-p a) (wf-decimal-chars-p b))
            (wf-decimal-chars-p (append a b)))))

(local
 (defthm wf-decimal-chars-of-rev
   (implies (wf-decimal-chars-p chars)
            (wf-decimal-chars-p (rev chars)))
   :hints (("Goal" :induct (len chars)))))

(local
 (defthm wf-no-space-in-decimal-chars
   (implies (wf-decimal-chars-p chars)
            (not (member-equal #\Space chars)))
   :hints (("Goal" :induct (len chars)))))

(local
 (defthm wf-decimal-chars-differ-from-kind-words
   (implies (wf-decimal-chars-p chars)
            (and (not (equal chars *wf-definition-token*))
                 (not (equal chars *wf-choice-token*))
                 (not (equal chars *wf-constraint-token*))))))

;;; Recover the source from any candidate's spelling, including a
;;; spelling with a decimal retry number after the kind and position.

(local
 (defun wf-candidate-name (fn kind position retry)
   (let ((base (concatenate 'string (symbol-name fn) " "
                            (wf-constraint-name-word kind position))))
     (if (equal retry 0)
         base
       (concatenate 'string base " "
                    (coerce (explode-nonnegative-integer retry 10 nil) 'string))))))

(local
 (defun wf-reversed-name-source (fn kind position)
   (list (rev (coerce (symbol-name fn) 'list))
         kind
         (and (eq kind :constraint)
              (rev (explode-nonnegative-integer position 10 nil))))))

(local
 (defthm wf-candidate-name-recovers-source
   (implies (wf-constraint-name-source-p fn kind position)
            (equal (wf-source-from-reversed-name
                     (rev (coerce (wf-candidate-name fn kind position retry) 'list)))
                   (wf-reversed-name-source fn kind position)))
   :hints (("Goal" :in-theory (disable explode-nonnegative-integer)))))

(local
 (defthm wf-fresh-name-recovers-source
   (let* ((base (concatenate 'string (symbol-name fn) " "
                             (wf-constraint-name-word kind position)))
          (name (bx-fresh-name base retry fn wrld fuel)))
     (implies (and (wf-constraint-name-source-p fn kind position) name)
              (equal (wf-source-from-reversed-name (rev (coerce (symbol-name name) 'list)))
                     (wf-reversed-name-source fn kind position))))
   :hints (("Goal"
            :induct (bx-fresh-name
                     (concatenate 'string (symbol-name fn) " "
                                  (wf-constraint-name-word kind position))
                     retry fn wrld fuel)
            :in-theory (disable wf-source-from-reversed-name wf-reversed-name-source
                                wf-constraint-name-word wf-constraint-name-source-p
                                wf-candidate-name-recovers-source
                                string-append bx-in-use-p keywordp
                                explode-nonnegative-integer))
           ("Subgoal *1/1" :use wf-candidate-name-recovers-source))))

(local
 (defthm wf-formula-name-recovers-source
   (let ((name (bx-formula-name fn (wf-constraint-name-word kind position) wrld)))
     (implies (and (wf-constraint-name-source-p fn kind position) name)
              (and (equal (symbol-package-name name) (symbol-package-name fn))
                   (equal (wf-source-from-reversed-name (rev (coerce (symbol-name name) 'list)))
                          (wf-reversed-name-source fn kind position)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance wf-fresh-name-recovers-source
                             (retry 0) (fuel *bx-name-tries*))
                  (:instance well-formed-fresh-constraint-name
                             (base (concatenate 'string (symbol-name fn) " "
                                                (wf-constraint-name-word kind position)))
                             (i 0) (fuel *bx-name-tries*)))
            :in-theory (disable bx-fresh-name string-append
                                wf-fresh-name-recovers-source well-formed-fresh-constraint-name
                                wf-constraint-name-source-p wf-constraint-name-word
                                wf-source-from-reversed-name wf-reversed-name-source)))))

(local
 (defthm wf-reversed-name-source-is-injective-in-package
   (implies (and (wf-constraint-name-source-p fn1 kind1 position1)
                 (wf-constraint-name-source-p fn2 kind2 position2)
                 (equal (symbol-package-name fn1) (symbol-package-name fn2))
                 (equal (wf-reversed-name-source fn1 kind1 position1)
                        (wf-reversed-name-source fn2 kind2 position2)))
            (and (equal fn1 fn2) (equal kind1 kind2) (equal position1 position2)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance symbol-equality (s1 fn1) (s2 fn2)))
            :in-theory (disable explode-nonnegative-integer)))))

;;; Equal, nonempty made names identify the same source. The two
;;; lookups may run against different worlds and try different numbers.

(defthm well-formed-equal-made-names-have-same-source
  (let ((name1 (bx-formula-name fn1 (wf-constraint-name-word kind1 position1) wrld1))
        (name2 (bx-formula-name fn2 (wf-constraint-name-word kind2 position2) wrld2)))
    (implies (and (wf-constraint-name-source-p fn1 kind1 position1)
                  (wf-constraint-name-source-p fn2 kind2 position2)
                  name1
                  (equal name1 name2))
             (and (equal fn1 fn2)
                  (equal kind1 kind2)
                  (equal position1 position2))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance wf-formula-name-recovers-source
                            (fn fn1) (kind kind1) (position position1) (wrld wrld1))
                 (:instance wf-formula-name-recovers-source
                            (fn fn2) (kind kind2) (position position2) (wrld wrld2))
                 wf-reversed-name-source-is-injective-in-package)
           :in-theory (disable bx-formula-name
                               wf-constraint-name-source-p wf-constraint-name-word
                               wf-source-from-reversed-name wf-reversed-name-source))))
