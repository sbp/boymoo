(in-package "ACL2")

(include-book "structure-items")

; A supplying statement survives the ground filter unless it is a ground
; declaration.  Only recognized statement kinds can supply a name.

(defthm structure-supplying-line-has-a-statement-word
  (implies (structure-line-supplies-p name line)
           (member-equal (car line)
                         '("package" "hidden-package" "define" "constrain"
                           "choose" "theorem" "axiom" "reserve"))))

(defun structure-first-supplying-line (name lines)
  (cond ((endp lines) nil)
        ((structure-line-supplies-p name (car lines)) (car lines))
        (t (structure-first-supplying-line name (cdr lines)))))

(defthm structure-first-supplying-line-is-a-member
  (implies (structure-lines-supply-p name lines)
           (and (member-equal (structure-first-supplying-line name lines) lines)
                (structure-line-supplies-p name (structure-first-supplying-line name lines))))
  :hints (("Goal" :induct (structure-first-supplying-line name lines)
                  :in-theory (disable structure-line-supplies-p))))

(defthm structure-member-line-supplies
  (implies (and (member-equal line lines) (structure-line-supplies-p name line))
           (structure-lines-supply-p name lines))
  :hints (("Goal" :induct (member-equal line lines)
                  :in-theory (disable structure-line-supplies-p)))
  :rule-classes nil)

(defthm structure-library-order-preserves-supplying-line
  (implies (structure-lines-supply-p name statements)
           (structure-lines-supply-p name (car (bx-library-order statements))))
  :hints (("Goal" :in-theory (disable bx-library-order structure-line-supplies-p
                                      structure-first-supplying-line structure-lines-supply-p
                                      structure-supplying-line-has-a-statement-word)
                  :use ((:instance structure-library-order-keeps-line
                                   (line (structure-first-supplying-line name statements)))
                        (:instance structure-member-line-supplies
                                   (line (structure-first-supplying-line name statements))
                                   (lines (car (bx-library-order statements))))
                        (:instance structure-supplying-line-has-a-statement-word
                                   (line (structure-first-supplying-line name statements)))))))

(defun structure-library-ground-supplies-p (name ground-fns)
  (if (stringp name)
      (member-equal name *structure-ground-packages*)
    (or (member-eq name '(t nil))
        (member-equal name ground-fns)
        (member-equal name *structure-ground-axioms*))))

(defthm structure-ground-filter-of-cons
  (equal (bx-not-ground (cons line rest) ground-fns)
         (append (bx-not-ground (list line) ground-fns)
                 (bx-not-ground rest ground-fns)))
  :hints (("Goal" :in-theory (e/d (bx-not-ground) (bx-introduced subsetp-equal))))
  :rule-classes nil)

(local (defthm structure-ground-member-of-subset
         (implies (and (subsetp-equal part whole) (member-equal name part))
                  (member-equal name whole))))

(defthm structure-supplied-name-of-ground-definition
  (implies (and (equal (car line) "define")
                (structure-event-line-supplies-p name line)
                (subsetp-equal (bx-introduced line) ground-fns))
           (member-equal name ground-fns))
  :hints (("Goal"
           :use ((:instance structure-ground-member-of-subset
                            (part (strip-cars (cdr (cadr line)))) (whole ground-fns)))
           :in-theory (e/d (bx-introduced)
                           (subsetp-equal structure-ground-member-of-subset))))
  :rule-classes nil)

(defthm structure-ground-filter-keeps-supplying-line
  (implies (and (structure-event-line-supplies-p name line)
                (not (structure-library-ground-supplies-p name ground-fns)))
           (equal (bx-not-ground (list line) ground-fns) (list line)))
  :hints (("Goal"
           :use ((:instance structure-supplied-name-of-ground-definition))
           :in-theory (disable bx-introduced subsetp-equal))))

(defthm structure-event-line-coverage-of-append
  (iff (structure-event-lines-supply-p name (append a b))
       (or (structure-event-lines-supply-p name a)
           (structure-event-lines-supply-p name b)))
  :hints (("Goal" :in-theory (disable structure-event-line-supplies-p))))

(defthm structure-library-filter-keeps-name
  (implies (and (structure-event-lines-supply-p name lines)
                (not (structure-library-ground-supplies-p name ground-fns)))
           (structure-event-lines-supply-p name (bx-not-ground lines ground-fns)))
  :hints (("Goal" :induct (structure-event-lines-supply-p name lines)
                  :in-theory (disable structure-event-line-supplies-p
                                      structure-library-ground-supplies-p bx-not-ground))
          ("Subgoal *1/1" :in-theory (enable bx-not-ground))
          ("Subgoal *1/2"
           :use ((:instance structure-ground-filter-of-cons (line (car lines)) (rest (cdr lines)))))))
