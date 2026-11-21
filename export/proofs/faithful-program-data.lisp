(in-package "ACL2")

(include-book "faithful-reserve")

; For a translated program body, the execution of an MBE is the
; execution of its executable argument. Apply this inside lambda bodies
; and actual arguments while leaving quoted data intact.

(defun faithful-executable-term (term argument-list-p)
  (declare (xargs :measure (acl2-count term)))
  (if argument-list-p
      (if (consp term)
          (cons (faithful-executable-term (car term) nil)
                (faithful-executable-term (cdr term) t))
        nil)
    (cond ((atom term) term)
          ((eq (car term) 'quote) term)
          ((and (eq (car term) 'return-last)
                (equal (cadr term) ''mbe1-raw))
           (faithful-executable-term (caddr term) nil))
          (t (cons (if (consp (car term))
                       (list 'lambda (cadar term)
                             (faithful-executable-term (caddar term) nil))
                     (car term))
                   (faithful-executable-term (cdr term) t))))))

(defund faithful-executable-half (term)
  (faithful-executable-term term nil))

(defund faithful-program-class-p (fn wrld)
  (eq (getprop fn 'symbol-class nil 'current-acl2-world wrld) :program))

(defund faithful-supplied-program-body (fn translations wrld)
  (or (getprop fn 'unnormalized-body nil 'current-acl2-world wrld)
      (let ((translation (cdr (assoc-equal fn translations))))
        (and (eq (car translation) :ok) (cdr translation)))))

(defund faithful-program-definition-p (definition translations wrld)
  (let* ((fn (car definition))
         (formals (getprop fn 'formals nil 'current-acl2-world wrld))
         (stored (getprop fn 'unnormalized-body nil 'current-acl2-world wrld)))
    (if (faithful-program-class-p fn wrld)
        (let ((body (faithful-supplied-program-body fn translations wrld)))
          (and body
               (equal definition
                      (list fn formals (faithful-executable-half body)))))
      (equal definition (list fn formals stored)))))

(defun faithful-program-definitions-p (definitions translations wrld)
  (if (atom definitions)
      (null definitions)
    (and (faithful-program-definition-p (car definitions) translations wrld)
         (faithful-program-definitions-p (cdr definitions) translations wrld))))

(defthm faithful-empty-program-definitions
  (faithful-program-definitions-p nil translations wrld)
  :hints (("Goal" :expand ((faithful-program-definitions-p nil translations wrld)))))

(defun faithful-nonprogram-fns-p (fns wrld)
  (if (endp fns)
      t
    (and (not (faithful-program-class-p (car fns) wrld))
         (faithful-nonprogram-fns-p (cdr fns) wrld))))

; Single-threaded object events supply program bodies directly from the
; world. A program-mode function of such an event must have a body.

(defun faithful-stobj-program-names-p (names wrld)
  (if (endp names)
      t
    (and (or (not (faithful-program-class-p (car names) wrld))
             (eq (getprop (car names) 'formals t 'current-acl2-world wrld) t)
             (getprop (car names) 'unnormalized-body nil
                      'current-acl2-world wrld))
         (faithful-stobj-program-names-p (cdr names) wrld))))

(defun faithful-stobj-program-events-p (triples wrld)
  (if (endp triples)
      t
    (let ((event (cddar triples)))
      (and (or (not (and (eq (caar triples) 'event-landmark)
                         (eq (cadar triples) 'global-value)
                         (member-eq (access-event-tuple-type event)
                                    '(defstobj defabsstobj))))
               (faithful-stobj-program-names-p (faithful-event-names event) wrld))
           (faithful-stobj-program-events-p (cdr triples) wrld)))))

(defund faithful-stobj-program-world-p (wrld)
  (faithful-stobj-program-events-p wrld wrld))

; Compare the two bodies and prove that the program definition
; constructors use recorded formals and the specified source of a body.

(local
 (defthm faithful-executable-term-of-bx
   (equal (faithful-executable-term term argument-list-p)
          (if argument-list-p (bx-exec-lst term) (bx-exec term)))
   :hints (("Goal" :induct (faithful-executable-term term argument-list-p)))))

(defthm faithful-bx-exec-agrees
  (equal (bx-exec term) (faithful-executable-half term))
  :hints (("Goal" :in-theory (e/d (faithful-executable-half)
                                  (bx-exec faithful-executable-term)))))

(defthm faithful-bx-programp-agrees
  (equal (bx-programp fn wrld) (faithful-program-class-p fn wrld))
  :hints (("Goal" :in-theory (e/d (faithful-program-class-p) (fgetprop)))))

(defthm faithful-bx-some-program-agrees
  (equal (not (bx-some-program-p fns wrld))
         (faithful-nonprogram-fns-p fns wrld))
  :hints (("Goal" :in-theory (disable bx-programp))))

(local
 (defthm faithful-body-from-bx-program-body
   (implies (car (bx-program-body fn form translations wrld))
            (equal (car (bx-program-body fn form translations wrld))
                   (faithful-supplied-program-body fn translations wrld)))
   :hints (("Goal" :in-theory (e/d (faithful-supplied-program-body)
                                   (bx-defun-forms fgetprop))))))

(local
 (defthm faithful-program-definitions-of-revappend
   (implies (and (faithful-program-definitions-p a translations wrld)
                 (faithful-program-definitions-p b translations wrld))
            (faithful-program-definitions-p (revappend a b) translations wrld))
   :hints (("Goal" :induct (revappend a b)))))

(defthm faithful-program-definitions-of-bx-defs
  (implies (and (plist-worldp-with-formals wrld)
                (faithful-nonprogram-fns-p fns wrld))
           (faithful-program-definitions-p (bx-defs fns wrld) translations wrld))
  :hints (("Goal" :induct (bx-defs fns wrld)
           :in-theory (e/d (faithful-program-definition-p)
                           (formals fgetprop plist-worldp-with-formals)))))

(local
 (defthm faithful-program-definition-from-bx-program-body
   (let ((body (car (bx-program-body fn form translations wrld))))
     (implies (and (plist-worldp-with-formals wrld)
                   (faithful-program-class-p fn wrld)
                   body)
              (faithful-program-definition-p
               (list fn (getprop fn 'formals nil 'current-acl2-world wrld)
                     (bx-exec body))
               translations wrld)))
   :hints (("Goal"
            :use faithful-body-from-bx-program-body
            :in-theory (e/d (faithful-program-definition-p)
                            (bx-program-body faithful-body-from-bx-program-body
                             bx-exec fgetprop plist-worldp-with-formals))))))

(defthm faithful-program-definitions-of-bx-program-defs
  (implies (and (plist-worldp-with-formals wrld)
                (bx-all-program-p fns wrld)
                (not (stringp defs))
                (faithful-program-definitions-p defs translations wrld))
           (faithful-program-definitions-p
            (car (bx-program-defs fns form translations wrld defs notes))
            translations wrld))
  :hints (("Goal"
           :induct (bx-program-defs fns form translations wrld defs notes)
           :in-theory (disable bx-program-body bx-exec bx-programp formals fgetprop
                               faithful-bx-exec-agrees
                               faithful-body-from-bx-program-body
                               plist-worldp-with-formals))))

(local
 (defthm faithful-stobj-record-of-landmark
   (implies (and (faithful-stobj-program-events-p triples wrld)
                 (faithful-event-landmark-p event triples)
                 (member-eq (access-event-tuple-type event) '(defstobj defabsstobj)))
            (faithful-stobj-program-names-p (faithful-event-names event) wrld))
   :hints (("Goal" :induct (faithful-stobj-program-events-p triples wrld)
            :in-theory (e/d (faithful-event-landmark-p)
                            (access-event-tuple-type faithful-event-names
                             faithful-stobj-program-names-p))))))

(defthm faithful-stobj-program-record-from-world
  (implies (and (faithful-stobj-program-world-p wrld)
                (faithful-event-landmark-p event wrld)
                (member-eq (access-event-tuple-type event) '(defstobj defabsstobj)))
           (faithful-stobj-program-names-p (faithful-event-names event) wrld))
  :hints (("Goal"
           :use ((:instance faithful-stobj-record-of-landmark (triples wrld)))
           :in-theory (e/d (faithful-stobj-program-world-p)
                           (faithful-stobj-program-events-p
                            faithful-stobj-program-names-p
                            faithful-event-names access-event-tuple-type
                            faithful-stobj-record-of-landmark))))
  :rule-classes nil)
