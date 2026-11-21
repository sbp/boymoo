(in-package "ACL2")

(include-book "core")
(include-book "structure-spec")

; ACL2's event landmarks are property-list world entries.  The tuple
; convention is specified by MAKE-EVENT-TUPLE and ACCESS-EVENT-TUPLE-NAMEX
; in ACL2's translate.lisp.  A local marker precedes the tuple.  The
; second field is either the head of a compact form or the event's header.

(defun structure-event-tuple (record)
  (if (eq (car record) 'local) (cdr record) record))

(defun structure-event-number (record)
  (let ((number-field (car (structure-event-tuple record))))
    (if (integerp number-field) number-field (car number-field))))

(defun structure-event-kind (record)
  (let* ((tuple (structure-event-tuple record))
         (header (cadr tuple)))
    (cond ((symbolp (cdr tuple)) nil)
          ((eq header 'mutual-recursion) 'defuns)
          ((symbolp header) header)
          (t (caar header)))))

(defun structure-event-class (record)
  (let ((header (cadr (structure-event-tuple record))))
    (if (symbolp header) :program (cddr header))))

(defun structure-signature-names (signatures)
  (if (endp signatures)
      nil
    (let ((first-field (caar signatures)))
      (cons (if (consp first-field) (car first-field) first-field)
            (structure-signature-names (cdr signatures))))))

(defun structure-event-namex (record)
  (let* ((tuple (structure-event-tuple record))
         (form (cdr tuple))
         (header (car form)))
    (cond ((symbolp form) nil)
          ((not (symbolp header)) (cadr header))
          ((eq header 'defuns) (strip-cars (cdr form)))
          ((eq header 'mutual-recursion) (strip-cadrs (cdr form)))
          ((eq header 'encapsulate) (structure-signature-names (cadr form)))
          ((member-eq header '(verify-guards in-theory in-arithmetic-theory
                               regenerate-tau-database push-untouchable
                               remove-untouchable reset-prehistory set-body table))
           0)
          (t (cadr form)))))

(defun structure-event-names (record)
  (let ((namex (structure-event-namex record)))
    (cond ((eql namex 0) nil)
          ((and (null namex) (not (eq (structure-event-kind record) 'defconst)))
           nil)
          ((or (symbolp namex) (stringp namex)) (list namex))
          (t namex))))

(defun structure-event-landmarkp (entry)
  (and (eq (car entry) 'event-landmark)
       (eq (cadr entry) 'global-value)))

; Range membership means exactly LO < number <= HI for a landmark found
; anywhere in the world.  Numbered landmarks are in decreasing order.

(defun structure-event-in-rangep (record lo hi wrld)
  (let ((number (structure-event-number record)))
    (and (integerp number)
         (< lo number)
         (<= number hi)
         (member-equal (list* 'event-landmark 'global-value record) wrld))))

(defun structure-decreasing-landmarks-p (wrld upper)
  (cond ((endp wrld) t)
        ((structure-event-landmarkp (car wrld))
         (let ((number (structure-event-number (cddar wrld))))
           (and (integerp number)
                (or (null upper) (< number upper))
                (structure-decreasing-landmarks-p (cdr wrld) number))))
        (t (structure-decreasing-landmarks-p (cdr wrld) upper))))

; An include-book record names the file, which introduces no name of its
; own.  Program-only definitions likewise owe no statement.  The record
; that moves a program function into logic mode is a definition in its
; own right.

(defun structure-program-or-file-p (name record wrld)
  (let ((kind (structure-event-kind record)))
    (or (eq kind 'include-book)
        (and (member-eq kind '(defun defuns))
             (eq (structure-event-class record) :program))
        (and (member-eq kind '(defstobj defabsstobj))
             (eq (getpropc name 'symbol-class nil wrld) :program)
             (not (eq (getpropc name 'formals t wrld) t))))))

; These are the ACL2 names that require an individual statement or
; coverage by a constraint.  Other event kinds can still take a name.
; For those, ACL2's function, theorem and reserved-name properties say
; whether the name uses the statement namespace.

(defun structure-event-kind-with-statements-p (kind)
  (member-eq kind '(defun defuns defthm defaxiom defchoose encapsulate defpkg
                    defmacro defconst deflabel deftheory defstobj defabsstobj)))

(defun structure-logic-name-p (name wrld)
  (and (symbolp name)
       (or (and (not (eq (getpropc name 'formals t wrld) t))
                (not (eq (getpropc name 'symbol-class nil wrld) :program)))
           (getpropc name 'theorem nil wrld))))

(defun structure-reserved-name-p (name wrld)
  (and (symbolp name)
       (or (getpropc name 'macro-body nil wrld)
           (getpropc name 'const nil wrld)
           (getpropc name 'label nil wrld)
           (getpropc name 'theory nil wrld)
           (getpropc name 'stobj nil wrld)
           (getpropc name 'stobj-live-var nil wrld))))

(defun structure-no-statement-due-p (name record wrld)
  (or (structure-program-or-file-p name record wrld)
      (and (not (structure-event-kind-with-statements-p
                 (structure-event-kind record)))
           (not (structure-logic-name-p name wrld))
           (not (structure-reserved-name-p name wrld)))))

; These four kinds take only one name.  A signature of a nonempty
; encapsulate is a list of functions, even when it has one member.

(defun structure-namex-shapep (record)
  (let ((kind (structure-event-kind record))
        (namex (structure-event-namex record)))
    (cond ((member-eq kind '(defpkg include-book)) (stringp namex))
          ((member-eq kind '(defun defthm defaxiom defchoose
                             defmacro defconst deflabel deftheory))
           (symbolp namex))
          ((member-eq kind '(defuns defstobj defabsstobj)) (symbol-listp namex))
          ((eq kind 'encapsulate)
           (or (eql namex 0) (symbol-listp namex)))
          (t t))))

; The exporter uses the same tuple fields as ACL2.  NIL is both the name
; of its constant and an empty name list, which the event kind resolves.

(defthm structure-event-number-agrees
  (equal (bx-ev-number record) (structure-event-number record)))

(defthm structure-event-kind-agrees
  (equal (bx-ev-type record) (structure-event-kind record)))

(defthm structure-event-class-agrees
  (equal (bx-ev-symbol-class record) (structure-event-class record)))

(defthm structure-signature-names-agree
  (equal (bx-signature-fns signatures) (structure-signature-names signatures)))

(defthm structure-event-namex-agrees
  (equal (bx-ev-namex record) (structure-event-namex record)))

(defthm structure-single-event-name
  (implies (and (structure-namex-shapep record)
                (member-eq (structure-event-kind record) '(defpkg defthm defaxiom defchoose))
                (member-equal name (structure-event-names record)))
           (equal (car (bx-names (structure-event-namex record))) name))
  :hints (("Goal" :in-theory (disable structure-event-namex structure-event-kind))))

; The lower-end early stop of the world's traversal cannot omit a
; landmark in the interval when the numbers decrease.

(defun structure-range-events (wrld lo hi acc)
  (if (endp wrld)
      acc
    (let* ((entry (car wrld))
           (record (cddr entry))
           (number (structure-event-number record)))
      (structure-range-events
       (cdr wrld) lo hi
       (if (and (structure-event-landmarkp entry)
                (integerp number) (< lo number) (<= number hi))
           (cons record acc)
         acc)))))

(defthm structure-range-events-below-lo
  (implies (and (structure-decreasing-landmarks-p wrld upper)
                (integerp upper)
                (<= upper lo))
           (equal (structure-range-events wrld lo hi acc) acc))
  :hints (("Goal" :induct (structure-decreasing-landmarks-p wrld upper)
                  :in-theory (disable structure-event-number))))

(defthm structure-events-implementation
  (implies (structure-decreasing-landmarks-p wrld upper)
           (equal (bx-events wrld lo hi acc)
                  (structure-range-events wrld lo hi acc)))
  :hints (("Goal" :induct (bx-events wrld lo hi acc)
                  :in-theory (disable structure-event-number bx-ev-number)))
  :rule-classes nil)

(defthm structure-member-in-range-events
  (iff (member-equal record (structure-range-events wrld lo hi acc))
       (or (member-equal record acc)
           (structure-event-in-rangep record lo hi wrld)))
  :hints (("Goal" :induct (structure-range-events wrld lo hi acc)
                  :in-theory (disable structure-event-number))))
