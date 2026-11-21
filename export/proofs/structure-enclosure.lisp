(in-package "ACL2")

(include-book "structure-events")

; An event is enclosed by the succeeding landmarks at strictly smaller
; depths.  On passing a smaller depth, only a smaller one still can enclose
; that landmark.  A signed encapsulate at such a depth supplies its
; constraint's name, if ACL2 has one.  LATER is in chronological order.

(defun structure-event-depth (record)
  (let ((number-field (car (structure-event-tuple record))))
    (if (integerp number-field) 0 (cdr number-field))))

(defun structure-constraint-root (record wrld)
  (let ((signature (structure-event-namex record)))
    (if (and (eq (structure-event-kind record) 'encapsulate)
             (consp signature))
        (mv-let (root formulas origins)
          (constraint-info (car signature) wrld)
          (declare (ignore formulas origins))
          root)
      nil)))

(defun structure-enclosing-landmarks (later limit)
  (if (endp later)
      nil
    (let ((depth (structure-event-depth (car later))))
      (if (or (null limit) (< depth limit))
          (cons (car later)
                (structure-enclosing-landmarks (cdr later) depth))
        (structure-enclosing-landmarks (cdr later) limit)))))

(defun structure-nearest-root (ancestors wrld)
  (if (endp ancestors)
      nil
    (or (structure-constraint-root (car ancestors) wrld)
        (structure-nearest-root (cdr ancestors) wrld))))

(defun structure-pair-range-events (newest later wrld acc)
  (if (endp newest)
      acc
    (let* ((record (car newest))
           (root (structure-nearest-root
                  (structure-enclosing-landmarks later (structure-event-depth record))
                  wrld)))
      (structure-pair-range-events (cdr newest) (cons record later) wrld
                                   (cons (cons record root) acc)))))

; A depth is an integer when ACL2 kept it with an event number.  This
; hypothesis is only needed for comparing limits and taking their minimum.

(defun structure-event-depths-are-integers-p (records)
  (or (endp records)
      (and (integerp (structure-event-depth (car records)))
           (structure-event-depths-are-integers-p (cdr records)))))

(defthm structure-event-depth-agrees
  (equal (bx-ev-depth record) (structure-event-depth record)))

(defthm structure-constraint-root-agrees
  (equal (bx-constrainer record wrld) (structure-constraint-root record wrld))
  :hints (("Goal" :in-theory (disable constraint-info structure-event-kind
                                      structure-event-namex bx-ev-type bx-ev-namex))))

; The exporter's stack is the projection to encapsulates of these
; enclosing landmarks.  Applying a depth limit to a projected stack
; is equivalent to applying it to the landmarks before projection.

(defun structure-enclosure-stack (ancestors wrld)
  (cond ((endp ancestors) nil)
        ((eq (structure-event-kind (car ancestors)) 'encapsulate)
         (cons (cons (structure-event-depth (car ancestors))
                     (structure-constraint-root (car ancestors) wrld))
               (structure-enclosure-stack (cdr ancestors) wrld)))
        (t (structure-enclosure-stack (cdr ancestors) wrld))))

(defthm structure-stack-first-root
  (equal (bx-first-constrainer (structure-enclosure-stack ancestors wrld))
         (structure-nearest-root ancestors wrld))
  :hints (("Goal" :induct (structure-enclosure-stack ancestors wrld)
                  :in-theory (disable structure-event-kind structure-event-namex
                                      constraint-info structure-event-depth))
          ("Subgoal *1/2"
           :expand ((structure-constraint-root (car ancestors) wrld)))))

(defthm structure-stack-pop-respects-limit
  (implies (and (structure-event-depths-are-integers-p later)
                (or (null old-limit) (integerp old-limit))
                (integerp limit))
           (equal
            (bx-pop (structure-enclosure-stack
                     (structure-enclosing-landmarks later old-limit) wrld)
                    limit)
            (structure-enclosure-stack
             (structure-enclosing-landmarks
              later (if (or (null old-limit) (< limit old-limit)) limit old-limit))
             wrld)))
  :hints (("Goal" :induct (structure-enclosing-landmarks later old-limit)
                  :in-theory (disable structure-event-depth structure-event-kind
                                      structure-constraint-root))))

(defthm structure-enclose-implements-pairing
  (implies (and (structure-event-depths-are-integers-p newest)
                (structure-event-depths-are-integers-p later))
           (equal (bx-enclose newest
                              (structure-enclosure-stack
                               (structure-enclosing-landmarks later nil) wrld)
                              acc wrld)
                  (structure-pair-range-events newest later wrld acc)))
  :hints (("Goal" :induct (structure-pair-range-events newest later wrld acc)
                  :in-theory (disable bx-pop bx-first-constrainer bx-constrainer
                                      bx-ev-depth bx-ev-type structure-constraint-root
                                      structure-event-depth structure-event-kind
                                      structure-nearest-root))))

(defthm structure-depths-of-revappend
  (equal (structure-event-depths-are-integers-p (revappend a b))
         (and (structure-event-depths-are-integers-p a)
              (structure-event-depths-are-integers-p b)))
  :hints (("Goal" :induct (revappend a b)
                  :in-theory (disable structure-event-depth))))

(defthm structure-depths-of-reverse
  (equal (structure-event-depths-are-integers-p (reverse a))
         (structure-event-depths-are-integers-p a))
  :hints (("Goal" :in-theory (disable revappend structure-event-depth))))
