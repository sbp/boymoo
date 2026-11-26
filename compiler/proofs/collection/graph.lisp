(in-package "BOYMOO-PROOFS")

(include-book "closure")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-movable-reference (word base objects)
  (let* ((tag (proof-word-tag word))
         (address (proof-pointer-address word base))
         (object (assoc-equal address objects)))
    (and object
         (member-eq (proof-object-zone object) '(:active :external))
         (case (proof-object-kind object)
           (:cons (equal tag 0))
           (:header (equal tag 2)))
         address)))

(defun collection-reference-fields (count address base objects machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (let* ((reference (collection-movable-reference (proof-load-word address machine)
                                                    base objects))
           (remaining (collection-reference-fields (1- count) (+ address 8)
                                                   base objects machine)))
      (if reference (cons reference remaining) remaining))))

(defun collection-published-object-graph (pending base objects machine)
  (if (endp pending)
      nil
    (let* ((object (car pending))
           (zone (proof-object-zone object))
           (kind (proof-object-kind object))
           (address (proof-object-address object))
           (rest (collection-published-object-graph (cdr pending) base objects machine)))
      (case zone
        (:external (cons (list address :external 0) rest))
        (:active
         (if (eq kind :cons)
             (cons (list* address :cons 16
                          (collection-reference-fields 2 address base objects machine))
                   rest)
           (let* ((header (proof-load-word address machine))
                  (type (proof-header-type header))
                  (words (ash (+ 7 (proof-header-size header)) -3))
                  (fields (if (member-equal type '(1 3))
                              nil
                            (collection-reference-fields words (+ 8 address)
                                                         base objects machine))))
             (cons (list* address :header (proof-object-size object machine) fields)
                   rest))))
        (otherwise rest)))))

(defun collection-published-roots (world objects)
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (bottom (proof-stack-base world))
         (count (ash (- (proof-stack-top world) bottom) -3))
         (slots (collection-reference-fields count bottom base objects machine))
         (dynamic (collection-movable-reference (proof-dynamic-root base machine)
                                                base objects)))
    (if dynamic (cons dynamic slots) slots)))

(defthm collection-extracted-graph-record-is-scannable
  (let ((record (assoc-equal address
                            (collection-published-object-graph pending base objects machine))))
    (implies record (collection-graph-record-p record)))
  :hints (("Goal" :induct (collection-published-object-graph pending base objects machine)
                  :in-theory (disable proof-load-word proof-header-type proof-header-size
                                      collection-reference-fields))))

(defthm collection-extracted-reference-has-published-object
  (implies (member-equal reference
                         (collection-reference-fields count address base objects machine))
           (assoc-equal reference objects))
  :hints (("Goal" :induct (collection-reference-fields count address base objects machine)
                  :in-theory (disable proof-load-word proof-pointer-address proof-word-tag
                                      assoc-equal))))
