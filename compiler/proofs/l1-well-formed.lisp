(in-package "BOYMOO-COMPILER")

(include-book "l1")

(logic)
(set-verify-guards-eagerness 0)

(defun l1-arity (op name definitions)
  (if (eq op :prim)
      (cadr (or (assoc-equal name *primitives*) (assoc-equal name *jets*)))
    (let ((definition (assoc-equal name definitions)))
      (and definition (len (cadr definition))))))

; Scope holds variable numbers available at the term. Used also holds
; numbers bound in parts of the definition that cannot be named here.
(defund l1-check (kind input scope definitions used)
  (declare (xargs :measure (acl2-count input)))
  (cond
   ((eq kind :terms)
    (if (consp input)
        (mv-let (ok used)
          (l1-check :term (car input) scope definitions used)
          (if ok (l1-check :terms (cdr input) scope definitions used) (mv nil used)))
      (mv (null input) used)))
   ((not (true-listp input)) (mv nil used))
   (t
    (case (car input)
      (:var (mv (and (equal (len input) 2) (member-equal (cadr input) scope)) used))
      (:const (mv (and (equal (len input) 2) (unsigned-byte-p 64 (cadr input))) used))
      (:if (if (equal (len input) 4)
               (l1-check :terms (cdr input) scope definitions used)
             (mv nil used)))
      (:let (let ((variables (cadr input))
                  (terms (caddr input)))
              (if (and (equal (len input) 4) (nat-listp variables)
                       (equal (len variables) (len terms)))
                  (mv-let (ok used)
                    (l1-check :terms terms scope definitions used)
                    (let ((used (append variables used)))
                      (if (and ok (no-duplicatesp-equal used))
                          (l1-check :term (cadddr input) (append variables scope)
                                       definitions used)
                        (mv nil used))))
                (mv nil used))))
      ((:call :prim :undef)
       (let ((name (cadr input))
             (terms (caddr input)))
         (if (and (equal (len input) 3)
                  (if (eq (car input) :undef)
                      (unsigned-byte-p 64 name)
                    (and (stringp name)
                         (equal (len terms) (l1-arity (car input) name definitions)))))
             (l1-check :terms terms scope definitions used)
           (mv nil used))))
      (otherwise (mv nil used))))))

(defun l1-formals-p (formals first)
  (if (consp formals)
      (and (equal (car formals) first) (l1-formals-p (cdr formals) (1+ first)))
    (null formals)))

(defun l1-definition-p (definition definitions)
  (let ((formals (cadr definition)))
    (and (true-listp definition) (equal (len definition) 3)
         (stringp (car definition)) (l1-formals-p formals 0)
         (mv-let (ok used)
           (l1-check :term (caddr definition) formals definitions formals)
           (declare (ignore used))
           ok))))

(defun l1-definitions-p (remaining definitions seen)
  (if (consp remaining)
      (let ((definition (car remaining)))
        (and (not (member-equal (car definition) seen))
             (l1-definition-p definition definitions)
             (l1-definitions-p (cdr remaining) definitions (cons (car definition) seen))))
    (null remaining)))

(defun l1-program-p (definitions)
  (l1-definitions-p definitions definitions nil))

(assert-event
 (l1-program-p '(("ACL2::MAIN" (0)
                     (:let (1) ((:var 0))
                       (:prim "ACL2::BINARY-+" ((:var 0) (:var 1))))))))

(assert-event
 (not (l1-program-p '(("ACL2::MAIN" (0)
                          (:let (0) ((:var 0)) (:var 0)))))))

(assert-event
 (not (l1-program-p '(("ACL2::MAIN" (0)
                          (:let (1) ((:var 1)) (:var 1)))))))
