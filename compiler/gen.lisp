(in-package "BOYMOO-COMPILER")

(include-book "data")

(set-verify-guards-eagerness 0)

; Code is consed in reverse order. X19 is the address below the first
; argument of the frame. Only the value stack holds its live data.

(defun gen-emit (items code)
  (reverse-onto items code))

(defun gen-load-high (rd n shift code)
  (declare (xargs :measure (nfix (- 64 shift))))
  (if (or (not (natp shift)) (<= 64 shift) (equal n 0))
      code
    (let ((half (low-bits n 16)))
      (gen-load-high rd (ash n -16) (+ shift 16)
                     (if (equal half 0) code
                       (cons (list :movk rd half shift) code))))))

(defun gen-load-word (rd n code)
  (gen-load-high rd (ash n -16) 16 (cons (list :movz rd (low-bits n 16) 0) code)))

(defun gen-load-datum (rd datum code)
  (if (consp datum)
      (let ((n (cdr datum)))
        (gen-load-high rd (ash n -15) 16
                       (cons (list :movz rd (+ 1 (* 2 (low-bits n 15))) 0) code)))
    (gen-load-word rd datum code)))

(defun gen-address (rd rn bytes subtract code)
  (if (< bytes 4096)
      (if (and (equal bytes 0) (equal rd rn)) code
        (cons (list (if subtract :sub :add) rd rn bytes) code))
    (cons (list (if subtract :sub-reg :add-reg) rd rn 17 0)
          (gen-load-word 17 bytes code))))

(defun gen-frame-word (rd slot code)
  (let ((bytes (* 8 slot)))
    (if (< bytes 32768)
        (cons (list :ldr rd 19 bytes) code)
      (cons (list :ldr-reg rd 19 17) (gen-load-word 17 bytes code)))))

(defun gen-push (code)
  (gen-emit '((:str 0 25 0) (:add 25 25 8)) code))

(defun gen-drop (count code)
  (gen-address 25 25 (* 8 count) t code))

(defun gen-finish (tail code)
  (if tail
      (gen-emit '((:mov 25 19) (:ldp-post 19 30 31 16) (:ret)) code)
    code))

(defun gen-slot (name scope)
  (or (table-tree-get name scope)
      (compiler-error "Variable outside its scope: ~x0." name)))

(defun gen-datum (text constants)
  (or (index-get text constants)
      (compiler-error "No static datum for: ~x0." text)))

(defun gen-simple-p (term)
  (or (atom term) (equal (car term) *quote-name*)))

(defun gen-simple (term rd scope constants code)
  (if (atom term)
      (gen-frame-word rd (gen-slot term scope) code)
    (if (and (stringp (cadr term)) (not (cddr term)))
        (gen-load-datum rd (gen-datum (cadr term) constants) code)
      (compiler-error "Invalid quoted constant: ~x0." term))))

(defun gen-simple-args-p (terms)
  (or (atom terms)
      (and (gen-simple-p (car terms)) (gen-simple-args-p (cdr terms)))))

(defun gen-simple-args (terms reg scope constants code)
  (if (atom terms)
      code
    (gen-simple-args (cdr terms) (+ reg 1) scope constants
                     (gen-simple (car terms) reg scope constants code))))

(defun gen-argument-registers (remaining slot reg code)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      code
    (gen-argument-registers (- remaining 1) (+ slot 1) (+ reg 1)
                            (gen-frame-word reg slot code))))

(defun gen-copy-arguments (remaining offset code)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      code
    (gen-copy-arguments (- remaining 1) (+ offset 8)
                        (if (< offset 32768)
                            (gen-emit (list (list :ldr 9 10 offset)
                                            (list :str 9 19 offset)) code)
                          (gen-emit '((:ldr-reg 9 10 17) (:str-reg 9 19 17))
                                    (gen-load-word 17 offset code))))))

(defun gen-defined-call (name arity tail code)
  (if tail
      (let* ((code (if (zp arity) code
                     (gen-copy-arguments arity 0
                                         (gen-address 10 25 (* 8 arity) t code))))
             (code (gen-address 25 19 (* 8 arity) nil code)))
        (gen-emit (list '(:ldp-post 19 30 31 16) (list :b (list :fn name))) code))
    (cons (list :bl (list :fn name)) code)))

(defun gen-local (serial)
  (list :local serial))

(defun gen-boolean (condition code)
  (gen-emit (list '(:movz 9 58 0) '(:movz 10 34 0)
                  (list :csel 0 9 10 condition)) code))

(defun gen-car-cdr (cdr-p serial code)
  (let ((done (gen-local serial)))
    (gen-emit (list '(:movz 9 34 0) '(:tst-mask 0 3)
                    (list :b-cond :ne done)
                    (if cdr-p '(:add 0 0 8) '(:add 0 0 0))
                    '(:ldr-reg 9 28 0) (list :label done) '(:mov 0 9))
              code)))

(defun gen-equal (serial code)
  (let ((yes (gen-local serial))
        (no (gen-local (+ serial 1)))
        (done (gen-local (+ serial 2))))
    (gen-emit
     (list '(:cmp-reg 0 1) (list :b-cond :eq yes)
           '(:orr-reg 9 0 1) '(:tst-mask 9 1) (list :b-cond :ne no)
           '(:and-mask 9 0 3) '(:cmp 9 4) (list :b-cond :eq no)
           '(:and-mask 9 1 3) '(:cmp 9 4) (list :b-cond :eq no)
           '(:bl "prim:COMMON-LISP::EQUAL") (list :b done)
           (list :label yes) '(:movz 0 58 0) (list :b done)
           (list :label no) '(:movz 0 34 0) (list :label done))
     code)))

(defun gen-arithmetic (name label serial code)
  (let* ((slow (gen-local serial))
         (done (gen-local (+ serial 1)))
         (unary (equal name "ACL2::UNARY--"))
         (code (if unary code (cons '(:and-reg 9 0 1) code)))
         (code (gen-emit (list (list :tst-mask (if unary 0 9) 1)
                               (list :b-cond :eq slow)) code))
         (code (cond (unary
                      (gen-emit (list '(:movz 9 2 0) '(:subs-reg 9 9 0 0)
                                      (list :b-cond :vs slow) '(:mov 0 9)) code))
                     ((equal name "ACL2::BINARY-+")
                      (gen-emit (list '(:sub 9 1 1) '(:adds-reg 9 0 9 0)
                                      (list :b-cond :vs slow) '(:mov 0 9)) code))
                     (t (gen-boolean :lt (cons '(:cmp-reg 0 1) code))))))
    (gen-emit (list (list :b done) (list :label slow) (list :bl label) (list :label done))
              code)))

(defun gen-routine (name label serial code)
  (cond ((equal name "COMMON-LISP::CAR")
         (mv (gen-car-cdr nil serial code) (+ serial 1)))
        ((equal name "COMMON-LISP::CDR")
         (mv (gen-car-cdr t serial code) (+ serial 1)))
        ((equal name "COMMON-LISP::CONSP")
         (mv (gen-boolean :eq (cons '(:tst-mask 0 3) code)) serial))
        ((equal name "COMMON-LISP::EQUAL")
         (mv (gen-equal serial code) (+ serial 3)))
        ((or (equal name "ACL2::BINARY-+") (equal name "ACL2::UNARY--")
             (equal name "COMMON-LISP::<"))
         (mv (gen-arithmetic name label serial code) (+ serial 2)))
        (t (mv (cons (list :bl label) code) serial))))

(defun gen-mbe-p (head args)
  (and (equal head "ACL2::RETURN-LAST")
       (equal (caar args) *quote-name*)
       (equal (cadar args) "ACL2::MBE1-RAW")))

(defun gen-max (a b)
  (if (< a b) b a))

(defun gen-call-info (head context)
  (let* ((target (or (index-get head (cadr context)) head))
         (routine (or (assoc-equal target *jets*) (assoc-equal target *primitives*))))
    (mv target (if routine (cadr routine) (index-get target (car context)))
        (cddr routine))))

; A term leaves its value in X0, or finishes the frame in tail position.
; DEPTH is the occupied part of the frame. HIGH bounds all pushes.
; CONTEXT holds the arities, resolved attachments, and static data map.
(mutual-recursion
 (defun gen-term (term scope depth tail context code high serial)
   (declare (xargs :measure (* 2 (acl2-count term))))
   (if (gen-simple-p term)
       (mv (gen-finish tail (gen-simple term 0 scope (caddr context) code)) high serial)
     (let ((head (car term))
           (args (cdr term)))
       (cond
        ((and (equal head *if-name*) (not (equal (length args) 3)))
         (mv (compiler-error "A conditional needs three arguments: ~x0." term) high serial))
        ((equal head *if-name*)
         (mv-let (code high serial)
           (gen-term (car args) scope depth nil context code high serial)
           (let* ((yes (gen-local serial))
                  (no (gen-local (+ serial 1)))
                  (done (gen-local (+ serial 2)))
                  (code (gen-emit (list '(:cmp 0 34) (list :b-cond :ne yes)
                                        (list :b no) (list :label yes)) code)))
             (mv-let (code high serial)
               (gen-term (cadr args) scope depth tail context code high (+ serial 3))
               (let ((code (if tail code (cons (list :b done) code))))
                 (mv-let (code high serial)
                   (gen-term (caddr args) scope depth tail context
                             (cons (list :label no) code) high serial)
                   (mv (if tail code (cons (list :label done) code)) high serial)))))))
        ((and (gen-mbe-p head args) (equal (length args) 3))
         (mv-let (ignored-code ignored-high ignored-serial)
           (gen-term (cadr args) scope depth nil context nil depth serial)
           (declare (ignore ignored-code ignored-high ignored-serial))
           (gen-term (caddr args) scope depth tail context code high serial)))
        ((and (consp head)
              (or (not (equal (car head) "COMMON-LISP::LAMBDA"))
                  (not (consp (cddr head))) (cdddr head)
                  (and (atom (cadr head)) (not (equal (cadr head) *nil-name*)))))
         (mv (compiler-error "Invalid lambda: ~x0." head) high serial))
        ((consp head)
         (let ((formals (declaration-list (cadr head))))
           (mv-let (code high serial body-scope top)
             (gen-lambda-args args formals scope nil depth context code high serial)
             (mv-let (code high serial)
               (gen-term (caddr head) body-scope top tail context code high serial)
               (mv (if tail code (gen-drop (- top depth) code)) high serial)))))
        (t
         (mv-let (target expected routine)
           (gen-call-info head context)
           (let ((arity (length args)))
             (cond
              ((and expected (not (equal arity expected)))
               (mv (compiler-error "Call with the wrong number of arguments: ~x0." head)
                   high serial))
              ((and routine (gen-simple-args-p args))
               (mv-let (code serial)
                 (gen-routine target routine serial
                              (gen-simple-args args 0 scope (caddr context) code))
                 (mv (gen-finish tail code) high serial)))
              (t
               (mv-let (code high serial)
                 (gen-args args scope depth context code high serial)
                 (cond (routine
                        (mv-let (code serial)
                          (gen-routine target routine serial
                                       (gen-argument-registers arity depth 0 code))
                          (mv (if tail (gen-finish t code) (gen-drop arity code))
                              high serial)))
                       (expected (mv (gen-defined-call target arity tail code) high serial))
                       (t (mv (cons '(:bl "rt:undefined")
                                    (gen-load-datum 0 (gen-datum target (caddr context)) code))
                              high serial)))))))))))))
 (defun gen-args (args scope depth context code high serial)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (atom args)
       (mv code high serial)
     (mv-let (code high serial)
       (gen-term (car args) scope depth nil context code high serial)
       (gen-args (cdr args) scope (+ depth 1) context (gen-push code)
                 (gen-max high (+ depth 1)) serial))))
 (defun gen-lambda-args (args formals scope body-scope depth context code high serial)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (cond ((atom args)
          (if (consp formals)
              (mv (compiler-error "Missing lambda arguments: ~x0." formals)
                  high serial body-scope depth)
            (mv code high serial body-scope depth)))
         ((atom formals)
          (mv (compiler-error "Extra lambda arguments: ~x0." args) high serial body-scope depth))
         ((atom (car args))
          (gen-lambda-args (cdr args) (cdr formals) scope
                           (bind-formal (car formals) (gen-slot (car args) scope) body-scope)
                           depth context code high serial))
         (t
          (mv-let (code high serial)
            (gen-term (car args) scope depth nil context code high serial)
            (gen-lambda-args (cdr args) (cdr formals) scope
                             (bind-formal (car formals) depth body-scope)
                             (+ depth 1) context (gen-push code)
                             (gen-max high (+ depth 1)) serial))))))

(defun gen-prologue (arity high serial code)
  (let* ((stack-ok (gen-local serial))
         (frame-ok (gen-local (+ serial 1)))
         (code (gen-emit (list '(:sub 9 31 16) '(:cmp-reg 9 23)
                               (list :b-cond :hs stack-ok) '(:bl "rt:deep")
                               (list :label stack-ok) '(:stp-pre 19 30 31 -16)) code))
         (code (if (< arity high)
                   (gen-emit (list '(:cmp-reg 0 24) (list :b-cond :ls frame-ok)
                                   '(:bl "rt:grow") (list :label frame-ok))
                             (gen-address 0 25 (* 8 (- high arity)) nil code))
                 code)))
    (gen-address 19 25 (* 8 arity) t code)))

(defun gen-functions (defs entry context serial code)
  (if (atom defs)
      code
    (let* ((def (car defs))
           (name (car def))
           (formals (declaration-list (cadr def)))
           (arity (length formals))
           (scope (bind-formals formals 0 nil)))
      (mv-let (body high next)
        (gen-term (caddr def) scope arity t context nil arity (+ serial 2))
        (let* ((code (if (equal name entry) (cons '(:label "rt:entry") code) code))
               (code (cons (list :label (list :fn name)) code))
               (code (gen-prologue arity high serial code)))
          (gen-functions (cdr defs) entry context next (reverse-onto (reverse-onto body nil) code)))))))
