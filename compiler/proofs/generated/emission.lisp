(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::gen-term boymoo-compiler::gen-args
                    boymoo-compiler::gen-lambda-args boymoo-compiler::gen-simple
                    boymoo-compiler::gen-simple-p boymoo-compiler::gen-call-info
                    boymoo-compiler::gen-prologue boymoo-compiler::gen-defined-call
                    boymoo-compiler::gen-load-high boymoo-compiler::gen-load-word
                    boymoo-compiler::gen-load-datum boymoo-compiler::gen-copy-arguments
                    boymoo-compiler::gen-address boymoo-compiler::gen-finish
                    boymoo-compiler::gen-frame-word boymoo-compiler::gen-push
                    boymoo-compiler::bind-formals boymoo-compiler::declaration-list
                    boymoo-compiler::gen-slot boymoo-compiler::gen-routine
                    boymoo-compiler::low-bits ash length))

(defthm generated-reverse-onto-of-append
  (equal (boymoo-compiler::reverse-onto (append first second) code)
         (boymoo-compiler::reverse-onto
          second (boymoo-compiler::reverse-onto first code)))
  :hints (("Goal" :induct (boymoo-compiler::reverse-onto first code))))

(defthm generated-append-associative
  (equal (append (append first second) third) (append first second third)))

(defthm generated-reverse-onto-of-appended-accumulator
  (equal (boymoo-compiler::reverse-onto items (append code suffix))
         (append (boymoo-compiler::reverse-onto items code) suffix))
  :hints (("Goal" :induct (boymoo-compiler::reverse-onto items code))))

(local
 (defthm generated-reverse-onto-single-item
   (equal (boymoo-compiler::reverse-onto items (list item))
          (append (boymoo-compiler::reverse-onto items nil) (list item)))
   :hints (("Goal" :use (:instance generated-reverse-onto-of-appended-accumulator
                                   (code nil) (suffix (list item)))
                   :in-theory (disable generated-reverse-onto-of-appended-accumulator)))))

(defthm generated-double-reverse-onto
  (equal (boymoo-compiler::reverse-onto (boymoo-compiler::reverse-onto items nil) code)
         (append items code))
  :hints (("Goal" :induct (append items code)
                  :expand (boymoo-compiler::reverse-onto items nil))))

(defthm generated-load-high-of-appended-accumulator
  (equal (boymoo-compiler::gen-load-high register word shift (append code suffix))
         (append (boymoo-compiler::gen-load-high register word shift code) suffix))
  :hints (("Goal" :induct (boymoo-compiler::gen-load-high register word shift code)
                  :in-theory (enable boymoo-compiler::gen-load-high))))

(defthm generated-load-word-of-appended-accumulator
  (equal (boymoo-compiler::gen-load-word register word (append code suffix))
         (append (boymoo-compiler::gen-load-word register word code) suffix))
  :hints (("Goal"
           :use (:instance generated-load-high-of-appended-accumulator
                           (word (ash word -16)) (shift 16)
                           (code (cons (list :movz register
                                             (boymoo-compiler::low-bits word 16) 0)
                                       code)))
           :in-theory (e/d (boymoo-compiler::gen-load-word)
                           (generated-load-high-of-appended-accumulator)))))

(defthm generated-load-word-accumulator
  (equal (boymoo-compiler::gen-load-word register word code)
         (append (boymoo-compiler::gen-load-word register word nil) code))
  :hints (("Goal" :use (:instance generated-load-word-of-appended-accumulator
                                  (code nil) (suffix code))
                  :in-theory (disable generated-load-word-of-appended-accumulator)))
  :rule-classes nil)

(defthm generated-address-accumulator
  (equal (boymoo-compiler::gen-address register base bytes subtract code)
         (append (boymoo-compiler::gen-address register base bytes subtract nil) code))
  :hints (("Goal" :use (:instance generated-load-word-accumulator
                                  (register 17) (word bytes))
                  :in-theory (enable boymoo-compiler::gen-address)))
  :rule-classes nil)

(defthm generated-copy-arguments-of-appended-accumulator
  (equal (boymoo-compiler::gen-copy-arguments count offset (append code suffix))
         (append (boymoo-compiler::gen-copy-arguments count offset code) suffix))
  :hints (("Goal" :induct (boymoo-compiler::gen-copy-arguments count offset code)
                  :in-theory (enable boymoo-compiler::gen-copy-arguments))))

(defthm generated-copy-arguments-accumulator
  (equal (boymoo-compiler::gen-copy-arguments count offset code)
         (append (boymoo-compiler::gen-copy-arguments count offset nil) code))
  :hints (("Goal" :use (:instance generated-copy-arguments-of-appended-accumulator
                                  (code nil) (suffix code))
                  :in-theory (disable generated-copy-arguments-of-appended-accumulator)))
  :rule-classes nil)

(local
 (defthm generated-address-to-append
   (implies (syntaxp (not (equal code ''nil)))
            (equal (boymoo-compiler::gen-address register base bytes subtract code)
                   (append (boymoo-compiler::gen-address register base bytes subtract nil)
                           code)))
   :hints (("Goal" :use generated-address-accumulator))))

(local
 (defthm generated-copy-arguments-to-append
   (implies (syntaxp (not (equal code ''nil)))
            (equal (boymoo-compiler::gen-copy-arguments count offset code)
                   (append (boymoo-compiler::gen-copy-arguments count offset nil) code)))
   :hints (("Goal" :use generated-copy-arguments-accumulator))))

(defun generated-address-items (register base bytes subtract)
  (boymoo-compiler::reverse-onto
   (boymoo-compiler::gen-address register base bytes subtract nil) nil))

(defun generated-prologue-items (arity high serial)
  (let ((stack-ok (boymoo-compiler::gen-local serial))
        (frame-ok (boymoo-compiler::gen-local (1+ serial))))
    (append (list '(:sub 9 31 16) '(:cmp-reg 9 23)
                  (list :b-cond :hs stack-ok) '(:bl "rt:deep")
                  (list :label stack-ok) '(:stp-pre 19 30 31 -16))
            (if (< arity high)
                (append (generated-address-items 0 25 (* 8 (- high arity)) nil)
                        (list '(:cmp-reg 0 24) (list :b-cond :ls frame-ok)
                              '(:bl "rt:grow") (list :label frame-ok)))
              nil)
            (generated-address-items 19 25 (* 8 arity) t))))

(defthmd generated-prologue-emission
  (equal (boymoo-compiler::gen-prologue arity high serial code)
         (boymoo-compiler::reverse-onto (generated-prologue-items arity high serial) code))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-prologue))))

(defun generated-defined-call-items (name arity tail)
  (if tail
      (append (if (zp arity)
                  nil
                (append (generated-address-items 10 25 (* 8 arity) t)
                        (boymoo-compiler::reverse-onto
                         (boymoo-compiler::gen-copy-arguments arity 0 nil) nil)))
              (generated-address-items 25 19 (* 8 arity) nil)
              (list '(:ldp-post 19 30 31 16) (list :b (list :fn name))))
    (list (list :bl (list :fn name)))))

(defthm generated-defined-call-emission
  (equal (boymoo-compiler::gen-defined-call name arity tail code)
         (boymoo-compiler::reverse-onto (generated-defined-call-items name arity tail) code))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-defined-call)))
  :rule-classes nil)

(defthm generated-term-emission-of-mbe
  (implies (and (not (boymoo-compiler::gen-simple-p term))
                (boymoo-compiler::gen-mbe-p (car term) (cdr term))
                (equal (length (cdr term)) 3))
           (equal (boymoo-compiler::gen-term term scope depth tail context code high serial)
                  (boymoo-compiler::gen-term (cadddr term) scope depth tail context
                                             code high serial)))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-mbe-p)
                  :expand (boymoo-compiler::gen-term term scope depth tail context
                                                    code high serial)))
  :rule-classes nil)

(defun generated-functions-items (definitions entry context serial)
  (if (atom definitions)
      nil
    (let* ((definition (car definitions))
           (name (car definition))
           (formals (boymoo-compiler::declaration-list (cadr definition)))
           (arity (length formals))
           (scope (boymoo-compiler::bind-formals formals 0 nil)))
      (mv-let (body high next)
        (boymoo-compiler::gen-term (caddr definition) scope arity t context nil
                                  arity (+ serial 2))
        (append (if (equal name entry) '((:label "rt:entry")) nil)
                (list (list :label (list :fn name)))
                (generated-prologue-items arity high serial)
                (boymoo-compiler::reverse-onto body nil)
                (generated-functions-items (cdr definitions) entry context next))))))

(defthm generated-functions-emission
  (equal (boymoo-compiler::gen-functions definitions entry context serial code)
         (boymoo-compiler::reverse-onto
          (generated-functions-items definitions entry context serial) code))
  :hints (("Goal" :induct (boymoo-compiler::gen-functions definitions entry context serial code)
                  :in-theory (enable generated-prologue-emission)))
  :rule-classes nil)
