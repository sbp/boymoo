(in-package "BOYMOO-PROOFS")

(include-book "range-checks")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable ash mod floor assembly-high assembly-low assembly-power-of-two
                           boymoo-compiler::low-bits)))

(local
 (defthm assembly-list-fields-of-reverse-onto
   (implies (and (assembly-fixed-item-list-p items) (assembly-fixed-item-list-p code))
            (assembly-fixed-item-list-p (boymoo-compiler::reverse-onto items code)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto items code)
                   :in-theory (disable assembly-fixed-item-p)))))

(defthm assembly-fixed-fields-of-gen-emit
  (implies (and (assembly-fixed-item-list-p items) (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-emit items code))))

(local
 (defthm assembly-low-bits-fits-generated-field
   (implies (and (natp width) (integerp value))
            (unsigned-byte-p width (boymoo-compiler::low-bits value width)))
   :hints (("Goal" :use (assembly-low-bounds)))))

(local
 (defthm assembly-low-field-with-integer-tag-fits-halfword
   (implies (integerp value)
            (unsigned-byte-p 16 (+ 1 (* 2 (boymoo-compiler::low-bits value 15)))))
   :hints (("Goal" :use ((:instance assembly-low-bounds (width 15)))))))

(local
 (defmacro assembly-prove-load-high-fields (name shift)
   `(defthm ,name
      (implies (and (unsigned-byte-p 5 rd) (integerp n) (assembly-fixed-item-list-p code))
               (assembly-fixed-item-list-p (boymoo-compiler::gen-load-high rd n ,shift code)))
      :hints (("Goal" :expand ((boymoo-compiler::gen-load-high rd n ,shift code))
                      :in-theory (disable (:definition boymoo-compiler::gen-load-high)))))))

(local (assembly-prove-load-high-fields assembly-load-high-fields-at-64 64))
(local (assembly-prove-load-high-fields assembly-load-high-fields-at-48 48))
(local (assembly-prove-load-high-fields assembly-load-high-fields-at-32 32))
(local (assembly-prove-load-high-fields assembly-load-high-fields-at-16 16))
(local (assembly-prove-load-high-fields assembly-load-high-fields-at-0 0))

(defthm assembly-fixed-fields-of-gen-load-high
  (implies (and (unsigned-byte-p 5 rd) (integerp n)
                (member-equal shift '(0 16 32 48 64))
                (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-load-high rd n shift code)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-load-high))))

(defthm assembly-fixed-fields-of-gen-load-word
  (implies (and (unsigned-byte-p 5 rd) (integerp n) (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-load-word rd n code)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-load-high))))

(defthm assembly-fixed-fields-of-gen-load-datum
  (implies (and (unsigned-byte-p 5 rd)
                (integerp (if (consp datum) (cdr datum) datum))
                (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-load-datum rd datum code)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-load-high boymoo-compiler::gen-load-word))))

(defthm assembly-fixed-fields-of-gen-address
  (implies (and (unsigned-byte-p 5 rd) (unsigned-byte-p 5 rn)
                (natp bytes) (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-address rd rn bytes subtract code)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-load-word))))

(local
 (defthm assembly-eighth-of-eight-times
   (equal (* 1/8 (* 8 value)) (fix value))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-* (acl2::x 1/8) (acl2::y 8) (acl2::z value)))
            :in-theory (disable acl2::associativity-of-*)))))

(defthm assembly-fixed-fields-of-gen-frame-word
  (implies (and (unsigned-byte-p 5 rd) (natp slot) (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-frame-word rd slot code)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-load-word))))

(defthm assembly-fixed-fields-of-gen-argument-registers
  (implies (and (natp slot) (natp reg) (<= (+ reg (nfix remaining)) 32)
                (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p
            (boymoo-compiler::gen-argument-registers remaining slot reg code)))
  :hints (("Goal" :induct (boymoo-compiler::gen-argument-registers remaining slot reg code)
                  :in-theory (disable boymoo-compiler::gen-frame-word))))

(defthm assembly-fixed-fields-of-gen-copy-arguments
  (implies (and (natp offset) (integerp (* 1/8 offset)) (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-copy-arguments remaining offset code)))
  :hints (("Goal" :induct (boymoo-compiler::gen-copy-arguments remaining offset code)
                  :in-theory (disable boymoo-compiler::gen-load-word))))

(defthm assembly-fixed-fields-of-gen-defined-call
  (implies (and (natp arity) (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-defined-call name arity tail code)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-copy-arguments boymoo-compiler::gen-address))))

(defthm assembly-fixed-fields-of-gen-prologue
  (implies (and (natp arity) (natp high) (natp serial) (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-prologue arity high serial code)))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-address))))

(defthm assembly-fixed-fields-of-gen-stack-helpers
  (implies (assembly-fixed-item-list-p code)
           (and (assembly-fixed-item-list-p (boymoo-compiler::gen-push code))
                (assembly-fixed-item-list-p (boymoo-compiler::gen-finish tail code))
                (implies (natp count)
                         (assembly-fixed-item-list-p (boymoo-compiler::gen-drop count code)))))
  :hints (("Goal" :in-theory (disable boymoo-compiler::gen-address))))

(defthm assembly-fixed-fields-of-gen-routine
  (implies (and (natp serial) (assembly-fixed-item-list-p code))
           (assembly-fixed-item-list-p
            (mv-nth 0 (boymoo-compiler::gen-routine name label serial code)))))

(defthm assembly-fixed-fields-of-gen-simple
  (let ((datum (boymoo-compiler::gen-datum (cadr term) constants)))
    (implies (and (unsigned-byte-p 5 rd) (assembly-fixed-item-list-p code)
                  (if (atom term)
                      (natp (boymoo-compiler::gen-slot term scope))
                    (and (stringp (cadr term)) (not (cddr term))
                         (integerp (if (consp datum) (cdr datum) datum)))))
             (assembly-fixed-item-list-p
              (boymoo-compiler::gen-simple term rd scope constants code))))
  :hints (("Goal"
           :in-theory (disable boymoo-compiler::gen-frame-word boymoo-compiler::gen-load-datum
                               boymoo-compiler::gen-slot boymoo-compiler::gen-datum))))

(defun assembly-generated-bodies-p (defs context serial)
  (if (atom defs)
      (null defs)
    (let* ((definition (car defs))
           (formals (boymoo-compiler::declaration-list (cadr definition)))
           (arity (length formals))
           (scope (boymoo-compiler::bind-formals formals 0 nil)))
      (mv-let (code high next)
        (boymoo-compiler::gen-term (caddr definition) scope arity t context nil arity (+ serial 2))
        (and (stringp (car definition))
             (natp high) (natp next)
             (assembly-fixed-item-list-p code)
             (assembly-generated-bodies-p (cdr defs) context next))))))

(local (in-theory (disable boymoo-compiler::gen-term
                           boymoo-compiler::bind-formals boymoo-compiler::declaration-list
                           boymoo-compiler::gen-prologue)))

(defthm assembly-fixed-fields-of-gen-functions
  (implies (and (natp serial) (assembly-fixed-item-list-p code)
                (assembly-generated-bodies-p defs context serial))
           (assembly-fixed-item-list-p (boymoo-compiler::gen-functions defs entry context serial code)))
  :hints (("Goal" :induct (boymoo-compiler::gen-functions defs entry context serial code))))

(defthm assembly-compiled-items-fixed-fields
  (implies (and (assembly-fixed-item-list-p system)
                (assembly-generated-bodies-p defs context 0)
                (proof-image-p data))
           (assembly-fixed-item-list-p (boymoo-compiler::compile-items entry defs context data system)))
  :hints (("Goal"
           :use (assembly-fixed-fields-of-system-and-runtime)
           :in-theory (disable boymoo-compiler::gen-functions boymoo-compiler::gen-emit
                               boymoo-compiler::runtime-code boymoo-compiler::system-code
                               boymoo-compiler::linux-system-code
                               (:executable-counterpart boymoo-compiler::runtime-code)
                               (:executable-counterpart boymoo-compiler::system-code)
                               (:executable-counterpart boymoo-compiler::linux-system-code)))))
