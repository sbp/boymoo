(in-package "BOYMOO-COMPILER")

(include-book "../emit")
(include-book "../../compiler/model/a64")
(include-book "mir-semantics")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthmd p9-move-between-registers
  (implies (and (natp rd) (< rd 31) (natp rs) (< rs 31))
           (equal (emit-inst (list :mov (cons :x rd) (cons :x rs)) ctx where code)
                  (if (equal rd rs) code (cons (list :mov rd rs) code)))))

(defthmd p9-move-from-register-to-spill-slot
  (implies (and (natp slot) (natp rs) (< rs 31))
           (equal (emit-inst (list :mov (cons :m slot) (cons :x rs)) ctx where code)
                  (cons (list :str rs 31 (emit-slot-offset slot)) code))))

(defthmd p9-move-from-spill-slot-to-register
  (implies (and (natp slot) (natp rd) (< rd 31))
           (equal (emit-inst (list :mov (cons :x rd) (cons :m slot)) ctx where code)
                  (cons (list :ldr rd 31 (emit-slot-offset slot)) code))))

(defthmd p9-move-x1-to-x0-decodes
  (equal (boymoo-model::a64-decode
          (a64-word (car (emit-inst '(:mov (:x . 0) (:x . 1)) ctx where code)) pc labels))
         '(:logical-reg 1 64 0 31 1 0 0 nil))
  :hints (("Goal" :in-theory (enable p9-move-between-registers))))

(local
 (defthm p9-a64-word-idempotent
   (equal (boymoo-model::a64-unsigned 64 (boymoo-model::a64-unsigned 64 x))
          (boymoo-model::a64-unsigned 64 x))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-unsigned boymoo-model::a64-ones)
                                  (acl2::binary-logand))))))

(defthmd p9-move-x1-to-x0-executes
  (let* ((code (emit-inst '(:mov (:x . 0) (:x . 1)) ctx where code))
         (word (a64-word (car code) pc labels))
         (after (boymoo-model::a64-execute (boymoo-model::a64-decode word) machine)))
    (and (equal (boymoo-model::a64-read-reg 0 64 nil after)
                (boymoo-model::a64-read-reg 1 64 nil machine))
         (equal (boymoo-model::a64-memory after) (boymoo-model::a64-memory machine))
         (equal (boymoo-model::a64-nzcv after) (boymoo-model::a64-nzcv machine))
         (equal (boymoo-model::a64-sp after) (boymoo-model::a64-sp machine))))
  :hints (("Goal" :use p9-move-x1-to-x0-decodes
           :in-theory (disable emit-inst a64-word boymoo-model::a64-decode boymoo-model::a64-unsigned
                               nth update-nth))))

(assert-event
 (let* ((inst '(:mov (:x . 0) (:x . 1)))
        (code (emit-inst inst nil nil nil))
        (machine (boymoo-model::a64-state '((0 . 17) (1 . 18446744073709551612)) 0 0 0 nil))
        (after (boymoo-model::a64-execute
                (boymoo-model::a64-decode (a64-word (car code) 0 nil)) machine)))
   (equal (boymoo-model::core-value (boymoo-model::a64-read-reg 0 64 nil after))
          (mir-pure-result inst '(18446744073709551612)))))

(assert-event
 (let* ((inst '(:li (:x . 3) -65538))
        (code (reverse (emit-inst inst nil nil nil)))
        (machine (boymoo-model::a64-state nil 0 0 0 nil))
        (after (boymoo-model::a64-execute
                (boymoo-model::a64-decode (a64-word (cadr code) 4 nil))
                (boymoo-model::a64-execute
                 (boymoo-model::a64-decode (a64-word (car code) 0 nil)) machine))))
   (equal (boymoo-model::core-value (boymoo-model::a64-read-reg 3 64 nil after))
          (mir-pure-result inst nil))))
