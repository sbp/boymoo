(in-package "BOYMOO-PROOFS")

(include-book "bits")
(include-book "registers")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-instruction-at-p proof-instruction-access-p
                    proof-instruction-effect proof-execute proof-linux-svc
                    proof-world-pc proof-world-reg proof-reg
                    boymoo-model::a64-unsigned boymoo-model::a64-execute
                    boymoo-model::a64-condition boymoo-model::a64-signed
                    boymoo-model::a64-load boymoo-model::a64-store
                    boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes
                    generated-load-word generated-sp generated-flags
                    ash logbitp acl2::binary-logand acl2::binary-logior
                    acl2::binary-logxor expt mod))

(in-theory (enable proof-world-machine))

(defthm generated-expand-update-nth-positive
  (implies (posp index)
           (equal (update-nth index value entries)
                  (cons (car entries) (update-nth (1- index) value (cdr entries)))))
  :hints (("Goal" :expand (update-nth index value entries))))

(defund generated-ordinary-machine-p (world)
  (not (eq (boymoo-model::a64-registers (proof-world-machine world)) :svc)))

(defthm generated-ordinary-machine-of-updates
  (and (equal (generated-ordinary-machine-p (generated-set-pc pc world))
              (generated-ordinary-machine-p world))
       (equal (generated-ordinary-machine-p (generated-set-sp sp world))
              (generated-ordinary-machine-p world))
       (equal (generated-ordinary-machine-p (generated-set-flags flags world))
              (generated-ordinary-machine-p world))
       (equal (generated-ordinary-machine-p (generated-store-word address value world))
              (generated-ordinary-machine-p world))
       (implies (and (natp register) (< register 31))
                (generated-ordinary-machine-p (generated-set-reg register datum world))))
  :hints (("Goal" :in-theory (enable generated-ordinary-machine-p generated-set-pc
                                    generated-set-sp generated-set-flags generated-store-word
                                    generated-set-reg generated-set-machine
                                    boymoo-model::a64-store))))

(defthm generated-effect-of-branch
  (implies (generated-ordinary-machine-p world)
           (equal (proof-instruction-effect (list :branch delta link) world)
                  (let* ((pc (proof-world-pc world))
                         (next (generated-set-pc (+ pc delta) world)))
                    (if link (generated-set-reg 30 (+ pc 4) next) next))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc
                                    generated-ordinary-machine-p generated-set-machine
                                    generated-set-pc generated-set-reg))))

(defthm generated-effect-of-conditional-branch
  (implies (generated-ordinary-machine-p world)
           (equal (proof-instruction-effect (list :branch-cond delta condition) world)
                  (generated-set-pc (+ (proof-world-pc world)
                                       (if (boymoo-model::a64-condition
                                            condition (generated-flags world))
                                           delta 4))
                                    world)))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc
                                    generated-ordinary-machine-p generated-set-machine
                                    generated-set-pc generated-flags))))

(defthm generated-effect-of-ret
  (implies (generated-ordinary-machine-p world)
           (equal (proof-instruction-effect '(:branch-reg 30 nil) world)
                  (generated-set-pc (proof-world-reg 30 world) world)))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc proof-world-reg
                                    proof-reg generated-ordinary-machine-p
                                    generated-set-machine generated-set-pc))))

(defthm generated-shift-by-zero
  (equal (boymoo-model::a64-shift 0 64 value 0)
         (boymoo-model::a64-unsigned 64 value))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned))))

(defthm generated-effect-of-mov-register
  (implies (and (natp rd) (< rd 31))
           (equal (proof-instruction-effect (list :logical-reg 1 64 rd 31 rn 0 0 nil) world)
                  (generated-set-reg rd (proof-world-reg rn world)
                                     (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc proof-world-reg
                                    proof-reg generated-set-machine generated-set-pc
                                    generated-set-reg))))

(defthm generated-effect-of-movz
  (implies (and (natp register) (< register 31))
           (equal (proof-instruction-effect (list :move-wide 2 64 register half position) world)
                  (generated-set-reg register (ash half position)
                                     (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc
                                    generated-set-machine generated-set-pc generated-set-reg))))

(defthm generated-effect-of-load-offset
  (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31))
           (equal (proof-instruction-effect (list :single 1 8 rn rd :offset offset) world)
                  (generated-set-reg rd (generated-load-word (+ (proof-world-reg rn world) offset)
                                                             world)
                                     (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc proof-world-reg
                                    proof-reg generated-set-machine generated-set-pc
                                    generated-set-reg generated-load-word proof-load-word
                                    boymoo-model::a64-load))))

(defthm generated-effect-of-store-offset
  (implies (and (generated-ordinary-machine-p world) (natp rn) (< rn 31))
           (equal (proof-instruction-effect (list :single 0 8 rn rt :offset offset) world)
                  (generated-store-word (+ (proof-world-reg rn world) offset)
                                        (proof-world-reg rt world)
                                        (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc proof-world-reg
                                    proof-reg generated-set-machine generated-set-pc
                                    generated-store-word generated-ordinary-machine-p
                                    boymoo-model::a64-store))))

(defthm generated-effect-of-load-indexed
  (implies (and (natp rd) (< rd 31) (natp rn) (< rn 31))
           (equal (proof-instruction-effect (list :single 1 8 rn rd :register rm 3 0) world)
                  (generated-set-reg rd (generated-load-word
                                         (+ (proof-world-reg rn world) (proof-world-reg rm world))
                                         world)
                                     (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc proof-world-reg
                                    proof-reg generated-set-machine generated-set-pc
                                    generated-set-reg generated-load-word proof-load-word
                                    boymoo-model::a64-load))))

(defthm generated-effect-of-store-indexed
  (implies (and (generated-ordinary-machine-p world) (natp rn) (< rn 31))
           (equal (proof-instruction-effect (list :single 0 8 rn rt :register rm 3 0) world)
                  (generated-store-word (+ (proof-world-reg rn world) (proof-world-reg rm world))
                                        (proof-world-reg rt world)
                                        (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc proof-world-reg
                                    proof-reg generated-set-machine generated-set-pc
                                    generated-store-word generated-ordinary-machine-p
                                    boymoo-model::a64-store))))

(defthm generated-effect-of-save-frame
  (implies (generated-ordinary-machine-p world)
           (equal (proof-instruction-effect '(:pair nil 31 19 30 :pre -16) world)
                  (let ((sp (generated-sp world)))
                    (generated-set-sp
                     (- sp 16)
                     (generated-store-word
                      (- sp 8) (proof-world-reg 30 world)
                      (generated-store-word
                       (- sp 16) (proof-world-reg 19 world)
                       (generated-set-pc (+ 4 (proof-world-pc world)) world)))))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc proof-world-reg
                                    proof-reg generated-set-machine generated-set-pc
                                    generated-store-word generated-ordinary-machine-p
                                    generated-set-sp generated-sp boymoo-model::a64-store))))

(defthm generated-effect-of-restore-frame
  (equal (proof-instruction-effect '(:pair t 31 19 30 :post 16) world)
         (let ((sp (generated-sp world)))
           (generated-set-sp
            (+ sp 16)
            (generated-set-reg
             30 (generated-load-word (+ sp 8) world)
             (generated-set-reg
              19 (generated-load-word sp world)
              (generated-set-pc (+ 4 (proof-world-pc world)) world))))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc
                                    generated-set-machine generated-set-pc generated-set-reg
                                    generated-load-word proof-load-word boymoo-model::a64-load
                                    generated-set-sp generated-sp))))
