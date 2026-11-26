(in-package "BOYMOO-PROOFS")

(include-book "steps")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::a64-unsigned proof-step proof-world-reg
                    proof-world-pc proof-world-machine proof-world-stop
                    proof-instruction-at-p proof-instruction-access-p proof-instruction-effect
                    proof-reg proof-load-word generated-sp generated-flags generated-load-word
                    boymoo-model::a64-execute boymoo-model::a64-store))

(defthm generated-assoc-after-put
  (equal (assoc-equal key (put-assoc-equal target value entries))
         (if (equal key target) (cons target value) (assoc-equal key entries)))
  :hints (("Goal" :induct (put-assoc-equal target value entries))))

(defthm generated-word-register-bounds
  (and (natp (proof-world-reg register world))
       (< (proof-world-reg register world) (expt 2 64)))
  :hints (("Goal" :in-theory (enable proof-world-reg proof-reg)))
  :rule-classes ((:type-prescription :corollary (natp (proof-world-reg register world)))
                 (:linear :corollary (< (proof-world-reg register world) (expt 2 64)))))

(defthm generated-pc-bounds
  (and (natp (proof-world-pc world)) (< (proof-world-pc world) (expt 2 64)))
  :hints (("Goal" :in-theory (enable proof-world-pc)))
  :rule-classes ((:type-prescription :corollary (natp (proof-world-pc world)))
                 (:linear :corollary (< (proof-world-pc world) (expt 2 64)))))

(defthm generated-sp-bounds
  (and (natp (generated-sp world)) (< (generated-sp world) (expt 2 64)))
  :hints (("Goal" :in-theory (enable generated-sp)))
  :rule-classes ((:type-prescription :corollary (natp (generated-sp world)))
                 (:linear :corollary (< (generated-sp world) (expt 2 64)))))

(defthm generated-reg-of-set-reg
  (implies (and (natp target) (< target 31))
           (equal (proof-world-reg register (generated-set-reg target value world))
                  (if (equal register target)
                      (boymoo-model::a64-unsigned 64 value)
                    (proof-world-reg register world))))
  :hints (("Goal" :in-theory (enable generated-set-reg proof-world-reg proof-reg))))

(defthm generated-reg-of-control-updates
  (and (equal (proof-world-reg register (generated-set-pc pc world))
              (proof-world-reg register world))
       (equal (proof-world-reg register (generated-set-sp sp world))
              (proof-world-reg register world))
       (equal (proof-world-reg register (generated-set-flags flags world))
              (proof-world-reg register world))
       (equal (proof-world-reg register (generated-store-word address value world))
              (proof-world-reg register world)))
  :hints (("Goal" :in-theory (enable generated-set-pc generated-set-sp
                                    generated-set-flags generated-store-word
                                    proof-world-reg proof-reg boymoo-model::a64-store))))

(defthm generated-pc-of-updates
  (and (equal (proof-world-pc (generated-set-pc pc world))
              (boymoo-model::a64-unsigned 64 pc))
       (equal (proof-world-pc (generated-set-reg register value world))
              (proof-world-pc world))
       (equal (proof-world-pc (generated-set-sp sp world)) (proof-world-pc world))
       (equal (proof-world-pc (generated-set-flags flags world)) (proof-world-pc world))
       (equal (proof-world-pc (generated-store-word address value world))
              (proof-world-pc world)))
  :hints (("Goal" :in-theory (enable generated-set-pc generated-set-reg generated-set-sp
                                    generated-set-flags generated-store-word
                                    proof-world-pc boymoo-model::a64-store))))

(defthm generated-sp-of-updates
  (and (equal (generated-sp (generated-set-sp sp world))
              (boymoo-model::a64-unsigned 64 sp))
       (equal (generated-sp (generated-set-pc pc world)) (generated-sp world))
       (equal (generated-sp (generated-set-reg register value world)) (generated-sp world))
       (equal (generated-sp (generated-set-flags flags world)) (generated-sp world))
       (equal (generated-sp (generated-store-word address value world))
              (generated-sp world)))
  :hints (("Goal" :in-theory (enable generated-sp generated-set-pc generated-set-reg
                                    generated-set-sp generated-set-flags generated-store-word
                                    boymoo-model::a64-store))))

(defthm generated-flags-of-updates
  (and (equal (generated-flags (generated-set-flags flags world))
              (boymoo-model::a64-unsigned 4 flags))
       (equal (generated-flags (generated-set-pc pc world)) (generated-flags world))
       (equal (generated-flags (generated-set-reg register value world))
              (generated-flags world))
       (equal (generated-flags (generated-set-sp sp world)) (generated-flags world))
       (equal (generated-flags (generated-store-word address value world))
              (generated-flags world)))
  :hints (("Goal" :in-theory (enable generated-flags generated-set-pc generated-set-reg
                                    generated-set-sp generated-set-flags generated-store-word
                                    boymoo-model::a64-store))))

(defthm generated-memory-of-register-updates
  (and (equal (boymoo-model::a64-memory (proof-world-machine (generated-set-pc pc world)))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (boymoo-model::a64-memory
               (proof-world-machine (generated-set-reg register value world)))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (boymoo-model::a64-memory (proof-world-machine (generated-set-sp sp world)))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (boymoo-model::a64-memory
               (proof-world-machine (generated-set-flags flags world)))
              (boymoo-model::a64-memory (proof-world-machine world))))
  :hints (("Goal" :in-theory (enable generated-set-pc generated-set-reg
                                    generated-set-sp generated-set-flags))))

(defthm generated-load-of-register-updates
  (and (equal (generated-load-word address (generated-set-pc pc world))
              (generated-load-word address world))
       (equal (generated-load-word address (generated-set-reg register value world))
              (generated-load-word address world))
       (equal (generated-load-word address (generated-set-sp sp world))
              (generated-load-word address world))
       (equal (generated-load-word address (generated-set-flags flags world))
              (generated-load-word address world)))
  :hints (("Goal" :in-theory (enable generated-load-word proof-load-word))))

(local
 (defthm generated-update-nth-replaces
   (equal (update-nth index value (update-nth index old entries))
          (update-nth index value entries))
   :hints (("Goal" :induct (update-nth index value entries)))))

(local
 (defthm generated-cdr-of-update-nth-positive
   (implies (posp index)
            (equal (cdr (update-nth index value entries))
                   (update-nth (1- index) value (cdr entries))))
   :hints (("Goal" :expand (update-nth index value entries)))))

(local
 (defun generated-update-induction (left right entries)
   (declare (xargs :measure (nfix left)))
   (if (or (zp left) (zp right))
       entries
     (generated-update-induction (1- left) (1- right) (cdr entries)))))

(local
 (defthm generated-update-nth-commutes
   (implies (and (natp small) (natp large) (< small large))
            (equal (update-nth large y (update-nth small x entries))
                   (update-nth small x (update-nth large y entries))))
   :hints (("Goal" :induct (generated-update-induction small large entries)))))

(local
 (defthm generated-update-pc-over-sp
   (equal (update-nth 2 pc (update-nth 1 sp entries))
          (update-nth 1 sp (update-nth 2 pc entries)))
   :hints (("Goal" :use (:instance generated-update-nth-commutes
                                   (small 1) (large 2) (x sp) (y pc))
                   :in-theory (disable generated-update-nth-commutes)))))

(local
 (defthm generated-update-pc-over-flags
   (equal (update-nth 2 pc (update-nth 3 flags entries))
          (update-nth 3 flags (update-nth 2 pc entries)))
   :hints (("Goal" :use (:instance generated-update-nth-commutes
                                   (small 2) (large 3) (x pc) (y flags))
                   :in-theory (disable generated-update-nth-commutes)))))

(defthm generated-ordinary-world-updates
  (and (equal (generated-set-pc pc (generated-set-pc previous world))
              (generated-set-pc pc world))
       (equal (generated-set-pc pc (generated-set-reg register value world))
              (generated-set-reg register value (generated-set-pc pc world)))
       (equal (generated-set-pc pc (generated-set-sp sp world))
              (generated-set-sp sp (generated-set-pc pc world)))
       (equal (generated-set-pc pc (generated-set-flags flags world))
              (generated-set-flags flags (generated-set-pc pc world))))
  :hints (("Goal" :in-theory (enable generated-set-machine generated-set-pc
                                    generated-set-reg generated-set-sp generated-set-flags
                                    proof-world-machine))))

(defthm generated-world-control-projections
  (and (equal (proof-world-stop (generated-set-pc pc world)) (proof-world-stop world))
       (equal (proof-world-stop (generated-set-sp sp world)) (proof-world-stop world))
       (equal (proof-world-stop (generated-set-reg register value world))
              (proof-world-stop world))
       (equal (proof-world-stop (generated-set-flags flags world)) (proof-world-stop world))
       (equal (proof-world-stop (generated-store-word address value world))
              (proof-world-stop world))
       (equal (proof-world-regions (generated-set-pc pc world)) (proof-world-regions world))
       (equal (proof-world-regions (generated-set-reg register value world))
              (proof-world-regions world))
       (equal (proof-world-regions (generated-set-sp sp world)) (proof-world-regions world))
       (equal (proof-world-regions (generated-set-flags flags world)) (proof-world-regions world))
       (equal (proof-world-regions (generated-store-word address value world))
              (proof-world-regions world)))
  :hints (("Goal" :in-theory (e/d (generated-set-pc generated-set-reg generated-set-sp
                                   generated-set-flags generated-store-word)
                                  (proof-world-regions)))))
