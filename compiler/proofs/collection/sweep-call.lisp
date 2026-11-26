(in-package "BOYMOO-PROOFS")

(include-book "sweep-contents")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-sweep-prologue-trace (origin)
  (collection-linux-trace "rt:sweep-strings" '(0 1 2) origin))

(defun collection-sweep-epilogue-trace (origin)
  (collection-linux-trace "rt:sweep-done" '(0 1 2 3 4 5 6) origin))

(defun collection-sweep-call-trace (records origin)
  (append (collection-sweep-prologue-trace origin)
          (collection-sweep-traversal-trace records origin)
          (collection-sweep-epilogue-trace origin)))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-reg proof-world-pc proof-world-stop
                     proof-world-regions proof-world-replies proof-load-word proof-instruction-effect
                     collection-cpu-p collection-write-register collection-write-word collection-write-sp
                     collection-write-pc collection-write-flags collection-subtract-flags collection-read-word
                     boymoo-model::a64-unsigned boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-condition boymoo-model::a64-nzcv boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand) (:definition acl2::binary-logior))))

(defthm collection-sweep-prologue-saves-pair-and-starts-list
  (let* ((entry (collection-linux-offset "rt:sweep-strings"))
         (next (collection-trace-effect (collection-sweep-prologue-trace origin) world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (heap (proof-world-reg 28 world)))
    (implies (and (collection-sweep-entry-p entry origin world) (<= 16 sp) (<= 128 heap)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world))))
             (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-string") origin next)
                  (equal (boymoo-model::a64-sp (proof-world-machine next)) (- sp 16))
                  (equal (collection-read-word (- sp 16) next) (proof-world-reg 29 world))
                  (equal (collection-read-word (- sp 8) next) (proof-world-reg 30 world))
                  (equal (proof-world-reg 19 next) (- heap 72))
                  (equal (proof-world-reg 22 next) 0)
                  (equal (proof-world-regions next) (proof-world-regions world))
                  (equal (proof-world-replies next) (proof-world-replies world))
                  (equal (proof-world-stop next) (proof-world-stop world))
                  (proof-streams-preserved-p world next)
                  (alistp (boymoo-model::a64-memory (proof-world-machine next)))
                  (implies (not (member-equal register '(19 22)))
                           (equal (proof-world-reg register next) (proof-world-reg register world))))))
  :hints (("Goal" :in-theory (enable proof-world-regions proof-world-replies proof-world-stop))))

(defthm collection-sweep-epilogue-returns-and-installs-accounting
  (let* ((entry (collection-linux-offset "rt:sweep-done"))
         (next (collection-trace-effect (collection-sweep-epilogue-trace origin) world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (heap (proof-world-reg 28 world))
         (budget (max *proof-minimum-string-budget* (proof-world-reg 22 world))))
    (implies (and (collection-sweep-entry-p entry origin world) (<= 128 heap)
                  (unsigned-byte-p 64 (+ sp 16))
                  (proof-disjoint-p sp (+ sp 16) (- heap 56) (- heap 40))
                  (alistp (boymoo-model::a64-memory (proof-world-machine world))))
             (and (equal (proof-world-pc next) (collection-read-word (+ sp 8) world))
                  (collection-cpu-p next)
                  (equal (proof-world-reg 29 next) (collection-read-word sp world))
                  (equal (proof-world-reg 30 next) (collection-read-word (+ sp 8) world))
                  (equal (boymoo-model::a64-sp (proof-world-machine next)) (+ sp 16))
                  (equal (collection-read-word (- heap 56) next) 0)
                  (equal (collection-read-word (- heap 48) next) budget)
                  (equal (proof-world-regions next) (proof-world-regions world))
                  (equal (proof-world-replies next) (proof-world-replies world))
                  (equal (proof-world-stop next) (proof-world-stop world))
                  (proof-streams-preserved-p world next)
                  (implies (not (member-equal register '(2 17 22 29 30)))
                           (equal (proof-world-reg register next) (proof-world-reg register world))))))
  :hints (("Goal" :in-theory (enable proof-world-regions proof-world-replies proof-world-stop))))

(local
 (in-theory (disable collection-sweep-entry-p collection-sweep-traversal-trace
                     collection-sweep-traversal-input-p collection-trace-effect)))

(defthm collection-sweep-body-protects-saved-pair
  (let* ((link (proof-world-reg 19 world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (address (+ sp (if linkp 8 0)))
         (after (collection-trace-effect (collection-sweep-traversal-trace records origin) world)))
    (implies (and (collection-sweep-traversal-input-p records origin world)
                  (proof-span-p sp 16)
                  (proof-disjoint-p sp (+ sp 16) link (+ link 8))
                  (collection-sweep-spans-separate-p sp (+ sp 16) records))
             (equal (collection-read-word address after) (collection-read-word address world))))
  :rule-classes nil
  :hints (("Goal" :cases (linkp)
                  :use ((:instance collection-sweep-traversal-preserves-word-outside-links-and-mappings
                                   (address (+ (boymoo-model::a64-sp (proof-world-machine world)) (if linkp 8 0))))
                        (:instance collection-sweep-subspan-separates-from-same-mappings
                                   (address (+ (boymoo-model::a64-sp (proof-world-machine world)) (if linkp 8 0)))
                                   (width 8) (start (boymoo-model::a64-sp (proof-world-machine world)))
                                   (end (+ 16 (boymoo-model::a64-sp (proof-world-machine world))))))
                  :in-theory (disable collection-sweep-spans-separate-p))))

(defun collection-sweep-body-end (records origin world)
  (collection-trace-effect
   (collection-sweep-traversal-trace records origin)
   (collection-trace-effect (collection-sweep-prologue-trace origin) world)))

(defun collection-sweep-call-input-p (records origin world)
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (heap (proof-world-reg 28 world))
         (loop (collection-trace-effect (collection-sweep-prologue-trace origin) world)))
    (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-strings") origin world)
         (<= 16 sp) (<= 128 heap)
         (alistp (boymoo-model::a64-memory (proof-world-machine world)))
         (proof-disjoint-p (- sp 16) sp (- heap 72) (- heap 40))
         (collection-sweep-spans-separate-p (- sp 16) sp records)
         (collection-sweep-traversal-input-p records origin loop))))

(local
 (in-theory (disable collection-sweep-prologue-trace collection-sweep-epilogue-trace
                     collection-sweep-spans-separate-p collection-sweep-retained-bytes
                     collection-sweep-discard-count proof-streams-preserved-p)))

(local
 (defthm collection-sweep-body-preserves-caller-pair-at-restore
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
          (next (collection-sweep-body-end records origin world)))
     (implies (collection-sweep-call-input-p records origin world)
              (and (equal (boymoo-model::a64-sp (proof-world-machine next)) (- sp 16))
                   (equal (collection-read-word (- sp 16) next) (proof-world-reg 29 world))
                   (equal (collection-read-word (- sp 8) next) (proof-world-reg 30 world)))))
   :hints (("Goal"
            :use ((:instance collection-sweep-prologue-saves-pair-and-starts-list (register 28))
                  (:instance collection-sweep-body-protects-saved-pair
                             (linkp t) (world (collection-trace-effect (collection-sweep-prologue-trace origin) world)))
                  (:instance collection-sweep-body-protects-saved-pair
                             (linkp nil) (world (collection-trace-effect (collection-sweep-prologue-trace origin) world))))
            :in-theory (disable collection-sweep-prologue-saves-pair-and-starts-list)))))

(local
 (defthm collection-sweep-body-opens-epilogue-with-exact-accounting
   (let* ((next (collection-sweep-body-end records origin world)))
     (implies (and (collection-sweep-call-input-p records origin world)
                   (proof-span-p origin (car *collection-linux-layout*)))
              (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-done") origin next)
                   (equal (proof-world-reg 22 next) (collection-sweep-retained-bytes records))
                   (equal (proof-world-reg 28 next) (proof-world-reg 28 world))
                   (equal (proof-world-replies next)
                          (nthcdr (collection-sweep-discard-count records) (proof-world-replies world)))
                   (equal (proof-world-regions next)
                          (collection-sweep-surviving-regions records (proof-world-regions world)))
                   (equal (proof-world-stop next) (proof-world-stop world))
                   (implies (not (member-equal register '(0 1 2 8 19 20 22 30)))
                            (equal (proof-world-reg register next) (proof-world-reg register world))))))
   :hints (("Goal"
            :use ((:instance collection-sweep-prologue-saves-pair-and-starts-list (register 28))
                  (:instance collection-sweep-traversal-removes-exactly-discarded-regions
                             (world (collection-trace-effect (collection-sweep-prologue-trace origin) world))))
            :in-theory (enable collection-sweep-entry-p)))))

(defthm collection-sweep-call-returns-and-debits-kernel-replies
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (body-end (collection-sweep-body-end records origin world))
         (after (collection-trace-effect (collection-sweep-call-trace records origin) world))
         (heap (proof-world-reg 28 world)))
    (implies (and (collection-sweep-call-input-p records origin world)
                  (alistp (boymoo-model::a64-memory (proof-world-machine body-end)))
                  (proof-span-p origin (car *collection-linux-layout*)))
             (and (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (collection-cpu-p after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) sp)
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (collection-read-word (- heap 56) after) 0)
                  (equal (collection-read-word (- heap 48) after)
                         (max *proof-minimum-string-budget* (collection-sweep-retained-bytes records)))
                  (equal (proof-world-replies after)
                         (nthcdr (collection-sweep-discard-count records) (proof-world-replies world)))
                  (equal (proof-world-regions after)
                         (collection-sweep-surviving-regions records (proof-world-regions world)))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (implies (not (member-equal register '(0 1 2 8 17 19 20 22)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :use ((:instance collection-sweep-body-preserves-caller-pair-at-restore)
                 (:instance collection-sweep-body-opens-epilogue-with-exact-accounting (register 28))
                 (:instance collection-sweep-body-opens-epilogue-with-exact-accounting)
                 (:instance collection-sweep-epilogue-returns-and-installs-accounting
                            (world (collection-sweep-body-end records origin world))))
           :in-theory (disable collection-sweep-body-preserves-caller-pair-at-restore
                               collection-sweep-body-opens-epilogue-with-exact-accounting
                               collection-sweep-epilogue-returns-and-installs-accounting))))

(local
 (defthm collection-sweep-prologue-preserves-word-outside-pair
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
          (after (collection-trace-effect (collection-sweep-prologue-trace origin) world)))
     (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-strings") origin world)
                   (<= 16 sp) (<= 128 (proof-world-reg 28 world))
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-span-p address 8)
                   (proof-disjoint-p address (+ address 8) (- sp 16) sp))
              (equal (collection-read-word address after) (collection-read-word address world))))
   :hints (("Goal" :in-theory (enable collection-sweep-entry-p collection-sweep-prologue-trace
                                      collection-trace-effect)))))

(local
 (defthm collection-sweep-epilogue-preserves-word-outside-accounting
   (let* ((heap (proof-world-reg 28 world))
          (after (collection-trace-effect (collection-sweep-epilogue-trace origin) world)))
     (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-done") origin world)
                   (<= 128 heap)
                   (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                   (proof-span-p address 8)
                   (proof-disjoint-p address (+ address 8) (- heap 56) (- heap 40)))
              (equal (collection-read-word address after) (collection-read-word address world))))
   :hints (("Goal" :in-theory (enable collection-sweep-entry-p collection-sweep-epilogue-trace
                                      collection-trace-effect)))))

(defthm collection-sweep-call-preserves-word-outside-its-write-spans
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (heap (proof-world-reg 28 world))
         (body-end (collection-sweep-body-end records origin world))
         (after (collection-trace-effect (collection-sweep-call-trace records origin) world)))
    (implies (and (collection-sweep-call-input-p records origin world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (alistp (boymoo-model::a64-memory (proof-world-machine body-end)))
                  (proof-span-p address 8)
                  (proof-disjoint-p address (+ address 8) (- sp 16) sp)
                  (proof-disjoint-p address (+ address 8) (- heap 72) (- heap 64))
                  (proof-disjoint-p address (+ address 8) (- heap 56) (- heap 40))
                  (collection-sweep-spans-separate-p address (+ address 8) records))
             (equal (collection-read-word address after) (collection-read-word address world))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-sweep-prologue-saves-pair-and-starts-list (register 28))
                 (:instance collection-sweep-prologue-preserves-word-outside-pair)
                 (:instance collection-sweep-traversal-preserves-word-outside-links-and-mappings
                            (world (collection-trace-effect (collection-sweep-prologue-trace origin) world)))
                 (:instance collection-sweep-body-opens-epilogue-with-exact-accounting (register 28))
                 (:instance collection-sweep-epilogue-preserves-word-outside-accounting
                            (world (collection-sweep-body-end records origin world))))
           :in-theory (disable collection-sweep-prologue-saves-pair-and-starts-list
                               collection-sweep-prologue-preserves-word-outside-pair
                               collection-sweep-body-opens-epilogue-with-exact-accounting
                               collection-sweep-epilogue-preserves-word-outside-accounting))))
