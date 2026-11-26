(in-package "BOYMOO-PROOFS")

(include-book "runtime-layout")
(include-book "comparisons")
(include-book "budget")
(include-book "memory")
(include-book "pages")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-instruction-effect proof-world-reg proof-world-pc
                     proof-world-machine proof-reg proof-load-word
                     collection-cpu-p collection-write-pc collection-write-register
                     collection-read-word collection-write-word collection-write-flags
                     collection-write-sp
                     collection-subtract-flags boymoo-model::a64-unsigned
                     boymoo-model::a64-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes (:definition ash))))

(defthm collection-finish-tests-capacity
  (let* ((entry (collection-linux-offset "rt:collect-finish"))
         (metadata (proof-world-reg 17 world))
         (floor (boymoo-model::a64-unsigned
                 64 (collection-read-word (+ metadata 24) world)))
         (end (boymoo-model::a64-unsigned
               64 (collection-read-word (+ metadata 32) world)))
         (box (proof-world-reg 20 world))
         (cells (proof-world-reg 21 world))
         (request (boymoo-model::a64-unsigned
                   64 (collection-read-word
                       (boymoo-model::a64-sp (proof-world-machine world)) world)))
         (retained (collection-retained-bytes floor box cells end))
         (sum (+ retained request))
         (next (collection-trace-effect
                (collection-linux-trace "rt:collect-finish" '(0 1 2 3 4 5 6 7 8) origin)
                world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry))
                  (equal end (+ floor *proof-space-size*))
                  (<= floor box) (<= box cells) (<= cells end)
                  (<= request *proof-space-size*))
             (and (equal (proof-world-reg 0 next) request)
                  (equal (proof-world-reg 4 next) retained)
                  (equal (proof-world-reg 5 next) sum)
                  (equal (proof-world-reg 6 next) *proof-space-size*)
                  (equal (proof-world-pc next)
                         (+ origin (if (< *proof-space-size* sum)
                                       (collection-linux-offset "rt:heap-size")
                                     (+ entry 36))))
                  (implies (< *proof-space-size* sum)
                           (proof-resource-bound-p :heap-size sum world))
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine world)))))))

(defthm collection-finish-computes-next-budget
  (let* ((entry (collection-linux-offset "rt:collect-finish"))
         (retained (proof-world-reg 4 world))
         (box (proof-world-reg 20 world))
         (budget (collection-budget retained request))
         (next (collection-trace-effect
                (collection-linux-trace "rt:collect-finish" '(9 10 11 12 13 14 15 16 17 18)
                                        origin)
                world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 36))
                  (natp request)
                  (equal (proof-world-reg 5 world) (+ retained request))
                  (equal (proof-world-reg 6 world) *proof-space-size*)
                  (<= (+ retained request) *proof-space-size*))
             (and (equal (proof-world-reg 7 next) budget)
                  (equal (proof-world-reg 26 next)
                         (boymoo-model::a64-unsigned 64 (- (+ box budget) retained)))
                  (equal (proof-world-pc next) (+ origin entry 76))))))

(defthm collection-finish-swaps-space-metadata
  (let* ((entry (collection-linux-offset "rt:collect-finish"))
         (metadata (proof-world-reg 17 world))
         (old-floor (collection-read-word metadata world))
         (old-end (collection-read-word (+ metadata 8) world))
         (old-cells (collection-read-word (+ metadata 16) world))
         (new-floor (proof-world-reg 2 world))
         (new-end (proof-world-reg 3 world))
         (new-cells (proof-world-reg 21 world))
         (next (collection-trace-effect
                (collection-linux-trace "rt:collect-finish" '(19 20 21 22 23 24 25)
                                        origin)
                world))
         (written (collection-write-word (+ metadata 24) old-floor world))
         (written (collection-write-word (+ metadata 32) old-end written))
         (written (collection-write-word metadata new-floor written))
         (written (collection-write-word (+ metadata 8) new-end written))
         (written (collection-write-word (+ metadata 16) new-cells written)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 76)))
             (and (equal (proof-world-pc next) (+ origin entry 104))
                  (equal (proof-world-reg 8 next) (proof-world-reg 27 world))
                  (equal (proof-world-reg 27 next) (proof-world-reg 20 world))
                  (equal (proof-world-reg 19 next) old-floor)
                  (equal (proof-world-reg 22 next) old-end)
                  (equal (proof-world-reg 20 next) old-cells)
                  (equal (boymoo-model::a64-memory (proof-world-machine next))
                         (boymoo-model::a64-memory (proof-world-machine written)))))))

(defthm collection-finish-selects-pending-allocator
  (let* ((entry (collection-linux-offset "rt:collect-finish"))
         (headerp (equal (proof-world-reg 1 world) 0))
         (next (collection-trace-effect
                (collection-linux-trace "rt:collect-finish"
                                        (if headerp '(41 42) '(41)) origin)
                world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 164)))
             (and (equal (proof-world-pc next)
                         (+ origin (collection-linux-offset
                                    (if headerp "rt:alloc" "rt:alloc-cells"))))
                  (equal (proof-world-reg 0 next) (proof-world-reg 0 world))
                  (equal (proof-world-reg 30 next) (proof-world-reg 30 world)))))
  :hints (("Goal" :cases ((equal (proof-world-reg 1 world) 0)))))

(local
 (defthm collection-page-quotient-is-unchanged-by-word-cast
   (implies (unsigned-byte-p 64 word)
            (equal (boymoo-model::a64-unsigned 64 (ash word -16))
                   (ash word -16)))
   :hints (("Goal" :use collection-right-shift-by-sixteen-fits
                   :in-theory (disable collection-right-shift-by-sixteen-fits)))))

(defthm collection-finish-passes-retired-header-range
  (let* ((entry (collection-linux-offset "rt:collect-finish"))
         (box (proof-world-reg 8 world))
         (next (collection-trace-effect
                (collection-linux-trace "rt:collect-finish" '(26 27 28 29 30 31) origin)
                world)))
    (implies (and (collection-cpu-p world)
                  (unsigned-byte-p 64 (+ box 65535))
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 104)))
             (and (equal (proof-world-pc next)
                         (+ origin (collection-linux-offset "rt:release-range")))
                  (equal (proof-world-reg 0 next) (proof-world-reg 19 world))
                  (equal (proof-world-reg 1 next) (collection-page-ceiling box))
                  (equal (proof-world-reg 30 next) (+ origin entry 128)))))
  :hints (("Goal"
           :use ((:instance collection-right-shift-by-sixteen-fits
                            (word (+ 65535 (proof-world-reg 8 world)))))
           :in-theory (disable collection-right-shift-by-sixteen-fits
                               collection-page-floor))))

(defthm collection-finish-passes-retired-cons-range
  (let* ((entry (collection-linux-offset "rt:collect-finish"))
         (cells (proof-world-reg 20 world))
         (next (collection-trace-effect
                (collection-linux-trace "rt:collect-finish" '(32 33 34 35) origin)
                world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry 128)))
             (and (equal (proof-world-pc next)
                         (+ origin (collection-linux-offset "rt:release-range")))
                  (equal (proof-world-reg 0 next) (collection-page-floor cells))
                  (equal (proof-world-reg 1 next) (proof-world-reg 22 world))
                  (equal (proof-world-reg 30 next) (+ origin entry 144)))))
  :hints (("Goal"
           :use ((:instance collection-right-shift-by-sixteen-fits
                            (word (proof-world-reg 20 world))))
           :in-theory (disable collection-right-shift-by-sixteen-fits
                               collection-page-floor))))

(defthm collection-release-range-selects-call-or-return
  (let* ((entry (collection-linux-offset "rt:release-range"))
         (start (proof-world-reg 0 world))
         (end (proof-world-reg 1 world))
         (nonempty (< start end))
         (next (collection-trace-effect
                (collection-linux-trace "rt:release-range"
                                        (if nonempty '(0 1 2 3) '(0 1)) origin)
                world)))
    (implies (and (collection-cpu-p world)
                  (proof-span-p origin (car *collection-linux-layout*))
                  (equal (proof-world-pc world) (+ origin entry)))
             (and (equal (proof-world-pc next)
                         (+ origin (if nonempty
                                       (collection-linux-offset "sys:release")
                                     (collection-linux-offset "rt:release-return"))))
                  (implies nonempty
                           (and (equal (proof-world-reg 0 next) start)
                                (equal (proof-world-reg 1 next) (- end start))
                                (equal (proof-world-reg 30 next) (+ origin entry 16))))
                  (implies (not nonempty)
                           (equal (boymoo-model::a64-memory (proof-world-machine next))
                                  (boymoo-model::a64-memory (proof-world-machine world)))))))
  :hints (("Goal" :cases ((< (proof-world-reg 0 world) (proof-world-reg 1 world))))))
