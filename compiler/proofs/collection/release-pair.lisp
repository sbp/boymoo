(in-package "BOYMOO-PROOFS")

(include-book "release-call")
(local (include-book "arithmetic/equalities" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun collection-nonempty-release-p (world)
  (< (proof-world-reg 0 world) (proof-world-reg 1 world)))

(defun collection-selected-release-trace (origin world)
  (if (collection-nonempty-release-p world)
      (collection-positive-release-trace origin)
    (collection-empty-release-trace origin)))

(defun collection-release-input-p (origin world)
  (let* ((start (proof-world-reg 0 world))
         (end (proof-world-reg 1 world))
         (sp (boymoo-model::a64-sp (proof-world-machine world))))
    (and (collection-cpu-p world)
         (proof-span-p origin (car *collection-linux-layout*))
         (equal (proof-world-pc world) (+ origin (collection-linux-offset "rt:release-range")))
         (alistp (boymoo-model::a64-memory (proof-world-machine world)))
         (implies (collection-nonempty-release-p world)
                  (and (<= 16 sp)
                       (proof-disjoint-p (- sp 16) sp start end)
                       (collection-relinquish-p start (- end start) world)))
         (collection-trace-ready-p (collection-selected-release-trace origin world)
                                   (list (proof-world-reg 30 world)) world))))

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-reg proof-world-pc proof-world-stop
                     proof-world-regions proof-world-replies proof-step proof-load-word
                     proof-segment-p proof-streams-preserved-p proof-instruction-effect
                     collection-cpu-p collection-read-word collection-trace-effect collection-trace-ready-p
                     collection-positive-release-trace collection-empty-release-trace
                     collection-release-saved-pair collection-relinquish-p
                     proof-clear-memory proof-clear-span boymoo-model::a64-unsigned
                     boymoo-model::a64-sp boymoo-model::a64-memory)))

(defthm collection-selected-release-returns-with-range-and-frame-effects
  (let* ((trace (collection-selected-release-trace origin world))
         (after (collection-trace-effect trace world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (start (proof-world-reg 0 world))
         (end (proof-world-reg 1 world))
         (saved (collection-release-saved-pair (- sp 16) world))
         (memory (boymoo-model::a64-memory (proof-world-machine world))))
    (implies (collection-release-input-p origin world)
             (and (collection-cpu-p after)
                  (proof-segment-p (len trace) (list (proof-world-reg 30 world)) world :cut after)
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) sp)
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (proof-streams-preserved-p world after)
                  (equal (proof-world-replies after)
                         (if (< start end) (cdr (proof-world-replies world)) (proof-world-replies world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (if (< start end)
                             (proof-clear-memory start end
                                                 (boymoo-model::a64-memory (proof-world-machine saved)))
                           memory))
                  (implies (not (member-equal register '(0 1 2 8)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal" :cases ((collection-nonempty-release-p world))
                  :use ((:instance collection-empty-release-returns-without-clearing)
                        (:instance collection-positive-release-clears-range-and-restores-frame)
                        (:instance collection-ready-trace-reaches-cut
                                   (trace (collection-selected-release-trace origin world))
                                   (cuts (list (proof-world-reg 30 world)))))
                  :in-theory (disable collection-positive-release-clears-range-and-restores-frame))))

(defun collection-retired-release-setup (headerp origin)
  (collection-linux-trace "rt:collect-finish"
                          (if headerp '(26 27 28 29 30 31) '(32 33 34 35)) origin))

(defun collection-retired-release-entry-p (headerp origin world)
  (and (collection-cpu-p world)
       (proof-span-p origin (car *collection-linux-layout*))
       (equal (proof-world-pc world)
              (+ origin (collection-linux-offset "rt:collect-finish") (if headerp 104 128)))
       (implies headerp (unsigned-byte-p 64 (+ 65535 (proof-world-reg 8 world))))))

(defun collection-retired-release-round-trace (headerp origin world)
  (let* ((setup (collection-retired-release-setup headerp origin))
         (call (collection-trace-effect setup world)))
    (append setup (collection-selected-release-trace origin call))))

(local
 (in-theory (disable collection-write-pc collection-write-register collection-write-flags
                     boymoo-model::a64-condition boymoo-model::a64-nzcv
                     (:definition ash) (:definition acl2::binary-logand))))

(defthm collection-retired-call-setup-preserves-caller-data
  (let* ((trace (collection-retired-release-setup headerp origin))
         (after (collection-trace-effect trace world)))
    (implies (collection-retired-release-entry-p headerp origin world)
             (and (equal (proof-world-replies after) (proof-world-replies world))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (proof-streams-preserved-p world after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (implies (not (member-equal register '(0 1 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal" :cases (headerp)
                  :use ((:instance collection-right-shift-by-sixteen-fits (word (proof-world-reg 20 world)))
                        (:instance collection-right-shift-by-sixteen-fits (word (+ 65535 (proof-world-reg 8 world)))))
                  :in-theory (e/d (collection-trace-effect proof-world-replies proof-world-regions
                                                           proof-world-stop proof-streams-preserved-p)
                                   (collection-right-shift-by-sixteen-fits)))))

(local
 (in-theory (disable collection-release-input-p collection-retired-release-setup
                     collection-retired-release-entry-p collection-selected-release-trace
                     collection-nonempty-release-p)))

(local
 (defthm collection-retired-call-setup-passes-range-and-link
   (let ((after (collection-trace-effect (collection-retired-release-setup headerp origin) world)))
     (implies (collection-retired-release-entry-p headerp origin world)
              (and (equal (proof-world-reg 0 after)
                          (if headerp (proof-world-reg 19 world)
                            (collection-page-floor (proof-world-reg 20 world))))
                   (equal (proof-world-reg 1 after)
                          (if headerp (collection-page-ceiling (proof-world-reg 8 world))
                            (proof-world-reg 22 world)))
                   (equal (proof-world-reg 30 after)
                          (+ origin (collection-linux-offset "rt:collect-finish") (if headerp 128 144))))))
   :hints (("Goal" :cases (headerp)
                   :use ((:instance collection-finish-passes-retired-header-range)
                         (:instance collection-finish-passes-retired-cons-range))
                   :in-theory (e/d (collection-retired-release-setup collection-retired-release-entry-p)
                                    (collection-page-ceiling collection-page-floor
                                     collection-finish-passes-retired-header-range
                                     collection-finish-passes-retired-cons-range))))))

(defthm collection-retired-release-round-returns-and-keeps-other-endpoints
  (let* ((setup (collection-retired-release-setup headerp origin))
         (call (collection-trace-effect setup world))
         (trace (collection-retired-release-round-trace headerp origin world))
         (after (collection-trace-effect trace world))
         (base (if headerp (proof-world-reg 19 world) (collection-page-floor (proof-world-reg 20 world))))
         (end (if headerp (collection-page-ceiling (proof-world-reg 8 world)) (proof-world-reg 22 world))))
    (implies (and (collection-retired-release-entry-p headerp origin world)
                  (collection-release-input-p origin call))
             (and (collection-cpu-p after)
                  (equal (proof-world-pc after) (+ origin (collection-linux-offset "rt:collect-finish")
                                                       (if headerp 128 144)))
                  (equal (proof-world-replies after)
                         (if (< base end) (cdr (proof-world-replies world)) (proof-world-replies world)))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (implies (not (member-equal register '(0 1 2 8 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :cases (headerp)
           :do-not-induct t
           :use ((:instance collection-retired-call-setup-passes-range-and-link)
                 (:instance collection-retired-call-setup-preserves-caller-data)
                 (:instance collection-selected-release-returns-with-range-and-frame-effects
                            (world (collection-trace-effect (collection-retired-release-setup headerp origin) world))))
           :in-theory (disable collection-page-ceiling collection-page-floor proof-register-frame-p
                               collection-retired-call-setup-passes-range-and-link
                               collection-retired-call-setup-preserves-caller-data
                               collection-selected-release-returns-with-range-and-frame-effects))))

(defun collection-retired-release-pair-trace (origin world)
  (let* ((first (collection-retired-release-round-trace t origin world))
         (second (collection-trace-effect first world)))
    (append first (collection-retired-release-round-trace nil origin second))))

(defun collection-retired-release-pair-input-p (origin world)
  (let* ((header-call (collection-trace-effect (collection-retired-release-setup t origin) world))
         (header-return (collection-trace-effect (collection-retired-release-round-trace t origin world) world))
         (cons-call (collection-trace-effect (collection-retired-release-setup nil origin) header-return)))
    (and (collection-retired-release-entry-p t origin world)
         (collection-release-input-p origin header-call)
         (collection-release-input-p origin cons-call))))

(local
 (defthm collection-first-retired-round-opens-second
   (let* ((header-call (collection-trace-effect (collection-retired-release-setup t origin) world))
          (after (collection-trace-effect (collection-retired-release-round-trace t origin world) world)))
     (implies (and (collection-retired-release-entry-p t origin world)
                   (collection-release-input-p origin header-call))
              (collection-retired-release-entry-p nil origin after)))
   :hints (("Goal"
            :use ((:instance collection-retired-release-round-returns-and-keeps-other-endpoints
                             (headerp t) (register 19)))
            :in-theory (e/d (collection-retired-release-entry-p)
                             (collection-retired-release-round-returns-and-keeps-other-endpoints
                              collection-retired-release-round-trace))))))

(local (in-theory (disable collection-retired-release-round-trace)))

(local
 (defthm collection-debit-one-or-two-release-replies
   (and (equal (nthcdr 1 replies) (cdr replies))
        (equal (nthcdr 2 replies) (cddr replies)))
   :hints (("Goal" :expand ((nthcdr 1 replies) (nthcdr 2 replies)
                            (nthcdr 1 (cdr replies)) (nthcdr 0 (cdr replies))
                            (nthcdr 0 (cddr replies)))))))

(defthm collection-retired-release-pair-preserves-frame-and-counts-replies
  (let* ((trace (collection-retired-release-pair-trace origin world))
         (after (collection-trace-effect trace world))
         (calls (+ (if (< (proof-world-reg 19 world) (collection-page-ceiling (proof-world-reg 8 world))) 1 0)
                   (if (< (collection-page-floor (proof-world-reg 20 world)) (proof-world-reg 22 world)) 1 0))))
    (implies (collection-retired-release-pair-input-p origin world)
             (and (equal (proof-world-pc after) (+ origin (collection-linux-offset "rt:collect-finish") 144))
                  (collection-cpu-p after)
                  (equal (proof-world-replies after) (nthcdr calls (proof-world-replies world)))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (implies (not (member-equal register '(0 1 2 8 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :use ((:instance collection-retired-release-round-returns-and-keeps-other-endpoints (headerp t))
                 (:instance collection-retired-release-round-returns-and-keeps-other-endpoints (headerp t) (register 20))
                 (:instance collection-retired-release-round-returns-and-keeps-other-endpoints (headerp t) (register 22))
                 (:instance collection-first-retired-round-opens-second)
                 (:instance collection-retired-release-round-returns-and-keeps-other-endpoints
                            (headerp nil)
                            (world (collection-trace-effect (collection-retired-release-round-trace t origin world) world))))
           :in-theory (disable collection-first-retired-round-opens-second collection-page-ceiling collection-page-floor
                               collection-retired-release-round-returns-and-keeps-other-endpoints))))

(defthm collection-checked-retired-release-pair-returns-to-sweep-call
  (let* ((trace (collection-retired-release-pair-trace origin world))
         (cuts (list (+ origin (collection-linux-offset "rt:collect-finish") 144))))
    (implies (and (collection-retired-release-pair-input-p origin world)
                  (collection-trace-ready-p trace cuts world))
             (proof-segment-p (len trace) cuts world :cut (collection-trace-effect trace world))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable collection-retired-release-pair-input-p collection-retired-release-pair-trace))))

(defthm collection-selected-release-preserves-word-outside-clear-and-save
  (let* ((start (proof-world-reg 0 world))
         (end (proof-world-reg 1 world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (trace (collection-selected-release-trace origin world))
         (after (collection-trace-effect trace world)))
    (implies (and (collection-release-input-p origin world) (proof-span-p address 8)
                  (proof-disjoint-p address (+ address 8) start end)
                  (proof-disjoint-p address (+ address 8) (- sp 16) sp))
             (equal (collection-read-word address after) (collection-read-word address world))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((< (proof-world-reg 0 world) (proof-world-reg 1 world)))
           :use ((:instance collection-selected-release-returns-with-range-and-frame-effects (register 0))
                 (:instance collection-release-link-load-depends-on-memory
                            (first (collection-trace-effect (collection-selected-release-trace origin world) world))
                            (second (if (< (proof-world-reg 0 world) (proof-world-reg 1 world))
                                        (proof-clear-span (proof-world-reg 0 world) (proof-world-reg 1 world)
                                                          (collection-release-saved-pair
                                                           (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                           world))
                                      world)))
                 (:instance collection-clear-preserves-word-outside-range
                            (base (proof-world-reg 0 world)) (end (proof-world-reg 1 world))
                            (world (collection-release-saved-pair
                                    (- (boymoo-model::a64-sp (proof-world-machine world)) 16) world))))
           :in-theory (e/d (collection-release-input-p collection-nonempty-release-p collection-release-saved-pair)
                            (collection-selected-release-returns-with-range-and-frame-effects
                             collection-clear-preserves-word-outside-range collection-write-word)))))

(local
 (defthm collection-retired-round-protects-disjoint-word
   (let* ((base (if headerp (proof-world-reg 19 world) (collection-page-floor (proof-world-reg 20 world))))
          (end (if headerp (collection-page-ceiling (proof-world-reg 8 world)) (proof-world-reg 22 world)))
          (sp (boymoo-model::a64-sp (proof-world-machine world)))
          (call (collection-trace-effect (collection-retired-release-setup headerp origin) world))
          (after (collection-trace-effect (collection-retired-release-round-trace headerp origin world) world)))
     (implies (and (collection-retired-release-entry-p headerp origin world)
                   (collection-release-input-p origin call)
                   (proof-span-p address 8)
                   (proof-disjoint-p address (+ address 8) base end)
                   (proof-disjoint-p address (+ address 8) (- sp 16) sp))
              (equal (collection-read-word address after) (collection-read-word address world))))
   :hints (("Goal" :cases (headerp)
                   :use ((:instance collection-retired-call-setup-passes-range-and-link)
                         (:instance collection-retired-call-setup-preserves-caller-data (register 19))
                         (:instance collection-selected-release-preserves-word-outside-clear-and-save
                                    (world (collection-trace-effect (collection-retired-release-setup headerp origin) world)))
                         (:instance collection-release-link-load-depends-on-memory
                                    (first (collection-trace-effect (collection-retired-release-setup headerp origin) world))
                                    (second world)))
                   :in-theory (e/d (collection-retired-release-round-trace)
                                    (collection-retired-call-setup-passes-range-and-link
                                     collection-retired-call-setup-preserves-caller-data
                                     collection-page-ceiling collection-page-floor))))))

(defthm collection-retired-release-pair-protects-word-outside-ranges-and-save
  (let* ((first (collection-retired-release-round-trace t origin world))
         (after (collection-trace-effect (collection-retired-release-pair-trace origin world) world))
         (sp (boymoo-model::a64-sp (proof-world-machine world))))
    (implies (and (collection-retired-release-pair-input-p origin world)
                  (proof-span-p address 8)
                  (proof-disjoint-p address (+ address 8) (proof-world-reg 19 world)
                                    (collection-page-ceiling (proof-world-reg 8 world)))
                  (proof-disjoint-p address (+ address 8) (collection-page-floor (proof-world-reg 20 world))
                                    (proof-world-reg 22 world))
                  (proof-disjoint-p address (+ address 8) (- sp 16) sp))
             (and (equal (collection-read-word address after) (collection-read-word address world))
                  (equal (collection-read-word address (collection-trace-effect first world))
                         (collection-read-word address world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-retired-round-protects-disjoint-word (headerp t))
                 (:instance collection-retired-round-protects-disjoint-word
                            (headerp nil)
                            (world (collection-trace-effect (collection-retired-release-round-trace t origin world) world)))
                 (:instance collection-first-retired-round-opens-second)
                 (:instance collection-retired-release-round-returns-and-keeps-other-endpoints (headerp t) (register 20))
                 (:instance collection-retired-release-round-returns-and-keeps-other-endpoints (headerp t) (register 22)))
           :in-theory (disable collection-retired-round-protects-disjoint-word
                               collection-first-retired-round-opens-second collection-page-ceiling collection-page-floor
                               collection-retired-release-round-returns-and-keeps-other-endpoints))))

(local
 (defthm collection-kernel-rounding-keeps-runtime-page-count
   (implies (and (natp pages) (proof-page-size-p page))
            (equal (proof-align-up (* *proof-runtime-page* pages) page)
                   (* *proof-runtime-page* pages)))
   :hints (("Goal" :in-theory (enable proof-align-up proof-page-size-p ceiling
                                     acl2::fold-consts-in-*)))))

(defthm collection-positive-runtime-page-range-admits-relinquish
  (let* ((base (* *proof-runtime-page* first))
         (bytes (* *proof-runtime-page* (- last first)))
         (regions (proof-world-regions world))
         (replies (proof-world-replies world)))
    (implies (and (natp first) (natp last) (< first last)
                  (proof-page-size-p (proof-world-page-size world))
                  (proof-covered-p base bytes :write regions)
                  (consp replies) (equal (car replies) 0))
             (collection-relinquish-p base bytes world)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-runtime-page-multiples-are-kernel-aligned
                            (index first) (page (proof-world-page-size world)))
                 (:instance collection-kernel-rounding-keeps-runtime-page-count
                            (pages (- last first)) (page (proof-world-page-size world))))
           :in-theory (e/d (collection-relinquish-p)
                            (proof-align-up proof-covered-p proof-world-page-size proof-page-size-p mod
                             collection-runtime-page-multiples-are-kernel-aligned
                             collection-kernel-rounding-keeps-runtime-page-count)))))
