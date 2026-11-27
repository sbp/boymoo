(in-package "BOYMOO-COMPILER")

(include-book "../runtime")
(include-book "../../compiler/model/a64")
(include-book "p6-clears")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defconst *p6-forward-items*
  (let ((items (member-equal '(:label "rt:forward") (runtime-memory-code))))
    (take (position-equal '(:label "rt:release-range") items) items)))

(defconst *p6-forward-labels*
  (mv-let (size labels items)
    (a64-layout *p6-forward-items* 0 nil nil)
    (declare (ignore size items))
    labels))

(defconst *p6-forward-foreign* (a64-offset "rt:forward-foreign" *p6-forward-labels*))
(defconst *p6-forward-ret* (a64-offset "rt:forward-return" *p6-forward-labels*))

(defun p6-code-bytes (text address)
  (if (atom text)
      nil
    (acons address (char-code (car text)) (p6-code-bytes (cdr text) (1+ address)))))

(defconst *p6-forward-bytes*
  (mv-let (text entry)
    (a64-assemble *p6-forward-items* "rt:forward")
    (declare (ignore entry))
    (p6-code-bytes (coerce text 'list) 0)))

; Upper bounds on the remaining steps for an immediate datum with tag 1.
(defconst *p6-forward-pcs*
  (append '((0 . 9) (4 . 8) (8 . 7) (12 . 6) (16 . 5) (20 . 4) (24 . 3) (28 . 2))
          (list (cons *p6-forward-foreign* 5)
                (cons (+ *p6-forward-foreign* 4) 4)
                (cons (+ *p6-forward-foreign* 8) 3)
                (cons (+ *p6-forward-foreign* 12) 2)
                (cons *p6-forward-ret* 1)
                '(4096 . 0))))

(defund p6-forward-rank (machine)
  (cdr (assoc-equal (boymoo-model::a64-pc machine) *p6-forward-pcs*)))

(defund p6-forward-path-p (machine)
  (let ((pc (boymoo-model::a64-pc machine)))
    (and (natp (p6-forward-rank machine))
         (equal (boymoo-model::a64-read-reg 0 64 nil machine) 1)
         (equal (boymoo-model::a64-read-reg 30 64 nil machine) 4096)
         (implies (member-equal pc (list 20 24 (+ *p6-forward-foreign* 8)))
                  (equal (boymoo-model::a64-read-reg 1 64 nil machine) 1))
         (implies (member-equal pc (list 28 (+ *p6-forward-foreign* 12)))
                  (boymoo-model::a64-condition 1 (boymoo-model::a64-nzcv machine))))))

(defund p6-forward-code-matches-p (pcs memory)
  (if (atom pcs)
      t
    (let ((pc (caar pcs)))
      (and (or (equal pc 4096)
               (equal (boymoo-model::a64-read-bytes 4 pc memory)
                      (boymoo-model::a64-read-bytes 4 pc *p6-forward-bytes*)))
           (p6-forward-code-matches-p (cdr pcs) memory)))))

(defund p6-forward-code-installed-p (memory)
  (p6-forward-code-matches-p *p6-forward-pcs* memory))

(local
 (defthmd p6-forward-code-matches-at-each-address
   (implies (and (p6-forward-code-matches-p pcs memory)
                 (assoc-equal pc pcs) (not (equal pc 4096)))
            (equal (boymoo-model::a64-read-bytes 4 pc memory)
                   (boymoo-model::a64-read-bytes 4 pc *p6-forward-bytes*)))
   :hints (("Goal" :induct (p6-forward-code-matches-p pcs memory)
            :in-theory (e/d (p6-forward-code-matches-p)
                             (boymoo-model::a64-read-bytes))))))

(local
 (defthm p6-forward-fetches-current-code
   (let ((pc (boymoo-model::a64-pc machine)))
     (implies (and (equal address pc) (p6-forward-rank machine) (not (equal pc 4096))
                   (p6-forward-code-installed-p (boymoo-model::a64-memory machine)))
              (equal (boymoo-model::a64-load 4 address machine)
                     (boymoo-model::a64-read-bytes 4 address *p6-forward-bytes*))))
   :hints (("Goal"
            :use (:instance p6-forward-code-matches-at-each-address
                            (pc (boymoo-model::a64-pc machine)) (pcs *p6-forward-pcs*)
                            (memory (boymoo-model::a64-memory machine)))
            :in-theory (e/d (p6-forward-rank p6-forward-code-installed-p)
                             (boymoo-model::a64-pc boymoo-model::a64-memory
                              boymoo-model::a64-read-bytes))
            :do-not-induct t))))

(local
 (defthm p6-a64-unsigned-is-idempotent
   (equal (boymoo-model::a64-unsigned width (boymoo-model::a64-unsigned width word))
          (boymoo-model::a64-unsigned width word))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-unsigned boymoo-model::a64-ones)
                                   (acl2::binary-logand))))))

(local
 (defthm p6-state-fields-after-updates
   (let* ((with-pc (boymoo-model::a64-set-pc value machine))
          (with-flags (boymoo-model::a64-set-nzcv value machine))
          (with-reg (boymoo-model::a64-write-reg 1 64 use-sp value machine)))
     (and (equal (boymoo-model::a64-pc with-pc) (boymoo-model::a64-unsigned 64 value))
          (equal (boymoo-model::a64-nzcv with-pc) (boymoo-model::a64-nzcv machine))
          (equal (boymoo-model::a64-memory with-pc) (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-read-reg reg 64 nil with-pc)
                 (boymoo-model::a64-read-reg reg 64 nil machine))
          (equal (boymoo-model::a64-pc with-flags) (boymoo-model::a64-pc machine))
          (equal (boymoo-model::a64-nzcv with-flags) (boymoo-model::a64-unsigned 4 value))
          (equal (boymoo-model::a64-memory with-flags) (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-read-reg reg 64 nil with-flags)
                 (boymoo-model::a64-read-reg reg 64 nil machine))
          (equal (boymoo-model::a64-pc with-reg) (boymoo-model::a64-pc machine))
          (equal (boymoo-model::a64-nzcv with-reg) (boymoo-model::a64-nzcv machine))
          (equal (boymoo-model::a64-memory with-reg) (boymoo-model::a64-memory machine))
          (equal (boymoo-model::a64-read-reg reg 64 nil with-reg)
                 (if (equal reg 1) (boymoo-model::a64-unsigned 64 value)
                   (boymoo-model::a64-read-reg reg 64 nil machine)))
          (equal (boymoo-model::a64-write-reg 31 64 nil value machine) machine)))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned put-assoc-equal)))))

(local
 (defthm p6-a64-flags-are-four-bits
   (equal (boymoo-model::a64-unsigned 4 (boymoo-model::a64-result-flags width result carry overflow))
          (boymoo-model::a64-result-flags width result carry overflow))
   :hints (("Goal" :cases ((logbitp (1- width) result) (equal result 0) carry overflow)))))

(local
 (defthm p6-general-register-read-ignores-use-sp
   (implies (and (natp reg) (< reg 31))
            (equal (boymoo-model::a64-read-reg reg 64 t machine)
                   (boymoo-model::a64-read-reg reg 64 nil machine)))))

(local
 (defthm p6-forward-exec-step-stays-on-immediate-path
   (let* ((pc (boymoo-model::a64-pc machine))
          (instruction (boymoo-model::a64-decode (boymoo-model::a64-load 4 pc machine)))
          (after (boymoo-model::a64-execute instruction machine)))
     (implies (and (p6-forward-path-p machine) (not (equal pc 4096))
                   (p6-forward-code-installed-p (boymoo-model::a64-memory machine)))
              (and (not (eq (car instruction) :svc))
                   (not (eq after :undefined))
                   (p6-forward-path-p after)
                   (<= (+ 1 (p6-forward-rank after)) (p6-forward-rank machine))
                   (equal (boymoo-model::a64-memory after) (boymoo-model::a64-memory machine)))))
   :rule-classes nil
   :hints (("Goal"
            :use (:instance p6-forward-fetches-current-code (address (boymoo-model::a64-pc machine)))
            :cases ((equal (boymoo-model::a64-pc machine) 0)
                    (equal (boymoo-model::a64-pc machine) 4)
                    (equal (boymoo-model::a64-pc machine) 8)
                    (equal (boymoo-model::a64-pc machine) 12)
                    (equal (boymoo-model::a64-pc machine) 16)
                    (equal (boymoo-model::a64-pc machine) 20)
                    (equal (boymoo-model::a64-pc machine) 24)
                    (equal (boymoo-model::a64-pc machine) 28)
                    (equal (boymoo-model::a64-pc machine) *p6-forward-foreign*)
                    (equal (boymoo-model::a64-pc machine) (+ *p6-forward-foreign* 4))
                    (equal (boymoo-model::a64-pc machine) (+ *p6-forward-foreign* 8))
                    (equal (boymoo-model::a64-pc machine) (+ *p6-forward-foreign* 12))
                    (equal (boymoo-model::a64-pc machine) *p6-forward-ret*))
            :in-theory (e/d (p6-forward-path-p p6-forward-rank)
                             ((:definition boymoo-model::a64-decode)
                              (:definition boymoo-model::a64-read-bytes)
                              (:definition boymoo-model::a64-load)
                              (:definition boymoo-model::a64-result-flags)
                              (:definition boymoo-model::a64-unsigned)
                              (:definition boymoo-model::a64-signed)
                              (:definition boymoo-model::a64-condition)
                              boymoo-model::a64-pc boymoo-model::a64-nzcv
                              boymoo-model::a64-read-reg boymoo-model::a64-memory
                              boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                              boymoo-model::a64-write-reg
                              (:definition acl2::binary-logxor)
                              (:definition acl2::binary-logand)
                              (:definition logbitp) (:definition ash)))
            :do-not-induct t))))

(local
 (defthm p6-forward-path-observations
   (implies (p6-forward-path-p machine)
            (and (natp (p6-forward-rank machine))
                 (equal (equal (p6-forward-rank machine) 0)
                        (equal (boymoo-model::a64-pc machine) 4096))
                 (equal (boymoo-model::a64-read-reg 0 64 nil machine) 1)))
   :hints (("Goal" :in-theory (e/d (p6-forward-path-p p6-forward-rank)
                                   (boymoo-model::a64-pc boymoo-model::a64-read-reg))))))

(local
 (defthmd p6-forward-run-on-immediate-path
   (let ((run (boymoo-model::a64-run fuel nil nil 4096 machine)))
     (implies (and (p6-forward-path-p machine)
                   (p6-forward-code-installed-p (boymoo-model::a64-memory machine))
                   (natp fuel) (<= (p6-forward-rank machine) fuel))
              (and (equal (mv-nth 0 run) :return)
                   (equal (boymoo-model::a64-read-reg 0 64 nil (mv-nth 1 run)) 1)
                   (equal (boymoo-model::a64-memory (mv-nth 1 run))
                          (boymoo-model::a64-memory machine)))))
   :hints (("Goal" :induct (boymoo-model::a64-run fuel nil nil 4096 machine)
            :in-theory (disable boymoo-model::a64-pc boymoo-model::a64-memory
                                boymoo-model::a64-read-reg boymoo-model::a64-execute
                                boymoo-model::a64-decode boymoo-model::a64-load))
           ("Subgoal *1/5" :use p6-forward-exec-step-stays-on-immediate-path)
           ("Subgoal *1/4" :use p6-forward-exec-step-stays-on-immediate-path)
           ("Subgoal *1/3" :use p6-forward-exec-step-stays-on-immediate-path)
           ("Subgoal *1/2" :in-theory (e/d (p6-forward-path-p p6-forward-rank)
                                           (boymoo-model::a64-pc boymoo-model::a64-read-reg))))))

(defthmd p6-collector-forwarding-preserves-word-one
  (let* ((run (boymoo-model::a64-run fuel nil nil 4096 machine))
         (after (mv-nth 1 run)))
    (implies (and (equal (boymoo-model::a64-pc machine) 0)
                  (equal (boymoo-model::a64-read-reg 0 64 nil machine) 1)
                  (equal (boymoo-model::a64-read-reg 30 64 nil machine) 4096)
                  (p6-forward-code-installed-p (boymoo-model::a64-memory machine))
                  (natp fuel) (<= 9 fuel))
             (and (equal (mv-nth 0 run) :return)
                  (equal (boymoo-model::a64-read-reg 0 64 nil after) 1)
                  (equal (boymoo-model::a64-memory after) (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :use p6-forward-run-on-immediate-path
           :in-theory (e/d (p6-forward-path-p p6-forward-rank)
                            (boymoo-model::a64-run boymoo-model::a64-pc
                             boymoo-model::a64-memory boymoo-model::a64-read-reg)))))

(defthmd p6-cleared-slot-is-inert-under-forwarding
  (let* ((clears (reverse (abi-clears stale temp nil)))
         (slots-after (boymoo-model::core-datum (p6-run-slot-code clears env slots nslots heap)))
         (cleared (qir-slot-value slot slots-after))
         (run (boymoo-model::a64-run fuel nil nil 4096 machine))
         (after (mv-nth 1 run)))
    (implies (and (member-equal slot stale)
                  (qir-dtemp-p temp) (p6-clear-slots-fit-p stale nslots)
                  (equal (boymoo-model::a64-pc machine) 0)
                  (equal (boymoo-model::a64-read-reg 0 64 nil machine)
                         (boymoo-model::core-datum cleared))
                  (equal (boymoo-model::a64-read-reg 30 64 nil machine) 4096)
                  (p6-forward-code-installed-p (boymoo-model::a64-memory machine))
                  (natp fuel) (<= 9 fuel))
             (and (equal (mv-nth 0 run) :return)
                  (equal cleared (boymoo-model::core-value 1))
                  (equal (boymoo-model::a64-read-reg 0 64 nil after) 1)
                  (equal (boymoo-model::a64-memory after) (boymoo-model::a64-memory machine)))))
  :hints (("Goal" :use (p6-emitted-clears-write-only-selected-slots
                         p6-collector-forwarding-preserves-word-one)
           :in-theory (disable boymoo-model::a64-run boymoo-model::a64-pc boymoo-model::a64-memory
                               boymoo-model::a64-read-reg abi-clears qir-slot-value reverse)
           :do-not-induct t)))

(assert-event
 (let ((machine (boymoo-model::a64-state '((0 . 1) (5 . 0) (6 . 1) (29 . 1) (30 . 4096))
                                          0 0 0 *p6-forward-bytes*)))
   (mv-let (status after)
     (boymoo-model::a64-run 9 nil nil 4096 machine)
     (and (p6-forward-code-installed-p (boymoo-model::a64-memory machine))
          (eq status :return)
          (equal (boymoo-model::a64-read-reg 0 64 nil after) 1)
          (equal (boymoo-model::a64-memory after) (boymoo-model::a64-memory machine))))))
