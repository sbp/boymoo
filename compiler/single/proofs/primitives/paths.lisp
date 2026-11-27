(in-package "BOYMOO-PROOFS")

(include-book "byte-views")

(logic)
(set-verify-guards-eagerness 0)

; A site pairs a byte offset from the runtime's first instruction with
; the decoded instruction at that offset. These fragments contain only
; instructions that assemble to one word and whose branches stay in
; the runtime.
(defconst *p6-runtime-layout*
  (mv-let (end labels reversed)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reversed))
    labels))

(defun p6-runtime-offset (label)
  (boymoo-compiler::a64-offset label *p6-runtime-layout*))

(defun p6-runtime-items-from (label items)
  (cond ((atom items) nil)
        ((equal (car items) (list :label label)) (cdr items))
        (t (p6-runtime-items-from label (cdr items)))))

(defun p6-runtime-sites (items pc count)
  (declare (xargs :measure (acl2-count items)))
  (if (or (atom items) (zp count))
      nil
    (let* ((item (car items))
           (size (boymoo-compiler::a64-size item)))
      (cond ((eq (car item) :label) (p6-runtime-sites (cdr items) pc count))
            ((equal size 4)
             (cons (cons pc (proof-decode (boymoo-compiler::a64-word
                                          item pc *p6-runtime-layout*)))
                   (p6-runtime-sites (cdr items) (+ pc 4) (1- count))))
            (t nil)))))

(defun p6-sites (label count)
  (p6-runtime-sites (p6-runtime-items-from label (boymoo-compiler::runtime-code))
                    (p6-runtime-offset label) count))

(in-theory (disable proof-step proof-instruction-effect proof-instruction-at-p
                    proof-instruction-access-p proof-run proof-label-address
                    proof-decode proof-decode-at proof-execute proof-covered-p
                    proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                    proof-world-regions boymoo-model::a64-memory))

(defun p6-sites-placed-p (sites base world)
  (if (atom sites)
      t
    (and (proof-instruction-at-p (cdar sites) (+ base (caar sites)) world)
         (p6-sites-placed-p (cdr sites) base world))))

(defund p6-same-mapped-memory-p (first second)
  (and (equal (proof-world-regions first) (proof-world-regions second))
       (equal (boymoo-model::a64-memory (proof-world-machine first))
              (boymoo-model::a64-memory (proof-world-machine second)))))

(local
 (defthm p6-placement-depends-on-mapped-memory
   (implies (p6-same-mapped-memory-p first second)
            (equal (proof-instruction-at-p instruction address first)
                   (proof-instruction-at-p instruction address second)))
   :hints (("Goal" :in-theory (enable p6-same-mapped-memory-p proof-instruction-at-p
                                    proof-decode-at boymoo-model::a64-load)))))

(defthm p6-sites-depend-on-mapped-memory
  (implies (p6-same-mapped-memory-p first second)
           (equal (p6-sites-placed-p sites base first)
                  (p6-sites-placed-p sites base second)))
  :rule-classes nil
  :hints (("Goal" :induct (p6-sites-placed-p sites base first))))

(defthm p6-run-step
  (implies (and (natp count) (not (proof-world-stop world))
                (not (member-equal (proof-world-pc world) cuts)))
           (equal (proof-run (1+ count) cuts world)
                  (proof-run count cuts (proof-step world))))
  :hints (("Goal" :expand ((proof-run (1+ count) cuts world)))))

(defthm p6-run-zero
  (equal (proof-run 0 cuts world)
         (mv (or (proof-world-stop world)
                 (if (member-equal (proof-world-pc world) cuts) :cut :limit))
             world))
  :hints (("Goal" :expand ((proof-run 0 cuts world)))))

(defun p6-path-end (sites world)
  (if (atom sites)
      world
    (p6-path-end (cdr sites) (proof-instruction-effect (cdar sites) world))))

(defun p6-read-only-path-p (sites base cuts world)
  (if (atom sites)
      t
    (let ((next (proof-instruction-effect (cdar sites) world)))
      (and (not (proof-world-stop world))
           (equal (proof-world-pc world) (+ base (caar sites)))
           (not (member-equal (proof-world-pc world) cuts))
           (proof-instruction-access-p (cdar sites) world)
           (p6-same-mapped-memory-p world next)
           (p6-read-only-path-p (cdr sites) base cuts next)))))

(defthm p6-read-only-path-runs
  (implies (and (p6-sites-placed-p sites base world)
                (p6-read-only-path-p sites base cuts world))
           (equal (proof-run (len sites) cuts world)
                  (proof-run 0 cuts (p6-path-end sites world))))
  :rule-classes nil
  :hints (("Goal" :induct (p6-read-only-path-p sites base cuts world)
                  :in-theory (disable p6-placement-depends-on-mapped-memory p6-run-zero))
          ("Subgoal *1/2"
           :use ((:instance p6-sites-depend-on-mapped-memory
                            (sites (cdr sites)) (first world)
                            (second (proof-instruction-effect (cdar sites) world)))))
          ("Subgoal *1/1" :expand ((len sites)))))

(defthm p6-read-only-path-to-cut
  (implies (and (p6-sites-placed-p sites base world)
                (p6-read-only-path-p sites base cuts world)
                (not (proof-world-stop (p6-path-end sites world)))
                (member-equal (proof-world-pc (p6-path-end sites world)) cuts))
           (proof-segment-p (len sites) cuts world :cut (p6-path-end sites world)))
  :rule-classes nil
  :hints (("Goal" :use p6-read-only-path-runs
                  :expand ((proof-run 0 cuts (p6-path-end sites world))))))
