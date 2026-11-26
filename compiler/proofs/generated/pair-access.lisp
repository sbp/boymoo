(in-package "BOYMOO-PROOFS")

(include-book "list-views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-step proof-segment-p proof-instruction-effect proof-world-pc
                    proof-world-reg proof-world-machine proof-world-stop proof-reg-value-p
                    proof-word-tag proof-value-p proof-view generated-load-word expt))

(defun generated-pair-access-items (cdr-p serial)
  (let ((done (boymoo-compiler::gen-local serial)))
    (list '(:movz 9 34 0) '(:tst-mask 0 3) (list :b-cond :ne done)
          (list :add 0 0 (if cdr-p 8 0)) '(:ldr-reg 9 28 0)
          (list :label done) '(:mov 0 9))))

(defthm generated-pair-access-emission
  (equal (mv-nth 0 (boymoo-compiler::gen-routine
                    (if cdr-p "COMMON-LISP::CDR" "COMMON-LISP::CAR") label serial code))
         (boymoo-compiler::reverse-onto (generated-pair-access-items cdr-p serial) code))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-routine))))

(defun generated-pair-access-path (cdr-p before)
  (append '((:move-wide 2 64 9 34 0) (:logical-imm 3 64 31 0 7) (:branch-cond 12 1))
          (if (equal (proof-word-tag (proof-world-reg 0 before)) 0)
              (list (list :arithmetic-imm 0 64 0 0 (if cdr-p 8 0))
                    '(:single 1 8 28 9 :register 0 3 0))
            nil)
          '((:logical-reg 1 64 0 31 9 0 0 nil))))

(defthm generated-pair-access-checked-path
  (let* ((pc (proof-world-pc before))
         (base (proof-heap-base before))
         (word (proof-world-reg 0 before))
         (offset (if cdr-p 8 0))
         (path (generated-pair-access-path cdr-p before))
         (after (generated-path-after path before)))
    (implies (and (< (+ pc 24) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before))
                  (proof-value-p word input base objects packages (proof-world-machine before))
                  (proof-value-p *proof-nil* nil base objects packages (proof-world-machine before))
                  (implies (consp input) (< (+ base word offset) (expt 2 64)))
                  (generated-path-p path (list (+ pc 24)) before))
             (and (proof-segment-p (if (consp input) 6 4) (list (+ pc 24)) before :cut after)
                  (proof-reg-value-p 0 (if cdr-p (cdr input) (car input)) after objects packages)
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use ((:instance generated-placed-path-to-cut
                            (instructions (generated-pair-access-path cdr-p before))
                            (cuts (list (+ 24 (proof-world-pc before)))))
                 (:instance generated-cons-word-points-to-two-datums
                            (word (proof-world-reg 0 before)) (value input)
                            (base (proof-heap-base before)) (machine (proof-world-machine before)))
                 (:instance generated-cons-tag-in-value-view
                            (word (proof-world-reg 0 before)) (value input)
                            (base (proof-heap-base before)) (machine (proof-world-machine before)))
                 (:instance generated-word-load-bounds (world before)
                            (address (+ (proof-heap-base before) (proof-world-reg 0 before))))
                 (:instance generated-word-load-bounds (world before)
                            (address (+ 8 (proof-heap-base before) (proof-world-reg 0 before)))))
           :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-value-p proof-pointer-address
                           proof-heap-base generated-load-word)
                          (generated-path-p generated-cons-tag-in-value-view
                           generated-word-load-bounds)))))

(defconst *generated-equal-identical-path*
  '((:arithmetic-reg 3 64 31 0 1 0 0) (:branch-cond 48 0)
    (:move-wide 2 64 0 58 0) (:branch 8 nil)))

(defthm generated-identical-word-equality-fast-path
  (let* ((pc (proof-world-pc before))
         (after (generated-path-after *generated-equal-identical-path* before)))
    (implies (and (< (+ pc 64) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-reg 0 before) (proof-world-reg 1 before))
                  (proof-value-p (proof-world-reg 0 before) left (proof-heap-base before)
                                 objects packages (proof-world-machine before))
                  (proof-value-p (proof-world-reg 1 before) right (proof-heap-base before)
                                 objects packages (proof-world-machine before))
                  (generated-path-p *generated-equal-identical-path* (list (+ pc 64)) before))
             (and (proof-segment-p 4 (list (+ pc 64)) before :cut after)
                  (equal left right)
                  (equal (proof-world-reg 0 after) *proof-t*)
                  (generated-heap-world-equiv after before))))
  :hints (("Goal" :use (:instance generated-placed-path-to-cut
                                  (instructions *generated-equal-identical-path*)
                                  (cuts (list (+ 64 (proof-world-pc before)))))
                  :in-theory (e/d (proof-value-p) (generated-path-p))))
  :rule-classes nil)
