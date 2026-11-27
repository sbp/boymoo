(in-package "BOYMOO-PROOFS")

(include-book "root-transfer")
(include-book "routines")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-instruction-effect proof-segment-p proof-value-p proof-view proof-stack-views
                    proof-reg-value-p proof-machine-value-p proof-register-arguments-p
                    generated-read-words generated-load-word generated-path-p
                    generated-wide-word-items generated-move-instructions
                    boymoo-compiler::gen-frame-word boymoo-compiler::gen-argument-registers
                    boymoo-model::a64-unsigned expt))

(defun generated-frame-load-items (register slot)
  (let ((bytes (* 8 slot)))
    (if (< bytes 32768)
        (list (list :ldr register 19 bytes))
      (append (generated-wide-word-items 17 bytes) (list (list :ldr-reg register 19 17))))))

(defthm generated-frame-load-emission
  (equal (boymoo-compiler::gen-frame-word register slot code)
         (boymoo-compiler::reverse-onto (generated-frame-load-items register slot) code))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-frame-word))))

(defun generated-argument-register-items (count slot register)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (append (generated-frame-load-items register slot)
            (generated-argument-register-items (1- count) (1+ slot) (1+ register)))))

(defthm generated-argument-register-emission
  (equal (boymoo-compiler::gen-argument-registers count slot register code)
         (boymoo-compiler::reverse-onto (generated-argument-register-items count slot register) code))
  :hints (("Goal" :induct (boymoo-compiler::gen-argument-registers count slot register code)
                  :in-theory (e/d (boymoo-compiler::gen-argument-registers)
                                  (generated-frame-load-items)))))

(defun generated-frame-load-path (register slot)
  (let ((bytes (* 8 slot)))
    (if (< bytes 32768)
        (list (list :single 1 8 19 register :offset bytes))
      (append (generated-move-instructions (generated-wide-word-items 17 bytes))
              (list (list :single 1 8 19 register :register 17 3 0))))))

(local
 (defthm generated-register-load-append-length
   (equal (len (append first second)) (+ (len first) (len second)))))

(defthm generated-frame-load-observations
  (let* ((path (generated-frame-load-path register slot))
         (after (generated-path-after path before))
         (pc (+ (proof-world-pc before) (* 4 (len path))))
         (value (generated-load-word (+ (proof-world-reg 19 before) (* 8 slot)) before)))
    (implies (and (natp register) (< register 17) (natp slot) (unsigned-byte-p 64 (* 8 slot)))
             (and (equal (proof-world-reg register after) value)
                  (implies (and (not (equal other register)) (not (equal other 17)))
                           (equal (proof-world-reg other after) (proof-world-reg other before)))
                  (implies (< pc (expt 2 64)) (equal (proof-world-pc after) pc))
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use ((:instance generated-wide-word-loads-value (rd 17) (word (* 8 slot)))
                 (:instance generated-word-load-bounds
                            (address (+ (proof-world-reg 19 before) (* 8 slot))) (world before)))
           :in-theory (e/d (generated-path-after) (generated-word-load-bounds))))
  :rule-classes nil)

(defun generated-argument-register-path (count slot register)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (append (generated-frame-load-path register slot)
            (generated-argument-register-path (1- count) (1+ slot) (1+ register)))))

(defun generated-register-words (count register world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (proof-world-reg register world) (generated-register-words (1- count) (1+ register) world))))

(local
 (defun generated-argument-register-induction (count slot register before)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       before
     (generated-argument-register-induction
      (1- count) (1+ slot) (1+ register)
      (generated-path-after (generated-frame-load-path register slot) before)))))

(defthm generated-argument-register-path-preserves-fields
  (let ((after (generated-path-after (generated-argument-register-path count slot register) before)))
    (implies (and (natp count) (natp register) (<= (+ count register) 17) (natp slot)
                  (< (* 8 (+ slot count)) (expt 2 64)))
             (and (generated-heap-world-equiv after before)
                  (implies (and (not (equal other 17))
                                (or (< other register) (<= (+ register count) other)))
                           (equal (proof-world-reg other after) (proof-world-reg other before))))))
  :hints (("Goal" :induct (generated-argument-register-induction count slot register before)
                  :in-theory (e/d (generated-path-after) (generated-frame-load-path)))
          ("Subgoal *1/2" :use generated-frame-load-observations)))

(defthm generated-argument-register-path-reads-words
  (let* ((path (generated-argument-register-path count slot register))
         (after (generated-path-after path before))
         (pc (+ (proof-world-pc before) (* 4 (len path)))))
    (implies (and (natp count) (natp register) (<= (+ count register) 17) (natp slot)
                  (< (* 8 (+ slot count)) (expt 2 64)) (< pc (expt 2 64)))
             (and (equal (proof-world-pc after) pc)
                  (equal (generated-register-words count register after)
                         (generated-read-words count (+ (proof-world-reg 19 before) (* 8 slot)) before)))))
  :hints (("Goal" :induct (generated-argument-register-induction count slot register before)
                  :in-theory (e/d (generated-read-words generated-path-after)
                                  (generated-frame-load-path)))
          ("Subgoal *1/2" :use ((:instance generated-frame-load-observations (other 19))
                               (:instance generated-argument-register-path-preserves-fields
                                          (count (1- count)) (slot (1+ slot)) (register (1+ register))
                                          (before (generated-path-after (generated-frame-load-path register slot)
                                                                       before))
                                          (other register)))))
  :rule-classes nil)

(local
 (defthm generated-register-view-has-slot-prefix
   (let ((view (generated-word-views words base objects packages machine)))
     (implies view (equal (cons :slots (cdr view)) view)))
   :hints (("Goal" :expand (generated-word-views words base objects packages machine)))))

(defthm generated-register-arguments-have-operand-views
  (implies (true-listp args)
           (equal (proof-register-arguments-p args register world objects packages)
                  (equal (generated-word-views (generated-register-words (len args) register world)
                                               (proof-heap-base world) objects packages
                                               (proof-world-machine world))
                         (cons :slots (proof-argument-views args)))))
  :hints (("Goal" :induct (proof-register-arguments-p args register world objects packages)
                  :in-theory (enable proof-register-arguments-p proof-reg-value-p
                                     proof-machine-value-p proof-value-p proof-argument-views))
          ("Subgoal *1/2"
           :use (:instance generated-register-view-has-slot-prefix
                           (words (generated-register-words (len (cdr args)) (1+ register) world))
                           (base (proof-heap-base world)) (machine (proof-world-machine world))))))

(defthm generated-argument-registers-load-views
  (let* ((count (len args))
         (path (generated-argument-register-path count slot register))
         (after (generated-path-after path before))
         (end (+ (proof-world-pc before) (* 4 (len path))))
         (address (+ (proof-world-reg 19 before) (* 8 slot))))
    (implies (and (true-listp args) (natp register) (<= (+ count register) 17) (natp slot)
                  (< (* 8 (+ slot count)) (expt 2 64)) (< end (expt 2 64))
                  (not (proof-world-stop before)) (generated-path-p path (list end) before)
                  (equal (proof-stack-views count address (proof-heap-base before) objects packages
                                            (proof-world-machine before))
                         (cons :slots (proof-argument-views args))))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (equal (proof-world-pc after) end)
                  (proof-register-arguments-p args register after objects packages)
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use ((:instance generated-argument-register-path-reads-words (count (len args)))
                 (:instance generated-argument-register-path-preserves-fields
                            (count (len args)) (other 19))
                 (:instance generated-placed-path-to-cut
                            (instructions (generated-argument-register-path (len args) slot register))
                            (cuts (list (+ (proof-world-pc before)
                                           (* 4 (len (generated-argument-register-path (len args) slot register))))))))
           :in-theory (disable generated-argument-register-path generated-register-words
                               generated-word-views generated-argument-register-path-preserves-fields)))
  :rule-classes nil)
