(in-package "BOYMOO-PROOFS")

(include-book "stack-invariant")
(include-book "view-calls")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-caller-stack-room-p (before)
  (let ((sp (boymoo-model::a64-sp (proof-world-machine before))))
    (and (< 0 (- sp 16))
         (<= (sequence-machine-stack-base before) (- sp 16)))))

(defun sequence-caller-save-memory (before)
  (let* ((machine (proof-world-machine before))
         (sp (boymoo-model::a64-sp machine)))
    (boymoo-model::a64-write-bytes
     8 (- sp 8) (proof-world-reg 30 before)
     (boymoo-model::a64-write-bytes
      8 (- sp 16) (proof-world-reg 29 before) (boymoo-model::a64-memory machine)))))

(defthm sequence-frame-keeps-heap-registers
  (implies (and (proof-register-frame-p 28 clobbers before after)
                (not (intersectp-equal '(23 24 25 26 27 28) clobbers)))
           (sequence-heap-registers-agree-p before after))
  :hints
  (("Goal"
    :in-theory (enable sequence-heap-registers-agree-p
                       proof-machine-limit proof-stack-limit proof-stack-top
                       proof-heap-limit proof-box-top proof-heap-base)
    :use ((:instance sequence-register-in-frame (limit 28) (register 23))
          (:instance sequence-register-in-frame (limit 28) (register 24))
          (:instance sequence-register-in-frame (limit 28) (register 25))
          (:instance sequence-register-in-frame (limit 28) (register 26))
          (:instance sequence-register-in-frame (limit 28) (register 27))
          (:instance sequence-register-in-frame (limit 28) (register 28)))))
  :rule-classes nil)

(defthm sequence-frame-restored-registers
  (implies (and (proof-register-frame-p 28 clobbers before after)
                (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
                (equal (proof-world-reg 30 after) (proof-world-reg 30 before)))
           (proof-register-frame-p 30 clobbers before after))
  :hints (("Goal"
           :in-theory (disable proof-register-frame-p)
           :expand ((proof-register-frame-p 30 clobbers before after)
                    (proof-register-frame-p 29 clobbers before after)))))

(local
 (defthm sequence-caller-frame-range
   (let* ((first (proof-world-machine before))
          (sp (boymoo-model::a64-sp first))
          (floor (sequence-machine-stack-base before))
          (ceil (sequence-machine-stack-end before)))
     (implies (and (proof-heap-layout-p before) (sequence-caller-stack-room-p before))
              (and (posp (- sp 16))
                   (proof-subspan-p (- sp 16) 16 floor ceil)
                   (proof-subspan-p (- sp 16) 0 floor ceil)
                   (proof-subspan-p sp 0 floor ceil)
                   (equal (mod sp 16) 0)
                   (equal (mod (- sp 16) 16) 0))))
   :hints
   (("Goal"
     :expand ((proof-heap-layout-p before))
     :in-theory (e/d (sequence-machine-stack-base sequence-machine-stack-end)
                     (proof-align-up proof-disjoint-p proof-page-size-p))
     :use ((:instance sequence-heap-layout-bounds (world before))
           (:instance sequence-mod-add-multiple (divisor 16) (multiple -1)
                      (value (boymoo-model::a64-sp (proof-world-machine before)))))))
   :rule-classes nil))

(defthm sequence-stack-write-from-caller-saves
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (sp (boymoo-model::a64-sp first))
         (scratch (- sp 16)))
    (implies (and (proof-heap-layout-p before)
                  (sequence-caller-stack-room-p before)
                  (sequence-heap-registers-agree-p before after)
                  (equal (cdr before) (cdr after))
                  (or (equal (boymoo-model::a64-sp last) sp)
                      (equal (boymoo-model::a64-sp last) scratch))
                  (equal (boymoo-model::a64-memory last) (sequence-caller-save-memory before)))
             (sequence-stack-write-p scratch sp before after)))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p)
                    (proof-subspan-p proof-heap-layout-p sequence-caller-stack-room-p))
    :use (sequence-caller-frame-range
          (:instance sequence-save-pair-confines-memory-write
                     (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (saved (proof-world-reg 29 before)) (link (proof-world-reg 30 before))))))
  :rule-classes nil)

(defthm sequence-caller-saves-readback
  (let* ((first (proof-world-machine before))
         (scratch (- (boymoo-model::a64-sp first) 16)))
    (implies (and (sequence-caller-stack-room-p before)
                  (equal (boymoo-model::a64-memory machine) (sequence-caller-save-memory before)))
             (and (equal (proof-load-word scratch machine) (proof-world-reg 29 before))
                  (equal (proof-load-word (+ scratch 8) machine) (proof-world-reg 30 before)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-load-word proof-world-reg proof-disjoint-p)
                    (sequence-read-outside-write))
    :use ((:instance sequence-read-outside-write
                     (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                     (start (- (boymoo-model::a64-sp (proof-world-machine before)) 8))
                     (size 8) (count 8)
                     (value (proof-world-reg 30 before))
                     (memory (boymoo-model::a64-write-bytes
                              8 (- (boymoo-model::a64-sp (proof-world-machine before)) 16)
                              (proof-world-reg 29 before)
                              (boymoo-model::a64-memory (proof-world-machine before))))))))
  :rule-classes nil)

(defun sequence-readonly-clobbers (routine)
  (if (eq routine 'char) '(0 1 2 3 4 5) '(0 1 2 3)))

(defun sequence-readonly-view-entry (routine before)
  (sequence-execute (sequence-view-call-path routine) before))

(defun sequence-readonly-view-path (routine before)
  (let ((called (sequence-readonly-view-entry routine before)))
    (sequence-string-view-path (proof-world-reg 0 called) (proof-heap-base called)
                               (proof-world-machine called))))

(defun sequence-readonly-view-return (routine before)
  (sequence-execute (sequence-readonly-view-path routine before)
                    (sequence-readonly-view-entry routine before)))

(defun sequence-readonly-view-link (routine image-base)
  (+ image-base (sequence-view-caller-offset routine)
     (* 4 (len (sequence-view-call-path routine)))))

(defun sequence-readonly-view-checked-p (routine before image-base)
  (let ((link (sequence-readonly-view-link routine image-base))
        (called (sequence-readonly-view-entry routine before)))
    (and (member-eq routine '(length char coerce))
         (consp (boymoo-model::a64-registers (proof-world-machine before)))
         (sequence-caller-stack-room-p before)
         (natp image-base)
         (equal (proof-world-pc before) (+ image-base (sequence-view-caller-offset routine)))
         (unsigned-byte-p 64 link)
         (sequence-instruction-path (sequence-readonly-view-path routine before)
                                    (list link) called))))

(local
 (defthm sequence-readonly-view-entry-frame
   (let* ((called (sequence-readonly-view-entry routine before))
          (sp (boymoo-model::a64-sp (proof-world-machine before))))
     (implies (and (sequence-readonly-view-checked-p routine before image-base)
                   (proof-heap-p before objects packages))
              (and (sequence-stack-write-p (- sp 16) sp before called)
                   (equal (proof-world-reg 0 called) (proof-world-reg 0 before))
                   (implies (eq routine 'char)
                            (equal (proof-world-reg 5 called) (proof-world-reg 1 before)))
                   (equal (proof-world-reg 30 called) (sequence-readonly-view-link routine image-base))
                   (equal (boymoo-model::a64-sp (proof-world-machine called)) (- sp 16))
                   (equal (boymoo-model::a64-memory (proof-world-machine called))
                          (sequence-caller-save-memory before))
                   (proof-register-frame-p 28 (sequence-readonly-clobbers routine) before called)
                   (not (proof-world-stop called))
                   (consp (boymoo-model::a64-registers (proof-world-machine called)))
                   (equal (cdr called) (cdr before))
                   (equal (proof-heap-base called) (proof-heap-base before)))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-heap-registers-agree-p)
                     (sequence-readonly-view-path sequence-string-view-path
                      proof-world-stop proof-reg-value-p proof-register-frame-p))
     :use (sequence-view-call-effects
           (:instance sequence-heap-layout-bounds (world before))
           (:instance sequence-frame-keeps-heap-registers
                      (clobbers (sequence-readonly-clobbers routine))
                      (after (sequence-readonly-view-entry routine before)))
           (:instance sequence-stack-write-from-caller-saves
                      (after (sequence-readonly-view-entry routine before))))))
   :rule-classes nil))

(defthm sequence-readonly-view-return-is-ready
  (let* ((returned (sequence-readonly-view-return routine before))
         (first (proof-world-machine before))
         (last (proof-world-machine returned))
         (sp (boymoo-model::a64-sp first))
         (word (proof-world-reg 0 before))
         (address (proof-pointer-address word (proof-heap-base before)))
         (clobbers (sequence-readonly-clobbers routine)))
    (implies (and (sequence-readonly-view-checked-p routine before image-base)
                  (proof-heap-p before objects packages)
                  (proof-reg-value-p 0 datum before objects packages)
                  (implies (stringp datum) (unsigned-byte-p 64 (+ address 8))))
             (and (sequence-stack-write-p (- sp 16) sp before returned)
                  (not (proof-world-stop returned))
                  (equal (proof-world-pc returned) (sequence-readonly-view-link routine image-base))
                  (equal (proof-world-reg 0 returned) word)
                  (implies (eq routine 'char)
                           (equal (proof-world-reg 5 returned) (proof-world-reg 1 before)))
                  (equal (proof-world-reg 1 returned) (if (stringp datum) (+ address 8) 0))
                  (equal (proof-world-reg 2 returned) (if (stringp datum) (len (coerce datum 'list)) 0))
                  (proof-register-frame-p 28 clobbers before returned)
                  (equal (proof-heap-base returned) (proof-heap-base before))
                  (equal (boymoo-model::a64-sp last) (- sp 16))
                  (equal (boymoo-model::a64-memory last) (sequence-caller-save-memory before))
                  (equal (proof-load-word (- sp 16) last) (proof-world-reg 29 before))
                  (equal (proof-load-word (- sp 8) last) (proof-world-reg 30 before))
                  (consp (boymoo-model::a64-registers last))
                  (equal (cdr returned) (cdr before)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-value-p proof-machine-value-p proof-reg-value-p proof-frame-return-p
                     sequence-heap-registers-agree-p)
                    (sequence-caller-save-memory proof-view proof-register-frame-p
                     proof-load-word proof-pointer-address
                     proof-world-stop proof-world-replies proof-world-regions
                     sequence-string-view-path sequence-caller-stack-room-p
                     proof-segment-p proof-heap-layout-p))
    :use (sequence-readonly-view-entry-frame
          (:instance sequence-confined-stack-write-preserves-value
                     (word (proof-world-reg 0 before))
                     (after (sequence-readonly-view-entry routine before))
                     (start (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                     (end (boymoo-model::a64-sp (proof-world-machine before))))
          (:instance sequence-string-view-field-contract
                     (before (sequence-readonly-view-entry routine before)))
          (:instance sequence-register-in-frame
                     (limit 30) (clobbers '(1 2 3)) (register 0)
                     (before (sequence-readonly-view-entry routine before))
                     (after (sequence-readonly-view-return routine before)))
          (:instance sequence-register-in-frame
                     (limit 30) (clobbers '(1 2 3)) (register 5)
                     (before (sequence-readonly-view-entry routine before))
                     (after (sequence-readonly-view-return routine before)))
          (:instance sequence-register-frame-on-prefix
                     (limit 30) (prefix 28) (clobbers '(1 2 3))
                     (before (sequence-readonly-view-entry routine before))
                     (after (sequence-readonly-view-return routine before)))
          (:instance sequence-register-frame-with-more-clobbers
                     (limit 28) (old '(1 2 3)) (new (sequence-readonly-clobbers routine))
                     (before (sequence-readonly-view-entry routine before))
                     (after (sequence-readonly-view-return routine before)))
          (:instance sequence-register-frame-transitive
                     (limit 28) (clobbers (sequence-readonly-clobbers routine))
                     (middle (sequence-readonly-view-entry routine before))
                     (after (sequence-readonly-view-return routine before)))
          (:instance sequence-frame-keeps-heap-registers
                     (clobbers (sequence-readonly-clobbers routine))
                     (after (sequence-readonly-view-return routine before)))
          (:instance sequence-stack-write-from-caller-saves
                     (after (sequence-readonly-view-return routine before)))
          (:instance sequence-caller-saves-readback
                     (machine (proof-world-machine (sequence-readonly-view-return routine before)))))))
  :rule-classes nil)
