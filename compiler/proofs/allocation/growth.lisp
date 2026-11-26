(in-package "BOYMOO-PROOFS")

(include-book "instructions")
(include-book "execution")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defconst *allocation-grow-fits-path*
  (list (nth 1 *allocation-grow-code*) (nth 2 *allocation-grow-code*)
        (nth 13 *allocation-grow-code*)))

(defconst *allocation-grow-extend-path* (cdr *allocation-grow-code*))
(defconst *allocation-grow-stop-path* (take 6 *allocation-grow-extend-path*))

(defun allocation-growth-path (entry required before)
  (append (if (equal entry "rt:grow") (list (car *allocation-grow-code*)) nil)
          (cond ((<= required (proof-stack-limit before)) *allocation-grow-fits-path*)
                ((< (proof-stack-end before) required) *allocation-grow-stop-path*)
                (t *allocation-grow-extend-path*))))

(defun allocation-growth-clobbers (entry)
  (if (equal entry "rt:grow")
      '(8 9 10 11 12 24)
    '(9 10 11 12 24)))

(defun allocation-growth-machine-pre-p (entry required origin before)
  (and (member-equal entry '("rt:grow" "rt:ensure-stack"))
       (allocation-code-origin-p origin)
       (allocation-machine-state-p before)
       (equal (proof-world-pc before) (allocation-code-address entry origin))
       (not (proof-world-stop before))
       (equal required (proof-world-reg (if (equal entry "rt:grow") 0 8) before))
       (<= 128 (proof-heap-base before))
       (<= (proof-stack-base before) (proof-stack-limit before))
       (<= (proof-stack-limit before) (proof-stack-end before))))

(defun allocation-growth-doubling-fits-p (before)
  (< (+ (proof-stack-base before)
        (* 2 (- (proof-stack-limit before) (proof-stack-base before))))
     *allocation-word-modulus*))

(defthm allocation-growth-doubling-in-linux-range
  (implies (and (natp base) (integerp old-limit)
                (<= base old-limit) (<= old-limit (expt 2 63))
                (<= (- old-limit base) *proof-value-reservation*))
           (< (+ base (* 2 (- old-limit base))) *allocation-word-modulus*))
  :rule-classes nil)

(defthm allocation-growth-limit-in-reservation
  (implies (and (integerp required)
                (<= (proof-stack-base world) (proof-stack-limit world))
                (<= (proof-stack-limit world) (proof-stack-end world))
                (<= required (proof-stack-end world)))
           (and (<= required (proof-grow-limit required world))
                (<= (proof-stack-limit world) (proof-grow-limit required world))
                (<= (proof-grow-limit required world) (proof-stack-end world))))
  :hints (("Goal" :in-theory (disable proof-stack-base proof-stack-end proof-stack-limit))))

(local
 (defthm allocation-growth-pc-room
   (implies (allocation-growth-machine-pre-p entry required origin before)
            (< (+ 56 (proof-world-pc before)) *allocation-word-modulus*))
   :hints (("Goal" :cases ((equal entry "rt:grow"))
            :in-theory (disable proof-stack-base proof-stack-end proof-stack-limit)))
   :rule-classes nil))

(defthm allocation-growth-machine-return
  (implies (and (allocation-growth-machine-pre-p entry required origin before)
                (<= required (proof-stack-end before))
                (or (<= required (proof-stack-limit before))
                    (allocation-growth-doubling-fits-p before))
                (equal after (allocation-path-end
                              (allocation-growth-path entry required before) before)))
           (and (proof-frame-return-p (allocation-growth-clobbers entry) t before after)
                (equal (proof-stack-limit after) (proof-grow-limit required before))
                (equal (proof-world-reg 8 after) required)
                (equal (allocation-memory after) (allocation-memory before))
                (equal (proof-world-regions after) (proof-world-regions before))
                (equal (proof-world-replies after) (proof-world-replies before))
                (proof-streams-preserved-p before after)))
  :rule-classes nil
  :hints (("Goal" :cases ((equal entry "rt:grow")
                         (<= required (proof-stack-limit before)))
           :in-theory (disable allocation-growth-limit-in-reservation
                               allocation-unsigned-64-of-sum
                               allocation-unsigned-64-of-difference))))

(defthm allocation-growth-checked-return
  (let* ((path (allocation-growth-path entry required before))
         (cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-growth-machine-pre-p entry required origin before)
                  (<= required (proof-stack-end before))
                  (or (<= required (proof-stack-limit before))
                      (allocation-growth-doubling-fits-p before))
                  (allocation-path-ready-p path cuts before)
                  (equal after (allocation-path-end path before)))
             (and (proof-frame-return-p (allocation-growth-clobbers entry) t before after)
                  (equal (proof-stack-limit after) (proof-grow-limit required before))
                  (equal (proof-world-reg 8 after) required)
                  (equal (allocation-memory after) (allocation-memory before))
                  (equal (proof-world-regions after) (proof-world-regions before))
                  (equal (proof-world-replies after) (proof-world-replies before))
                  (proof-streams-preserved-p before after)
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-growth-machine-return
                        (:instance allocation-checked-cut
                         (instructions (allocation-growth-path entry required before))
                         (world before) (cuts (list (proof-world-reg 30 before)))))
           :in-theory (disable allocation-checked-cut allocation-growth-path
                               allocation-growth-machine-pre-p allocation-path-end
                               allocation-path-ready-p proof-segment-p proof-grow-limit
                               allocation-growth-doubling-fits-p))))

(defthm allocation-growth-machine-stop
  (implies (and (allocation-growth-machine-pre-p entry required origin before)
                (< (proof-stack-end before) required)
                (equal after (allocation-path-end
                              (allocation-growth-path entry required before) before)))
           (and (not (proof-world-stop after))
                (equal (proof-world-pc after)
                       (allocation-code-address
                        (proof-resource-label :value-stack) origin))
                (proof-resource-bound-p :value-stack required before)))
  :rule-classes nil
  :hints (("Goal" :cases ((equal entry "rt:grow"))
           :use allocation-growth-pc-room
           :in-theory (disable allocation-unsigned-64-of-sum
                               allocation-unsigned-64-of-difference))))

(defthm allocation-growth-checked-stop
  (let* ((path (allocation-growth-path entry required before))
         (stop (allocation-code-address (proof-resource-label :value-stack) origin))
         (cuts (list stop)))
    (implies (and (allocation-growth-machine-pre-p entry required origin before)
                  (< (proof-stack-end before) required)
                  (allocation-path-ready-p path cuts before)
                  (equal after (allocation-path-end path before)))
             (and (proof-resource-bound-p :value-stack required before)
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-growth-machine-stop
                        (:instance allocation-checked-cut
                         (instructions (allocation-growth-path entry required before))
                         (world before)
                         (cuts (list (allocation-code-address
                                      (proof-resource-label :value-stack) origin)))))
           :in-theory (disable allocation-checked-cut allocation-growth-path
                               allocation-growth-machine-pre-p allocation-path-end
                               allocation-path-ready-p allocation-code-address
                               proof-segment-p proof-resource-bound-p))))
