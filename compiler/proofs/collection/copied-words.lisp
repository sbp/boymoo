(in-package "BOYMOO-PROOFS")

(include-book "memory")
(include-book "copy-loop")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-world-machine proof-load-word
                     collection-cpu-p collection-write-register collection-write-pc
                     collection-read-word collection-write-word collection-write-flags
                     collection-subtract-flags boymoo-model::a64-unsigned
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes)))

(defthm collection-external-string-keeps-word-and-acquires-mark
  (let* ((mark (- (proof-world-reg 2 world) 8))
         (next (collection-mark-string-effect world)))
    (implies (and (collection-cpu-p world)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-span-p mark 8))
             (and (equal (collection-read-word mark next) 1)
                  (equal (proof-world-reg 0 next) (proof-world-reg 0 world))
                  (equal (proof-world-reg 20 next) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 next) (proof-world-reg 21 world))
                  (equal (proof-world-pc next) (proof-world-reg 30 world))))))

(defthm collection-cons-copy-publishes-marker-and-both-fields
  (let* ((source (proof-world-reg 2 world))
         (destination (- (proof-world-reg 21 world) 16))
         (word (boymoo-model::a64-unsigned 64 (- destination (proof-world-reg 28 world))))
         (next (collection-copy-cons-effect world)))
    (implies (and (collection-cpu-p world)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-span-p source 16) (proof-span-p destination 16)
                  (proof-disjoint-p source (+ source 16) destination (+ destination 16)))
             (and (equal (collection-read-word source next) 6)
                  (equal (collection-read-word (+ source 8) next) word)
                  (equal (collection-read-word destination next) (proof-world-reg 3 world))
                  (equal (collection-read-word (+ destination 8) next) (proof-world-reg 4 world))
                  (equal (proof-world-reg 0 next) word)
                  (equal (proof-world-reg 20 next) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 next) destination)
                  (equal (proof-world-pc next) (proof-world-reg 30 world))))))

(defthm collection-payload-iteration-copies-word
  (let ((destination (proof-world-reg 20 world))
        (source (proof-world-reg 2 world)))
    (implies (and (collection-cpu-p world)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-span-p destination 8))
             (equal (collection-read-word destination (collection-copy-word-effect world))
                    (collection-read-word source world)))))

(defthm collection-payload-iteration-frame
  (let* ((from (proof-world-reg 2 world))
         (to (proof-world-reg 20 world))
         (next (collection-copy-word-effect world)))
    (implies (and (collection-cpu-p world)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (unsigned-byte-p 64 (+ from 8)) (unsigned-byte-p 64 (+ to 8)))
             (and (equal (proof-world-reg 2 next) (+ from 8))
                  (equal (proof-world-reg 20 next) (+ to 8))
                  (collection-cpu-p next)
                  (alistp (boymoo-model::a64-memory (proof-world-machine next)))))))

(defthm collection-payload-iteration-preserves-disjoint-word
  (let ((destination (proof-world-reg 20 world)))
    (implies (and (collection-cpu-p world)
                  (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                  (proof-span-p address 8) (proof-span-p destination 8)
                  (proof-disjoint-p address (+ address 8) destination (+ destination 8)))
             (equal (collection-read-word address (collection-copy-word-effect world))
                    (collection-read-word address world)))))

(defun collection-payload-span-p (count world)
  (and (collection-cpu-p world)
       (alistp (boymoo-model::a64-memory (proof-world-machine world)))
       (equal count (proof-world-reg 3 world))
       (unsigned-byte-p 64 (+ (proof-world-reg 2 world) (* 8 count)))
       (unsigned-byte-p 64 (+ (proof-world-reg 20 world) (* 8 count)))))

(defthm collection-payload-iteration-preserves-span
  (implies (and (collection-payload-span-p count world) (posp count))
           (collection-payload-span-p (1- count) (collection-copy-word-effect world)))
  :hints (("Goal" :in-theory (disable collection-copy-word-effect))))

(local (in-theory (disable collection-copy-word-effect)))

(defthm collection-payload-preserves-disjoint-word
  (let ((destination (proof-world-reg 20 world)))
    (implies (and (collection-payload-span-p count world) (proof-span-p address 8)
                  (proof-disjoint-p address (+ address 8)
                                    destination (+ destination (* 8 count))))
             (equal (collection-read-word address (collection-copy-payload-effect count world))
                    (collection-read-word address world))))
  :hints (("Goal" :induct (collection-copy-payload-effect count world))))

(local
 (defun collection-payload-word-induction (index count world)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (list index world)
     (collection-payload-word-induction (1- index) (1- count)
                                         (collection-copy-word-effect world)))))

(local
 (defthm collection-payload-first-word
   (implies (and (collection-payload-span-p count world) (posp count))
            (equal (collection-read-word (proof-world-reg 20 world)
                                          (collection-copy-payload-effect count world))
                   (collection-read-word (proof-world-reg 2 world) world)))
   :hints (("Goal"
            :expand ((collection-copy-payload-effect count world))
            :use ((:instance collection-payload-preserves-disjoint-word
                             (address (proof-world-reg 20 world))
                             (count (1- count))
                             (world (collection-copy-word-effect world))))))))

(defthm collection-payload-copies-every-word
  (let ((source (proof-world-reg 2 world))
        (destination (proof-world-reg 20 world)))
    (implies (and (collection-payload-span-p count world)
                  (natp index) (< index count)
                  (proof-disjoint-p source (+ source (* 8 count))
                                    destination (+ destination (* 8 count))))
             (equal (collection-read-word
                     (+ destination (* 8 index)) (collection-copy-payload-effect count world))
                    (collection-read-word (+ source (* 8 index)) world))))
  :rule-classes nil
  :hints (("Goal" :induct (collection-payload-word-induction index count world))
          ("Subgoal *1/2" :cases ((equal index 0)))))
