(in-package "BOYMOO-PROOFS")

(include-book "copy-path")
(include-book "wide-words")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::gen-copy-arguments boymoo-compiler::gen-load-word
                    generated-wide-word-items generated-move-instructions proof-instruction-effect
                    proof-world-reg proof-world-pc proof-world-stop generated-sp generated-load-word
                    generated-store-word generated-read-words generated-copy-words
                    boymoo-model::a64-unsigned expt))

(defun generated-copy-step-items (offset)
  (if (< offset 32768)
      (list (list :ldr 9 10 offset) (list :str 9 19 offset))
    (append (generated-wide-word-items 17 offset) '((:ldr-reg 9 10 17) (:str-reg 9 19 17)))))

(defun generated-indexed-copy-items (count offset)
  (declare (xargs :measure (nfix count)))
  (if (zp count) nil
    (append (generated-copy-step-items offset) (generated-indexed-copy-items (1- count) (+ 8 offset)))))

(defthm generated-indexed-copy-emission
  (equal (boymoo-compiler::gen-copy-arguments count offset code)
         (boymoo-compiler::reverse-onto (generated-indexed-copy-items count offset) code))
  :hints (("Goal" :induct (boymoo-compiler::gen-copy-arguments count offset code)
                  :in-theory (enable boymoo-compiler::gen-copy-arguments boymoo-compiler::gen-emit))))

(defun generated-copy-step-path (offset)
  (if (< offset 32768)
      (generated-copy-pair offset)
    (append (generated-move-instructions (generated-wide-word-items 17 offset))
            '((:single 1 8 10 9 :register 17 3 0) (:single 0 8 19 9 :register 17 3 0)))))

(defun generated-indexed-copy-path (count offset)
  (declare (xargs :measure (nfix count)))
  (if (zp count) nil
    (append (generated-copy-step-path offset) (generated-indexed-copy-path (1- count) (+ 8 offset)))))

(local
 (defthm generated-indexed-copy-length-append
   (equal (len (append first second)) (+ (len first) (len second)))))

(defthm generated-copy-step-path-observations
  (let* ((path (generated-copy-step-path offset))
         (after (generated-path-after path before))
         (source (+ (proof-world-reg 10 before) offset))
         (destination (+ (proof-world-reg 19 before) offset))
         (pc (+ (proof-world-pc before) (* 4 (len path)))))
    (implies (and (generated-ordinary-machine-p before) (unsigned-byte-p 64 offset))
             (and (generated-ordinary-machine-p after)
                  (generated-heap-world-equiv
                   after (generated-store-word destination (generated-load-word source before) before))
                  (implies (not (member-equal register '(9 17)))
                           (equal (proof-world-reg register after) (proof-world-reg register before)))
                  (equal (generated-sp after) (generated-sp before))
                  (equal (proof-world-stop after) (proof-world-stop before))
                  (implies (< pc (expt 2 64)) (equal (proof-world-pc after) pc)))))
  :hints (("Goal" :use (:instance generated-wide-word-loads-value (rd 17) (word offset))
                  :in-theory (enable generated-copy-pair))))

(local
 (defun generated-indexed-copy-induction (count offset before)
   (declare (xargs :measure (nfix count)))
   (if (zp count) before
     (generated-indexed-copy-induction (1- count) (+ 8 offset)
                                       (generated-path-after (generated-copy-step-path offset) before)))))

(defthm generated-indexed-copy-path-observations
  (let* ((path (generated-indexed-copy-path count offset))
         (after (generated-path-after path before))
         (source (+ (proof-world-reg 10 before) offset))
         (destination (+ (proof-world-reg 19 before) offset))
         (pc (+ (proof-world-pc before) (* 4 (len path)))))
    (implies (and (generated-ordinary-machine-p before) (natp count) (natp offset)
                  (<= (+ offset (* 8 count)) (expt 2 64)))
             (and (generated-ordinary-machine-p after)
                  (generated-heap-world-equiv after (generated-copy-words count source destination before))
                  (implies (not (member-equal register '(9 17)))
                           (equal (proof-world-reg register after) (proof-world-reg register before)))
                  (equal (generated-sp after) (generated-sp before))
                  (equal (proof-world-stop after) (proof-world-stop before))
                  (implies (< pc (expt 2 64)) (equal (proof-world-pc after) pc)))))
  :hints (("Goal" :induct (generated-indexed-copy-induction count offset before)
                  :in-theory (e/d (generated-copy-words)
                                  (generated-copy-step-path)))))

(defthm generated-indexed-copy-transfers-words
  (let* ((source (+ (proof-world-reg 10 before) offset))
         (destination (+ (proof-world-reg 19 before) offset))
         (path (generated-indexed-copy-path count offset))
         (after (generated-path-after path before)))
    (implies (and (generated-ordinary-machine-p before) (natp offset)
                  (generated-word-block-span-p source count)
                  (generated-word-block-span-p destination count) (<= destination source))
             (equal (generated-read-words count destination after)
                    (generated-read-words count source before))))
  :hints (("Goal" :in-theory (e/d (generated-word-block-span-p)
                                  (generated-indexed-copy-path generated-copy-step-path))))
  :rule-classes nil)
