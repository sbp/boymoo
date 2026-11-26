(in-package "BOYMOO-PROOFS")

(include-book "layout")

(logic)
(set-verify-guards-eagerness 0)

; Each cell holds its first word and the preceding tail reference. The
; tail may name NIL or any other previously encoded datum.
(defun data-list-cell-chunks (reversed tail offset)
  (if (atom reversed)
      nil
    (append (data-list-cell-chunks (cdr reversed) offset (+ offset 16))
            (list tail (car reversed)))))

(local
 (defthm append-associative-for-list-chunks
   (equal (append (append first second) third) (append first second third))))

(defthmd data-list-cells-allocate-consecutive-pairs
  (implies (integerp (car block))
           (equal (mv-list 2 (boymoo-compiler::data-list-cells reversed tail block))
                  (list (if (consp reversed) (+ (car block) (* 16 (1- (len reversed)))) tail)
                        (cons (+ (car block) (* 16 (len reversed)))
                              (append (data-list-cell-chunks reversed tail (car block))
                                      (cdr block))))))
  :hints (("Goal" :induct (boymoo-compiler::data-list-cells reversed tail block))))

(defthm data-list-cell-chunks-are-words
  (implies (and (data-word-chunks-p reversed) (not (stringp tail)) (integerp offset))
           (data-word-chunks-p (data-list-cell-chunks reversed tail offset)))
  :hints (("Goal" :induct (data-list-cell-chunks reversed tail offset))))

(defthm data-list-cell-chunks-have-two-words-per-cell
  (equal (len (data-list-cell-chunks reversed tail offset)) (* 2 (len reversed)))
  :hints (("Goal" :induct (data-list-cell-chunks reversed tail offset))))
