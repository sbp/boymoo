(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

; A trace contains absolute instruction addresses and their decodings.
; It stops before executing an instruction at a cutpoint.
(defun collection-trace-effect (trace world)
  (if (endp trace)
      world
    (collection-trace-effect
     (cdr trace) (proof-instruction-effect (cdar trace) world))))

(defun collection-trace-ready-p (trace cuts world)
  (and (not (proof-world-stop world))
       (if (endp trace)
           (member-equal (proof-world-pc world) cuts)
         (and (equal (proof-world-pc world) (caar trace))
              (not (member-equal (proof-world-pc world) cuts))
              (proof-instruction-at-p (cdar trace) (caar trace) world)
              (proof-instruction-access-p (cdar trace) world)
              (collection-trace-ready-p
               (cdr trace) cuts (proof-instruction-effect (cdar trace) world))))))

(defthm collection-ready-trace-reaches-cut
  (implies (collection-trace-ready-p trace cuts world)
           (proof-segment-p (len trace) cuts world :cut
                            (collection-trace-effect trace world)))
  :hints (("Goal" :induct (collection-trace-ready-p trace cuts world)
           :in-theory (disable proof-step proof-instruction-at-p
                               proof-instruction-access-p proof-instruction-effect
                               proof-world-pc proof-world-stop))))

(defun collection-write-register (register value world)
  (update-nth 0
              (boymoo-model::a64-write-reg
               register 64 nil value (proof-world-machine world))
              world))

(defun collection-write-pc (address world)
  (update-nth 0 (boymoo-model::a64-set-pc address (proof-world-machine world))
              world))

(defun collection-write-flags (flags world)
  (update-nth 0 (boymoo-model::a64-set-nzcv flags (proof-world-machine world))
              world))

(defun collection-read-word (address world)
  (proof-load-word address (proof-world-machine world)))

(defun collection-write-word (address value world)
  (update-nth 0 (boymoo-model::a64-store 8 address value (proof-world-machine world))
              world))

(defun collection-slice (first next items)
  (if (endp items)
      nil
    (let ((item (car items)))
      (cond ((equal item (list :label next)) nil)
            ((or (not first) (equal item (list :label first)))
             (cons item (collection-slice nil next (cdr items))))
            (t (collection-slice first next (cdr items)))))))

(defun collection-decode-words (count offset bytes)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (let ((word (+ (char-code (char bytes offset))
                   (ash (char-code (char bytes (+ offset 1))) 8)
                   (ash (char-code (char bytes (+ offset 2))) 16)
                   (ash (char-code (char bytes (+ offset 3))) 24))))
      (cons (proof-decode word)
            (collection-decode-words (1- count) (+ offset 4) bytes)))))

(defun collection-decode-items (items)
  (let ((bytes (boymoo-compiler::a64-bytes items)))
    (collection-decode-words (ash (length bytes) -2) 0 bytes)))

(defun collection-indexed-trace (indices instructions origin)
  (if (endp indices)
      nil
    (let ((index (car indices)))
      (cons (cons (+ origin (* 4 index)) (nth index instructions))
            (collection-indexed-trace (cdr indices) instructions origin)))))
