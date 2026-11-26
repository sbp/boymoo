(in-package "BOYMOO-PROOFS")

(include-book "strings")

(logic)
(set-verify-guards-eagerness 0)

; A span has an inclusive start and an exclusive end. Within a barred
; or quoted part, only its own delimiter closes the part.
(defun data-atom-span-p (text start count closing)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (null closing)
    (let ((byte (char text start)))
      (and (not (equal byte #\Newline))
           (or closing (not (member-equal byte '(#\Space #\( #\)))))
           (data-atom-span-p text (1+ start) (1- count)
                             (cond (closing (if (equal byte closing) nil closing))
                                   ((member-equal byte '(#\| #\")) byte)
                                   (t nil)))))))

(defun data-byte-absent-p (text start count byte)
  (declare (xargs :measure (nfix count)))
  (or (zp count)
      (and (not (equal (char text start) byte))
           (data-byte-absent-p text (1+ start) (1- count) byte))))

(defthmd data-find-byte-after-prefix
  (implies (and (natp start) (natp count) (posp suffix)
                (data-byte-absent-p text start count byte)
                (equal (char text (+ start count)) byte))
           (equal (boymoo-compiler::find-char text start (+ count suffix) byte)
                  (+ start count)))
  :hints (("Goal" :induct (data-byte-absent-p text start count byte)
                  :in-theory (disable char))
          ("Subgoal *1/2" :expand ((boymoo-compiler::find-char text start (+ count suffix) byte)))))

(defthmd data-ordinary-atom-end-at-span-boundary
  (implies (and (natp start) (natp count) (natp suffix)
                (data-atom-span-p text start count closing)
                (or (zp suffix) (boymoo-compiler::delimiter (char text (+ start count)))))
           (equal (boymoo-compiler::atom-end text start (+ count suffix) closing)
                  (+ start count)))
  :hints (("Goal" :induct (data-atom-span-p text start count closing)
                  :in-theory (disable char boymoo-compiler::atom-end))
          ("Subgoal *1/1" :expand ((:free (left mode) (boymoo-compiler::atom-end text start left mode))))
          ("Subgoal *1/2" :expand ((:free (left mode) (boymoo-compiler::atom-end text start left mode))))))

(defun data-complex-prefix-p (text start limit)
  (and (< (+ start 2) limit)
       (equal (char text start) #\#)
       (equal (char text (1+ start)) #\C)
       (equal (char text (+ start 2)) #\()))

(defun data-token-span-p (text start end limit)
  (and (natp start) (natp end) (natp limit) (< start end) (<= end limit)
       (if (data-complex-prefix-p text start limit)
           (and (<= (+ start 4) end)
                (data-byte-absent-p text (+ start 3) (- end (+ start 4)) #\))
                (equal (char text (1- end)) #\)))
         (and (data-atom-span-p text start (- end start) nil)
              (or (equal end limit) (boymoo-compiler::delimiter (char text end)))))))

(local
 (defthm remaining-span-counts
   (and (equal (+ (- end start) (- limit end)) (- limit start))
        (equal (+ (- end (+ start 4)) (+ 1 (- limit end))) (- limit (+ start 3))))
   :rule-classes nil))

(defthmd data-token-end-at-span-boundary
  (implies (data-token-span-p text start end limit)
           (equal (boymoo-compiler::token-end text start limit) end))
  :hints (("Goal" :use (remaining-span-counts
                        (:instance data-ordinary-atom-end-at-span-boundary
                                   (count (- end start)) (suffix (- limit end)) (closing nil))
                        (:instance data-find-byte-after-prefix
                                   (start (+ start 3)) (count (- end (+ start 4)))
                                   (suffix (+ 1 (- limit end))) (byte #\))))
                  :in-theory (disable char boymoo-compiler::atom-end boymoo-compiler::find-char
                                      data-atom-span-p data-byte-absent-p boymoo-compiler::delimiter))))
