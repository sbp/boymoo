(in-package "BOYMOO-PROOFS")

(include-book "token-spans")

(logic)
(set-verify-guards-eagerness 0)

; The segment ends describe only the lexical boundary of one datum.
; The data pass interprets the atoms and the dotted-list marker.
(defun data-datum-segments-p (ends text start limit depth end)
  (and (consp ends) (natp start) (natp limit) (< start limit) (natp depth)
       (let ((next (car ends)) (rest (cdr ends)) (byte (char text start)))
         (cond ((equal byte #\()
                (and (equal next (1+ start))
                     (data-datum-segments-p rest text next limit (1+ depth) end)))
               ((equal byte #\))
                (and (equal next (1+ start))
                     (if (equal depth 1)
                         (and (null rest) (equal next end))
                       (and (< 1 depth)
                            (data-datum-segments-p rest text next limit (1- depth) end)))))
               ((equal byte #\Space)
                (and (equal next (1+ start))
                     (data-datum-segments-p rest text next limit depth end)))
               ((equal byte #\Newline) nil)
               (t (and (data-token-span-p text start next limit)
                       (if (zp depth)
                           (and (null rest) (equal next end))
                         (data-datum-segments-p rest text next limit depth end))))))))

(local
 (in-theory (disable char boymoo-compiler::token-end data-token-span-p)))

(local
 (defthm token-span-end-is-in-range
   (implies (data-token-span-p text start next limit)
            (and (integerp next) (< start next) (<= next limit)))
   :rule-classes ((:forward-chaining :trigger-terms ((data-token-span-p text start next limit))))
   :hints (("Goal" :in-theory (enable data-token-span-p)))))

(defthmd data-datum-segments-are-bounded
  (implies (data-datum-segments-p ends text start limit depth end)
           (and (natp start) (natp limit) (posp (len ends)) (integerp end)
                (<= (+ start (len ends)) end) (<= end limit)))
  :hints (("Goal" :induct (data-datum-segments-p ends text start limit depth end))))

(local
 (defthm datum-end-with-additional-fuel
   (implies (and (data-datum-segments-p ends text start limit depth end) (natp extra))
            (equal (boymoo-compiler::datum-end text start limit depth (+ (len ends) extra)) end))
   :rule-classes nil
   :hints (("Goal" :induct (data-datum-segments-p ends text start limit depth end)
                   :in-theory (enable data-token-end-at-span-boundary)))))

(defthmd data-datum-end-at-segment-boundary
  (implies (and (data-datum-segments-p ends text start limit depth end)
                (natp fuel) (<= (len ends) fuel))
           (equal (boymoo-compiler::datum-end text start limit depth fuel) end))
  :hints (("Goal" :use ((:instance datum-end-with-additional-fuel (extra (- fuel (len ends)))))
                  :in-theory (disable data-datum-segments-p boymoo-compiler::datum-end))))

(defthmd data-datum-end-with-reader-fuel
  (implies (data-datum-segments-p ends text start limit depth end)
           (equal (boymoo-compiler::datum-end text start limit depth (- limit start)) end))
  :hints (("Goal" :use ((:instance data-datum-end-at-segment-boundary (fuel (- limit start)))
                        data-datum-segments-are-bounded)
                  :in-theory (disable data-datum-segments-p boymoo-compiler::datum-end))))
