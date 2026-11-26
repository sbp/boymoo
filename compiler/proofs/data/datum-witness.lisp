(in-package "BOYMOO-PROOFS")

(include-book "datum-spans")

(logic)
(set-verify-guards-eagerness 0)

; A missing delimiter has no candidate endpoint.
(defun data-ordinary-token-end-candidate (text start left closing)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      (if closing nil start)
    (let ((byte (char text start)))
      (cond ((equal byte #\Newline) (if closing nil start))
            (closing (data-ordinary-token-end-candidate text (1+ start) (1- left)
                                                         (if (equal byte closing) nil closing)))
            ((boymoo-compiler::delimiter byte) start)
            (t (data-ordinary-token-end-candidate text (1+ start) (1- left)
                                                  (if (member-equal byte '(#\| #\")) byte nil)))))))

(defun data-token-end-candidate (text start limit)
  (if (data-complex-prefix-p text start limit)
      (let ((end (boymoo-compiler::find-char text (+ start 3) (- limit (+ start 3)) #\))))
        (and end (1+ end)))
    (data-ordinary-token-end-candidate text start (- limit start) nil)))

(local
 (defthm reader-error-has-nil-as-its-logical-result
   (equal (boymoo-compiler::compiler-error message value) nil)))

(local
 (defthm ordinary-token-candidate-agrees-with-logical-scanner
   (equal (data-ordinary-token-end-candidate text start left closing)
          (boymoo-compiler::atom-end text start left closing))
   :hints (("Goal" :induct (data-ordinary-token-end-candidate text start left closing)
                   :in-theory (disable char)))))

(defthmd data-token-candidate-agrees-with-logical-scanner
  (equal (data-token-end-candidate text start limit) (boymoo-compiler::token-end text start limit))
  :hints (("Goal" :in-theory (disable char boymoo-compiler::find-char boymoo-compiler::atom-end))))

; Each step finds the end of one lexical segment of a quoted datum.
; Its final flag records whether the datum ends at that segment.
(defun data-datum-segment-candidate (text start limit depth)
  (let ((byte (char text start)) (next (1+ start)))
    (cond ((equal byte #\() (mv t next (1+ depth) nil))
          ((equal byte #\)) (mv (posp depth) next (1- depth) (equal depth 1)))
          ((equal byte #\Space) (mv t next depth nil))
          ((equal byte #\Newline) (mv nil start depth nil))
          (t (let ((end (data-token-end-candidate text start limit)))
               (mv (data-token-span-p text start end limit) end depth (zp depth)))))))

(defun data-infer-datum-segments (text start limit depth fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (not (natp start)) (not (natp limit)) (<= limit start) (not (natp depth)))
      (mv nil nil start)
    (mv-let (ok next deeper done) (data-datum-segment-candidate text start limit depth)
      (cond ((not ok) (mv nil nil start))
            (done (mv t (list next) next))
            (t (mv-let (ok ends end) (data-infer-datum-segments text next limit deeper (1- fuel))
                 (mv ok (cons next ends) end)))))))

(local
 (in-theory (disable char boymoo-compiler::token-end data-token-end-candidate data-token-span-p)))

(defthmd data-inferred-datum-segments-validate
  (mv-let (ok ends end) (data-infer-datum-segments text start limit depth fuel)
    (implies ok (data-datum-segments-p ends text start limit depth end)))
  :hints (("Goal" :induct (data-infer-datum-segments text start limit depth fuel)
                  :in-theory (disable data-datum-segments-p)
                  :expand ((:free (next others nesting last)
                                  (data-datum-segments-p (cons next others) text start limit nesting last))))))

(local
 (defthm remainder-fuel-after-one-segment
   (implies (consp ends) (equal (1- (+ extra (len ends))) (+ extra (len (cdr ends)))))))

(local
 (defthm syntax-of-datum-segments-determines-the-candidates
   (implies (and (data-datum-segments-p ends text start limit depth end) (natp extra))
            (equal (mv-list 3 (data-infer-datum-segments text start limit depth (+ (len ends) extra)))
                   (list t ends end)))
   :rule-classes nil
   :hints (("Goal" :induct (data-datum-segments-p ends text start limit depth end)
                   :in-theory (enable data-token-end-at-span-boundary
                                      data-token-candidate-agrees-with-logical-scanner)))))

(defthmd data-inferred-datum-segments-recover-the-validated-boundary
  (implies (data-datum-segments-p ends text start limit depth end)
           (equal (mv-list 3 (data-infer-datum-segments text start limit depth (- limit start)))
                  (list t ends end)))
  :hints (("Goal" :use (data-datum-segments-are-bounded
                        (:instance syntax-of-datum-segments-determines-the-candidates
                                   (extra (- limit (+ start (len ends))))))
                  :in-theory (disable data-datum-segments-p data-infer-datum-segments))))
