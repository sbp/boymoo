(in-package "BOYMOO-PROOFS")

(include-book "datum-witness")
(include-book "reader-spans")

(logic)
(set-verify-guards-eagerness 0)

; Candidates come from the current byte, frame and lexical endpoints.
; The reader-event relation checks each candidate before it is used.
(defun data-reader-event-candidate (text position limit frames)
  (let ((byte (char text position)))
    (cond ((equal byte #\Space) '(:space))
          ((equal byte #\Newline) '(:line-feed))
          ((equal byte #\)) '(:close))
          ((data-quote-field-p frames)
           (mv-let (ok ends end) (data-infer-datum-segments text position limit 0 (- limit position))
             (and ok (list :quote end ends))))
          ((equal byte #\() '(:open))
          (t (list :atom (data-token-end-candidate text position limit))))))

(defun data-infer-reader-events (text position limit frames lines terms fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((equal position limit) (mv (not (consp frames)) nil lines))
        ((or (<= limit position) (zp fuel)) (mv nil nil lines))
        (t (let ((event (data-reader-event-candidate text position limit frames)))
             (mv-let (ok next new-frames new-lines) (data-reader-event event text position limit frames lines terms)
               (if ok
                   (mv-let (ok rest result) (data-infer-reader-events
                                             text next limit new-frames new-lines terms (1- fuel))
                     (mv ok (cons event rest) result))
                 (mv nil nil lines)))))))

(local
 (in-theory (disable char boymoo-compiler::read-push boymoo-compiler::read-list-role
                     boymoo-compiler::reverse-onto subseq data-token-end-candidate data-token-span-p
                     data-infer-datum-segments data-datum-segments-p)))

(local
 (defthm inferred-events-pass-the-reader-relation
   (mv-let (ok events result) (data-infer-reader-events text position limit frames lines terms fuel)
     (implies ok (equal (mv-list 2 (data-reader-events events text position limit frames lines terms))
                        (list t result))))
   :hints (("Goal" :induct (data-infer-reader-events text position limit frames lines terms fuel)
                   :in-theory (disable data-reader-event-candidate data-reader-event)))))

(local
 (defthm a-validated-event-has-the-same-step-as-the-candidate
   (implies (mv-nth 0 (data-reader-event event text position limit frames lines terms))
            (equal (mv-list 4 (data-reader-event (data-reader-event-candidate text position limit frames)
                                                 text position limit frames lines terms))
                   (mv-list 4 (data-reader-event event text position limit frames lines terms))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-inferred-datum-segments-recover-the-validated-boundary
                                    (ends (caddr event)) (start position) (depth 0) (end (cadr event)))
                         (:instance data-token-end-at-span-boundary (start position) (end (cadr event))))
                   :in-theory (e/d (data-token-candidate-agrees-with-logical-scanner)
                                   (boymoo-compiler::token-end data-quote-field-p data-reader-separator-p))))))

(local
 (in-theory (disable data-reader-event-candidate data-reader-event data-infer-reader-events)))

(local
 (defthm fuel-after-reading-one-event
   (implies (consp events) (equal (1- (+ extra (len events))) (+ extra (len (cdr events)))))))

(local
 (defthm inferred-events-cover-each-validated-event-sequence
   (mv-let (ok result) (data-reader-events events text position limit frames lines terms)
     (implies (and ok (natp extra))
              (mv-let (ok inferred parsed) (data-infer-reader-events
                                             text position limit frames lines terms (+ (len events) extra))
                (declare (ignore inferred))
                (and ok (equal parsed result)))))
   :rule-classes nil
   :hints (("Goal" :induct (data-reader-events events text position limit frames lines terms)
                   :expand ((:free (fuel) (data-infer-reader-events text position limit frames lines terms fuel))))
           ("Subgoal *1/1" :expand ((data-infer-reader-events text limit limit frames lines terms extra)))
           ("Subgoal *1/3" :use ((:instance a-validated-event-has-the-same-step-as-the-candidate
                                            (event (car events))))))))

(defthmd data-inferred-events-recover-the-validated-lines
  (mv-let (ok result) (data-reader-events events text position limit frames lines terms)
    (implies (and ok (natp position) (integerp limit))
             (mv-let (ok inferred parsed) (data-infer-reader-events text position limit frames lines terms (- limit position))
               (declare (ignore inferred))
               (and ok (equal parsed result)))))
  :hints (("Goal" :use (data-reader-events-fit-in-input
                        (:instance inferred-events-cover-each-validated-event-sequence
                                   (extra (- limit (+ position (len events))))))
                  :in-theory (disable data-reader-events))))

(defun data-infer-program-spans (text)
  (let ((size (length text)))
    (if (and (stringp text) (< 0 size) (equal (char text (1- size)) #\Newline)
             (data-ascii-program-bytes-p text 0 size))
        (data-infer-reader-events text 0 size nil nil t size)
      (mv nil nil nil))))

(local (in-theory (disable length data-ascii-program-bytes-p data-reader-events boymoo-compiler::read-program)))

(defthmd data-inferred-program-spans-validate
  (mv-let (ok events lines) (data-infer-program-spans text)
    (implies ok (data-program-spans-p text events lines)))
  :hints (("Goal" :in-theory (enable inferred-events-pass-the-reader-relation))))

(defthmd data-inferred-program-spans-cover-validated-input
  (implies (data-program-spans-p text events lines)
           (mv-let (ok inferred parsed) (data-infer-program-spans text)
             (declare (ignore inferred))
             (and ok (equal parsed lines))))
  :hints (("Goal" :use ((:instance data-inferred-events-recover-the-validated-lines
                                   (position 0) (limit (length text)) (frames nil) (terms t) (lines nil)))
                  :in-theory (disable data-infer-reader-events))))

(defthmd data-read-program-from-inferred-spans
  (mv-let (ok events lines) (data-infer-program-spans text)
    (declare (ignore events))
    (implies ok (equal (boymoo-compiler::read-program text) lines)))
  :hints (("Goal" :use (data-inferred-program-spans-validate
                        (:instance data-read-program-from-spans
                                   (events (mv-nth 1 (data-infer-program-spans text)))
                                   (lines (mv-nth 2 (data-infer-program-spans text)))))
                  :in-theory (disable data-infer-program-spans data-program-spans-p))))
