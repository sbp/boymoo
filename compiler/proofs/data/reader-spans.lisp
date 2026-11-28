(in-package "BOYMOO-PROOFS")

(include-book "datum-spans")

(logic)
(set-verify-guards-eagerness 0)

(defun data-quote-field-p (frames)
  (and (eq (caar frames) :term)
       (equal (cadar frames) boymoo-compiler::*quote-name*)
       (not (cddar frames))))

(defun data-reader-separator-p (text position limit in-list)
  (let ((byte (char text position)))
    (if in-list
        (member-equal byte '(#\Space #\)))
      (or (<= limit position) (equal byte #\Newline)))))

; A witness specifies punctuation and the endpoints of atom and quote
; spans. It determines the list structure without reading ahead.
(defun data-reader-event (event text position limit frames lines terms)
  (let ((byte (char text position))
        (next (1+ position))
        (end (cadr event)))
    (case (car event)
      (:open
       (mv (and (equal byte #\() (not (data-quote-field-p frames)))
           next (cons (list (boymoo-compiler::read-list-role frames terms)) frames) lines))
      (:close
       (let* ((parent (cdr frames))
              (inside (consp parent))
              (item (boymoo-compiler::reverse-onto (cdar frames) nil)))
         (mv (and (equal byte #\)) (consp (cdar frames))
                  (data-reader-separator-p text next limit inside))
             next (if inside (boymoo-compiler::read-push item parent) nil)
             (if inside lines (cons item lines)))))
      (:space
       (mv (and (equal byte #\Space) (consp (cdar frames))
                (not (member-equal (char text next) '(#\Space #\Newline #\)))))
           next frames lines))
      (:line-feed
       (mv (and (equal byte #\Newline) (not (consp frames)) (posp position)
                (not (equal (char text (1- position)) #\Newline)))
           next nil lines))
      (:atom
       (mv (and (consp frames) (not (data-quote-field-p frames))
                (not (boymoo-compiler::delimiter byte))
                (data-token-span-p text position end limit)
                (data-reader-separator-p text end limit t))
           end (boymoo-compiler::read-push (subseq text position end) frames) lines))
      (:quote
       (mv (and (data-quote-field-p frames)
                (not (member-equal byte '(#\Space #\Newline #\))))
                (data-datum-segments-p (caddr event) text position limit 0 end)
                (data-reader-separator-p text end limit t))
           end (boymoo-compiler::read-push (subseq text position end) frames) lines))
      (otherwise (mv nil position frames lines)))))

(defun data-reader-events (events text position limit frames lines terms)
  (if (atom events)
      (mv (and (null events) (equal position limit) (not (consp frames))) lines)
    (if (<= limit position)
        (mv nil lines)
      (mv-let (ok next new-frames new-lines)
        (data-reader-event (car events) text position limit frames lines terms)
        (if ok (data-reader-events (cdr events) text next limit new-frames new-lines terms)
          (mv nil lines))))))

(local
 (in-theory (disable char subseq boymoo-compiler::read-push boymoo-compiler::read-list-role
                     boymoo-compiler::reverse-onto boymoo-compiler::token-end boymoo-compiler::datum-end
                     data-token-span-p data-datum-segments-p)))

(local
 (defthm token-span-advances-position
   (implies (data-token-span-p text position end limit)
            (and (integerp end) (< position end) (<= end limit)))
   :rule-classes ((:forward-chaining :trigger-terms ((data-token-span-p text position end limit))))
   :hints (("Goal" :in-theory (enable data-token-span-p)))))

(local
 (defthm reader-event-advances-position
   (mv-let (ok next new-frames new-lines)
     (data-reader-event event text position limit frames lines terms)
     (declare (ignore new-frames new-lines))
     (implies (and ok (natp position) (integerp limit) (< position limit))
              (and (integerp next) (< position next) (<= next limit))))
   :hints (("Goal" :use ((:instance data-datum-segments-are-bounded
                                    (ends (caddr event)) (start position) (depth 0) (end (cadr event))))))))

(local
 (defthm reader-after-a-separator
   (implies (data-reader-separator-p text position limit in-list)
            (equal (boymoo-compiler::read-after text position limit in-list) position))))

(local
 (defthm reader-follows-event
   (mv-let (ok next new-frames new-lines)
     (data-reader-event event text position limit frames lines terms)
     (implies (and ok (natp position) (< position limit) (posp fuel))
              (equal (boymoo-compiler::read-lines text position limit frames lines terms fuel)
                     (boymoo-compiler::read-lines text next limit new-frames new-lines terms (1- fuel)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-token-end-at-span-boundary (start position) (end (cadr event)))
                         (:instance data-datum-end-with-reader-fuel
                                    (ends (caddr event)) (start position) (depth 0) (end (cadr event))))
                   :in-theory (disable boymoo-compiler::read-lines boymoo-compiler::compiler-error)
                   :expand ((boymoo-compiler::read-lines text position limit frames lines terms fuel))))))

(local
 (in-theory (disable data-reader-event)))

(defthmd data-reader-events-fit-in-input
  (implies (and (natp position) (integerp limit)
                (mv-nth 0 (data-reader-events events text position limit frames lines terms)))
           (<= (len events) (- limit position)))
  :hints (("Goal" :induct (data-reader-events events text position limit frames lines terms)
                  :in-theory (disable mv-nth))
          ("Subgoal *1/3" :use ((:instance reader-event-advances-position (event (car events))))
                          :in-theory (disable reader-event-advances-position mv-nth))))

(local
 (defthm reader-events-with-additional-fuel
   (mv-let (ok result) (data-reader-events events text position limit frames lines terms)
     (implies (and ok (natp position) (integerp limit) (natp extra))
              (equal (boymoo-compiler::read-lines text position limit frames lines terms (+ (len events) extra))
                     result)))
   :rule-classes nil
   :hints (("Goal" :induct (data-reader-events events text position limit frames lines terms)
                   :in-theory (disable mv-nth boymoo-compiler::read-lines))
           ("Subgoal *1/1" :in-theory (enable boymoo-compiler::read-lines))
           ("Subgoal *1/3" :use ((:instance reader-follows-event (event (car events))
                                            (fuel (+ (len events) extra)))
                                 (:instance reader-event-advances-position (event (car events))))
                           :in-theory (disable reader-event-advances-position mv-nth
                                               boymoo-compiler::read-lines)))))

(defthmd data-read-lines-from-spans
  (mv-let (ok result) (data-reader-events events text position limit frames lines terms)
    (implies (and ok (natp position) (integerp limit) (natp fuel) (<= (len events) fuel))
             (equal (boymoo-compiler::read-lines text position limit frames lines terms fuel) result)))
  :hints (("Goal" :use ((:instance reader-events-with-additional-fuel (extra (- fuel (len events)))))
                  :in-theory (disable data-reader-events boymoo-compiler::read-lines mv-nth))))

(defun data-ascii-program-bytes-p (text position count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((byte (char text position)))
      (and (or (equal byte #\Newline) (and (<= 32 (char-code byte)) (<= (char-code byte) 126)))
           (data-ascii-program-bytes-p text (1+ position) (1- count))))))

(local
 (defthm ascii-program-bytes-pass-the-check
   (implies (data-ascii-program-bytes-p text position count)
            (boymoo-compiler::check-program-bytes text position count))
   :hints (("Goal" :induct (data-ascii-program-bytes-p text position count)))))

(defun data-program-spans-p (text events lines)
  (let ((size (length text)))
    (and (stringp text) (< 0 size) (equal (char text (1- size)) #\Newline)
         (data-ascii-program-bytes-p text 0 size)
         (mv-let (ok result) (data-reader-events events text 0 size nil nil t)
           (and ok (equal result lines))))))

(defthmd data-read-program-from-spans
  (implies (data-program-spans-p text events lines)
           (equal (boymoo-compiler::read-program text) lines))
  :hints (("Goal" :use ((:instance data-reader-events-fit-in-input
                                   (position 0) (limit (length text)) (frames nil) (lines nil) (terms t))
                        (:instance data-read-lines-from-spans
                                   (position 0) (limit (length text)) (frames nil) (lines nil) (terms t)
                                   (fuel (length text))))
                  :in-theory (disable data-reader-events boymoo-compiler::read-lines
                                      boymoo-compiler::check-program-bytes mv-nth length))))

(defthmd data-read-constant-from-spans
  (let ((size (length text)))
    (mv-let (ok result) (data-reader-events events text 0 size nil nil nil)
      (implies (and (stringp text) ok (equal result (list parsed)))
               (equal (boymoo-compiler::read-lines text 0 size nil nil nil size) (list parsed)))))
  :hints (("Goal" :use ((:instance data-reader-events-fit-in-input
                                   (position 0) (limit (length text)) (frames nil) (lines nil) (terms nil))
                        (:instance data-read-lines-from-spans
                                   (position 0) (limit (length text)) (frames nil) (lines nil) (terms nil)
                                   (fuel (length text))))
                  :in-theory (disable data-reader-events boymoo-compiler::read-lines mv-nth length))))
