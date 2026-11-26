(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

; The scanners return a success flag and the next input position.
; Rejection is an ordinary result of these functions.
(defun assembly-scan-atom (text at left closing)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      (if closing (mv nil 0) (mv t at))
    (let ((byte (char text at)))
      (cond ((equal byte #\Newline) (if closing (mv nil 0) (mv t at)))
            (closing (assembly-scan-atom text (+ at 1) (1- left)
                                         (if (equal byte closing) nil closing)))
            ((boymoo-compiler::delimiter byte) (mv t at))
            ((member-equal byte '(#\| #\"))
             (assembly-scan-atom text (+ at 1) (1- left) byte))
            (t (assembly-scan-atom text (+ at 1) (1- left) nil))))))

(defun assembly-scan-token (text at end)
  (if (and (< (+ at 2) end)
           (equal (char text at) #\#)
           (equal (char text (+ at 1)) #\C)
           (equal (char text (+ at 2)) #\())
      (let ((close (boymoo-compiler::find-char text (+ at 3) (- end (+ at 3)) #\))))
        (if close (mv t (+ close 1)) (mv nil 0)))
    (assembly-scan-atom text at (- end at) nil)))

(defun assembly-scan-datum (text at end depth fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (<= end at))
      (mv nil 0)
    (let ((byte (char text at)))
      (case byte
        (#\( (assembly-scan-datum text (+ at 1) end (+ depth 1) (1- fuel)))
        (#\) (cond ((equal depth 1) (mv t (+ at 1)))
                   ((< 1 depth) (assembly-scan-datum text (+ at 1) end (1- depth) (1- fuel)))
                   (t (mv nil 0))))
        (#\Space (assembly-scan-datum text (+ at 1) end depth (1- fuel)))
        (#\Newline (mv nil 0))
        (otherwise
         (mv-let (ok next)
           (assembly-scan-token text at end)
           (cond ((not ok) (mv nil 0))
                 ((zp depth) (mv t next))
                 (t (assembly-scan-datum text next end depth (1- fuel))))))))))

(defun assembly-reader-separator-p (text at end in-list)
  (let ((byte (char text at)))
    (if in-list
        (member-equal byte '(#\Space #\)))
      (or (<= end at) (equal byte #\Newline)))))

(defun assembly-checked-read-lines (text at end frames lines terms fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((<= end at) (if (consp frames) (mv nil nil) (mv t lines)))
        ((zp fuel) (mv nil nil))
        (t
         (let ((byte (char text at)))
           (cond
            ((equal byte #\Newline)
             (if (or (consp frames) (equal at 0) (equal (char text (1- at)) #\Newline))
                 (mv nil nil)
               (assembly-checked-read-lines text (+ at 1) end nil lines terms (1- fuel))))
            ((equal byte #\Space)
             (if (and (consp (cdar frames))
                      (not (member-equal (char text (+ at 1)) '(#\Space #\Newline #\)))))
                 (assembly-checked-read-lines text (+ at 1) end frames lines terms (1- fuel))
               (mv nil nil)))
            ((and (eq (caar frames) :term)
                  (equal (cadar frames) boymoo-compiler::*quote-name*)
                  (not (cddar frames)) (not (equal byte #\))))
             (mv-let (ok next)
               (assembly-scan-datum text at end 0 (- end at))
               (if (and ok (assembly-reader-separator-p text next end t))
                   (assembly-checked-read-lines
                    text next end (boymoo-compiler::read-push (subseq text at next) frames)
                    lines terms (1- fuel))
                 (mv nil nil))))
            ((equal byte #\()
             (assembly-checked-read-lines
              text (+ at 1) end
              (cons (list (boymoo-compiler::read-list-role frames terms)) frames)
              lines terms (1- fuel)))
            ((equal byte #\))
             (let ((in-list (consp (cdr frames)))
                   (next (+ at 1)))
               (if (and (consp (cdar frames)) (assembly-reader-separator-p text next end in-list))
                   (let ((item (boymoo-compiler::reverse-onto (cdar frames) nil)))
                     (if in-list
                         (assembly-checked-read-lines
                          text next end (boymoo-compiler::read-push item (cdr frames))
                          lines terms (1- fuel))
                       (assembly-checked-read-lines
                        text next end nil (cons item lines) terms (1- fuel))))
                 (mv nil nil))))
            ((consp frames)
             (mv-let (ok next)
               (assembly-scan-token text at end)
               (if (and ok (assembly-reader-separator-p text next end t))
                   (assembly-checked-read-lines
                    text next end (boymoo-compiler::read-push (subseq text at next) frames)
                    lines terms (1- fuel))
                 (mv nil nil))))
            (t (mv nil nil)))))))

(defun assembly-program-printable-p (text at left)
  (declare (xargs :measure (nfix left)))
  (or (zp left)
      (and (let ((byte (char text at)))
             (or (equal byte #\Newline) (boymoo-compiler::printable-byte-p byte)))
           (assembly-program-printable-p text (+ at 1) (1- left)))))

(defun assembly-checked-read-program (text)
  (let ((size (length text)))
    (if (and (stringp text) (< 0 size) (equal (char text (1- size)) #\Newline)
             (assembly-program-printable-p text 0 size))
        (assembly-checked-read-lines text 0 size nil nil t size)
      (mv nil nil))))

(local (in-theory (disable char length subseq boymoo-compiler::find-char
                           boymoo-compiler::delimiter boymoo-compiler::printable-byte-p
                           boymoo-compiler::read-push boymoo-compiler::read-list-role
                           boymoo-compiler::reverse-onto
                           (:executable-counterpart boymoo-compiler::compiler-error))))

(defthm assembly-accepted-atom-scan-agrees
  (mv-let (ok next)
    (assembly-scan-atom text at left closing)
    (implies ok
             (equal (boymoo-compiler::atom-end text at left closing) next)))
  :hints (("Goal" :induct (assembly-scan-atom text at left closing))))

(local (in-theory (disable assembly-scan-atom boymoo-compiler::atom-end)))

(defthm assembly-accepted-token-scan-agrees
  (mv-let (ok next)
    (assembly-scan-token text at end)
    (implies ok
             (equal (boymoo-compiler::token-end text at end) next))))

(local (in-theory (disable assembly-scan-token boymoo-compiler::token-end)))

(defthm assembly-accepted-datum-scan-agrees
  (mv-let (ok next)
    (assembly-scan-datum text at end depth fuel)
    (implies ok
             (equal (boymoo-compiler::datum-end text at end depth fuel) next)))
  :hints (("Goal" :induct (assembly-scan-datum text at end depth fuel))))

(defthm assembly-accepted-reader-separator-agrees
  (implies (assembly-reader-separator-p text at end in-list)
           (equal (boymoo-compiler::read-after text at end in-list) at)))

(local (in-theory (disable assembly-scan-datum boymoo-compiler::datum-end
                           assembly-reader-separator-p boymoo-compiler::read-after)))

(defthm assembly-accepted-line-reader-agrees
  (mv-let (ok result)
    (assembly-checked-read-lines text at end frames lines terms fuel)
    (implies ok
             (equal (boymoo-compiler::read-lines text at end frames lines terms fuel) result)))
  :hints (("Goal" :induct (assembly-checked-read-lines text at end frames lines terms fuel))))

(local
 (defthm assembly-accepted-program-byte-check-agrees
   (implies (assembly-program-printable-p text at left)
            (equal (boymoo-compiler::check-program-bytes text at left) t))
   :hints (("Goal" :induct (assembly-program-printable-p text at left)))))

(local (in-theory (disable assembly-checked-read-lines boymoo-compiler::read-lines
                           assembly-program-printable-p boymoo-compiler::check-program-bytes)))

(defthm assembly-accepted-program-reader-agrees
  (mv-let (ok lines)
    (assembly-checked-read-program text)
    (implies ok
             (equal (boymoo-compiler::read-program text) lines))))
