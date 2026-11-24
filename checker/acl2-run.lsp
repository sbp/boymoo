; Runs the checker inside ACL2, for development and as a cross-check of the
; runner: checker/acl2-check.sh includes the book build/checker/acl2/check,
; loads this file, and then calls RUN-CASE-FOUR for each case.  It is no
; part of the checker.

(in-package "ACL2")

; The bytes of a file as a string, one character for each byte; or NIL if
; the file cannot be opened.
(defun bm-read-bytes (channel acc state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (byte state)
    (read-byte$ channel state)
    (if (null byte)
        (mv (coerce (reverse acc) 'string) state)
      (bm-read-bytes channel (cons (code-char byte) acc) state))))

(defun bm-file-string (name state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (channel state)
    (open-input-channel name :byte state)
    (if (null channel)
        (mv nil state)
      (mv-let (string state)
        (bm-read-bytes channel nil state)
        (let ((state (close-input-channel channel state)))
          (mv string state))))))

; Prints the line "verdict NAME<tab>VERDICT".
(defun run-case-four (name library statements proofs library-proofs state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (g state) (bm-file-string "spec/ground.txt" state)
    (mv-let (l state) (bm-file-string library state)
      (mv-let (s state) (bm-file-string statements state)
        (mv-let (p state) (bm-file-string proofs state)
          (mv-let (lp state)
            (if (equal library-proofs "")
                (mv "" state)
              (bm-file-string library-proofs state))
            (let ((v (if (and g l s p lp)
                         (boymoo::check-four g l s p lp)
                       (list "a file could not be read" ""))))
              (prog2$ (cw "~%verdict ~s0~s1~s2~%" name
                          (coerce (list (code-char 9)) 'string) (car v))
                      (value :done)))))))))

(defun run-case (name library statements proofs state)
  (declare (xargs :mode :program :stobjs state))
  (run-case-four name library statements proofs "" state))

(set-guard-checking :none)

; A verdict is printed on one line, however long.
(set-fmt-soft-right-margin 100000 state)
(set-fmt-hard-right-margin 100000 state)
