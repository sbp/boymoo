; Evaluate a group of canonical terms in one ACL2 world.
; Load after the H4 books and prover/tools/acl2-run.lsp.

(in-package "ACL2")

(program)
(set-state-ok t)

(defun h4-prover-run-lines (text start end pkgs channel number failures state)
  (if (<= end start)
      (mv failures state)
    (prog2$ (cw "~%h4-run-start ~x0~%" number)
            (mv-let (next printable)
              (rb-line-end text start end t)
              (mv-let (error result seconds state)
                (prover-run-value text start next printable pkgs number state)
                (let* ((value (if error "no value"
                                (coerce (reverse (bm-obj result nil)) 'string)))
                       (state (princ$ value channel state))
                       (state (newline channel state)))
                  (prog2$ (cw "~%h4-run-cpu ~x0 ~x1~%" number seconds)
                          (h4-prover-run-lines text (1+ next) end pkgs channel (1+ number)
                                             (+ failures (if error 1 0)) state))))))))

(defun h4-prover-run-file (input output first state)
  (let ((text (read-file-into-string input)))
    (cond ((not (stringp text))
           (er soft 'h4-prover-run-file "Could not read ~x0." input))
          (t (mv-let (channel state)
               (open-output-channel output :character state)
               (if (null channel)
                   (er soft 'h4-prover-run-file "Could not write ~x0." output)
                 (let ((pkgs (rb-witnesses (global-val 'known-package-alist (w state)))))
                   (mv-let (failures state)
                     (h4-prover-run-lines text 0 (length text) pkgs channel first 0 state)
                     (let ((state (close-output-channel channel state)))
                       (prog2$ (cw "~%prover-run-finished ~x0~%" failures)
                               (value failures)))))))))))
