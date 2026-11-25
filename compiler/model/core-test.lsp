(in-package "ACL2")

(defpkg "BOYMOO-CORE-VISIBLE" '(common-lisp::car))
(defpkg "BOYMOO-CORE-HIDDEN" '(common-lisp::car))

(in-package "BOYMOO-MODEL")

(set-guard-checking :none)

(assert-event
 (and (eq (core-eval '(quote nil) nil nil 0) :out-of-fuel)
      (equal (core-eval '(quote nil) nil nil 1) (core-value nil))))

(program)

(defun core-test-read (channel acc state)
  (declare (xargs :stobjs state))
  (mv-let (eof object state)
    (read-object channel state)
    (if eof
        (mv (reverse acc) state)
      (core-test-read channel (cons object acc) state))))

(defun core-test-read-file (file state)
  (declare (xargs :stobjs state))
  (mv-let (channel state)
    (open-input-channel file :object state)
    (if channel
        (mv-let (objects state)
          (core-test-read channel nil state)
          (let ((state (close-input-channel channel state)))
            (mv objects state)))
      (prog2$ (er hard 'core-test-read-file "Cannot read ~x0." file)
              (mv nil state)))))

(defun core-test-program (forms definitions attachments)
  (if (endp forms)
      (core-program definitions attachments '("BOYMOO-CORE-VISIBLE")
                    '(boymoo-core-hidden::acl2-pkg-witness))
    (let ((form (car forms)))
      (case (car form)
        (define
         (core-test-program (cdr forms)
                            (revappend (cddr form) definitions)
                            attachments))
        (attach
         (core-test-program (cdr forms) definitions
                            (cons (cdr form) attachments)))
        (otherwise (er hard 'core-test-program "Unknown line ~x0." form))))))

(defun core-test-results (terms program)
  (if (endp terms)
      nil
    (let* ((result (core-eval (car terms) nil program 64))
           (printed (if (core-value-p result) (core-datum result) result)))
      (cons (coerce (reverse (acl2::bm-obj printed nil)) 'string)
            (core-test-results (cdr terms) program)))))

(defun core-test-run (state)
  (declare (xargs :stobjs state))
  (mv-let (forms state)
    (core-test-read-file "test.program" state)
    (mv-let (terms state)
      (core-test-read-file "queries.terms" state)
      (acl2::bm-write-file
       (core-test-results terms (core-test-program forms nil nil))
       "model.results" state))))

(core-test-run state)
