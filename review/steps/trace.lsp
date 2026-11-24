; Replay the accepted input with the checker's admission and proof functions.
; Each record holds an input line number, the parsed line, and either its
; pending obligations or, at a step, the computed clause itself.

(in-package "ACL2")

(defun steps-replay (slines sn plines pn context input world records)
  (declare (xargs :mode :program))
  (let ((library (eq input :library)))
    (cond
     (context
      (let* ((line (boymoo::parse-line (car plines) boymoo::*proof-words*
                                      (boymoo::w-pkgs world)))
             (result (boymoo::proof-line line context library world))
             (next (car result))
             (source (if library :library-proofs :proofs))
             (detail
              (cond ((member-eq (car line) boymoo::*step-words*)
                     (caar (nth 4 next)))
                    ((eq (car line) :define) (eq (car next) :define-entry))
                    ((member-eq (car line) '(:lemma :measure :witness :theorem))
                     (cadr next)))))
        (steps-replay slines sn (cdr plines) (+ 1 pn) next input (cdr result)
                      (cons (list source pn line detail) records))))
     ((endp slines) (mv world records))
     (t
      (let* ((line (boymoo::parse-line (car slines) boymoo::*statement-words*
                                      (boymoo::w-pkgs world)))
             (result (if (and library (endp plines))
                         (boymoo::admit line input world)
                       (boymoo::prepare-statement line input world))))
        (steps-replay
         (cdr slines) (+ 1 sn) plines pn
         (and (cdr result) (list :entry (cdr result))) input (car result)
         (if (boymoo::repeat-p line world)
             records
           (cons (list input sn line (not (null (cdr result))))
                 records))))))))

; A cons is written once, after its children. The file uses the format's
; spelling for atoms, including the symbol names held by the checker.

(defun steps-atom-text (x)
  (declare (xargs :mode :program))
  (if (and (symbolp x) (equal (symbol-package-name x) "BOYMOO"))
      (symbol-name x)
    (coerce (reverse (bm-obj x nil)) 'string)))

(defun steps-write-object (x ids n channel state)
  (declare (xargs :mode :program :stobjs state))
  (let ((hit (hons-get x ids)))
    (cond
     (hit (mv (cdr hit) ids n state))
     ((atom x)
      (let* ((state (princ$ "(atom " channel state))
             (state (princ$ (steps-atom-text x) channel state))
             (state (princ$ #\) channel state))
             (state (newline channel state)))
        (mv n (hons-acons x n ids) (+ n 1) state)))
     (t
      (mv-let (a ids n state)
        (steps-write-object (car x) ids n channel state)
        (mv-let (d ids n state)
          (steps-write-object (cdr x) ids n channel state)
          (let* ((state (princ$ "(pair " channel state))
                 (state (princ$ a channel state))
                 (state (princ$ #\Space channel state))
                 (state (princ$ d channel state))
                 (state (princ$ #\) channel state))
                 (state (newline channel state)))
            (mv n (hons-acons x n ids) (+ n 1) state))))))))

(defun steps-records (ground library statements proofs library-proofs)
  (declare (xargs :mode :program))
  (let ((world (boymoo::load-ground (boymoo::lines-of ground)
                                   (boymoo::initial-world))))
    (mv-let (world records)
      (steps-replay (boymoo::lines-of library) 1 (boymoo::lines-of library-proofs)
                    1 nil :library world nil)
      (mv-let (world records)
        (steps-replay (boymoo::lines-of statements) 1 (boymoo::lines-of proofs)
                      1 nil :statements world records)
        (declare (ignore world))
        (reverse records)))))

(defun steps-trace (library statements proofs library-proofs output state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (g state) (bm-file-string "spec/ground.txt" state)
    (mv-let (l state) (bm-file-string library state)
      (mv-let (s state) (bm-file-string statements state)
        (mv-let (p state) (bm-file-string proofs state)
          (mv-let (lp state) (bm-file-string library-proofs state)
            (if (not (and g l s p lp))
                (er soft 'steps-trace "An input could not be read.")
              (let* ((verdict (car (boymoo::check-four g l s p lp)))
                     (records
                      (and (or (equal verdict "accepted")
                               (equal (subseq verdict 0 (min 12 (length verdict)))
                                      "provisional "))
                           (steps-records g l s p lp))))
                (mv-let (channel state)
                  (open-output-channel output :character state)
                  (if (not channel)
                      (er soft 'steps-trace "The trace could not be opened.")
                    (mv-let (root ids n state)
                      (steps-write-object (hons-copy (cons verdict records))
                                          nil 0 channel state)
                      (declare (ignore n))
                      (prog2$ (fast-alist-free ids)
                              (let* ((state (princ$ "(root " channel state))
                                     (state (princ$ root channel state))
                                     (state (princ$ #\) channel state))
                                     (state (newline channel state))
                                     (state (close-output-channel channel state)))
                                (value :done))))))))))))))
