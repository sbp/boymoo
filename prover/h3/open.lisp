(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h3-open-session (base prefix measures)
  (list :h3-session base prefix measures))

(defun h3-api-open (library)
  (let* ((lib (h3-api-library library))
         (base (if (failure-p lib)
                   lib
                 (cons lib (h3-book-tactics-prepare-facts (library-library-proof lib))))))
    (h3-open-session base nil nil)))

(defun h3-open-prefix-suffix (prefix lines)
  (cond ((null prefix) (cons t lines))
        ((and (consp prefix) (consp lines) (equal (car prefix) (car lines)))
         (h3-open-prefix-suffix (cdr prefix) (cdr lines)))
        (t nil)))

(defun h3-open-admit-extension (lib lines reversed-names)
  (cond
   ((h3-api-sequence-failure lines))
   ((endp lines) (cons lib (reverse reversed-names)))
   (t
    (proof-with-checked-results
     ((parsed (h3-api-read-declaration (car lines))))
     (if parsed
         (let ((kind (car parsed)) (fields (cadr parsed)))
           (proof-with-checked-results
            ((next (h3-api-admit lib kind fields)))
            (h3-open-admit-extension next (cdr lines)
                                      (revappend (h3-api-admitted-names kind fields) reversed-names))))
       (h3-open-admit-extension lib (cdr lines) reversed-names))))))

(defun h3-open-extend-world (world lines)
  (let ((lib (car world)))
    (proof-with-checked-results
     ((admitted (h3-open-admit-extension lib lines nil)))
     (if (endp (cdr admitted))
         world
       (let ((next (car admitted)))
         (cons next (h3-book-tactics-update-prepared-facts
                     (cdr world) (library-library-proof lib) (library-library-proof next)
                     (cdr admitted))))))))

(defun h3-open-admit-earlier (base prefix earlier)
  (let ((suffix (and prefix (h3-open-prefix-suffix (car prefix) earlier))))
    (if suffix
        (h3-open-extend-world (cdr prefix) (cdr suffix))
      (h3-open-extend-world base earlier))))

(defun h3-open-measures (cache aids)
  (if (and cache (equal (car cache) aids))
      cache
    (cons aids (h3-api-measures aids))))

(defun h3-api-prove-open (session statement earlier aids)
  (let ((parsed (h3-api-read statement))
        (base (cadr session)))
    (if (or (failure-p parsed)
            (not (member-equal (car parsed) '("theorem" "define" "constrain")))
            (h3-api-sequence-failure earlier)
            (failure-p base))
        (cons nil session)
      (let ((world (h3-open-admit-earlier base (caddr session) earlier)))
        (if (failure-p world)
            (cons nil session)
          (let* ((define (equal (car parsed) "define"))
                 (cache (if define (h3-open-measures (cadddr session) aids) (cadddr session)))
                 (answer (h3-api-prove-with-prepared-facts
                          parsed (car world) (and define (cdr cache)) (cdr world))))
            (cons (if (failure-p answer) nil answer)
                  (h3-open-session base (cons earlier world) cache))))))))

(defun h3-open-collect-answers (session cases reversed)
  (if (endp cases)
      (reverse reversed)
    (let* ((obligation (car cases))
           (result (h3-api-prove-open session (car obligation) (cadr obligation)
                                     (caddr obligation))))
      (h3-open-collect-answers (cdr result) (cdr cases) (cons (car result) reversed)))))

(defun h3-api-prove-all-loop (session cases)
  (h3-open-collect-answers session cases nil))

(defun h3-api-prove-all (library cases)
  (h3-api-prove-all-loop (h3-api-open library) cases))
