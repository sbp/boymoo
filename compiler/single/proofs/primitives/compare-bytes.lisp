(in-package "BOYMOO-PROOFS")

(include-book "leaf-routines")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm p6-byte-register-upper-bound
   (< (proof-world-reg register world) #x10000000000000000)
   :rule-classes :linear
   :hints (("Goal" :use p6-world-register-range
                   :in-theory (disable p6-world-register-range)))))

(defund p6-byte-entry (width)
  (if (equal width 8) "rt:equal-bytes" "rt:equal-bytes-tail"))

(defund p6-byte-chunk-match-p (width world)
  (equal (p6-world-load width (proof-world-reg 0 world) world)
         (p6-world-load width (proof-world-reg 1 world) world)))

(defund p6-byte-block-sites (width action)
  (let ((entry (p6-byte-entry width)))
    (case action
      (:tail (p6-sites entry 2))
      (:empty (append (p6-sites entry 1) (p6-literal-sites "rt:bytes-match")))
      (:advance (p6-sites entry (if (equal width 8) 10 9)))
      (:different (append (p6-sites entry (if (equal width 8) 6 5))
                          (p6-literal-sites "rt:bytes-differ"))))))

(defund p6-byte-block-pre-p (width action base world)
  (let ((count (proof-world-reg 2 world))
        (left (proof-world-reg 0 world))
        (right (proof-world-reg 1 world)))
    (and (p6-path-entry-p (p6-byte-block-sites width action) base world)
         (case action
           (:empty (equal count 0))
           (:tail (let ((target (+ base (p6-runtime-offset "rt:equal-bytes-tail"))))
                    (and (< count 8) (unsigned-byte-p 64 target)
                         (not (equal target (proof-world-reg 30 world))))))
           (otherwise
            (and (<= width count)
                 (proof-covered-p left width :read (proof-world-regions world))
                 (proof-covered-p right width :read (proof-world-regions world))
                 (if (eq action :advance)
                     (and (p6-byte-chunk-match-p width world)
                          (< (+ left width) (expt 2 64))
                          (< (+ right width) (expt 2 64)))
                   (not (p6-byte-chunk-match-p width world)))))))))

(defund p6-byte-frame-p (before after)
  (and (p6-same-mapped-memory-p before after)
       (equal (cdr before) (cdr after))
       (equal (boymoo-model::a64-sp (proof-world-machine before))
              (boymoo-model::a64-sp (proof-world-machine after)))
       (proof-register-frame-p 30 '(0 1 2 3 4) before after)))

(defund p6-byte-block-post-p (width action base before)
  (let* ((sites (p6-byte-block-sites width action))
         (after (p6-path-end sites before))
         (link (proof-world-reg 30 before)))
    (and (p6-byte-frame-p before after)
         (not (proof-world-stop after))
         (p6-register-file-p after)
         (p6-read-only-path-p sites base (list link) before)
         (case action
           (:tail (and (equal (proof-world-pc after)
                              (+ base (p6-runtime-offset "rt:equal-bytes-tail")))
                       (not (equal (proof-world-pc after) link))
                       (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                       (equal (proof-world-reg 1 after) (proof-world-reg 1 before))
                       (equal (proof-world-reg 2 after) (proof-world-reg 2 before))))
           (:advance (and (equal (proof-world-pc after) (proof-world-pc before))
                          (not (equal (proof-world-pc after) link))
                          (equal (proof-world-reg 0 after) (+ width (proof-world-reg 0 before)))
                          (equal (proof-world-reg 1 after) (+ width (proof-world-reg 1 before)))
                          (equal (proof-world-reg 2 after) (- (proof-world-reg 2 before) width))))
           (otherwise (and (equal (proof-world-pc after) link)
                           (equal (proof-world-reg 0 after) (if (eq action :empty) 1 0))))))))

(defmacro p6-prove-byte-block (theorem width action)
  `(defthm ,theorem
     (implies (p6-byte-block-pre-p ,width ,action base world)
              (p6-byte-block-post-p ,width ,action base world))
     :rule-classes nil
     :hints (("Goal"
              :in-theory (e/d (p6-byte-block-pre-p p6-byte-block-post-p p6-byte-block-sites
                                                    p6-byte-entry p6-path-entry-p p6-byte-chunk-match-p
                                                    p6-byte-frame-p p6-same-mapped-memory-p p6-literal-sites)
                              (p6-sites-placed-p))))))

(p6-prove-byte-block p6-byte-comparison-empty-span 1 :empty)
(p6-prove-byte-block p6-byte-comparison-switches-to-tail 8 :tail)
(p6-prove-byte-block p6-byte-comparison-byte-mismatch 1 :different)
(p6-prove-byte-block p6-byte-comparison-word-mismatch 8 :different)
(p6-prove-byte-block p6-byte-comparison-advances-one-byte 1 :advance)
(p6-prove-byte-block p6-byte-comparison-advances-eight-bytes 8 :advance)

(defthm p6-byte-comparison-block-runs
  (let* ((sites (p6-byte-block-sites width action))
         (after (p6-path-end sites before))
         (reason (if (member-eq action '(:empty :different)) :cut :limit)))
    (implies (and (p6-byte-block-pre-p width action base before)
                  (p6-byte-block-post-p width action base before)
                  (member-eq action '(:empty :different :advance :tail)))
             (proof-segment-p (len sites) (list (proof-world-reg 30 before)) before reason after)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-byte-block-pre-p p6-byte-block-post-p p6-path-entry-p)
                           (p6-path-end p6-sites-placed-p p6-read-only-path-p p6-run-step))
           :use ((:instance p6-read-only-path-runs
                            (sites (p6-byte-block-sites width action)) (world before)
                            (cuts (list (proof-world-reg 30 before))))))))
