(in-package "BOYMOO-PROOFS")

(include-book "byte-loop")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable (:definition p6-runtime-offset) (:definition p6-sites))))

(local
 (defthm p6-code-site-from-placed-set
   (implies (and (p6-sites-placed-p all base world) (member-equal site all))
            (proof-instruction-at-p (cdr site) (+ base (car site)) world))
   :rule-classes nil
   :hints (("Goal" :induct (p6-sites-placed-p all base world)))))

(local
 (defthm p6-placement-for-site-subset
   (implies (and (p6-sites-placed-p all base world) (subsetp-equal sites all))
            (p6-sites-placed-p sites base world))
   :rule-classes nil
   :hints (("Goal" :induct (p6-sites-placed-p sites base world))
           ("Subgoal *1/2" :use ((:instance p6-code-site-from-placed-set (site (car sites))))))))

(local
 (defthm p6-code-address-from-site-set
   (implies (and (p6-site-addresses-p all base link) (member-equal site all))
            (and (unsigned-byte-p 64 (+ base (car site)))
                 (not (equal (+ base (car site)) link))))
   :rule-classes nil
   :hints (("Goal" :induct (p6-site-addresses-p all base link)))))

(local
 (defund p6-site-permitted-p (site base link)
   (and (unsigned-byte-p 64 (+ base (car site)))
        (not (equal (+ base (car site)) link)))))

(local
 (defthm p6-site-addresses-step
   (and (implies (atom sites) (p6-site-addresses-p sites base link))
        (implies (consp sites)
                 (equal (p6-site-addresses-p sites base link)
                        (and (p6-site-permitted-p (car sites) base link)
                             (p6-site-addresses-p (cdr sites) base link)))))
   :hints (("Goal" :in-theory (enable p6-site-permitted-p)
                   :expand ((p6-site-addresses-p sites base link))))))

(local
 (defthm p6-site-permitted-from-set
   (implies (and (p6-site-addresses-p all base link) (member-equal site all))
            (p6-site-permitted-p site base link))
   :rule-classes nil
   :hints (("Goal" :use p6-code-address-from-site-set
                   :in-theory (enable p6-site-permitted-p)))))

(local
 (defthm p6-addresses-for-site-subset
   (implies (and (p6-site-addresses-p all base link) (subsetp-equal sites all))
            (p6-site-addresses-p sites base link))
   :rule-classes nil
   :hints (("Goal" :induct (subsetp-equal sites all)
                   :do-not '(fertilize generalize eliminate-destructors)
                   :in-theory (disable (:definition p6-site-addresses-p)))
           ("Subgoal *1/2" :use ((:instance p6-site-permitted-from-set (site (car sites))))))))

(local (in-theory (disable p6-site-addresses-step)))

(local
 (defthm p6-subspan-transitive
   (implies (and (proof-subspan-p address size low high)
                 (proof-subspan-p part width address (+ address size)))
            (proof-subspan-p part width low high))))

(defthm p6-covered-subspan
  (implies (and (proof-covered-p address size access regions)
                (proof-subspan-p part width address (+ address size)))
           (proof-covered-p part width access regions))
  :rule-classes nil
  :hints (("Goal" :induct (proof-covered-p address size access regions)
                  :in-theory (e/d (proof-covered-p) (proof-subspan-p proof-region-allows-p)))
          ("Subgoal *1/2" :use ((:instance p6-subspan-transitive
                                         (low (caar regions)) (high (cadar regions)))))))

(defund p6-byte-span-readable-p (address count world)
  (and (proof-span-p address count)
       (< (+ address count) (expt 2 64))
       (or (zp count) (proof-covered-p address count :read (proof-world-regions world)))))

(local
 (defthm p6-readable-prefix
   (implies (and (p6-byte-span-readable-p address count world) (posp width) (<= width count))
            (proof-covered-p address width :read (proof-world-regions world)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable p6-byte-span-readable-p)
                   :use ((:instance p6-covered-subspan
                                    (size count) (access :read) (part address)
                                    (regions (proof-world-regions world))))))))

(local
 (defthm p6-readable-suffix
   (implies (and (p6-byte-span-readable-p address count world) (natp width) (<= width count)
                 (equal (proof-world-regions world) (proof-world-regions after)))
            (p6-byte-span-readable-p (+ address width) (- count width) after))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable p6-byte-span-readable-p)
                   :use ((:instance p6-covered-subspan
                                    (size count) (access :read) (part (+ address width))
                                    (width (- count width)) (regions (proof-world-regions world))))))))

(defconst *p6-byte-comparison-code*
  (append (p6-sites "rt:equal-bytes" 10)
          (p6-sites "rt:equal-bytes-tail" 9)
          (p6-literal-sites "rt:bytes-differ")
          (p6-literal-sites "rt:bytes-match")))

(defund p6-byte-comparison-entry-p (width count base world)
  (and (member-equal width '(1 8)) (equal count (proof-world-reg 2 world))
       (p6-register-file-p world) (not (proof-world-stop world)) (natp base)
       (equal (proof-world-pc world) (+ base (p6-runtime-offset (p6-byte-entry width))))
       (p6-sites-placed-p *p6-byte-comparison-code* base world)
       (p6-site-addresses-p *p6-byte-comparison-code* base (proof-world-reg 30 world))
       (p6-byte-span-readable-p (proof-world-reg 0 world) count world)
       (p6-byte-span-readable-p (proof-world-reg 1 world) count world)))

(local
 (defthm p6-byte-block-in-entry-code
   (let* ((action (p6-byte-action width count world)) (sites (p6-byte-block-sites width action)))
     (implies (member-equal width '(1 8))
              (and (consp sites)
                   (equal (caar sites) (p6-runtime-offset (p6-byte-entry width)))
                   (subsetp-equal sites *p6-byte-comparison-code*))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable p6-byte-action p6-byte-entry p6-byte-block-sites)))))

(defthm p6-byte-comparison-entry-admits-block
  (implies (p6-byte-comparison-entry-p width count base world)
           (p6-byte-block-pre-p width (p6-byte-action width count world) base world))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-byte-comparison-entry-p p6-byte-block-pre-p p6-path-entry-p
                                                     p6-byte-action p6-byte-span-readable-p)
                           (p6-sites-placed-p p6-site-addresses-p p6-byte-block-sites p6-byte-entry
                            proof-covered-p p6-byte-chunk-match-is-span-match))
           :use (p6-byte-block-in-entry-code
                 (:instance p6-placement-for-site-subset
                            (all *p6-byte-comparison-code*)
                            (sites (p6-byte-block-sites width (p6-byte-action width count world))))
                 (:instance p6-addresses-for-site-subset
                            (all *p6-byte-comparison-code*) (link (proof-world-reg 30 world))
                            (sites (p6-byte-block-sites width (p6-byte-action width count world))))
                 (:instance p6-code-address-from-site-set
                            (all *p6-byte-comparison-code*) (link (proof-world-reg 30 world))
                            (site (car (p6-sites "rt:equal-bytes-tail" 1))))
                 (:instance p6-readable-prefix (address (proof-world-reg 0 world)))
                 (:instance p6-readable-prefix (address (proof-world-reg 1 world)))))))

(defthm p6-byte-comparison-continuation-precondition
  (let* ((action (p6-byte-action width count world))
         (next-width (if (eq action :tail) 1 width))
         (next-count (if (eq action :tail) count (- count width)))
         (after (p6-path-end (p6-byte-block-sites width action) world)))
    (implies (and (p6-byte-comparison-entry-p width count base world)
                  (member-eq action '(:tail :advance)))
             (p6-byte-comparison-entry-p next-width next-count base after)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-byte-comparison-entry-p p6-byte-block-post-p p6-byte-frame-p
                                                     p6-same-mapped-memory-p p6-byte-action p6-byte-entry)
                           (p6-sites-placed-p p6-site-addresses-p p6-path-end p6-byte-block-sites
                            p6-byte-chunk-match-is-span-match proof-register-frame-p p6-read-only-path-p))
           :use (p6-byte-comparison-entry-admits-block p6-chosen-byte-block-post
                 (:instance p6-sites-depend-on-mapped-memory
                            (sites *p6-byte-comparison-code*) (first world)
                            (second (p6-path-end (p6-byte-block-sites width (p6-byte-action width count world))
                                                  world)))
                 (:instance p6-frame-preserves-unlisted-register
                            (max 30) (register 30) (clobbers '(0 1 2 3 4)) (before world)
                            (after (p6-path-end (p6-byte-block-sites width (p6-byte-action width count world))
                                                 world)))
                 (:instance p6-readable-suffix (address (proof-world-reg 0 world))
                            (after (p6-path-end (p6-byte-block-sites width :advance) world)))
                 (:instance p6-readable-suffix (address (proof-world-reg 1 world))
                            (after (p6-path-end (p6-byte-block-sites width :advance) world)))
                 (:instance p6-readable-suffix (width 0) (address (proof-world-reg 0 world))
                            (after (p6-path-end (p6-byte-block-sites width :tail) world)))
                 (:instance p6-readable-suffix (width 0) (address (proof-world-reg 1 world))
                            (after (p6-path-end (p6-byte-block-sites width :tail) world)))))))

(local
 (defthm p6-byte-loop-join-ready
   (implies (and (p6-byte-comparison-entry-p width count base world)
                 (implies (member-eq (p6-byte-action width count world) '(:tail :advance))
                          (caddr continuation)))
            (caddr (p6-byte-loop-join width count base world continuation)))
   :hints (("Goal"
            :in-theory (enable p6-byte-loop-join p6-byte-comparison-entry-p)
            :use p6-byte-comparison-entry-admits-block))))

(local
 (defthm p6-byte-entry-width
   (implies (p6-byte-comparison-entry-p width count base world)
            (or (equal width 1) (equal width 8)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable p6-byte-comparison-entry-p)))))

(defthm p6-byte-loop-recipe-applies-to-mapped-spans
  (implies (p6-byte-comparison-entry-p width count base world)
           (caddr (p6-byte-loop-recipe width count base world)))
  :rule-classes nil
  :hints (("Goal"
           :induct (p6-byte-loop-recipe width count base world)
           :in-theory (disable (:definition p6-byte-loop-recipe) p6-path-end p6-byte-block-sites
                               p6-byte-action)
           :expand ((:free (mode) (p6-byte-loop-recipe mode count base world))))
          (and stable-under-simplificationp
               '(:use ((:instance p6-byte-comparison-continuation-precondition (width 8))
                       (:instance p6-byte-comparison-continuation-precondition (width 1)))))))

(local
 (defthm p6-cut-segment-ends-at-cut
   (implies (and (proof-segment-p count cuts before :cut after)
                 (not (proof-world-stop after)))
            (member-equal (proof-world-pc after) cuts))
   :rule-classes nil
   :hints (("Goal" :induct (proof-run count cuts before)
                   :in-theory (enable proof-run)))))

(defthm p6-byte-comparison-runtime-contract
  (let* ((count (proof-world-reg 2 world))
         (recipe (p6-byte-loop-recipe 8 count base world))
         (steps (car recipe))
         (after (cadr recipe)))
    (implies (p6-byte-comparison-entry-p 8 count base world)
             (and (natp steps)
                  (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut after)
                  (proof-frame-return-p '(0 1 2 3 4) t world after)
                  (p6-same-mapped-memory-p world after)
                  (equal (cdr world) (cdr after))
                  (equal (proof-world-reg 0 after) (if (p6-bytes-match-p count world) 1 0)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable p6-byte-loop-summary-p p6-byte-frame-p p6-byte-comparison-entry-p)
           :use ((:instance p6-byte-loop-recipe-applies-to-mapped-spans
                            (width 8) (count (proof-world-reg 2 world)))
                 (:instance p6-byte-loop-recipe-correct
                            (width 8) (count (proof-world-reg 2 world)))
                 (:instance p6-cut-segment-ends-at-cut
                            (count (car (p6-byte-loop-recipe 8 (proof-world-reg 2 world) base world)))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (cadr (p6-byte-loop-recipe 8 (proof-world-reg 2 world) base world))))))))
