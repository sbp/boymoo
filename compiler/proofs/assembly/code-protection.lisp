(in-package "BOYMOO-PROOFS")

(include-book "machine-invariant")
(include-book "image-loading")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-no-writable-overlap-p (start end regions)
  (if (atom regions)
      t
    (and (or (not (eq (caddar regions) :rw))
             (proof-disjoint-p start end (caar regions) (cadar regions)))
         (assembly-no-writable-overlap-p start end (cdr regions)))))

(defun assembly-code-protected-p (base size regions)
  (and (proof-covered-p base size :execute regions)
       (assembly-no-writable-overlap-p base (+ base size) regions)))

(defthm assembly-no-writable-overlap-on-subspan
  (implies (and (assembly-no-writable-overlap-p lower upper regions)
                (<= lower start) (<= end upper))
           (assembly-no-writable-overlap-p start end regions))
  :hints (("Goal" :induct (assembly-no-writable-overlap-p lower upper regions)))
  :rule-classes nil)

(defthm assembly-disjoint-region-list-excludes-writable-overlap
  (implies (proof-region-disjoint-p start end regions)
           (assembly-no-writable-overlap-p start end regions))
  :hints (("Goal" :induct (proof-region-disjoint-p start end regions))))

(defthm assembly-writable-span-disjoint-from-code
  (implies (and (assembly-no-writable-overlap-p code-base code-end regions)
                (proof-covered-p base size :write regions))
           (proof-disjoint-p code-base code-end base (+ base size)))
  :hints (("Goal" :induct (proof-covered-p base size :write regions)))
  :rule-classes nil)

(defthm assembly-new-region-disjoint-from-covered-span
  (implies (and (proof-covered-p base size access regions)
                (proof-region-disjoint-p start end regions))
           (proof-disjoint-p base (+ base size) start end))
  :hints (("Goal" :induct (proof-covered-p base size access regions)))
  :rule-classes nil)

(local
 (defthm assembly-protected-code-inside-head-executable-region
   (implies (and (proof-subspan-p base size (caar regions) (cadar regions))
                 (eq (caddar regions) :rx)
                 (proof-region-disjoint-p (caar regions) (cadar regions) (cdr regions)))
            (assembly-no-writable-overlap-p base (+ base size) regions))
   :hints (("Goal"
            :use ((:instance assembly-no-writable-overlap-on-subspan
                             (lower (caar regions)) (upper (cadar regions))
                             (start base) (end (+ base size)) (regions (cdr regions))))
            :in-theory (disable proof-region-disjoint-p)))))

(defthm assembly-standard-executable-span-protected
  (implies (and (proof-regions-p regions)
                (proof-covered-p base size :execute regions))
           (assembly-code-protected-p base size regions))
  :hints (("Goal" :induct (proof-covered-p base size :execute regions)
                  :in-theory (disable proof-region-disjoint-p proof-subspan-p))
          ("Subgoal *1/2"
           :use ((:instance assembly-new-region-disjoint-from-covered-span
                            (access :execute) (start (caar regions)) (end (cadar regions))
                            (regions (cdr regions))))))
  :rule-classes nil)

(defthm assembly-add-disjoint-writable-region-preserves-code-protection
  (implies (and (assembly-code-protected-p base size regions)
                (proof-region-disjoint-p start end regions))
           (assembly-code-protected-p base size (cons (proof-region start end :rw) regions)))
  :hints (("Goal"
           :use ((:instance assembly-new-region-disjoint-from-covered-span (access :execute)))
           :in-theory (disable proof-subspan-p proof-region-disjoint-p))))

(defthm assembly-unmap-preserves-executable-coverage
  (iff (proof-covered-p base size :execute (proof-remove-region-span start count regions))
       (proof-covered-p base size :execute regions))
  :hints (("Goal" :induct (proof-remove-region-span start count regions)
                  :in-theory (disable proof-subspan-p))))

(local
 (defthm assembly-cut-writable-region-preserves-disjointness
   (implies (and (proof-disjoint-p base end lower upper)
                 (proof-subspan-p start count lower upper))
            (and (proof-disjoint-p base end lower start)
                 (proof-disjoint-p base end (+ start count) upper)))))

(defthm assembly-unmap-preserves-no-writable-overlap
  (implies (assembly-no-writable-overlap-p base end regions)
           (assembly-no-writable-overlap-p base end (proof-remove-region-span start count regions)))
  :hints (("Goal" :induct (proof-remove-region-span start count regions)
                  :in-theory (disable proof-subspan-p proof-disjoint-p))
          ("Subgoal *1/2"
           :use ((:instance assembly-cut-writable-region-preserves-disjointness
                            (lower (caar regions)) (upper (cadar regions))))
           :in-theory (disable assembly-cut-writable-region-preserves-disjointness))))

(defthm assembly-unmap-preserves-code-protection
  (implies (assembly-code-protected-p base size regions)
           (assembly-code-protected-p base size (proof-remove-region-span start count regions)))
  :hints (("Goal" :in-theory (disable proof-remove-region-span
                                      proof-covered-p assembly-no-writable-overlap-p))))
