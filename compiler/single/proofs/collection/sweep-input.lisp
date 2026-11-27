(in-package "BOYMOO-PROOFS")

(include-book "sweep-snapshot")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "arithmetic/equalities" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun collection-original-mappings (headers original)
  (if (endp headers)
      nil
    (cons (list (- (car headers) 24) (collection-read-word (- (car headers) 16) original))
          (collection-original-mappings (cdr headers) original))))

(defun collection-published-sweep-records (headers original work)
  (collection-sweep-records (collection-original-mappings headers original)
                            (collection-forwarding work)))

; The sweep starts after the old pages have been released. Its links
; and mapping sizes are read from the original world. The current
; world must preserve those words and supply aligned mapping bases.
(defun collection-sweep-metadata-preserved-p (headers original current)
  (if (endp headers)
      t
    (let ((base (- (car headers) 24))
          (size-address (- (car headers) 16)))
      (and (equal (mod base (proof-world-page-size current)) 0)
           (equal (collection-read-word base current) (collection-read-word base original))
           (equal (collection-read-word size-address current)
                  (collection-read-word size-address original))
           (collection-sweep-metadata-preserved-p (cdr headers) original current)))))

(local
 (in-theory (disable collection-read-word proof-load-word proof-world-machine
                     proof-world-regions proof-world-page-size proof-world-reg
                     proof-header-size proof-header-type proof-page-size-p proof-align-up
                     proof-region proof-regions-p proof-covered-p mod
                     proof-heap-base proof-stack-base proof-stack-end proof-spaces-end proof-machine-limit
                     collection-forwarding collection-external-mark-table-p collection-external-mark-p
                     boymoo-model::a64-memory boymoo-model::a64-unsigned)))

(local
 (defthm collection-mapping-size-at-least-prefix
   (implies (natp length)
            (<= 32 (proof-align-up (+ 32 length) *proof-runtime-page*)))
   :hints (("Goal"
            :use ((:instance acl2::floor-bounded-by-/
                             (acl2::x (- (+ 32 length))) (acl2::y *proof-runtime-page*))
                  (:instance acl2::rational-implies2
                             (acl2::x (* (/ *proof-runtime-page*) (+ 32 length)))))
            :in-theory (e/d (proof-align-up ceiling)
                             (floor acl2::floor-minus acl2::floor-minus-arg1-better
                              acl2::floor-=-x/y acl2::floor-unique-equal-version
                              acl2::rational-implies2))))))

(local
 (defthm collection-mapping-runtime-size-is-aligned-for-kernel
   (implies (and (natp length) (proof-page-size-p page))
            (equal (proof-align-up (proof-align-up (+ 32 length) *proof-runtime-page*) page)
                   (proof-align-up (+ 32 length) *proof-runtime-page*)))
   :hints (("Goal"
            :in-theory (e/d (proof-align-up proof-page-size-p ceiling acl2::fold-consts-in-*)
                             (floor acl2::floor-minus acl2::floor-minus-arg1-better))
            :use ((:instance collection-mapping-size-at-least-prefix))))))

(local
 (defthm collection-mapping-region-is-covered
   (implies (and (proof-regions-p regions)
                 (member-equal (proof-region base (+ base size) :rw) regions)
                 (natp size))
            (proof-covered-p base size :write regions))
   :hints (("Goal"
            :induct (member-equal (proof-region base (+ base size) :rw) regions)
            :in-theory (enable proof-region proof-regions-p proof-covered-p)))))

(local
 (defthm collection-sweep-original-read-is-machine-load
   (equal (proof-load-word address (proof-world-machine world)) (collection-read-word address world))
   :hints (("Goal" :in-theory (enable collection-read-word)))))

(local
 (defthm collection-read-header-length-is-natural
   (natp (proof-header-size (collection-read-word address world)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-header-size)))))

(defthm collection-published-sweep-records-match-links-sizes-and-marks
  (let* ((mappings (proof-external-objects head fuel original objects))
         (headers (cdr mappings))
         (records (collection-published-sweep-records headers original work)))
    (implies (and mappings
                  (unsigned-byte-p 64 head)
                  (proof-page-size-p (proof-world-page-size current))
                  (proof-regions-p (proof-world-regions original))
                  (equal (proof-world-regions current) (proof-world-regions original))
                  (collection-sweep-metadata-preserved-p headers original current)
                  (collection-external-mark-table-p headers work current))
             (and (equal (collection-sweep-next-head records) head)
                  (collection-sweep-snapshot-p records current))))
  :rule-classes nil
  :hints (("Goal"
           :induct (proof-external-objects head fuel original objects)
           :in-theory (e/d (collection-external-mark-table-p collection-external-mark-p)
                            (proof-disjoint-p collection-mapping-region-is-covered
                             collection-mapping-runtime-size-is-aligned-for-kernel)))
          (and stable-under-simplificationp
               '(:use ((:instance collection-mapping-size-at-least-prefix
                                  (length (proof-header-size (collection-read-word (+ head 24) original))))
                       (:instance collection-mapping-runtime-size-is-aligned-for-kernel
                                  (page (proof-world-page-size current))
                                  (length (proof-header-size (collection-read-word (+ head 24) original))))
                       (:instance collection-mapping-region-is-covered
                                  (base head) (size (collection-read-word (+ head 8) original))
                                  (regions (proof-world-regions original))))))))

(defthm collection-published-sweep-record-uses-forwarding-map
  (implies (and (integerp header) (member-equal header headers))
           (equal (assoc-equal (- header 24)
                               (collection-published-sweep-records headers original work))
                  (list (- header 24) (collection-read-word (- header 16) original)
                        (if (assoc-equal header (collection-forwarding work)) t nil))))
  :hints (("Goal" :induct (len headers))))

(defthm collection-published-sweep-retains-at-most-mapped-bytes
  (<= (collection-sweep-retained-bytes (collection-published-sweep-records headers original work))
      (proof-external-bytes headers (proof-world-machine original)))
  :rule-classes :linear
  :hints (("Goal" :induct (len headers))))
