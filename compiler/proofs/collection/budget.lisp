(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-retained-bytes (floor box cons-floor end)
  (+ (- box floor) (- end cons-floor)))

(defun collection-budget (retained request)
  (min *proof-space-size*
       (max *proof-runtime-page* (max (* 2 retained) (+ retained request)))))

(defun collection-limit (floor box cons-floor end request)
  (let ((retained (collection-retained-bytes floor box cons-floor end)))
    (- (+ box (collection-budget retained request)) retained)))

(defthm collection-budget-covers-live-bytes-and-request
  (implies (and (natp retained) (natp request)
                (<= (+ retained request) *proof-space-size*))
           (and (<= (+ retained request) (collection-budget retained request))
                (<= *proof-runtime-page* (collection-budget retained request))
                (<= (collection-budget retained request) *proof-space-size*)))
  :rule-classes nil)

(defthm collection-limit-admits-pending-span
  (implies (and (natp floor) (natp box) (natp cons-floor) (natp request)
                (equal end (+ floor *proof-space-size*))
                (<= floor box) (<= box cons-floor) (<= cons-floor end)
                (<= (+ (collection-retained-bytes floor box cons-floor end) request)
                    *proof-space-size*))
           (and (<= (+ box request)
                    (collection-limit floor box cons-floor end request))
                (<= (collection-limit floor box cons-floor end request) cons-floor)
                (<= box (- cons-floor request))))
  :rule-classes nil)

(defthm collection-budget-limit-admits-fast-allocator
  (let ((box (proof-box-top world))
        (cells (proof-cons-floor world)))
    (implies (and (member-eq kind '(:header :cons))
                  (natp request) (equal (mod request (if (eq kind :cons) 16 8)) 0)
                  (natp floor) (natp box) (natp cells)
                  (equal end (+ floor *proof-space-size*))
                  (<= floor box) (<= box cells) (<= cells end)
                  (<= (+ (collection-retained-bytes floor box cells end) request)
                      *proof-space-size*)
                  (equal (proof-heap-limit world)
                         (collection-limit floor box cells end request)))
             (proof-allocation-fits-p kind request world)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-limit-admits-pending-span
                            (box (proof-box-top world)) (cons-floor (proof-cons-floor world))))
           :in-theory (disable proof-box-top proof-cons-floor proof-heap-limit
                               collection-limit collection-retained-bytes mod))))

(defthm collection-capacity-test-identifies-resource-bound
  (implies (and (natp floor) (natp box) (natp cons-floor) (natp end) (natp request)
                (<= floor box) (<= cons-floor end)
                (< *proof-space-size*
                   (+ (collection-retained-bytes floor box cons-floor end) request)))
           (proof-resource-bound-p
            :heap-size (+ (collection-retained-bytes floor box cons-floor end) request)
            world)))

(defthm collection-capacity-test-sum-fits-word
  (implies (and (natp floor) (natp box) (natp cons-floor) (natp request)
                (equal end (+ floor *proof-space-size*))
                (<= floor box) (<= box cons-floor) (<= cons-floor end)
                (<= request *proof-space-size*))
           (unsigned-byte-p
            34 (+ (collection-retained-bytes floor box cons-floor end) request))))
