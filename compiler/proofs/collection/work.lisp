(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

; The graph contains the movable objects and external strings. A record
; consists of its source address, kind, size in bytes, and the source
; addresses referred to by its fields. An address outside the graph
; creates no scan work. In particular, static objects are closed under
; their references, and external strings have no reference fields.
;
; Both queues are in allocation order. The cons cursor moves down and
; the header cursor moves up. A scan handles all fields of the selected
; object before testing the two queues again.
(defun collection-work (unseen forwarding cells headers low high)
  (list unseen forwarding cells headers low high))

(defun collection-unseen (work) (nth 0 work))
(defun collection-forwarding (work) (nth 1 work))
(defun collection-cell-queue (work) (nth 2 work))
(defun collection-header-queue (work) (nth 3 work))
(defun collection-header-frontier (work) (nth 4 work))
(defun collection-cell-frontier (work) (nth 5 work))

(defun collection-copy-address (record work)
  (case (cadr record)
    (:cons (- (collection-cell-frontier work) 16))
    (:header (collection-header-frontier work))
    (otherwise (car record))))

(defun collection-discover (address work)
  (let* ((unseen (collection-unseen work))
         (record (assoc-equal address unseen))
         (kind (cadr record))
         (copy (collection-copy-address record work))
         (low (collection-header-frontier work))
         (high (collection-cell-frontier work))
         (cells (collection-cell-queue work))
         (headers (collection-header-queue work)))
    (if (not record)
        work
      (collection-work
       (remove-assoc-equal address unseen)
       (acons address copy (collection-forwarding work))
       (if (eq kind :cons) (append cells (list record)) cells)
       (if (eq kind :header) (append headers (list record)) headers)
       (if (eq kind :header) (+ low (nfix (caddr record))) low)
       (if (eq kind :cons) copy high)))))

(defun collection-discover-fields (fields work)
  (if (endp fields)
      work
    (collection-discover-fields (cdr fields) (collection-discover (car fields) work))))

(defun collection-scan-one (work)
  (let ((cells (collection-cell-queue work))
        (headers (collection-header-queue work)))
    (cond ((consp cells)
           (collection-discover-fields (cdddar cells) (update-nth 2 (cdr cells) work)))
          ((consp headers)
           (collection-discover-fields (cdddar headers) (update-nth 3 (cdr headers) work)))
          (t work))))

(defun collection-work-size (work)
  (+ (len (collection-unseen work))
     (len (collection-cell-queue work))
     (len (collection-header-queue work))))

(local
 (defthm collection-len-of-append-singleton
   (equal (len (append items (list item))) (+ 1 (len items)))))

(local
 (defthm collection-remove-assoc-does-not-increase-length
   (<= (len (remove-assoc-equal address records)) (len records))
   :rule-classes :linear))

(local
 (defthm collection-remove-assoc-decreases
   (implies (assoc-equal address records)
            (< (len (remove-assoc-equal address records)) (len records)))
   :rule-classes :linear
   :hints (("Goal" :induct (remove-assoc-equal address records)))))

(defthm collection-discovery-does-not-increase-work
  (<= (collection-work-size (collection-discover address work))
      (collection-work-size work))
  :rule-classes :linear)

(in-theory (disable collection-discover collection-work-size))

(defthm collection-field-discovery-does-not-increase-work
  (<= (collection-work-size (collection-discover-fields fields work))
      (collection-work-size work))
  :rule-classes :linear
  :hints (("Goal" :induct (collection-discover-fields fields work))))

(local
 (defthm collection-work-size-after-advancing-cell-cursor
   (implies (consp (collection-cell-queue work))
            (equal (collection-work-size
                    (update-nth 2 (cdr (collection-cell-queue work)) work))
                   (1- (collection-work-size work))))
   :hints (("Goal" :in-theory (e/d (collection-work-size) (nth update-nth))))))

(local
 (defthm collection-work-size-after-advancing-header-cursor
   (implies (consp (collection-header-queue work))
            (equal (collection-work-size
                    (update-nth 3 (cdr (collection-header-queue work)) work))
                   (1- (collection-work-size work))))
   :hints (("Goal" :in-theory (e/d (collection-work-size) (nth update-nth))))))

(defthm collection-scan-one-decreases-work
  (implies (or (consp (collection-cell-queue work))
               (consp (collection-header-queue work)))
           (< (collection-work-size (collection-scan-one work))
              (collection-work-size work)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable collection-cell-queue
                                      collection-header-queue update-nth))))

(defun collection-finish-scan (work)
  (declare (xargs :measure (collection-work-size work)
                  :hints (("Goal" :in-theory (disable collection-scan-one)))))
  (if (or (consp (collection-cell-queue work))
          (consp (collection-header-queue work)))
      (collection-finish-scan (collection-scan-one work))
    work))

(in-theory (disable collection-scan-one))

(defthm collection-finish-scan-drains-both-queues
  (let ((finish (collection-finish-scan work)))
    (and (not (consp (collection-cell-queue finish)))
         (not (consp (collection-header-queue finish)))))
  :hints (("Goal" :induct (collection-finish-scan work))))

(local
 (defthm collection-assoc-after-remove
   (equal (assoc-equal query (remove-assoc-equal address records))
          (and (not (equal query address)) (assoc-equal query records)))))

(defthm collection-discover-removes-only-its-object
  (equal (assoc-equal query (collection-unseen (collection-discover address work)))
         (and (not (equal query address))
              (assoc-equal query (collection-unseen work))))
  :hints (("Goal" :in-theory (enable collection-discover))))

(defthm collection-discover-installs-its-forwarding-entry
  (implies (assoc-equal address (collection-unseen work))
           (equal (assoc-equal address
                               (collection-forwarding (collection-discover address work)))
                  (cons address (collection-copy-address
                                 (assoc-equal address (collection-unseen work)) work))))
  :hints (("Goal" :in-theory (enable collection-discover))))

(defthm collection-discover-again-is-idempotent
  (equal (collection-discover address (collection-discover address work))
         (collection-discover address work))
  :hints (("Goal" :in-theory (enable collection-discover))))
