(in-package "BOYMOO-PROOFS")

(include-book "attachments")

(logic)
(set-verify-guards-eagerness 0)

; An order lists each source once. A target with a further attachment
; occurs later in the order, and a terminal target has no outgoing edge.
(defun data-attachment-order-p (order attachments)
  (if (atom order)
      (null order)
    (let ((next (data-attachment-edge (car order) attachments)))
      (and (stringp (car order)) (stringp next) (not (member-equal (car order) (cdr order)))
           (or (not (data-attachment-edge next attachments)) (member-equal next (cdr order)))
           (data-attachment-order-p (cdr order) attachments)))))

(defun data-attachment-path-in-order (name order attachments)
  (let ((next (data-attachment-edge name attachments)))
    (cond ((not next) (list name))
          ((atom order) nil)
          ((equal name (car order)) (cons name (data-attachment-path-in-order next (cdr order) attachments)))
          (t (data-attachment-path-in-order name (cdr order) attachments)))))

(defun data-path-sources-covered-p (path order attachments)
  (or (atom path)
      (and (or (not (data-attachment-edge (car path) attachments)) (member-equal (car path) order))
           (data-path-sources-covered-p (cdr path) order attachments))))

(local
 (in-theory (disable data-attachment-edge boymoo-compiler::index-get)))

(local
 (defthm extending-an-order-preserves-path-coverage
   (implies (data-path-sources-covered-p path order attachments)
            (data-path-sources-covered-p path (cons name order) attachments))))

(local
 (defthm covered-outgoing-source-is-in-order
   (implies (and (data-path-sources-covered-p path order attachments) (member-equal name path)
                 (data-attachment-edge name attachments))
            (member-equal name order))))

(defthmd data-attachment-order-yields-a-bounded-path
  (let ((path (data-attachment-path-in-order name order attachments)))
    (implies (and (stringp name) (data-attachment-order-p order attachments)
                  (or (not (data-attachment-edge name attachments)) (member-equal name order)))
             (and (consp path) (equal (car path) name)
                  (data-attachment-path-p path attachments) (no-duplicatesp-equal path)
                  (data-path-sources-covered-p path order attachments)
                  (implies (data-attachment-edge name attachments) (consp (cdr path)))
                  (<= (1- (len path)) (len order)))))
  :hints (("Goal" :induct (data-attachment-path-in-order name order attachments))
          ("Subgoal *1/3" :use ((:instance covered-outgoing-source-is-in-order (order (cdr order))
                                           (path (data-attachment-path-in-order
                                                  (data-attachment-edge name attachments) (cdr order) attachments))))
                          :in-theory (disable covered-outgoing-source-is-in-order))))

(defun data-attachment-sources-in-order-p (sources order)
  (if (atom sources)
      (null sources)
    (and (member-equal (car sources) order) (data-attachment-sources-in-order-p (cdr sources) order))))

(defun data-attachment-paths-in-order (sources order attachments)
  (if (atom sources)
      nil
    (cons (data-attachment-path-in-order (car sources) order attachments)
          (data-attachment-paths-in-order (cdr sources) order attachments))))

(local
 (defthm ordered-source-is-a-string-with-an-outgoing-edge
   (implies (and (data-attachment-order-p order attachments) (member-equal source order))
            (and (stringp source) (data-attachment-edge source attachments)))))

(defthmd data-ordered-attachment-paths-fit-resolution
  (let ((paths (data-attachment-paths-in-order sources order attachments)))
    (implies (and (data-attachment-order-p order attachments)
                  (data-attachment-sources-in-order-p sources order) (natp fuel) (<= (len order) fuel))
             (and (equal (strip-cars paths) sources)
                  (data-source-attachment-paths-p paths attachments fuel))))
  :hints (("Goal" :induct (data-attachment-paths-in-order sources order attachments)
                  :in-theory (disable data-attachment-path-in-order data-attachment-order-p
                                      data-attachment-path-p data-path-sources-covered-p))
          ("Subgoal *1/2" :use ((:instance data-attachment-order-yields-a-bounded-path (name (car sources)))
                                (:instance ordered-source-is-a-string-with-an-outgoing-edge (source (car sources))))
                          :in-theory (disable ordered-source-is-a-string-with-an-outgoing-edge
                                              data-attachment-path-in-order data-attachment-order-p
                                              data-attachment-path-p data-path-sources-covered-p))))

(local
 (defthm absent-cache-agrees-with-a-path
   (data-attachment-cache-p path target nil)))

(local
 (defthm absent-cache-agrees-with-all-paths
   (data-resolved-paths-p paths nil)))

(defthmd data-resolving-ordered-attachments-with-configured-fuel
  (let ((paths (data-attachment-paths-in-order sources order attachments)))
    (implies (and (data-attachment-order-p order attachments)
                  (data-attachment-sources-in-order-p sources order) (<= (len order) (len sources)))
             (proof-index-agrees-p
              (data-path-targets paths)
              (boymoo-compiler::resolve-attachments sources attachments nil (len sources)))))
  :hints (("Goal" :use ((:instance data-ordered-attachment-paths-fit-resolution (fuel (len sources)))
                        (:instance data-attachment-pass-index-agreement
                                   (paths (data-attachment-paths-in-order sources order attachments))
                                   (resolved nil) (fuel (len sources))))
                  :in-theory (disable data-attachment-paths-in-order data-attachment-order-p
                                      data-attachment-sources-in-order-p data-source-attachment-paths-p
                                      data-path-targets boymoo-compiler::resolve-attachments proof-index-agrees-p))))
