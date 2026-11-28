(in-package "BOYMOO-PROOFS")

(include-book "tables")
(include-book "layout")
(include-book "placement")
(include-book "words")
(include-book "package-layout")

(logic)
(set-verify-guards-eagerness 0)

; Ordinary allocations refer to earlier addresses. The two symbols in
; the fixed header refer to their separately allocated name strings.
(defun data-static-rank (offset)
  (case offset
    (32 11)
    (56 13)
    (otherwise (nfix (ash offset -3)))))

(defun data-static-object-spans-p (objects base size machine)
  (if (atom objects)
      (null objects)
    (let* ((object (car objects))
           (address (proof-object-address object))
           (bytes (proof-object-size object machine)))
      (and (proof-object-record-p object)
           (eq (proof-object-zone object) :static)
           (equal (proof-object-rank object) (data-static-rank (- address base)))
           (proof-subspan-p address bytes (+ base 32) (+ base size))
           (proof-object-disjoint-p address (+ address bytes) (cdr objects) machine)
           (data-static-object-spans-p (cdr objects) base size machine)))))

(defun data-static-word-work (word depth)
  (list :word word depth))

(defun data-static-fields-work (address count depth)
  (list :fields address count depth))

(defun data-static-header-work (object pending machine)
  (let* ((address (proof-object-address object))
         (rank (proof-object-rank object)))
    (if (eq (proof-object-kind object) :cons)
        (mv t (cons (data-static-fields-work address 2 rank) pending))
      (let* ((header (proof-load-word address machine))
             (size (proof-header-size header))
             (payload (+ 8 address)))
        (case (proof-header-type header)
          ((1 3) (mv t pending))
          ((2 4 5)
           (mv (equal size 16) (cons (data-static-fields-work payload 2 rank) pending)))
          (6 (mv (equal (mod size 8) 0)
                 (cons (data-static-fields-work payload (ash size -3) rank) pending)))
          (otherwise (mv nil pending)))))))

(defun data-static-word-step (word depth pending objects base size machine)
  (let ((tag (proof-word-tag word)))
    (cond ((not (unsigned-byte-p 64 word)) (mv nil pending objects))
          ((oddp word) (mv t pending objects))
          ((equal tag 4) (mv (unsigned-byte-p 8 (ash word -3)) pending objects))
          ((not (member-equal tag '(0 2))) (mv nil pending objects))
          (t
           (let* ((address (proof-pointer-address word base))
                  (rank (data-static-rank (- address base)))
                  (kind (if (equal tag 0) :cons :header))
                  (old (assoc-equal address objects)))
             (cond ((not (< rank depth)) (mv nil pending objects))
                   (old (mv (eq (proof-object-kind old) kind) pending objects))
                   (t
                    (let* ((object (proof-object address :static kind rank))
                           (bytes (proof-object-size object machine)))
                      (if (and (proof-object-record-p object)
                               (proof-subspan-p address bytes (+ base 32) (+ base size))
                               (proof-object-disjoint-p address (+ address bytes) objects machine))
                          (mv-let (ok pending)
                            (data-static-header-work object pending machine)
                            (mv ok pending (if ok (cons object objects) objects)))
                        (mv nil pending objects))))))))))

(defun data-static-scan-step (task pending objects base size machine)
  (case (car task)
    (:word (data-static-word-step (cadr task) (caddr task) pending objects base size machine))
    (:fields
     (let ((address (cadr task)) (count (caddr task)) (depth (cadddr task)))
       (if (zp count)
           (mv t pending objects)
         (mv t (list* (data-static-word-work (proof-load-word address machine) depth)
                      (data-static-fields-work (+ address 8) (1- count) depth)
                      pending)
             objects))))
    (otherwise (mv nil pending objects))))

(defun data-static-scan (pending objects base size machine fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((atom pending) (mv (null pending) objects))
        ((zp fuel) (mv nil objects))
        (t
         (mv-let (ok pending objects)
           (data-static-scan-step (car pending) (cdr pending) objects base size machine)
           (if ok (data-static-scan pending objects base size machine (1- fuel))
             (mv nil objects))))))

(defun data-static-constant-work (bindings depth)
  (if (atom bindings)
      nil
    (cons (data-static-word-work (proof-constant-word (cdar bindings)) depth)
          (data-static-constant-work (cdr bindings) depth))))

(defun data-static-image-work (base size bindings)
  (let ((depth (+ 1 (nfix (ash size -3)))))
    (list* (data-static-word-work *proof-nil* depth)
           (data-static-word-work *proof-t* depth)
           (data-static-fields-work (+ base 8) 2 depth)
           (data-static-constant-work bindings depth))))

(defun data-static-image-map (base image constants machine)
  (let* ((size (car image))
         (bindings (data-table-bindings constants 12))
         (pending (data-static-image-work base size bindings)))
    (data-static-scan pending nil base size machine (+ 16 (nfix size) (len bindings)))))

(local
 (in-theory (disable data-static-header-work data-static-rank proof-object-record-p
                     proof-object-size proof-object-disjoint-p proof-subspan-p
                     proof-word-tag proof-pointer-address proof-load-word ash)))

(local
 (defthm static-object-spans-after-word-step
   (implies (data-static-object-spans-p objects base size machine)
            (data-static-object-spans-p
             (mv-nth 2 (data-static-word-step word depth pending objects base size machine))
             base size machine))))

(defthm data-static-object-spans-after-scan-step
  (implies (data-static-object-spans-p objects base size machine)
           (data-static-object-spans-p
            (mv-nth 2 (data-static-scan-step task pending objects base size machine))
            base size machine))
  :hints (("Goal" :in-theory (disable data-static-word-step data-static-object-spans-p))))

(local
 (defthm static-object-spans-after-scan
   (implies (data-static-object-spans-p objects base size machine)
            (data-static-object-spans-p (mv-nth 1 (data-static-scan pending objects base size machine fuel))
                                        base size machine))
   :hints (("Goal" :induct (data-static-scan pending objects base size machine fuel)
                   :in-theory (disable data-static-scan-step data-static-object-spans-p)))))

(defthm data-static-image-map-has-static-spans
  (data-static-object-spans-p (mv-nth 1 (data-static-image-map base image constants machine))
                             base (car image) machine)
  :hints (("Goal" :in-theory (disable data-static-scan))))

(defthm data-static-map-filter-is-identity
  (implies (data-static-object-spans-p objects base size machine)
           (equal (proof-static-objects objects) objects)))

(defthm data-static-map-meets-foundation-spans
  (implies (data-static-object-spans-p objects base size machine)
           (proof-static-spans-p objects base size machine)))

(defthmd data-build-map-and-initial-root
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (constants (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))
         (objects (mv-nth 1 (data-static-image-map base image constants machine))))
    (implies (proof-image-at-p image base machine)
             (and (equal (proof-dynamic-root base machine) *proof-nil*)
                  (equal (proof-static-objects objects) objects)
                  (proof-static-spans-p objects base (car image) machine))))
  :hints (("Goal" :use ((:instance data-static-map-filter-is-identity
                                   (objects (mv-nth 1 (data-static-image-map
                                                      base (car (boymoo-compiler::data-build lines package-lines))
                                                      (mv-nth 1 (boymoo-compiler::data-build lines package-lines))
                                                      machine)))
                                   (size (car (car (boymoo-compiler::data-build lines package-lines))))))
                  :in-theory (e/d (data-build-has-empty-dynamic-root)
                                 (boymoo-compiler::data-build data-static-image-map proof-image-at-p
                                  proof-static-spans-p proof-static-objects proof-dynamic-root)))))

; These are the interpretation obligations for the independently
; constructed map. The placed image supplies the size and root words.
(defun data-static-views-p (base objects packages machine)
  (let* ((package-word (proof-load-word (+ base 8) machine))
         (bucket-word (proof-load-word (+ base 16) machine))
         (buckets (proof-view bucket-word base objects packages machine)))
    (and (proof-packages-p packages)
         (proof-object-map-p objects objects nil base packages machine)
         (proof-value-p *proof-nil* nil base objects packages machine)
         (proof-value-p *proof-t* t base objects packages machine)
         (equal (proof-view package-word base objects packages machine)
                (cons :vector (proof-package-row-views packages)))
         (eq (car buckets) :vector)
         (proof-static-buckets-p (cdr buckets) 0 packages)
         (proof-home-bindings-p objects base objects packages machine (cdr buckets))
         (proof-package-bindings-p packages 0 (cdr buckets)))))

(local
 (defthm placed-image-has-aligned-size-and-header
   (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
          (size (car image)))
     (implies (proof-image-at-p image base machine)
              (and (<= 80 size) (equal (mod size 8) 0))))
   :hints (("Goal" :use (data-image-produced-by-data-build-has-header
                        data-build-fragment-count-agreement data-build-declared-size-is-word-aligned)
                   :in-theory (disable boymoo-compiler::data-build data-image-parts data-chunks-size
                                       proof-fragments-size proof-fragments-p proof-fragments-at-p
                                       data-image-produced-by-data-build-has-header mod)))))

(defthmd data-build-initial-static-under-view-obligations
  (let* ((image (car (boymoo-compiler::data-build lines package-lines)))
         (constants (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))
         (objects (mv-nth 1 (data-static-image-map base image constants machine)))
         (size (car image)))
    (implies (and (proof-image-at-p image base machine)
                  (< size *proof-space-size*) (equal (mod base 8) 0)
                  (data-static-views-p base objects packages machine))
             (proof-static-initial-p base objects packages machine)))
  :hints (("Goal" :use (data-build-map-and-initial-root data-build-loads-static-size
                       placed-image-has-aligned-size-and-header)
                  :in-theory (disable boymoo-compiler::data-build data-static-image-map
                                      proof-static-spans-p proof-static-objects proof-dynamic-root
                                      proof-static-size proof-fragments-at-p proof-fragments-size
                                      proof-fragments-p proof-span-p proof-view proof-value-p
                                      proof-object-map-p proof-static-buckets-p proof-packages-p
                                      proof-home-bindings-p proof-package-bindings-p mod))))
