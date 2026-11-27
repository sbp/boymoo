(in-package "BOYMOO-PROOFS")

(include-book "attachment-budget")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm removing-a-source-reduces-list-length
   (and (<= (len (remove-equal name sources)) (len sources))
        (implies (member-equal name sources) (< (len (remove-equal name sources)) (len sources))))
   :rule-classes :linear))

; The walk consumes each used source once. If the walk stops on an
; outgoing edge, its last name was absent from the remaining sources.
(defun data-attachment-walk (name attachments sources)
  (declare (xargs :measure (len sources)))
  (let ((next (data-attachment-edge name attachments)))
    (if (and next (member-equal name sources))
        (cons name (data-attachment-walk next attachments (remove-equal name sources)))
      (list name))))

(local
 (in-theory (disable data-attachment-edge boymoo-compiler::index-get data-protected-name-p
                     remove-equal data-attachment-path-p)))

(defthm data-attachment-walk-starts-with-the-query
  (and (consp (data-attachment-walk name attachments sources))
       (equal (car (data-attachment-walk name attachments sources)) name)))

(defthmd data-attachment-walk-fits-source-budget
  (<= (1- (len (data-attachment-walk name attachments sources))) (len sources))
  :rule-classes :linear
  :hints (("Goal" :induct (data-attachment-walk name attachments sources))))

(local
 (defthm removing-another-source-preserves-membership
   (implies (not (equal name removed))
            (iff (member-equal name (remove-equal removed sources)) (member-equal name sources)))
   :hints (("Goal" :in-theory (enable remove-equal)))))

(local
 (defthm removing-a-name-outside-a-path-preserves-coverage
   (implies (and (data-path-sources-covered-p path sources attachments) (not (member-equal name path)))
            (data-path-sources-covered-p path (remove-equal name sources) attachments))))

(defthmd data-covered-acyclic-attachment-walk-is-a-terminal-path
  (let ((path (data-attachment-walk name attachments sources)))
    (implies (and (no-duplicatesp-equal path) (string-listp path)
                  (data-path-sources-covered-p path sources attachments))
             (data-attachment-path-p path attachments)))
  :hints (("Goal" :induct (data-attachment-walk name attachments sources)
                  :expand ((data-attachment-path-p (list name) attachments)
                           (data-attachment-path-p
                            (cons name (data-attachment-walk (data-attachment-edge name attachments)
                                                            attachments (remove-equal name sources)))
                            attachments)))))

(defun data-attachment-walks (names attachments sources)
  (if (atom names)
      nil
    (cons (data-attachment-walk (car names) attachments sources)
          (data-attachment-walks (cdr names) attachments sources))))

(defun data-acyclic-attachment-walks-p (paths)
  (if (atom paths)
      (null paths)
    (and (no-duplicatesp-equal (car paths)) (data-acyclic-attachment-walks-p (cdr paths)))))

(defthm data-attachment-walks-start-with-the-queries
  (implies (true-listp names)
           (equal (strip-cars (data-attachment-walks names attachments sources)) names))
  :hints (("Goal" :induct (data-attachment-walks names attachments sources)
                  :in-theory (disable data-attachment-walk))))

(local
 (in-theory (disable data-attachment-walk)))

(local
 (defthm latest-attachment-from-an-indexable-source-is-a-string
   (implies (and (data-indexable-lines-p lines entry target) (data-latest-attachment name lines))
            (stringp (data-latest-attachment name lines)))
   :hints (("Goal" :induct (data-indexable-lines-p lines entry target)
                   :in-theory (disable data-indexable-definitions-p)))))

(defthmd data-latest-attachment-source-is-unprotected
  (implies (and (data-indexable-lines-p lines entry target) (data-latest-attachment name lines))
           (not (data-protected-name-p name)))
  :hints (("Goal" :induct (data-indexable-lines-p lines entry target)
                  :in-theory (disable data-indexable-definitions-p))))

(defthmd data-indexed-attachment-edges-are-string-targets
  (let* ((pass (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
         (attachments (mv-nth 2 pass))
         (next (data-attachment-edge name attachments)))
    (implies (and (data-indexable-lines-p lines nil nil) (stringp name) next) (stringp next)))
  :hints (("Goal" :use ((:instance data-index-lines-latest-attachment
                                   (query name) (definitions nil) (arities nil) (attachments nil)
                                   (sources nil) (packages nil) (entry nil) (target nil))
                        (:instance latest-attachment-from-an-indexable-source-is-a-string (entry nil) (target nil)))
                  :in-theory (e/d (data-attachment-edge)
                                 (boymoo-compiler::index-lines data-latest-attachment data-indexable-lines-p
                                  latest-attachment-from-an-indexable-source-is-a-string)))))

(defthmd data-indexed-attachment-edges-have-listed-sources
  (let* ((pass (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
         (attachments (mv-nth 2 pass))
         (sources (mv-nth 3 pass)))
    (implies (and (data-indexable-lines-p lines nil nil) (stringp name) (data-attachment-edge name attachments))
             (member-equal name sources)))
  :hints (("Goal" :use ((:instance data-index-lines-latest-attachment
                                   (query name) (definitions nil) (arities nil) (attachments nil)
                                   (sources nil) (packages nil) (entry nil) (target nil))
                        (:instance data-index-lines-attachment-sources
                                   (query name) (definitions nil) (arities nil) (attachments nil)
                                   (sources nil) (packages nil) (entry nil) (target nil)))
                  :in-theory (e/d (data-attachment-edge)
                                 (boymoo-compiler::index-lines data-latest-attachment data-indexable-lines-p)))))

(defthmd data-listed-attachment-source-has-an-edge
  (let* ((pass (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
         (attachments (mv-nth 2 pass))
         (sources (mv-nth 3 pass)))
    (implies (and (data-indexable-lines-p lines nil nil) (stringp name) (member-equal name sources))
             (data-attachment-edge name attachments)))
  :hints (("Goal" :use ((:instance data-index-lines-latest-attachment
                                   (query name) (definitions nil) (arities nil) (attachments nil)
                                   (sources nil) (packages nil) (entry nil) (target nil))
                        (:instance data-index-lines-attachment-sources
                                   (query name) (definitions nil) (arities nil) (attachments nil)
                                   (sources nil) (packages nil) (entry nil) (target nil))
                        (:instance data-latest-attachment-source-is-unprotected (entry nil) (target nil)))
                  :in-theory (e/d (data-attachment-edge)
                                 (boymoo-compiler::index-lines data-latest-attachment data-indexable-lines-p)))))

(local
 (defthm index-pass-sources-are-strings
   (implies (and (data-indexable-lines-p lines entry target) (string-listp sources) (true-listp sources))
            (let ((listed (mv-nth 3 (boymoo-compiler::index-lines
                                     lines definitions arities attachments sources packages entry target))))
              (and (string-listp listed) (true-listp listed))))
   :hints (("Goal" :induct (boymoo-compiler::index-lines
                             lines definitions arities attachments sources packages entry target)
                   :in-theory (disable boymoo-compiler::index-definitions data-indexable-definitions-p)))))

(local
 (in-theory (disable boymoo-compiler::index-lines data-indexable-lines-p)))

(defthmd data-indexed-attachment-sources-are-strings
  (implies (data-indexable-lines-p lines nil nil)
           (let ((listed (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
             (and (string-listp listed) (true-listp listed)))))

(local
 (defthm indexed-attachment-walk-is-a-covered-string-path
   (let* ((pass (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
          (attachments (mv-nth 2 pass))
          (sources (mv-nth 3 pass))
          (path (data-attachment-walk name attachments remaining)))
     (implies (and (data-indexable-lines-p lines nil nil) (stringp name))
              (and (string-listp path) (data-path-sources-covered-p path sources attachments))))
   :rule-classes nil
   :hints (("Goal" :induct (data-attachment-walk name (mv-nth 2 (boymoo-compiler::index-lines
                                                                lines nil nil nil nil nil nil nil)) remaining)
                   :in-theory (enable (:induction data-attachment-walk)
                                      data-indexed-attachment-edges-are-string-targets
                                      data-indexed-attachment-edges-have-listed-sources)
                   :expand ((:free (attachments) (data-attachment-walk name attachments remaining)))))))

(local
 (defthm a-terminal-path-starting-with-an-edge-has-a-second-name
   (implies (and (data-attachment-path-p path attachments) (data-attachment-edge (car path) attachments))
            (consp (cdr path)))
   :hints (("Goal" :expand ((data-attachment-path-p path attachments))))))

(defthmd data-indexed-attachment-walks-fit-resolution
  (let* ((pass (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
         (attachments (mv-nth 2 pass))
         (sources (mv-nth 3 pass))
         (paths (data-attachment-walks names attachments sources)))
    (implies (and (data-indexable-lines-p lines nil nil) (string-listp names) (subsetp-equal names sources)
                  (data-acyclic-attachment-walks-p paths))
             (data-source-attachment-paths-p paths attachments (len sources))))
  :hints (("Goal" :induct (data-attachment-walks
                            names (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                            (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)))
                  :in-theory (disable data-path-sources-covered-p))
          ("Subgoal *1/2"
           :use ((:instance data-listed-attachment-source-has-an-edge (name (car names)))
                 (:instance indexed-attachment-walk-is-a-covered-string-path
                            (name (car names))
                            (remaining (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
                 (:instance data-covered-acyclic-attachment-walk-is-a-terminal-path
                            (name (car names))
                            (attachments (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)))
                            (sources (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
                 (:instance data-attachment-walk-fits-source-budget
                            (name (car names))
                            (attachments (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)))
                            (sources (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))))))

(local
 (defthm empty-cache-agrees-with-every-walk
   (and (data-attachment-cache-p path target nil) (data-resolved-paths-p paths nil))))

(local
 (defthm superset-can-have-an-extra-source
   (implies (subsetp-equal names sources)
            (subsetp-equal names (cons extra sources)))))

(local
 (defthm subset-of-self-for-attachment-sources
   (subsetp-equal sources sources)))

(defthmd data-resolve-indexed-acyclic-attachments-with-configured-fuel
  (let* ((pass (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
         (attachments (mv-nth 2 pass))
         (sources (mv-nth 3 pass))
         (paths (data-attachment-walks sources attachments sources)))
    (implies (and (data-indexable-lines-p lines nil nil) (data-acyclic-attachment-walks-p paths))
             (proof-index-agrees-p
              (data-path-targets paths)
              (boymoo-compiler::resolve-attachments sources attachments nil (len sources)))))
  :hints (("Goal" :use (data-indexed-attachment-sources-are-strings
                        (:instance data-indexed-attachment-walks-fit-resolution
                                   (names (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
                        (:instance data-attachment-pass-index-agreement
                                   (attachments (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)))
                                   (paths (data-attachment-walks
                                           (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                                           (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                                           (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
                                   (resolved nil)
                                   (fuel (len (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))))
                  :in-theory (disable data-attachment-walks data-acyclic-attachment-walks-p
                                      data-source-attachment-paths-p data-path-targets data-resolved-paths-p
                                      boymoo-compiler::resolve-attachments proof-index-agrees-p))))

(defun data-indexed-attachments-acyclic-p (lines)
  (mv-let (definitions arities attachments sources packages entry target)
    (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)
    (declare (ignore definitions arities packages entry target))
    (data-acyclic-attachment-walks-p (data-attachment-walks sources attachments sources))))

(local
 (defthm walk-from-a-listed-source-is-a-listed-walk
   (implies (member-equal name names)
            (member-equal (data-attachment-walk name attachments sources)
                          (data-attachment-walks names attachments sources)))))

(local
 (defthm listed-resolution-path-is-a-terminal-path
   (implies (and (data-source-attachment-paths-p paths attachments fuel) (member-equal path paths))
            (data-attachment-path-p path attachments))))

(local
 (defthm resolution-index-gives-the-target-of-a-listed-path
   (implies (and (proof-index-agrees-p (data-path-targets paths) resolved) (member-equal path paths))
            (equal (boymoo-compiler::index-get (car path) resolved) (data-attachment-terminal path)))
   :hints (("Goal" :induct (data-path-targets paths) :in-theory (disable data-attachment-terminal)))))

(defthmd data-indexed-walk-is-terminal-and-gives-resolved-target
  (let* ((pass (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
         (attachments (mv-nth 2 pass))
         (sources (mv-nth 3 pass))
         (path (data-attachment-walk name attachments sources))
         (resolved (boymoo-compiler::resolve-attachments sources attachments nil (len sources))))
    (implies (and (data-indexable-lines-p lines nil nil) (data-indexed-attachments-acyclic-p lines)
                  (member-equal name sources))
             (and (data-attachment-path-p path attachments)
                  (equal (boymoo-compiler::index-get name resolved) (data-attachment-terminal path)))))
  :hints (("Goal" :use (data-indexed-attachment-sources-are-strings
                        (:instance data-indexed-attachment-walks-fit-resolution
                                   (names (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
                        data-resolve-indexed-acyclic-attachments-with-configured-fuel
                        (:instance resolution-index-gives-the-target-of-a-listed-path
                                   (path (data-attachment-walk
                                          name
                                          (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                                          (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
                                   (paths (data-attachment-walks
                                           (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                                           (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                                           (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))))
                                   (resolved (boymoo-compiler::resolve-attachments
                                              (mv-nth 3 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                                              (mv-nth 2 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil))
                                              nil (len (mv-nth 3 (boymoo-compiler::index-lines
                                                                  lines nil nil nil nil nil nil nil)))))))
                  :in-theory (disable data-attachment-walks data-acyclic-attachment-walks-p
                                      data-source-attachment-paths-p data-path-targets data-attachment-terminal
                                      resolution-index-gives-the-target-of-a-listed-path
                                      boymoo-compiler::resolve-attachments proof-index-agrees-p))))
