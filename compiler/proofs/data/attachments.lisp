(in-package "BOYMOO-PROOFS")

(include-book "index")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::index-set data-table-p)))

(defun data-attachment-edge (name attachments)
  (and (not (data-protected-name-p name))
       (boymoo-compiler::index-get name attachments)))

; A path includes the terminal target and has one edge per preceding name.
(defun data-attachment-path-p (path attachments)
  (and (consp path) (stringp (car path))
       (let ((next (data-attachment-edge (car path) attachments)))
         (if next
             (and (equal next (cadr path))
                  (data-attachment-path-p (cdr path) attachments))
           (null (cdr path))))))

(defun data-attachment-terminal (path)
  (if (consp (cdr path)) (data-attachment-terminal (cdr path)) (car path)))

(defun data-attachment-cache-p (path target resolved)
  (if (atom path)
      t
    (let ((cached (boymoo-compiler::index-get (car path) resolved)))
      (and (or (not cached) (equal cached target))
           (data-attachment-cache-p (cdr path) target resolved)))))

(defun data-attachment-cache-prefix (path resolved)
  (if (or (atom (cdr path)) (boymoo-compiler::index-get (car path) resolved))
      nil
    (cons (car path) (data-attachment-cache-prefix (cdr path) resolved))))

(local
 (defthm data-attachment-path-is-string-list
   (implies (data-attachment-path-p path attachments)
            (and (consp path) (stringp (car path)) (string-listp path)))
   :rule-classes ((:forward-chaining :trigger-terms ((data-attachment-path-p path attachments))))))

(local
 (defthm terminal-of-string-path-is-string
   (implies (and (consp path) (string-listp path)) (stringp (data-attachment-terminal path)))))

(local
 (defthm terminal-on-attachment-path-is-string
   (implies (data-attachment-path-p path attachments)
            (stringp (data-attachment-terminal path)))
   :rule-classes :forward-chaining))

(local
 (defthm data-attachment-cache-unchanged-on-unrelated-set
   (implies (and (string-listp path) (stringp name) (data-table-p resolved 12)
                 (not (member-equal name path)))
            (equal (data-attachment-cache-p path target (boymoo-compiler::index-set name value resolved))
                   (data-attachment-cache-p path target resolved)))))

(local
 (defthm data-attachment-cache-prefix-unchanged-on-unrelated-set
   (implies (and (string-listp path) (stringp name) (data-table-p resolved 12)
                 (not (member-equal name path)))
            (equal (data-attachment-cache-prefix path (boymoo-compiler::index-set name value resolved))
                   (data-attachment-cache-prefix path resolved)))))

(local
 (defun data-resolve-chain-induction (path resolved fuel)
   (if (atom (cdr path))
       (list resolved fuel)
     (data-resolve-chain-induction (cdr path) (boymoo-compiler::index-set (car path) :pending resolved)
                                   (1- fuel)))))

(local
 (defthm resolve-chain-first-step
   (and (equal (car (boymoo-compiler::resolve-chain name attachments resolved fuel))
               (let ((cached (boymoo-compiler::index-get name resolved))
                     (next (data-attachment-edge name attachments)))
                 (cond ((equal cached :pending) nil)
                       (cached cached)
                       ((not next) name)
                       ((zp fuel) nil)
                       (t (car (boymoo-compiler::resolve-chain
                                next attachments (boymoo-compiler::index-set name :pending resolved)
                                (1- fuel)))))))
        (equal (mv-nth 1 (boymoo-compiler::resolve-chain name attachments resolved fuel))
               (let ((cached (boymoo-compiler::index-get name resolved))
                     (next (data-attachment-edge name attachments)))
                 (cond ((equal cached :pending) nil)
                       ((or cached (not next)) resolved)
                       ((zp fuel) nil)
                       (t (let ((tail (boymoo-compiler::resolve-chain
                                       next attachments (boymoo-compiler::index-set name :pending resolved)
                                       (1- fuel))))
                            (boymoo-compiler::index-set name (car tail) (mv-nth 1 tail))))))))
   :rule-classes nil
   :hints (("Goal" :expand ((boymoo-compiler::resolve-chain name attachments resolved fuel))))))

(local
 (in-theory (disable boymoo-compiler::resolve-chain data-attachment-edge data-protected-name-p)))

(defun data-resolution-pre-p (path attachments resolved fuel)
  (and (data-attachment-path-p path attachments) (no-duplicatesp-equal path)
       (<= (1- (len path)) (nfix fuel)) (data-table-p resolved 12)
       (data-attachment-cache-p path (data-attachment-terminal path) resolved)))

(local
 (defthm resolution-precondition-has-path
   (implies (data-resolution-pre-p path attachments resolved fuel)
            (data-attachment-path-p path attachments))
   :rule-classes :forward-chaining))

(defthmd data-resolve-chain-terminal
  (implies (data-resolution-pre-p path attachments resolved fuel)
           (let ((result (boymoo-compiler::resolve-chain (car path) attachments resolved fuel)))
             (and (equal (car result) (data-attachment-terminal path))
                  (data-table-p (mv-nth 1 result) 12))))
  :hints (("Goal" :induct (data-resolve-chain-induction path resolved fuel))
          ("Subgoal *1/1" :use ((:instance resolve-chain-first-step (name (car path)))))
          ("Subgoal *1/2" :use ((:instance resolve-chain-first-step (name (car path)))))))

(defthmd data-resolve-chain-cache-lookup
  (implies (and (data-resolution-pre-p path attachments resolved fuel) (stringp query))
           (equal (boymoo-compiler::index-get
                   query (mv-nth 1 (boymoo-compiler::resolve-chain (car path) attachments resolved fuel)))
                  (if (member-equal query (data-attachment-cache-prefix path resolved))
                      (data-attachment-terminal path)
                    (boymoo-compiler::index-get query resolved))))
  :hints (("Goal" :induct (data-resolve-chain-induction path resolved fuel))
          ("Subgoal *1/1" :use ((:instance resolve-chain-first-step (name (car path)))))
          ("Subgoal *1/2" :use ((:instance resolve-chain-first-step (name (car path)))
                                (:instance data-resolve-chain-terminal
                                           (path (cdr path))
                                           (resolved (boymoo-compiler::index-set (car path) :pending resolved))
                                           (fuel (1- fuel)))))))

(local
 (defun data-two-paths-induction (first second)
   (if (and (consp first) (consp second))
       (data-two-paths-induction (cdr first) (cdr second))
     nil)))

(defthm data-attachment-path-from-name-is-unique
  (implies (and (data-attachment-path-p first attachments)
                (data-attachment-path-p second attachments)
                (equal (car first) (car second)))
           (equal first second))
  :rule-classes nil
  :hints (("Goal" :induct (data-two-paths-induction first second))))

(local
 (defthm data-attachment-suffix
   (implies (and (data-attachment-path-p path attachments) (member-equal query path))
            (and (data-attachment-path-p (member-equal query path) attachments)
                 (equal (data-attachment-terminal (member-equal query path))
                        (data-attachment-terminal path))
                 (equal (car (member-equal query path)) query)))
   :rule-classes nil
   :hints (("Goal" :induct (member-equal query path)))))

(defthmd data-overlapping-attachment-paths-have-one-target
  (implies (and (data-attachment-path-p first attachments)
                (data-attachment-path-p second attachments)
                (member-equal query first) (member-equal query second))
           (equal (data-attachment-terminal first) (data-attachment-terminal second)))
  :hints (("Goal" :use ((:instance data-attachment-suffix (path first))
                       (:instance data-attachment-suffix (path second))
                       (:instance data-attachment-path-from-name-is-unique
                                  (first (member-equal query first))
                                  (second (member-equal query second))))
                  :in-theory (disable data-attachment-terminal data-attachment-path-p))))

(local
 (defthm cache-prefix-membership
   (implies (member-equal query (data-attachment-cache-prefix path resolved))
            (and (member-equal query path) (not (boymoo-compiler::index-get query resolved))))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((member-equal query (data-attachment-cache-prefix path resolved)))))
   :hints (("Goal" :induct (data-attachment-cache-prefix path resolved)))))

(defthmd data-resolve-chain-retains-cached-target
  (implies (and (data-resolution-pre-p path attachments resolved fuel) (stringp query)
                (boymoo-compiler::index-get query resolved))
           (equal (boymoo-compiler::index-get
                   query (mv-nth 1 (boymoo-compiler::resolve-chain (car path) attachments resolved fuel)))
                  (boymoo-compiler::index-get query resolved)))
  :hints (("Goal" :use data-resolve-chain-cache-lookup
                  :in-theory (disable data-resolution-pre-p))))

(defthmd data-resolve-chain-caches-source
  (implies (and (data-resolution-pre-p path attachments resolved fuel) (consp (cdr path)))
           (equal (boymoo-compiler::index-get
                   (car path) (mv-nth 1 (boymoo-compiler::resolve-chain
                                         (car path) attachments resolved fuel)))
                  (data-attachment-terminal path)))
  :hints (("Goal" :use ((:instance data-resolve-chain-cache-lookup (query (car path))))
                  :in-theory (disable data-attachment-path-p data-attachment-terminal))))

(local
 (defthm resolution-preserves-other-path-cache
   (implies (and (data-resolution-pre-p path attachments resolved fuel)
                 (data-attachment-path-p other attachments)
                 (equal target (data-attachment-terminal other))
                 (data-attachment-cache-p other target resolved))
            (data-attachment-cache-p
             other target (mv-nth 1 (boymoo-compiler::resolve-chain
                                     (car path) attachments resolved fuel))))
   :hints (("Goal" :induct (data-attachment-cache-p other target resolved)
                   :in-theory (e/d (data-resolve-chain-cache-lookup)
                                  (data-resolution-pre-p data-attachment-cache-prefix)))
           ("Subgoal *1/2" :use ((:instance data-overlapping-attachment-paths-have-one-target
                                             (first path) (second other) (query (car other))))))))

(defun data-source-attachment-paths-p (paths attachments fuel)
  (if (atom paths)
      (null paths)
    (and (data-attachment-path-p (car paths) attachments)
         (consp (cdar paths)) (no-duplicatesp-equal (car paths))
         (<= (1- (len (car paths))) (nfix fuel))
         (data-source-attachment-paths-p (cdr paths) attachments fuel))))

(defun data-resolved-paths-p (paths resolved)
  (if (atom paths)
      t
    (and (data-attachment-cache-p (car paths) (data-attachment-terminal (car paths)) resolved)
         (data-resolved-paths-p (cdr paths) resolved))))

(defun data-path-targets (paths)
  (if (atom paths)
      nil
    (cons (cons (caar paths) (data-attachment-terminal (car paths)))
          (data-path-targets (cdr paths)))))

(local
 (defthm resolution-preserves-path-caches
   (implies (and (data-resolution-pre-p path attachments resolved fuel)
                 (data-source-attachment-paths-p paths attachments fuel)
                 (data-resolved-paths-p paths resolved))
            (data-resolved-paths-p
             paths (mv-nth 1 (boymoo-compiler::resolve-chain
                                     (car path) attachments resolved fuel))))
   :hints (("Goal" :induct (data-resolved-paths-p paths resolved)
                   :in-theory (disable data-resolution-pre-p data-attachment-path-p
                                       data-attachment-cache-p data-attachment-terminal)))))

(local
 (defun data-attachment-pass-induction (paths attachments fuel resolved)
   (if (atom paths)
       resolved
     (mv-let (target next) (boymoo-compiler::resolve-chain (caar paths) attachments resolved fuel)
       (declare (ignore target))
       (data-attachment-pass-induction (cdr paths) attachments fuel next)))))

(defthmd data-attachment-pass-retains-cached-target
  (implies (and (data-source-attachment-paths-p paths attachments fuel)
                (data-table-p resolved 12) (data-resolved-paths-p paths resolved)
                (stringp query) (boymoo-compiler::index-get query resolved))
           (equal (boymoo-compiler::index-get
                   query (boymoo-compiler::resolve-attachments (strip-cars paths) attachments resolved fuel))
                  (boymoo-compiler::index-get query resolved)))
  :hints (("Goal" :induct (data-attachment-pass-induction paths attachments fuel resolved)
                  :in-theory (e/d (data-resolve-chain-terminal data-resolve-chain-retains-cached-target)
                                 (data-attachment-path-p data-attachment-terminal data-attachment-cache-p)))))

(defthmd data-attachment-pass-index-agreement
  (implies (and (data-source-attachment-paths-p paths attachments fuel)
                (data-table-p resolved 12) (data-resolved-paths-p paths resolved))
           (proof-index-agrees-p
            (data-path-targets paths)
            (boymoo-compiler::resolve-attachments (strip-cars paths) attachments resolved fuel)))
  :hints (("Goal" :induct (data-attachment-pass-induction paths attachments fuel resolved)
                  :in-theory (e/d (data-resolve-chain-terminal data-resolve-chain-caches-source
                                   data-attachment-pass-retains-cached-target)
                                 (data-attachment-path-p data-attachment-terminal data-attachment-cache-p)))))
