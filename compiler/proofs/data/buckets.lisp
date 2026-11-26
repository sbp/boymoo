(in-package "BOYMOO-PROOFS")

(include-book "layout")
(include-book "tables")
(include-book "bits")
(include-book "hash")
(include-book "placement")

(logic)
(set-verify-guards-eagerness 0)

(defun data-bucket-for-name (number name)
  (boymoo-compiler::low-bits (+ (boymoo-compiler::text-hash name) (* 7919 number)) 12))

(defun data-bucket-low-branch-p (bucket next)
  (equal (boymoo-compiler::low-bits (ash bucket (- next)) 1) 0))

(defun data-bucket-same-path-p (first second bits)
  (declare (xargs :measure (nfix bits)))
  (or (zp bits)
      (and (equal (data-bucket-low-branch-p first (1- bits))
                  (data-bucket-low-branch-p second (1- bits)))
           (data-bucket-same-path-p first second (1- bits)))))

(local
 (in-theory (disable ash boymoo-compiler::low-bits boymoo-compiler::text-hash)))

(defthm data-bucket-lookup-after-set
  (equal (boymoo-compiler::bucket-get query bits (boymoo-compiler::bucket-set bucket bits word tree))
         (if (data-bucket-same-path-p query bucket bits) word
           (boymoo-compiler::bucket-get query bits tree)))
  :hints (("Goal" :induct (boymoo-compiler::bucket-set bucket bits word tree))))

(defun data-static-bucket-tree-p (tree bits)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom tree) (null tree))
        ((zp bits) (and (null (cdr tree)) (not (stringp (car tree)))))
        (t (and (data-static-bucket-tree-p (car tree) (1- bits))
                (data-static-bucket-tree-p (cdr tree) (1- bits))))))

(defthm data-bucket-tree-p-after-set
  (implies (and (data-static-bucket-tree-p tree bits) (not (stringp word)))
           (data-static-bucket-tree-p (boymoo-compiler::bucket-set bucket bits word tree) bits))
  :hints (("Goal" :induct (boymoo-compiler::bucket-set bucket bits word tree))))

(defun data-ascending-bucket-words (tree bits)
  (declare (xargs :measure (nfix bits)))
  (if (zp bits)
      (list (if tree (car tree) *proof-nil*))
    (append (data-ascending-bucket-words (car tree) (1- bits))
            (data-ascending-bucket-words (cdr tree) (1- bits)))))

(local
 (defthm data-words-over-append
   (equal (boymoo-compiler::data-words (append first second) block)
          (boymoo-compiler::data-words second (boymoo-compiler::data-words first block)))
   :hints (("Goal" :induct (boymoo-compiler::data-words first block)
                   :in-theory (disable boymoo-compiler::data-word)))))

(defthmd data-bucket-vector-serializes-ascending-leaves
  (equal (boymoo-compiler::data-bucket-vector tree bits block)
         (boymoo-compiler::data-words (data-ascending-bucket-words tree bits) block))
  :hints (("Goal" :induct (boymoo-compiler::data-bucket-vector tree bits block)
                  :in-theory (disable boymoo-compiler::data-word))))

(local
 (defthm length-of-appended-bucket-lists
   (equal (len (append first second)) (+ (len first) (len second)))))

(local
 (defthm bucket-power-of-two-step
   (implies (posp bits) (equal (expt 2 bits) (* 2 (expt 2 (1- bits)))))
   :rule-classes nil
   :hints (("Goal" :expand ((expt 2 bits))))))

(defthm data-bucket-vector-contains-one-word-per-path
  (equal (len (data-ascending-bucket-words tree bits)) (expt 2 (nfix bits)))
  :hints (("Goal" :induct (data-ascending-bucket-words tree bits) :in-theory (disable expt))
          ("Subgoal *1/2" :use bucket-power-of-two-step)))

(defun data-bucket-path-position (bucket bits)
  (declare (xargs :measure (nfix bits)))
  (if (zp bits)
      0
    (let ((next (1- bits)))
      (+ (if (data-bucket-low-branch-p bucket next) 0 (expt 2 next))
         (data-bucket-path-position bucket next)))))

(defthm data-bucket-path-position-in-range
  (and (natp (data-bucket-path-position bucket bits))
       (< (data-bucket-path-position bucket bits) (expt 2 (nfix bits))))
  :hints (("Goal" :induct (data-bucket-path-position bucket bits) :in-theory (disable expt))
          ("Subgoal *1/2" :use bucket-power-of-two-step)))

(local
 (defthm nth-from-first-bucket-list
   (implies (and (natp index) (< index (len first)))
            (equal (nth index (append first second)) (nth index first)))))

(local
 (defthm nth-from-second-bucket-list
   (implies (and (natp index) (<= (len first) index))
            (equal (nth index (append first second)) (nth (- index (len first)) second)))
   :hints (("Goal" :induct (nth index first)))))

(local
 (defthm cancel-bucket-prefix-length
   (implies (and (acl2-numberp offset) (acl2-numberp index))
            (equal (+ offset (- offset) index) index))
   :hints (("Goal" :use ((:instance associativity-of-+ (acl2::x offset)
                                    (acl2::y (- offset)) (acl2::z index)))
                   :in-theory (disable associativity-of-+)))))

(defthmd data-bucket-vector-path-lookup
  (implies (data-static-bucket-tree-p tree bits)
           (equal (nth (data-bucket-path-position bucket bits)
                       (data-ascending-bucket-words tree bits))
                  (boymoo-compiler::bucket-get bucket bits tree)))
  :hints (("Goal" :induct (data-ascending-bucket-words tree bits)
                  :in-theory (disable expt data-low-bit-parity))
          ("Subgoal *1/2" :use ((:instance data-bucket-path-position-in-range (bits (1- bits))))
                          :in-theory (disable data-bucket-path-position-in-range))))

(local
 (defthm split-bucket-high-bit
   (implies (and (integerp bucket) (posp bits))
            (equal (boymoo-compiler::low-bits bucket bits)
                   (+ (boymoo-compiler::low-bits bucket (1- bits))
                      (* (expt 2 (1- bits))
                         (boymoo-compiler::low-bits (ash bucket (- 1 bits)) 1)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-low-bits-of-two-fields
                                    (word bucket) (lower (1- bits)) (upper 1)))
                   :in-theory (disable floor expt data-low-bit-parity)))))

(defthmd data-bucket-position-is-low-bits
  (implies (and (integerp bucket) (natp bits))
           (equal (data-bucket-path-position bucket bits)
                  (boymoo-compiler::low-bits bucket bits)))
  :hints (("Goal" :induct (data-bucket-path-position bucket bits)
                  :in-theory (disable floor expt))
          ("Subgoal *1/2" :use (split-bucket-high-bit))
          ("Subgoal *1/1" :use ((:instance data-low-bits-remainder (word bucket) (width 0))))))

(defthmd data-bucket-vector-number-lookup
  (implies (and (data-static-bucket-tree-p tree bits) (natp bits) (unsigned-byte-p bits bucket))
           (equal (nth bucket (data-ascending-bucket-words tree bits))
                  (boymoo-compiler::bucket-get bucket bits tree)))
  :hints (("Goal" :use (data-bucket-vector-path-lookup data-bucket-position-is-low-bits)
                  :in-theory (disable data-static-bucket-tree-p boymoo-compiler::bucket-get))))

(defthmd data-bucket-vector-home-or-import-lookup
  (implies (and (stringp name) (natp package) (data-static-bucket-tree-p tree 12))
           (equal (nth (proof-symbol-hash package name 12) (data-ascending-bucket-words tree 12))
                  (boymoo-compiler::bucket-get (data-bucket-for-name package name) 12 tree)))
  :hints (("Goal" :use ((:instance data-compiler-bucket-hash-agrees (number package))
                       (:instance data-bucket-vector-number-lookup
                                  (bits 12) (bucket (proof-symbol-hash package name 12))))
                  :in-theory (disable data-static-bucket-tree-p boymoo-compiler::bucket-get
                                      proof-hash-characters boymoo-model::a64-unsigned
                                      unsigned-byte-p))))

(local
 (in-theory (disable boymoo-compiler::bucket-get boymoo-compiler::bucket-set
                    boymoo-compiler::data-text boymoo-compiler::data-fields
                    boymoo-compiler::table-get boymoo-compiler::table-put
                    boymoo-compiler::data-bucket-vector)))

(defthmd data-bucket-add-publishes-three-cells
  (let* ((block (boymoo-compiler::data-block state-data))
         (start (car block))
         (old (boymoo-compiler::bucket-get (data-bucket-for-name package name) 12 (caddr state-data)))
         (next (boymoo-compiler::data-bucket-add package name name-word symbol-word state-data)))
    (implies (natp start)
             (and (equal (boymoo-compiler::data-block next)
                         (cons (+ start 48)
                               (list* old (+ start 16) symbol-word start name-word
                                      (+ 1 (* 2 package)) (cdr block))))
                  (equal (caddr next)
                         (boymoo-compiler::bucket-set
                          (data-bucket-for-name package name) 12 (+ start 32) (caddr state-data)))))))

(defthm data-bucket-add-keeps-name-and-constant-tables
  (let ((next (boymoo-compiler::data-bucket-add package name name-word symbol-word state-data)))
    (and (equal (car next) (car state-data)) (equal (cadr next) (cadr state-data)))))

(local
 (in-theory (disable boymoo-compiler::data-bucket-add)))

(defun data-name-table-lookup (package name state-data)
  (boymoo-compiler::table-get (cons package name)
                             (+ (boymoo-compiler::text-hash name) (* 7919 package))
                             12 (car state-data)))

(defthmd data-intern-reuses-owned-name
  (let ((binding (data-name-table-lookup package name state-data)))
    (implies (and binding (not (eq (car binding) :import)))
             (equal (mv-list 3 (boymoo-compiler::data-intern package name state-data))
                    (list (car binding) (cdr binding) state-data)))))

(defthmd data-intern-publishes-owned-name
  (implies (and (natp package) (stringp name) (data-table-p (car state-data) 12)
                (not (data-name-table-lookup package name state-data)))
           (mv-let (symbol-word name-word next) (boymoo-compiler::data-intern package name state-data)
             (and (equal (data-name-table-lookup package name next) (cons symbol-word name-word))
                  (data-table-p (car next) 12))))
  :hints (("Goal" :in-theory (disable data-table-p))))

(local
 (defthm package-name-get-after-put
   (let ((query (cons query-package query-name))
         (key (cons package name))
         (query-hash (+ (boymoo-compiler::text-hash query-name) (* 7919 query-package)))
         (hash (+ (boymoo-compiler::text-hash name) (* 7919 package))))
     (implies (and (natp package) (stringp name) (natp query-package) (stringp query-name)
                   (data-table-p table 12))
              (equal (boymoo-compiler::table-get
                      query query-hash 12 (boymoo-compiler::table-put key value hash 12 table))
                     (if (equal query key) value
                       (boymoo-compiler::table-get query query-hash 12 table)))))
   :hints (("Goal" :use ((:instance data-table-get-after-put
                                    (query (cons query-package query-name)) (key (cons package name))
                                    (query-hash (+ (boymoo-compiler::text-hash query-name) (* 7919 query-package)))
                                    (hash (+ (boymoo-compiler::text-hash name) (* 7919 package)))
                                    (bits 12) (tree table)))
                   :in-theory (disable data-table-p data-table-get-after-put boymoo-compiler::text-hash)))))

(defthmd data-intern-keeps-existing-name-binding
  (let ((old (data-name-table-lookup query-package query-name state-data)))
    (implies (and (natp package) (stringp name) (natp query-package) (stringp query-name)
                  (data-table-p (car state-data) 12) old)
             (equal (data-name-table-lookup
                     query-package query-name (mv-nth 2 (boymoo-compiler::data-intern package name state-data)))
                    old)))
  :hints (("Goal" :in-theory (disable data-table-p boymoo-compiler::text-hash))))

(local
 (defthm new-symbol-word-is-not-the-import-marker
   (implies (not (data-name-table-lookup package name state-data))
            (not (eq (car (boymoo-compiler::data-intern package name state-data)) :import)))
   :hints (("Goal" :in-theory (enable boymoo-compiler::data-fields)))))

(defthmd data-reinterning-a-new-owned-name-retains-its-allocation
  (implies (and (natp package) (stringp name) (data-table-p (car state-data) 12)
                (not (data-name-table-lookup package name state-data)))
           (mv-let (symbol-word name-word next) (boymoo-compiler::data-intern package name state-data)
             (equal (mv-list 3 (boymoo-compiler::data-intern package name next))
                    (list symbol-word name-word next))))
  :hints (("Goal" :use (data-intern-publishes-owned-name new-symbol-word-is-not-the-import-marker
                       (:instance data-intern-reuses-owned-name
                                  (state-data (mv-nth 2 (boymoo-compiler::data-intern package name state-data)))))
                  :in-theory (disable boymoo-compiler::data-intern data-name-table-lookup data-table-p
                                      new-symbol-word-is-not-the-import-marker))))
