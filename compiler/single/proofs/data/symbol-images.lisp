(in-package "BOYMOO-PROOFS")

(include-book "builtin-symbols")

(logic)
(set-verify-guards-eagerness 0)

(defun data-owned-symbol-chunks (number name offset)
  (list (+ 1 (* 256 (length name))) name 4098 (+ offset 2) (+ 1 (* 2 number))))

(defun data-owned-symbol-offset (name offset)
  (+ offset 8 (boymoo-compiler::aligned-size (length name) 3)))

(local
 (in-theory (disable boymoo-compiler::aligned-size boymoo-compiler::table-get boymoo-compiler::table-put
                     boymoo-compiler::text-hash boymoo-compiler::data-bucket-add
                     data-state-retains-chunks-p length ash)))

(local
 (defthm symbol-state-chunks-are-block-chunks
   (equal (data-state-retains-chunks-p earlier (list* names constants buckets block))
          (data-retained-chunks-p earlier (cdr block)))
   :hints (("Goal" :in-theory (enable data-state-retains-chunks-p)))))

(defthmd data-fresh-intern-allocates-name-and-symbol
  (let* ((block (boymoo-compiler::data-block state-data)) (offset (car block))
         (allocated (data-owned-symbol-chunks number name offset)))
    (implies (and (natp offset) (natp number) (stringp name)
                  (not (data-name-table-lookup number name state-data)))
             (mv-let (symbol-word name-word next) (boymoo-compiler::data-intern number name state-data)
               (and (equal name-word (+ offset 2))
                    (equal symbol-word (+ 2 (data-owned-symbol-offset name offset)))
                    (data-state-retains-chunks-p
                     (boymoo-compiler::reverse-onto allocated (cdr block)) next)))))
  :hints (("Goal" :in-theory (e/d (data-ash-left)
                                 (data-retained-chunks-p boymoo-compiler::bucket-get)))))

(local
 (in-theory (disable proof-view proof-load-word proof-load-string proof-pointer-address proof-word-tag
                     data-placed-characters-p evenp)))

(local
 (defthm string-allocation-byte-length
   (implies (stringp name)
            (equal (len (data-forward-chunk-characters (list (+ 1 (* 256 (length name))) name)))
                   (+ 8 (boymoo-compiler::aligned-size (length name) 3))))
   :hints (("Goal" :use ((:instance data-forward-chunk-characters-size
                                    (chunks (list (+ 1 (* 256 (length name))) name))))
                   :in-theory (disable data-forward-chunk-characters)))))

(local
 (defthm appended-symbol-chunks-associate
   (equal (append (append first middle) rest) (append first middle rest))))

(local
 (defthm character-prefixes-for-a-new-symbol
   (equal (data-forward-chunk-characters (data-owned-symbol-chunks number name offset))
          (append (data-forward-chunk-characters (list (+ 1 (* 256 (length name))) name))
                  (data-forward-chunk-characters (list 4098 (+ 2 offset) (+ 1 (* 2 number))))))
   :rule-classes nil))

(local
 (defthm character-stream-of-chunks-is-true-list
   (true-listp (data-forward-chunk-characters chunks))))

(defthmd data-placed-owned-symbol-chunks-load-fields
  (let* ((address (+ base offset)) (symbol-address (+ base (data-owned-symbol-offset name offset)))
         (size (length name)))
    (implies (and (integerp base) (natp offset) (stringp name) (< size *proof-space-size*)
                  (< (+ offset 2) *proof-space-size*) (natp number) (proof-immediate-integer-p number)
                  (data-placed-characters-p (data-forward-chunk-characters (data-owned-symbol-chunks number name offset))
                                            address machine))
             (and (equal (proof-load-word address machine) (+ 1 (* 256 size)))
                  (equal (proof-load-string size (+ address 8) machine) name)
                  (equal (proof-load-word symbol-address machine) 4098)
                  (equal (proof-load-word (+ symbol-address 8) machine) (+ 2 offset))
                  (equal (proof-load-word (+ symbol-address 16) machine) (proof-integer-word number)))))
  :hints (("Goal" :use (character-prefixes-for-a-new-symbol
                        (:instance data-placed-string-allocation-loads-fields (address (+ base offset)) (string name))
                        (:instance data-placed-u64-chunks-load-their-words
                                   (words (list 4098 (+ 2 offset) (+ 1 (* 2 number))))
                                   (address (+ base (data-owned-symbol-offset name offset))))
                        (:instance data-immediate-integer-twos-complement (integer number)))
                  :in-theory (disable data-forward-chunk-characters proof-integer-word data-owned-symbol-chunks))))

(local
 (defthm retained-chunk-suffixes-compose
   (implies (and (data-retained-chunks-p earlier middle) (data-retained-chunks-p middle last))
            (data-retained-chunks-p earlier last))
   :rule-classes nil
   :hints (("Goal" :induct (data-retained-chunks-p middle last)))))

(defthmd data-placed-fresh-intern-loads-owned-symbol-fields
  (let* ((block (boymoo-compiler::data-block state-data)) (offset (car block))
         (symbol-address (+ base (data-owned-symbol-offset name offset)))
         (name-address (+ base offset)) (size (length name)))
    (implies (and (integerp base) (data-block-sized-p block 80) (natp number) (proof-immediate-integer-p number)
                  (stringp name) (< size *proof-space-size*) (< (+ offset 2) *proof-space-size*)
                  (not (data-name-table-lookup number name state-data))
                  (data-state-retains-chunks-p
                   (cdr (boymoo-compiler::data-block (mv-nth 2 (boymoo-compiler::data-intern number name state-data))))
                   final-state)
                  (data-placed-characters-p (data-chunks-characters (cdr (boymoo-compiler::data-block final-state)))
                                            (+ base 80) machine))
             (and (equal (proof-load-word name-address machine) (+ 1 (* 256 size)))
                  (equal (proof-load-string size (+ name-address 8) machine) name)
                  (equal (proof-load-word symbol-address machine) 4098)
                  (equal (proof-load-word (+ symbol-address 8) machine) (+ 2 offset))
                  (equal (proof-load-word (+ symbol-address 16) machine) (proof-integer-word number)))))
  :hints (("Goal" :use (data-fresh-intern-allocates-name-and-symbol
                        (:instance data-placed-owned-symbol-chunks-load-fields
                                   (offset (car (boymoo-compiler::data-block state-data))))
                        (:instance data-placed-retained-builder-allocation (before (boymoo-compiler::data-block state-data))
                                   (allocated (data-owned-symbol-chunks
                                               number name (car (boymoo-compiler::data-block state-data))))
                                   (body (cdr (boymoo-compiler::data-block final-state))))
                        (:instance retained-chunk-suffixes-compose
                                   (earlier (boymoo-compiler::reverse-onto
                                             (data-owned-symbol-chunks number name (cadddr state-data))
                                             (cddddr state-data)))
                                   (middle (cddddr (mv-nth 2 (boymoo-compiler::data-intern number name state-data))))
                                   (last (cddddr final-state))))
                  :in-theory (e/d (data-state-retains-chunks-p)
                                 (boymoo-compiler::data-intern data-retained-chunks-p data-block-sized-p
                                  data-name-table-lookup data-owned-symbol-offset data-owned-symbol-chunks
                                  data-chunks-characters data-forward-chunk-characters
                                  boymoo-compiler::reverse-onto proof-integer-word)))))

(local
 (defthm package-fields-denote-their-owned-symbol
   (let* ((package (nth number packages)) (witness (proof-package-witness package)))
     (implies (and (stringp name) (natp number) (proof-immediate-integer-p number) (< number (len packages))
                   (symbolp symbol) (symbolp witness) (equal (symbol-name symbol) name)
                   (equal (symbol-package-name symbol) (proof-package-name package))
                   (equal (symbol-package-name witness) (proof-package-name package)))
              (equal (data-two-field-view 2 name number packages) (proof-value-view symbol))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance acl2::intern-in-package-of-symbol-symbol-name
                                    (acl2::x symbol) (acl2::y (proof-package-witness (nth number packages)))))
                   :in-theory (disable acl2::intern-in-package-of-symbol-symbol-name proof-immediate-integer-p)))))

(local
 (defthm owned-symbol-package-is-an-immediate-child
   (implies (and (proof-immediate-integer-p number) (posp rank))
            (data-child-value-p (proof-integer-word number) number rank base objects packages machine))
   :hints (("Goal" :use ((:instance data-view-of-immediate-integer (integer number)))
                   :in-theory (disable proof-immediate-integer-p proof-integer-word)))))

(local
 (defthm owned-symbol-name-is-earlier-child
   (let* ((offset (* 8 slot)) (word (+ 2 offset)) (address (+ base offset)) (bytes (length name)))
     (implies (and (proof-span-p base size) (< size *proof-space-size*) (natp slot) (posp rank) (< slot rank)
                   (stringp name) (<= (+ offset 8 bytes) size)
                   (equal (assoc-equal address objects) (proof-object address :static :header slot))
                   (equal (proof-load-word address machine) (+ 1 (* 256 bytes)))
                   (equal (proof-load-string bytes (+ 8 address) machine) name))
              (data-child-value-p word name rank base objects packages machine)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-static-reference-fits-and-points-at-offset (tag 2))
                         (:instance data-view-of-static-string-fields (word (+ 2 (* 8 slot))) (string name)))))))

(defthmd data-view-of-placed-owned-symbol-fields
  (let* ((address (+ base (* 8 symbol-slot))) (name-address (+ base (* 8 name-slot)))
         (package (nth number packages)) (witness (proof-package-witness package)))
    (implies (and (proof-span-p base size) (< size *proof-space-size*) (natp name-slot) (posp symbol-slot)
                  (< name-slot symbol-slot) (<= (+ 24 (* 8 symbol-slot)) size)
                  (equal (assoc-equal address objects) (proof-object address :static :header symbol-slot))
                  (equal (assoc-equal name-address objects) (proof-object name-address :static :header name-slot))
                  (stringp name) (<= (+ 8 (* 8 name-slot) (length name)) size)
                  (equal (proof-load-word name-address machine) (+ 1 (* 256 (length name))))
                  (equal (proof-load-string (length name) (+ 8 name-address) machine) name)
                  (equal (proof-load-word address machine) 4098)
                  (equal (proof-load-word (+ 8 address) machine) (+ 2 (* 8 name-slot)))
                  (equal (proof-load-word (+ 16 address) machine) (proof-integer-word number))
                  (natp number) (proof-immediate-integer-p number) (< number (len packages))
                  (symbolp symbol) (symbolp witness) (equal (symbol-name symbol) name)
                  (equal (symbol-package-name symbol) (proof-package-name package))
                  (equal (symbol-package-name witness) (proof-package-name package)))
             (proof-value-p (+ 2 (* 8 symbol-slot)) symbol base objects packages machine)))
  :hints (("Goal" :use (package-fields-denote-their-owned-symbol
                        (:instance owned-symbol-name-is-earlier-child (slot name-slot) (rank symbol-slot))
                        (:instance owned-symbol-package-is-an-immediate-child (rank symbol-slot))
                        (:instance data-static-reference-fits-and-points-at-offset (tag 2) (slot symbol-slot))
                        (:instance data-view-of-static-two-field-header
                                   (type 2) (word (+ 2 (* 8 symbol-slot))) (first name) (second number)))
                  :in-theory (disable data-child-value-p data-two-field-view proof-integer-word
                                      proof-immediate-integer-p owned-symbol-package-is-an-immediate-child))))
