(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defthm symbols-package-number-type
  (implies (natp first)
           (or (not (proof-package-number name packages first))
               (natp (proof-package-number name packages first))))
  :hints (("Goal" :induct (proof-package-number name packages first)))
  :rule-classes :type-prescription)

(defthm symbols-package-number-range
  (implies (and (natp first)
                (proof-package-number name packages first))
           (and (<= first (proof-package-number name packages first))
                (< (proof-package-number name packages first)
                   (+ first (len packages)))))
  :hints (("Goal" :induct (proof-package-number name packages first)))
  :rule-classes :linear)

; The package vector is indexed by package number. A name search selects
; the same row by testing the first field of each package record.
(defthm symbols-package-number-selects-row
  (implies (and (natp first)
                (proof-package-number name packages first))
           (equal (nth (- (proof-package-number name packages first) first)
                       packages)
                  (assoc-equal name packages)))
  :hints (("Goal" :induct (proof-package-number name packages first)
                  :in-theory (enable proof-package-name))))

(defthm symbols-package-number-present
  (implies (and (natp first) (alistp packages))
           (iff (proof-package-number name packages first)
                (assoc-equal name packages)))
  :hints (("Goal" :induct (proof-package-number name packages first)
                  :in-theory (enable proof-package-name))))

(defthm symbols-package-row-of-member
  (implies (and (proof-packages-p packages)
                (member-equal row packages))
           (equal (assoc-equal (proof-package-name row) packages) row)))

(defthm symbols-packages-are-an-alist
  (implies (proof-packages-p packages) (alistp packages)))

(defthm symbols-visible-row
  (implies (proof-packages-p packages)
           (iff (member-equal name (proof-public-package-names packages))
                (proof-package-visible (assoc-equal name packages)))))

(defthm symbols-core-visible-row
  (implies (proof-program-packages-p program packages)
           (iff (boymoo-model::core-visible-package-p name program)
                (proof-package-visible (assoc-equal name packages))))
  :hints (("Goal" :in-theory (enable proof-program-packages-p
                                     boymoo-model::core-visible-package-p))))

(defthm symbols-row-imports
  (implies (and (proof-packages-p packages)
                (assoc-equal name packages))
           (equal (proof-package-imports (assoc-equal name packages))
                  (acl2::pkg-imports name))))

(defthm symbols-row-witness-fields
  (implies (and (proof-packages-p packages)
                (assoc-equal name packages))
           (let ((witness (proof-package-witness (assoc-equal name packages))))
             (and (stringp name)
                  (not (equal name ""))
                  (symbolp witness)
                  (equal (symbol-name witness) "ACL2-PKG-WITNESS")
                  (equal (acl2::symbol-package-name witness) name)))))

(defthm symbols-equal-when-spellings-agree
  (implies (and (symbolp x) (symbolp y)
                (equal (symbol-name x) (symbol-name y))
                (equal (acl2::symbol-package-name x)
                       (acl2::symbol-package-name y)))
           (equal x y))
  :hints (("Goal"
           :use ((:instance acl2::intern-in-package-of-symbol-symbol-name
                            (acl2::x x) (acl2::y y))
                 (:instance acl2::intern-in-package-of-symbol-symbol-name
                            (acl2::x y) (acl2::y y)))
           :in-theory (disable acl2::intern-in-package-of-symbol-symbol-name)))
  :rule-classes nil)

(defthm symbols-intern-in-same-package
  (implies (and (stringp name) (symbolp x) (symbolp y)
                (equal (acl2::symbol-package-name x)
                       (acl2::symbol-package-name y)))
           (equal (acl2::intern-in-package-of-symbol name x)
                  (acl2::intern-in-package-of-symbol name y)))
  :hints (("Goal"
           :cases ((acl2::member-symbol-name
                    name (acl2::pkg-imports (acl2::symbol-package-name y))))
           :use ((:instance symbols-equal-when-spellings-agree
                            (x (acl2::intern-in-package-of-symbol name x))
                            (y (acl2::intern-in-package-of-symbol name y))))))
  :rule-classes nil)

(defthm symbols-row-witness-implements-pkg-witness
  (implies (and (proof-packages-p packages)
                (assoc-equal name packages))
           (equal (proof-package-witness (assoc-equal name packages))
                  (acl2::pkg-witness name)))
  :hints (("Goal"
           :use ((:instance symbols-row-witness-fields)
                 (:instance symbols-equal-when-spellings-agree
                            (x (proof-package-witness (assoc-equal name packages)))
                            (y (acl2::pkg-witness name))))
           :in-theory (disable proof-packages-p assoc-equal))))

(defthm symbols-nonstring-witness
  (implies (not (stringp datum))
           (equal (acl2::pkg-witness datum) (acl2::pkg-witness "ACL2")))
  :hints (("Goal"
           :use ((:instance symbols-equal-when-spellings-agree
                            (x (acl2::pkg-witness datum))
                            (y (acl2::pkg-witness "ACL2")))))))

(defun symbols-package-query (primitive datum packages)
  (if (stringp datum)
      (let ((row (assoc-equal datum packages)))
        (if (proof-package-visible row)
            (boymoo-model::core-value
             (if (eq primitive 'acl2::pkg-imports)
                 (proof-package-imports row)
               (proof-package-witness row)))
          :no-value))
    (boymoo-model::core-value
     (if (eq primitive 'acl2::pkg-imports)
         nil
       (proof-package-witness (assoc-equal "ACL2" packages))))))

(defthm symbols-acl2-row-visible
  (implies (proof-program-packages-p program packages)
           (proof-package-visible (assoc-equal "ACL2" packages)))
  :hints (("Goal" :use ((:instance symbols-core-visible-row (name "ACL2")))
                  :in-theory (disable symbols-core-visible-row
                                      proof-program-packages-p assoc-equal))))

(local
 (defthm symbols-program-has-packages
   (implies (proof-program-packages-p program packages)
            (proof-packages-p packages))
   :rule-classes nil))

(local
 (defthm symbols-visible-row-present
   (implies (proof-package-visible (assoc-equal name packages))
            (assoc-equal name packages))
   :hints (("Goal" :in-theory (enable proof-package-visible)))))

(defthm symbols-package-query-implements-core
  (implies (and (proof-program-packages-p program packages)
                (member-eq primitive '(acl2::pkg-imports acl2::pkg-witness)))
           (equal (symbols-package-query primitive datum packages)
                  (boymoo-model::core-primitive primitive (list datum) program)))
  :hints (("Goal"
           :use ((:instance acl2::completion-of-pkg-imports (acl2::x datum))
                 (:instance symbols-acl2-row-visible)
                 (:instance symbols-core-visible-row (name datum))
                 (:instance symbols-program-has-packages))
           :in-theory (e/d (boymoo-model::core-primitive)
                           (proof-program-packages-p assoc-equal
                            proof-packages-p proof-package-visible
                            proof-package-imports proof-package-witness
                            symbols-acl2-row-visible
                            symbols-core-visible-row)))))

(defthm symbols-intern-witness
  (implies (and (symbolp symbol)
                (proof-packages-p packages)
                (assoc-equal (acl2::symbol-package-name symbol) packages))
           (equal (acl2::intern-in-package-of-symbol "ACL2-PKG-WITNESS" symbol)
                  (proof-package-witness
                   (assoc-equal (acl2::symbol-package-name symbol) packages))))
  :hints (("Goal"
           :use ((:instance symbols-row-witness-fields
                            (name (acl2::symbol-package-name symbol)))
                 (:instance symbols-intern-in-same-package
                            (name "ACL2-PKG-WITNESS")
                            (x symbol)
                            (y (proof-package-witness
                                (assoc-equal (acl2::symbol-package-name symbol)
                                             packages))))
                 (:instance acl2::intern-in-package-of-symbol-symbol-name
                            (acl2::x (proof-package-witness
                                      (assoc-equal (acl2::symbol-package-name symbol)
                                                   packages)))
                            (acl2::y (proof-package-witness
                                      (assoc-equal (acl2::symbol-package-name symbol)
                                                   packages)))))
           :in-theory (disable proof-packages-p proof-package-witness
                               assoc-equal symbols-row-witness-fields
                               symbols-row-witness-implements-pkg-witness
                               acl2::intern-in-package-of-symbol-symbol-name))))

(local
 (defthm symbols-row-witness-from-name
   (implies (proof-packages-p packages)
            (iff (member-eq witness (proof-hidden-package-witnesses packages))
                 (let ((row (assoc-equal (acl2::symbol-package-name witness)
                                         packages)))
                   (and row (not (proof-package-visible row))
                        (equal witness (proof-package-witness row))))))
   :hints (("Goal" :induct (proof-packages-p packages)))))

(defthm symbols-core-hidden-row
  (implies (and (proof-program-packages-p program packages)
                (symbolp symbol)
                (assoc-equal (acl2::symbol-package-name symbol) packages))
           (iff (boymoo-model::core-hidden-symbol-p symbol program)
                (not (proof-package-visible
                      (assoc-equal (acl2::symbol-package-name symbol) packages)))))
  :hints (("Goal"
           :use ((:instance symbols-row-witness-from-name
                            (witness (proof-package-witness
                                      (assoc-equal (acl2::symbol-package-name symbol)
                                                   packages))))
                 (:instance symbols-row-witness-fields
                            (name (acl2::symbol-package-name symbol))))
           :in-theory (disable proof-packages-p proof-hidden-package-witnesses
                               assoc-equal proof-package-visible proof-package-witness
                               symbols-row-witness-from-name symbols-row-witness-fields
                               symbols-row-witness-implements-pkg-witness))))

(defun symbols-package-name-result (datum packages)
  (if (symbolp datum)
      (let* ((name (acl2::symbol-package-name datum))
             (row (assoc-equal name packages)))
        (if (proof-package-visible row)
            (boymoo-model::core-value name)
          :no-value))
    (boymoo-model::core-value "")))

(defthm symbols-package-name-implements-core
  (implies (and (proof-program-packages-p program packages)
                (or (not (symbolp datum))
                    (assoc-equal (acl2::symbol-package-name datum) packages)))
           (equal (symbols-package-name-result datum packages)
                  (boymoo-model::core-primitive
                   'acl2::symbol-package-name (list datum) program)))
  :hints (("Goal"
           :use ((:instance symbols-core-hidden-row (symbol datum))
                 (:instance acl2::completion-of-symbol-package-name (acl2::x datum)))
           :in-theory (e/d (boymoo-model::core-primitive)
                           (proof-program-packages-p assoc-equal
                            proof-package-visible symbols-core-hidden-row)))))

(defthm symbols-name-of-nonsymbol-implements-core
  (implies (not (symbolp datum))
           (equal (boymoo-model::core-primitive 'symbol-name (list datum) program)
                  (boymoo-model::core-value "")))
  :hints (("Goal" :in-theory (enable boymoo-model::core-primitive))))

(defthm symbols-intern-default-implements-core
  (implies (or (not (stringp name)) (not (symbolp designator)))
           (equal (boymoo-model::core-primitive 'acl2::intern-in-package-of-symbol
                                               (list name designator) program)
                  (boymoo-model::core-value nil)))
  :hints (("Goal" :in-theory (enable boymoo-model::core-primitive))))

(defthm symbols-static-bucket-hit
  (implies (and (proof-static-bucket-p entries index packages)
                (assoc-equal (cons number name) entries))
           (let* ((result (assoc-equal (cons number name) entries))
                  (row (nth number packages)))
             (and (natp number)
                  (< number (len packages))
                  (stringp name)
                  (equal (proof-symbol-hash number name 12) index)
                  (equal (cdr result)
                         (acl2::intern-in-package-of-symbol
                          name (proof-package-witness row))))))
  :hints (("Goal" :induct (proof-static-bucket-p entries index packages)
                  :in-theory (disable proof-symbol-hash proof-package-witness))))

(defthm symbols-import-resolves-in-static-bucket
  (implies (and (proof-import-bindings-p imports number buckets)
                (member-eq symbol imports))
           (equal (proof-static-binding number (symbol-name symbol) buckets)
                  (cons (cons number (symbol-name symbol)) symbol)))
  :hints (("Goal" :in-theory (disable proof-static-binding))))

(local
 (defun symbols-package-bindings-induction (offset first packages)
   (if (atom packages)
       (cons offset first)
     (symbols-package-bindings-induction (1- offset) (1+ first) (cdr packages)))))

(defthm symbols-selected-row-import-bindings
  (implies (and (proof-package-bindings-p packages first buckets)
                (natp offset) (< offset (len packages))
                (natp first))
           (proof-import-bindings-p (proof-package-imports (nth offset packages))
                                    (+ first offset) buckets))
  :hints (("Goal" :induct (symbols-package-bindings-induction offset first packages)
                  :in-theory (disable proof-package-imports proof-import-bindings-p))))

(defthm symbols-intern-on-static-hit-implements-core
  (let* ((number (proof-package-number (acl2::symbol-package-name designator)
                                       packages 0))
         (bucket (proof-view-value (nth (proof-symbol-hash number name 12) buckets)))
         (binding (proof-static-binding number name buckets)))
    (implies (and (proof-packages-p packages)
                  (symbolp designator) (stringp name) (natp number)
                  (proof-static-bucket-p bucket (proof-symbol-hash number name 12)
                                         packages)
                  binding)
             (equal (boymoo-model::core-primitive 'acl2::intern-in-package-of-symbol
                                                  (list name designator) program)
                    (boymoo-model::core-value (cdr binding)))))
  :hints (("Goal"
           :use ((:instance symbols-static-bucket-hit
                            (number (proof-package-number (acl2::symbol-package-name designator)
                                                           packages 0))
                            (index (proof-symbol-hash
                                    (proof-package-number (acl2::symbol-package-name designator)
                                                          packages 0)
                                    name 12))
                            (entries (proof-view-value
                                      (nth (proof-symbol-hash
                                            (proof-package-number
                                             (acl2::symbol-package-name designator) packages 0)
                                            name 12)
                                           buckets))))
                 (:instance symbols-intern-in-same-package
                            (x designator)
                            (y (proof-package-witness
                                (assoc-equal (acl2::symbol-package-name designator)
                                             packages))))
                 (:instance symbols-row-witness-fields
                            (name (acl2::symbol-package-name designator)))
                 (:instance symbols-package-number-selects-row
                            (name (acl2::symbol-package-name designator)) (first 0))
                 (:instance symbols-package-number-present
                            (name (acl2::symbol-package-name designator)) (first 0)))
           :in-theory (e/d (boymoo-model::core-primitive)
                           (proof-packages-p proof-static-bucket-p proof-symbol-hash
                            proof-package-number proof-package-witness assoc-equal
                            symbols-static-bucket-hit symbols-row-witness-fields)))))

(local
 (defthm symbols-member-symbol-name-matches
   (implies (acl2::member-symbol-name name imports)
            (let ((match (car (acl2::member-symbol-name name imports))))
              (and (member-equal match imports)
                   (equal (symbol-name match) name))))
   :hints (("Goal" :induct (acl2::member-symbol-name name imports)
                   :in-theory (enable acl2::member-symbol-name)))))

(defthm symbols-intern-on-static-miss-is-home
  (let* ((package (acl2::symbol-package-name designator))
         (number (proof-package-number package packages 0))
         (symbol (acl2::intern-in-package-of-symbol name designator)))
    (implies (and (proof-packages-p packages)
                  (proof-package-bindings-p packages 0 buckets)
                  (stringp name) (symbolp designator) (natp number)
                  (not (proof-static-binding number name buckets)))
             (and (symbolp symbol)
                  (equal (symbol-name symbol) name)
                  (equal (acl2::symbol-package-name symbol) package))))
  :hints (("Goal"
           :use ((:instance symbols-selected-row-import-bindings
                            (first 0)
                            (offset (proof-package-number (acl2::symbol-package-name designator)
                                                          packages 0)))
                 (:instance symbols-package-number-selects-row
                            (first 0) (name (acl2::symbol-package-name designator)))
                 (:instance symbols-package-number-present
                            (first 0) (name (acl2::symbol-package-name designator)))
                 (:instance symbols-member-symbol-name-matches
                            (imports (acl2::pkg-imports (acl2::symbol-package-name designator))))
                 (:instance symbols-import-resolves-in-static-bucket
                            (number (proof-package-number (acl2::symbol-package-name designator)
                                                           packages 0))
                            (symbol (car (acl2::member-symbol-name
                                          name (acl2::pkg-imports
                                                (acl2::symbol-package-name designator)))))
                            (imports (acl2::pkg-imports (acl2::symbol-package-name designator)))))
           :in-theory (disable proof-static-binding proof-package-bindings-p
                               proof-import-bindings-p proof-package-imports
                               proof-packages-p proof-package-number
                               acl2::member-symbol-name assoc-equal
                               symbols-package-number-present
                               symbols-selected-row-import-bindings
                               symbols-member-symbol-name-matches
                               symbols-import-resolves-in-static-bucket))))

(defthm symbols-intern-on-dynamic-hit-implements-core
  (let* ((package (acl2::symbol-package-name designator))
         (number (proof-package-number package packages 0)))
    (implies (and (proof-packages-p packages)
                  (proof-package-bindings-p packages 0 buckets)
                  (stringp name) (symbolp designator) (natp number)
                  (not (proof-static-binding number name buckets))
                  (symbolp resident) (equal (symbol-name resident) name)
                  (equal (acl2::symbol-package-name resident) package))
             (equal (boymoo-model::core-primitive 'acl2::intern-in-package-of-symbol
                                                  (list name designator) program)
                    (boymoo-model::core-value resident))))
  :hints (("Goal"
           :use ((:instance symbols-intern-on-static-miss-is-home)
                 (:instance symbols-equal-when-spellings-agree
                            (x (acl2::intern-in-package-of-symbol name designator)) (y resident)))
           :in-theory (e/d (boymoo-model::core-primitive)
                           (symbols-intern-on-static-miss-is-home
                            proof-package-number proof-static-binding proof-package-bindings-p proof-packages-p))))
  :rule-classes nil)

(local
 (defthm symbols-indexed-package-name-is-present
   (implies (and (alistp packages) (natp number) (< number (len packages)))
            (assoc-equal (proof-package-name (nth number packages)) packages))
   :hints (("Goal" :induct (nth number packages)))))

(local
 (defun symbols-indexed-package-induction (number packages first)
   (declare (xargs :measure (nfix number)))
   (if (zp number)
       (cons first packages)
     (symbols-indexed-package-induction (1- number) (cdr packages) (1+ first)))))

(defthm symbols-package-number-of-indexed-row
  (implies (and (proof-packages-p packages) (natp number) (< number (len packages))
                (natp first))
           (equal (proof-package-number (proof-package-name (nth number packages)) packages first)
                  (+ first number)))
  :hints (("Goal" :induct (symbols-indexed-package-induction number packages first)
                  :in-theory (disable acl2::pkg-imports))
          ("Subgoal *1/2"
           :use ((:instance symbols-indexed-package-name-is-present
                            (number (1- number)) (packages (cdr packages))))
           :in-theory (disable acl2::pkg-imports symbols-indexed-package-name-is-present)))
  :rule-classes nil)
