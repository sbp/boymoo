(in-package "BOYMOO-PROOFS")

(include-book "scalar-agreement")
(include-book "builtin-agreement")

(logic)
(set-verify-guards-eagerness 0)

; These bindings require a view of an object in the static image.
(defun data-allocated-quote-bindings (bindings)
  (if (atom bindings)
      bindings
    (let ((value (cdar bindings))
          (rest (data-allocated-quote-bindings (cdr bindings))))
      (if (or (proof-immediate-integer-p value) (characterp value))
          rest
        (cons (car bindings) rest)))))

(local
 (defun immediate-quote-views-p (bindings index base objects packages machine)
   (or (atom bindings)
       (and (implies (or (proof-immediate-integer-p (cdar bindings)) (characterp (cdar bindings)))
                     (proof-constant-map-p (list (car bindings)) index base objects packages machine))
            (immediate-quote-views-p (cdr bindings) index base objects packages machine)))))

(local
 (in-theory (disable proof-immediate-integer-p proof-constant-word proof-value-p
                     boymoo-compiler::index-get data-elaborate-quote data-elaborate-program-lines
                     data-infer-program-spans data-program-quoted-texts)))

(local
 (defthm immediate-and-allocated-views-supply-the-complete-map
   (implies (and (immediate-quote-views-p bindings index base objects packages machine)
                 (proof-constant-map-p
                  (data-allocated-quote-bindings bindings) index base objects packages machine))
            (proof-constant-map-p bindings index base objects packages machine))
   :hints (("Goal" :induct (immediate-quote-views-p bindings index base objects packages machine)))))

(local
 (defthm a-successfully-elaborated-quote-has-a-text-key
   (implies (car (data-elaborate-quote text packages))
            (stringp text))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (e/d (data-elaborate-quote)
                                  (data-infer-reader-events data-atom-value-candidate data-datum-value-candidate
                                   data-constant-spells-value-p char length))))))

(local
 (defthm any-elaborated-quote-entry-is-the-value-computed-for-its-text
   (implies (and (car (data-elaborate-quote-list texts packages))
                 (member-equal binding (mv-nth 1 (data-elaborate-quote-list texts packages))))
            (and (consp binding)
                 (stringp (car binding))
                 (equal (cdr binding) (mv-nth 1 (data-elaborate-quote (car binding) packages)))))
   :hints (("Goal" :induct (data-elaborate-quote-list texts packages)))))

(local (in-theory (disable data-elaborate-quote-list)))

(local
 (defthm a-program-quote-entry-is-the-value-computed-for-its-text
   (implies (member-equal binding (mv-nth 4 (data-elaborate-program-with-quotes text packages)))
            (and (consp binding)
                 (stringp (car binding))
                 (equal (cdr binding) (mv-nth 1 (data-elaborate-quote (car binding) packages)))))))

(local (in-theory (disable data-elaborate-program-with-quotes)))

(local
 (defthm a-member-has-a-corresponding-key
   (implies (and (consp binding) (car binding) (member-equal binding bindings))
            (assoc-equal (car binding) bindings))
   :hints (("Goal" :induct (member-equal binding bindings)))))

(local
 (defthm lookup-finds-a-binding-with-the-requested-key
   (implies (and query (assoc-equal query bindings))
            (and (consp (assoc-equal query bindings))
                 (equal (car (assoc-equal query bindings)) query)
                 (member-equal (assoc-equal query bindings) bindings)))
   :hints (("Goal" :induct (assoc-equal query bindings)))))

(local
 (defthm elaborated-bindings-are-consistent-at-repeated-text
   (let ((bindings (mv-nth 4 (data-elaborate-program-with-quotes text packages))))
     (implies (member-equal binding bindings)
              (equal (assoc-equal (car binding) bindings) binding)))
   :rule-classes nil
   :hints (("Goal"
            :use (a-program-quote-entry-is-the-value-computed-for-its-text
                  (:instance a-member-has-a-corresponding-key
                             (bindings (mv-nth 4 (data-elaborate-program-with-quotes text packages))))
                  (:instance lookup-finds-a-binding-with-the-requested-key
                             (query (car binding))
                             (bindings (mv-nth 4 (data-elaborate-program-with-quotes text packages))))
                  (:instance a-program-quote-entry-is-the-value-computed-for-its-text
                             (binding (assoc-equal (car binding)
                                                   (mv-nth 4 (data-elaborate-program-with-quotes text packages))))))
            :in-theory (disable a-program-quote-entry-is-the-value-computed-for-its-text
                                lookup-finds-a-binding-with-the-requested-key assoc-equal)))))

(local
 (in-theory (disable boymoo-compiler::read-program boymoo-compiler::index-lines boymoo-compiler::data-build
                     boymoo-compiler::data-package-numbers proof-constant-map-p)))

(local
 (defthm a-member-of-elaborated-scalar-bindings-has-its-view
   (let* ((parsed (boymoo-compiler::read-program text))
          (package-lines (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil)))
          (index (mv-nth 1 (boymoo-compiler::data-build parsed package-lines))))
     (implies (and (mv-nth 0 (data-elaborate-program-with-quotes text packages))
                   (member-equal binding (mv-nth 4 (data-elaborate-program-with-quotes text packages)))
                   (or (proof-immediate-integer-p (cdr binding)) (characterp (cdr binding)))
                   (boymoo-compiler::index-get
                    "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
              (proof-constant-map-p (list binding) index base objects packages machine)))
   :rule-classes nil
   :hints (("Goal" :use (elaborated-bindings-are-consistent-at-repeated-text
                         a-program-quote-entry-is-the-value-computed-for-its-text
                         (:instance data-elaborated-text-scalar-quotation-has-its-source-value
                                    (query (car binding))))
                   :in-theory (disable assoc-equal a-program-quote-entry-is-the-value-computed-for-its-text)))))

(local
 (defthm selected-elaborated-immediate-quotes-all-have-views
   (let* ((parsed (boymoo-compiler::read-program text))
          (package-lines (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil)))
          (index (mv-nth 1 (boymoo-compiler::data-build parsed package-lines))))
     (implies (and (mv-nth 0 (data-elaborate-program-with-quotes text packages))
                   (subsetp-equal pending (mv-nth 4 (data-elaborate-program-with-quotes text packages)))
                   (boymoo-compiler::index-get
                    "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
              (immediate-quote-views-p pending index base objects packages machine)))
   :rule-classes nil
   :hints (("Goal" :induct (subsetp-equal pending (mv-nth 4 (data-elaborate-program-with-quotes text packages))))
           ("Subgoal *1/2" :use ((:instance a-member-of-elaborated-scalar-bindings-has-its-view
                                           (binding (car pending))))))))

(local
 (defthm adding-a-binding-preserves-existing-membership
   (implies (subsetp-equal pending bindings)
            (subsetp-equal pending (cons binding bindings)))
   :hints (("Goal" :induct (subsetp-equal pending bindings)))))

(local
 (defthm every-binding-is-selected-from-its-own-list
   (subsetp-equal bindings bindings)))

(defthmd data-elaborated-text-constant-map-from-allocated-quote-views
  (mv-let (ok events lines sources bindings witnesses) (data-elaborate-program-with-quotes text packages)
    (declare (ignore events lines sources witnesses))
    (let* ((parsed (boymoo-compiler::read-program text))
           (package-lines (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil)))
           (index (mv-nth 1 (boymoo-compiler::data-build parsed package-lines))))
      (implies (and ok (boymoo-compiler::index-get
                        "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil))
                    (proof-constant-map-p (data-allocated-quote-bindings bindings) index base objects packages machine))
               (proof-constant-map-p bindings index base objects packages machine))))
  :hints (("Goal" :use ((:instance selected-elaborated-immediate-quotes-all-have-views
                                   (pending (mv-nth 4 (data-elaborate-program-with-quotes text packages)))))
                  :in-theory (disable immediate-quote-views-p data-allocated-quote-bindings))))

(local
 (in-theory (disable data-allocated-quote-bindings data-before-buckets data-build-allocation-records
                     proof-image-at-p data-build-allocation-check-p data-static-views-p
                     data-static-table-and-object-views-p proof-package-name proof-package-witness
                     data-program-storage-input-p data-package-lines-storage-input-p data-program-constant-keys-p
                     data-indexable-lines-p data-program-spans-p data-source-lines-spelled-p data-quote-spellings-p
                     data-lookup-heads-spelled-p strip-cars
                     data-static-image-map proof-static-initial-p proof-index-agrees-p data-latest-arities mod nth)))

(local
 (defthm elaboration-supplies-the-storage-conditions
   (let* ((parsed (boymoo-compiler::read-program text))
          (package-lines (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))))
     (implies (car (data-elaborate-program-with-quotes text packages))
              (and (data-program-storage-input-p parsed)
                   (data-package-lines-storage-input-p package-lines))))
   :rule-classes nil
   :hints (("Goal" :use (data-elaborated-program-with-quotes-supplies-all-checked-relations
                         (:instance data-read-program-gives-source-front-pass-inputs
                                    (events (mv-nth 1 (data-elaborate-program-with-quotes text packages)))
                                    (lines (mv-nth 2 (data-elaborate-program-with-quotes text packages)))
                                    (sources (mv-nth 3 (data-elaborate-program-with-quotes text packages)))
                                    (bindings (mv-nth 4 (data-elaborate-program-with-quotes text packages)))
                                    (witnesses (mv-nth 5 (data-elaborate-program-with-quotes text packages)))))))))

(defthmd data-elaborated-text-and-allocated-views-give-static-agreement
  (mv-let (ok events lines sources bindings witnesses) (data-elaborate-program-with-quotes text packages)
    (declare (ignore events sources witnesses))
    (let* ((parsed (boymoo-compiler::read-program text))
           (pass (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil))
           (arities (mv-nth 1 pass)) (package-lines (mv-nth 4 pass))
           (records (data-build-allocation-records parsed package-lines base))
           (number (mv-nth 0 (data-before-buckets parsed package-lines)))
           (package (nth number packages))
           (witness (proof-package-witness package)))
      (mv-let (image constants) (boymoo-compiler::data-build parsed package-lines)
        (implies (and ok (string-listp queries)
                      number (natp number) (proof-immediate-integer-p number) (< number (len packages))
                      (equal (proof-package-name package) "COMMON-LISP")
                      (symbolp witness) (equal (symbol-package-name witness) "COMMON-LISP")
                      (proof-image-at-p image base machine) (< (car image) *proof-space-size*)
                      (equal (mod base 8) 0) (data-build-allocation-check-p parsed package-lines base)
                      (data-static-table-and-object-views-p base records packages machine)
                      (proof-constant-map-p (data-allocated-quote-bindings bindings) constants base records packages machine))
                 (mv-let (scanned objects) (data-static-image-map base image constants machine)
                   (and scanned (proof-static-initial-p base objects packages machine)
                        (proof-constant-map-p bindings constants base objects packages machine)
                        (proof-index-agrees-p (data-latest-arities queries lines) arities)))))))
  :hints (("Goal" :use (data-elaborated-text-and-allocations-give-static-agreement
                        elaboration-supplies-the-storage-conditions
                        (:instance data-placed-builder-table-and-object-views-supply-static-views
                                   (lines (boymoo-compiler::read-program text))
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil))))
                        (:instance data-elaborated-text-constant-map-from-allocated-quote-views
                                   (objects (data-build-allocation-records
                                             (boymoo-compiler::read-program text)
                                             (mv-nth 4 (boymoo-compiler::index-lines
                                                        (boymoo-compiler::read-program text)
                                                        nil nil nil nil nil nil nil)) base)))
                        (:instance data-build-common-lisp-number-agrees-with-index
                                   (lines (boymoo-compiler::read-program text))
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil))))))))
