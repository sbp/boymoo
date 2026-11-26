(in-package "BOYMOO-PROOFS")

(include-book "scalar-quotes")
(include-book "trace-agreement")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable data-program-spans-p data-source-lines-spelled-p data-quote-spellings-p
                     data-program-quoted-texts data-program-quote-count data-quote-witness-for-text
                     data-program-storage-input-p data-program-constant-keys-p data-package-lines-storage-input-p
                     data-atom-spells-value-p boymoo-compiler::read-program boymoo-compiler::index-lines
                     boymoo-compiler::data-build boymoo-compiler::data-package-numbers boymoo-compiler::index-get
                     proof-constant-map-p)))

(local
 (defthm an-immediate-quotation-has-an-atomic-spelling
   (implies (and (or (proof-immediate-integer-p value) (characterp value))
                 (data-constant-spells-value-p query quote-events datum value))
            (data-scalar-quote-p query value))
   :hints (("Goal" :in-theory (disable data-reader-events data-parsed-datum-spells-value-p)))))

(local
 (in-theory (disable data-constant-spells-value-p proof-immediate-integer-p data-scalar-quote-p)))

(defthmd data-checked-text-scalar-quotation-has-its-source-value
  (let* ((parsed (boymoo-compiler::read-program text))
         (package-lines (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil)))
         (value (cdr (assoc-equal query bindings))))
    (implies (and (data-program-spans-p text events lines)
                  (data-source-lines-spelled-p lines sources bindings nil nil)
                  (data-quote-spellings-p bindings witnesses)
                  (< 0 (data-program-quote-count lines query))
                  (or (proof-immediate-integer-p value) (characterp value))
                  (boymoo-compiler::index-get
                   "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
             (proof-constant-map-p (list (cons query value))
                                   (mv-nth 1 (boymoo-compiler::data-build parsed package-lines))
                                   base objects packages machine)))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        data-checked-program-quote-supplies-its-spelling
                        (:instance data-build-scalar-quote-has-its-source-value
                                   (lines (boymoo-compiler::read-program text))
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil)))
                                   (value (cdr (assoc-equal query bindings))))))))

(local
 (defthm a-binding-key-occurs-among-the-keys
   (implies (assoc-equal query bindings)
            (member-equal query (strip-cars bindings)))))

(local (in-theory (disable data-elaborate-program-with-quotes)))

(defthmd data-elaborated-text-scalar-quotation-has-its-source-value
  (mv-let (ok events lines sources bindings witnesses) (data-elaborate-program-with-quotes text packages)
    (declare (ignore events lines sources witnesses))
    (let* ((parsed (boymoo-compiler::read-program text))
           (package-lines (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil)))
           (binding (assoc-equal query bindings))
           (value (cdr binding)))
      (implies (and ok binding (or (proof-immediate-integer-p value) (characterp value))
                    (boymoo-compiler::index-get
                     "COMMON-LISP" (boymoo-compiler::data-package-numbers package-lines 0 nil)))
               (proof-constant-map-p (list (cons query value))
                                     (mv-nth 1 (boymoo-compiler::data-build parsed package-lines))
                                     base objects packages machine))))
  :hints (("Goal" :use (data-elaborated-program-with-quotes-supplies-all-checked-relations
                        (:instance data-program-quoted-texts-cover-all-syntactic-occurrences
                                   (text query) (lines (mv-nth 2 (data-elaborate-program-with-quotes text packages))))
                        (:instance data-checked-text-scalar-quotation-has-its-source-value
                                   (events (mv-nth 1 (data-elaborate-program-with-quotes text packages)))
                                   (lines (mv-nth 2 (data-elaborate-program-with-quotes text packages)))
                                   (sources (mv-nth 3 (data-elaborate-program-with-quotes text packages)))
                                   (bindings (mv-nth 4 (data-elaborate-program-with-quotes text packages)))
                                   (witnesses (mv-nth 5 (data-elaborate-program-with-quotes text packages)))))
                  :in-theory (disable assoc-equal strip-cars member-equal))))
