(in-package "BOYMOO-PROOFS")

(include-book "home-availability")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable data-home-available-state-p data-natural-table-values-p
                     boymoo-compiler::data-with-block boymoo-compiler::data-block
                     boymoo-compiler::data-list-cells boymoo-compiler::data-atom
                     boymoo-compiler::data-symbol boymoo-compiler::data-remember
                     boymoo-compiler::read-lines boymoo-compiler::index-get
                     boymoo-compiler::declaration-list boymoo-compiler::compiler-error
                     data-symbol-storage-input-p data-atom-storage-input-p char length)))

(local
 (defthm datum-pass-preserves-available-home
   (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                 (data-home-available-state-p number name state-data) (data-datum-storage-input-p kind parsed))
            (data-home-available-state-p
             number name
             (mv-nth 1 (if (eq kind :datum)
                           (boymoo-compiler::data-datum parsed packages state-data)
                         (boymoo-compiler::data-list-datum parsed packages state-data reversed)))))
   :rule-classes nil
   :hints (("Goal" :induct (data-datum-state-induction kind parsed packages state-data reversed)))))

(defthm data-datum-preserves-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-datum-storage-input-p :datum parsed))
           (data-home-available-state-p
            number name (mv-nth 1 (boymoo-compiler::data-datum parsed packages state-data))))
  :hints (("Goal" :use ((:instance datum-pass-preserves-available-home (kind :datum) (reversed nil)))
                  :in-theory (disable boymoo-compiler::data-datum data-datum-storage-input-p))))

(local
 (in-theory (disable boymoo-compiler::data-datum boymoo-compiler::data-list-datum
                     data-datum-storage-input-p)))

(defthm data-constant-preserves-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-constant-storage-input-p text))
           (data-home-available-state-p number name (boymoo-compiler::data-constant text packages state-data))))

(defthm data-note-symbol-preserves-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-symbol-storage-input-p text))
           (data-home-available-state-p number name (boymoo-compiler::data-note-symbol text packages state-data))))

(local
 (in-theory (disable boymoo-compiler::data-note-symbol boymoo-compiler::data-constant
                     data-constant-storage-input-p)))

(defthm data-formals-preserve-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-formals-storage-input-p formals))
           (data-home-available-state-p number name (boymoo-compiler::data-formals formals packages state-data)))
  :hints (("Goal" :induct (boymoo-compiler::data-formals formals packages state-data))))

(local (in-theory (disable boymoo-compiler::data-formals data-formals-storage-input-p)))

(local
 (defthm term-pass-preserves-available-home
   (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                 (data-home-available-state-p number name state-data) (data-term-storage-input-p kind parsed depth))
            (data-home-available-state-p
             number name
             (if (eq kind :term)
                 (boymoo-compiler::data-term parsed packages state-data depth)
               (boymoo-compiler::data-terms parsed packages state-data depth))))
   :rule-classes nil
   :hints (("Goal" :induct (data-term-state-induction kind parsed packages state-data depth)))))

(defthm data-term-preserves-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-term-storage-input-p :term parsed depth))
           (data-home-available-state-p number name (boymoo-compiler::data-term parsed packages state-data depth)))
  :hints (("Goal" :use ((:instance term-pass-preserves-available-home (kind :term)))
                  :in-theory (disable boymoo-compiler::data-term data-term-storage-input-p))))

(defthm data-term-list-preserves-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-term-storage-input-p :terms parsed depth))
           (data-home-available-state-p number name (boymoo-compiler::data-terms parsed packages state-data depth)))
  :hints (("Goal" :use ((:instance term-pass-preserves-available-home (kind :terms)))
                  :in-theory (disable boymoo-compiler::data-terms data-term-storage-input-p))))

(local
 (in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms data-term-storage-input-p)))

(defthm data-definitions-preserve-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-definitions-storage-input-p definitions))
           (data-home-available-state-p
            number name (boymoo-compiler::data-definitions definitions packages state-data)))
  :hints (("Goal" :induct (boymoo-compiler::data-definitions definitions packages state-data))))

(local (in-theory (disable boymoo-compiler::data-definitions data-definitions-storage-input-p)))

(defthm data-program-symbols-preserve-available-home
  (implies (and (natp number) (stringp name) (data-natural-table-values-p packages 12)
                (data-home-available-state-p number name state-data) (data-program-storage-input-p lines))
           (data-home-available-state-p number name (boymoo-compiler::data-program-symbols lines packages state-data)))
  :hints (("Goal" :induct (boymoo-compiler::data-program-symbols lines packages state-data))))
