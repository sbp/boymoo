(in-package "BOYMOO-PROOFS")

(include-book "program-home-availability")
(include-book "trace-agreement")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable data-natural-table-values-p data-table-p
                     data-atom-spells-value-p data-symbol-home-available-p
                     data-symbol-storage-input-p data-formals-storage-input-p
                     boymoo-compiler::data-symbol boymoo-compiler::data-note-symbol boymoo-compiler::data-formals
                     boymoo-compiler::data-constant boymoo-compiler::data-datum boymoo-compiler::data-atom
                     boymoo-compiler::declaration-list boymoo-compiler::index-get
                     data-term-storage-input-p data-term-constant-keys-p)))

(local
 (defthm an-available-state-has-an-available-symbol-home
   (implies (data-home-available-state-p number name state-data)
            (data-symbol-home-available-p number name state-data))))

(local
 (defthm symbol-spelling-is-text
   (implies (data-atom-spells-value-p query symbol) (stringp query))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (e/d (data-atom-spells-value-p)
                                  (data-symbol-spelling-p data-character-text-p
                                   data-rational-text-p data-complex-text-p data-delimited-text-p))))))

(local
 (defthm append-keeps-missing-entries-from-both-lists
   (iff (member-equal nil (append first rest))
        (or (member-equal nil first) (member-equal nil rest)))))

(local (in-theory (disable data-home-available-state-p)))

(defthmd data-term-visits-record-spelled-symbol-constant
  (let ((number (boymoo-compiler::index-get (symbol-package-name symbol) packages)))
    (implies (and (symbolp symbol) (data-atom-spells-value-p query symbol)
                  number (data-natural-table-values-p packages 12)
                  (data-home-available-state-p number (symbol-name symbol) state-data)
                  (data-term-storage-input-p kind parsed depth) (data-term-constant-keys-p kind parsed depth)
                  (data-table-p (cadr state-data) 12))
             (not (member-equal nil (data-term-quote-visits kind parsed query packages state-data depth)))))
  :hints (("Goal" :induct (data-term-quote-visits kind parsed query packages state-data depth)
                  :in-theory (enable data-spelled-symbol-constant-has-an-entry-with-available-home)
                  :expand ((:free (mode) (data-term-storage-input-p mode parsed depth))
                           (:free (mode) (data-term-constant-keys-p mode parsed depth))
                           (boymoo-compiler::data-term parsed packages state-data depth)))))

(local
 (in-theory (disable data-term-quote-visits boymoo-compiler::data-term boymoo-compiler::data-terms
                     boymoo-compiler::data-definitions)))

(defthmd data-definition-visits-record-spelled-symbol-constant
  (let ((number (boymoo-compiler::index-get (symbol-package-name symbol) packages)))
    (implies (and (symbolp symbol) (data-atom-spells-value-p query symbol)
                  number (data-natural-table-values-p packages 12)
                  (data-home-available-state-p number (symbol-name symbol) state-data)
                  (data-definitions-storage-input-p definitions) (data-definition-constant-keys-p definitions)
                  (data-table-p (cadr state-data) 12))
             (not (member-equal nil (data-definition-quote-visits definitions query packages state-data)))))
  :hints (("Goal" :induct (data-definition-quote-visits definitions query packages state-data)
                  :in-theory (enable data-term-visits-record-spelled-symbol-constant))))

(local
 (in-theory (disable data-definition-quote-visits data-definition-constant-keys-p data-definitions-storage-input-p
                     data-datum-storage-input-p data-datum-token-keys-p boymoo-compiler::data-program-symbols)))

(defthmd data-program-visits-record-spelled-symbol-constant
  (let ((number (boymoo-compiler::index-get (symbol-package-name symbol) packages)))
    (implies (and (symbolp symbol) (data-atom-spells-value-p query symbol)
                  number (data-natural-table-values-p packages 12)
                  (data-home-available-state-p number (symbol-name symbol) state-data)
                  (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                  (data-table-p (cadr state-data) 12))
             (not (member-equal nil (data-program-quote-visits lines query packages state-data)))))
  :hints (("Goal" :induct (data-program-quote-visits lines query packages state-data)
                  :in-theory (enable data-definition-visits-record-spelled-symbol-constant))
          ("Subgoal *1/2" :expand ((data-program-storage-input-p (list (car lines)))
                                   (data-program-constant-keys-p (list (car lines)))))))

; The initial home binding for the program pass comes from the full
; package pass, including its imports and package witnesses.
(defun data-build-home-available-p (package-lines symbol)
  (let* ((packages (boymoo-compiler::data-package-numbers package-lines 0 nil))
         (common-lisp (boymoo-compiler::index-get "COMMON-LISP" packages))
         (home (boymoo-compiler::index-get (symbol-package-name symbol) packages)))
    (and common-lisp home
         (mv-let (nil-name t-name initial) (boymoo-compiler::data-initial common-lisp)
           (declare (ignore nil-name t-name))
           (mv-let (package-word after-packages)
             (boymoo-compiler::data-packages package-lines 0 packages initial nil)
             (declare (ignore package-word))
             (data-home-available-state-p home (symbol-name symbol) after-packages))))))

(local
 (in-theory (disable data-program-quote-visits data-program-storage-input-p data-program-constant-keys-p
                     boymoo-compiler::data-packages boymoo-compiler::data-package-numbers)))

(local
 (defthm initial-symbol-visit-constant-index-is-a-table
   (data-table-p (cadr (mv-nth 2 (boymoo-compiler::data-initial number))) 12)))

(local (in-theory (disable boymoo-compiler::data-initial)))

(defthmd data-build-visits-record-spelled-symbol-constant
  (implies (and (symbolp symbol) (data-atom-spells-value-p query symbol)
                (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                (data-build-home-available-p package-lines symbol))
           (not (member-equal nil (data-build-quote-visits lines package-lines query))))
  :hints (("Goal" :in-theory (enable data-program-visits-record-spelled-symbol-constant))))

(local
 (defthm first-entry-occurs-in-nonempty-visits
   (implies (< 0 (len visits)) (member-equal (car visits) visits))))

(defthmd data-build-records-every-spelled-symbol-quote-with-available-home
  (implies (and (symbolp symbol) (data-atom-spells-value-p query symbol)
                (data-program-storage-input-p lines) (data-program-constant-keys-p lines)
                (data-build-home-available-p package-lines symbol) (< 0 (data-program-quote-count lines query)))
           (boymoo-compiler::index-get query (mv-nth 1 (boymoo-compiler::data-build lines package-lines))))
  :hints (("Goal" :use (data-build-visits-record-spelled-symbol-constant
                        data-build-quote-visits-count-every-occurrence
                        (:instance data-build-retains-each-present-quote-visit
                                   (entry (car (data-build-quote-visits lines package-lines query))))
                        (:instance first-entry-occurs-in-nonempty-visits
                                   (visits (data-build-quote-visits lines package-lines query))))
                  :in-theory (disable data-build-quote-visits data-program-quote-count boymoo-compiler::data-build
                                      first-entry-occurs-in-nonempty-visits))))

(local
 (defthm a-spelled-symbol-constant-uses-the-atom-spelling
   (implies (and (symbolp symbol) (data-constant-spells-value-p query quote-events datum symbol))
            (data-atom-spells-value-p query symbol))
   :hints (("Goal" :in-theory (disable data-reader-events data-parsed-datum-spells-value-p)))))

(local
 (in-theory (disable data-build-home-available-p data-program-spans-p data-source-lines-spelled-p
                     data-quote-spellings-p data-constant-spells-value-p data-program-quote-count
                     boymoo-compiler::read-program boymoo-compiler::index-lines boymoo-compiler::data-build)))

(defthmd data-checked-text-records-a-symbol-quote-with-available-home
  (let* ((parsed (boymoo-compiler::read-program text))
         (package-lines (mv-nth 4 (boymoo-compiler::index-lines parsed nil nil nil nil nil nil nil)))
         (value (cdr (assoc-equal query bindings))))
    (implies (and (data-program-spans-p text events lines)
                  (data-source-lines-spelled-p lines sources bindings nil nil)
                  (data-quote-spellings-p bindings witnesses)
                  (< 0 (data-program-quote-count lines query))
                  (symbolp value) (data-build-home-available-p package-lines value))
             (boymoo-compiler::index-get query (mv-nth 1 (boymoo-compiler::data-build parsed package-lines)))))
  :hints (("Goal" :use (data-read-program-gives-source-front-pass-inputs
                        data-checked-program-quote-supplies-its-spelling
                        (:instance data-build-records-every-spelled-symbol-quote-with-available-home
                                   (lines (boymoo-compiler::read-program text))
                                   (package-lines (mv-nth 4 (boymoo-compiler::index-lines
                                                            (boymoo-compiler::read-program text)
                                                            nil nil nil nil nil nil nil)))
                                   (symbol (cdr (assoc-equal query bindings))))))))
