(in-package "BOYMOO-PROOFS")

(include-book "constant-retention")

(logic)
(set-verify-guards-eagerness 0)

; Each visit records the entry just after the selected quote is handled.
; The states between visits come from the compiler's own data passes.
(defun data-term-quote-visits (kind parsed query packages state-data depth)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
  (if (eq kind :term)
      (cond ((or (< 10000 depth) (atom parsed)) nil)
            ((equal (car parsed) boymoo-compiler::*quote-name*)
             (if (and (equal (cadr parsed) query) (stringp query) (null (cddr parsed)))
                 (list (boymoo-compiler::index-get
                        query (cadr (boymoo-compiler::data-term parsed packages state-data depth))))
               nil))
            ((consp (car parsed))
             (let* ((head (car parsed))
                    (named (boymoo-compiler::data-note-symbol (car head) packages state-data))
                    (bound (boymoo-compiler::data-formals
                            (boymoo-compiler::declaration-list (cadr head)) packages named))
                    (body (boymoo-compiler::data-term (caddr head) packages bound (1+ depth))))
               (append (data-term-quote-visits :term (caddr head) query packages bound (1+ depth))
                       (data-term-quote-visits :terms (cdr parsed) query packages body (1+ depth)))))
            (t (data-term-quote-visits :terms (cdr parsed) query packages
                                      (boymoo-compiler::data-note-symbol (car parsed) packages state-data) (1+ depth))))
    (if (atom parsed)
        nil
      (append (data-term-quote-visits :term (car parsed) query packages state-data depth)
              (data-term-quote-visits :terms (cdr parsed) query packages
                                     (boymoo-compiler::data-term (car parsed) packages state-data depth) depth)))))

(defun data-term-quote-count (kind parsed query)
  (declare (xargs :measure (+ (* 2 (acl2-count parsed)) (if (eq kind :term) 1 0))))
  (if (eq kind :term)
      (cond ((atom parsed) 0)
            ((equal (car parsed) boymoo-compiler::*quote-name*) (if (equal query (cadr parsed)) 1 0))
            ((consp (car parsed))
             (+ (data-term-quote-count :term (caddar parsed) query)
                (data-term-quote-count :terms (cdr parsed) query)))
            (t (data-term-quote-count :terms (cdr parsed) query)))
    (if (atom parsed)
        0
      (+ (data-term-quote-count :term (car parsed) query)
         (data-term-quote-count :terms (cdr parsed) query)))))

(local
 (in-theory (disable boymoo-compiler::index-get boymoo-compiler::data-note-symbol
                     boymoo-compiler::data-formals boymoo-compiler::declaration-list
                     boymoo-compiler::data-constant boymoo-compiler::data-atom
                     data-table-p data-constant-token-key-p)))

(local
 (defthm len-of-joined-quote-visits
   (equal (len (append first rest)) (+ (len first) (len rest)))))

(local
 (defthm quote-visit-is-from-one-of-the-joined-traversals
   (iff (member-equal entry (append first rest))
        (or (member-equal entry first) (member-equal entry rest)))))

(defthmd data-term-quote-visits-count-every-occurrence
  (implies (and (data-term-constant-keys-p kind parsed depth) (stringp query))
           (equal (len (data-term-quote-visits kind parsed query packages state-data depth))
                  (data-term-quote-count kind parsed query)))
  :hints (("Goal" :induct (data-term-quote-visits kind parsed query packages state-data depth)
                  :in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms))))

(defthmd data-term-retains-each-present-quote-visit
  (let ((result (if (eq kind :term) (boymoo-compiler::data-term parsed packages state-data depth)
                  (boymoo-compiler::data-terms parsed packages state-data depth))))
    (implies (and (data-term-constant-keys-p kind parsed depth) (stringp query)
                  (data-table-p (cadr state-data) 12) entry
                  (member-equal entry (data-term-quote-visits kind parsed query packages state-data depth)))
             (equal (boymoo-compiler::index-get query (cadr result)) entry)))
  :hints (("Goal" :induct (data-term-quote-visits kind parsed query packages state-data depth)
                  :in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms data-term-constant-keys-p)
                  :expand ((boymoo-compiler::data-term parsed packages state-data depth)
                           (boymoo-compiler::data-terms parsed packages state-data depth)
                           (:free (mode) (data-term-constant-keys-p mode parsed depth))))))

(local
 (in-theory (disable boymoo-compiler::data-term boymoo-compiler::data-terms data-term-constant-keys-p
                     data-term-quote-visits data-term-quote-count)))

(defun data-definition-quote-visits (items query packages state-data)
  (if (atom items)
      nil
    (let* ((definition (car items))
           (named (boymoo-compiler::data-note-symbol (car definition) packages state-data))
           (bound (boymoo-compiler::data-formals
                   (boymoo-compiler::declaration-list (cadr definition)) packages named))
           (next (boymoo-compiler::data-term (caddr definition) packages bound 0)))
      (append (data-term-quote-visits :term (caddr definition) query packages bound 0)
              (data-definition-quote-visits (cdr items) query packages next)))))

(defun data-definition-quote-count (items query)
  (if (atom items)
      0
    (+ (data-term-quote-count :term (caddar items) query)
       (data-definition-quote-count (cdr items) query))))

(defthmd data-definition-quote-visits-count-every-occurrence
  (implies (and (data-definition-constant-keys-p items) (stringp query))
           (equal (len (data-definition-quote-visits items query packages state-data))
                  (data-definition-quote-count items query)))
  :hints (("Goal" :induct (data-definition-quote-visits items query packages state-data)
                  :in-theory (enable data-term-quote-visits-count-every-occurrence))))

(defthmd data-definitions-retain-each-present-quote-visit
  (implies (and (data-definition-constant-keys-p items) (stringp query)
                (data-table-p (cadr state-data) 12) entry
                (member-equal entry (data-definition-quote-visits items query packages state-data)))
           (equal (boymoo-compiler::index-get
                   query (cadr (boymoo-compiler::data-definitions items packages state-data)))
                  entry))
  :hints (("Goal" :induct (data-definition-quote-visits items query packages state-data)
                  :in-theory (disable data-term-retains-each-present-quote-visit))
          ("Subgoal *1/2"
           :use ((:instance data-term-retains-each-present-quote-visit
                            (kind :term) (parsed (caddar items)) (depth 0)
                            (state-data (boymoo-compiler::data-formals
                                         (boymoo-compiler::declaration-list (cadar items)) packages
                                         (boymoo-compiler::data-note-symbol (caar items) packages state-data))))
                 (:instance data-definitions-retain-constant-entry
                            (definitions (cdr items))
                            (state-data (boymoo-compiler::data-term
                                         (caddar items) packages
                                         (boymoo-compiler::data-formals
                                          (boymoo-compiler::declaration-list (cadar items)) packages
                                          (boymoo-compiler::data-note-symbol (caar items) packages state-data)) 0))))
           :in-theory (disable data-definitions-retain-constant-entry))))

(local
 (in-theory (disable boymoo-compiler::data-definitions data-definition-constant-keys-p
                     data-definition-quote-visits data-definition-quote-count boymoo-compiler::data-datum)))

(defun data-program-quote-visits (lines query packages state-data)
  (if (atom lines)
      nil
    (let* ((line (car lines))
           (next (boymoo-compiler::data-program-symbols (list line) packages state-data))
           (visits (and (equal (car line) "define")
                        (mv-let (rulers named) (boymoo-compiler::data-datum (cadr line) packages state-data)
                          (declare (ignore rulers))
                          (data-definition-quote-visits (cddr line) query packages named)))))
      (append visits (data-program-quote-visits (cdr lines) query packages next)))))

(defun data-program-quote-count (lines query)
  (if (atom lines)
      0
    (+ (if (equal (caar lines) "define") (data-definition-quote-count (cddar lines) query) 0)
       (data-program-quote-count (cdr lines) query))))

(defthm data-program-symbols-cons-is-a-single-line-pass
  (equal (boymoo-compiler::data-program-symbols (cons line rest) packages state-data)
         (boymoo-compiler::data-program-symbols
          rest packages (boymoo-compiler::data-program-symbols (list line) packages state-data)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable boymoo-compiler::data-formals))))

(local
 (in-theory (disable boymoo-compiler::data-program-symbols)))

(defthmd data-program-quote-visits-count-every-occurrence
  (implies (and (data-program-constant-keys-p lines) (stringp query))
           (equal (len (data-program-quote-visits lines query packages state-data))
                  (data-program-quote-count lines query)))
  :hints (("Goal" :induct (data-program-quote-visits lines query packages state-data)
                  :in-theory (enable data-definition-quote-visits-count-every-occurrence))))

(defthmd data-program-retains-each-present-quote-visit
  (implies (and (data-program-constant-keys-p lines) (stringp query)
                (data-table-p (cadr state-data) 12) entry
                (member-equal entry (data-program-quote-visits lines query packages state-data)))
           (equal (boymoo-compiler::index-get
                   query (cadr (boymoo-compiler::data-program-symbols lines packages state-data)))
                  entry))
  :hints (("Goal" :induct (data-program-quote-visits lines query packages state-data)
                  :in-theory (e/d (data-definitions-retain-each-present-quote-visit)
                                 (data-datum-token-keys-p)))
          ("Subgoal *1/2" :use ((:instance data-program-symbols-cons-is-a-single-line-pass
                                           (line (car lines)) (rest (cdr lines))))
                          :expand ((data-program-constant-keys-p (list (car lines)))
                                   (boymoo-compiler::data-program-symbols (list (car lines)) packages state-data)))))

(defun data-build-quote-visits (lines package-lines query)
  (let* ((packages (boymoo-compiler::data-package-numbers package-lines 0 nil))
         (common-lisp (boymoo-compiler::index-get "COMMON-LISP" packages)))
    (if (not common-lisp)
        nil
      (mv-let (nil-name t-name initial) (boymoo-compiler::data-initial common-lisp)
        (declare (ignore nil-name t-name))
        (mv-let (package-word after-packages) (boymoo-compiler::data-packages package-lines 0 packages initial nil)
          (declare (ignore package-word))
          (data-program-quote-visits lines query packages after-packages))))))

(local
 (in-theory (disable boymoo-compiler::data-packages boymoo-compiler::data-package-numbers
                     data-program-quote-visits data-program-quote-count data-program-constant-keys-p)))

(local
 (defthm initial-quote-index-is-a-table
   (data-table-p (cadr (mv-nth 2 (boymoo-compiler::data-initial number))) 12)))

(local (in-theory (disable boymoo-compiler::data-initial)))

(defthmd data-build-quote-visits-count-every-occurrence
  (implies (and (data-program-constant-keys-p lines) (stringp query)
                (boymoo-compiler::index-get "COMMON-LISP"
                                            (boymoo-compiler::data-package-numbers package-lines 0 nil)))
           (equal (len (data-build-quote-visits lines package-lines query)) (data-program-quote-count lines query)))
  :hints (("Goal" :in-theory (enable data-program-quote-visits-count-every-occurrence))))

(defthmd data-build-retains-each-present-quote-visit
  (implies (and (data-program-constant-keys-p lines) (stringp query) entry
                (member-equal entry (data-build-quote-visits lines package-lines query)))
           (equal (boymoo-compiler::index-get query (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))
                  entry))
  :hints (("Goal" :use (data-build-image-and-index)
                  :in-theory (e/d (data-program-retains-each-present-quote-visit)
                                 (boymoo-compiler::data-build boymoo-compiler::data-bucket-vector
                                  boymoo-compiler::data-write boymoo-compiler::reverse-onto)))))
