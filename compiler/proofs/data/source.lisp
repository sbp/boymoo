(in-package "BOYMOO-PROOFS")

(include-book "attachments")
(include-book "entry")

(logic)
(set-verify-guards-eagerness 0)

(defun data-source-symbol-agrees-p (text name)
  (and (stringp text) (symbolp name)
       (let ((split (boymoo-compiler::symbol-separator text)))
         (and split
              (equal (boymoo-compiler::decode-symbol-part text 0 split)
                     (symbol-package-name name))
              (equal (boymoo-compiler::decode-symbol-part text (+ split 2) (length text))
                     (symbol-name name))))))

(defun data-source-symbols-agree-p (texts names)
  (if (atom texts)
      (and (null texts) (null names))
    (and (consp names) (data-source-symbol-agrees-p (car texts) (car names))
         (data-source-symbols-agree-p (cdr texts) (cdr names)))))

(local
 (in-theory (disable data-source-symbol-agrees-p)))

(defthm data-source-symbols-have-equal-arity
  (implies (data-source-symbols-agree-p texts names)
           (equal (len texts) (len names)))
  :rule-classes nil)

; The quote binding pairs one preserved token with the datum it spells.
; In a lambda, the formals and body belong to the callee's own scope.
(mutual-recursion
 (defun data-source-term-agrees-p (parsed term constants)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count parsed)))))
   (cond ((atom parsed) (data-source-symbol-agrees-p parsed term))
         ((equal (car parsed) boymoo-compiler::*quote-name*)
          (let ((binding (assoc-equal (cadr parsed) constants)))
            (and (eq (car term) 'quote) (consp (cdr term)) (null (cddr term))
                 (stringp (cadr parsed)) (null (cddr parsed))
                 binding (equal (cdr binding) (cadr term)))))
         ((consp (car parsed))
          (let ((head (car parsed)) (source (car term)))
            (and (equal (car head) "COMMON-LISP::LAMBDA") (null (cdddr head))
                 (eq (car source) 'lambda) (consp (cddr source)) (null (cdddr source))
                 (data-source-symbols-agree-p
                  (boymoo-compiler::declaration-list (cadr head)) (cadr source))
                 (data-source-term-agrees-p (caddr head) (caddr source) constants)
                 (data-source-terms-agree-p (cdr parsed) (cdr term) constants))))
         (t (and (consp term) (data-source-symbol-agrees-p (car parsed) (car term))
                 (data-source-terms-agree-p (cdr parsed) (cdr term) constants)))))
 (defun data-source-terms-agree-p (parsed terms constants)
   (declare (xargs :measure (* 2 (acl2-count parsed))))
   (if (atom parsed)
       (and (null parsed) (null terms))
     (and (consp terms)
          (data-source-term-agrees-p (car parsed) (car terms) constants)
          (data-source-terms-agree-p (cdr parsed) (cdr terms) constants)))))

(defun data-source-definition-agrees-p (parsed definition constants)
  (if parsed
      (and (consp definition) (data-source-symbol-agrees-p (car parsed) (car definition))
           (data-source-symbols-agree-p (boymoo-compiler::declaration-list (cadr parsed))
                                       (cadr definition))
           (data-source-term-agrees-p (caddr parsed) (caddr definition) constants))
    (null definition)))

(defun data-source-arity (definition)
  (and definition (len (cadr definition))))

(defthm data-related-definition-has-source-arity
  (implies (data-source-definition-agrees-p parsed definition constants)
           (equal (data-definition-arity parsed) (data-source-arity definition)))
  :hints (("Goal" :use ((:instance data-source-symbols-have-equal-arity
                                   (texts (boymoo-compiler::declaration-list (cadr parsed)))
                                   (names (cadr definition))))
                  :in-theory (disable data-source-term-agrees-p data-source-symbols-agree-p))))

(defthmd data-index-arity-for-source-definition
  (implies (and (stringp query) (data-indexable-lines-p lines nil nil)
                (data-source-definition-agrees-p (data-latest-definition query lines)
                                                 (boymoo-model::core-definition name program)
                                                 constants))
           (equal (boymoo-compiler::index-get
                   query (mv-nth 1 (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)))
                  (data-source-arity (boymoo-model::core-definition name program))))
  :hints (("Goal" :use ((:instance data-index-lines-latest-arity
                                   (definitions nil) (arities nil) (attachments nil) (sources nil)
                                   (packages nil) (entry nil) (target nil)))
                  :in-theory (disable boymoo-compiler::index-lines boymoo-compiler::index-get
                                      boymoo-model::core-definition data-latest-definition
                                      data-definition-arity data-source-definition-agrees-p))))

(defun data-source-attachment-path-p (path args program)
  (and (consp path) (symbolp (car path))
       (if (atom (cdr path))
           (null (cdr path))
         (and (not (boymoo-model::core-primitive (car path) args program))
              (let ((attachment (boymoo-model::core-attachment (car path) program)))
                (and attachment (equal (cadr attachment) (cadr path))))
              (data-source-attachment-path-p (cdr path) args program)))))

(local
 (defthm core-call-along-one-attachment
   (implies (and (posp fuel) (not (boymoo-model::core-primitive name args program))
                 (boymoo-model::core-attachment name program))
            (equal (boymoo-model::core-call name args program fuel)
                   (boymoo-model::core-call (cadr (boymoo-model::core-attachment name program))
                                          args program (1- fuel))))
   :hints (("Goal" :in-theory (enable boymoo-model::core-eval-step)))))

(defthmd data-source-call-along-attachment-path
  (implies (and (data-source-attachment-path-p path args program) (natp fuel))
           (equal (boymoo-model::core-call (car path) args program (+ fuel (1- (len path))))
                  (boymoo-model::core-call (data-attachment-terminal path) args program fuel)))
  :hints (("Goal" :induct (data-source-attachment-path-p path args program)
                  :in-theory (disable boymoo-model::core-call boymoo-model::core-attachment))))

(local
 (defthm related-paths-have-related-terminals
   (implies (and (consp text-path) (data-source-symbols-agree-p text-path symbol-path))
            (data-source-symbol-agrees-p (data-attachment-terminal text-path)
                                         (data-attachment-terminal symbol-path)))
   :hints (("Goal" :induct (data-source-symbols-agree-p text-path symbol-path)))))

(defthmd data-resolved-attachment-agrees-with-source-path
  (implies (and (data-resolution-pre-p text-path attachments resolved resolution-fuel)
                (consp text-path) (data-source-symbols-agree-p text-path symbol-path)
                (data-source-attachment-path-p symbol-path args program) (natp source-fuel))
           (let ((target (car (boymoo-compiler::resolve-chain
                               (car text-path) attachments resolved resolution-fuel)))
                 (source-target (data-attachment-terminal symbol-path)))
             (and (data-source-symbol-agrees-p target source-target)
                  (equal (boymoo-model::core-call (car symbol-path) args program
                                                  (+ source-fuel (1- (len text-path))))
                         (boymoo-model::core-call source-target args program source-fuel)))))
  :hints (("Goal" :use ((:instance data-resolve-chain-terminal (path text-path) (fuel resolution-fuel))
                       (:instance data-source-symbols-have-equal-arity (texts text-path) (names symbol-path))
                       (:instance data-source-call-along-attachment-path (path symbol-path) (fuel source-fuel)))
                  :in-theory (disable data-resolution-pre-p data-source-symbols-agree-p
                                      data-source-attachment-path-p data-attachment-terminal
                                      boymoo-compiler::resolve-chain boymoo-model::core-call))))
