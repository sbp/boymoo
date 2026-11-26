(in-package "BOYMOO-PROOFS")

(include-book "operand-registers")
(include-book "stack-prefix")
(include-book "tagged-constants")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-compiler::gen-simple boymoo-compiler::gen-simple-args boymoo-compiler::gen-slot
                    boymoo-compiler::index-get boymoo-compiler::gen-load-datum boymoo-compiler::gen-datum
                    boymoo-compiler::gen-frame-word boymoo-compiler::gen-load-word boymoo-compiler::gen-simple-p
                    boymoo-compiler::symbol-separator boymoo-compiler::decode-symbol-part
                    boymoo-model::core-eval-step boymoo-model::a64-unsigned
                    proof-world-reg proof-world-pc proof-world-stop proof-world-machine proof-heap-base
                    proof-constant-word proof-constant-map-p proof-environment-p proof-subspan-p proof-span-p
                    proof-value-p proof-reg-value-p proof-machine-value-p proof-register-arguments-p proof-segment-p
                    generated-register-arguments-have-operand-views generated-frame-load-path generated-frame-load-items
                    generated-path-after generated-path-p generated-wide-word-items generated-move-instructions expt))

(defund generated-variable-text-p (text variable)
  (and (stringp text) (symbolp variable)
       (let ((split (boymoo-compiler::symbol-separator text)))
         (and split
              (equal (boymoo-compiler::decode-symbol-part text 0 split)
                     (acl2::symbol-package-name variable))
              (equal (boymoo-compiler::decode-symbol-part text (+ split 2) (length text))
                     (symbol-name variable))))))

(defund generated-simple-operand-agrees-p (term source scope slots quoted)
  (if (atom term)
      (and (generated-variable-text-p term source)
           (member-equal (cons source (boymoo-compiler::gen-slot term scope)) slots))
    (and (stringp (cadr term))
         (equal term (list boymoo-compiler::*quote-name* (cadr term)))
         (equal source (list 'quote (cadr source)))
         (member-equal (cons (cadr term) (cadr source)) quoted))))

(defun generated-simple-operands-agree-p (terms sources scope slots quoted)
  (if (atom terms)
      (and (null terms) (null sources))
    (and (consp sources)
         (generated-simple-operand-agrees-p (car terms) (car sources) scope slots quoted)
         (generated-simple-operands-agree-p (cdr terms) (cdr sources) scope slots quoted))))

(defun generated-simple-source-value (source env)
  (if (symbolp source) (cdr (assoc-eq source env)) (cadr source)))

(defun generated-simple-source-values (sources env)
  (if (atom sources)
      nil
    (cons (generated-simple-source-value (car sources) env)
          (generated-simple-source-values (cdr sources) env))))

(defthm generated-constant-binding-has-represented-word
  (let ((word (proof-constant-word (boymoo-compiler::index-get text constants))))
    (implies (and (proof-constant-map-p quoted constants base objects packages machine)
                  (member-equal (cons text datum) quoted))
             (and word (proof-value-p word datum base objects packages machine))))
  :hints (("Goal" :induct (len quoted) :in-theory (enable proof-constant-map-p)))
  :rule-classes nil)

(defun generated-simple-operand-items (term register scope constants)
  (if (atom term)
      (generated-frame-load-items register (boymoo-compiler::gen-slot term scope))
    (generated-wide-word-items register
                              (proof-constant-word (boymoo-compiler::index-get (cadr term) constants)))))

(defun generated-simple-operand-path (term register scope constants)
  (if (atom term)
      (generated-frame-load-path register (boymoo-compiler::gen-slot term scope))
    (generated-move-instructions
     (generated-wide-word-items register
                               (proof-constant-word (boymoo-compiler::index-get (cadr term) constants))))))

(local
 (defthm generated-present-constant-emits-word-items
   (implies (proof-constant-word entry)
            (equal (boymoo-compiler::gen-load-datum register entry code)
                   (boymoo-compiler::reverse-onto
                    (generated-wide-word-items register (proof-constant-word entry)) code)))
   :hints (("Goal" :cases ((consp entry))
                   :in-theory (enable proof-constant-word proof-immediate-integer-p))
           ("Subgoal 2" :in-theory (enable boymoo-compiler::gen-load-datum proof-constant-word
                                           proof-immediate-integer-p)))))

(defthm generated-simple-operand-emission
  (implies (and (generated-simple-operand-agrees-p term source scope slots quoted)
                (proof-constant-map-p quoted constants base objects packages machine))
           (equal (boymoo-compiler::gen-simple term register scope constants code)
                  (boymoo-compiler::reverse-onto
                   (generated-simple-operand-items term register scope constants) code)))
  :hints (("Goal"
           :use (:instance generated-constant-binding-has-represented-word
                           (text (cadr term)) (datum (cadr source)))
           :in-theory (enable generated-simple-operand-agrees-p boymoo-compiler::gen-simple
                              boymoo-compiler::gen-datum)))
  :rule-classes nil)

(defun generated-simple-register-items (terms register scope constants)
  (if (atom terms)
      nil
    (append (generated-simple-operand-items (car terms) register scope constants)
            (generated-simple-register-items (cdr terms) (1+ register) scope constants))))

(defun generated-simple-register-path (terms register scope constants)
  (if (atom terms)
      nil
    (append (generated-simple-operand-path (car terms) register scope constants)
            (generated-simple-register-path (cdr terms) (1+ register) scope constants))))

(local
 (defun generated-simple-register-emission-induction (terms sources register scope constants code)
   (if (atom terms)
       (cons sources code)
     (generated-simple-register-emission-induction
      (cdr terms) (cdr sources) (1+ register) scope constants
      (boymoo-compiler::gen-simple (car terms) register scope constants code)))))

(defthm generated-simple-register-emission
  (implies (and (generated-simple-operands-agree-p terms sources scope slots quoted)
                (proof-constant-map-p quoted constants base objects packages machine))
           (equal (boymoo-compiler::gen-simple-args terms register scope constants code)
                  (boymoo-compiler::reverse-onto
                   (generated-simple-register-items terms register scope constants) code)))
  :hints (("Goal"
           :induct (generated-simple-register-emission-induction terms sources register scope constants code)
           :in-theory (e/d (boymoo-compiler::gen-simple-args)
                           (generated-simple-operand-items boymoo-compiler::reverse-onto)))
          ("Subgoal *1/2"
           :use (:instance generated-simple-operand-emission (term (car terms)) (source (car sources))))
          ("Subgoal *1/1" :in-theory (enable boymoo-compiler::gen-simple-args boymoo-compiler::reverse-onto)))
  :rule-classes nil)

(defthm generated-agreeing-simple-operands-are-simple
  (implies (generated-simple-operands-agree-p terms sources scope slots quoted)
           (and (true-listp terms) (true-listp sources)
                (equal (len sources) (len terms))
                (boymoo-compiler::gen-simple-args-p terms)))
  :hints (("Goal" :induct (generated-simple-operands-agree-p terms sources scope slots quoted)
                  :in-theory (enable generated-simple-operand-agrees-p boymoo-compiler::gen-simple-p))))

(defcong generated-memory-equiv equal (proof-constant-map-p quoted constants base objects packages machine) 6
  :hints (("Goal" :induct (len quoted) :in-theory (enable proof-constant-map-p proof-value-p))))

(local
 (defthm generated-constant-word-is-unsigned
   (implies (proof-constant-word entry) (unsigned-byte-p 64 (proof-constant-word entry)))
   :hints (("Goal" :in-theory (enable proof-constant-word proof-integer-word)))))

(local
 (defthm generated-simple-variable-loads-value
   (let* ((frame (proof-world-reg 19 before)) (slot (boymoo-compiler::gen-slot term scope))
          (path (generated-frame-load-path register slot))
          (after (generated-path-after path before))
          (end (+ (proof-world-pc before) (* 4 (len path)))))
     (implies (and (atom term) (natp register) (< register 17)
                   (generated-simple-operand-agrees-p term source scope slots quoted)
                   (proof-environment-p slots env frame before objects packages) (< end (expt 2 64)))
              (and (proof-reg-value-p register (generated-simple-source-value source env) after objects packages)
                   (equal (proof-world-pc after) end)
                   (generated-heap-world-equiv after before)
                   (implies (and (not (equal other register)) (not (equal other 17)))
                            (equal (proof-world-reg other after) (proof-world-reg other before))))))
   :hints (("Goal"
            :use ((:instance generated-environment-binding (variable source)
                             (slot (boymoo-compiler::gen-slot term scope)) (bindings slots)
                             (frame (proof-world-reg 19 before)) (world before))
                  (:instance generated-frame-load-observations (slot (boymoo-compiler::gen-slot term scope))))
            :in-theory (enable generated-simple-operand-agrees-p generated-variable-text-p
                               proof-subspan-p proof-span-p proof-reg-value-p)))
   :rule-classes nil))

(local
 (defthm generated-simple-constant-loads-value
   (let* ((word (proof-constant-word (boymoo-compiler::index-get (cadr term) constants)))
          (path (generated-move-instructions (generated-wide-word-items register word)))
          (after (generated-path-after path before))
          (end (+ (proof-world-pc before) (* 4 (len path)))))
     (implies (and (consp term) (natp register) (< register 17)
                   (generated-simple-operand-agrees-p term source scope slots quoted)
                   (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                         (proof-world-machine before))
                   (< end (expt 2 64)))
              (and (proof-reg-value-p register (generated-simple-source-value source env) after objects packages)
                   (equal (proof-world-pc after) end)
                   (generated-heap-world-equiv after before)
                   (implies (and (not (equal other register)) (not (equal other 17)))
                            (equal (proof-world-reg other after) (proof-world-reg other before))))))
   :hints (("Goal"
            :use ((:instance generated-constant-binding-has-represented-word
                             (text (cadr term)) (datum (cadr source))
                             (base (proof-heap-base before)) (machine (proof-world-machine before)))
                  (:instance generated-wide-word-loads-value
                             (rd register)
                             (word (proof-constant-word (boymoo-compiler::index-get (cadr term) constants)))))
            :in-theory (enable generated-simple-operand-agrees-p proof-reg-value-p proof-machine-value-p
                               proof-value-p)))
   :rule-classes nil))

(defthm generated-simple-operand-loads-value
  (let* ((path (generated-simple-operand-path term register scope constants))
         (after (generated-path-after path before))
         (end (+ (proof-world-pc before) (* 4 (len path)))))
    (implies (and (natp register) (< register 17) (< end (expt 2 64))
                  (generated-simple-operand-agrees-p term source scope slots quoted)
                  (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                  (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                        (proof-world-machine before)))
             (and (proof-reg-value-p register (generated-simple-source-value source env) after objects packages)
                  (equal (proof-world-pc after) end)
                  (generated-heap-world-equiv after before)
                  (implies (and (not (equal other register)) (not (equal other 17)))
                           (equal (proof-world-reg other after) (proof-world-reg other before))))))
  :hints (("Goal" :use (generated-simple-variable-loads-value generated-simple-constant-loads-value)))
  :rule-classes nil)

(local
 (defun generated-simple-register-path-induction (terms sources register scope constants before)
   (if (atom terms)
       (cons sources before)
     (generated-simple-register-path-induction
      (cdr terms) (cdr sources) (1+ register) scope constants
      (generated-path-after (generated-simple-operand-path (car terms) register scope constants) before)))))

(local
 (defthm generated-simple-context-preserved-by-first-load
   (let* ((path (generated-simple-operand-path term register scope constants))
          (after (generated-path-after path before)))
     (implies (and (natp register) (< register 17)
                   (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                   (generated-simple-operand-agrees-p term source scope slots quoted)
                   (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                   (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                         (proof-world-machine before)))
              (and (proof-environment-p slots env (proof-world-reg 19 after) after objects packages)
                   (proof-constant-map-p quoted constants (proof-heap-base after) objects packages
                                         (proof-world-machine after)))))
   :hints (("Goal" :use (:instance generated-simple-operand-loads-value (other 19))
                   :in-theory (disable generated-simple-operand-path)))
   :rule-classes nil))

(defthm generated-simple-register-path-keeps-fields
  (let* ((path (generated-simple-register-path terms register scope constants))
         (after (generated-path-after path before))
         (end (+ (proof-world-pc before) (* 4 (len path)))))
    (implies (and (natp register) (<= (+ register (len terms)) 17) (< end (expt 2 64))
                  (generated-simple-operands-agree-p terms sources scope slots quoted)
                  (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                  (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                        (proof-world-machine before)))
             (and (equal (proof-world-pc after) end)
                  (generated-heap-world-equiv after before)
                  (implies (and (not (equal other 17))
                                (or (< other register) (<= (+ register (len terms)) other)))
                           (equal (proof-world-reg other after) (proof-world-reg other before))))))
  :hints (("Goal"
           :induct (generated-simple-register-path-induction terms sources register scope constants before)
           :in-theory (e/d (generated-path-after) (generated-simple-operand-path)))
          ("Subgoal *1/2"
           :use ((:instance generated-simple-operand-loads-value (term (car terms)) (source (car sources)))
                 (:instance generated-simple-context-preserved-by-first-load (term (car terms)) (source (car sources))))))
  :rule-classes nil)

(local
 (defthm generated-register-arguments-of-cons
   (equal (proof-register-arguments-p (cons value rest) register world objects packages)
          (and (proof-reg-value-p register value world objects packages)
               (proof-register-arguments-p rest (1+ register) world objects packages)))
   :hints (("Goal" :expand (proof-register-arguments-p (cons value rest) register world objects packages)))))

(defthm generated-simple-register-path-loads-source-values
  (let* ((path (generated-simple-register-path terms register scope constants))
         (after (generated-path-after path before))
         (end (+ (proof-world-pc before) (* 4 (len path)))))
    (implies (and (natp register) (<= (+ register (len terms)) 17) (< end (expt 2 64))
                  (generated-simple-operands-agree-p terms sources scope slots quoted)
                  (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                  (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                        (proof-world-machine before)))
             (proof-register-arguments-p (generated-simple-source-values sources env)
                                         register after objects packages)))
  :hints (("Goal"
           :induct (generated-simple-register-path-induction terms sources register scope constants before)
           :in-theory (e/d (generated-path-after) (generated-simple-operand-path)))
          ("Subgoal *1/2"
           :use ((:instance generated-simple-operand-loads-value (term (car terms)) (source (car sources)) (other 19))
                 (:instance generated-simple-context-preserved-by-first-load (term (car terms)) (source (car sources)))
                 (:instance generated-simple-register-path-keeps-fields
                            (terms (cdr terms)) (sources (cdr sources)) (register (1+ register)) (other register)
                            (before (generated-path-after
                                     (generated-simple-operand-path (car terms) register scope constants) before))))
           :in-theory (e/d (generated-path-after proof-reg-value-p) (generated-simple-operand-path)))
          ("Subgoal *1/1" :in-theory (enable proof-register-arguments-p generated-path-after)))
  :rule-classes nil)

(local
 (defun generated-simple-source-fuel-induction (terms sources fuel)
   (if (atom terms)
       (cons sources fuel)
     (generated-simple-source-fuel-induction (cdr terms) (cdr sources) (1- fuel)))))

(defthm generated-simple-source-values-agree-with-evaluation
  (let ((result (boymoo-model::core-eval-step :terms sources env program fuel)))
    (implies (and (generated-simple-operands-agree-p terms sources scope slots quoted)
                  (boymoo-model::core-value-p result))
             (equal result (boymoo-model::core-value (generated-simple-source-values sources env)))))
  :hints (("Goal" :induct (generated-simple-source-fuel-induction terms sources fuel))
          ("Subgoal *1/2"
           :expand ((boymoo-model::core-eval-step :terms sources env program fuel)
                    (boymoo-model::core-eval-step :term (car sources) env program (1- fuel)))
           :in-theory (enable generated-simple-operand-agrees-p generated-variable-text-p))
          ("Subgoal *1/1" :in-theory (enable boymoo-model::core-eval-step)))
  :rule-classes nil)

(defthm generated-simple-registers-load-source-arguments
  (let* ((path (generated-simple-register-path terms register scope constants))
         (after (generated-path-after path before))
         (end (+ (proof-world-pc before) (* 4 (len path))))
         (result (boymoo-model::core-eval-step :terms sources env program fuel)))
    (implies (and (natp register) (<= (+ register (len terms)) 17) (< end (expt 2 64))
                  (generated-simple-operands-agree-p terms sources scope slots quoted)
                  (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                  (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                        (proof-world-machine before))
                  (boymoo-model::core-value-p result)
                  (not (proof-world-stop before)) (generated-path-p path (list end) before))
             (and (proof-segment-p (len path) (list end) before :cut after)
                  (equal (proof-world-pc after) end)
                  (proof-register-arguments-p (boymoo-model::core-datum result) register after objects packages)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use (generated-simple-source-values-agree-with-evaluation
                 generated-simple-register-path-loads-source-values
                 (:instance generated-simple-register-path-keeps-fields (other 19))
                 (:instance generated-placed-path-to-cut
                            (instructions (generated-simple-register-path terms register scope constants))
                            (cuts (list (+ (proof-world-pc before)
                                           (* 4 (len (generated-simple-register-path terms register scope constants))))))))
           :in-theory (disable generated-simple-register-path generated-simple-source-values
                               generated-simple-operands-agree-p)))
  :rule-classes nil)

(defthm generated-simple-runtime-call-emission
  (let* ((info (boymoo-compiler::gen-call-info head context))
         (routine (mv-nth 2 info))
         (target (mv-nth 0 info))
         (items (generated-simple-register-items terms 0 scope (caddr context))))
    (implies (and (stringp head) (not (equal head boymoo-compiler::*quote-name*))
                  (not (equal head boymoo-compiler::*if-name*))
                  (not (boymoo-compiler::gen-mbe-p head terms))
                  routine (equal (mv-nth 1 info) (len terms))
                  (generated-simple-operands-agree-p terms sources scope slots quoted)
                  (proof-constant-map-p quoted (caddr context) base objects packages machine))
             (equal (boymoo-compiler::gen-term (cons head terms) scope depth tail context code high serial)
                    (mv-let (routine-code next)
                      (boymoo-compiler::gen-routine target routine serial (boymoo-compiler::reverse-onto items code))
                      (mv (boymoo-compiler::gen-finish tail routine-code) high next)))))
  :hints (("Goal"
           :use ((:instance generated-simple-register-emission (register 0) (constants (caddr context)))
                 generated-agreeing-simple-operands-are-simple)
           :expand (boymoo-compiler::gen-term (cons head terms) scope depth tail context code high serial)
           :in-theory (e/d (boymoo-compiler::gen-simple-p length)
                           (boymoo-compiler::gen-call-info boymoo-compiler::gen-routine boymoo-compiler::gen-finish
                            boymoo-compiler::gen-mbe-p generated-simple-register-items
                            generated-simple-operands-agree-p generated-agreeing-simple-operands-are-simple))))
  :rule-classes nil)
