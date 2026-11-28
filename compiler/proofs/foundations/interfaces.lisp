(in-package "BOYMOO-PROOFS")

(include-book "heap")
(include-book "loading")
(include-book "../model/core")
(include-book "../compiler/data")
(include-book "../compiler/macos")
(include-book "../compiler/linux")

(logic)
(set-verify-guards-eagerness 0)

(defun proof-label-address (label base labels)
  (let ((offset (boymoo-compiler::a64-offset label labels)))
    (and (natp offset)
         (unsigned-byte-p 64 base)
         (unsigned-byte-p 64 (+ base offset))
         (+ base offset))))

(defun proof-linked-image-p (items entry base world)
  (mv-let (image offset)
    (boymoo-compiler::a64-assemble-image items entry)
    (and (natp offset) (< offset (car image))
         (equal (mod base 4096) 0)
         (proof-image-at-p image base (proof-world-machine world))
         (proof-covered-p base (car image) :execute (proof-world-regions world)))))

(defun proof-source-result (entry input program fuel)
  (boymoo-model::core-call entry (list input) program fuel))

(defun proof-advance (count world)
  (declare (xargs :measure (nfix count)
                  :hints (("Goal" :in-theory (disable proof-step)))))
  (if (zp count)
      world
    (proof-advance (1- count) (proof-step world))))

(defthm proof-advance-append
  (equal (proof-advance (+ (nfix prefix) (nfix suffix)) world)
         (proof-advance suffix (proof-advance prefix world)))
  :hints (("Goal" :induct (proof-advance prefix world)
                  :in-theory (disable proof-step))))

(defthm proof-step-after-stop
  (implies (proof-world-stop world)
           (equal (proof-step world) world)))

(defthm proof-advance-after-stop
  (implies (proof-world-stop world)
           (equal (proof-advance count world) world))
  :hints (("Goal" :induct (proof-advance count world)
                  :in-theory (disable proof-step))))

(defthm proof-run-reached-without-cuts
  (equal (mv-nth 1 (proof-run count nil world))
         (proof-advance count world))
  :hints (("Goal" :induct (proof-advance count world)
                  :in-theory (disable proof-step))))

(defun proof-public-package-names (packages)
  (if (atom packages)
      nil
    (let ((package (car packages)))
      (if (proof-package-visible package)
          (cons (proof-package-name package) (proof-public-package-names (cdr packages)))
        (proof-public-package-names (cdr packages))))))

(defun proof-hidden-package-witnesses (packages)
  (if (atom packages)
      nil
    (let ((package (car packages)))
      (if (proof-package-visible package)
          (proof-hidden-package-witnesses (cdr packages))
        (cons (proof-package-witness package)
              (proof-hidden-package-witnesses (cdr packages)))))))

(defun proof-core-program (definitions attachments packages)
  (boymoo-model::core-program definitions attachments
                             (proof-public-package-names packages)
                             (proof-hidden-package-witnesses packages)))

(defun proof-program-packages-p (program packages)
  (let ((visible (proof-public-package-names packages)))
    (and (proof-packages-p packages)
         (subsetp-equal '("COMMON-LISP" "KEYWORD" "ACL2"
                          "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL") visible)
         (equal (caddr program) visible)
         (equal (cadddr program) (proof-hidden-package-witnesses packages)))))

(defun proof-machine-value-p (word value world objects packages)
  (proof-value-p word value (proof-heap-base world) objects packages
                 (proof-world-machine world)))

(defun proof-reg-value-p (register value world objects packages)
  (proof-machine-value-p (proof-world-reg register world) value world objects packages))

(defun proof-register-arguments-p (args register world objects packages)
  (if (atom args)
      (null args)
    (and (proof-reg-value-p register (car args) world objects packages)
         (proof-register-arguments-p (cdr args) (+ 1 register) world objects packages))))

(defun proof-argument-views (args)
  (if (atom args)
      nil
    (cons (proof-value-view (car args)) (proof-argument-views (cdr args)))))

(defun proof-compiled-entry-p (address args world objects packages)
  (let* ((arity (len args))
         (start (- (proof-stack-top world) (* 8 arity))))
    (and (true-listp args)
         (equal (proof-world-pc world) address)
         (proof-heap-p world objects packages)
         (<= (proof-stack-base world) start)
         (equal (proof-stack-views arity start (proof-heap-base world)
                                   objects packages (proof-world-machine world))
                (cons :slots (proof-argument-views args))))))

; A binding is (source-variable . slot-number), with slots based at frame.
(defun proof-environment-p (bindings env frame world objects packages)
  (if (atom bindings)
      (null bindings)
    (let* ((binding (car bindings))
           (slot (cdr binding))
           (value (assoc-eq (car binding) env)))
      (and (natp slot) value
           (let ((address (+ frame (* 8 slot))))
             (and (proof-subspan-p address 8 (proof-stack-base world)
                                    (proof-stack-top world))
                  (proof-machine-value-p
                   (proof-load-word address (proof-world-machine world))
                   (cdr value) world objects packages)))
           (proof-environment-p (cdr bindings) env frame world objects packages)))))

; Entries pair canonical texts with the values used by an arity or
; attachment lookup. A known absent binding has value NIL.
(defun proof-index-agrees-p (entries index)
  (if (atom entries)
      (null entries)
    (and (equal (boymoo-compiler::index-get (caar entries) index)
                (cdar entries))
         (proof-index-agrees-p (cdr entries) index))))

(defun proof-constant-word (entry)
  (cond ((and (consp entry) (eq (car entry) :integer)
              (proof-immediate-integer-p (cdr entry)))
         (proof-integer-word (cdr entry)))
        ((unsigned-byte-p 64 entry) entry)
        (t nil)))

(defun proof-constant-map-p (bindings index base objects packages machine)
  (if (atom bindings)
      (null bindings)
    (let* ((entry (boymoo-compiler::index-get (caar bindings) index))
           (word (proof-constant-word entry)))
      (and word
           (proof-value-p word (cdar bindings) base objects packages machine)
           (proof-constant-map-p (cdr bindings) index base objects packages machine)))))

(defun proof-register-frame-p (register clobbers before after)
  (declare (xargs :measure (nfix register)))
  (and (or (member-equal register clobbers)
           (equal (proof-world-reg register before) (proof-world-reg register after)))
       (or (zp register)
           (proof-register-frame-p (1- register) clobbers before after))))

(defun proof-frame-return-p (clobbers changes-flags before after)
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after)))
    (and (not (proof-world-stop before)) (not (proof-world-stop after))
         (equal (proof-world-pc after) (proof-world-reg 30 before))
         (equal (boymoo-model::a64-sp first) (boymoo-model::a64-sp last))
         (or changes-flags
             (equal (boymoo-model::a64-nzcv first) (boymoo-model::a64-nzcv last)))
         (proof-register-frame-p 30 clobbers before after))))

(defun proof-byte-entries-agree-p (entries start end before after)
  (if (atom entries)
      t
    (let ((address (caar entries)))
      (and (if (and (<= start address) (< address end))
               (equal (boymoo-model::a64-byte address before)
                      (boymoo-model::a64-byte address after))
             t)
           (proof-byte-entries-agree-p (cdr entries) start end before after)))))

(defun proof-memory-span-agrees-p (start end before after)
  (let ((first (boymoo-model::a64-memory (proof-world-machine before)))
        (last (boymoo-model::a64-memory (proof-world-machine after))))
    (and (proof-byte-entries-agree-p first start end first last)
         (proof-byte-entries-agree-p last start end first last))))

(defun proof-streams-preserved-p (before after)
  (and (equal (proof-world-input before) (proof-world-input after))
       (equal (proof-world-stdout before) (proof-world-stdout after))
       (equal (proof-world-stderr before) (proof-world-stderr after))
       (equal (proof-world-page-size before) (proof-world-page-size after))))

(defun proof-heap-frame-p (before after)
  (let* ((base (proof-heap-base before))
         (sp (boymoo-model::a64-sp (proof-world-machine before)))
         (machine-end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                         *proof-machine-reservation*)))
    (and (equal base (proof-heap-base after))
         (equal (proof-stack-base before) (proof-stack-base after))
         (equal (proof-stack-end before) (proof-stack-end after))
         (equal (proof-spaces-end before) (proof-spaces-end after))
         (proof-memory-span-agrees-p base (+ base 24) before after)
         (proof-memory-span-agrees-p
          (+ base 32) (+ base (proof-static-size base (proof-world-machine before)))
          before after)
         (proof-memory-span-agrees-p sp machine-end before after)
         (proof-streams-preserved-p before after))))

(defun proof-prefix-preserved-p (top before after old-objects new-objects packages)
  (let ((prefix (proof-stack-prefix top before old-objects packages)))
    (and prefix
         (equal prefix (proof-stack-prefix top after new-objects packages)))))

(defun proof-dynamic-table-preserved-p (may-intern before after old-objects new-objects packages)
  (let ((old (proof-dynamic-view before old-objects packages))
        (new (proof-dynamic-view after new-objects packages)))
    (if may-intern
        (let ((old-entries (proof-dynamic-entries old packages))
              (new-entries (proof-dynamic-entries new packages)))
          (and old-entries new-entries
               (subsetp-eq (cdr old-entries) (cdr new-entries))))
      (equal old new))))

(defun proof-fixed-external-p (mappings before after)
  (if (atom mappings)
      t
    (let* ((base (- (car mappings) 24))
           (size (proof-load-word (+ base 8) (proof-world-machine before))))
      (and (proof-memory-span-agrees-p base (+ base size) before after)
           (proof-fixed-external-p (cdr mappings) before after)))))

(defun proof-fixed-heap-p (before after objects)
  (let ((base (proof-heap-base before))
        (external (proof-external-objects (proof-external-head before)
                                          (len objects) before objects)))
    (and (equal (proof-world-regions before) (proof-world-regions after))
         (equal (proof-world-replies before) (proof-world-replies after))
         (equal (proof-box-top before) (proof-box-top after))
         (equal (proof-heap-limit before) (proof-heap-limit after))
         (proof-memory-span-agrees-p (- base *proof-heap-prefix*)
                                      (proof-spaces-end before) before after)
         external
         (proof-fixed-external-p (cdr external) before after))))

(defun proof-preserved-heap-p (may-intern before after old-objects new-objects packages)
  (and (proof-heap-p after new-objects packages)
       (proof-heap-frame-p before after)
       (proof-prefix-preserved-p (proof-stack-top before)
                                 before after old-objects new-objects packages)
       (proof-dynamic-table-preserved-p may-intern before after old-objects
                                        new-objects packages)))

(defun proof-routine-spelling (name)
  (concatenate 'string (acl2::symbol-package-name name) "::" (symbol-name name)))

(defun proof-runtime-entry (name)
  (let ((spelling (proof-routine-spelling name)))
    (or (assoc-equal spelling boymoo-compiler::*primitives*)
        (assoc-equal spelling boymoo-compiler::*jets*))))

(defun proof-runtime-label (name)
  (cddr (proof-runtime-entry name)))

(defun proof-runtime-value (name args program)
  (or (boymoo-model::core-primitive name args program)
      (boymoo-model::core-prelude name args)))

(defconst *proof-volatile-registers*
  '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17))

(defun proof-runtime-clobbers (name)
  (case name
    ((acl2::bad-atom<= car cdr code-char) '(0))
    (char-code '(0 1))
    ((consp characterp stringp symbolp integerp rationalp complex-rationalp
            acl2-numberp) '(0 1 2))
    ((numerator denominator realpart imagpart) '(0 3 4 5))
    (length '(0 1 2 3))
    (char '(0 1 2 3 4 5))
    ((acl2::pkg-imports acl2::pkg-witness) '(0 1 2 3 4 5 6 7 8 9))
    (equal '(0 1 2 3 4 5 6 7 8 9 10 11 12 24))
    ((symbol-name acl2::symbol-package-name)
     (append *proof-volatile-registers* '(26 27)))
    (otherwise (append *proof-volatile-registers* '(24 26 27)))))

(defun proof-runtime-allocates-p (name args)
  (case name
    ((symbol-name acl2::symbol-package-name) (not (symbolp (car args))))
    ((cons coerce acl2::intern-in-package-of-symbol acl2::binary-+
           acl2::binary-* < complex acl2::unary-- acl2::unary-/
           ash acl2::binary-logxor subseq) t)
    (otherwise nil)))

(defun proof-runtime-pre-p (name args program labels base before objects packages)
  (let ((entry (proof-runtime-entry name)))
    (and entry (true-listp args) (equal (len args) (cadr entry))
         (equal (proof-world-pc before) (proof-label-address (cddr entry) base labels))
         (proof-program-packages-p program packages)
         (proof-heap-p before objects packages)
         (proof-register-arguments-p args 0 before objects packages))))

(defun proof-datum-return-p (datum clobbers changes-flags allocates may-intern
                                  before after old-objects new-objects packages)
  (and (proof-frame-return-p clobbers changes-flags before after)
       (proof-preserved-heap-p may-intern before after old-objects new-objects packages)
       (or allocates (proof-fixed-heap-p before after old-objects))
       (proof-reg-value-p 0 datum after new-objects packages)))

(defun proof-runtime-return-p (name args program before after old-objects new-objects packages)
  (let ((result (proof-runtime-value name args program)))
    (and (boymoo-model::core-value-p result)
         (proof-datum-return-p (boymoo-model::core-datum result)
                               (proof-runtime-clobbers name)
                               (not (eq name 'acl2::bad-atom<=))
                               (proof-runtime-allocates-p name args)
                               (eq name 'acl2::intern-in-package-of-symbol)
                               before after old-objects new-objects packages))))

(defun proof-compiled-return-p (arity result before after old-objects new-objects packages)
  (let ((top (- (proof-stack-top before) (* 8 arity))))
    (and (natp arity)
         (boymoo-model::core-value-p result)
         (proof-frame-return-p (append *proof-volatile-registers* '(24 25 26 27))
                               t before after)
         (proof-heap-p after new-objects packages)
         (proof-heap-frame-p before after)
         (equal (proof-stack-top after) top)
         (proof-prefix-preserved-p top before after old-objects new-objects packages)
         (proof-dynamic-table-preserved-p t before after old-objects new-objects packages)
         (proof-reg-value-p 0 (boymoo-model::core-datum result)
                            after new-objects packages))))

(defun proof-grow-return-p (entry required before after old-objects new-objects packages)
  (and (member-equal entry '("rt:grow" "rt:ensure-stack"))
       (proof-frame-return-p (if (equal entry "rt:grow")
                                 '(8 9 10 11 12 24) '(9 10 11 12 24))
                             t before after)
       (equal (proof-stack-limit after) (proof-grow-limit required before))
       (proof-preserved-heap-p nil before after old-objects new-objects packages)
       (proof-fixed-heap-p before after old-objects)))

(defun proof-allocator-return-p (kind bytes before after old-objects new-objects packages)
  (and (proof-frame-return-p (append *proof-volatile-registers* '(26 27))
                             t before after)
       (proof-preserved-heap-p nil before after old-objects new-objects packages)
       (proof-reserved-span-p kind (proof-world-reg 0 after) bytes after new-objects)))

(defun proof-allocation-fits-p (kind bytes world)
  (and (member-eq kind '(:header :cons))
       (natp bytes)
       (equal (mod bytes (if (eq kind :cons) 16 8)) 0)
       (<= bytes (- (proof-heap-limit world) (proof-box-top world)))))

(defun proof-fast-allocation-return-p (kind bytes before after old-objects new-objects packages)
  (and (proof-allocation-fits-p kind bytes before)
       (proof-allocator-return-p kind bytes before after old-objects new-objects packages)
       (equal (proof-world-regions before) (proof-world-regions after))
       (equal (proof-world-replies before) (proof-world-replies after))
       (equal (proof-active-floor before) (proof-active-floor after))
       (equal (proof-inactive-floor before) (proof-inactive-floor after))
       (if (eq kind :header)
           (and (equal (proof-world-reg 0 after) (proof-box-top before))
                (equal (proof-heap-limit before) (proof-heap-limit after))
                (equal (proof-cons-floor before) (proof-cons-floor after)))
         (and (equal (proof-box-top before) (proof-box-top after))
              (equal (proof-heap-limit after) (- (proof-heap-limit before) bytes))
              (equal (proof-cons-floor after) (- (proof-cons-floor before) bytes))))))

(defun proof-collector-return-p (kind bytes before after old-objects new-objects packages)
  (and (proof-allocator-return-p kind bytes before after old-objects new-objects packages)
       (equal (proof-active-floor after) (proof-inactive-floor before))
       (equal (proof-inactive-floor after) (proof-active-floor before))))

(defun proof-integer-reserve-return-p (left right bytes before after
                                           old-objects new-objects packages)
  (and (proof-frame-return-p (append *proof-volatile-registers* '(24 26 27))
                             t before after)
       (proof-preserved-heap-p nil before after old-objects new-objects packages)
       (proof-reg-value-p 0 left after new-objects packages)
       (proof-reg-value-p 1 right after new-objects packages)
       (proof-reserved-span-p :header (proof-world-reg 2 after) bytes after new-objects)))

(defun proof-string-result-p (length world objects packages)
  (let* ((word (proof-world-reg 0 world))
         (header (proof-pointer-address word (proof-heap-base world)))
         (view (proof-view word (proof-heap-base world) objects packages
                           (proof-world-machine world))))
    (and (proof-value-view-p view) (stringp (proof-view-value view))
         (equal (length (proof-view-value view)) length)
         (equal (proof-world-reg 1 world) (+ header 8))
         (equal (proof-world-reg 2 world) length)
         (proof-covered-p (+ header 8) length :write (proof-world-regions world)))))

(defun proof-string-constructor-return-p (length before after old-objects new-objects packages)
  (and (proof-frame-return-p (append *proof-volatile-registers* '(26 27))
                             t before after)
       (proof-preserved-heap-p nil before after old-objects new-objects packages)
       (proof-string-result-p length after new-objects packages)))

(defun proof-integer-view-p (value address count world)
  (let ((machine (proof-world-machine world)))
    (and (integerp value) (natp count)
         (equal (proof-load-word address machine) (+ 3 (* 2048 (+ 1 count))))
         (equal (proof-integer-view address machine) (proof-value-view value)))))

(defun proof-exact-quotient-p (dividend divisor quotient)
  (and (integerp dividend) (integerp divisor) (integerp quotient)
       (not (equal divisor 0))
       (equal (* divisor quotient) dividend)))

(defun proof-gcd-p (a b gcd)
  (and (integerp a) (integerp b) (natp gcd)
       (if (equal b 0)
           (equal gcd (abs a))
         (equal (* gcd (denominator (/ a b))) (abs b)))))

(defun proof-resource-label (kind)
  (case kind
    (:word-size "rt:size")
    (:heap-size "rt:heap-size")
    (:number-size "rt:number-size")
    ((:allocation-size :string-size :input-size) "rt:datum-size")
    (:value-stack "rt:stack-size")
    (:machine-stack "rt:deep")
    (:mapping "rt:memory")
    (otherwise nil)))

(defun proof-exit-status-p (status world)
  (equal (proof-world-stop world) (cons :exit status)))

(defun proof-source-observation-p (result world)
  (cond ((and (boymoo-model::core-value-p result)
              (stringp (boymoo-model::core-datum result)))
         (and (proof-exit-status-p 0 world)
              (equal (proof-world-stdout world)
                     (proof-string-bytes (coerce (boymoo-model::core-datum result) 'list)))
              (null (proof-world-stderr world))))
        ((or (equal result :no-value) (boymoo-model::core-value-p result))
         (and (proof-exit-status-p 1 world) (null (proof-world-stdout world))))
        (t nil)))

(defun proof-resource-bound-p (kind demand world)
  (and (natp demand)
       (case kind
         (:word-size (<= (expt 2 64) demand))
         ((:heap-size :number-size :allocation-size) (< *proof-space-size* demand))
         (:string-size (<= *proof-space-size* demand))
         (:input-size (< (- *proof-space-size* 8) demand))
         (:value-stack (< (proof-stack-end world) demand))
         (:machine-stack (< demand (proof-machine-limit world)))
         (otherwise nil))))

(defun proof-mapping-refused-p (world)
  (and (equal (proof-world-reg 8 world) 222)
       (proof-linux-errno-p (car (proof-world-replies world)))
       (let ((next (proof-step world)))
         (and (not (proof-world-stop next))
              (equal (proof-world-pc next) (+ 4 (proof-world-pc world)))
              (equal (boymoo-model::a64-signed 64 (proof-world-reg 0 next))
                     (car (proof-world-replies world)))
              (equal (proof-world-replies next) (cdr (proof-world-replies world)))))))

(defun proof-resource-observation-p (world)
  (and (proof-exit-status-p 3 world) (null (proof-world-stdout world))))
