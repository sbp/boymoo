(in-package "BOYMOO-PROOFS")

(include-book "text-inputs")
(include-book "compiled-entry")
(include-book "macho-link")

(logic)
(set-verify-guards-eagerness 0)

(defun assembly-system-for-target (target)
  (if (eq target :linux)
      (boymoo-compiler::linux-system-code)
    (boymoo-compiler::system-code)))

(defun assembly-compiler-input-items (inputs)
  (boymoo-compiler::compile-items (car inputs) (cadr inputs) (caddr inputs) (cadddr inputs)
                                  (assembly-system-for-target (nth 4 inputs))))

(defun assembly-bounded-compiler-text-p (text)
  (let* ((inputs (assembly-read-compiler-inputs text))
         (entry (car inputs))
         (defs (cadr inputs))
         (context (caddr inputs))
         (data (cadddr inputs))
         (system (assembly-system-for-target (nth 4 inputs))))
    (and inputs (assembly-entry-arity-p entry context)
         (assembly-constant-index-p (caddr context) 12)
         (proof-image-p data)
         (< (assembly-size (assembly-compile-prefix entry defs context system)) (expt 2 20)))))

(local (in-theory (disable boymoo-compiler::compile-items
                           boymoo-compiler::compile-entry-definitions
                           boymoo-compiler::index-lines boymoo-compiler::read-program
                           boymoo-compiler::resolve-attachments boymoo-compiler::data-build
                           boymoo-compiler::a64-assemble-image
                           boymoo-compiler::elf-image-executable
                           boymoo-compiler::macho-image-executable
                           boymoo-compiler::runtime-code
                           (:executable-counterpart boymoo-compiler::runtime-code)
                           assembly-compile-prefix assembly-constant-index-p
                           assembly-entry-arity-p assembly-size)))

(local
 (defthm assembly-target-system-has-layout
   (assembly-system-layout-p (assembly-system-for-target target))
   :hints (("Goal"
            :use (assembly-system-and-runtime-layout)
            :in-theory (disable assembly-system-layout-p boymoo-compiler::linux-system-code
                                boymoo-compiler::system-code
                                (:executable-counterpart boymoo-compiler::linux-system-code)
                                (:executable-counterpart boymoo-compiler::system-code))))))

(defthm assembly-bounded-compiler-text-passes-image-checks
  (implies (assembly-bounded-compiler-text-p text)
           (assembly-image-program-p (assembly-compiler-input-items (assembly-read-compiler-inputs text))))
  :hints (("Goal"
           :use (assembly-read-compiler-inputs-definition-checks
                 (:instance assembly-compile-items-pass-image-checks
                            (entry (car (assembly-read-compiler-inputs text)))
                            (defs (cadr (assembly-read-compiler-inputs text)))
                            (context (caddr (assembly-read-compiler-inputs text)))
                            (data (cadddr (assembly-read-compiler-inputs text)))
                            (system (assembly-system-for-target (nth 4 (assembly-read-compiler-inputs text))))))
           :in-theory (disable assembly-read-compiler-inputs assembly-system-layout-p
                               assembly-system-for-target assembly-image-program-p
                               assembly-arity-index-covered-p proof-image-p)))
  :rule-classes nil)

(defthm assembly-compile-text-serializes-input-items
  (let* ((inputs (assembly-read-compiler-inputs text))
         (items (assembly-compiler-input-items inputs)))
    (implies inputs
             (mv-let (image offset)
               (boymoo-compiler::a64-assemble-image items "os:main")
               (equal (boymoo-compiler::compile-text text)
                      (if (eq (nth 4 inputs) :linux)
                          (boymoo-compiler::elf-image-executable image offset)
                        (boymoo-compiler::macho-image-executable image offset))))))
  :rule-classes nil)

(local
 (defthm assembly-revappend-with-nonempty-tail
   (implies (consp tail)
            (consp (revappend items tail)))
   :hints (("Goal" :induct (revappend items tail)))))

(local
 (defthm assembly-compile-items-is-nonempty
   (consp (boymoo-compiler::compile-items entry defs context data system))
   :hints (("Goal"
            :in-theory (e/d (boymoo-compiler::compile-items)
                            (assembly-compile-items-prefixed-by-system
                             boymoo-compiler::gen-functions boymoo-compiler::gen-emit))))
   :rule-classes :type-prescription))

(local
 (defthm assembly-linux-input-items-agree
   (let ((inputs (assembly-read-compiler-inputs text)))
     (implies (and inputs (eq (nth 4 inputs) :linux))
              (and (assembly-linux-items-from-text text)
                   (equal (assembly-linux-items-from-text text)
                          (assembly-compiler-input-items inputs)))))
   :hints (("Goal"
            :in-theory (disable assembly-compile-items-prefixed-by-system)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm assembly-bounded-compiler-text-has-inputs
   (implies (assembly-bounded-compiler-text-p text)
            (consp (assembly-read-compiler-inputs text)))
   :hints (("Goal" :in-theory (disable assembly-compile-prefix length
                                       assembly-system-for-target)))))

(local (in-theory (disable assembly-read-compiler-inputs assembly-compiler-input-items
                           assembly-linux-items-from-text
                           boymoo-compiler::compile-text proof-compiled-start)))

(defthm assembly-bounded-linux-compiled-start
  (let* ((inputs (assembly-read-compiler-inputs text))
         (items (assembly-compiler-input-items inputs))
         (world (proof-compiled-start text machine regions page input replies)))
    (implies (and (assembly-bounded-compiler-text-p text) (eq (nth 4 inputs) :linux)
                  (<= (+ *proof-linux-code-base* (assembly-size items)) (expt 2 63))
                  (assembly-linux-loader-input-p (assembly-size items) machine regions page input))
             (and (assembly-image-program-p items)
                  (proof-linked-image-p items "os:main" *proof-linux-code-base* world)
                  (equal (proof-world-pc world) (+ *proof-linux-code-base* 108))
                  (not (proof-world-stop world)))))
  :hints (("Goal"
           :use (assembly-bounded-compiler-text-passes-image-checks
                 assembly-compiled-start-maps-linux-items assembly-linux-input-items-agree)
           :in-theory (disable assembly-bounded-compiler-text-p assembly-linux-loader-input-p
                               proof-linked-image-p proof-world-pc proof-world-stop
                               assembly-image-layout-p assembly-items-executable-p
                               assembly-system-for-target proof-image-p)))
  :rule-classes nil)

(local
 (defthm assembly-macho-system-entry
   (equal (assoc-equal "os:main" (assembly-labels (append (boymoo-compiler::system-code) rest) 0))
          (cons "os:main" 144))
   :hints (("Goal" :in-theory (disable assembly-labels-after-prefix)))))

(local
 (defthm assembly-macho-system-size
   (equal (assembly-size (boymoo-compiler::system-code)) 156)
   :hints (("Goal" :in-theory (enable assembly-size)))))

(local (in-theory (disable boymoo-compiler::system-code
                           (:executable-counterpart boymoo-compiler::system-code))))

(local
 (defthm assembly-macho-compiler-inputs-entry
   (implies (not (eq (nth 4 inputs) :linux))
            (equal (assoc-equal "os:main" (assembly-labels (assembly-compiler-input-items inputs) 0))
                   (cons "os:main" 144)))
   :hints (("Goal"
            :in-theory (e/d (assembly-compiler-input-items)
                            (assembly-labels assembly-labels-after-prefix))
            :do-not-induct t))))

(local
 (defthm assembly-valid-data-after-prefix
   (implies (assembly-data-list-p (append prefix items))
            (assembly-data-list-p items))
   :hints (("Goal" :induct (append prefix items) :in-theory (disable assembly-data-p)))))

(local
 (defthm assembly-compiler-inputs-valid-size
   (implies (assembly-data-list-p items) (natp (assembly-size items)))
   :hints (("Goal"
            :use ((:instance assembly-items-character-count (pc 0) (labels nil)))
            :in-theory (disable assembly-items-character-count assembly-items-characters
                                assembly-data-list-p)))
   :rule-classes nil))

(local
 (defthm assembly-valid-suffix-size
   (implies (assembly-data-list-p (append prefix items))
            (<= 0 (assembly-size items)))
   :hints (("Goal" :use (assembly-compiler-inputs-valid-size)))
   :rule-classes :linear))

(local
 (defthm assembly-macho-compiler-inputs-size
   (let ((items (assembly-compiler-input-items inputs)))
     (implies (and (not (eq (nth 4 inputs) :linux)) (assembly-data-list-p items))
              (<= 156 (assembly-size items))))
   :hints (("Goal" :in-theory (enable assembly-compiler-input-items)))
   :rule-classes :linear))

(defun assembly-compiled-macho-start (text base machine regions input)
  (assembly-load-macho-text (boymoo-compiler::compile-text text) base machine regions input))

(defthm assembly-bounded-macho-compiled-start
  (let* ((inputs (assembly-read-compiler-inputs text))
         (items (assembly-compiler-input-items inputs))
         (size (boymoo-compiler::macho-segment-size
                (+ *assembly-macho-code-offset* (assembly-size items))))
         (code-base (+ base *assembly-macho-code-offset*))
         (world (assembly-compiled-macho-start text base machine regions input)))
    (implies (and (assembly-bounded-compiler-text-p text) (not (eq (nth 4 inputs) :linux))
                  (< size (expt 2 32))
                  (assembly-macho-loader-input-p size base machine regions input))
             (and (assembly-image-program-p items)
                  (proof-linked-image-p items "os:main" code-base world)
                  (equal (proof-world-pc world) (+ code-base 144))
                  (not (proof-world-stop world)))))
  :hints (("Goal"
           :use (assembly-bounded-compiler-text-passes-image-checks
                 assembly-compile-text-serializes-input-items
                 (:instance assembly-macho-compiler-inputs-entry
                            (inputs (assembly-read-compiler-inputs text)))
                 (:instance assembly-load-linked-macho-image
                            (items (assembly-compiler-input-items (assembly-read-compiler-inputs text)))
                            (entry "os:main")))
           :in-theory (disable assembly-bounded-compiler-text-p
                               assembly-load-macho-text assembly-macho-loader-input-p
                               proof-linked-image-p proof-world-pc proof-world-stop
                               assembly-labels assembly-assoc-label-of-layout
                               assembly-macho-compiler-inputs-entry
                               assembly-data-list-p assembly-items-executable-p
                               boymoo-compiler::macho-segment-size
                               assembly-system-for-target proof-image-p)))
  :rule-classes nil)
