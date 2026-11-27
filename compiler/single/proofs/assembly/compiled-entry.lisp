(in-package "BOYMOO-PROOFS")

(include-book "linux-link")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-compiler::runtime-code
                           (:executable-counterpart boymoo-compiler::runtime-code)
                           boymoo-compiler::gen-term)))

(local
 (defthm assembly-gen-reverse-onto
   (equal (boymoo-compiler::reverse-onto items code) (revappend items code))))

(local
 (defthm assembly-generated-code-reverse-append
   (equal (revappend (append a b) suffix)
          (revappend b (revappend a suffix)))
   :hints (("Goal" :induct (revappend a suffix)))))

(local
 (defthm assembly-generated-code-double-reverse
   (equal (revappend (revappend a b) suffix)
          (revappend b (append a suffix)))
   :hints (("Goal" :induct (revappend a b)))))

(local
 (defthm assembly-generated-code-append
   (equal (revappend items (append code suffix))
          (append (revappend items code) suffix))
   :hints (("Goal" :induct (revappend items code)))))

(local
 (defthm assembly-gen-load-high-preserves-suffix
   (equal (boymoo-compiler::gen-load-high rd n shift (append code suffix))
          (append (boymoo-compiler::gen-load-high rd n shift code) suffix))
   :hints (("Goal" :induct (boymoo-compiler::gen-load-high rd n shift code)
                   :in-theory (disable ash boymoo-compiler::low-bits)))))

(local
 (defthm assembly-generated-cons-before-append
   (equal (cons item (append code suffix))
          (append (cons item code) suffix))))

(local
 (defthm assembly-gen-load-word-preserves-suffix
   (equal (boymoo-compiler::gen-load-word rd n (append code suffix))
          (append (boymoo-compiler::gen-load-word rd n code) suffix))
   :hints (("Goal" :in-theory (disable binary-append boymoo-compiler::gen-load-high
                                       ash boymoo-compiler::low-bits)))))

(local
 (defthm assembly-gen-address-preserves-suffix
   (equal (boymoo-compiler::gen-address rd rn bytes subtract (append code suffix))
          (append (boymoo-compiler::gen-address rd rn bytes subtract code) suffix))
   :hints (("Goal" :in-theory (disable binary-append boymoo-compiler::gen-load-word)))))

(local
 (defthm assembly-gen-prologue-preserves-suffix
   (equal (boymoo-compiler::gen-prologue arity high serial (append code suffix))
          (append (boymoo-compiler::gen-prologue arity high serial code) suffix))
   :hints (("Goal" :in-theory (disable binary-append boymoo-compiler::gen-address)))))

(local
 (defthm assembly-gen-functions-preserve-suffix
   (equal (boymoo-compiler::gen-functions defs entry context serial (append code suffix))
          (append (boymoo-compiler::gen-functions defs entry context serial code) suffix))
   :hints (("Goal" :induct (boymoo-compiler::gen-functions defs entry context serial code)
                   :in-theory (disable binary-append boymoo-compiler::gen-prologue
                                       boymoo-compiler::bind-formals
                                       boymoo-compiler::declaration-list length)))))

(defthm assembly-compile-items-prefixed-by-system
  (implies (syntaxp (not (equal system ''nil)))
           (equal (boymoo-compiler::compile-items entry defs context data system)
                  (append system (boymoo-compiler::compile-items entry defs context data nil))))
  :hints (("Goal"
           :use ((:instance assembly-generated-code-append
                            (items (boymoo-compiler::runtime-code))
                            (code nil) (suffix (revappend system nil)))
                 (:instance assembly-gen-functions-preserve-suffix
                            (serial 0)
                            (code (revappend (boymoo-compiler::runtime-code) nil))
                            (suffix (revappend system nil))))
           :in-theory (disable boymoo-compiler::gen-functions
                               assembly-gen-functions-preserve-suffix assembly-generated-code-append))))

(local (in-theory (disable assembly-generated-cons-before-append)))

(local
 (defthm assembly-label-lookup-in-appended-lists
   (implies (alistp prefix)
            (equal (assoc-equal key (append prefix suffix))
                   (or (assoc-equal key prefix) (assoc-equal key suffix))))
   :hints (("Goal" :induct (append prefix suffix)))))

(local
 (defthm assembly-linux-entry-label-in-system
   (equal (assoc-equal "os:main" (assembly-labels (append (boymoo-compiler::linux-system-code) tail) 0))
          (cons "os:main" 108))))

(local
 (defthm assembly-linux-system-size
   (equal (assembly-size (boymoo-compiler::linux-system-code)) 120)))

(local (in-theory (disable boymoo-compiler::linux-system-code
                           (:executable-counterpart boymoo-compiler::linux-system-code))))

(defthm assembly-linux-entry-in-compile-items
  (equal (assoc-equal "os:main"
                      (assembly-labels
                       (boymoo-compiler::compile-items entry defs context data
                                                      (boymoo-compiler::linux-system-code))
                       0))
         (cons "os:main" 108))
  :hints (("Goal" :in-theory (disable boymoo-compiler::compile-items assembly-labels
                                      assembly-labels-after-prefix))))

(defun assembly-linux-items-from-text (text)
  (let ((lines (boymoo-compiler::read-program text)))
    (mv-let (defs names attachments sources packages entry target)
      (boymoo-compiler::index-lines lines nil nil nil nil nil nil nil)
      (and entry (eq target :linux)
           (let ((resolved (boymoo-compiler::resolve-attachments sources attachments nil (length sources))))
             (mv-let (data constants)
               (boymoo-compiler::data-build lines packages)
               (let ((context (list names resolved constants)))
                 (boymoo-compiler::compile-items
                  entry (boymoo-compiler::compile-entry-definitions entry defs context)
                  context data (boymoo-compiler::linux-system-code)))))))))

(local (in-theory (disable boymoo-compiler::compile-items
                           boymoo-compiler::compile-entry-definitions
                           boymoo-compiler::index-lines boymoo-compiler::read-program
                           boymoo-compiler::resolve-attachments boymoo-compiler::data-build
                           boymoo-compiler::a64-assemble-image
                           boymoo-compiler::elf-image-executable
                           boymoo-compiler::macho-image-executable)))

(defthm assembly-compile-text-elf-of-linux-items
  (let ((items (assembly-linux-items-from-text text)))
    (implies items
             (mv-let (image offset)
               (boymoo-compiler::a64-assemble-image items "os:main")
               (equal (boymoo-compiler::compile-text text)
                      (boymoo-compiler::elf-image-executable image offset)))))
  :hints (("Goal" :in-theory (disable assembly-compile-items-prefixed-by-system)))
  :rule-classes nil)

(local
 (defthm assembly-linux-items-entry-from-text
   (implies (assembly-linux-items-from-text text)
            (equal (assoc-equal "os:main" (assembly-labels (assembly-linux-items-from-text text) 0))
                   (cons "os:main" 108)))
   :hints (("Goal" :in-theory (disable assembly-compile-items-prefixed-by-system
                                       assembly-labels assembly-labels-after-prefix)))))

(local
 (defthm assembly-nonnegative-size-of-valid-data
   (implies (assembly-data-list-p items)
            (natp (assembly-size items)))
   :hints (("Goal" :use ((:instance assembly-items-character-count (pc 0) (labels nil)))
                   :in-theory (disable assembly-items-character-count assembly-items-characters
                                       assembly-data-list-p assembly-size)))))

(local
 (defthm assembly-valid-data-suffix
   (implies (assembly-data-list-p (append prefix suffix))
            (assembly-data-list-p suffix))
   :hints (("Goal" :induct (append prefix suffix) :in-theory (disable assembly-data-p)))))

(local
 (defthm assembly-linux-suffix-size-lower-bound
   (implies (assembly-data-list-p (append (boymoo-compiler::linux-system-code) suffix))
            (<= 0 (assembly-size suffix)))
   :hints (("Goal"
            :use ((:instance assembly-valid-data-suffix (prefix (boymoo-compiler::linux-system-code)))
                  (:instance assembly-nonnegative-size-of-valid-data (items suffix)))
            :in-theory (disable assembly-valid-data-suffix assembly-nonnegative-size-of-valid-data
                                assembly-size assembly-data-list-p)))
   :rule-classes :linear))

(local
 (defthm assembly-linux-items-size-from-text
   (let ((items (assembly-linux-items-from-text text)))
     (implies (and items (assembly-data-list-p items))
              (<= 120 (assembly-size items))))
   :hints (("Goal" :in-theory (disable assembly-data-list-p assembly-size
                                       boymoo-compiler::linux-system-code)))))

(defthm assembly-compiled-start-maps-linux-items
  (let* ((items (assembly-linux-items-from-text text))
         (world (proof-compiled-start text machine regions page input replies)))
    (implies (and items
                  (assembly-image-layout-p items)
                  (<= (+ *proof-linux-code-base* (assembly-size items)) (expt 2 63))
                  (assembly-linux-loader-input-p (assembly-size items) machine regions page input))
             (and (proof-linked-image-p items "os:main" *proof-linux-code-base* world)
                  (equal (proof-world-pc world) (+ *proof-linux-code-base* 108))
                  (not (proof-world-stop world)))))
  :hints (("Goal"
           :use (assembly-compile-text-elf-of-linux-items
                 assembly-linux-items-size-from-text
                 (:instance assembly-load-linked-linux-image
                            (items (assembly-linux-items-from-text text)) (entry "os:main")))
           :in-theory (disable assembly-linux-items-from-text
                               assembly-linux-loader-input-p assembly-data-list-p
                               boymoo-compiler::compile-text proof-load-linux proof-linked-image-p
                               assembly-labels assembly-size assembly-label-key-list-p
                               assembly-linux-items-size-from-text
                               proof-world-stop proof-world-pc)))
  :rule-classes nil)

(defthm assembly-compiled-start-places-linux-instructions
  (let* ((items (append prefix (cons item suffix)))
         (start (proof-compiled-start text machine regions page input replies)))
    (implies (and (equal (assembly-linux-items-from-text text) items)
                  (consp items)
                  (assembly-image-program-p items)
                  (<= (+ *proof-linux-code-base* (assembly-size items)) (expt 2 63))
                  (assembly-linux-loader-input-p (assembly-size items) machine regions page input)
                  (assembly-code-item-p item))
             (proof-instructions-at-p
              (assembly-specified-instructions item (assembly-size prefix) (assembly-labels items 0))
              (+ *proof-linux-code-base* (assembly-size prefix))
              start)))
  :hints (("Goal"
           :use (assembly-compiled-start-maps-linux-items
                 assembly-linux-items-entry-from-text
                 (:instance assembly-linked-program-item-instructions
                            (entry "os:main") (base *proof-linux-code-base*)
                            (world (proof-compiled-start text machine regions page input replies))))
           :in-theory (disable assembly-linux-items-from-text assembly-linux-items-entry-from-text
                               proof-compiled-start proof-linked-image-p proof-instructions-at-p
                               assembly-specified-instructions assembly-image-layout-p
                               assembly-items-executable-p assembly-linux-loader-input-p
                               assembly-size assembly-code-item-p assembly-labels
                               assembly-labels-after-prefix)))
  :rule-classes nil)
