(in-package "BOYMOO-PROOFS")

(include-book "linked")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable boymoo-compiler::gen-term boymoo-compiler::runtime-code
                     (:executable-counterpart boymoo-compiler::runtime-code)
                     boymoo-compiler::a64-image-item-size boymoo-compiler::table-get
                     boymoo-compiler::table-put boymoo-compiler::label-hash)))

(local
 (defthm division-reverse-onto-distributes-over-tail
   (equal (boymoo-compiler::reverse-onto source (append prefix tail))
          (append (boymoo-compiler::reverse-onto source prefix) tail))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto source prefix)))))

(local
 (defthm division-reverse-onto-of-append
   (equal (boymoo-compiler::reverse-onto (append first second) tail)
          (boymoo-compiler::reverse-onto second (boymoo-compiler::reverse-onto first tail)))
   :hints (("Goal" :induct (boymoo-compiler::reverse-onto first tail)))))

(local
 (defthm division-reverse-onto-twice
   (equal (boymoo-compiler::reverse-onto (boymoo-compiler::reverse-onto source prefix) tail)
          (boymoo-compiler::reverse-onto prefix (append source tail)))
   :hints (("Goal"
            :induct (boymoo-compiler::reverse-onto source prefix)
            :in-theory (disable division-reverse-onto-distributes-over-tail)))))

(local
 (defthm division-load-high-preserves-code-tail
   (equal (boymoo-compiler::gen-load-high register value shift (append code tail))
          (append (boymoo-compiler::gen-load-high register value shift code) tail))
   :hints (("Goal" :induct (boymoo-compiler::gen-load-high register value shift code)))))

(local
 (defthm division-load-word-preserves-code-tail
   (equal (boymoo-compiler::gen-load-word register value (append code tail))
          (append (boymoo-compiler::gen-load-word register value code) tail))
   :hints (("Goal"
            :use (:instance division-load-high-preserves-code-tail
                            (value (ash value -16)) (shift 16)
                            (code (cons (list :movz register (boymoo-compiler::low-bits value 16) 0) code)))
            :in-theory (disable boymoo-compiler::gen-load-high boymoo-compiler::low-bits ash
                                division-load-high-preserves-code-tail)))))

(local
 (defthm division-address-generation-preserves-code-tail
   (equal (boymoo-compiler::gen-address target source bytes subtract (append code tail))
          (append (boymoo-compiler::gen-address target source bytes subtract code) tail))
   :hints (("Goal" :in-theory (disable boymoo-compiler::gen-load-word)))))

(local
 (defthm division-emission-preserves-code-tail
   (equal (boymoo-compiler::gen-emit emitted (append code tail))
          (append (boymoo-compiler::gen-emit emitted code) tail))))

(local
 (defthm division-prologue-generation-preserves-code-tail
   (equal (boymoo-compiler::gen-prologue arity high serial (append code tail))
          (append (boymoo-compiler::gen-prologue arity high serial code) tail))
   :hints (("Goal" :in-theory (disable boymoo-compiler::gen-address boymoo-compiler::gen-emit)))))

(local
 (defthm division-prologue-preserves-tail-after-labels
   (and
    (equal (boymoo-compiler::gen-prologue arity high serial (cons label (append code tail)))
           (append (boymoo-compiler::gen-prologue arity high serial (cons label code)) tail))
    (equal (boymoo-compiler::gen-prologue arity high serial (cons label (cons entry-label (append code tail))))
           (append (boymoo-compiler::gen-prologue arity high serial (cons label (cons entry-label code))) tail)))
   :hints (("Goal"
            :use ((:instance division-prologue-generation-preserves-code-tail (code (cons label code)))
                  (:instance division-prologue-generation-preserves-code-tail (code (cons label (cons entry-label code)))))
            :in-theory (disable boymoo-compiler::gen-prologue division-prologue-generation-preserves-code-tail)))))

(local
 (defthm division-functions-preserve-code-tail
   (equal (boymoo-compiler::gen-functions defs entry context serial (append code tail))
          (append (boymoo-compiler::gen-functions defs entry context serial code) tail))
   :hints (("Goal" :induct (boymoo-compiler::gen-functions defs entry context serial code)
                   :in-theory (disable boymoo-compiler::gen-prologue boymoo-compiler::gen-address
                                       boymoo-compiler::reverse-onto division-reverse-onto-twice)
                   :do-not '(generalize fertilize))
           ("Subgoal *1/2" :expand ((boymoo-compiler::gen-functions defs entry context serial (append code tail)))))))

(defthm division-compile-items-has-runtime-prefix
  (equal (boymoo-compiler::compile-items entry defs context data system)
         (append system
                 (append (boymoo-compiler::runtime-code)
                         (boymoo-compiler::reverse-onto
                          (boymoo-compiler::gen-functions defs entry context 0 nil)
                          (list '(:label "data:static") (list :image (car data) (cdr data)))))))
  :hints (("Goal"
           :use (:instance division-functions-preserve-code-tail (code nil) (serial 0)
                           (tail (boymoo-compiler::reverse-onto
                                  (boymoo-compiler::runtime-code) (boymoo-compiler::reverse-onto system nil))))
           :in-theory (disable boymoo-compiler::gen-functions division-functions-preserve-code-tail)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-layout-proceeds-from-runtime-to-program
  (mv-let (next found emitted)
    (boymoo-compiler::a64-layout prefix pc labels reversed)
    (mv-let (end combined-labels combined-items)
      (boymoo-compiler::a64-layout (append prefix suffix) pc labels reversed)
      (mv-let (suffix-end suffix-labels suffix-items)
        (boymoo-compiler::a64-layout suffix next found emitted)
        (implies found
                 (and (equal end suffix-end)
                      (equal combined-labels suffix-labels)
                      (equal combined-items suffix-items))))))
  :hints (("Goal"
           :induct (boymoo-compiler::a64-layout prefix pc labels reversed)
           :do-not '(generalize fertilize))
          ("Subgoal *1/2" :expand ((boymoo-compiler::a64-layout (append prefix suffix) pc labels reversed)))
          ("Subgoal *1/3" :expand ((boymoo-compiler::a64-layout (append prefix suffix) pc labels reversed))))
  :rule-classes nil)

(defconst *division-macos-runtime-items*
  (boymoo-compiler::compile-items "ACL2::IDENTITY"
   '(("ACL2::IDENTITY" ("ACL2::X") "ACL2::X"))
   (list nil nil nil) (cons 0 nil) (boymoo-compiler::system-code)))

(defconst *division-macos-runtime-image*
  (mv-let (image offset)
    (boymoo-compiler::a64-assemble-image *division-macos-runtime-items* "os:main")
    (declare (ignore offset))
    image))

(defconst *division-runtime-operation-word-count*
  (mv-let (size labels reversed)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-division-code) 0 nil nil)
    (declare (ignore labels reversed))
    (floor size 4)))

(defthm division-runtime-example-words-agree-on-targets
  (equal (division-runtime-block "rt:z-quotient" 0 *division-runtime-operation-word-count*)
         (division-decode-image-words
          *division-runtime-operation-word-count*
          (division-label-offset "rt:z-quotient" *division-macos-runtime-items*)
          (cdr *division-macos-runtime-image*)))
  :rule-classes nil)
