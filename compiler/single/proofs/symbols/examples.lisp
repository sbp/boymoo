(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

; These calls use the emitted runtime in the checked A64 model. The
; entry label is supplied for assembly because the calls enter runtime
; routines directly. Each call can use the available heap and stack
; space without a mapping request.
(defconst *symbols-example-items*
  (append (boymoo-compiler::linux-system-code)
          (boymoo-compiler::runtime-code)
          '((:label "rt:entry") (:ret) (:label "data:static"))))

(defconst *symbols-example-code*
  (boymoo-compiler::a64-bytes *symbols-example-items*))

(defconst *symbols-example-labels*
  (mv-let (end labels reversed)
    (boymoo-compiler::a64-layout *symbols-example-items* 0 nil nil)
    (declare (ignore end reversed))
    labels))

(defconst *symbols-example-code-base* #x10000)
(defconst *symbols-example-heap-base* #x100000)
(defconst *symbols-example-link* #x80000)

(defun symbols-example-label (label)
  (proof-label-address label *symbols-example-code-base* *symbols-example-labels*))

(defconst *symbols-example-packages*
  '(("package" "\"COMMON-LISP\"" "COMMON-LISP::NIL")
    ("package" "\"ACL2\"" "COMMON-LISP::NIL")
    ("package" "\"EXAMPLE\"" ("COMMON-LISP::CAR"))
    ("hidden-package" "\"HIDDEN\"" "COMMON-LISP::NIL")))

(defun symbols-example-world ()
  (mv-let (image constants)
    (boymoo-compiler::data-build
     '(("entry" "HIDDEN::ANCHOR")) *symbols-example-packages*)
    (let* ((registers (list (cons 24 #x220000) (cons 25 #x200000)
                           (cons 26 #x180000) (cons 27 #x110000)
                           (cons 28 *symbols-example-heap-base*)))
           (machine (boymoo-model::a64-state registers #x280000 0 0 nil))
           (machine (proof-load-cleared-string
                     (boymoo-compiler::image-string (cdr image))
                     *symbols-example-heap-base* machine))
           (machine (proof-load-cleared-string
                     *symbols-example-code* *symbols-example-code-base* machine))
           (regions (list (proof-region *symbols-example-code-base*
                                        (+ *symbols-example-code-base*
                                           (length *symbols-example-code*))
                                        :rx)
                          (proof-region *symbols-example-heap-base* #x300000 :rw))))
      (mv (proof-world machine regions 4096 nil nil nil nil nil)
          (boymoo-compiler::index-get "HIDDEN::ANCHOR" constants)))))

(defun symbols-example-call (label first second world)
  (let* ((machine (proof-world-machine world))
         (machine (boymoo-model::a64-write-reg 0 64 nil first machine))
         (machine (boymoo-model::a64-write-reg 1 64 nil second machine))
         (machine (boymoo-model::a64-write-reg 30 64 nil *symbols-example-link* machine))
         (machine (boymoo-model::a64-set-pc (symbols-example-label label) machine)))
    (proof-run 2048
               (list *symbols-example-link*
                     (symbols-example-label "rt:imports-absent")
                     (symbols-example-label "rt:witness-absent")
                     (symbols-example-label "rt:hidden-symbol"))
               (update-nth 0 machine world))))

(defun symbols-example-returned-p (reason world)
  (and (eq reason :cut) (equal (proof-world-pc world) *symbols-example-link*)))

(defun symbols-example-string (string address world)
  (let* ((machine (proof-world-machine world))
         (header (+ 1 (* 256 (length string))))
         (machine (boymoo-model::a64-store 8 address header machine))
         (machine (proof-store-string string (+ address 8) machine)))
    (mv (+ 2 (- address *symbols-example-heap-base*)) (update-nth 0 machine world))))

(defun symbols-example-read-word (address world)
  (proof-load-word address (proof-world-machine world)))

(defun symbols-example-result-string (world)
  (let* ((address (proof-pointer-address (proof-world-reg 0 world)
                                         *symbols-example-heap-base*))
         (header (symbols-example-read-word address world)))
    (and (equal (proof-header-type header) 1)
         (proof-load-string (proof-header-size header) (+ address 8)
                            (proof-world-machine world)))))

(defun symbols-example-string-result-p (label input expected world)
  (mv-let (reason final)
    (symbols-example-call label input 0 world)
    (and (symbols-example-returned-p reason final)
         (equal (symbols-example-result-string final) expected))))

(defun symbols-example-stop-p (label input stop message world)
  (mv-let (reason final)
    (symbols-example-call label input 0 world)
    (and (eq reason :cut)
         (equal (proof-world-pc final) (symbols-example-label stop))
         (equal (proof-world-reg 0 final) input)
         (let ((with-replies (update-nth 6 (list (length message) 1) final)))
           (mv-let (exit-reason exited)
             (proof-run 2048 nil with-replies)
             (and (equal exit-reason (cons :exit 1))
                  (null (proof-world-stdout exited))
                  (equal (proof-world-stderr exited)
                         (append (proof-string-bytes (coerce message 'list)) (list 10)))))))))

(defun symbols-example-package-queries ()
  (mv-let (world hidden-symbol)
    (symbols-example-world)
    (mv-let (hidden-name world)
      (symbols-example-string "HIDDEN" #x1d0000 world)
      (mv-let (absent-name world)
        (symbols-example-string "" #x1d0010 world)
        (let ((symbol-name "prim:COMMON-LISP::SYMBOL-NAME")
              (package-name "prim:ACL2::SYMBOL-PACKAGE-NAME")
              (imports "prim:ACL2::PKG-IMPORTS")
              (witness "prim:ACL2::PKG-WITNESS"))
          (and (symbols-example-string-result-p symbol-name *proof-nil* "NIL" world)
               (symbols-example-string-result-p symbol-name 1 "" world)
               (symbols-example-string-result-p package-name *proof-nil* "COMMON-LISP" world)
               (symbols-example-string-result-p package-name 1 "" world)
               (symbols-example-stop-p
                package-name hidden-symbol "rt:hidden-symbol"
                "no value: symbol-package-name of a symbol of a hidden package: HIDDEN::ANCHOR" world)
               (symbols-example-stop-p
                imports hidden-name "rt:imports-absent"
                "no value: pkg-imports of a string that names no package, or a hidden one: \"HIDDEN\"" world)
               (symbols-example-stop-p
                witness absent-name "rt:witness-absent"
                "no value: pkg-witness of a string that names no package, or a hidden one: \"\"" world)
               (mv-let (reason final)
                 (symbols-example-call imports 1 0 world)
                 (and (symbols-example-returned-p reason final)
                      (equal (proof-world-reg 0 final) *proof-nil*)))
               (mv-let (reason final)
                 (symbols-example-call witness 1 0 world)
                 (and (symbols-example-returned-p reason final)
                      (symbols-example-string-result-p
                       package-name (proof-world-reg 0 final) "ACL2" final)))))))))

(assert-event (symbols-example-package-queries))

(defconst *symbols-example-intern* "prim:ACL2::INTERN-IN-PACKAGE-OF-SYMBOL")

(defun symbols-example-name-address (index)
  (+ #x1e0000 (* 16 index)))

(defun symbols-example-name-word (index)
  (+ 2 (- (symbols-example-name-address index) *symbols-example-heap-base*)))

(defun symbols-example-insert-names (left index designator world words)
  (declare (xargs :measure (nfix left)
                  :hints (("Goal" :in-theory
                           (disable symbols-example-call symbols-example-string
                                    symbols-example-read-word proof-world-reg)))))
  (if (zp left)
      (mv world words)
    (mv-let (name world)
      (symbols-example-string (coerce (list (code-char (+ 65 index))) 'string)
                              (symbols-example-name-address index) world)
      (mv-let (reason final)
        (symbols-example-call *symbols-example-intern* name designator world)
        (let* ((word (proof-world-reg 0 final))
               (address (proof-pointer-address word *symbols-example-heap-base*)))
          (if (and (symbols-example-returned-p reason final)
                   (equal (symbols-example-read-word address final) 4098)
                   (equal (symbols-example-read-word (+ address 8) final) name))
              (symbols-example-insert-names (1- left) (1+ index) designator final
                                            (cons word words))
            (mv nil nil)))))))

(defun symbols-example-lookup-names (last designator world words)
  (declare (xargs :measure (acl2-count words)
                  :hints (("Goal" :in-theory
                           (disable symbols-example-call proof-world-reg)))))
  (if (atom words)
      (null words)
    (mv-let (reason final)
      (symbols-example-call *symbols-example-intern* (symbols-example-name-word last)
                            designator world)
      (and (symbols-example-returned-p reason final)
           (equal (proof-world-reg 0 final) (car words))
           (symbols-example-lookup-names (1- last) designator final (cdr words))))))

(defun symbols-example-interner-returns-nil-p (name designator world)
  (mv-let (reason final)
    (symbols-example-call *symbols-example-intern* name designator world)
    (and (symbols-example-returned-p reason final)
         (equal (proof-world-reg 0 final) *proof-nil*))))

(defun symbols-example-import-resolves-p (name designator world)
  (mv-let (reason final)
    (symbols-example-call *symbols-example-intern* name designator world)
    (let ((import (proof-world-reg 0 final)))
      (and (symbols-example-returned-p reason final)
           (symbols-example-string-result-p "prim:COMMON-LISP::SYMBOL-NAME"
                                            import "CAR" final)
           (symbols-example-string-result-p "prim:ACL2::SYMBOL-PACKAGE-NAME"
                                            import "COMMON-LISP" final)
           (equal (proof-dynamic-root *symbols-example-heap-base* (proof-world-machine final))
                  *proof-nil*)))))

(defun symbols-example-doubling-p (designator world)
  (mv-let (grown words)
    (symbols-example-insert-names 17 0 designator world nil)
    (and grown
         (let* ((root (proof-dynamic-root *symbols-example-heap-base*
                                          (proof-world-machine grown)))
                (address (proof-pointer-address root *symbols-example-heap-base*)))
           (and (equal (symbols-example-read-word address grown) (+ (* 2048 33) 6))
                (equal (symbols-example-read-word (+ address 8) grown) 35)
                (symbols-example-lookup-names 16 designator grown words))))))

(defun symbols-example-interning ()
  (mv-let (world hidden-symbol)
    (symbols-example-world)
    (declare (ignore hidden-symbol))
    (mv-let (package-name world)
      (symbols-example-string "EXAMPLE" #x1d0000 world)
      (mv-let (reason with-witness)
        (symbols-example-call "prim:ACL2::PKG-WITNESS" package-name 0 world)
        (and (symbols-example-returned-p reason with-witness)
             (let ((designator (proof-world-reg 0 with-witness)))
               (mv-let (import-name ready)
                 (symbols-example-string "CAR" #x1d0010 with-witness)
                 (and (symbols-example-interner-returns-nil-p 1 designator ready)
                      (symbols-example-interner-returns-nil-p import-name 1 ready)
                      (symbols-example-import-resolves-p import-name designator ready)
                      (symbols-example-doubling-p designator ready)))))))))

(assert-event (symbols-example-interning))
