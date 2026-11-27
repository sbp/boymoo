(in-package "BOYMOO-COMPILER")

(include-book "p5")

(logic)
(set-verify-guards-eagerness 0)

(defun p5-licm-load-p (inst)
  (member-eq (qir-inst-op inst) '(:ld :ldb)))

(defun p5-licm-prefix-op-p (inst)
  (or (qir-word-op-p (qir-inst-op inst))
      (member-eq (qir-inst-op inst) '(:sel :copy))))

(defthmd p5-licm-prefix-op-is-total-and-pure
  (implies (p5-licm-prefix-op-p inst)
           (let ((exec (qir-compute inst args slots nslots :m heap program)))
             (and (boymoo-model::core-value-p (mv-nth 0 exec))
                  (equal (mv-nth 1 exec) slots)
                  (equal (mv-nth 2 exec) heap))))
  :hints (("Goal" :in-theory (enable qir-compute))))

(local
 (defthm p5-licm-movable-load-after-barrier-is-guarded
   (implies (and (p5-licm-load-p inst)
                 (licm-movable-p inst defs collects definitions nil))
            (licm-header-load-p inst definitions))
   :hints (("Goal" :in-theory (disable licm-header-load-p licm-outside-p
                                      opt-pure-op-p)))))

(defthmd p5-licm-moved-load-after-barrier-is-guarded
  (implies (and (not clean)
                (p5-licm-load-p load)
                (not (member-equal load moved))
                (member-equal load (mv-nth 1 (licm-insts insts defs collects definitions clean kept moved))))
           (licm-header-load-p load definitions))
  :hints (("Goal" :induct (licm-insts insts defs collects definitions clean kept moved)
           :in-theory (e/d (licm-insts) (licm-movable-p licm-header-load-p)))))

(defthmd p5-licm-load-after-kept-barrier-is-guarded
  (implies (and (consp insts)
                (not (licm-movable-p (car insts) defs collects definitions clean))
                (not (p5-licm-prefix-op-p (car insts)))
                (p5-licm-load-p load)
                (not (member-equal load moved))
                (member-equal load (mv-nth 1 (licm-insts insts defs collects definitions clean kept moved))))
           (licm-header-load-p load definitions))
  :hints (("Goal" :expand ((licm-insts insts defs collects definitions clean kept moved))
           :use (:instance p5-licm-moved-load-after-barrier-is-guarded
                           (insts (cdr insts)) (clean nil) (kept (cons (car insts) kept)))
           :in-theory (disable licm-insts licm-movable-p licm-header-load-p qir-word-op-p)
           :do-not-induct t)))

(local
 (defthm p5-licm-block-scan-excludes-unguarded-load
   (implies (and (p5-licm-load-p load)
                 (not (licm-header-load-p load definitions))
                 (not (member-equal load moved)))
            (not (member-equal load (mv-nth 1 (licm-insts insts defs collects definitions nil kept moved)))))
   :hints (("Goal" :use (:instance p5-licm-moved-load-after-barrier-is-guarded (clean nil))
            :in-theory (disable licm-insts licm-header-load-p p5-licm-load-p member-equal)))))

(defthmd p5-licm-new-load-outside-header-is-guarded
  (implies (and (not clean)
                (p5-licm-load-p load)
                (not (licm-header-load-p load definitions))
                (not (member-equal load moved)))
           (not (member-equal load (mv-nth 1 (licm-blocks labels bmap defs collects definitions clean moved)))))
  :hints (("Goal" :induct (licm-blocks labels bmap defs collects definitions clean moved)
           :in-theory (disable licm-insts licm-movable-p licm-header-load-p p5-licm-load-p
                               qir-get qir-put reverse member-equal))))

(defthmd p5-licm-unguarded-new-load-comes-from-header
  (let* ((header (qir-get (car labels) bmap))
         (header-scan (licm-insts (qir-block-insts header) defs collects definitions t nil moved))
         (loop-scan (licm-blocks labels bmap defs collects definitions t moved)))
    (implies (and (consp labels) (p5-licm-load-p load)
                  (not (licm-header-load-p load definitions))
                  (not (member-equal load moved))
                  (member-equal load (mv-nth 1 loop-scan)))
             (member-equal load (mv-nth 1 header-scan))))
  :hints (("Goal" :expand ((licm-blocks labels bmap defs collects definitions t moved))
           :in-theory (e/d (p5-licm-new-load-outside-header-is-guarded)
                            (licm-blocks licm-insts licm-header-load-p p5-licm-load-p
                             qir-get qir-put reverse member-equal))
           :do-not-induct t)))

(defund p5-licm-prefix-total-p (insts)
  (if (atom insts)
      t
    (and (p5-licm-prefix-op-p (car insts))
         (p5-licm-prefix-total-p (cdr insts)))))

(local
 (defthm p5-licm-prefix-remains-nontotal
   (implies (not (p5-licm-prefix-total-p kept))
            (not (p5-licm-prefix-total-p
                  (car (licm-insts insts defs collects definitions clean kept moved)))))
   :hints (("Goal" :induct (licm-insts insts defs collects definitions clean kept moved)
            :in-theory (e/d (p5-licm-prefix-total-p)
                             (licm-movable-p p5-licm-prefix-op-p qir-put qir-word-op-p))))))

(local
 (defthm p5-licm-movable-with-nonnil-clean
   (implies (and clean (syntaxp (not (quotep clean))))
            (equal (licm-movable-p inst defs collects definitions clean)
                   (licm-movable-p inst defs collects definitions t)))
   :hints (("Goal" :in-theory (disable licm-header-load-p licm-outside-p
                                      opt-pure-op-p opt-stable-inst-p)))))

(local
 (defthm p5-licm-scan-with-nonnil-clean
   (implies (and clean (syntaxp (not (quotep clean))))
            (equal (licm-insts insts defs collects definitions clean kept moved)
                   (licm-insts insts defs collects definitions t kept moved)))
   :hints (("Goal" :induct (licm-insts insts defs collects definitions clean kept moved)
            :in-theory (disable licm-movable-p qir-put qir-word-op-p)))))

(defthmd p5-licm-split-at-any-prefix
  (let* ((scan (licm-insts prefix defs collects definitions clean kept moved))
         (kept-prefix (mv-nth 0 scan))
         (moved-prefix (mv-nth 1 scan))
         (remaining-defs (mv-nth 2 scan)))
    (implies (or (not clean) (p5-licm-prefix-total-p kept))
             (equal (licm-insts (append prefix suffix) defs collects definitions clean kept moved)
                    (licm-insts suffix remaining-defs collects definitions
                                (and clean (p5-licm-prefix-total-p kept-prefix))
                                kept-prefix moved-prefix))))
  :hints (("Goal" :induct (licm-insts prefix defs collects definitions clean kept moved)
           :in-theory (e/d (p5-licm-prefix-total-p)
                            (licm-movable-p qir-put qir-word-op-p)))))

(defthmd p5-licm-load-after-any-kept-barrier-is-guarded
  (let* ((prefix-scan (licm-insts prefix defs collects definitions t nil nil))
         (moved-prefix (mv-nth 1 prefix-scan))
         (moved-block (mv-nth 1 (licm-insts (append prefix suffix) defs collects definitions t nil nil))))
    (implies (and (p5-licm-load-p load)
                  (not (p5-licm-prefix-total-p (mv-nth 0 prefix-scan)))
                  (not (member-equal load moved-prefix))
                  (member-equal load moved-block))
             (licm-header-load-p load definitions)))
  :hints (("Goal"
           :use ((:instance p5-licm-split-at-any-prefix (clean t) (kept nil) (moved nil))
                 (:instance p5-licm-moved-load-after-barrier-is-guarded
                            (insts suffix) (clean nil)
                            (defs (mv-nth 2 (licm-insts prefix defs collects definitions t nil nil)))
                            (kept (mv-nth 0 (licm-insts prefix defs collects definitions t nil nil)))
                            (moved (mv-nth 1 (licm-insts prefix defs collects definitions t nil nil)))))
           :in-theory (disable licm-insts licm-header-load-p p5-licm-load-p member-equal)
           :do-not-induct t)))

(defthmd p5-licm-header-load-cannot-fault
  (let* ((tag (model-word-op :and word 7))
         (test (model-word-op :ceq tag 2))
         (base (boymoo-model::core-datum
                (mv-nth 0 (qir-compute '(nil :sel) (list test word 34)
                                           slots nslots :m heap program))))
         (width (if (eq op :ld) 8 1)))
    (implies (and (member-eq op '(:ld :ldb))
                  (boymoo-model::core-value-p (model-heap-read width 32 heap))
                  (implies (equal tag 2)
                           (boymoo-model::core-value-p
                            (model-heap-read width (model-word (+ word #xFFFFFFFFFFFFFFFE)) heap))))
             (boymoo-model::core-value-p
              (mv-nth 0 (qir-compute (list nil op) (list base #xFFFFFFFFFFFFFFFE)
                                        slots nslots :m heap program)))))
  :hints (("Goal" :in-theory (enable qir-compute model-word-equality-computes-flag)
           :do-not-induct t)))

(local
 (defthm p5-licm-recognized-constant-is-the-model-word
   (implies (integerp (opt-constant-word operand))
            (equal (qir-operand operand env :m heap)
                   (boymoo-model::core-value (opt-constant-word operand))))
   :hints (("Goal" :in-theory (enable qir-operand)))))

(defthmd p5-licm-recognized-header-load-has-guard-shape
  (let* ((selection (licm-def (caddr inst) definitions))
         (source (cadddr selection))
         (test (licm-def (caddr selection) definitions))
         (masked (if (qir-const-p (caddr test)) (cadddr test) (caddr test))))
    (implies (licm-header-load-p inst definitions)
             (and (eq (qir-inst-op selection) :sel)
                  (qir-dtemp-p source)
                  (equal (qir-operand (car (cddddr selection)) env :m heap)
                         (boymoo-model::core-value 34))
                  (licm-op-with-p test :ceq masked 2)
                  (licm-op-with-p (licm-def masked definitions) :and source 7)
                  (equal (qir-operand (cadddr inst) env :m heap)
                         (boymoo-model::core-value #xFFFFFFFFFFFFFFFE)))))
  :hints (("Goal" :in-theory (e/d (qir-operand)
                                  (licm-def licm-op-with-p opt-constant-word))
           :use (:instance p5-licm-recognized-constant-is-the-model-word (operand (cadddr inst)))
           :do-not-induct t)))

(local
 (defthm p5-licm-list-of-length-two
   (implies (and (true-listp xs) (equal (len xs) 2))
            (equal xs (list (car xs) (cadr xs))))
   :rule-classes nil
   :hints (("Goal" :cases ((consp xs) (consp (cdr xs)) (consp (cddr xs)))
            :expand ((len xs) (len (cdr xs)) (len (cddr xs)))
            :in-theory (disable (:elim acl2::car-cdr-elim))
            :do-not-induct t))))

(local
 (defthm p5-licm-load-uses-two-operands
   (implies (and (p5-licm-load-p inst) (qir-inst-ok inst :m))
            (equal (qir-inst-uses inst) (list (caddr inst) (cadddr inst))))
   :hints (("Goal" :use (:instance p5-licm-list-of-length-two (xs (cddr inst)))
            :in-theory (disable qir-dest-ok qir-operand-p qir-data-operand-p)))))

(defthmd p5-licm-guarded-instruction-reads-modeled-header
  (let* ((selection (licm-def (caddr inst) definitions))
         (source (qir-operand (cadddr selection) env :m heap))
         (word (boymoo-model::core-datum source))
         (tagged (equal (model-word-op :and word 7) 2))
         (base (if tagged word 34))
         (width (if (eq (qir-inst-op inst) :ld) 8 1))
         (header (model-heap-read width (model-word (+ base #xFFFFFFFFFFFFFFFE)) heap))
         (args (qir-operands (qir-inst-uses inst) env :m heap)))
    (implies (and (p5-licm-load-p inst) (qir-inst-ok inst :m)
                  (licm-header-load-p inst definitions)
                  (boymoo-model::core-value-p source)
                  (equal (qir-operand (caddr inst) env :m heap) (boymoo-model::core-value base))
                  (boymoo-model::core-value-p header))
             (and (boymoo-model::core-value-p args)
                  (equal (mv-nth 0 (qir-compute inst (boymoo-model::core-datum args)
                                                   slots nslots :m heap program))
                         header))))
  :hints (("Goal" :use p5-licm-recognized-header-load-has-guard-shape
           :in-theory (e/d (qir-operands qir-compute)
                            (licm-def licm-header-load-p licm-op-with-p qir-inst-ok
                             qir-inst-uses qir-dtemp-p))
           :do-not-induct t)))

(assert-event
 (let* ((definitions (licm-insts-defs '(((:w . 1) :and (:d . 0) (:k . 7))
                                       ((:w . 2) :ceq (:w . 1) (:k . 2))
                                       ((:d . 3) :sel (:w . 2) (:d . 0) (:k . 34))) nil))
        (early '((:w . 4) :ld (:d . 0) (:k . 0)))
        (call '((:d . 5) :call "ACL2::WORK" (:d . 0)))
        (late '((:w . 6) :ld (:d . 0) (:k . 8)))
        (guarded '((:w . 7) :ld (:d . 3) (:k . -2))))
   (mv-let (kept moved defs)
     (licm-insts (list early call late guarded) nil t definitions t nil nil)
     (declare (ignore defs))
     (and (equal kept (list late call))
          (equal moved (list guarded early))))))
