(in-package "BOYMOO-PROOFS")

(include-book "copy-path")
(include-book "stack")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-reg proof-world-pc proof-world-stop proof-segment-p
                    proof-instruction-effect generated-sp generated-load-word
                    generated-store-word generated-read-words boymoo-model::a64-unsigned
                    boymoo-compiler::gen-push boymoo-compiler::gen-drop
                    boymoo-compiler::gen-address boymoo-compiler::gen-args
                    boymoo-compiler::gen-term expt))

(defthm generated-push-emission
  (equal (boymoo-compiler::gen-push code)
         (boymoo-compiler::reverse-onto '((:str 0 25 0) (:add 25 25 8)) code))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-push boymoo-compiler::gen-emit))))

(defthm generated-argument-emission-in-evaluation-order
  (implies (consp args)
           (equal (boymoo-compiler::gen-args args scope depth context code high serial)
                  (mv-let (first first-high first-serial)
                    (boymoo-compiler::gen-term (car args) scope depth nil context code high serial)
                    (boymoo-compiler::gen-args (cdr args) scope (1+ depth) context
                                               (boymoo-compiler::gen-push first)
                                               (boymoo-compiler::gen-max first-high (1+ depth))
                                               first-serial))))
  :hints (("Goal" :expand (boymoo-compiler::gen-args args scope depth context code high serial)))
  :rule-classes nil)

(local
 (defthm generated-read-no-words
   (equal (generated-read-words 0 address world) nil)
   :hints (("Goal" :expand (generated-read-words 0 address world)))))

(local
 (defthm generated-read-one-word
   (equal (generated-read-words 1 address world) (list (generated-load-word address world)))
   :hints (("Goal" :expand ((generated-read-words 1 address world)
                            (generated-read-words 0 (+ address 8) world))))))

(local
 (defthm generated-one-more-stack-word
   (implies (and (natp count) (natp lower))
            (equal (generated-read-words (1+ count) lower world)
                   (append (generated-read-words count lower world)
                           (list (generated-load-word (+ lower (* 8 count)) world)))))
   :hints (("Goal" :induct (generated-read-words count lower world)
                   :in-theory (enable generated-read-words)))))

(defconst *generated-push-path*
  '((:single 0 8 25 0 :offset 0) (:arithmetic-imm 0 64 25 25 8)))

(defthm generated-push-appends-operand-word
  (let* ((top (proof-world-reg 25 before))
         (pc (proof-world-pc before))
         (after (generated-path-after *generated-push-path* before)))
    (implies (and (natp count) (natp lower) (equal top (+ lower (* 8 count)))
                  (< (+ top 8) (expt 2 64)) (< (+ pc 8) (expt 2 64))
                  (generated-ordinary-machine-p before) (not (proof-world-stop before))
                  (generated-path-p *generated-push-path* (list (+ pc 8)) before))
             (and (proof-segment-p 2 (list (+ pc 8)) before :cut after)
                  (equal (proof-world-reg 25 after) (+ top 8))
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                  (equal (generated-read-words (1+ count) lower after)
                         (append (generated-read-words count lower before)
                                 (list (proof-world-reg 0 before)))))))
  :hints (("Goal"
           :use (:instance generated-placed-path-to-cut (instructions *generated-push-path*)
                           (cuts (list (+ 8 (proof-world-pc before)))))
           :in-theory (e/d (proof-span-p proof-disjoint-p) (generated-path-p))))
  :rule-classes nil)

(defthm generated-immediate-drop-emission
  (implies (and (natp count) (< (* 8 count) 4096))
           (equal (boymoo-compiler::gen-drop count code)
                  (if (zp count) code
                    (cons (list :sub 25 25 (* 8 count)) code))))
  :hints (("Goal" :in-theory (enable boymoo-compiler::gen-drop boymoo-compiler::gen-address))))

(defthm generated-immediate-drop-restores-top
  (let* ((top (proof-world-reg 25 before))
         (pc (proof-world-pc before))
         (bytes (* 8 count))
         (instruction (list :arithmetic-imm 2 64 25 25 bytes))
         (after (proof-instruction-effect instruction before)))
    (implies (and (posp count) (< bytes 4096) (<= bytes top)
                  (< (+ pc 4) (expt 2 64)) (generated-instruction-p instruction before))
             (and (proof-segment-p 1 (list (+ pc 4)) before :cut after)
                  (equal (proof-world-reg 25 after) (- top bytes))
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                  (equal (generated-read-words slots lower after)
                         (generated-read-words slots lower before)))))
  :hints (("Goal" :use (:instance generated-one-instruction-segment
                                  (instruction (list :arithmetic-imm 2 64 25 25 (* 8 count)))
                                  (cuts (list (+ 4 (proof-world-pc before)))))))
  :rule-classes nil)
