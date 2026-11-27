(in-package "BOYMOO-PROOFS")

(include-book "indexed-tail")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-segment-p proof-world-pc proof-world-reg proof-world-stop
                    proof-world-machine proof-compiled-entry-p proof-heap-p
                    proof-stack-views proof-value-view proof-view proof-load-word
                    proof-stack-base proof-stack-top generated-read-words generated-sp
                    generated-path-p generated-path-after generated-indexed-tail-path
                    boymoo-model::a64-unsigned expt))

(defun generated-word-views (words base objects packages machine)
  (if (atom words)
      (list :slots)
    (let ((first (proof-view (car words) base objects packages machine))
          (rest (generated-word-views (cdr words) base objects packages machine)))
      (and first rest (list* :slots first (cdr rest))))))

(defcong generated-memory-equiv equal (generated-word-views words base objects packages machine) 5
  :hints (("Goal" :induct (generated-word-views words base objects packages machine))))

(defthm generated-stack-views-are-word-views
  (equal (proof-stack-views count address base objects packages (proof-world-machine world))
         (generated-word-views (generated-read-words count address world)
                               base objects packages (proof-world-machine world)))
  :hints (("Goal" :induct (generated-read-words count address world)
                  :in-theory (enable proof-stack-views generated-load-word generated-read-words))))

(defthm generated-word-views-append
  (let ((first (generated-word-views first-words base objects packages machine))
        (second (generated-word-views second-words base objects packages machine)))
    (equal (generated-word-views (append first-words second-words) base objects packages machine)
           (and first second (cons :slots (append (cdr first) (cdr second))))))
  :hints (("Goal" :induct (generated-word-views first-words base objects packages machine))
          ("Subgoal *1/1" :expand (generated-word-views second-words base objects packages machine))))

(defthm generated-indexed-tail-enters-with-argument-views
  (let* ((arity (len args))
         (bytes (* 8 arity))
         (frame (proof-world-reg 19 before))
         (source (- (proof-stack-top before) bytes))
         (sp (generated-sp before))
         (path (generated-indexed-tail-path arity target before))
         (after (generated-path-after path before))
         (words (generated-read-words arity source before)))
    (implies (and (unsigned-byte-p 64 bytes) (<= frame source)
                  (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                  (< (+ sp 16) (expt 2 64))
                  (proof-disjoint-p frame (+ frame bytes) sp (+ sp 16))
                  (unsigned-byte-p 64 target) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before)) (generated-path-p path (list target) before)
                  (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                  (proof-heap-p after objects packages) (<= (proof-stack-base after) frame)
                  (equal (generated-word-views words (proof-heap-base after) objects packages
                                               (proof-world-machine after))
                         (generated-word-views words (proof-heap-base before) objects packages
                                               (proof-world-machine before))))
             (and (proof-segment-p (len path) (list target) before :cut after)
                  (proof-compiled-entry-p target args after objects packages)
                  (equal (proof-world-reg 30 after) (generated-load-word (+ sp 8) before))
                  (equal (generated-sp after) (+ sp 16)))))
  :hints (("Goal"
           :use (:instance generated-indexed-tail-call-transfer (arity (len args)))
           :in-theory (enable proof-compiled-entry-p proof-stack-top)))
  :rule-classes nil)
