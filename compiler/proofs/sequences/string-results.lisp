(in-package "BOYMOO-PROOFS")

(include-book "coerce-copy")
(include-book "string-copy")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-initialized-string-p (word base header length objects machine)
  (let ((record (assoc-equal header objects)))
    (and (unsigned-byte-p 64 word)
         (equal (proof-word-tag word) 2)
         (equal (proof-pointer-address word base) header)
         record (eq (proof-object-kind record) :header) (natp (proof-object-rank record))
         (natp length) (proof-span-p header (+ 8 length))
         (equal (proof-load-word header machine) (+ 1 (* 256 length))))))

(defthm sequence-initialized-string-views-its-bytes
  (implies (sequence-initialized-string-p word base header length objects machine)
           (equal (proof-view word base objects packages machine)
                  (proof-value-view (proof-load-string length (+ 8 header) machine))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-view proof-header-type proof-header-size
                     sequence-a64-unsigned-as-mod)
                    (proof-view-step proof-word-tag proof-pointer-address
                     proof-load-word proof-load-string oddp evenp
                     sequence-even-tags-mark-even-words sequence-floor-add-multiple sequence-mod-add-multiple))
    :expand ((:free (depth) (proof-view-step :word word 0 depth base objects packages machine)))
    :use (sequence-even-tags-mark-even-words
          (:instance sequence-mod-add-multiple (value 1) (divisor 256) (multiple length))
          (:instance sequence-floor-add-multiple (value 1) (divisor 256) (multiple length)))))
  :rule-classes nil)

(local
 (defthm sequence-list-copy-keeps-earlier-reads
   (implies (and (proof-span-p address width)
                 (proof-span-p destination (len datum))
                 (<= (+ address width) destination))
            (equal (boymoo-model::a64-read-bytes
                    width address (sequence-write-list-bytes datum destination memory))
                   (boymoo-model::a64-read-bytes width address memory)))
   :hints
   (("Goal"
     :in-theory (e/d ((:induction sequence-write-list-bytes)) (sequence-write-one-byte))
     :induct (sequence-write-list-bytes datum destination memory)
     :expand ((sequence-write-list-bytes datum destination memory))))))

(local
 (defthm sequence-subseq-copy-keeps-earlier-reads
   (let ((written (sequence-subseq-string-copy-memory remaining index start length source destination memory)))
     (implies (and (natp remaining) (natp index)
                   (proof-span-p destination (+ index remaining))
                   (proof-span-p address width)
                   (<= (+ address width) (+ destination index)))
              (equal (boymoo-model::a64-read-bytes width address written)
                     (boymoo-model::a64-read-bytes width address memory))))
   :hints
   (("Goal"
     :in-theory (e/d ((:induction boymoo-model::a64-read-bytes))
                     (sequence-subseq-string-copy-memory))
     :induct (boymoo-model::a64-read-bytes width address memory))
    ("Subgoal *1/2"
     :use ((:instance sequence-read-bytes-as-sum (count width))
           (:instance sequence-read-bytes-as-sum
                      (count width)
                      (memory (sequence-subseq-string-copy-memory
                               remaining index start length source destination memory))))))
   :rule-classes nil))

(defthm sequence-coerce-string-copy-returns-represented-value
  (let* ((machine (proof-world-machine before))
         (memory (boymoo-model::a64-memory machine))
         (base (proof-heap-base before))
         (destination (proof-world-reg 1 before))
         (header (- destination 8))
         (length (len datum))
         (path (sequence-coerce-string-copy-path datum))
         (after (sequence-execute path before))
         (cuts (list (+ 40 (proof-world-pc before)))))
    (implies
     (and (consp datum) (not (eq result-type 'list))
          (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers machine))
          (equal (proof-world-reg 2 before) length)
          (unsigned-byte-p 64 (+ destination length))
          (unsigned-byte-p 64 (+ 40 (proof-world-pc before)))
          (sequence-initialized-string-p (proof-world-reg 0 before) base header length objects machine)
          (sequence-coerce-input-cells-p datum (proof-world-reg 4 before)
                                        base destination (+ destination length) memory)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after) objects packages
                             (proof-world-machine after))
                 (boymoo-model::core-primitive 'coerce (list datum result-type) program)))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-load-word sequence-initialized-string-p)
                    (proof-view proof-load-string proof-pointer-address proof-word-tag
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-heap-base
                     sequence-execute sequence-coerce-string-copy-path sequence-coerce-input-cells-p
                     sequence-write-list-bytes proof-segment-p boymoo-model::core-primitive
                     sequence-core-coerce))
    :use (sequence-coerce-string-copy-source-value sequence-coerce-string-copy-effects
          (:instance sequence-initialized-string-views-its-bytes
                     (header (- (proof-world-reg 1 before) 8)) (length (len datum))
                     (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                     (machine (proof-world-machine (sequence-execute (sequence-coerce-string-copy-path datum) before))))
          (:instance sequence-list-copy-keeps-earlier-reads
                     (address (- (proof-world-reg 1 before) 8)) (width 8)
                     (destination (proof-world-reg 1 before))
                     (memory (boymoo-model::a64-memory (proof-world-machine before)))))))
  :rule-classes nil)

(defthm sequence-subseq-string-copy-retains-represented-value
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (destination (proof-world-reg 7 before))
         (header (- destination 8))
         (length (proof-world-reg 19 before))
         (path (sequence-subseq-string-copy-path length 0 (proof-world-reg 20 before)
                                                 (proof-world-reg 2 before)))
         (after (sequence-execute path before))
         (cuts (list (+ 40 (proof-world-pc before)))))
    (implies
     (and (sequence-subseq-copy-input-p before datum start end)
          (sequence-initialized-string-p (proof-world-reg 6 before) base header length objects machine))
     (and (proof-segment-p (len path) cuts before :cut after)
          (equal (proof-view (proof-world-reg 6 after) (proof-heap-base after) objects packages
                             (proof-world-machine after))
                 (boymoo-model::core-prelude 'subseq (list datum start end))))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-load-word sequence-initialized-string-p)
                    (proof-view proof-load-string proof-pointer-address proof-word-tag
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-heap-base
                     sequence-execute sequence-subseq-string-copy-path sequence-subseq-string-copy-memory
                     sequence-subseq-source-byte sequence-instruction-path proof-segment-p
                     sequence-result-size sequence-runtime-count boymoo-model::core-prelude sequence-core-subseq))
    :use (sequence-subseq-string-copy-source-value
          (:instance sequence-subseq-string-copy-segment (remaining (proof-world-reg 19 before)) (byte-index 0))
          (:instance sequence-subseq-string-copy-effects (remaining (proof-world-reg 19 before)))
          (:instance sequence-initialized-string-views-its-bytes
                     (header (- (proof-world-reg 7 before) 8)) (length (proof-world-reg 19 before))
                     (word (proof-world-reg 6 before)) (base (proof-heap-base before))
                     (machine (proof-world-machine (sequence-execute
                              (sequence-subseq-string-copy-path (proof-world-reg 19 before) 0
                                                                (proof-world-reg 20 before) (proof-world-reg 2 before))
                              before))))
          (:instance sequence-subseq-copy-keeps-earlier-reads (width 8) (index 0)
                     (address (- (proof-world-reg 7 before) 8))
                     (remaining (proof-world-reg 19 before)) (start (proof-world-reg 20 before))
                     (length (proof-world-reg 2 before)) (source (proof-world-reg 1 before))
                     (destination (proof-world-reg 7 before))
                     (memory (boymoo-model::a64-memory (proof-world-machine before)))))))
  :rule-classes nil)
