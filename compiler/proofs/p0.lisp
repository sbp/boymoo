(in-package "BOYMOO-COMPILER")

(include-book "../data")
(include-book "values")

(logic)
(set-verify-guards-eagerness 0)

(defthm p0-write-immediate-integer
  (implies (model-immediate-integer-p value)
           (and (equal (mv-nth 0 (data-write-integer value length block))
                       (cons :integer value))
                (equal (mv-nth 1 (data-write-integer value length block)) block)))
  :hints (("Goal" :in-theory (enable signed-byte-p integer-range-p))))

(defthm p0-cached-list-constant
  (implies (and (equal (char text 0) #\()
                (index-get text (cadr state-data)))
           (equal (data-constant text packages state-data) state-data))
  :hints (("Goal" :in-theory (disable index-get char))))

(defthm p0-resolve-chain-uses-cache
  (implies (and (index-get name resolved)
                (not (equal (index-get name resolved) :pending)))
           (and (equal (mv-nth 0 (resolve-chain name attachments resolved fuel))
                       (index-get name resolved))
                (equal (mv-nth 1 (resolve-chain name attachments resolved fuel)) resolved)))
  :hints (("Goal" :expand ((resolve-chain name attachments resolved fuel))
           :in-theory (disable index-get))))

(defthmd p0-read-lines-keeps-accumulator
  (implies (consp (read-lines text i end frames lines terms fuel))
           (equal (read-lines text i end frames (append lines older) terms fuel)
                  (append (read-lines text i end frames lines terms fuel) older)))
  :hints (("Goal" :induct (read-lines text i end frames lines terms fuel)
           :in-theory (disable read-after datum-end token-end read-push read-list-role
                               char subseq reverse-onto))))
