(in-package "ACL2")

(include-book "core")

; The walker consumes one unit for a list entry still to visit, an edge
; still to inspect or a frame still to pop.  Pushing a statement moves
; the cost of its frame from the reserve into the stack.

(defun structure-frame-cost (stack)
  (if (endp stack)
      0
    (+ 1 (len (cdar stack)) (structure-frame-cost (cdr stack)))))

(defun structure-markedp (line done)
  (member-eq (cdr (hons-get line done)) '(t :pending)))

(defun structure-walk-reserve (lines done)
  (if (endp lines)
      0
    (+ (if (structure-markedp (car lines) done)
           0
         (+ 1 (len (bx-used (car lines)))))
       (structure-walk-reserve (cdr lines) done))))

(defthm structure-walk-reserve-is-natural
  (natp (structure-walk-reserve lines done))
  :rule-classes :type-prescription)

(defthm structure-frame-cost-is-natural
  (natp (structure-frame-cost stack))
  :rule-classes :type-prescription)

(defthm structure-mark-after-put
  (equal (structure-markedp line (hons-acons placed mark done))
         (if (equal line placed)
             (member-eq mark '(t :pending))
           (structure-markedp line done))))

(defthm structure-walk-debit
  (implies (member-eq mark '(t :pending))
           (<= (+ (if (and (member-equal placed lines)
                           (not (structure-markedp placed done)))
                      (+ 1 (len (bx-used placed)))
                    0)
                  (structure-walk-reserve lines (hons-acons placed mark done)))
               (structure-walk-reserve lines done)))
  :hints (("Goal" :induct (structure-walk-reserve lines done)
                  :in-theory (disable structure-markedp bx-used hons-acons)))
  :rule-classes :linear)

(defthm structure-index-value-in-universe
  (implies (and (hons-get function index)
                (subsetp-equal (strip-cdrs index) universe))
           (member-equal (cdr (hons-get function index)) universe))
  :hints (("Goal" :induct (hons-assoc-equal function index))))

(defthm structure-index-fns-in-universe
  (implies (and (member-equal line universe)
                (subsetp-equal (strip-cdrs index) universe))
           (subsetp-equal (strip-cdrs (bx-index-fns fns line index)) universe)))

(defthm structure-index-in-universe
  (implies (and (subsetp-equal lines universe)
                (subsetp-equal (strip-cdrs index) universe))
           (subsetp-equal (strip-cdrs (bx-index lines index)) universe))
  :hints (("Goal" :induct (bx-index lines index)
                  :in-theory (disable bx-index-fns bx-introduced))))

(defthm structure-use-cost-below-bx-steps
  (< (+ (len lines) (structure-walk-reserve lines nil))
     (bx-steps lines))
  :hints (("Goal" :in-theory (disable bx-used)))
  :rule-classes :linear)

(defconst *structure-walk-incomplete*
  '(:note "order of the library not completed" nil))

(local (in-theory (disable structure-walk-reserve structure-mark-after-put
                    bx-index-fns bx-index bx-used bx-introduced)))

(defthm structure-len-when-consp
  (implies (consp x)
           (equal (len x) (+ 1 (len (cdr x))))))

(defthm structure-walk-fuel-suffices
  (implies (and (subsetp-equal todo universe)
                (subsetp-equal (strip-cdrs index) universe)
                (integerp fuel)
                (< (+ (len todo) (structure-frame-cost stack)
                      (structure-walk-reserve universe done))
                   fuel))
           (iff (member-equal *structure-walk-incomplete*
                              (mv-nth 1 (bx-walk stack todo index done acc notes fuel)))
                (member-equal *structure-walk-incomplete* notes)))
  :hints (("Goal" :induct (bx-walk stack todo index done acc notes fuel)
                  :in-theory (disable hons-get hons-acons len))))

(defthm structure-subsetp-of-cons-right
  (implies (subsetp-equal x y)
           (subsetp-equal x (cons z y))))

(defthm structure-subsetp-reflexive
  (subsetp-equal x x))

(defthm structure-walk-library-fuel-suffices
  (not (member-equal *structure-walk-incomplete*
                     (mv-nth 1 (bx-walk nil definitions (bx-index definitions nil)
                                        nil nil nil (bx-steps definitions)))))
  :hints (("Goal"
           :use ((:instance structure-walk-fuel-suffices
                            (stack nil) (todo definitions)
                            (index (bx-index definitions nil))
                            (done nil) (acc nil) (notes nil)
                            (fuel (bx-steps definitions)) (universe definitions)))
           :in-theory (disable bx-walk bx-steps structure-walk-fuel-suffices))))

; Unless the walk runs out of fuel, a statement waiting in TODO or on the
; stack eventually reaches the result.  A mark may only move the statement
; from TODO to a frame or from a frame to the output.

(defun structure-walk-holds-line-p (line stack todo acc)
  (or (member-equal line todo)
      (member-equal line (strip-cars stack))
      (member-equal line acc)))

(defun structure-walk-mark-matches-p (line stack done acc)
  (let ((mark (cdr (hons-get line done))))
    (cond ((eq mark t) (member-equal line acc))
          ((eq mark :pending) (member-equal line (strip-cars stack)))
          (t t))))

(defthm structure-member-of-revappend
  (iff (member-equal x (revappend a b))
       (or (member-equal x a) (member-equal x b)))
  :hints (("Goal" :induct (revappend a b))))

(defthm structure-member-of-reverse
  (iff (member-equal x (reverse a)) (member-equal x a))
  :hints (("Goal" :in-theory (disable revappend))))

(defthm structure-member-of-append
  (iff (member-equal x (append a b))
       (or (member-equal x a) (member-equal x b))))

(defthm structure-walk-keeps-line-or-notes-exhaustion
  (implies (and (structure-walk-holds-line-p line stack todo acc)
                (structure-walk-mark-matches-p line stack done acc))
           (or (member-equal line
                             (mv-nth 0 (bx-walk stack todo index done acc notes fuel)))
               (member-equal *structure-walk-incomplete*
                             (mv-nth 1 (bx-walk stack todo index done acc notes fuel)))))
  :hints (("Goal" :induct (bx-walk stack todo index done acc notes fuel)
                  :in-theory (disable reverse))))

(defthm structure-walk-library-keeps-line
  (implies (member-equal line definitions)
           (member-equal line
                         (car (bx-walk nil definitions (bx-index definitions nil)
                                       nil nil nil (bx-steps definitions)))))
  :hints (("Goal"
           :use ((:instance structure-walk-keeps-line-or-notes-exhaustion
                            (stack nil) (todo definitions)
                            (index (bx-index definitions nil))
                            (done nil) (acc nil) (notes nil)
                            (fuel (bx-steps definitions))))
           :in-theory (disable bx-walk bx-steps
                               structure-walk-keeps-line-or-notes-exhaustion))))

; All eight statement kinds pass through the grouping and the walk.

(defthm structure-word-filter-keeps-line
  (implies (and (member-equal line statements)
                (member-equal (car line) words))
           (member-equal line (bx-words words statements))))

(defthm structure-library-order-keeps-line
  (implies (and (member-equal line statements)
                (member-equal (car line)
                              '("package" "hidden-package" "define" "constrain"
                                "choose" "theorem" "axiom" "reserve")))
           (member-equal line (mv-nth 0 (bx-library-order statements))))
  :hints (("Goal" :in-theory (disable bx-walk bx-steps bx-words append))))
