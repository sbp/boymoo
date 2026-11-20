; Boymoo, the checker: lists, tries and decimal numbers.
;
; The checker is written in ACL2 Core: every function it defines calls only
; the 32 primitive functions, the 36 functions that the ground theory
; defines (spec/logic.md, section 3) and functions defined in these books.
; So it uses none of the list functions of ACL2's library, and defines the
; few it needs here.

(in-package "BOYMOO")

; ---------------------------------------------------------------------------
; Lists

; The elements of X in reverse order, followed by ACC.
(defun rev-onto (x acc)
  (if (consp x)
      (rev-onto (cdr x) (cons (car x) acc))
    acc))

(defun rev (x)
  (rev-onto x nil))

; X followed by Y.
(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun member-p (x l)
  (if (consp l)
      (if (equal x (car l))
          t
        (member-p x (cdr l)))
    nil))

; The first pair of the association list AL whose car is K, or NIL.
(defun pair-of (k al)
  (if (consp al)
      (if (and (consp (car al)) (equal k (car (car al))))
          (car al)
        (pair-of k (cdr al)))
    nil))

; No element of L stands twice in it.
(defun distinct-p (l)
  (if (consp l)
      (if (member-p (car l) (cdr l))
          nil
        (distinct-p (cdr l)))
    t))

; No element of X is an element of Y.
(defun disjoint-p (x y)
  (if (consp x)
      (if (member-p (car x) y)
          nil
        (disjoint-p (cdr x) y))
    t))

; The element of L at position N, counted from 1.
(defun nth-elem (n l)
  (if (consp l)
      (if (zp n)
          nil
        (if (equal n 1)
            (car l)
          (nth-elem (+ -1 n) (cdr l))))
    nil))

; L with its element at position N, counted from 1, replaced by X.
(defun replace-nth (n l x)
  (if (consp l)
      (if (zp n)
          l
        (if (equal n 1)
            (cons x (cdr l))
          (cons (car l) (replace-nth (+ -1 n) (cdr l) x))))
    l))

; The last element of L.
(defun last-elem (l)
  (if (consp l)
      (if (consp (cdr l))
          (last-elem (cdr l))
        (car l))
    nil))

; L begins with the elements of P.
(defun prefix-p (p l)
  (if (consp p)
      (if (consp l)
          (if (equal (car p) (car l))
              (prefix-p (cdr p) (cdr l))
            nil)
        nil)
    t))

; The sum of the numbers of L.
(defun sum (l)
  (if (consp l)
      (+ (car l) (sum (cdr l)))
    0))

; ---------------------------------------------------------------------------
; Tries
;
; A trie maps keys, which are lists of characters, to values that are not
; NIL.  A node is NIL, or a cons of the value at the node, NIL if there is
; none, and an association list from characters to the nodes below it.
; The runner has no arrays, and a symbol has no number of its own, so the
; checker finds a name by walking the characters of its text.

(defun trie-child (c kids)
  (if (consp kids)
      (if (and (consp (car kids)) (equal c (car (car kids))))
          (cdr (car kids))
        (trie-child c (cdr kids)))
    nil))

; The value of KEY in the trie NODE, or NIL.
(defun trie-get (key node)
  (if (consp node)
      (if (consp key)
          (trie-get (cdr key) (trie-child (car key) (cdr node)))
        (car node))
    nil))

(defun trie-drop (c kids)
  (if (consp kids)
      (if (and (consp (car kids)) (equal c (car (car kids))))
          (cdr kids)
        (cons (car kids) (trie-drop c (cdr kids))))
    nil))

; The trie NODE with the value of KEY made VAL.  The child changed is put
; first, so that the names used most recently are found soonest.
(defun trie-put (key val node)
  (if (consp key)
      (cons (if (consp node) (car node) nil)
            (cons (cons (car key)
                        (trie-put (cdr key) val
                                  (if (consp node)
                                      (trie-child (car key) (cdr node))
                                    nil)))
                  (if (consp node) (trie-drop (car key) (cdr node)) nil)))
    (cons val (if (consp node) (cdr node) nil))))

; ---------------------------------------------------------------------------
; Decimal numbers, written without division: the runner computes floor by
; its definition, one subtraction for each unit of the quotient.

; The powers of ten that are not above N, the largest first, before ACC.
(defun tens-up-to (n p acc)
  (declare (xargs :measure (nfix (- (+ 1 (nfix n)) (nfix p)))))
  (if (and (integerp n) (integerp p) (< 0 p) (not (< n p)))
      (tens-up-to n (* 10 p) (cons p acc))
    acc))

; The number of times, at most 9, that P can be taken from N.
(defun digit-count (n p d)
  (declare (xargs :measure (nfix (- 9 (nfix d)))))
  (if (and (natp d) (< d 9) (integerp n) (integerp p) (< 0 p) (not (< n p)))
      (digit-count (- n p) p (+ 1 d))
    d))

(defun decimal-digits (n ps)
  (if (consp ps)
      (let ((d (digit-count n (car ps) 0)))
        (cons (code-char (+ 48 d))
              (decimal-digits (- n (* d (car ps))) (cdr ps))))
    nil))

; The characters of the decimal numeral of the natural number N.
(defun decimal (n)
  (if (and (integerp n) (< 0 n))
      (decimal-digits n (tens-up-to n 1 nil))
    (list #\0)))
