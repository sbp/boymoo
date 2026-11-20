; A book for the exporter, for two cases that no certified book of ACL2's
; distribution keeps in its world: functions introduced by choice with
; the strengthened axiom, with one bound variable and with two, and a
; definition admitted with the well-founded relation l<.  export/run.sh
; copies it into build/ and certifies it there.

(in-package "ACL2")

(defchoose bx-choice-1 (v) (x)
  (member-equal v x)
  :strengthen t)

(defchoose bx-choice-2 (v w) (x y)
  (equal (cons v (cons w y)) x)
  :strengthen t)

(defun bx-lex (i j)
  (declare (xargs :measure (list (nfix i) (nfix j))
                  :well-founded-relation l<))
  (cond ((zp i) 0)
        ((zp j) (bx-lex (1- i) 10))
        (t (bx-lex i (1- j)))))
