(in-package "BOYMOO-COMPILER")

(include-book "qir")

(set-verify-guards-eagerness 0)

; Routines of the runtime written as functions of QIR-M, which the passes
; P5 to P9 compile like the functions of the program. Each computes what
; the routine of runtime.lisp named in its comment computes, for every
; datum. They obey the contract of a routine (compiler/README.md, "The
; runtime"), as the table of routines in qir.lisp lists them: arguments
; from x0 and the result in x0; x19 to x23, x25, x28, x29 and sp kept,
; for P8 allocates their registers without x19 to x22 and x29; only x0 to
; x17, x24 and the flags changed. P4 calls them with :rt in its slow
; paths (EXPAND-PROGRAM), P9 gives each the label of its name, and the
; driver adds (RT-QIR-FUNCTIONS) to the program after P4. A call of one
; from another is a :call. Their names have no "::", so that no function
; of a program has one of them. The hand-written routines stay in
; runtime.lisp, where the runtime itself calls them.
;
; None of them allocates. Each reads fields only of an object that it has
; tested to be a cons or an object with a header, or of the symbol NIL,
; the datum 34, which the static block always holds: the base of such a
; load is (:sel C X 34), which is X when the test C holds.
;
; The words of the data are those of compiler/README.md, "The data": an
; immediate integer n is 2n + 1; a cons has the low three bits 000; an
; object with a header has 010, and its header, at the datum less 2, is
; (size << 8) | type, the size counting the bytes after the header (type
; 1 string, 2 symbol, 3 integer, 4 fraction, 5 complex rational, 6
; vector); a character of code c is 8c + 4.

; jet:COMMON-LISP::LENGTH: the length of a string, from its header, as an
; immediate integer; for anything else, the number of conses reached by
; following CDR from it.
(defconst *rt-qir-length*
  '(:fn "rt-qir:LENGTH" ((:d . 0))
        ((0 () (((:w . 1) :and (:d . 0) (:k . 7))
                ((:w . 2) :ceq (:w . 1) (:k . 2))
                ((:d . 3) :sel (:w . 2) (:d . 0) (:k . 34))
                ((:w . 4) :ld (:d . 3) (:k . -2))
                ((:w . 5) :and (:w . 4) (:k . 255))
                ((:w . 6) :ceq (:w . 5) (:k . 1)))
            (:jnz (:w . 6) 1 2))
         (1 () (((:w . 7) :shr (:w . 4) (:k . 8))
                ((:w . 8) :shl (:w . 7) (:k . 1))
                ((:w . 9) :or (:w . 8) (:k . 1))
                ((:d . 10) :copy (:w . 9)))
            (:ret (:d . 10)))
         (2 () () (:jmp 3))
         (3 (((:d . 11) ((2 . (:d . 0)) (4 . (:d . 13))))
             ((:w . 12) ((2 . (:k . 1)) (4 . (:w . 14)))))
            (((:w . 15) :and (:d . 11) (:k . 7)))
            (:jnz (:w . 15) 5 4))
         (4 () (((:d . 13) :ld (:d . 11) (:k . 8))
                ((:w . 14) :add (:w . 12) (:k . 2)))
            (:jmp 3))
         (5 () (((:d . 16) :copy (:w . 12)))
            (:ret (:d . 16))))))

; jet:COMMON-LISP::CHAR: for a string S, the character at the index that
; I gives, or NIL when that index is not below the length; NIL for
; anything but a string. An immediate integer k gives the index k when k
; is above 0, else 0; a positive integer with a header gives 2^32; any
; other datum gives 0 (runtime.lisp, rt:sequence-count).
(defconst *rt-qir-char*
  '(:fn "rt-qir:CHAR" ((:d . 0) (:d . 1))
        ((0 () (((:w . 2) :and (:d . 0) (:k . 7))
                ((:w . 3) :ceq (:w . 2) (:k . 2))
                ((:d . 4) :sel (:w . 3) (:d . 0) (:k . 34))
                ((:w . 5) :ld (:d . 4) (:k . -2))
                ((:w . 6) :and (:w . 5) (:k . 255))
                ((:w . 7) :ceq (:w . 6) (:k . 1)))
            (:jnz (:w . 7) 1 9))
         (9 () () (:ret (:k . 34)))
         (1 () (((:w . 8) :and (:d . 1) (:k . 1)))
            (:jnz (:w . 8) 2 3))
         (2 () (((:w . 9) :sar (:d . 1) (:k . 1))
                ((:w . 10) :csgt (:w . 9) (:k . 0))
                ((:w . 11) :sel (:w . 10) (:w . 9) (:k . 0)))
            (:jmp 5))
         (3 () (((:w . 12) :and (:d . 1) (:k . 7))
                ((:w . 13) :ceq (:w . 12) (:k . 2))
                ((:d . 14) :sel (:w . 13) (:d . 1) (:k . 34))
                ((:w . 15) :ldb (:d . 14) (:k . -2))
                ((:w . 16) :ceq (:w . 15) (:k . 3))
                ((:d . 17) :sel (:w . 16) (:d . 14) (:k . 34))
                ((:w . 18) :ld (:d . 17) (:k . 6))
                ((:w . 19) :ceq (:w . 18) (:k . 0))
                ((:w . 20) :and (:w . 16) (:w . 19))
                ((:w . 21) :sel (:w . 20) (:k . 4294967296) (:k . 0)))
            (:jmp 5))
         (5 (((:w . 22) ((2 . (:w . 11)) (3 . (:w . 21)))))
            (((:w . 23) :shr (:w . 5) (:k . 8))
             ((:w . 24) :cult (:w . 22) (:w . 23)))
            (:jnz (:w . 24) 6 7))
         (6 () (((:w . 25) :add (:w . 22) (:k . 6))
                ((:w . 26) :ldb (:d . 0) (:w . 25))
                ((:w . 27) :shl (:w . 26) (:k . 3))
                ((:w . 28) :or (:w . 27) (:k . 4))
                ((:d . 29) :copy (:w . 28)))
            (:ret (:d . 29)))
         (7 () () (:ret (:k . 34))))))

; prim:COMMON-LISP::EQUAL: T when X and Y are the same word. Otherwise
; NIL unless both are conses or both have headers: their low three bits
; differ, or they are immediate integers or characters, each held in one
; way only. Two objects with headers go to RT-QIR:EQUAL-ATOM. Two conses
; are compared along their CDRs in a loop; each pair of CARs that differ
; is decided here when they are atoms, and by RT-QIR:EQUAL-ATOM when both
; have headers; at the first pair of CARs that are both conses, the rest
; of the two lists goes to the hand-written routine, which keeps its
; pending comparisons on the value stack. No function
; here calls itself, directly or not, so the machine stack holds at most
; one frame of each, which P9 leaves in the margin below x23 without a
; check (emit.lisp, EMIT-UNCHECKED), as the routines use it: a
; comparison stops, if at all, where the routine's would.
(defconst *rt-qir-equal*
  '(:fn "rt-qir:EQUAL" ((:d . 0) (:d . 1))
        ((0 () (((:w . 2) :ceq (:d . 0) (:d . 1)))
            (:jnz (:w . 2) 1 2))
         (1 () () (:ret (:k . 58)))
         (2 () (((:w . 3) :xor (:d . 0) (:d . 1))
                ((:w . 4) :and (:w . 3) (:k . 7)))
            (:jnz (:w . 4) 3 4))
         (3 () () (:ret (:k . 34)))
         (4 () (((:w . 5) :and (:d . 0) (:k . 7)))
            (:jnz (:w . 5) 5 10))
         (5 () (((:w . 6) :ceq (:w . 5) (:k . 2)))
            (:jnz (:w . 6) 7 6))
         (6 () () (:ret (:k . 34)))
         (7 () () (:tail "rt-qir:EQUAL-ATOM" (:d . 0) (:d . 1)))
         (10 () () (:jmp 11))
         (11 (((:d . 7) ((10 . (:d . 0)) (27 . (:d . 18))))
              ((:d . 8) ((10 . (:d . 1)) (27 . (:d . 19)))))
             (((:d . 9) :ld (:d . 7) (:k . 0))
              ((:d . 10) :ld (:d . 8) (:k . 0))
              ((:w . 11) :ceq (:d . 9) (:d . 10)))
             (:jnz (:w . 11) 20 12))
         (12 () (((:w . 12) :xor (:d . 9) (:d . 10))
                 ((:w . 13) :and (:w . 12) (:k . 7)))
             (:jnz (:w . 13) 13 14))
         (13 () () (:ret (:k . 34)))
         (14 () (((:w . 14) :and (:d . 9) (:k . 7)))
             (:jnz (:w . 14) 15 18))
         (15 () (((:w . 15) :ceq (:w . 14) (:k . 2)))
             (:jnz (:w . 15) 16 31))
         (31 () () (:ret (:k . 34)))
         (16 () (((:d . 23) :call "rt-qir:EQUAL-ATOM" (:d . 9) (:d . 10))
                 ((:w . 24) :ceq (:d . 23) (:k . 34)))
             (:jnz (:w . 24) 32 19))
         (32 () () (:ret (:k . 34)))
         (18 () (((:d . 25) :rt "prim:COMMON-LISP::EQUAL" (:d . 7) (:d . 8)))
             (:ret (:d . 25)))
         (19 () () (:jmp 20))
         (20 () (((:d . 18) :ld (:d . 7) (:k . 8))
                 ((:d . 19) :ld (:d . 8) (:k . 8))
                 ((:w . 27) :ceq (:d . 18) (:d . 19)))
             (:jnz (:w . 27) 21 22))
         (21 () () (:ret (:k . 58)))
         (22 () (((:w . 28) :xor (:d . 18) (:d . 19))
                 ((:w . 29) :and (:w . 28) (:k . 7)))
             (:jnz (:w . 29) 23 24))
         (23 () () (:ret (:k . 34)))
         (24 () (((:w . 30) :and (:d . 18) (:k . 7)))
             (:jnz (:w . 30) 25 27))
         (25 () (((:w . 31) :ceq (:w . 30) (:k . 2)))
             (:jnz (:w . 31) 26 34))
         (34 () () (:ret (:k . 34)))
         (26 () () (:tail "rt-qir:EQUAL-ATOM" (:d . 18) (:d . 19)))
         (27 () () (:jmp 11)))))

; EQUAL of X and Y, two different words with headers: NIL unless their
; headers, which give their type and size, are the same; NIL for
; symbols, which are equal only when they are the same word
; (runtime.lisp, rt:equal-distinct); strings and integers compare their
; bytes, word by word and then byte by byte; fractions, complex
; rationals and vectors, whose fields are data, go to the hand-written
; routine.
(defconst *rt-qir-equal-atom*
  '(:fn "rt-qir:EQUAL-ATOM" ((:d . 0) (:d . 1))
        ((0 () (((:w . 30) :ld (:d . 0) (:k . -2))
                ((:w . 31) :ld (:d . 1) (:k . -2))
                ((:w . 32) :cne (:w . 30) (:w . 31)))
            (:jnz (:w . 32) 41 42))
         (41 () () (:ret (:k . 34)))
         (42 () (((:w . 33) :and (:w . 30) (:k . 255))
                 ((:w . 34) :ceq (:w . 33) (:k . 2)))
             (:jnz (:w . 34) 43 44))
         (43 () () (:ret (:k . 34)))
         (44 () (((:w . 35) :shr (:w . 30) (:k . 8))
                 ((:w . 36) :cult (:w . 33) (:k . 4)))
             (:jnz (:w . 36) 50 45))
         (45 () (((:d . 37) :rt "prim:COMMON-LISP::EQUAL" (:d . 0) (:d . 1)))
             (:ret (:d . 37)))
         (50 () (((:w . 40) :and (:w . 35) (:k . -8)))
             (:jmp 51))
         (51 (((:w . 41) ((50 . (:k . 0)) (54 . (:w . 45)))))
             (((:w . 42) :cult (:w . 41) (:w . 40)))
             (:jnz (:w . 42) 52 55))
         (52 () (((:w . 43) :add (:w . 41) (:k . 6))
                 ((:w . 44) :ld (:d . 0) (:w . 43))
                 ((:w . 46) :ld (:d . 1) (:w . 43))
                 ((:w . 47) :cne (:w . 44) (:w . 46)))
             (:jnz (:w . 47) 53 54))
         (53 () () (:ret (:k . 34)))
         (54 () (((:w . 45) :add (:w . 41) (:k . 8)))
             (:jmp 51))
         (55 () () (:jmp 56))
         (56 (((:w . 48) ((55 . (:w . 40)) (59 . (:w . 53)))))
             (((:w . 49) :cult (:w . 48) (:w . 35)))
             (:jnz (:w . 49) 57 58))
         (57 () (((:w . 50) :add (:w . 48) (:k . 6))
                 ((:w . 51) :ldb (:d . 0) (:w . 50))
                 ((:w . 52) :ldb (:d . 1) (:w . 50))
                 ((:w . 54) :cne (:w . 51) (:w . 52)))
             (:jnz (:w . 54) 61 59))
         (61 () () (:ret (:k . 34)))
         (59 () (((:w . 53) :add (:w . 48) (:k . 1)))
             (:jmp 56))
         (58 () () (:ret (:k . 58))))))

; FN with each critical edge split (qir.lisp), as the back end needs.
(defun rt-qir-split (fn)
  (list :fn (qir-fn-name fn) (qir-fn-params fn)
        (qir-split-critical-edges (qir-fn-blocks fn) (qir-next-label fn))))

; The functions, which the driver adds to the program after P4.
(defun rt-qir-functions ()
  (list (rt-qir-split *rt-qir-length*)
        (rt-qir-split *rt-qir-char*)
        (rt-qir-split *rt-qir-equal*)
        (rt-qir-split *rt-qir-equal-atom*)))
