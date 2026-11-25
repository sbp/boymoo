(in-package "BOYMOO-MODEL")

(logic)
(set-verify-guards-eagerness 0)
(set-guard-checking :none)

(assert-event
 (equal
  (list (a64-decode #x52c00000)   ; MOVZ W0 with a halfword beyond bit 31.
        (a64-decode #x12c00000)   ; MOVN W0 with a halfword beyond bit 31.
        (a64-decode #x11400000)   ; ADD W0, W0, #0, LSL #12.
        (a64-decode #x11800000)   ; An ADD immediate encoding with a reserved bit set.
        (a64-decode #x0bc00000)   ; ADD with a reserved shift.
        (a64-decode #x0a008000)   ; AND W0 with a shift beyond bit 31.
        (a64-decode #x8a200000)   ; BIC, outside the instruction subset.
        (a64-decode #xaa200000)   ; ORN with a first operand other than XZR.
        (a64-decode #x12400000)   ; A logical W immediate with N set.
        (a64-decode #x9240fc00)   ; A logical immediate with an all-ones element.
        (a64-decode #x53008000)   ; UBFM W0 with imms beyond bit 31.
        (a64-decode #x1ac02c00)   ; RORV, outside the instruction subset.
        (a64-decode #x9a800800)   ; A conditional-select encoding with a reserved bit set.
        (a64-decode #x78400800)   ; A load with a halfword size and reserved mode.
        (a64-decode #xf8400000)   ; LDUR, outside the addressed forms.
        (a64-decode #xf8600800)   ; A register-offset load with a reserved option.
        (a64-decode #xf8400c00)   ; LDR with base and destination overlap on writeback.
        (a64-decode #xa9400000)   ; LDP with both destinations equal.
        (a64-decode #xa8800400)   ; STP with base and source overlap on writeback.
        (a64-decode #xa8400400)   ; LDNP, outside the addressed forms.
        (a64-decode #x54000010)   ; BC.cond, outside the instruction subset.
        (a64-decode #xd61f0001)   ; A branch-register encoding with a reserved bit set.
        (a64-decode #xd503201f)   ; NOP, outside the instruction subset.
        (a64-decode #x114000000)) ; An input wider than one instruction word.
  '(:undefined :undefined (:arithmetic-imm 0 32 0 0 0)
    :undefined :undefined :undefined :undefined :undefined :undefined :undefined
    :undefined :undefined :undefined :undefined :undefined :undefined :undefined
    :undefined :undefined :undefined :undefined :undefined :undefined :undefined)))

(assert-event
 (let* ((empty (a64-state nil 0 16 0 nil))
        (entry (a64-store 4 20 #xd65f03c0
                 (a64-store 4 16 #xd28000e0
                   (a64-write-reg 30 64 nil 64 empty)))))
   (and
    (mv-let (status last)
      (a64-run 2 16 24 64 entry)
      (and (eq status :return) (= (a64-pc last) 64)
           (= (a64-read-reg 0 64 nil last) 7)))
    (mv-let (status last)
      (a64-run 2 16 24 nil entry)
      (and (eq status :outside) (= (a64-pc last) 64)))
    (mv-let (status last)
      (a64-run 1 16 24 64 entry)
      (and (eq status :limit) (= (a64-pc last) 20)))
    (mv-let (status last)
      (a64-run 3 nil nil nil empty)
      (and (eq status :undefined) (equal last empty))))))

(assert-event
 (let ((machine (a64-store 8 #xfffffffffffffffe #x8877665544332211
                           (a64-state nil 0 0 0 nil))))
   (and (= (a64-load 4 #xfffffffffffffffe machine) #x44332211)
        (= (a64-load 4 2 machine) #x88776655)
        (= (a64-load 8 #xfffffffffffffffe machine) #x8877665544332211))))

(assert-event
 (let* ((machine (a64-state '((8 . 64) (16 . 4)) 0 16 6 nil))
        (darwin (a64-store 4 16 #xd4001001 machine))
        (linux (a64-store 4 16 #xd4000001 machine)))
   (and (equal (a64-decode #xd41fffe1) '(:svc 65535))
        (equal (a64-decode #xd4000002) :undefined)
        (equal (a64-step darwin) '(:svc 128 4 64))
        (mv-let (status last)
          (a64-run 1 16 20 nil darwin)
          (and (equal status '(:svc 128 4 64)) (equal last darwin)))
        (mv-let (status last)
          (a64-run 1 16 20 nil linux)
          (and (equal status '(:svc 0 4 64)) (equal last linux))))))

(cw "A64 model checks passed.~%")
