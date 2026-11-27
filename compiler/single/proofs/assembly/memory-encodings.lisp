(in-package "BOYMOO-PROOFS")

(include-book "signed-fields")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-compiler::a64-signed-scaled)))

(assembly-decode-word-rule assembly-decode-ldr
  (list :ldr rt rn (* 8 immediate))
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #xf9400000 ((0 5 rt) (5 5 rn) (10 12 immediate))
  (list :single 1 8 rn rt :offset (* 8 immediate)))

(assembly-decode-word-rule assembly-decode-str
  (list :str rt rn (* 8 immediate))
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rn) (unsigned-byte-p 12 immediate))
  #xf9000000 ((0 5 rt) (5 5 rn) (10 12 immediate))
  (list :single 0 8 rn rt :offset (* 8 immediate)))

(assembly-decode-word-rule assembly-decode-ldp
  (list :ldp rt rt2 rn (* 8 displacement))
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rt2) (unsigned-byte-p 5 rn)
       (signed-byte-p 7 displacement)
       (not (equal rt rt2)))
  #xa9400000 ((0 5 rt) (5 5 rn) (10 5 rt2) (15 7 (assembly-low 7 displacement)))
  (list :pair t rn rt rt2 :offset (* 8 displacement)))

(assembly-decode-word-rule assembly-decode-stp
  (list :stp rt rt2 rn (* 8 displacement))
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rt2) (unsigned-byte-p 5 rn)
       (signed-byte-p 7 displacement))
  #xa9000000 ((0 5 rt) (5 5 rn) (10 5 rt2) (15 7 (assembly-low 7 displacement)))
  (list :pair nil rn rt rt2 :offset (* 8 displacement)))

(assembly-decode-word-rule assembly-decode-ldp-post
  (list :ldp-post rt rt2 rn (* 8 displacement))
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rt2) (unsigned-byte-p 5 rn)
       (signed-byte-p 7 displacement)
       (not (equal rt rt2))
       (or (equal rn 31) (and (not (equal rn rt)) (not (equal rn rt2)))))
  #xa8c00000 ((0 5 rt) (5 5 rn) (10 5 rt2) (15 7 (assembly-low 7 displacement)))
  (list :pair t rn rt rt2 :post (* 8 displacement)))

(assembly-decode-word-rule assembly-decode-stp-pre
  (list :stp-pre rt rt2 rn (* 8 displacement))
  (and (unsigned-byte-p 5 rt) (unsigned-byte-p 5 rt2) (unsigned-byte-p 5 rn)
       (signed-byte-p 7 displacement)
       (or (equal rn 31) (and (not (equal rn rt)) (not (equal rn rt2)))))
  #xa9800000 ((0 5 rt) (5 5 rn) (10 5 rt2) (15 7 (assembly-low 7 displacement)))
  (list :pair nil rn rt rt2 :pre (* 8 displacement)))
