(in-package "BOYMOO")

(include-book "guards-entry")
(include-book "guards-equations")

(make-event
 (let ((wrld (w state)))
   (value
    (list 'defthm 'cg-native-car-guard-rejects-integer
          (list 'not
                (list (list 'lambda (acl2::formals 'car wrld)
                            (acl2::untranslate (acl2::guard 'car nil wrld) nil wrld))
                      42))
          :rule-classes nil))))

; The compute rule uses the total value of CAR. On a number it gives
; NIL, although an integer is outside the ACL2 execution guard of CAR.
(defthm cg-compute-car-on-an-integer
  (equal (check "(primitive COMMON-LISP::CAR 1)
(primitive COMMON-LISP::EQUAL 2)
"
                ""
                "(theorem COMMON-LISP::GUARD-SAMPLE (COMMON-LISP::EQUAL (COMMON-LISP::CAR (COMMON-LISP::QUOTE 42)) (COMMON-LISP::QUOTE COMMON-LISP::NIL)))
"
                "(theorem COMMON-LISP::GUARD-SAMPLE)
(compute (COMMON-LISP::CAR (COMMON-LISP::QUOTE 42)))
(qed)
")
         '("accepted" ""))
  :rule-classes nil)

; Duplicate detection can see a malformed definition. The total
; projection of 7 gives NIL, and admission rejects the line.
(defthm cg-malformed-definition-is-rejected
  (equal (check "" "" "(define COMMON-LISP::NIL 7)
" "")
         '("rejected statements 1" "a define line needs ruler-extenders and definitions"))
  :rule-classes nil)

(defthm cg-malformed-definition-has-no-first-name
  (equal (first-name '(:define nil 7)) nil)
  :rule-classes nil)

; A number used as a ground package name is outside the ACL2 guard
; of COERCE and fails the shape check for ground package lines.
(make-event
 (let ((wrld (w state)))
   (value
    (list 'defthm 'cg-native-coerce-guard-rejects-number-to-list
          (list 'not
                (list (list 'lambda (acl2::formals 'coerce wrld)
                            (acl2::untranslate (acl2::guard 'coerce nil wrld) nil wrld))
                      42 ''list))
          :rule-classes nil))))

(defthm cg-ground-package-with-numeric-name
  (equal (check "(package 42 COMMON-LISP::NIL)
" "" "" "")
         '("the ground theory could not be read" ""))
  :rule-classes nil)
