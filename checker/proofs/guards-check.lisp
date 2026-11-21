(in-package "BOYMOO")

(include-book "check")
(include-book "guards-admit")

(verify-guards initial-world
  :hints (("Goal" :in-theory (enable declare-package
                                     set-pkgs put-entry set-names make-world))))
(verify-guards verdict
  :hints (("Goal" :in-theory (disable app decimal))))
(verify-guards rejection-verdict
  :hints (("Goal" :in-theory (disable app decimal))))
