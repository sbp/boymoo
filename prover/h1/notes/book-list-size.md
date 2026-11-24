# Length and count bounds

The induction tactic proves bounds on `LEN` and `ACL2-COUNT`. Its
simplifier uses the H1 constant rules. The scan tactics use the
installed bounds when proving that an index stays within a list.
