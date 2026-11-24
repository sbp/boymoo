# Book proof rules

Book library construction selects the `:book` rules before building
the slice theory. The shared constant proof operation uses that rule
selection for quoted cons values. The book theory also proves Boolean
types and turns known Boolean truth values into equalities.
