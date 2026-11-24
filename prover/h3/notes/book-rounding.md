# Rounding

The divisor-shift recipe uses floor bounds and an integer-gap lemma to
remove an inner floor. The rounding theorem's `-with-library` form
preserves those lemmas for the next tactic if a later bound fails.
