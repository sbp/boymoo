# Lexer suffix bounds

The lexer recipes bound the length of a suffix returned by a scanner. `*lexer-fields*` gives the selector depths for the output suffix and the input suffix of each scanner. The tactic combines bounds along suffix edges and uses the resulting length comparison for an ordinal decrease.
