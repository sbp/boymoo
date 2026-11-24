# Abstract list constraints

The list signature identifies the list argument and the two constraint
facts for its cons and atom cases. Recipe dispatch uses
`b1-abstract-lists-abstract-list-butlast-with-library` to retain the
number lemmas installed while proving the length of `BUTLAST`.

The `SUBSEQ` recipe uses the earlier `TAKE` type law. The statement
generator uses its input Library when a recipe returns a bare failure.
