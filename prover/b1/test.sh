# Judge with both checkers what the set proves alone (prover/CONVENTIONS.md,
# "Building and testing"). From the root of the repository, after
# sh prover/b1/build.sh and sh prover/driver/build.sh:
#
#     sh prover/b1/test.sh
#
# The table of what is expected is prover/b1/expected.tsv.
exec sh prover/driver/test.sh --sets B1 prover/b1/expected.tsv
