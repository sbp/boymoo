# Judge with both checkers what the set proves alone (prover/CONVENTIONS.md,
# "Building and testing"). From the root of the repository, after
# sh prover/h3/build.sh and sh prover/driver/build.sh:
#
#     sh prover/h3/test.sh
#
# The table of what is expected is prover/h3/expected.tsv.
exec sh prover/driver/test.sh --sets H3 prover/h3/expected.tsv
