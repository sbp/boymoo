# Judge with both checkers what the set proves alone (prover/CONVENTIONS.md,
# "Building and testing"). From the root of the repository, after
# sh prover/h2/build.sh and sh prover/driver/build.sh:
#
#     sh prover/h2/test.sh
#
# The table of what is expected is prover/h2/expected.tsv.
exec sh prover/driver/test.sh --sets H2 prover/h2/expected.tsv
