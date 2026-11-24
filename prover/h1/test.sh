# Judge with both checkers what the set proves alone (prover/CONVENTIONS.md,
# "Building and testing"). From the root of the repository, after
# sh prover/h1/build.sh and sh prover/driver/build.sh:
#
#     sh prover/h1/test.sh
#
# The table of what is expected is prover/h1/expected.tsv.
exec sh prover/driver/test.sh --sets H1 prover/h1/expected.tsv
