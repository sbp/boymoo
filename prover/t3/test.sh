# Judge with both checkers what the set proves alone (prover/CONVENTIONS.md,
# "Building and testing"). From the root of the repository, after
# sh prover/t3/build.sh and sh prover/driver/build.sh:
#
#     sh prover/t3/test.sh
#
# The table of what is expected is prover/t3/expected.tsv.
exec sh prover/driver/test.sh --sets T3 prover/t3/expected.tsv
