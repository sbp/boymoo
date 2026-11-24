# Judge with both checkers what the set proves alone (prover/CONVENTIONS.md,
# "Building and testing"). From the root of the repository, after
# sh prover/t4/build.sh and sh prover/driver/build.sh:
#
#     sh prover/t4/test.sh
#
# The table of what is expected is prover/t4/expected.tsv.
exec sh prover/driver/test.sh --sets T4 prover/t4/expected.tsv
