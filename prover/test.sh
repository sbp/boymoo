# Judge with both checkers what the set proves alone (prover/CONVENTIONS.md,
# "Building and testing"). From the root of the repository, after
# sh prover/build.sh and sh prover/driver/build.sh:
#
#     sh prover/test.sh
#
# The table of what is expected is prover/expected.tsv.
exec sh prover/driver/test.sh --sets T1 prover/expected.tsv
