# Judge with both checkers what the set proves alone (prover/CONVENTIONS.md,
# "Building and testing"). From the root of the repository, after
# sh prover/t2/build.sh and sh prover/driver/build.sh:
#
#     sh prover/t2/test.sh
#
# The table of what is expected is prover/t2/expected.tsv.
exec sh prover/driver/test.sh --sets T2 prover/t2/expected.tsv
