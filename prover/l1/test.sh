# Judge with both checkers what the set proves alone (prover/CONVENTIONS.md,
# "Building and testing"). From the root of the repository, after
# sh prover/l1/build.sh and sh prover/driver/build.sh:
#
#     sh prover/l1/test.sh
#
# The table of what is expected is prover/l1/expected.tsv.
exec sh prover/driver/test.sh --sets L1 prover/l1/expected.tsv
