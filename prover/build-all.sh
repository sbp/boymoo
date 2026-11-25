#!/bin/sh
# Certify and export every book of the prover.  From the root of the
# repository, after sh export/run.sh:
#
#     sh prover/build-all.sh
#
# It runs sh prover/build.sh, then sh prover/SET/build.sh for the ten other
# sets, four at a time, each writing its output to build/prover/build-SET.log,
# then sh prover/driver/build.sh.  It stops at the first failure and ends
# with "All prover books are built." when every build succeeds.
set -u
mkdir -p build/prover
sh prover/build.sh || exit 1
printf '%s\n' t2 t3 t4 b1 b2 h1 h2 h3 h4 l1 |
    xargs -P 4 -n 1 sh -c '
        if ! sh prover/$0/build.sh > build/prover/build-$0.log 2>&1; then
            echo "prover/build-all.sh: sh prover/$0/build.sh failed; see build/prover/build-$0.log" >&2
            exit 255
        fi' || exit 1
sh prover/driver/build.sh || exit 1
echo 'All prover books are built.'
