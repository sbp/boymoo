#!/bin/sh
# Run every test of the prover.  From the root of the repository, after
# sh prover/build-all.sh and sh review/termination/run.sh:
#
#     sh prover/test-all.sh
#
# The driver's test runs first and alone, so that the fast runner compiles
# the driver's program into its cache once; then the tests of the eleven
# sets, three at a time.  Each test writes its output to
# build/prover/test-SET.log, and its last line is printed.  It ends with
# "All prover tests passed." or "Some prover tests failed."
set -u
mkdir -p build/prover
status=0
sh prover/driver/test.sh > build/prover/test-driver.log 2>&1 || status=1
echo "driver: $(tail -1 build/prover/test-driver.log)"
printf '%s\n' t1 t2 t3 t4 b1 b2 h1 h2 h3 h4 l1 |
    xargs -P 3 -n 1 sh -c '
        case $0 in t1) test=prover/test.sh ;; *) test=prover/$0/test.sh ;; esac
        sh $test > build/prover/test-$0.log 2>&1
        result=$?
        echo "$0: $(tail -1 build/prover/test-$0.log)"
        exit $result' || status=1
if [ "$status" -eq 0 ]; then
    echo 'All prover tests passed.'
else
    echo 'Some prover tests failed.'
    exit 1
fi
