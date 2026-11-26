#!/bin/sh
# Run every test of the prover.  From the root of the repository, after
# sh prover/build-all.sh and sh review/termination/run.sh:
#
#     sh prover/test-all.sh [--compare]
#
# The driver's test runs first and alone, so that the fast runner compiles
# the driver's program into its cache once; then the tests of the eleven
# sets, three at a time.  Each test writes its output to
# build/prover/test-SET.log, and its last line is printed.  It ends with
# "All prover tests passed." or "Some prover tests failed." With --compare,
# each case uses both drivers, compares their proof bytes and checks the
# compiled driver's proof. The comparison logs are in build/prover/compare/.
set -u
jobs=${PROVER_TEST_JOBS:-3}
case $jobs in ''|0*|*[!0-9]*) exit 2 ;; esac
logs=build/prover
if [ "${1-}" = --compare ]; then
    [ -x build/compiler/prover ] || {
        printf '%s\n' 'Run sh compiler/build-prover.sh before comparing the drivers.' >&2
        exit 2
    }
    export PROVER_TEST_COMPARE=1
    logs=$logs/compare
    shift
fi
[ "$#" -eq 0 ] || { printf '%s\n' 'Usage: sh prover/test-all.sh [--compare]' >&2; exit 2; }
mkdir -p "$logs" || exit 2
status=0
sh prover/driver/test.sh > "$logs/test-driver.log" 2>&1 || status=1
echo "driver: $(tail -1 "$logs/test-driver.log")"
printf '%s\n' t1 t2 t3 t4 b1 b2 h1 h2 h3 h4 l1 |
    xargs -P "$jobs" -n 1 sh -c '
        logs=$1 set=$2
        case $set in t1) test=prover/test.sh ;; *) test=prover/$set/test.sh ;; esac
        sh "$test" > "$logs/test-$set.log" 2>&1
        result=$?
        echo "$set: $(tail -1 "$logs/test-$set.log")"
        exit "$result"' sh "$logs" || status=1
if [ "$status" -eq 0 ]; then
    echo 'All prover tests passed.'
else
    echo 'Some prover tests failed.'
    exit 1
fi
