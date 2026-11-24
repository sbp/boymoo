#!/bin/sh
# The benchmarks of the fast runner, against the reference runner.  Run
# from the root of the repository:
#
#     sh runner-fast/bench.sh
#
# It needs make, cc, acl2 (ACL2 8.7) and the POSIX tools env, time, sort,
# sed and awk, and the library's exported files, which sh export/run.sh
# or sh runner/test.sh writes.  ACL2 certifies each book of runner/bench/
# into build/runner-fast/bench/, unless it has done so already for the
# same text, and export/book.sh exports it.  Then the call (bench-BOOK)
# is run in each runner, as the whole process that reads the program text
# and makes the call: first once in the fast runner, which compiles what
# the call needs into the cache build/runner-fast/bench/cache, and then
# three times in each runner.  Each time is the median of the three runs,
# in seconds of processor time, user and system, as time -p gives it; the
# ratio is the reference runner's time over the fast runner's.  The two
# runners must give the same output and status.  The table is written to
# build/runner-fast/bench/table.txt.

B=build/runner-fast/bench
BOOKS="fib loop lists sort alist fact power fractions chars symbols library"
F=build/runner-fast/boymoo-run-fast
R=build/runner/boymoo-run
make -f runner-fast/Makefile > /dev/null || exit 1
make -f runner/Makefile > /dev/null || exit 1
LIB="-p spec/ground.txt -p build/export/library.statements"
PROG=build/export/library.program
if [ ! -f $PROG ] || [ ! -f build/export/library.statements ]; then
    echo "runner-fast/bench.sh: run sh runner/test.sh or sh export/run.sh first" >&2
    exit 1
fi
BOYMOO_FAST_CACHE=$B/cache
export BOYMOO_FAST_CACHE
unset BOYMOO_FAST BOYMOO_FAST_NATIVE BOYMOO_FAST_NOINLINE BOYMOO_FAST_VERBOSE BOYMOO_FAST_KEEP \
      BOYMOO_FAST_NAMES BOYMOO_FAST_ROOT
mkdir -p $B

for b in $BOOKS; do
    E=build/export/books/$B/$b
    if ! cmp -s runner/bench/$b.lisp $B/$b.lisp || [ ! -f $B/$b.cert ]; then
        rm -f "$B/$b.cert" "$B/$b.port" "$E.program"
        cp runner/bench/$b.lisp $B/$b.lisp
        {
            echo '(ld "checks/version.lsp")'
            echo "(certify-book \"$B/$b\" 0 nil)"
        } | acl2 > $B/$b.cert.log 2>&1
        if [ $? -eq 3 ]; then
            echo "runner-fast/bench.sh stopped: $(sed -n 's/^version: //p' $B/$b.cert.log)" >&2
            exit 3
        fi
        [ -f $B/$b.cert ] || { echo "runner-fast/bench.sh: ACL2 did not certify $B/$b" >&2; exit 1; }
    fi
    if [ ! -f $E.program ]; then
        sh export/book.sh $B/$b || exit $?
        [ -f $E.program ] || { echo "runner-fast/bench.sh: $B/$b was not exported; see $E.log" >&2; exit 1; }
    fi
done

median() { sort -n | sed -n 2p; }
# cpu RUNNER ARGS...: the processor time of one run on $B/call.in.
cpu() {
    env time -p "$@" < $B/call.in 2>&1 > $B/out.$$ |
        awk '$1 == "user" || $1 == "sys" { t += $2 } END { printf "%.2f\n", t }'
}

status=0
printf '%-10s %8s %8s %6s %s\n' book ref-cpu fast-cpu ratio value > $B/table.txt
for b in $BOOKS; do
    E=build/export/books/$B/$b
    A="$LIB -p $E.statements $PROG $E.program"
    echo "(bench-$b)" | tr a-z A-Z | sed 's/^(/(ACL2::/' > $B/call.in
    "$F" $A < $B/call.in > /dev/null 2>&1
    "$R" $A < $B/call.in > $B/$b.ref.out 2> /dev/null
    rs=$?
    "$F" $A < $B/call.in > $B/$b.fast.out 2> /dev/null
    fs=$?
    for i in 1 2 3; do cpu "$R" $A; done > $B/$b.ref.cpu
    for i in 1 2 3; do cpu "$F" $A; done > $B/$b.fast.cpu
    rc=$(median < $B/$b.ref.cpu)
    fc=$(median < $B/$b.fast.cpu)
    ratio=$(awk -v a="$rc" -v b="$fc" 'BEGIN { if (b > 0) printf "%.1f", a / b; else print "-" }')
    if [ $rs -eq 0 ] && [ $fs -eq 0 ] && cmp -s $B/$b.ref.out $B/$b.fast.out; then
        same=same
    else
        same=DIFFERENT
        status=1
    fi
    printf '%-10s %8s %8s %6s %s\n' $b "$rc" "$fc" "$ratio" $same >> $B/table.txt
done
rm -f $B/out.$$
{
    echo
    echo "sh runner-fast/bench.sh, run on $(date +%Y-%m-%d); processor time in seconds, medians of three runs"
} >> $B/table.txt
cat $B/table.txt
exit $status
