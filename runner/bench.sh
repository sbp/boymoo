#!/bin/sh
# The benchmarks of the reference runner, against ACL2 8.7.  Run from the
# root of the repository:
#
#     sh runner/bench.sh            builds build/runner/boymoo-run and times it
#     sh runner/bench.sh RUNNER     times the runner RUNNER, built otherwise
#
# It needs make, c99, acl2 (ACL2 8.7) and the POSIX tools env, time,
# sort, sed and awk.  ACL2 certifies each book of runner/bench/ into
# build/runner/bench/, so that its functions, whose guards are verified,
# run as compiled code, and export/book.sh exports it.  Then the same
# call is timed in ACL2, inside ACL2 with time$ (twenty calls timed
# together, divided by twenty) and as the whole process that starts
# ACL2, includes the book and makes the call; and in the runner, as the
# whole process that reads the program text and makes the call, and
# apart from that the process that only reads the program text.  Each
# time is the median of three runs, in seconds of elapsed time.  The peak
# of memory is what the runner reports with -v.  The runner's value must
# be ACL2's.  The table is written to build/runner/bench/table.txt.

B=build/runner/bench
BOOKS="fib loop lists sort alist fact power fractions chars symbols library"
if [ $# -gt 0 ]; then
    R=$1
else
    R=build/runner/boymoo-run
    make -f runner/Makefile > /dev/null || exit 1
fi
mkdir -p $B
LIB="-p spec/ground.txt -p build/export/library.statements"
PROG=build/export/library.program
if [ ! -f $PROG ] || [ ! -f build/export/library.statements ]; then
    echo "runner/bench.sh: run sh runner/test.sh or sh export/run.sh first" >&2
    exit 1
fi

median() { sort -n | sed -n 2p; }

for b in $BOOKS; do
    rm -f "$B/$b.cert" "$B/$b.port"
    cp runner/bench/$b.lisp $B/$b.lisp
    {
        echo '(ld "checks/version.lsp")'
        echo "(certify-book \"$B/$b\" 0 nil)"
    } | acl2 > $B/$b.cert.log 2>&1
    if [ $? -eq 3 ]; then
        echo "runner/bench.sh stopped: $(sed -n 's/^version: //p' $B/$b.cert.log)" >&2
        exit 3
    fi
    [ -f $B/$b.cert ] || { echo "runner/bench.sh: ACL2 did not certify $B/$b" >&2; exit 1; }
    sh export/book.sh $B/$b
    echo "(bench-$b)" > $B/$b.calls
done

printf '%-10s %10s %10s %10s %10s %8s %s\n' book acl2-call acl2-proc runner runner-load peak-MB value > $B/table.txt
for b in $BOOKS; do
    E=build/export/books/$B/$b
    # ACL2: its value in the text of the formats; then four times twenty
    # calls, each twenty timed together by time$, of which the last three
    # count; and the whole process.
    {
        echo '(in-package "ACL2")'
        echo "(include-book \"$B/$b\")"
        echo '(ld "checks/canon.lsp")'
        echo '(ld "runner/test/expect.lsp")'
        echo "(rt-expect \"$B/$b.calls\" \"$B/$b\" state)"
        calls=$(awk -v b=$b 'BEGIN { for (i = 0; i < 20; i++) printf "(bench-%s) ", b }')
        for i in 1 2 3 4; do echo "(time\$ (list $calls))"; done
        echo '(good-bye)'
    } | acl2 > $B/$b.acl2.log 2>&1
    call=$(grep -a -o '[0-9.]* seconds realtime' $B/$b.acl2.log | sed 1d | sed 's/ .*//' | median |
               awk '{ printf "%.4f", $1 / 20 }')
    for i in 1 2 3; do
        { echo "(include-book \"$B/$b\")"; echo "(bench-$b)"; echo '(good-bye)'; } |
            env time -p acl2 2>&1 > /dev/null | sed -n 's/^real //p'
    done > $B/$b.proc
    proc=$(median < $B/$b.proc)
    # The runner: the whole process, and the reading of the program text.
    for i in 1 2 3; do
        env time -p "$R" -v $LIB -p $E.statements $PROG $E.program < $B/$b.terms 2> $B/$b.err > $B/$b.out
        sed -n 's/^real //p' $B/$b.err
    done > $B/$b.run
    run=$(median < $B/$b.run)
    peak=$(sed -n 's/.*peak memory \([0-9]*\) KB.*/\1/p' $B/$b.err | awk '{ printf "%.0f", $1 / 1024 }')
    echo "(COMMON-LISP::QUOTE 0)" > $B/load.in
    for i in 1 2 3; do
        env time -p "$R" $LIB -p $E.statements $PROG $E.program < $B/load.in 2>&1 > /dev/null |
            sed -n 's/^real //p'
    done > $B/$b.load
    load=$(median < $B/$b.load)
    if cmp -s $B/$b.out $B/$b.values; then same=same; else same=DIFFERENT; fi
    printf '%-10s %10s %10s %10s %10s %8s %s\n' $b "$call" "$proc" "$run" "$load" "$peak" $same >> $B/table.txt
done
{
    echo
    echo "sh runner/bench.sh, run on $(date +%Y-%m-%d); times in seconds of elapsed time, medians of three runs"
} >> $B/table.txt
cat $B/table.txt
