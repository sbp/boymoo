#!/bin/sh
# What each function of the reference runner's prelude saves (the option
# -j, runner/README.md, "The prelude").  Run from the root of the
# repository:
#
#     sh runner/prelude.sh            builds build/runner/boymoo-run and times it
#     sh runner/prelude.sh RUNNER     times the runner RUNNER, built otherwise
#
# It needs make and c99 (or the compiler given to make), the library's
# program text and statements, which sh runner/test.sh writes if they
# are missing, and the POSIX tools grep, sed and awk.  For each
# of ash and binary-logxor it times calls on the same arguments
# twice: by ACL2's definitions, from the library's program text; and
# with -j, from that text less the define line of that one function, so
# that only it is the prelude's.  The calls are made by a loop defined
# in program text, and the time of the same loop without the call is
# taken away.  Times are the runner's own (-v), of the processor, the
# least of three runs, in microseconds a call.  Every run is given at most 1,000 megabytes, which
# a call by the definitions exhausts when its quotient is large.  The
# table is written to build/runner/prelude/table.txt.

T=build/runner/prelude
if [ $# -gt 0 ]; then
    R=$1
else
    R=build/runner/boymoo-run
    make -f runner/Makefile > /dev/null || exit 1
fi
mkdir -p $T
LIB="-p spec/ground.txt -p build/export/library.statements"
PROG=build/export/library.program
Q=COMMON-LISP::QUOTE
grep -v '^(define COMMON-LISP::NIL (COMMON-LISP::ASH ' $PROG > $T/ASH.program
grep -v '^(define COMMON-LISP::NIL (ACL2::BINARY-LOGXOR ' $PROG > $T/LOGXOR.program

# (LOOP-F n x y acc) calls F on x and y, n times.
loop() {
    printf '(define COMMON-LISP::NIL (ACL2::LOOP-%s (ACL2::N ACL2::X ACL2::Y ACL2::ACC) ' "$1"
    printf '(COMMON-LISP::IF (ACL2::ZP ACL2::N) ACL2::ACC (ACL2::LOOP-%s ' "$1"
    printf '(ACL2::BINARY-+ ACL2::N (%s -1)) ACL2::X ACL2::Y %s))))\n' $Q "$2"
}
{
    loop NOTHING 'ACL2::X'
    loop ASH '(COMMON-LISP::ASH ACL2::X ACL2::Y)'
    loop LOGXOR '(ACL2::BINARY-LOGXOR ACL2::X ACL2::Y)'
} > $T/loops.program

# seconds OPTION LIBRARY FUNCTION N X Y: the seconds of N calls, the
# least of three runs, or "memory" if a run exhausted it.
seconds() {
    least=
    for run in 1 2 3; do
        echo "(ACL2::LOOP-$3 ($Q $4) ($Q $5) ($Q $6) ($Q 0))" |
            "$R" -v -m 1000 $1 $LIB $2 $T/loops.program > /dev/null 2> $T/err
        case $? in
            0) s=$(sed -n 's/.* run \([0-9.]*\) s .*/\1/p' $T/err)
               least=$(echo "$s $least" | awk '{ print ($2 == "" || $1 < $2) ? $1 : $2 }') ;;
            3) echo memory; return ;;
            *) echo "runner/prelude.sh: $(cat $T/err)" >&2; exit 1 ;;
        esac
    done
    echo "$least"
}

# row FUNCTION ARGUMENTS X Y N: N calls by the definitions, 200,000 with
# the prelude.
row() {
    d0=$(seconds "" $PROG NOTHING $5 $3 $4)
    d1=$(seconds "" $PROG $1 $5 $3 $4)
    j0=$(seconds "" $PROG NOTHING 200000 $3 $4)
    j1=$(seconds -j $T/$1.program $1 200000 $3 $4)
    case $1 in ASH) name=ash ;; *) name=binary-logxor ;; esac
    awk -v f="$name" -v what="$2" -v n=$5 -v d0="$d0" -v d1="$d1" -v j0="$j0" -v j1="$j1" 'BEGIN {
        j = (j1 - j0) / 200000 * 1000000
        d = (d1 - d0) / n * 1000000
        if (d1 == "memory") d = "1,000 megabytes exhausted"
        else d = sprintf(d < 100 ? "%.1f" : "%.0f", d)
        printf "| `%s` | %s | %s | %.2f |\n", f, what, d, j }'
}
{
    echo '| Function | Arguments | By its definition | By the prelude |'
    echo '|---|---|---:|---:|'
    row ASH "an integer of 64 bits, left by 13 bits" 12345678901234567890 13 20000
    row ASH "an integer of 64 bits, right by 51 bits" 12345678901234567890 -51 200
    row ASH "an integer of 64 bits, right by 43 bits" 12345678901234567890 -43 2
    row ASH "an integer of 64 bits, right by 32 bits" 12345678901234567890 -32 1
    row LOGXOR "two integers of 8 bits" 201 77 2000
    row LOGXOR "two integers of 16 bits" 51234 43210 50
    row LOGXOR "two integers of 24 bits" 12345678 9876543 1
    row LOGXOR "two integers of 64 bits" 12345678901234567890 9876543210987654321 1
} | tee $T/table.txt
