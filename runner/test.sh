#!/bin/sh
# The tests of the reference runner, PLAN.md step 3.  Run from the root
# of the repository:
#
#     sh runner/test.sh            builds build/runner/boymoo-run and tests it
#     sh runner/test.sh RUNNER     tests the runner RUNNER, built otherwise
#
# It needs make and c99 (or the compiler given to make), and, to compare
# with ACL2, acl2 (ACL2 8.7) and python3.  It compares the runner's
# values with ACL2's on: the calls of checks/expected/facts.txt and the
# calls of checks/expected/edge.txt (value and no-value lines); the
# calls of runner/test/book.lisp, a book of stops; calls of functions of
# ACL2's library, run from its exported program text; and calls of the
# arithmetic primitives.  runner/test/gen.py writes the last three sets
# and ACL2 computes their values (runner/test/expect.lsp), as it does
# those of calls of the two functions of the prelude (the option -j),
# which are also given the calls on large integers whose values
# runner-fast/test/expected/large.txt records.  It then runs
# cases that concern the runner alone: deep recursion, deep nesting,
# large numbers, exhaustion of memory, text that is not in the
# format, and the prelude with and without definitions of its
# functions.  Last, it has the runner read and compile every definition of
# the library's program text and of each book that export/run.sh has
# exported.  It writes into build/runner/test/, prints one line for each
# set, and ends with "all runner tests passed" or "some runner tests
# failed".

T=build/runner/test
if [ $# -gt 0 ]; then
    R=$1
else
    R=build/runner/boymoo-run
    make -f runner/Makefile > /dev/null || exit 1
fi
mkdir -p $T
status=0
report() {
    if [ "$1" -eq 0 ]; then echo "ok $2"; else echo "FAIL $2"; status=1; fi
}

# The program text and statements of ACL2's library, which the exporter
# writes (README.md).
if [ ! -f build/export/library.program ] || [ ! -f build/export/library.statements ] ||
   [ ! -f build/export/ground-fns.lsp ]; then
    mkdir -p build/export
    names=$(sed -n 's/^(define [^ (][^ ]* (\([^ ]*\) .*/\1/p; s/^(define ([^()]*) (\([^ ]*\) .*/\1/p' spec/ground.txt |
                tr '\n' ' ')
    echo "(assign bx-ground-fns '($names))" > build/export/ground-fns.lsp
    sh export/book.sh :library || exit $?
fi
LIB="-p spec/ground.txt -p build/export/library.statements"
PROG=build/export/library.program

# check NAME ARGS...: runs the runner on NAME.terms, whose values must be
# NAME.expected, and on each line of NAME.none, which must stop with
# status 1, as at a call that has no value.
check() {
    name=$1
    shift
    "$R" "$@" < $T/$name.terms > $T/$name.out 2> $T/$name.err
    ok=$?
    [ $ok -eq 0 ] && cmp -s $T/$name.out $T/$name.expected
    ok=$?
    stops=0
    while read -r term; do
        echo "$term" | "$R" "$@" > /dev/null 2>> $T/$name.err
        if [ $? -eq 1 ]; then stops=$((stops + 1)); else ok=1; echo "   did not stop: $term"; fi
    done < $T/$name.none
    report $ok "$name: $(grep -c . < $T/$name.terms) values and $stops stops agree with ACL2"
}

# Splits ACL2's terms and values into the inputs of check.
expected() {
    : > $T/$1.none
    : > $T/$1.terms2
    : > $T/$1.expected
    paste $T/$1.terms $T/$1.values |
        awk -F '	' -v t=$T/$1 '$2 == "no value" { print $1 > (t ".none") }
                                $2 != "no value" { print $1 > (t ".terms2"); print $2 > (t ".expected") }'
    mv $T/$1.terms2 $T/$1.terms
}

# 1. The calls of checks/expected/facts.txt and edge.txt.
for t in facts edge; do
    python3 runner/test/split.py checks/expected/$t.txt $T/$t || exit 1
done
grep '^(package ' checks/expected/facts.txt > $T/facts.packages
check facts $LIB -p $T/facts.packages $PROG
check edge $LIB $PROG

# 2. ACL2 certifies and exports runner/test/book.lisp, and computes the
#    values of the generated calls.
rm -f $T/book.* $T/*.calls $T/*.values
cp runner/test/book.lisp $T/book.lisp
{
    echo '(ld "checks/version.lsp")'
    echo '(certify-book "build/runner/test/book" 0 nil)'
} | acl2 > $T/certify.log 2>&1
if [ $? -eq 3 ]; then
    echo "runner/test.sh stopped: $(sed -n 's/^version: //p' $T/certify.log)" >&2
    exit 3
fi
sh export/book.sh build/runner/test/book
B=build/export/books/build/runner/test/book
python3 runner/test/gen.py $T || exit 1
# The calls of the two functions of the prelude (README.md, "The
# prelude"): on integers at the edges of the runner's representations
# (2^29, 10^9, 2^32, 10^18, 2^64 and 2^128), on fractions and complex
# rationals, and on data that are not numbers; ash by up to 200 bits
# and, for an integer, by more bits than it has.
awk 'BEGIN {
    ni = split("0 1 -1 7 -7 536870911 -536870912 536870912 -536870913 999999999 1000000000 -1000000000 " \
               "4294967295 4294967296 -4294967296 999999999999999999 1000000000000000000 " \
               "18446744073709551615 -18446744073709551616 340282366920938463463374607431768211455 " \
               "-340282366920938463463374607431768211457", whole, " ")
    no = split("3/2|-3/2|7/3|#c(1 2)|#c(0 1)|#c(3/2 -1/2)|\"a\"|x|(1 . 2)|#\\a", odd, "|")
    ns = split("0 1 -1 2 -2 3 -3 29 30 31 32 33 -29 -30 -31 -32 -33 59 60 61 64 -64 89 90 91 -89 -90 -91 " \
               "200 -200", shift, " ")
    for (i = 1; i <= ni; i++) {
        for (j = 1; j <= ns; j++) print "(ash " whole[i] " " shift[j] ")"
        print "(ash " whole[i] " -536870912)"
        print "(ash " whole[i] " -100000000000000000000)"
        for (j = 1; j <= ni; j++) print "(binary-logxor " whole[i] " " whole[j] ")"
        for (j = 1; j <= no; j++) {
            print "(ash " whole[i] " " odd[j] ")"
            print "(binary-logxor " whole[i] " " odd[j] ")"
            print "(binary-logxor " odd[j] " " whole[i] ")"
        }
    }
    for (i = 1; i <= no; i++) {
        for (j = 1; j <= ns; j++) print "(ash " odd[i] " " shift[j] ")"
        for (j = 1; j <= no; j++) {
            print "(ash " odd[i] " " odd[j] ")"
            print "(binary-logxor " odd[i] " " odd[j] ")"
        }
    }
    print "(ash 0 536870911)"
}' > $T/prelude.calls
{
    echo '(in-package "ACL2")'
    echo '(ld "checks/version.lsp")'
    echo '(include-book "build/runner/test/book")'
    echo '(ld "checks/canon.lsp")'
    echo '(ld "runner/test/expect.lsp")'
    # Guard checking is set again before each set of calls: after the
    # errors of the calls of the book that have no value, ACL2 refuses
    # some calls in program mode that its top level, with guard checking
    # :none, computes.
    for s in book lib arith prelude; do
        echo '(set-guard-checking :none)'
        echo "(rt-expect \"$T/$s.calls\" \"$T/$s\" state)"
    done
    echo '(good-bye)'
} | acl2 > $T/expect.log 2>&1
for s in book lib arith prelude; do
    if [ -f $T/$s.values ]; then expected $s; else : > $T/$s.terms; : > $T/$s.none; fi
done
check book $LIB -p $B.statements $PROG $B.program
check lib $LIB $PROG
check arith $LIB $PROG

# The prelude.  A define line is in force in the place of a function of
# the prelude, so the prelude computes ash and binary-logxor only for
# program text that does not define them: the library's, less two lines.
# It is given the calls above, and then the calls of
# runner-fast/test/gen.awk on integers of up to 200 bits that are of
# those two functions, with the values that ACL2 gave for them.
grep -v -e '^(define COMMON-LISP::NIL (COMMON-LISP::ASH ' \
     -e '^(define COMMON-LISP::NIL (ACL2::BINARY-LOGXOR ' $PROG > $T/library.program
[ $(($(grep -c . < $PROG) - $(grep -c . < $T/library.program))) -eq 2 ]
report $? "the library's program text has one define line for each function of the prelude"
check prelude -j $LIB $T/library.program
: > $T/large.none
awk -v set=large -f runner-fast/test/gen.awk | paste - runner-fast/test/expected/large.txt |
    awk -F '	' -v t=$T/large '
        $1 ~ /^\((COMMON-LISP::ASH|ACL2::BINARY-LOGXOR) / {
            print $1 > (t ".terms"); print $2 > (t ".expected") }'
check large -j $LIB $T/library.program

# 3. Cases that concern the runner alone.  Each line names the case, the
#    status the runner must end with, and what it must print.
run() {   # run TERMFILE ARGS...: the status, then the output
    f=$1
    shift
    "$R" "$@" < $f > $T/case.out 2> $T/case.err
    echo $?
}
case_ok() {   # case_ok NAME STATUS WANTED-STATUS [EXPECTED-OUTPUT-FILE]
    if [ "$2" -ne "$3" ]; then
        report 1 "$1 (status $2, not $3: $(head -n 1 $T/case.err | cut -c 1-200))"
    elif [ $# -gt 3 ] && ! cmp -s $T/case.out "$4"; then
        report 1 "$1 (wrong output)"
    else
        report 0 "$1"
    fi
}
Q='COMMON-LISP::QUOTE'
echo "(ACL2::RT-DEEP ($Q 1000000))" > $T/case.in
echo 1000000 > $T/case.want
case_ok "a recursion a million calls deep" "$(run $T/case.in $LIB -p $B.statements $PROG $B.program)" 0 $T/case.want
awk -v q=$Q 'BEGIN { for (i = 0; i < 1000; i++) printf "(ACL2::BINARY-+ (%s 1) ", q
                     printf "(%s 0)", q; for (i = 0; i < 1000; i++) printf ")"; print "" }' > $T/case.in
echo 1000 > $T/case.want
case_ok "a term nested a thousand levels deep" "$(run $T/case.in $LIB $PROG)" 0 $T/case.want
awk -v q=$Q 'BEGIN { for (i = 0; i < 20000; i++) printf "(COMMON-LISP::CAR "
                     printf "(%s 0)", q; for (i = 0; i < 20000; i++) printf ")"; print "" }' > $T/case.in
case_ok "a term nested twenty thousand levels deep stops" "$(run $T/case.in $LIB $PROG)" 2
awk 'BEGIN { for (i = 0; i < 1000000; i++) printf "("; printf "1"
             for (i = 0; i < 1000000; i++) printf ")"; print "" }' > $T/case.want
{ printf '(%s ' $Q; tr -d '\n' < $T/case.want; echo ')'; } > $T/case.in
case_ok "a datum nested a million levels deep" "$(run $T/case.in $LIB $PROG)" 0 $T/case.want
awk 'BEGIN { printf "1"; for (i = 1; i < 1000000; i++) printf "0"; print "" }' > $T/big
N=$(cat $T/big)
{
    echo "($Q $N)"
    echo "(ACL2::BINARY-+ ($Q $N) ($Q 1))"
    echo "(ACL2::BINARY-* ($Q $N) ($Q 7))"
    echo "(ACL2::UNARY-/ ($Q $N))"
    echo "(COMMON-LISP::EQUAL (ACL2::BINARY-* (ACL2::UNARY-/ ($Q $N)) ($Q $N)) ($Q 1))"
    echo "(ACL2::BINARY-+ ($Q $N) (ACL2::UNARY-- ($Q $N)))"
    echo "(COMMON-LISP::< ($Q $N) (ACL2::BINARY-+ ($Q $N) ($Q 1/2)))"
} > $T/case.in
{
    echo "$N"
    echo "$N" | sed 's/0$/1/'
    echo "$N" | sed 's/^1/7/'
    echo "1/$N"
    echo COMMON-LISP::T
    echo 0
    echo COMMON-LISP::T
} > $T/case.want
case_ok "numbers of a million digits" "$(run $T/case.in $LIB $PROG)" 0 $T/case.want
echo "(ACL2::RT-DEEP ($Q 100000000))" > $T/case.in
case_ok "a recursion that exhausts memory stops" "$(run $T/case.in -m 64 $LIB -p $B.statements $PROG $B.program)" 3
echo "(ACL2::MAKE-LIST-AC ($Q 100000000) ($Q 1) ($Q COMMON-LISP::NIL))" > $T/case.in
case_ok "a list that exhausts memory stops" "$(run $T/case.in -m 64 $LIB $PROG)" 3
bad=0
for text in '(' '(ACL2::LEN' '#\4' '-0' '01' '2/4' '1/1' '#C(1 0)' '#c(1 2)' 'ACL2::CAR' \
            '|ACL2|::X' '"\41"' 'ACL2::|X|' '()' '(1 . (2))' '(1 . COMMON-LISP::NIL)' \
            '(1  2)' 'acl2::x' 'NO-SUCH-PACKAGE::X' 'ACL2::X' "($Q)" "($Q 1 2)" \
            "(COMMON-LISP::CAR ($Q 1) ($Q 2))" "((COMMON-LISP::LAMBDA (ACL2::X) ACL2::Y) ($Q 1))" \
            "((COMMON-LISP::LAMBDA (ACL2::X ACL2::X) ACL2::X) ($Q 1) ($Q 2))" "(7 ($Q 1))"; do
    printf '%s\n' "$text" > $T/case.in
    s=$(run $T/case.in $LIB $PROG)
    if [ "$s" -ne 2 ]; then bad=1; echo "   not refused: $text (status $s)"; fi
done
printf '(define COMMON-LISP::NIL (ACL2::F (ACL2::X) ACL2::X))' > $T/case.program
echo "($Q 1)" > $T/case.in
s1=$(run $T/case.in $LIB $T/case.program)
printf '(define COMMON-LISP::NIL (ACL2::F (ACL2::X) ACL2::Y))\n' > $T/case.program
echo "(ACL2::F ($Q 1))" > $T/case.in
s2=$(run $T/case.in $LIB $T/case.program)
printf '(define COMMON-LISP::NIL (COMMON-LISP::CAR (ACL2::X) ACL2::X))\n' > $T/case.program
s3=$(run $T/case.in $LIB $T/case.program)
[ $bad -eq 0 ] && [ "$s1" -eq 2 ] && [ "$s2" -eq 2 ] && [ "$s3" -eq 2 ]
report $? "text that is not in the format, and terms that are not terms, stop with status 2"
# The functions of the prelude are functions like any other.  Without -j
# they have no definition.  With it they are called from a term and from
# a definition, in the last position and not; a define line for one of
# them is in force in its place and the other stays; and a call with one
# argument is not a term.
printf '(define COMMON-LISP::NIL (ACL2::F (ACL2::X) (ACL2::BINARY-+ (COMMON-LISP::ASH ACL2::X (%s 2)) (ACL2::BINARY-LOGXOR ACL2::X (%s 1)))))\n' $Q $Q > $T/case.program
{
    echo "(COMMON-LISP::ASH ($Q 1) ($Q 3))"
    echo "(ACL2::F ($Q 5))"
} > $T/case.in
case_ok "without -j the functions of the prelude have no definition" "$(run $T/case.in $LIB $T/case.program)" 1
printf '8\n24\n' > $T/case.want
case_ok "with -j they are called from a term and from a definition" "$(run $T/case.in -j $LIB $T/case.program)" 0 $T/case.want
# By its definition (ash 0 c) is 0 for every c.  The Lisp under ACL2 does
# not shift by a count this large, and ACL2 aborts on the call.
echo "(COMMON-LISP::ASH ($Q 0) ($Q 100000000000000000000))" > $T/case0.in
echo 0 > $T/case.want
case_ok "with -j, ash of 0 by a count that ACL2 does not compute is 0" "$(run $T/case0.in -j $LIB $T/case.program)" 0 $T/case.want
printf '(define COMMON-LISP::NIL (COMMON-LISP::ASH (ACL2::I ACL2::C) (%s 77)))\n' $Q >> $T/case.program
printf '77\n81\n' > $T/case.want
case_ok "a define line is in force in the place of a function of the prelude" "$(run $T/case.in -j $LIB $T/case.program)" 0 $T/case.want
echo "(ACL2::BINARY-LOGXOR ($Q 1))" > $T/case.in
case_ok "a call of a function of the prelude with one argument stops" "$(run $T/case.in -j $LIB $T/case.program)" 2

# 4. Every definition of the library's program text, and of the program
#    text of each book that export/run.sh has exported, is read and
#    compiled (the option -l).
echo "($Q 1)" > $T/case.in
case_ok "every definition of the library compiles" "$(run $T/case.in -l $LIB $PROG)" 0
case_ok "every definition of the library compiles after the prelude" "$(run $T/case.in -l -j $LIB $PROG)" 0
if [ -f build/export/books.list ]; then
    n=0
    bad=0
    while read -r b; do
        f=build/export/books/$b
        [ -f $f.program ] || continue
        n=$((n + 1))
        s=$(run $T/case.in -l $LIB -p $f.statements $PROG $f.program)
        if [ "$s" -ne 0 ]; then bad=1; echo "   $b: $(head -n 1 $T/case.err | cut -c 1-200)"; fi
    done < build/export/books.list
    report $bad "every definition of the program text of the $n exported books compiles"
fi

if [ $status -eq 0 ]; then echo "all runner tests passed"; else echo "some runner tests failed"; fi
exit $status
