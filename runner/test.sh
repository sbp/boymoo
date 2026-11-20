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
# and ACL2 computes their values (runner/test/expect.lsp).  It then runs
# cases that concern the runner alone: deep recursion, deep nesting,
# large numbers, exhaustion of memory and text that is not in the
# format.  Last, it has the runner read and compile every definition of
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
    for s in book lib arith; do
        echo '(set-guard-checking :none)'
        echo "(rt-expect \"$T/$s.calls\" \"$T/$s\" state)"
    done
    echo '(good-bye)'
} | acl2 > $T/expect.log 2>&1
for s in book lib arith; do
    if [ -f $T/$s.values ]; then expected $s; else : > $T/$s.terms; : > $T/$s.none; fi
done
check book $LIB -p $B.statements $PROG $B.program
check lib $LIB $PROG
check arith $LIB $PROG

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

# 4. Every definition of the library's program text, and of the program
#    text of each book that export/run.sh has exported, is read and
#    compiled (the option -l).
echo "($Q 1)" > $T/case.in
case_ok "every definition of the library compiles" "$(run $T/case.in -l $LIB $PROG)" 0
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
