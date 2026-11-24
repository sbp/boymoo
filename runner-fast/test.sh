#!/bin/sh
# The tests of the fast runner.  Run from the root of the repository:
#
#     sh runner-fast/test.sh
#
# The reference runner is the judge: on every input below, the fast
# runner must give the same standard output and the same exit status.
# It builds build/runner-fast/boymoo-run-fast and, if it is not up to
# date, build/runner/boymoo-run, and it reads, as they stand, files that
# other commands of the repository write, which must have been run
# first:
#
#   - sh export/run.sh (or sh runner/test.sh): build/export/library.*;
#   - sh runner/test.sh: the cases of build/runner/test/ and the exported
#     book of runner/test/book.lisp, under build/export/books/;
#   - sh checker/build.sh: the checker's program text in build/checker/.
#
# It needs make, cc, cksum and the POSIX tools that runner/test.sh uses,
# and not ACL2.  It compares the two runners on: (a) the reference
# runner's own cases, those that runner/test.sh wrote, each line of a
# .none file run alone, and its cases of deep recursion, deep nesting,
# large numbers, exhaustion of memory, text that is not in the format and
# -l; (b) 20,000 calls of the arithmetic primitives; (c) the functions
# that the fast runner computes natively: 10,000 calls on which the
# definitions finish, run three ways, by the native forms, with
# BOYMOO_FAST_NATIVE=0, and on the reference runner, and 4,000 on large
# integers, on which they do not, whose values must be those that ACL2
# gave, as must those of 12 calls of functions of the library that loop
# over the native functions while memory is collected; and it requires
# that all eleven native forms be installed for the library's program
# text; (d) the checker, on every case of checker/cases/ and
# checker-js/cases/; (e) a recursion ten million calls deep, which goes
# past the fast runner's C stack and is finished by its interpreter.
#
# runner-fast/test/gen.awk writes the calls of (b) and (c), the same on
# every run.  ACL2's values for the 4,000 calls and the 12 are the files
# large.txt and loop.txt of runner-fast/test/expected/, the value of each
# call on a line, which sh runner-fast/test/record.sh records, with ACL2;
# cksum.txt, beside them, holds what cksum prints for the calls that were
# recorded, and the calls written here must give the same.
#
# It writes into build/runner-fast/test/, with a cache of compiled code of
# its own there, prints one line for each set, and ends with "all fast
# runner tests passed" or "some fast runner tests failed".

F=build/runner-fast/boymoo-run-fast
R=build/runner/boymoo-run
T=build/runner-fast/test
make -f runner-fast/Makefile > /dev/null || exit 1
make -f runner/Makefile > /dev/null || exit 1
BOYMOO_FAST_CACHE=$T/cache
export BOYMOO_FAST_CACHE
unset BOYMOO_FAST BOYMOO_FAST_NATIVE BOYMOO_FAST_NOINLINE BOYMOO_FAST_VERBOSE BOYMOO_FAST_KEEP \
      BOYMOO_FAST_NAMES BOYMOO_FAST_ROOT
mkdir -p $T

RT=build/runner/test
B=build/export/books/build/runner/test/book
for f in build/export/library.program build/export/library.statements \
         $RT/facts.terms $RT/facts.none $RT/facts.packages $RT/edge.terms $RT/edge.none \
         $RT/book.terms $RT/book.none $RT/lib.terms $RT/lib.none $RT/arith.terms $RT/arith.none \
         $B.statements $B.program \
         build/checker/checker.statements build/checker/ground.program build/checker/checker.program; do
    if [ ! -f $f ]; then
        echo "runner-fast/test.sh: no $f; run sh runner/test.sh and sh checker/build.sh first" >&2
        exit 1
    fi
done
LIB="-p spec/ground.txt -p build/export/library.statements"
PROG=build/export/library.program

status=0
report() {
    if [ "$1" -eq 0 ]; then echo "ok $2"; else echo "FAIL $2"; status=1; fi
}

# same INPUT ARGS...: runs both runners on INPUT; 0 if they give the same
# output and status, which is left in $rs.
same() {
    in=$1
    shift
    "$R" "$@" < "$in" > $T/ref.out 2> $T/ref.err
    rs=$?
    "$F" "$@" < "$in" > $T/fast.out 2> $T/fast.err
    fs=$?
    if [ $rs -eq $fs ] && cmp -s $T/ref.out $T/fast.out; then
        return 0
    fi
    echo "   different on $in: status $rs and $fs; $(head -n 1 $T/fast.err | cut -c 1-200)"
    return 1
}

# (a) The reference runner's cases.  set_ NAME ARGS...: NAME.terms
# whole, then each line of NAME.none alone.
set_() {
    name=$1
    shift
    same $RT/$name.terms "$@"
    ok=$?
    n=0
    while read -r term; do
        printf '%s\n' "$term" > $T/one.in
        same $T/one.in "$@" || { ok=1; echo "   on: $term"; }
        n=$((n + 1))
    done < $RT/$name.none
    report $ok "$name: $name.terms ($(grep -c . < $RT/$name.terms) lines) whole and $name.none ($n lines) each line alone, the same on both runners"
}
set_ facts $LIB -p $RT/facts.packages $PROG
set_ edge $LIB $PROG
set_ book $LIB -p $B.statements $PROG $B.program
set_ lib $LIB $PROG
set_ arith $LIB $PROG

# case NAME ARGS...: both runners on $T/case.in.
case_() {
    name=$1
    shift
    same $T/case.in "$@"
    report $? "$name: the same on both runners (status $rs)"
}
Q='COMMON-LISP::QUOTE'
echo "(ACL2::RT-DEEP ($Q 1000000))" > $T/case.in
case_ "a recursion a million calls deep" $LIB -p $B.statements $PROG $B.program
awk -v q=$Q 'BEGIN { for (i = 0; i < 1000; i++) printf "(ACL2::BINARY-+ (%s 1) ", q
                     printf "(%s 0)", q; for (i = 0; i < 1000; i++) printf ")"; print "" }' > $T/case.in
case_ "a term nested a thousand levels deep" $LIB $PROG
awk -v q=$Q 'BEGIN { for (i = 0; i < 20000; i++) printf "(COMMON-LISP::CAR "
                     printf "(%s 0)", q; for (i = 0; i < 20000; i++) printf ")"; print "" }' > $T/case.in
case_ "a term nested twenty thousand levels deep" $LIB $PROG
awk -v q=$Q 'BEGIN { printf "(%s ", q; for (i = 0; i < 1000000; i++) printf "("; printf "1"
                     for (i = 0; i < 1000000; i++) printf ")"; print ")" }' > $T/case.in
case_ "a datum nested a million levels deep" $LIB $PROG
N=$(awk 'BEGIN { printf "1"; for (i = 1; i < 1000000; i++) printf "0"; print "" }')
{
    echo "($Q $N)"
    echo "(ACL2::BINARY-+ ($Q $N) ($Q 1))"
    echo "(ACL2::BINARY-* ($Q $N) ($Q 7))"
    echo "(ACL2::UNARY-/ ($Q $N))"
    echo "(COMMON-LISP::EQUAL (ACL2::BINARY-* (ACL2::UNARY-/ ($Q $N)) ($Q $N)) ($Q 1))"
    echo "(ACL2::BINARY-+ ($Q $N) (ACL2::UNARY-- ($Q $N)))"
    echo "(COMMON-LISP::< ($Q $N) (ACL2::BINARY-+ ($Q $N) ($Q 1/2)))"
} > $T/case.in
case_ "numbers of a million digits" $LIB $PROG
echo "(ACL2::RT-DEEP ($Q 100000000))" > $T/case.in
case_ "a recursion that exhausts memory under -m 64" -m 64 $LIB -p $B.statements $PROG $B.program
echo "(ACL2::MAKE-LIST-AC ($Q 100000000) ($Q 1) ($Q COMMON-LISP::NIL))" > $T/case.in
case_ "a list that exhausts memory under -m 64" -m 64 $LIB $PROG
ok=0
n=0
for text in '(' '(ACL2::LEN' '#\4' '-0' '01' '2/4' '1/1' '#C(1 0)' '#c(1 2)' 'ACL2::CAR' \
            '|ACL2|::X' '"\41"' 'ACL2::|X|' '()' '(1 . (2))' '(1 . COMMON-LISP::NIL)' \
            '(1  2)' 'acl2::x' 'NO-SUCH-PACKAGE::X' 'ACL2::X' "($Q)" "($Q 1 2)" \
            "(COMMON-LISP::CAR ($Q 1) ($Q 2))" "((COMMON-LISP::LAMBDA (ACL2::X) ACL2::Y) ($Q 1))" \
            "((COMMON-LISP::LAMBDA (ACL2::X ACL2::X) ACL2::X) ($Q 1) ($Q 2))" "(7 ($Q 1))"; do
    printf '%s\n' "$text" > $T/case.in
    same $T/case.in $LIB $PROG || { ok=1; echo "   on: $text"; }
    n=$((n + 1))
done
report $ok "$n texts that are not in the format or terms that are not terms: the same on both runners"
printf '(define COMMON-LISP::NIL (ACL2::F (ACL2::X) ACL2::X))' > $T/case.program
echo "($Q 1)" > $T/case.in
case_ "program text with no newline at its end" $LIB $T/case.program
printf '(define COMMON-LISP::NIL (ACL2::F (ACL2::X) ACL2::Y))\n' > $T/case.program
printf "($Q 5)\n(ACL2::F ($Q 1))\n($Q 6)\n" > $T/case.in
case_ "a variable not bound in a definition, called after a value" $LIB $T/case.program
printf '(define COMMON-LISP::NIL (COMMON-LISP::CAR (ACL2::X) ACL2::X))\n' > $T/case.program
case_ "a definition of a primitive" $LIB $T/case.program
echo "($Q 1)" > $T/case.in
case_ "-l: every definition of the library" -l $LIB $PROG

# (b) The arithmetic primitives near the edges of the paths in machine
#     words.  Every call has a value, so the status must be 0.
awk -v set=arith -f runner-fast/test/gen.awk > $T/arith.in || exit 1
same $T/arith.in $LIB $PROG && [ $rs -eq 0 ]
report $? "$(grep -c . < $T/arith.in) calls of the arithmetic primitives: the same on both runners (status $rs)"

# (c) The native functions.  First, 10,000 calls on which the
#     definitions finish quickly, three ways: native, by the compiled
#     definitions (BOYMOO_FAST_NATIVE=0), and on the reference runner.
#     Every call has a value, so the status must be 0.
awk -v set=natives -f runner-fast/test/gen.awk > $T/natives.in || exit 1
BOYMOO_FAST_VERBOSE=1 "$F" $LIB $PROG < $T/natives.in > $T/natives.native 2> $T/natives.native.err
s1=$?
BOYMOO_FAST_NATIVE=0 "$F" $LIB $PROG < $T/natives.in > $T/natives.definition 2> $T/natives.definition.err
s2=$?
"$R" $LIB $PROG < $T/natives.in > $T/natives.reference 2> $T/natives.reference.err
s3=$?
[ $s3 -eq 0 ] && [ $s1 -eq $s3 ] && [ $s2 -eq $s3 ] && cmp -s $T/natives.native $T/natives.reference &&
    cmp -s $T/natives.definition $T/natives.reference
report $? "$(grep -c . < $T/natives.in) calls of the natively computed functions: the same native, by the definitions and on the reference (status $s3)"

# recorded NAME: 0 if the calls of $T/NAME.in are those whose values
# runner-fast/test/expected/NAME.txt records: cksum must print for them
# what it printed when the values were recorded.
E=runner-fast/test/expected
recorded() {
    [ "$1 $(cksum < $T/$1.in)" = "$(grep "^$1 " $E/cksum.txt)" ] && return 0
    echo "   the calls of the set $1 are not those whose values are recorded in $E/$1.txt"
    return 1
}

#     Then 4,000 calls of the quotient, the bitwise functions and ash on
#     large integers, on which the definitions do not finish, so that
#     neither they nor the reference runner can be run: the native values
#     must be those that ACL2 gave, and each must be equal, by the
#     primitive equal, to the integer read from its text, which holds only
#     when the native form makes the one representation of its value.
awk -v set=large -f runner-fast/test/gen.awk > $T/large.in || exit 1
n=$(grep -c . < $T/large.in)
"$F" $LIB $PROG < $T/large.in > $T/large.out 2> $T/large.err
s1=$?
recorded large && [ $s1 -eq 0 ] && cmp -s $T/large.out $E/large.txt
report $? "$n calls of the quotient, the bitwise functions and ash on large integers: the values that ACL2 gave (status $s1)"
paste -d ' ' $T/large.in $E/large.txt |
    awk '{ v = $NF; $NF = ""; sub(/ $/, ""); print "(COMMON-LISP::EQUAL " $0 " (COMMON-LISP::QUOTE " v "))" }' > $T/equal.in
"$F" $LIB $PROG < $T/equal.in > $T/equal.out 2> $T/equal.err
s1=$?
[ $s1 -eq 0 ] && [ "$(grep -c -v '^COMMON-LISP::T$' < $T/equal.out)" -eq 0 ] &&
    [ "$(grep -c . < $T/equal.out)" -eq "$n" ]
report $? "the same $n values, each equal to the integer of its text (status $s1)"

#     Then 12 calls of three functions of the library that call a native
#     function again and again while they hold data of their own, and make
#     so many integers and strings that memory is collected many times
#     inside the native functions: a native function must leave every
#     datum of its callers where the collector finds it.  The values must
#     be those that ACL2 gave.
awk -v set=loop -f runner-fast/test/gen.awk > $T/loop.in || exit 1
"$F" $LIB $PROG < $T/loop.in > $T/loop.out 2> $T/loop.err
s1=$?
recorded loop && [ $s1 -eq 0 ] && cmp -s $T/loop.out $E/loop.txt
report $? "$(grep -c . < $T/loop.in) calls of functions of the library that loop over native functions, with memory collected inside them: the values that ACL2 gave (status $s1)"

#     Last, every native form must be installed for the library's program
#     text: under BOYMOO_FAST_VERBOSE=1 the fast runner prints, for each
#     function of its table, the fingerprint of the definition found, the
#     one expected, and whether the native form is used.
ok=0
for name in COMMON-LISP::LENGTH COMMON-LISP::CHAR COMMON-LISP::SUBSEQ ACL2::STRING-APPEND \
            ACL2::NONNEGATIVE-INTEGER-QUOTIENT ACL2::BINARY-LOGAND ACL2::BINARY-LOGIOR \
            ACL2::BINARY-LOGXOR ACL2::BINARY-LOGEQV COMMON-LISP::STRING\< COMMON-LISP::ASH; do
    prints=$(sed -n "s/^boymoo-run-fast: $name: fingerprint \([0-9a-f]*\), expected \([0-9a-f]*\): native\$/\1 \2/p" \
                 $T/natives.native.err)
    if [ -z "$prints" ] || [ "${prints% *}" != "${prints#* }" ]; then
        ok=1
        echo "   not native: $name: $(grep "^boymoo-run-fast: $name:" $T/natives.native.err)"
    fi
done
report $ok "the eleven native functions are installed for build/export/library.program"

# (d) The checker, on every case, as checker/check.sh runs it.
. checker/quote.sh
quote spec/ground.txt > $T/ground.q
CHECK="-p spec/ground.txt -p build/checker/checker.statements build/checker/ground.program build/checker/checker.program"
input() { if [ -f "$1" ]; then echo "$1"; else echo /dev/null; fi; }
n=0
ok=0
for d in checker/cases/*/ checker-js/cases/*/; do
    {
        printf '(BOYMOO::CHECK-FOUR '
        cat $T/ground.q
        printf ' '
        quote "$(input ${d}library.txt)"
        printf ' '
        quote "$(input ${d}statements.txt)"
        printf ' '
        quote "$(input ${d}proofs.txt)"
        printf ' '
        quote "$(input ${d}library-proofs.txt)"
        printf ')\n'
    } > $T/check.in
    same $T/check.in $CHECK || { ok=1; echo "   on: $d"; }
    n=$((n + 1))
done
report $ok "the checker on $n cases of checker/cases/ and checker-js/cases/: the same on both runners"

# (e) A recursion deeper than the fast runner's C stack holds.
echo "(ACL2::RT-DEEP ($Q 10000000))" > $T/case.in
echo 10000000 > $T/case.want
same $T/case.in $LIB -p $B.statements $PROG $B.program && cmp -s $T/fast.out $T/case.want
report $? "a recursion ten million calls deep: 10000000 on both runners"

if [ $status -eq 0 ]; then echo "all fast runner tests passed"; else echo "some fast runner tests failed"; fi
exit $status
