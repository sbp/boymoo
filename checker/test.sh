#!/bin/sh
# The tests of the checker, from the root of the repository:
#
#     sh checker/test.sh
#
# It builds the runner and the checker, and then runs on the runner:
#
#   - spec/example, which must give accepted;
#   - every case of checker/cases/, which must give the first line of its
#     verdict.txt;
#   - the tests that the checker is written in ACL2 Core: every function
#     called in the define lines of its exported statements is a primitive,
#     a function of the ground theory or one of its own (checker/closed.py);
#     and its own statements, with an empty library and a skip for each
#     obligation, give a provisional verdict;
#
# and computes each of those verdicts again inside ACL2, with the same
# functions, which must give the same line.  It prints a line for each set
# and a last line that says whether all passed.  It writes what it ran and
# what each gave to build/checker/test/.  It needs acl2, python3, and the
# POSIX tools.

if [ -z "$RUNNER" ]; then
    RUNNER=build/runner/boymoo-run
    make -s -f runner/Makefile > /dev/null || exit 2
fi
sh checker/build.sh || exit 2
. checker/quote.sh

t=build/checker/test
rm -rf "$t"
mkdir -p "$t/q"
: > "$t/empty"
quote spec/ground.txt > "$t/q/ground"
: > "$t/list"
failed=0
tab=$(printf '\t')

# Runs the checker on the runner on a case NAME with inputs LIBRARY,
# STATEMENTS, PROOFS and optional LIBRARY-PROOFS. It records the verdict
# in $t/runner and the inputs in $t/list for ACL2 and prints the verdict.
run() {
    quote "$2" > "$t/q/library"
    quote "$3" > "$t/q/statements"
    quote "$4" > "$t/q/proofs"
    quote "${5:-$t/empty}" > "$t/q/library-proofs"
    v=$(run_check "$t/q/ground" "$t/q/library" "$t/q/statements" "$t/q/proofs" \
            "$t/q/library-proofs" | sed -n 1p)
    echo "$1$tab$v" >> "$t/runner"
    echo "$1 $2 $3 $4 ${5:-$t/empty}" >> "$t/list"
    echo "$v"
}

input() {
    if [ -f "$1" ]; then echo "$1"; else echo "$t/empty"; fi
}

# spec/example
v=$(run example "$t/empty" spec/example/statements.txt spec/example/proofs.txt)
if [ "$v" = accepted ]; then
    echo "spec/example: accepted"
else
    echo "spec/example: FAILED, $v"
    failed=1
fi

# The cases
n=0
bad=0
for d in checker/cases/*/; do
    name=$(basename "$d")
    expected=$(sed -n 1p "$d/verdict.txt")
    v=$(run "$name" "$(input "$d/library.txt")" "$(input "$d/statements.txt")" \
            "$(input "$d/proofs.txt")" "$(input "$d/library-proofs.txt")")
    n=$((n + 1))
    if [ "$v" != "$expected" ]; then
        echo "  case $name: expected \"$expected\", gave \"$v\""
        bad=$((bad + 1))
    fi
done
if [ $bad -eq 0 ]; then
    echo "checker/cases: all $n cases gave their verdict"
else
    echo "checker/cases: FAILED, $bad of $n cases did not give their verdict"
    failed=1
fi

# The checker in ACL2 Core
statements=build/checker/checker.statements
if closed=$(python3 checker/closed.py spec/ground.txt "$statements"); then
    echo "checker/closed.py: $closed"
else
    echo "checker/closed.py: FAILED, $closed"
    failed=1
fi
python3 checker/skips.py "$t/empty" "$statements" > "$t/self.proofs"
v=$(run self "$t/empty" "$statements" "$t/self.proofs")
skips=$(grep -c '' "$t/self.proofs")
if [ "$v" = "provisional skipped $skips assumed 0 given-definitions 0 given-facts 0" ]; then
    echo "the checker on its own statements: $v"
else
    echo "the checker on its own statements: FAILED, $v"
    failed=1
fi

# The same verdicts computed inside ACL2
sh checker/acl2-check.sh < "$t/list" > "$t/acl2"
if cmp -s "$t/runner" "$t/acl2"; then
    echo "ACL2: the same verdict on all $(grep -c '' "$t/list") inputs"
else
    echo "ACL2: FAILED, the verdicts differ:"
    diff "$t/runner" "$t/acl2" | sed 's/^/  /' | head -20
    failed=1
fi

if [ $failed -eq 0 ]; then
    echo "all checker tests passed"
else
    echo "some checker tests FAILED"
    exit 1
fi
