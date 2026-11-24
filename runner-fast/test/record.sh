#!/bin/sh
# Records ACL2's values for two sets of the fast runner's tests, of which
# the reference runner cannot be the judge, because the definitions do
# not finish on them: the sets large and loop of
# runner-fast/test/gen.awk.  Run from the root of the repository:
#
#     sh runner-fast/test/record.sh
#
# It needs acl2 (ACL2 8.7), awk, cksum and the POSIX tools that
# checks/run.sh uses, and stops at once under any other version of ACL2
# (checks/version.lsp).  It has gen.awk write the calls of each set, and
# ACL2 read them, write each back in the text of spec/formats.md, and
# evaluate each as its top level does, with guard checking :none, the
# setting of a runner (runner-fast/test/record.lsp).  For a set to be
# recorded, what ACL2 writes back must be the calls byte for byte, so
# that ACL2 took each line for the term that a runner takes it for, and
# every call must have a value.  It writes into build/runner-fast/record/
# and then records, in runner-fast/test/expected/:
#
#   - large.txt and loop.txt: the value of each call of the set, one a
#     line, in the order of the calls, which is what a runner prints for
#     the calls;
#   - cksum.txt: for each set a line with its name and what cksum prints
#     for its calls, the checksum and the number of bytes, by which
#     runner-fast/test.sh knows that the awk it runs under writes the
#     calls whose values are recorded.
#
# sh runner-fast/test.sh reads the three files and needs no ACL2.

T=build/runner-fast/record
E=runner-fast/test/expected
mkdir -p $T $E || exit 1
rm -f $T/*.terms $T/*.read $T/*.values $T/cksum.txt
for s in large loop; do
    awk -v set=$s -f runner-fast/test/gen.awk > $T/$s.terms || exit 1
done
{
    echo '(in-package "ACL2")'
    echo '(ld "checks/version.lsp")'
    echo '(ld "checks/canon.lsp")'
    echo '(ld "runner-fast/test/record.lsp")'
    for s in large loop; do
        echo '(set-guard-checking :none)'
        echo "(rf-record \"$T/$s.terms\" \"$T/$s\" state)"
    done
    echo '(good-bye)'
} | acl2 > $T/record.log 2>&1
if [ $? -eq 3 ]; then
    echo "runner-fast/test/record.sh stopped: $(sed -n 's/^version: //p' $T/record.log)" >&2
    exit 3
fi

status=0
for s in large loop; do
    n=$(grep -c . < $T/$s.terms)
    if cmp -s $T/$s.terms $T/$s.read && [ "$(grep -c . < $T/$s.values)" -eq "$n" ] &&
       ! grep -q '^no value$' $T/$s.values; then
        echo "$s $(cksum < $T/$s.terms)" >> $T/cksum.txt
        echo "ok $s: ACL2 read the $n calls as they are written and gave a value for each"
    else
        echo "FAIL $s: ACL2 did not read the $n calls as they are written, or gave no value for one ($T/record.log)"
        status=1
    fi
done
if [ $status -eq 0 ]; then
    cp $T/large.values $E/large.txt && cp $T/loop.values $E/loop.txt && cp $T/cksum.txt $E/cksum.txt || exit 1
    echo "recorded $E/large.txt, $E/loop.txt and $E/cksum.txt"
else
    echo "nothing recorded"
fi
exit $status
