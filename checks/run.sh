#!/bin/sh
# The checks of this repository.  Run from the root of the repository:
#
#     sh checks/run.sh
#
# It needs acl2 (ACL2 8.6, with its distributed books), python3 and the
# usual POSIX tools on the PATH.  It writes into build/ and prints one
# line for each check, "ok" or "FAIL", and then "all checks passed" or
# "some checks failed".

status=0
mkdir -p build
rm -f build/ground.txt build/facts.txt

report() {
    if [ "$1" -eq 0 ]; then echo "ok $2"; else echo "FAIL $2"; status=1; fi
}

# 1. The ground theory is what ACL2 holds, and ACL2 proves every fact
#    of it that is not one of ACL2's axioms.
acl2 < checks/ground.lsp > build/ground.log 2>&1
cmp -s build/ground.txt spec/ground.txt
report $? "spec/ground.txt is the ground theory that ACL2 writes"
grep -a 'ground: ' build/ground.log | sed 's/^.*ground: /   ground: /'

# 2. What ACL2 says on the points where the specification speaks of it.
#    First ACL2 certifies two small books, which give it a package that
#    it keeps hidden.
rm -f build/hidden.* build/outer.*
cp checks/hidden.lisp build/hidden.lisp
cp checks/outer.lisp build/outer.lisp
acl2 < checks/hidden.lsp > build/hidden.log 2>&1
acl2 < checks/outer.lsp > build/outer.log 2>&1
[ -f build/hidden.cert ] && [ -f build/outer.cert ]
report $? "ACL2 certifies the two books of the hidden package"
acl2 < checks/facts.lsp > build/facts.log 2>&1
cmp -s build/facts.txt checks/expected/facts.txt
report $? "checks/expected/facts.txt is what ACL2 says"

# 2a. What ACL2 says on each entry of EDGE-CASES.md.  ACL2 certifies a
#     book that gives it a symbol of the hidden package; a second book is
#     copied and never certified.
rm -f build/edge.txt build/edge-hidden.* build/edge-false.*
cp checks/edge-hidden.lisp build/edge-hidden.lisp
cp checks/edge-false.lisp build/edge-false.lisp
acl2 < checks/edge-hidden.lsp > build/edge-hidden.log 2>&1
[ -f build/edge-hidden.cert ]
report $? "ACL2 certifies the book of a symbol of the hidden package"
acl2 < checks/edge.lsp > build/edge.log 2>&1
cmp -s build/edge.txt checks/expected/edge.txt
report $? "checks/expected/edge.txt is what ACL2 says on each entry of EDGE-CASES.md"

# 3. The files in the formats of spec/formats.md are read by a reader
#    written from that document, and written back unchanged.
python3 checks/reader.py spec/ground.txt checks/expected/facts.txt \
    checks/expected/edge.txt \
    spec/example/statements.txt spec/example/proofs.txt > build/reader.txt
report $? "the reader reads the files of the repository"
sed 's/^/   /' build/reader.txt

# 4. The counts that the documents give.
count() { grep -a -c "$1" spec/ground.txt; }
[ "$(count '^(package ')" = 5 ] && [ "$(count '^(specials ')" = 1 ] &&
    [ "$(count '^(primitive ')" = 32 ] &&
    [ "$(count '^(define ')" = 36 ] && [ "$(count '^(clause "')" = 41 ] &&
    [ "$(count '^(clause [A-Z]')" = 80 ]
report $? "the ground theory has 5 packages, 1 list of specials, 32 primitives, 36 definitions, 41 and 80 clauses"
[ "$(grep -a -c '^(event ' checks/expected/facts.txt)" = 41 ]
report $? "ACL2 lists 41 kinds of event"
[ "$(grep -a -c '^(value \|^(no-value ' checks/expected/facts.txt)" = 157 ]
report $? "ACL2 gives its value for 157 calls of the primitives"

# 5. Every fact of the ground theory is named in spec/logic.md.
missing=0
for name in $(sed -n 's/^(clause "\([^"]*\)".*/"\1"/p; s/^(clause ACL2::\([^ ]*\) .*/\1/p' spec/ground.txt |
                  tr 'ABCDEFGHIJKLMNOPQRSTUVWXYZ' 'abcdefghijklmnopqrstuvwxyz'); do
    grep -q -F -e "\`$name\`" spec/logic.md || { echo "   not named: $name"; missing=1; }
done
report $missing "every fact of the ground theory is named in spec/logic.md"

# 6. spec/logic.md lists the definitions of the ground theory in the
#    order of the file.
defs=$(sed -n 's/^(define [^ (][^ ]* (\([^ ]*\) .*/\1/p; s/^(define ([^()]*) (\([^ ]*\) .*/\1/p' spec/ground.txt | sed 's/.*:://' |
           tr 'ABCDEFGHIJKLMNOPQRSTUVWXYZ' 'abcdefghijklmnopqrstuvwxyz' |
           sed 's/.*/`&`/' | paste -sd, - | sed 's/,/, /g')
grep -q -F -e "$defs" spec/logic.md
report $? "spec/logic.md lists the definitions of the ground theory in order"

if [ $status -eq 0 ]; then echo "all checks passed"; else echo "some checks failed"; fi
exit $status
