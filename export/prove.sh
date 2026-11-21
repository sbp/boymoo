#!/bin/sh
# Runs every proof about the exporter of PLAN.md, step 4b.  Run from the
# root of the repository:
#
#     sh export/prove.sh
#
# It needs acl2 (ACL2 8.7 with its distributed books, certified),
# timeout and the usual POSIX tools on the PATH, and stops at once, with
# status 3, under any other version of ACL2 (checks/version.lsp).  It
# has export/certify.sh certify the printer and the core, then runs the
# five sets of proofs in export/proofs/, one after the other, each of
# which certifies its books in build/export/acl2/, refuses a certificate
# with a skipped proof, an added axiom or a trust tag, and tests the
# hypotheses of its theorems on ACL2's worlds:
#
#     round-trip    the printer and the checker's reader
#     guards        the guards of the core, verified, and the guards of
#                   its three entry functions evaluated on ACL2's worlds
#     structure     completeness without repeats, and order
#     well-formed   the lines are statements and program text of the format
#     faithful      each line says what ACL2's world holds
#
# No set needs another's books.  The guards set certifies its books
# afresh each time (export/certify.sh --fresh-guards).
#
# It prints one line for each set and a last line that says whether all
# passed, and exits with status 0 only then.  What each set printed is
# in build/export/prove-NAME.out, and its logs are in build/export/acl2/.

mkdir -p build/export
start=$(date +%s)

# ACL2 loads checks/version.lsp, which ends it with status 3 under any
# version but the one it names.  export/certify.sh runs ACL2 only for a
# book that has changed, so the version is checked here first.
echo '(ld "checks/version.lsp")' | timeout 600 acl2 > build/export/prove-version.log 2>&1
if [ $? -eq 3 ]; then
    echo "export/prove.sh stopped: $(sed -n 's/^version: //p' build/export/prove-version.log)" >&2
    exit 3
fi

sh export/certify.sh
status=$?
if [ $status -eq 3 ]; then
    exit 3
elif [ $status -ne 0 ]; then
    echo 'export/certify.sh failed; no proof was run'
    echo 'some proofs failed'
    exit 1
fi

failed=0
for set in round-trip guards structure well-formed faithful; do
    out=build/export/prove-$set.out
    begin=$(date +%s)
    sh "export/proofs/$set.sh" > "$out" 2>&1
    status=$?
    seconds=$(( $(date +%s) - begin ))
    if [ $status -eq 0 ]; then
        echo "$set: $(tail -n 1 "$out"), in $seconds seconds"
    else
        echo "$set: failed with status $status in $seconds seconds; see $out"
        failed=1
    fi
done

if [ $failed -eq 0 ]; then
    echo "all proofs passed, in $(( $(date +%s) - start )) seconds"
    exit 0
fi
echo 'some proofs failed'
exit 1
