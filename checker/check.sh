#!/bin/sh
# The checker of spec/logic.md, run on the reference runner.  From the root
# of the repository:
#
#     sh checker/check.sh LIBRARY STATEMENTS PROOFS
#
# Each argument is a file, which may be empty.  The first line of the
# output is the verdict of spec/formats.md, section 9; a second line, which
# nothing may be concluded from, says in a few words what failed.  The exit
# status is 0 when the checker gave a verdict, and otherwise that of the
# step that failed.
#
# It builds what it needs: the runner, with runner/Makefile, and the
# checker, with checker/build.sh, which needs ACL2.  Then it writes the
# bytes of spec/ground.txt and of the three inputs as four strings in the
# text of spec/formats.md, section 2, and has the runner compute the
# checker's function CHECK on them from the checker's program text.
#
# With RUNNER set in the environment, it uses that runner and builds none.

if [ $# -ne 3 ]; then
    echo "usage: sh checker/check.sh LIBRARY STATEMENTS PROOFS" >&2
    exit 2
fi
for f in "$1" "$2" "$3"; do
    if [ ! -f "$f" ]; then
        echo "checker/check.sh: no file $f" >&2
        exit 2
    fi
done

if [ -z "$RUNNER" ]; then
    RUNNER=build/runner/boymoo-run
    make -s -f runner/Makefile > /dev/null || exit 2
fi
sh checker/build.sh || exit 2

tmp=build/checker/tmp.$$
mkdir -p "$tmp" || exit 2
trap 'rm -rf "$tmp"' 0
. checker/quote.sh
quote spec/ground.txt > "$tmp/ground"
quote "$1" > "$tmp/library"
quote "$2" > "$tmp/statements"
quote "$3" > "$tmp/proofs"
run_check "$tmp/ground" "$tmp/library" "$tmp/statements" "$tmp/proofs" > "$tmp/out"
status=$?
sed '2{/^$/d;}' "$tmp/out"
exit $status
