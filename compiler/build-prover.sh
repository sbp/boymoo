# Build the compiled prover from the repository root after prover/build-all.sh.
set -eu
export LC_ALL=C

fail() {
    printf 'compiler/build-prover.sh: %s\n' "$*" >&2
    exit 2
}

limit=${PROVER_HEAP_LIMIT:-1024}
case $limit in ''|*[!0-9]*|0*) fail 'PROVER_HEAP_LIMIT must be an integer from 1 to 4096' ;; esac
[ "${#limit}" -le 4 ] && [ "$limit" -le 4096 ] ||
    fail 'PROVER_HEAP_LIMIT must be an integer from 1 to 4096'

driver=build/prover/driver
exported=$driver/export/driver
book=$driver/acl2/prover-entry
work=build/compiler/prover-build
entry=BOYMOO-PROVER::PROVER-ENTRY
mkdir -p "$work/tmp"
TMPDIR=$PWD/$work/tmp
export TMPDIR
mkdir "$work/lock" || fail 'a compiled prover build is already running'
trap 'rm -rf "$work/lock"; rm -f "$work/prover.tmp"' 0
trap 'exit 2' HUP INT TERM

sh prover/driver/build.sh
if ! cmp -s compiler/prover-entry.lisp "$book.lisp" ||
   [ ! -s "$book.cert" ] || [ "$driver/acl2/driver.cert" -nt "$book.cert" ]; then
    cp compiler/prover-entry.lisp "$book.lisp"
    rm -f "$book.cert"
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
        printf '%s\n' '(ld "build/prover/acl2/package.lsp")'
        printf '%s\n' '(ld "build/prover/driver/acl2/checker/package.lsp")'
        printf '(certify-book "%s" 2 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' "$book"
        printf '%s\n' '(good-bye)'
    } | sh prover/tools/acl2.sh > "$work/certify.log" 2>&1 ||
        fail "ACL2 could not certify the entry. See $work/certify.log."
fi
[ -s "$book.cert" ] || fail "ACL2 did not certify the entry. See $work/certify.log."

out=$work/entry
if [ ! -s "$out.program" ] || [ ! -s "$out.readback" ] || [ "$book.cert" -nt "$out.program" ]; then
    rm -f "$out.program" "$out.readback"
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
        printf '%s\n' "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
        printf '%s\n' '(assign bx-boot-hi (max-absolute-event-number (w state)))'
        printf '%s\n' '(ld "build/prover/acl2/package.lsp")'
        printf '%s\n' '(ld "build/prover/driver/acl2/checker/package.lsp")'
        printf '%s\n' '(include-book "build/prover/driver/acl2/driver" :uncertified-okp nil)'
        printf '%s\n' '(assign bx-lo (max-absolute-event-number (w state)))'
        printf '(include-book "%s" :uncertified-okp nil)\n' "$book"
        printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))'
        printf '%s\n' '(ld "build/export/ground-fns.lsp")'
        printf '%s\n' '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
        printf '%s\n' '(include-book "build/export/acl2/guards" :uncertified-okp nil)'
        printf '%s\n' '(ld "export/export.lsp")' '(set-guard-checking t)'
        printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-lo) (@ bx-hi) "%s" state)\n' "$out"
        printf '%s\n' '(ld "export/readback.lsp")'
        printf '(rb-readback "%s" :book (@ bx-lo) (@ bx-hi) (@ bx-ground-fns) state)\n' "$out"
        printf '%s\n' '(good-bye)'
    } | sh prover/tools/acl2.sh > "$work/export.log" 2>&1 ||
        fail "ACL2 could not export the entry. See $work/export.log."
fi
[ -s "$out.program" ] && [ -s "$out.readback" ] &&
    awk '{ n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || n != $(NF - 1)) bad = 1 }
         /^\(readback / { files++ }
         END { exit (bad || files != 2) }' "$out.readback" ||
    fail "The entry did not pass readback. See $work/export.log."

compiler=build/compiler/compiler-2
stale=
[ -x "$compiler" ] || stale=1
for source in a64 read index data gen sha256 macos linux runtime compile; do
    [ ! "compiler/$source.lisp" -nt "$compiler" ] || stale=1
done
[ ! compiler/package.lsp -nt "$compiler" ] || stale=1
[ -z "$stale" ] || sh compiler/bootstrap.sh

library=build/export/library
{
    awk '/^\((package|hidden-package) /' spec/ground.txt "$library.statements" "$exported.statements" "$out.statements"
    awk -v entry="$entry" -f prover/tools/reachable-program.awk \
        "$library.program" "$exported.program" "$out.program"
    printf '(entry %s)\n' "$entry"
    if [ "$limit" -ne 4096 ]; then
        printf '(heap-limit %s)\n' "$limit"
    fi
} > "$work/prover.input"

time -p "$compiler" < "$work/prover.input" > "$work/prover.tmp"
[ -s "$work/prover.tmp" ] || fail 'The compiler wrote no executable.'
chmod +x "$work/prover.tmp"
mv "$work/prover.tmp" build/compiler/prover
printf 'Built build/compiler/prover with a heap limit of %s MiB.\n' "$limit"
