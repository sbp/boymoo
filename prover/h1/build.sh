# Certify and export the available H1 prefix from the repository root.
# Use sh prover/h1/build.sh [LAST-BOOK]. A partial build gives status 1.

. prover/h1/tools/artifacts.sh || exit 2
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h1/build.sh [LAST-BOOK]' >&2
    exit 2
fi
books=$(cat "$h1_order") || exit 2
target=${1-$(printf '%s\n' "$books" | awk 'NF { last = $1 } END { print last }')}
if ! h1_has_book "$target"; then
    echo "prover/h1/build.sh: $target is outside $h1_order" >&2
    exit 2
fi
if [ ! -s "$h1_shared.cert" ]; then
    echo "prover/h1/build.sh: the certified shared book $h1_shared is required" >&2
    exit 2
fi

mkdir -p "$h1_acl2" "$h1_exports" "$h1_work/tmp" || exit 2
lock=$h1_work/build.lock
if ! mkdir "$lock"; then
    echo "prover/h1/build.sh: a build is already using $lock" >&2
    exit 2
fi
trap 'rm -f "$lock/certify.in" "$lock/certify.out" "$lock/marker" "$lock/export.in" "$lock"/prefix.*; rmdir "$lock"' 0
trap 'exit 143' 1 2 15
TMPDIR=$PWD/$h1_work/tmp
export TMPDIR

record() {
    printf '%s\n' "$2" > "$lock/marker" && mv "$lock/marker" "$h1_work/$1"
}

export_book() {
    local_book=$1
    for required in build/export/ground-fns.lsp build/export/acl2/canon.cert build/export/acl2/guards.cert; do
        if [ ! -s "$required" ]; then
            printf 'prover/h1/build.sh: missing %s\n' "$required" >&2
            return 1
        fi
    done
    prefix=$lock/prefix
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
        printf '%s\n' "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
        printf '%s\n' '(assign bx-boot-hi (max-absolute-event-number (w state)))'
        printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$h1_acl2" "$local_book"
        printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))'
        printf '%s\n' '(ld "build/export/ground-fns.lsp")'
        printf '%s\n' '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
        printf '%s\n' '(include-book "build/export/acl2/guards" :uncertified-okp nil)'
        printf '%s\n' '(ld "export/export.lsp")' '(set-guard-checking t)'
        printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi) (@ bx-hi) "%s" state)\n' "$prefix"
        printf '%s\n' '(ld "export/readback.lsp")' '(value-triple #+sbcl (gc$ :full t) #-sbcl (gc$))'
        printf '(rb-readback "%s" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)\n' "$prefix"
        printf '%s\n' '(good-bye)'
    } > "$lock/export.in" || return 1
    timeout --foreground -k 15 1800 sh prover/tools/acl2.sh \
        < "$lock/export.in" > "$h1_exports/$local_book.log" 2>&1 || return 1
    [ -s "$prefix.program" ] && [ -s "$prefix.statements" ] &&
        h1_readback_matches "$prefix.readback" || return 1
    for suffix in aids notes statements program readback; do
        mv "$prefix.$suffix" "$h1_exports/$local_book.$suffix" || return 1
    done
}

dependency=$h1_shared
previous=
pending=
stopped=
for book in $books; do
    source=$h1_source/$book.lisp
    copy=$h1_acl2/$book.lisp
    cert=$h1_acl2/$book.cert
    if [ ! -s "$source" ]; then
        stopped="missing $source"
        break
    fi
    if ! cmp -s "$source" "$copy"; then
        rm -f "$cert" || exit 2
        cp "$source" "$copy" || exit 2
    fi
    if [ -n "$pending" ] || [ ! -s "$cert" ] || [ "$copy" -nt "$cert" ] ||
       [ "$h1_package" -nt "$cert" ] || [ "$dependency.cert" -nt "$cert" ]; then
        rm -f "$cert" "$h1_acl2/$book.fasl" "$h1_acl2/$book.failed" || exit 2
        pending="${pending:+$pending }$book"
    else
        dependency=$h1_acl2/$book
        previous=$book
    fi
    [ "$book" != "$target" ] || break
done

if [ -n "$pending" ]; then
    {
        printf "(set-ld-error-action '(:exit 1) state)\n"
        printf "(set-inhibit-output-lst '(proof-tree prove observation event history warning warning!))\n"
        printf '(ld "%s" :ld-error-action :error)\n' "$h1_package"
        for book in $pending; do
            printf '(cw "~%%h1-certifying %s~%%")\n' "$book"
            printf '(include-book "%s" :uncertified-okp nil)\n' "$dependency"
            printf '(certify-book "%s/%s" 2 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' \
                "$h1_acl2" "$book"
            printf '(cw "~%%h1-certified %s~%%")\n' "$book"
            # Keep the package and replace the included prefix for the next book.
            [ "$book" = "${pending##* }" ] || printf '(ubt! 2)\n'
            dependency=$h1_acl2/$book
        done
        printf '(good-bye)\n'
    } > "$lock/certify.in" || exit 2
    echo "prover/h1/build.sh: certifying $pending"
    timeout --foreground -k 15 1800 sh prover/tools/acl2.sh \
        < "$lock/certify.in" > "$lock/certify.out" 2>&1
    status=$?
    awk -v directory="$h1_acl2" -v book="${pending%% *}" '
        /^h1-certifying / && $2 != book { close(directory "/" book ".out"); book = $2 }
        { print > (directory "/" book ".out") }
    ' "$lock/certify.out" || exit 2
    for book in $pending; do
        base=$h1_acl2/$book
        if [ ! -s "$base.cert" ] || ! grep -Fxq -- "h1-certified $book" "$base.out"; then
            rm -f "$base.cert" || exit 2
            if [ ! -f "$base.out" ] || ! grep -Fxq -- "h1-certifying $book" "$base.out"; then
                cp "$lock/certify.out" "$base.out" || exit 2
            fi
            printf '%s\n' "$status" > "$base.failed" || exit 2
            stopped="ACL2 could not certify $h1_source/$book.lisp (see $base.out)"
            break
        fi
        previous=$book
    done
fi

record certified "$previous" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/h1/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    record exported '' || exit 2
    exit 1
fi

if ! h1_exported "$previous"; then
    record exported '' || exit 2
    echo "prover/h1/build.sh: exporting $previous"
    if ! export_book "$previous" || ! h1_exported "$previous"; then
        log=$h1_exports/$previous.log
        echo "prover/h1/build.sh: certified through $previous. Export failed (see $log)." >&2
        exit 1
    fi
fi
record exported "$previous" || exit 2
echo "prover/h1/build.sh: certified and exported through $previous"
[ -z "$stopped" ]
