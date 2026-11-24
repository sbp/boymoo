# From the repository root, certify and export the available T4 prefix.
# Use sh prover/t4/build.sh [LAST-BOOK].

. prover/t4/tools/artifacts.sh || exit 2

if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/t4/build.sh [LAST-BOOK]' >&2
    exit 2
fi
books=$(cat "$t4_order") || exit 2
target=${1-$(printf '%s\n' "$books" | awk 'END { print }')}
if ! grep -Fxq -- "$target" "$t4_order"; then
    echo "prover/t4/build.sh: $target is outside $t4_order" >&2
    exit 2
fi
if [ ! -s "$t4_shared.cert" ] || [ ! -f "$t4_shared.lisp" ]; then
    echo "prover/t4/build.sh: $t4_shared must already be certified" >&2
    exit 2
fi

mkdir -p "$t4_acl2" "$t4_exports" || exit 2
lock=$t4_work/build.lock
if ! mkdir "$lock"; then
    echo "prover/t4/build.sh: could not acquire $lock" >&2
    exit 2
fi
trap 'rm -rf "$lock"' 0
trap 'exit 143' 1 2 15

record() {
    printf '%s\n' "$2" > "$lock/marker" && mv "$lock/marker" "$t4_work/$1"
}

export_prefix() {
    for input in ground-fns.lsp acl2/canon.cert acl2/guards.cert; do
        if [ ! -s "build/export/$input" ]; then
            echo "prover/t4/build.sh: missing build/export/$input" >&2
            return 1
        fi
    done
    staged=$lock/$1
    out=$t4_exports/$1
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
        printf '%s\n' "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
        printf '%s\n' '(assign bx-boot-hi (max-absolute-event-number (w state)))'
        printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$t4_acl2" "$1"
        printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))'
        printf '%s\n' '(ld "build/export/ground-fns.lsp")'
        printf '%s\n' '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
        printf '%s\n' '(include-book "build/export/acl2/guards" :uncertified-okp nil)'
    } > "$lock/export-base.in" || return 1

    {
        cat "$lock/export-base.in"
        printf '%s\n' '(ld "export/export.lsp")' '(set-guard-checking t)'
        printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi) (@ bx-hi) "%s" state)\n' "$staged"
        printf '%s\n' '(cw "~%t4 export complete~%")' '(good-bye)'
    } > "$lock/export.in" || return 1
    t4_run_acl2 < "$lock/export.in" > "$out.log" 2>&1 &&
        grep -Fxq 't4 export complete' "$out.log" &&
        [ -s "$staged.statements" ] && [ -f "$staged.program" ] || return 1

    {
        cat "$lock/export-base.in"
        printf '%s\n' '(ld "export/readback.lsp")'
        printf '(rb-readback "%s" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)\n' "$staged"
        printf '%s\n' '(good-bye)'
    } > "$lock/readback.in" || return 1
    t4_run_acl2 < "$lock/readback.in" >> "$out.log" 2>&1 &&
        t4_readback_ok "$staged" || return 1
    for suffix in statements aids notes program readback; do
        mv "$staged.$suffix" "$out.$suffix" || return 1
    done
    t4_exported "$1"
}

dependency=$t4_shared
previous=
pending=
stopped=
for book in $books; do
    source=$t4_source/$book.lisp
    copy=$t4_acl2/$book.lisp
    cert=$t4_acl2/$book.cert
    if [ ! -f "$source" ]; then
        stopped="missing $source"
        break
    fi
    if ! cmp -s "$source" "$copy"; then
        rm -f "$cert" || exit 2
        cp "$source" "$copy" || exit 2
    fi
    if [ -n "$pending" ] || [ ! -s "$cert" ] || [ "$copy" -nt "$cert" ] ||
       [ "$t4_package" -nt "$cert" ] || [ "$dependency.cert" -nt "$cert" ]; then
        rm -f "$cert" "$t4_acl2/$book.fasl" || exit 2
        pending="${pending:+$pending }$book"
    else
        dependency=$t4_acl2/$book
        previous=$book
    fi
    [ "$book" != "$target" ] || break
done

if [ -n "$pending" ]; then
    # Use one ACL2 slot for the prefix and retain the package between books.
    {
        printf "(set-ld-error-action '(:exit 1) state)\n"
        printf "(set-inhibit-output-lst '(proof-tree prove observation event history warning warning!))\n"
        printf '(ld "%s" :ld-error-action :error)\n' "$t4_package"
        for book in $pending; do
            printf '(cw "~%%t4-certifying %s~%%")\n' "$book"
            printf '(include-book "%s" :uncertified-okp nil)\n' "$dependency"
            printf '(certify-book "%s/%s" 2 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' \
                "$t4_acl2" "$book"
            printf '(cw "~%%t4-certified %s~%%")\n' "$book"
            [ "$book" = "${pending##* }" ] || printf '(ubt! 2)\n'
            dependency=$t4_acl2/$book
        done
        printf '(good-bye)\n'
    } > "$lock/certify.in" || exit 2
    echo "prover/t4/build.sh: certifying ${pending%% *} through ${pending##* }"
    t4_run_acl2 < "$lock/certify.in" > "$lock/certify.out" 2>&1
    status=$?
    awk -v directory="$t4_acl2" -v book="${pending%% *}" '
        /^t4-certifying / && $2 != book { close(directory "/" book ".out"); book = $2 }
        { print > (directory "/" book ".out") }
    ' "$lock/certify.out" || exit 2
    for book in $pending; do
        prefix=$t4_acl2/$book
        if [ ! -s "$prefix.cert" ] || ! grep -Fxq -- "t4-certified $book" "$lock/certify.out"; then
            rm -f "$prefix.cert" || exit 2
            if [ ! -f "$prefix.out" ] || ! grep -Fxq -- "t4-certifying $book" "$prefix.out"; then
                cp "$lock/certify.out" "$prefix.out" || exit 2
            fi
            stopped="ACL2 could not certify $t4_source/$book.lisp (status $status, see $prefix.out)"
            break
        fi
        previous=$book
    done
fi

record certified "$previous" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/t4/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    record exported '' || exit 2
    exit 1
fi
if ! t4_exported "$previous"; then
    record exported '' || exit 2
    echo "prover/t4/build.sh: exporting $previous"
    if ! export_prefix "$previous"; then
        log=$t4_exports/$previous.log
        echo "prover/t4/build.sh: certified through $previous; export failed (see $log)" >&2
        exit 1
    fi
fi
record exported "$previous" || exit 2
echo "prover/t4/build.sh: certified and exported through $previous"
[ -z "$stopped" ]
