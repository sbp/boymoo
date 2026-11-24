#!/bin/sh
# From the repository root, run sh prover/l1/build.sh [LAST-BOOK].
# A partial build exports its last certified book and returns status 1.

. prover/l1/tools/artifacts.sh || exit 2
if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/l1/build.sh [LAST-BOOK]' >&2
    exit 2
fi
books=$(cat "$l1_order") || exit 2
target=${1-$(printf '%s\n' "$books" | awk 'END { print }')}
if ! grep -Fxq -- "$target" "$l1_order"; then
    echo "prover/l1/build.sh: $target is outside $l1_order" >&2
    exit 2
fi
if [ ! -f "$l1_package" ] || [ ! -s "$l1_shared.cert" ] || [ ! -f "$l1_shared.lisp" ]; then
    echo "prover/l1/build.sh: the certified shared prefix through $l1_shared is required" >&2
    exit 2
fi

mkdir -p "$l1_acl2" "$l1_exports" || exit 2
lock=$l1_work/build.lock
if ! mkdir "$lock"; then
    echo "prover/l1/build.sh: could not acquire $lock" >&2
    exit 2
fi
trap 'rm -f "$lock/source" "$lock/session" "$lock/log" "$lock/prefix" "$lock"/book.*; rmdir "$lock"' 0
trap 'exit 143' HUP INT TERM

record() {
    printf '%s\n' "$2" > "$lock/prefix" && mv "$lock/prefix" "$l1_work/$1"
}

export_book() {
    for dependency in ground-fns.lsp acl2/canon.cert acl2/guards.cert; do
        if [ ! -s "build/export/$dependency" ]; then
            echo "prover/l1/build.sh: missing build/export/$dependency" >&2
            return 1
        fi
    done
    {
        printf '%s\n' '(ld "checks/version.lsp")' \
            "(set-ld-error-action '(:exit 1) state)" \
            "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))" \
            '(assign bx-boot-hi (max-absolute-event-number (w state)))'
        printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$l1_acl2" "$1"
        printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))' \
            '(ld "build/export/ground-fns.lsp")' \
            '(include-book "build/export/acl2/canon" :uncertified-okp nil)' \
            '(include-book "build/export/acl2/guards" :uncertified-okp nil)' \
            '(ld "export/export.lsp")' '(set-guard-checking t)'
        printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi) (@ bx-hi) "%s/book" state)\n' "$lock"
        printf '%s\n' '(ld "export/readback.lsp")'
        printf '(rb-readback "%s/book" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)\n' "$lock"
        printf '%s\n' '(good-bye)'
    } > "$lock/session" || return 1
    timeout --foreground -k 30 3600 sh prover/tools/acl2.sh \
        < "$lock/session" > "$l1_exports/$1.log" 2>&1 || return 1
    l1_readback_agrees "$lock/book.readback" || return 1
    for suffix in statements program aids notes readback; do
        mv "$lock/book.$suffix" "$l1_exports/$1.$suffix" || return 1
    done
}

dependency=$l1_shared
previous=
pending=
stopped=
for book in $books; do
    source=$l1_source/$book.lisp
    copy=$l1_acl2/$book.lisp
    cert=$l1_acl2/$book.cert
    if [ ! -f "$source" ]; then
        stopped="missing $source"
        break
    fi
    if ! cmp -s "$source" "$copy"; then
        cp "$source" "$lock/source" && rm -f "$cert" && mv "$lock/source" "$copy" || exit 2
    fi
    if [ -n "$pending" ] || [ ! -s "$cert" ] || [ "$copy" -nt "$cert" ] ||
       [ "$l1_package" -nt "$cert" ] || [ "$dependency.cert" -nt "$cert" ]; then
        rm -f "$cert" "$l1_acl2/$book.fasl" || exit 2
        pending="${pending:+$pending }$book"
    else
        dependency=$l1_acl2/$book
        previous=$book
    fi
    [ "$book" != "$target" ] || break
done

if [ -n "$pending" ]; then
    # Undo the include and certification before including the next predecessor.
    {
        printf "(set-ld-error-action '(:exit 1) state)\n"
        printf "(set-inhibit-output-lst '(proof-tree prove observation event history warning warning!))\n"
        printf '(ld "%s" :ld-error-action :error)\n' "$l1_package"
        for book in $pending; do
            printf '(cw "~%%l1-certifying %s~%%")\n' "$book"
            printf '(include-book "%s" :uncertified-okp nil)\n' "$dependency"
            printf '(certify-book "%s/%s" 2 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' \
                "$l1_acl2" "$book"
            printf '(cw "~%%l1-certified %s~%%")\n' "$book"
            [ "$book" = "${pending##* }" ] || printf '(ubt! 2)\n'
            dependency=$l1_acl2/$book
        done
        printf '(good-bye)\n'
    } > "$lock/session" || exit 2
    echo "prover/l1/build.sh: certifying ${pending%% *} through ${pending##* }"
    timeout --foreground -k 30 3600 sh prover/tools/acl2.sh < "$lock/session" > "$lock/log" 2>&1
    awk -v directory="$l1_acl2" -v book="${pending%% *}" '
        /^l1-certifying / && $2 != book { close(directory "/" book ".out"); book = $2 }
        { print > (directory "/" book ".out") }
    ' "$lock/log" || exit 2
    for book in $pending; do
        cert=$l1_acl2/$book.cert
        if [ ! -s "$cert" ] || ! grep -Fxq -- "l1-certified $book" "$lock/log"; then
            rm -f "$cert" || exit 2
            log=$l1_acl2/$book.out
            if ! grep -Fxq -- "l1-certifying $book" "$log" 2>/dev/null; then
                cp "$lock/log" "$log" || exit 2
            fi
            stopped="ACL2 could not certify $l1_source/$book.lisp (see $log)"
            break
        fi
        previous=$book
    done
fi

record certified "$previous" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/l1/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    record exported '' || exit 2
    exit 1
fi
if ! l1_exported "$previous"; then
    record exported '' || exit 2
    echo "prover/l1/build.sh: exporting $previous"
    if ! export_book "$previous" || ! l1_exported "$previous"; then
        log=$l1_exports/$previous.log
        echo "prover/l1/build.sh: certified through $previous; export failed (see $log)" >&2
        exit 1
    fi
fi
record exported "$previous" || exit 2
echo "prover/l1/build.sh: certified and exported through $previous"
if ! l1_certified "$previous" current; then
    echo "prover/l1/build.sh: sources changed during the build; the export uses the certified copies" >&2
fi
[ -z "$stopped" ]
