# Run from the repository root with sh prover/t2/build.sh [LAST-BOOK].
# Certify the available prefix of ORDER and export its last book.

. prover/t2/tools/artifacts.sh

run_acl2() {
    t2_use_work_tmp || return 1
    SBCL_USER_ARGS='--dynamic-space-size 1500' \
        timeout --foreground -k 15 "$1" "${ACL2:-acl2}"
}

if [ "${1-}" = --run-acl2 ] && [ "$#" -eq 2 ]; then
    run_acl2 "$2"
    exit $?
fi

if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/t2/build.sh [LAST-BOOK]' >&2
    exit 2
fi
books=$(cat "$t2_order") || exit 2
target=${1-$(printf '%s\n' "$books" | awk 'END { print }')}
if ! grep -Fxq -- "$target" "$t2_order"; then
    echo "prover/t2/build.sh: $target is outside $t2_order" >&2
    exit 2
fi
if [ ! -s "$t2_shared.cert" ] || [ ! -f "$t2_shared.lisp" ]; then
    echo "prover/t2/build.sh: $t2_shared must already be certified" >&2
    exit 2
fi

mkdir -p "$t2_work" "$t2_acl2" || exit 2
lock=$t2_work/build.lock
if ! mkdir "$lock"; then
    echo "prover/t2/build.sh: a build holds $lock" >&2
    exit 2
fi
trap 'rm -rf "$lock"' 0
trap 'exit 143' 1 2 15

record() {
    printf '%s\n' "$2" > "$lock/marker" && mv "$lock/marker" "$t2_work/$1"
}

export_book() {
    for prerequisite in ground-fns.lsp acl2/canon.cert acl2/guards.cert; do
        if [ ! -s "build/export/$prerequisite" ]; then
            echo "prover/t2/build.sh: missing build/export/$prerequisite" >&2
            return 1
        fi
    done
    mkdir -p "$t2_exports" || return 1
    temporary=$lock/export
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
        printf '%s\n' "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
        printf '%s\n' '(assign bx-boot-hi (max-absolute-event-number (w state)))'
        printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$t2_acl2" "$1"
        printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))'
        printf '%s\n' '(ld "build/export/ground-fns.lsp")'
        printf '%s\n' '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
        printf '%s\n' '(include-book "build/export/acl2/guards" :uncertified-okp nil)'
        printf '%s\n' '(ld "export/export.lsp")' '(set-guard-checking t)'
        printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi) (@ bx-hi) "%s" state)\n' "$temporary"
        printf '%s\n' '(ld "export/readback.lsp")'
        printf '(rb-readback "%s" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)\n' "$temporary"
        printf '%s\n' '(good-bye)'
    } > "$lock/export.in" || return 1
    run_acl2 1800 < "$lock/export.in" > "$t2_exports/$1.log" 2>&1 || return 1
    t2_readback_agrees "$temporary.readback" || return 1
    for suffix in statements aids notes readback program; do
        mv "$temporary.$suffix" "$t2_exports/$1.$suffix" || return 1
    done
}

dependency=$t2_shared
previous=
pending=
stopped=
for book in $books; do
    source=$t2_source/$book.lisp
    copy=$t2_acl2/$book.lisp
    if [ ! -f "$source" ]; then
        stopped="missing $source"
        break
    fi
    if [ -z "$pending" ] && t2_current "$book" "$dependency"; then
        dependency=$t2_acl2/$book
        previous=$book
    else
        rm -f "$t2_acl2/$book.cert" "$t2_acl2/$book.fasl" "$t2_acl2/$book.port" \
            "$t2_acl2/$book.failed" || exit 2
        if ! cmp -s "$source" "$copy"; then
            cp "$source" "$lock/source" && mv "$lock/source" "$copy" || exit 2
        fi
        pending="${pending:+$pending }$book"
    fi
    [ "$book" != "$target" ] || break
done

if [ -n "$pending" ]; then
    {
        printf "(set-ld-error-action '(:exit 1) state)\n"
        printf "(set-inhibit-output-lst '(proof-tree prove observation event history warning warning!))\n"
        printf '(ld "%s" :ld-error-action :error)\n' "$t2_package"
        for book in $pending; do
            printf '(cw "~%%t2-certifying %s~%%")\n' "$book"
            printf '(include-book "%s" :uncertified-okp nil)\n' "$dependency"
            printf '(cw "~%%t2-admitting %s~%%")\n' "$book"
            printf '(certify-book "%s/%s" 2 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' \
                "$t2_acl2" "$book"
            printf '(cw "~%%t2-certified %s~%%")\n' "$book"
            # Remove the included predecessor and keep the package command.
            [ "$book" = "${pending##* }" ] || printf '(ubt! 2)\n'
            dependency=$t2_acl2/$book
        done
        printf '(good-bye)\n'
    } > "$lock/session.in" || exit 2
    echo "prover/t2/build.sh: certifying from ${pending%% *} through ${pending##* }"
    run_acl2 1800 \
        < "$lock/session.in" > "$lock/session.out" 2>&1
    status=$?
    awk -v directory="$t2_acl2" -v book="${pending%% *}" '
        /^t2-certifying / && $2 != book { close(directory "/" book ".out"); book = $2 }
        { print > (directory "/" book ".out") }
    ' "$lock/session.out" || exit 2
    for book in $pending; do
        progress=$t2_acl2/$book
        if [ ! -s "$progress.cert" ] || ! grep -Fxq "t2-certified $book" "$progress.out"; then
            rm -f "$progress.cert" || exit 2
            if [ ! -s "$progress.out" ] || ! grep -Fxq "t2-certifying $book" "$progress.out"; then
                cp "$lock/session.out" "$progress.out" || exit 2
            fi
            printf '%s\n' "$status" > "$progress.failed" || exit 2
            stopped="ACL2 could not certify $t2_source/$book.lisp (see $progress.out)"
            break
        fi
        rm -f "$progress.failure" || exit 2
        previous=$book
    done
fi

# Use the current prefix if a source changed while ACL2 held its copy.
if [ -n "$previous" ] && ! t2_certified "$previous"; then
    prefix_end=$previous
    previous=
    dependency=$t2_shared
    for book in $books; do
        if ! t2_current "$book" "$dependency"; then
            stopped="a change in $t2_source/$book.lisp during certification"
            break
        fi
        previous=$book
        dependency=$t2_acl2/$book
        [ "$book" != "$prefix_end" ] || break
    done
fi

record certified "$previous" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/t2/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    record exported '' || exit 2
    exit 1
fi

if ! t2_exported "$previous"; then
    record exported '' || exit 2
    echo "prover/t2/build.sh: exporting $previous"
    if ! export_book "$previous" || ! t2_exported "$previous"; then
        echo "prover/t2/build.sh: certified through $previous. Export failed. See $t2_exports/$previous.log." >&2
        exit 1
    fi
    rm -f "$t2_acl2/$previous.export-failure" || exit 2
fi
if ! t2_certified "$previous"; then
    record exported '' || exit 2
    echo 'prover/t2/build.sh: the sources changed during export' >&2
    exit 1
fi
record exported "$previous" || exit 2
echo "prover/t2/build.sh: certified and exported through $previous"
[ -z "$stopped" ]
