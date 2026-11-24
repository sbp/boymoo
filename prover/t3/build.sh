# Run from the repository root with sh prover/t3/build.sh [LAST-BOOK].
# Certify the available prefix of ORDER and export its last book.

. prover/t3/tools/artifacts.sh

has_line() {
    [ -f "$2" ] && awk -v line="$1" '$0 == line { found = 1; exit } END { exit !found }' "$2"
}

if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/t3/build.sh [LAST-BOOK]' >&2
    exit 2
fi
books=$(cat "$t3_order") || exit 2
target=${1-$(printf '%s\n' "$books" | awk 'END { print }')}
if ! has_line "$target" "$t3_order"; then
    echo "prover/t3/build.sh: $target is outside $t3_order" >&2
    exit 2
fi
if [ ! -s "$t3_shared.cert" ] || [ ! -f "$t3_shared.lisp" ]; then
    echo "prover/t3/build.sh: $t3_shared must be certified" >&2
    exit 2
fi

mkdir -p "$t3_acl2" "$t3_work" || exit 2
lock=$t3_work/build.lock
if ! mkdir "$lock" 2>&-; then
    echo "prover/t3/build.sh: a build holds $lock" >&2
    exit 2
fi
trap 'rm -rf "$lock"' 0
trap 'exit 143' 1 2 15
ulimit -f 48000 || exit 2

record() {
    printf '%s\n' "$2" > "$lock/marker" && mv "$lock/marker" "$t3_work/$1"
}

dependency=$t3_shared
previous=
pending=
stopped=
for book in $books; do
    source=$t3_source/$book.lisp
    copy=$t3_acl2/$book.lisp
    cert=$t3_acl2/$book.cert
    if [ ! -f "$source" ]; then
        stopped="missing $source"
        break
    fi
    if ! cmp -s "$source" "$copy"; then
        rm -f "$cert" || exit 2
        cp "$source" "$copy" || exit 2
    fi
    if [ -n "$pending" ] || [ ! -s "$cert" ] || [ "$copy" -nt "$cert" ] ||
       [ "$t3_package" -nt "$cert" ] || [ "$dependency.cert" -nt "$cert" ]; then
        rm -f "$cert" "$t3_acl2/$book.fasl" || exit 2
        pending="${pending:+$pending }$book"
    else
        dependency=$t3_acl2/$book
        previous=$book
    fi
    [ "$book" != "$target" ] || break
done

if [ -n "$pending" ]; then
    {
        printf "(set-ld-error-action '(:exit 1) state)\n"
        printf "(set-inhibit-output-lst '(proof-tree prove observation event history warning warning!))\n"
        printf '(ld "%s" :ld-error-action :error)\n' "$t3_package"
        for book in $pending; do
            printf '(cw "~%%t3-certifying %s~%%")\n' "$book"
            printf '(include-book "%s" :uncertified-okp nil)\n' "$dependency"
            printf '(certify-book "%s/%s" 2 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' \
                "$t3_acl2" "$book"
            printf '(cw "~%%t3-certified %s~%%")\n' "$book"
            # Keep the package and replace the included predecessor.
            [ "$book" = "${pending##* }" ] || printf '(ubt! 2)\n'
            dependency=$t3_acl2/$book
        done
        printf '(good-bye)\n'
    } > "$lock/session.in" || exit 2
    echo "prover/t3/build.sh: certifying from ${pending%% *} through ${pending##* }"
    timeout --foreground -k 15 "$t3_limit" sh prover/tools/acl2.sh \
        < "$lock/session.in" > "$lock/session.out" 2>&1
    # Preserve a log for each attempted book and any output before the first.
    awk -v directory="$t3_acl2" -v book="${pending%% *}" '
        /^t3-certifying / && $2 != book { close(directory "/" book ".out"); book = $2 }
        { print > (directory "/" book ".out") }
    ' "$lock/session.out" || exit 2
    for book in $pending; do
        prefix=$t3_acl2/$book
        if [ ! -s "$prefix.cert" ] || ! has_line "t3-certified $book" "$prefix.out"; then
            rm -f "$prefix.cert" || exit 2
            if ! has_line "t3-certifying $book" "$prefix.out"; then
                cp "$lock/session.out" "$prefix.out" || exit 2
            fi
            stopped="ACL2 could not certify $t3_source/$book.lisp (see $prefix.out)"
            break
        fi
        previous=$book
    done
fi

record certified "$previous" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/t3/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    record exported '' || exit 2
    exit 1
fi

if ! t3_exported "$previous"; then
    record exported '' || exit 2
    echo "prover/t3/build.sh: exporting $previous"
    for prerequisite in ground-fns.lsp acl2/canon.cert acl2/guards.cert; do
        if [ ! -s "build/export/$prerequisite" ]; then
            echo "prover/t3/build.sh: missing build/export/$prerequisite" >&2
            exit 2
        fi
    done
    mkdir -p "$t3_exports" || exit 2
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf "%s\n" "(set-ld-error-action '(:exit 1) state)"
        printf "%s\n" "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
        printf '%s\n' '(assign bx-boot-hi (max-absolute-event-number (w state)))'
        printf '(include-book "%s/%s" :uncertified-okp nil)\n' "$t3_acl2" "$previous"
        printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))'
        printf '%s\n' '(ld "build/export/ground-fns.lsp")'
        printf '%s\n' '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
        printf '%s\n' '(include-book "build/export/acl2/guards" :uncertified-okp nil)'
        printf '%s\n' '(ld "export/export.lsp")' '(set-guard-checking t)'
        printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi) (@ bx-hi) "%s/export" state)\n' "$lock"
        printf '%s\n' '(ld "export/readback.lsp")'
        printf '(rb-readback "%s/export" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)\n' "$lock"
        printf '%s\n' '(good-bye)'
    } > "$lock/export.in" || exit 2
    timeout --foreground -k 15 "$t3_limit" sh prover/tools/acl2.sh \
        < "$lock/export.in" > "$t3_exports/$previous.log" 2>&1
    status=$?
    if [ "$status" -ne 0 ] || ! t3_readback_agrees "$lock/export.readback"; then
        echo "prover/t3/build.sh: certified through $previous; export failed (see $t3_exports/$previous.log)" >&2
        exit 1
    fi
    for suffix in statements program aids notes readback; do
        mv "$lock/export.$suffix" "$t3_exports/$previous.$suffix" || exit 2
    done
fi
record exported "$previous" || exit 2
echo "prover/t3/build.sh: certified and exported through $previous"
[ -z "$stopped" ]
