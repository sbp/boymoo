# From the repository root, certify and export the available H2 prefix.
# Use sh prover/h2/build.sh [LAST-BOOK]. A build that misses its target returns status 1.

. prover/h2/tools/artifacts.sh || exit 2

if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h2/build.sh [LAST-BOOK]' >&2
    exit 2
fi
books=$(cat "$h2_order") || exit 2
target=${1-$(printf '%s\n' "$books" | awk 'NF { last = $1 } END { print last }')}
if ! grep -Fxq -- "$target" "$h2_order"; then
    echo "prover/h2/build.sh: $target is outside $h2_order" >&2
    exit 2
fi
if [ ! -s "$h2_shared.cert" ] || [ ! -f "$h2_shared.lisp" ]; then
    echo "prover/h2/build.sh: the certified shared book $h2_shared is required" >&2
    exit 2
fi

mkdir -p "$h2_acl2" "$h2_exports" "$h2_work/tmp" || exit 2
lock=$h2_work/build.lock
if ! mkdir "$lock" 2>/dev/null; then
    echo "prover/h2/build.sh: could not acquire $lock" >&2
    exit 2
fi
trap 'rm -rf "$lock"' 0
trap 'exit 143' 1 2 15
TMPDIR=$PWD/$h2_work/tmp
export TMPDIR

record() {
    printf '%s\n' "$2" > "$lock/marker" && mv "$lock/marker" "$h2_work/$1"
}

dependency=$h2_shared
previous=
pending=
stopped=
for book in $books; do
    source=$h2_source/$book.lisp
    copy=$h2_acl2/$book.lisp
    cert=$h2_acl2/$book.cert
    if [ ! -f "$source" ]; then
        stopped="missing $source"
        break
    fi
    if ! cmp -s "$source" "$copy"; then
        rm -f "$cert" || exit 2
        cp "$source" "$copy" || exit 2
    fi
    if [ -n "$pending" ] || [ ! -s "$cert" ] || [ "$copy" -nt "$cert" ] ||
       [ "$h2_package" -nt "$cert" ] || [ "$dependency.cert" -nt "$cert" ]; then
        rm -f "$cert" "$h2_acl2/$book.fasl" "$h2_acl2/$book.failed" || exit 2
        pending="${pending:+$pending }$book"
    else
        dependency=$h2_acl2/$book
        previous=$book
    fi
    [ "$book" != "$target" ] || break
done

if [ -n "$pending" ]; then
    {
        printf "(set-ld-error-action '(:exit 1) state)\n"
        printf "(set-inhibit-output-lst '(proof-tree prove observation event history warning warning!))\n"
        printf '(ld "%s" :ld-error-action :error)\n' "$h2_package"
        for book in $pending; do
            printf '(cw "~%%h2-certifying %s~%%")\n' "$book"
            printf '(include-book "%s" :uncertified-okp nil)\n' "$dependency"
            printf '(certify-book "%s/%s" 2 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' \
                "$h2_acl2" "$book"
            printf '(cw "~%%h2-certified %s~%%")\n' "$book"
            # Retain the package and replace the included prefix before each book.
            [ "$book" = "${pending##* }" ] || printf '(ubt! 2)\n'
            dependency=$h2_acl2/$book
        done
        printf '(good-bye)\n'
    } > "$lock/certify.in" || exit 2
    echo "prover/h2/build.sh: certifying $pending"
    timeout --foreground -k 15 1800 sh prover/tools/acl2.sh \
        < "$lock/certify.in" > "$lock/certify.out" 2>&1
    status=$?
    awk -v directory="$h2_acl2" -v book="${pending%% *}" '
        /^h2-certifying / && $2 != book { close(directory "/" book ".out"); book = $2 }
        { print > (directory "/" book ".out") }
    ' "$lock/certify.out" || exit 2
    for book in $pending; do
        base=$h2_acl2/$book
        if [ ! -s "$base.cert" ] || ! grep -Fxq -- "h2-certified $book" "$base.out"; then
            rm -f "$base.cert" || exit 2
            if ! grep -Fxq -- "h2-certifying $book" "$base.out" 2>/dev/null; then
                cp "$lock/certify.out" "$base.out" || exit 2
            fi
            stopped="could not certify $h2_source/$book.lisp (see $base.out)"
            echo "prover/h2/build.sh: ACL2 exited with status $status" >&2
            break
        fi
        rm -f "$base.failed" || exit 2
        previous=$book
    done
fi

record certified "$previous" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/h2/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    record exported '' || exit 2
    exit 1
fi
if ! h2_exported "$previous"; then
    record exported '' || exit 2
    echo "prover/h2/build.sh: exporting $previous"
    sh prover/h2/tools/export.sh "$previous" "$lock"
    status=$?
    if [ "$status" -ne 0 ] || ! h2_exported "$previous"; then
        log=$h2_exports/$previous.log
        echo "prover/h2/build.sh: certified through $previous. Export failed (see $log)." >&2
        exit 1
    fi
    rm -f "$h2_acl2/$previous.export-failure" || exit 2
fi
record exported "$previous" || exit 2
echo "prover/h2/build.sh: certified and exported through $previous"
[ -z "$stopped" ]
