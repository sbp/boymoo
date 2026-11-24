# Certify and export the available prefix of prover/b1/ORDER.
# From the repository root, run sh prover/b1/build.sh [LAST-BOOK].
# Status 1 means the requested prefix could not be certified and exported.

. prover/b1/tools/artifacts.sh

if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/b1/build.sh [LAST-BOOK]' >&2
    exit 2
fi
books=$(cat "$b1_order") || exit 2
target=${1-$(printf '%s\n' "$books" | awk 'NF { last = $0 } END { print last }')}
if ! grep -Fxq -- "$target" "$b1_order"; then
    echo "prover/b1/build.sh: $target is outside prover/b1/ORDER" >&2
    exit 2
fi
if [ ! -s "$b1_shared.cert" ] || [ ! -f "$b1_shared.lisp" ]; then
    echo "prover/b1/build.sh: $b1_shared must already be certified" >&2
    exit 2
fi

mkdir -p "$b1_books" "$b1_exports" || exit 2
b1_tempdir || exit 2
lock=$b1_work/build.lock
if ! mkdir "$lock"; then
    echo "prover/b1/build.sh: another build holds $lock" >&2
    exit 2
fi
trap 'rm -f "$lock"/*; rmdir "$lock"' 0
trap 'exit 143' 1 2 15

record() {
    printf '%s\n' "$2" > "$lock/marker" && mv "$lock/marker" "$b1_work/$1"
}

previous=
dependency=$b1_shared
stopped=
planned=
for book in $books; do
    source=$b1_source/$book.lisp
    copy=$b1_books/$book.lisp
    cert=$b1_books/$book.cert
    if [ ! -f "$source" ]; then
        stopped="missing $source"
        break
    fi
    if ! cmp -s "$source" "$copy"; then
        cp "$source" "$lock/source" && mv "$lock/source" "$copy" || exit 2
        rm -f "$cert" || exit 2
    fi
    if [ -n "$planned" ] || [ ! -s "$cert" ] || [ "$copy" -nt "$cert" ] ||
       [ "$b1_package" -nt "$cert" ] || [ "$dependency.cert" -nt "$cert" ]; then
        rm -f "$cert" "$b1_books/$book.fasl" "$b1_books/$book.port" "$b1_books/$book.failed" || exit 2
        planned="${planned:+$planned }$book"
    else
        previous=$book
        dependency=$b1_books/$book
    fi
    [ "$book" != "$target" ] || break
done

if [ -n "$planned" ]; then
    {
        printf "(set-ld-error-action '(:exit 1) state)\n"
        printf "(set-inhibit-output-lst '(proof-tree prove observation event history warning warning!))\n"
        printf '(ld "%s" :ld-error-action :error)\n' "$b1_package"
        for book in $planned; do
            printf '(cw "~%%b1-certifying %s~%%")\n' "$book"
            printf '(include-book "%s" :uncertified-okp nil)\n' "$dependency"
            printf '(certify-book "%s/%s" ? :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' \
                "$b1_books" "$book"
            # Undo the command while keeping its certificate and the included book.
            printf '(u)\n(cw "~%%b1-certified %s~%%")\n' "$book"
            dependency=$b1_books/$book
        done
        printf '(good-bye)\n'
    } > "$lock/forms" || exit 2
    echo "prover/b1/build.sh: certifying from ${planned%% *} through ${planned##* }"
    timeout --foreground -k 15 1800 sh prover/tools/acl2.sh < "$lock/forms" > "$lock/log" 2>&1
    status=$?
    awk -v directory="$b1_books" -v book="${planned%% *}" '
        /^b1-certifying / && $2 != book { close(directory "/" book ".out"); book = $2 }
        { print > (directory "/" book ".out") }
    ' "$lock/log" || exit 2
    for book in $planned; do
        if [ ! -s "$b1_books/$book.cert" ] ||
           ! grep -Fxq -- "b1-certified $book" "$lock/log"; then
            rm -f "$b1_books/$book.cert" || exit 2
            # A timeout waiting for a slot can leave the combined log empty.
            : >> "$b1_books/$book.out" || exit 2
            printf '%s\n' "$status" > "$b1_books/$book.failed" || exit 2
            stopped="ACL2 could not certify $b1_source/$book.lisp (see $b1_books/$book.out)"
            break
        fi
        previous=$book
    done
fi

record certified "$previous" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/b1/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    record exported '' || exit 2
    exit 1
fi
if ! b1_exported "$previous"; then
    record exported '' || exit 2
    echo "prover/b1/build.sh: exporting $previous"
    if ! sh prover/b1/tools/export.sh "$previous" "$lock" || ! b1_exported "$previous"; then
        echo "prover/b1/build.sh: certified through $previous; export failed (see $b1_exports/$previous.log)" >&2
        exit 1
    fi
fi
record exported "$previous" || exit 2
echo "prover/b1/build.sh: certified and exported through $previous"
[ -z "$stopped" ]
