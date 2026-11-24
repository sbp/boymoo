# Certify and export the available prefix of prover/b2/ORDER.
# Run from the repository root with sh prover/b2/build.sh [LAST-BOOK].

. prover/b2/tools/artifacts.sh

if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/b2/build.sh [LAST-BOOK]' >&2
    exit 2
fi
books=$(cat "$b2_order") || exit 2
target=${1-$(printf '%s\n' "$books" | awk 'END { print }')}
if ! grep -Fxq -- "$target" "$b2_order"; then
    echo "prover/b2/build.sh: $target is outside prover/b2/ORDER" >&2
    exit 2
fi
if [ ! -f "$b2_shared.cert" ] || [ ! -f "$b2_shared.lisp" ]; then
    echo "prover/b2/build.sh: $b2_shared must already be certified" >&2
    exit 2
fi

mkdir -p "$b2_work" "$b2_acl2" || exit 2
lock=$b2_work/build.lock
if ! mkdir "$lock"; then
    echo "prover/b2/build.sh: could not acquire $lock" >&2
    exit 2
fi
trap 'rm -f "$lock/certify.in" "$lock/certify.out" "$lock/marker"; rmdir "$lock"' 0
trap 'exit 143' 1 2 15

record() {
    printf '%s\n' "$2" > "$lock/marker" && mv "$lock/marker" "$b2_work/$1"
}

dependency=$b2_shared
previous=
stopped=
planned=
for book in $books; do
    source=$b2_source/$book.lisp
    copy=$b2_acl2/$book.lisp
    cert=$b2_acl2/$book.cert
    if [ ! -f "$source" ]; then
        stopped="missing $source"
        break
    fi
    if ! cmp -s "$source" "$copy"; then
        rm -f "$cert" || exit 2
        cp "$source" "$copy" || exit 2
    fi
    if [ -n "$planned" ] || [ ! -s "$cert" ] || [ "$copy" -nt "$cert" ] ||
       [ "$b2_package" -nt "$cert" ] || [ "$dependency.cert" -nt "$cert" ]; then
        rm -f "$cert" "$b2_acl2/$book.fasl" "$b2_acl2/$book.failed" || exit 2
        planned="${planned:+$planned }$book"
    else
        dependency=$b2_acl2/$book
        previous=$book
    fi
    [ "$book" != "$target" ] || break
done

if [ -n "$planned" ]; then
    # Including each predecessor keeps the certification world available
    # for the next book in the same ACL2 session.
    {
        printf "(set-ld-error-action '(:exit 1) state)\n"
        printf "(set-inhibit-output-lst '(proof-tree prove observation event history warning warning!))\n"
        printf '(ld "%s" :ld-error-action :error)\n' "$b2_package"
        for book in $planned; do
            printf '(cw "~%%b2-certifying %s~%%")\n' "$book"
            printf '(include-book "%s" :uncertified-okp nil)\n' "$dependency"
            printf '(certify-book "%s/%s" ? :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' \
                "$b2_acl2" "$book"
            # Certify-book itself is a command outside the next book's
            # certification world. Its certificate remains on disk.
            printf '(u)\n'
            printf '(cw "~%%b2-certified %s~%%")\n' "$book"
            dependency=$b2_acl2/$book
        done
        printf '(good-bye)\n'
    } > "$lock/certify.in" || exit 2
    echo "prover/b2/build.sh: certifying from ${planned%% *} through ${planned##* }"
    timeout --foreground -k 10 900 sh prover/tools/acl2.sh \
        < "$lock/certify.in" > "$lock/certify.out" 2>&1
    status=$?
    awk -v directory="$b2_acl2" -v book="${planned%% *}" '
        /^b2-certifying / && $2 != book { close(directory "/" book ".out"); book = $2 }
        { print > (directory "/" book ".out") }
    ' "$lock/certify.out" || exit 2
    for book in $planned; do
        if [ ! -s "$b2_acl2/$book.cert" ] ||
           ! grep -Fxq -- "b2-certified $book" "$lock/certify.out"; then
            rm -f "$b2_acl2/$book.cert" || exit 2
            # ACL2 may be interrupted while still waiting for a slot.
            [ -f "$b2_acl2/$book.out" ] || cp "$lock/certify.out" "$b2_acl2/$book.out" || exit 2
            printf '%s\n' "$status" > "$b2_acl2/$book.failed" || exit 2
            stopped="could not certify $b2_source/$book.lisp. See $b2_acl2/$book.out."
            break
        fi
        rm -f "$b2_acl2/$book.failure" || exit 2
        previous=$book
    done
fi

record certified "$previous" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/b2/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    record exported '' || exit 2
    exit 1
fi
if ! b2_exported "$previous"; then
    record exported '' || exit 2
    echo "prover/b2/build.sh: exporting $previous"
    if ! sh export/book.sh "$b2_acl2/$previous" || ! b2_exported "$previous"; then
        echo "prover/b2/build.sh: certified through $previous. Export failed. See $b2_exports/$previous.log." >&2
        exit 1
    fi
fi
record exported "$previous" || exit 2
echo "prover/b2/build.sh: certified and exported through $previous"
[ -z "$stopped" ]
