# Run from the repository root with sh prover/h3/build.sh [LAST-BOOK].
# Certifies and exports the available prefix of prover/h3/ORDER.

if [ "$#" -gt 1 ]; then
    echo 'usage: sh prover/h3/build.sh [LAST-BOOK]' >&2
    exit 2
fi
order=prover/h3/ORDER
books=$(cat "$order") || exit 2
target=${1-$(awk 'NF { last = $1 } END { print last }' "$order")}
if ! grep -Fxq -- "$target" "$order"; then
    echo "prover/h3/build.sh: $target is outside $order" >&2
    exit 2
fi

work=build/prover/h3
dir=build/prover/acl2/h3
shared=build/prover/acl2/descent
package=prover/package.lsp
if [ ! -f "$shared.cert" ] || [ ! -f "$shared.lisp" ]; then
    echo "prover/h3/build.sh: the certified shared book $shared is required" >&2
    exit 2
fi
mkdir -p "$work" "$dir" || exit 2
lock=$work/build.lock
if ! mkdir "$lock"; then
    echo "prover/h3/build.sh: could not acquire $lock" >&2
    exit 2
fi
trap 'rm -f "$work/certified.new" "$work/exported.new"; rmdir "$lock"' 0
trap 'exit 143' 1 2 15
ulimit -f 48000 || exit 2
SBCL_USER_ARGS=${SBCL_USER_ARGS-'--dynamic-space-size 1500'}
export SBCL_USER_ARGS

record() {
    printf '%s\n' "$2" > "$work/$1.new" &&
        mv "$work/$1.new" "$work/$1"
}

dependency=$shared
certified_dependency=$shared
previous=
stopped=
stale=0
pending=
for book in $books; do
    source=prover/h3/$book.lisp
    copy=$dir/$book.lisp
    cert=$dir/$book.cert
    if [ ! -f "$source" ]; then
        stopped="missing $source"
        break
    fi
    if ! cmp -s "$source" "$copy"; then
        stale=1
        cp "$source" "$copy" || exit 2
    fi
    if [ "$stale" -eq 1 ] || [ ! -f "$cert" ] ||
       [ "$copy" -nt "$cert" ] || [ "$package" -nt "$cert" ] ||
       [ "$dependency.cert" -nt "$cert" ]; then
        stale=1
        rm -f "$cert" "$dir/$book.failed" || exit 2
        pending="$pending $book"
    else
        certified_dependency=$dir/$book
        previous=$book
    fi
    dependency=$dir/$book
    [ "$book" != "$target" ] || break
done

if [ -n "$pending" ]; then
    echo "prover/h3/build.sh: certifying$pending"
    # The names in pending come from ORDER.
    sh prover/h3/tools/certify-prefix.sh "$certified_dependency" $pending
    status=$?
    for book in $pending; do
        prefix=$dir/$book
        if [ ! -s "$prefix.cert" ] || ! grep -Fxq "h3-certify-done $book" "$prefix.out"; then
            rm -f "$prefix.cert" || exit 2
            if [ ! -f "$prefix.out" ] || ! grep -Fxq "h3-certify-begin $book" "$prefix.out"; then
                tail -n 150 "$work/certify.out" > "$prefix.out"
            fi
            printf '%s\n' "$status" > "$prefix.failed" || exit 2
            stopped="could not certify prover/h3/$book.lisp (see $prefix.out)"
            break
        fi
        rm -f "$prefix.failure" || exit 2
        previous=$book
    done
fi

record certified "$previous" || exit 2
if [ -n "$stopped" ]; then
    echo "prover/h3/build.sh: stopped at $stopped" >&2
fi
if [ -z "$previous" ]; then
    record exported "" || exit 2
    exit 1
fi

dependency=$dir/$previous
out=build/export/books/$dependency
export_ok() {
    [ -s "$out.statements" ] && [ -f "$out.program" ] && [ -s "$out.readback" ] &&
        awk '/^\(readback / { count++ }
             { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
             END { exit (count != 2 || NR < 6 || bad) }' "$out.readback"
}

if [ "$dependency.cert" -nt "$out.statements" ] ||
   [ "$dependency.cert" -nt "$out.program" ] ||
   [ "$dependency.cert" -nt "$out.readback" ] || ! export_ok; then
    record exported "" || exit 2
    echo "prover/h3/build.sh: exporting $previous"
    if ! sh export/book.sh "$dependency" || ! export_ok; then
        echo "prover/h3/build.sh: certified through $previous; export failed (see $out.log)" >&2
        exit 1
    fi
fi
record exported "$previous" || exit 2
echo "prover/h3/build.sh: certified and exported through $previous"
[ -z "$stopped" ]
