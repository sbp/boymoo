# Find the certified books and their runner exports.

h4_source=prover/h4
h4_work=build/prover/h4
h4_books=$h4_work/acl2
h4_exports=$h4_work/export
h4_shared=build/prover/acl2

h4_acl2() {
    sh prover/tools/acl2.sh "$@"
}

h4_readback_agrees() {
    awk '
        { found = $NF; sub(/\)$/, "", found)
          if (found !~ /^[0-9]+$/ || $(NF - 1) != found) bad = 1 }
        /^\(readback / { readbacks++ }
        END { exit (bad || readbacks != 2 || NR < 6) }
    ' "$1"
}

h4_export_current() {
    for suffix in statements program readback; do
        [ -s "$1.$suffix" ] && [ ! "$2" -nt "$1.$suffix" ] || return 1
    done
    h4_readback_agrees "$1.readback"
}

h4_book() {
    book=$1
    stage=$2
    if [ -z "$book" ]; then book=$(cat "$h4_work/$stage" 2>/dev/null) || book=; fi
    if ! h4_cert_current "$book"; then
        echo 'Run sh prover/h4/build.sh to certify the requested H4 book.' >&2
        return 2
    fi
    out=$h4_exports/$book
    if [ "$stage" = exported ] && ! h4_export_current "$out" "$h4_books/$book.cert"; then
        echo "Run sh prover/h4/build.sh -- $book to export the requested H4 book." >&2
        return 2
    fi
}

h4_cert_current() {
    previous=$h4_shared/descent.cert
    [ -s "$previous" ] || return 1
    while IFS= read -r prefix_book; do
        source=$h4_source/$prefix_book.lisp
        staged=$h4_books/$prefix_book.lisp
        cert=$h4_books/$prefix_book.cert
        [ -s "$cert" ] && [ -s "$staged" ] && [ -s "$source" ] &&
            [ ! "$previous" -nt "$cert" ] && [ ! prover/package.lsp -nt "$cert" ] &&
            [ ! "$staged" -nt "$cert" ] || return 1
        if [ "$source" -nt "$cert" ] && ! cmp -s "$source" "$staged"; then
            return 1
        fi
        [ "$prefix_book" != "$1" ] || return 0
        previous=$cert
    done < "$h4_source/ORDER"
    return 1
}
