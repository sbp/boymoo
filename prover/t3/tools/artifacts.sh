# Paths and certificate checks for the T3 build and its two entry points.
t3_source=prover/t3
t3_order=$t3_source/ORDER
t3_work=build/prover/t3
t3_acl2=$t3_work/acl2
t3_shared=build/prover/acl2/descent
t3_package=prover/package.lsp
t3_exports=$t3_work/export
t3_limit=1800

t3_certified() {
    t3_requested=$1
    t3_before=$t3_shared.cert
    [ -s "$t3_before" ] || return 1
    while IFS= read -r t3_book; do
        t3_cert=$t3_acl2/$t3_book.cert
        if [ ! -s "$t3_cert" ] || ! cmp -s "$t3_source/$t3_book.lisp" "$t3_acl2/$t3_book.lisp" ||
           [ "$t3_acl2/$t3_book.lisp" -nt "$t3_cert" ] ||
           [ "$t3_package" -nt "$t3_cert" ] || [ "$t3_before" -nt "$t3_cert" ]; then
            return 1
        fi
        [ "$t3_book" != "$t3_requested" ] || return 0
        t3_before=$t3_cert
    done < "$t3_order"
    return 1
}

t3_exported() {
    t3_export=$t3_exports/$1
    t3_export_cert=$t3_acl2/$1.cert
    [ -s "$t3_export_cert" ] && [ -s "$t3_export.statements" ] &&
        [ -f "$t3_export.program" ] && [ -s "$t3_export.readback" ] &&
        [ ! "$t3_export_cert" -nt "$t3_export.statements" ] &&
        [ ! "$t3_export_cert" -nt "$t3_export.program" ] &&
        [ ! "$t3_export_cert" -nt "$t3_export.readback" ] &&
        t3_readback_agrees "$t3_export.readback"
}

t3_readback_agrees() {
    awk '/^\(readback / { count++ }
         { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
         END { exit (count != 2 || NR < 6 || bad) }' "$1"
}
