# Locations and currency checks for L1 certificates and runner programs.
l1_source=prover/l1
l1_order=$l1_source/ORDER
l1_work=build/prover/l1
l1_acl2=$l1_work/acl2
l1_shared=build/prover/acl2/descent
l1_package=build/prover/acl2/package.lsp
l1_exports=$l1_work/export

l1_certified() {
    l1_before=$l1_shared.cert
    [ -s "$l1_before" ] && [ -f "$l1_package" ] || return 1
    for l1_book in $(cat "$l1_order"); do
        l1_copy=$l1_acl2/$l1_book.lisp
        l1_cert=$l1_acl2/$l1_book.cert
        if [ ! -f "$l1_copy" ] || [ ! -s "$l1_cert" ] || [ "$l1_before" -nt "$l1_cert" ] ||
           [ "$l1_package" -nt "$l1_cert" ] || [ "$l1_copy" -nt "$l1_cert" ]; then
            return 1
        fi
        if [ "${2-}" = current ] && ! cmp -s "$l1_source/$l1_book.lisp" "$l1_copy"; then
            return 1
        fi
        [ "$l1_book" != "$1" ] || return 0
        l1_before=$l1_cert
    done
    return 1
}

l1_exported() {
    l1_out=$l1_exports/$1
    l1_cert=$l1_acl2/$1.cert
    [ -s "$l1_out.statements" ] && [ -f "$l1_out.program" ] && [ -s "$l1_out.readback" ] &&
        [ ! "$l1_cert" -nt "$l1_out.statements" ] && [ ! "$l1_cert" -nt "$l1_out.program" ] &&
        [ ! "$l1_cert" -nt "$l1_out.readback" ] && l1_readback_agrees "$l1_out.readback"
}

l1_readback_agrees() {
    awk 'NR <= 2 && !/^\(readback / { bad = 1 }
             NR > 2 && !/^\(complete / { bad = 1 }
             { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
             END { exit (NR != 6 || bad) }' "$1"
}
