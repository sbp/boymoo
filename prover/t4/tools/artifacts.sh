# Locations and certificate checks used by the T4 shell commands.
t4_source=prover/t4
t4_order=$t4_source/ORDER
t4_work=build/prover/t4
t4_acl2=$t4_work/acl2
t4_shared=build/prover/acl2/descent
t4_package=prover/package.lsp
t4_exports=$t4_work/export

t4_certified() {
    t4_before=$t4_shared.cert
    [ -s "$t4_before" ] || return 1
    for t4_book in $(cat "$t4_order"); do
        t4_copy=$t4_acl2/$t4_book.lisp
        t4_cert=$t4_acl2/$t4_book.cert
        if ! cmp -s "$t4_source/$t4_book.lisp" "$t4_copy" || [ ! -s "$t4_cert" ] ||
           [ "$t4_copy" -nt "$t4_cert" ] || [ "$t4_package" -nt "$t4_cert" ] ||
           [ "$t4_before" -nt "$t4_cert" ]; then
            return 1
        fi
        [ "$t4_book" != "$1" ] || return 0
        t4_before=$t4_cert
    done
    return 1
}

t4_readback_ok() {
    [ -s "$1.statements" ] &&
        [ -f "$1.program" ] && [ -s "$1.readback" ] &&
        awk '/^\(readback / { count++ }
             { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
             END { exit (count != 2 || NR < 6 || bad) }' "$1.readback"
}

t4_exported() {
    t4_cert=$t4_acl2/$1.cert
    t4_export=$t4_exports/$1
    [ -s "$t4_cert" ] && t4_readback_ok "$t4_export" &&
        [ ! "$t4_cert" -nt "$t4_export.statements" ] &&
        [ ! "$t4_cert" -nt "$t4_export.program" ] &&
        [ ! "$t4_cert" -nt "$t4_export.readback" ]
}

t4_run_acl2() {
    timeout --foreground -k 15 1800 sh prover/tools/acl2.sh
}
