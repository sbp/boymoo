# Paths and checks shared by the H2 shell commands.
h2_source=prover/h2
h2_order=$h2_source/ORDER
h2_work=build/prover/h2
h2_acl2=$h2_work/acl2
h2_shared=build/prover/acl2/descent
h2_package=prover/package.lsp
h2_exports=$h2_work/export

h2_certified() {
    h2_dependency=$h2_shared.cert
    [ -s "$h2_dependency" ] || return 1
    for h2_book in $(cat "$h2_order"); do
        h2_copy=$h2_acl2/$h2_book.lisp
        h2_cert=$h2_acl2/$h2_book.cert
        if [ ! -s "$h2_cert" ] || ! cmp -s "$h2_source/$h2_book.lisp" "$h2_copy" ||
           [ "$h2_copy" -nt "$h2_cert" ] || [ "$h2_package" -nt "$h2_cert" ] ||
           [ "$h2_dependency" -nt "$h2_cert" ]; then
            return 1
        fi
        [ "$h2_book" != "$1" ] || return 0
        h2_dependency=$h2_cert
    done
    return 1
}

h2_exported() {
    h2_base=$h2_exports/$1
    h2_cert=$h2_acl2/$1.cert
    [ -s "$h2_base.statements" ] && [ -f "$h2_base.program" ] &&
        [ -s "$h2_base.readback" ] &&
        [ ! "$h2_cert" -nt "$h2_base.statements" ] &&
        [ ! "$h2_cert" -nt "$h2_base.program" ] &&
        [ ! "$h2_cert" -nt "$h2_base.readback" ] &&
        awk '/^\(readback / { headers++ }
             { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
             END { exit (headers != 2 || NR < 6 || bad) }' "$h2_base.readback"
}
