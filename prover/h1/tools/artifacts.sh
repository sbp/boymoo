# Paths and artifact checks shared by the H1 shell commands.
h1_source=prover/h1
h1_order=$h1_source/ORDER
h1_work=build/prover/h1
h1_acl2=$h1_work/acl2
h1_package=prover/package.lsp
h1_shared=build/prover/acl2/descent
h1_exports=$h1_work/export

h1_has_book() {
    [ -n "$1" ] && grep -Fxq -- "$1" "$h1_order"
}

h1_certified() {
    h1_prior_cert=$h1_shared.cert
    [ -s "$h1_prior_cert" ] || return 1
    for h1_name in $(cat "$h1_order"); do
        h1_cert=$h1_acl2/$h1_name.cert
        h1_copy=$h1_acl2/$h1_name.lisp
        if [ ! -s "$h1_cert" ] || [ ! -f "$h1_copy" ] ||
           [ "$h1_prior_cert" -nt "$h1_cert" ] || [ "$h1_copy" -nt "$h1_cert" ] ||
           [ "$h1_package" -nt "$h1_cert" ] ||
           ! cmp -s "$h1_source/$h1_name.lisp" "$h1_copy"; then
            return 1
        fi
        [ "$h1_name" != "$1" ] || return 0
        h1_prior_cert=$h1_cert
    done
    return 1
}

h1_readback_matches() {
    awk '/^\(readback / { headers++ }
         { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
         END { exit (headers != 2 || NR < 6 || bad) }' "$1"
}

h1_exported() {
    h1_output=$h1_exports/$1
    h1_certificate=$h1_acl2/$1.cert
    [ -s "$h1_output.statements" ] && [ -s "$h1_output.program" ] &&
        [ -s "$h1_output.readback" ] &&
        [ ! "$h1_certificate" -nt "$h1_output.statements" ] &&
        [ ! "$h1_certificate" -nt "$h1_output.program" ] &&
        [ ! "$h1_certificate" -nt "$h1_output.readback" ] &&
        h1_readback_matches "$h1_output.readback"
}
