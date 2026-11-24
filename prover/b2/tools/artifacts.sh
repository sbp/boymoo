# Locations and checks for B2 certificates and programs.

b2_source=prover/b2
b2_work=build/prover/b2
b2_acl2=build/prover/acl2/b2
b2_shared=build/prover/acl2/descent
b2_exports=build/export/books/$b2_acl2
b2_order=$b2_source/ORDER
b2_package=prover/package.lsp

b2_current() {
    b2_check_source=$b2_source/$1.lisp
    b2_check_copy=$b2_acl2/$1.lisp
    b2_check_cert=$b2_acl2/$1.cert
    [ -s "$b2_check_cert" ] && cmp -s "$b2_check_source" "$b2_check_copy" &&
        [ ! "$b2_check_copy" -nt "$b2_check_cert" ] && [ ! "$2" -nt "$b2_check_cert" ] &&
        [ ! "$b2_package" -nt "$b2_check_cert" ]
}

b2_certified() {
    [ -f "$b2_shared.cert" ] || return 1
    prior=$b2_shared.cert
    for candidate in $(cat "$b2_order"); do
        b2_current "$candidate" "$prior" || return 1
        [ "$candidate" != "$1" ] || return 0
        prior=$b2_acl2/$candidate.cert
    done
    return 1
}

b2_run() {
    BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-$b2_work/runner-fast-cache}
    export BOYMOO_FAST_CACHE
    library=build/export/library
    exec "$RUNNER" "$@" -m 2200 -p spec/ground.txt -p "$library.statements" \
        -p "$output.statements" "$library.program" "$output.program"
}

b2_exported() {
    output=$b2_exports/$1
    certificate=$b2_acl2/$1.cert
    [ -f "$certificate" ] && [ -s "$output.statements" ] &&
        [ -f "$output.program" ] && [ -s "$output.readback" ] &&
        [ ! "$certificate" -nt "$output.statements" ] &&
        [ ! "$certificate" -nt "$output.program" ] &&
        [ ! "$certificate" -nt "$output.readback" ] &&
        awk '/^\(readback / { count++ }
             { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
             END { exit (count != 2 || NR < 6 || bad) }' "$output.readback"
}
