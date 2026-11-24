# Build locations and checks for T2.

t2_source=prover/t2
t2_order=$t2_source/ORDER
t2_work=build/prover/t2
t2_acl2=$t2_work/acl2
t2_shared=build/prover/acl2/descent
t2_package=prover/package.lsp
t2_exports=$t2_work/export

t2_use_work_tmp() {
    mkdir -p "$t2_work/tmp" || return 1
    TMPDIR=$(cd "$t2_work/tmp" && pwd -P) || return 1
    export TMPDIR
}

t2_current() {
    t2_copy=$t2_acl2/$1.lisp
    t2_cert=$t2_acl2/$1.cert
    [ -s "$t2_cert" ] && [ -f "$t2_copy" ] &&
        [ ! "$t2_copy" -nt "$t2_cert" ] && [ ! "$2.cert" -nt "$t2_cert" ] &&
        [ ! "$t2_package" -nt "$t2_cert" ] &&
        { [ "${3-}" = snapshot ] || cmp -s "$t2_source/$1.lisp" "$t2_copy"; }
}

t2_certified() {
    t2_previous=$t2_shared
    [ -s "$t2_previous.cert" ] || return 1
    while IFS= read -r t2_book; do
        t2_current "$t2_book" "$t2_previous" "${2-}" || return 1
        [ "$t2_book" != "$1" ] || return 0
        t2_previous=$t2_acl2/$t2_book
    done < "$t2_order"
    return 1
}

t2_exported() {
    t2_output=$t2_exports/$1
    t2_cert=$t2_acl2/$1.cert
    [ -s "$t2_cert" ] && [ -s "$t2_output.statements" ] &&
        [ -f "$t2_output.program" ] && [ -s "$t2_output.readback" ] &&
        [ ! "$t2_cert" -nt "$t2_output.statements" ] &&
        [ ! "$t2_cert" -nt "$t2_output.program" ] &&
        [ ! "$t2_cert" -nt "$t2_output.readback" ] &&
        t2_readback_agrees "$t2_output.readback"
}

t2_readback_agrees() {
    awk '/^\(readback / { count++ }
         { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
         END { exit (count != 2 || NR < 6 || bad) }' "$1"
}
