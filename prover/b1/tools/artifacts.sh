# The source and build locations of the B1 books.

b1_source=prover/b1
b1_order=$b1_source/ORDER
b1_work=build/prover/b1
b1_books=$b1_work/acl2
b1_shared=build/prover/acl2/descent
b1_package=prover/package.lsp
b1_exports=$b1_work/export

b1_tempdir() {
    mkdir -p "$b1_work/tmp" || return 1
    TMPDIR=$PWD/$b1_work/tmp
    export TMPDIR
}

b1_certified() {
    [ -s "$b1_shared.cert" ] || return 1
    prior=$b1_shared.cert
    for candidate in $(cat "$b1_order"); do
        copy=$b1_books/$candidate.lisp
        cert=$b1_books/$candidate.cert
        source=$b1_source/$candidate.lisp
        [ -s "$cert" ] && [ -f "$copy" ] && [ -f "$source" ] &&
            { [ ! "$source" -nt "$cert" ] || cmp -s "$source" "$copy"; } &&
            [ ! "$copy" -nt "$cert" ] && [ ! "$prior" -nt "$cert" ] &&
            [ ! "$b1_package" -nt "$cert" ] || return 1
        [ "$candidate" != "$1" ] || return 0
        prior=$cert
    done
    return 1
}

b1_readback_ok() {
    awk '/^\(readback / { count++ }
         { n = $NF; sub(/\)$/, "", n); if (n !~ /^[0-9]+$/ || $(NF - 1) != n) bad = 1 }
         END { exit (count != 2 || NR < 6 || bad) }' "$1"
}

b1_exported() {
    path=$b1_exports/$1
    cert=$b1_books/$1.cert
    [ -s "$cert" ] && [ -s "$path.statements" ] && [ -f "$path.program" ] &&
        [ -s "$path.readback" ] &&
        [ ! "$cert" -nt "$path.statements" ] && [ ! "$cert" -nt "$path.program" ] &&
        [ ! "$cert" -nt "$path.readback" ] &&
        b1_readback_ok "$path.readback"
}
