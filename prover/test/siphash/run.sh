# Checks the hash of prover/siphash.lisp on strings whose values are known.
# From the root of the repository, after sh prover/build.sh:
#
#     sh prover/test/siphash/run.sh
#
# RUNNER names the runner. The first two values are the published ones of
# SipHash-2-4 with the key of the bytes 0 to 15, for the empty string and for
# the fifteen bytes 0 to 14.
set -eu
export LC_ALL=C
export RUNNER=${RUNNER:-build/runner-fast/boymoo-run-fast}
export BOYMOO_FAST_CACHE=${BOYMOO_FAST_CACHE:-build/prover/t1-open/cache}

# One string a line: the sixteen digits expected, a space, and the string as
# a term writes it (spec/formats.md). The first string is empty, and the
# last is 256 times "x".
cases() {
    cat <<'EOF'
726fdb47dd0e0e31
a129ca6149be45e5 \00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E
2ba3e8e9a71148ca a
5dbcfa53aa2007a5 abc
1ff1772171d6215f ACL2::X
02130609caea37eb 12345678
6f1f3578a937b7fc (theorem ACL2::CAR-CONS (COMMON-LISP::EQUAL (COMMON-LISP::CAR (COMMON-LISP::CONS ACL2::X ACL2::Y)) ACL2::X))
46f982a243023666 say \22hi\22\5C\0A\FF
EOF
    awk 'BEGIN { while (n++ < 256) s = s "x"; print "3c0a62b0cdbcef96 " s }'
}

count=$(cases | awk 'END { print NR }')
if ! actual=$(cases |
        awk '{ print "(BOYMOO-PROVER::SIPHASH-HEXDIGEST (COMMON-LISP::QUOTE \"" substr($0, 18) "\"))" }' |
        sh prover/run.sh); then
    echo 'prover/test/siphash/run.sh: the runner did not give every value' >&2
    exit 1
fi

{ cases; printf '%s\n' "$actual"; } | awk -v n="$count" '
    NR <= n { want[NR] = "\"" substr($0, 1, 16) "\""; next }
    { i = NR - n
      if ($0 == want[i]) same++
      else printf "string %d: expected %s, got %s\n", i, want[i], $0 }
    END { printf "siphash: %d of %d strings give the expected value\n", same, n
          exit (same != n || NR != 2 * n) }'
