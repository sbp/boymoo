# Run from the repository root.
set -eu
SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS
exec sh compiler/single/proofs/certify.sh --books primitives \
    words byte-views data-views equality-views equality-work paths machine-ops leaf-routines \
    state-invariants contracts heap-views characters numeric-projections equality-entry \
    compare-bytes byte-loop byte-ranges mapped-data machine-stack scratch-frame \
    numeric-stack-paths boxed-numeric bignum-equality equality-stack \
    equality-dispatch equality-byte-call equality-fields equality-header-views \
    store-views growth-example store-frame boxed-scratch \
    numeric-contract equality-control
