#!/bin/sh
# Run from the repository root.
set -eu
SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS
exec sh compiler/proofs/certify.sh --books division \
    arithmetic limbs estimate correction words bitfields ranges emission \
    normalization window long-loop views euclid results memory shifts linked linked-prefix \
    effects left-bitfield cutpoints machine-arithmetic one-limb-loop gcd-loop fast-paths \
    estimate-machine limb-machine shift-machine correction-machine correction-loops \
    divide-flow view-frame window-memory position-machine dispatch divide-return \
    divide-one divide-correctness correction-execution sign-view boxed-gcd \
    boxed-quotient copy short public-immediate position-result normalization-machine \
    long-iteration position-layout long-traversal normalize-view shift-loops right-shift \
    left-shift-call scale-setup unscale long-finish long-scale traversal-invariants divide-long divide-all \
    boxed-entry boxed-divide boxed-return boxed-exact boxed-copies boxed-euclid \
    boxed-setup public-boxed examples
