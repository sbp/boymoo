#!/bin/sh
# Run from the repository root.
set -eu
export SBCL_USER_ARGS='--dynamic-space-size 2500'
exec sh compiler/single/proofs/certify.sh --books symbols \
    bits memory package-model layout object-map table hash execution routines loops find contracts \
    query row-data names rehash growth rehash-table rehash-layout grow-call intern chain-layout lookup intern-call \
    publication rooting key-lookup creation examples
