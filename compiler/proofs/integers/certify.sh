#!/bin/sh
# Run from the repository root after certifying the foundations.
set -eu

SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS
exec sh compiler/proofs/certify.sh --books integers \
    words limbs signed-words representation bits ash-immediate \
    runtime-image ash-right-branch logxor-immediate ash-left-branch \
    ash-count entry-tests logxor-path runtime-examples zero-shift
