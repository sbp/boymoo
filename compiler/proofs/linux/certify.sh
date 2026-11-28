#!/bin/sh
# Run from the repository root. Certifies the books of this directory,
# each after the books it includes.
set -eu

SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS

exec sh compiler/proofs/certify-sets.sh --books linux \
  arithmetic elf load install wrappers
