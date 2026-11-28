#!/bin/sh
# Run from the repository root. Certifies the books of this directory,
# each after the books it includes.
set -eu

SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS

exec sh compiler/proofs/certify-sets.sh --books assembly \
  layout label-table bits words word-transfers label-order label-ranks \
  bytes static-serialization static-block reader-acceptance \
  index-acceptance placement fields encodings signed-fields \
  register-encodings control-encodings memory-encodings bitfield-encodings \
  shift-effects fetch expansions execution effects expanded-effects link \
  item-decoding image-decoding image-execution expansion-link elf-image \
  macho-header macho-image macho-hash-range macho-hash-pages \
  macho-signature image-loading linux-link macho-link arity-index \
  index-uniqueness machine-invariant macho-handoff darwin-kernel \
  code-protection memory-footprints instruction-footprints
