#!/bin/sh
# Run from the repository root after certifying the foundations.
set -eu
SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS
exec sh compiler/proofs/certify.sh --books assembly \
    layout label-table bits words word-transfers label-order label-ranks bytes \
    static-serialization static-block reader-acceptance index-acceptance placement \
    fields encodings signed-fields register-encodings control-encodings \
    memory-encodings bitfield-encodings shift-effects fetch expansions \
    execution effects expanded-effects link item-decoding image-decoding \
    image-execution expansion-link elf-image macho-header macho-image \
    macho-hash-range macho-hash-pages macho-signature image-loading linux-link macho-link \
    compiled-entry range-checks generated-fields generator-inputs \
    static-symbols static-terms static-data generator-induction generator-acceptance \
    generator-fields image-bounds generator-emission generator-size generator-labels \
    generator-references definition-labels definition-references arity-index \
    index-uniqueness compiler-layout text-inputs bounded-entry source-bounds source-layout \
    machine-invariant macho-handoff darwin-kernel code-protection memory-footprints \
    instruction-footprints checks
