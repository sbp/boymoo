#!/bin/sh
# Run from the repository root. Certifies the books of this directory,
# each after the books it includes.
set -eu

SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS

exec sh compiler/proofs/certify-sets.sh --books data \
  arithmetic bits limbs serialization layout tables index attachments \
  attachment-budget attachment-graph packages reader strings token-spans \
  datum-spans reader-spans datum-witness reader-witness static-values \
  constants hash placement buckets sizing builder allocation \
  program-layout package-layout constant-retention quote-visits rows lists \
  words views image encoded-chunks chunk-retention boxed string-objects \
  numbers collections imports objects discovery fuel scan-completeness \
  static-bounds builtin-symbols symbol-images map-views constant-roots \
  record-words object-map-agreement static-agreement bucket-views \
  list-images allocation-trace allocation-map value-allocation-trace \
  program-allocation-trace package-allocation-trace build-allocation-trace \
  builder-map
