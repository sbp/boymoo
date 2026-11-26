#!/bin/sh
# Run from the repository root.
set -eu
SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS
exec sh compiler/proofs/certify.sh --books data \
    arithmetic bits limbs serialization layout tables index attachments attachment-budget attachment-graph packages entry reader strings \
    token-spans datum-spans reader-spans datum-witness reader-witness source \
    static-values constants hash placement buckets sizing builder allocation program-layout package-layout \
    symbol-spelling symbol-identity constant-retention quote-visits rows lists words views image encoded-chunks chunk-retention \
    boxed string-objects numbers datum-spelling constant-writer quote-presence scalar-constants scalar-quotes \
    symbol-emission term-spelling elaboration program-spelling \
    package-agreement source-lookup terminal-agreement program-elaboration quote-elaboration \
    collections imports objects discovery fuel scan-completeness static-bounds builtin-symbols symbol-images \
    map-views constant-roots record-words object-map-agreement static-agreement \
    bucket-views list-images allocation-trace allocation-map value-allocation-trace program-allocation-trace \
    package-allocation-trace build-allocation-trace builder-map front-agreement trace-agreement \
    scalar-agreement builtin-agreement quote-map-agreement \
    home-availability program-home-availability symbol-quotes package-home-availability examples
