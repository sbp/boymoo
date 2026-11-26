# Run from the repository root after preparing the foundations.
set -eu
SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS
exec sh compiler/proofs/certify.sh --books collection \
    machine words actions comparisons memory segments runtime-layout placement regions \
    forward copy-loop copied-words budget pages scanner slot-calls sweep finish frame \
    frame-protection agreements work closure reachability space queues graph published exactness \
    heap-access rewrite-words live-bytes slot-rewrites \
    forward-calls header-calls fixed-calls forward-placement header-placement header-copy-placement \
    marks source-markers \
    scan-control scan-traversal raw-scan retirement release-call release-pair sweep-rounds sweep-traversal \
    sweep-contents sweep-call entry diagnostic-write diagnostics resource-paths \
    views root-views relocated-views handoff finish-tail cleanup \
    scan-fields scan-domain scan-transition scan-cons root-rewrites scan-memory \
    scan-copy-table scan-invariant-run \
    unmap-placement sweep-readiness sweep-snapshot sweep-input sweep-loop sweep-geometry \
    examples
