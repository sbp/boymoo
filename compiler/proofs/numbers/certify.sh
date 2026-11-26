# Run from the repository root after certifying the foundations.
set -eu
export SBCL_USER_ARGS='--dynamic-space-size 2500'

exec sh compiler/proofs/certify.sh --books numbers \
    arithmetic words memory execution representation formulas frames \
    normalization boxing state-views publication fresh-views formula-execution \
    classification reciprocal dispatch type-completion comparison returns \
    formula-trace formula-entry dispatch-return immediate immediate-arithmetic \
    multiplication completion-return box-return memory-invariant object-locality \
    memory-footprint object-publication heap-frame heap-layout frame-composition \
    store-traces register-effects comparison-return immediate-contracts \
    type-dispatch numeric-comparisons static-preservation external-preservation \
    local-heap stack-heap type-effects formula-saves numeric-frames raw-return \
    publication-heap box-contracts complex-contract resource-returns \
    wrapper-frames public-delegation comparison-frame arithmetic-frames \
    arithmetic-dispatch value-stack formula-heap formula-growth formula-contracts \
    arithmetic-returns arithmetic-public arithmetic-paths immediate-delegation rational-contracts \
    primitive-returns inversion-contracts order-contracts order-paths public-stops reciprocal-entry \
    stack-storage formula-storage
