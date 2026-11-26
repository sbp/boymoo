# Run with sh from the repository root.
set -eu

SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS

exec sh compiler/proofs/certify.sh --books allocation \
    instructions words bitfields execution segments memory alignment \
    heap-frames representation publication growth allocators collector-size \
    runtime-contracts locality reservations fast-contracts heap-locality external-list region-tally external-bounds \
    cell-contract saved-words frame-composition memory-keys cons cons-contracts cons-publication published-heap word-writes \
    static-locality unpublished-write cons-fast-contract cons-heap stack-pop cons-tail cons-caller cons-prefix writes-heap \
    mapping large-strings large-return large-contracts large-flow large-publication large-heap placement stack-writes cons-root-heap \
    cons-growth-boundary cons-composition cons-entry-heap \
    large-layout large-caller large-entry large-entry-heap large-map large-map-heap large-composition large-dispatch \
    counterexamples
