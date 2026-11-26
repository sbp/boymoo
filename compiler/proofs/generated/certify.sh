set -eu

export SBCL_USER_ARGS='--dynamic-space-size 2500'
exec sh compiler/proofs/certify.sh --books generated \
    arithmetic bits steps registers placement memory copy instructions comparisons \
    emission frames views heap-views source stack prologue growth calls copy-path terms tail \
    operand-stack inlines list-views pair-access object-views compound-terms routines \
    lambda-alias fast-arithmetic wide-words addresses indexed-copy indexed-tail root-transfer \
    memory-frame published-writes tail-roots stack-pop stack-prefix operand-registers wide-terms \
    tagged-constants wide-prologue prologue-paths prologue-flow arithmetic-paths \
    object-frame static-frame heap-layout-frame external-frame heap-update heap-disjoint stack-write protected-frame tail-frame \
    tail-return prologue-heap simple-registers scope-order scope-tree lambda-slots lambda-environment \
    immediate-views equal-paths segments prefix-suffix argument-flow argument-evaluation runtime-flow \
    term-flow conditional-flow noncall-terms prologue-state entry-bindings defined-flow resolved-calls \
    capacity growth-edge inline-flow number-flow lambda-flow lambda-result prepared-calls runtime-term conditional-result \
    return-heap compiled-return saved-frame function-body-entry linked-loads linked-control linked-push \
    named-calls tail-call-flow evaluation-tree frame-cuts named-frame-flow tail-frame-flow function-return-flow limit-contract \
    recursive-cut-example refusals
