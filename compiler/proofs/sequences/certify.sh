#!/bin/sh
# Run from the repository root after certifying the foundations.
set -eu
SBCL_USER_ARGS='--dynamic-space-size 2500'
export SBCL_USER_ARGS
exec sh compiler/proofs/certify.sh --books sequences \
    source execution words views state instructions shifts memory helpers length \
    constructors counts roots returns copy-loops string-copy heap-bounds coerce-dispatch \
    view-calls spine-bounds constructor-calls subseq-counts coerce-copy view-memory list-drop resources \
    length-resume char-resume frame-memory object-memory stack-storage stack-mappings \
    stack-external heap-objects stack-objects stack-static stack-invariant \
    static-roots readonly-call readonly-runtime length-entry symbol-fields cell-memory \
    coerce-list subseq-arithmetic char-entry call-segments byte-words coerce-list-layout \
    subseq-list-fill datum-stop constructor-entry register-only root-prefix cons-views \
    coerce-list-view coerce-type subseq-call-contracts coerce-empty-list subseq-list-layout \
    publication-views subseq-view subseq-source-words publication-map canonical-symbols root-storage \
    publication-memory subseq-entry-view subseq-end subseq-empty-list subseq-list-view subseq-start-call \
    subseq-select coerce-list-resume subseq-entry span-composition publication-heap \
    subseq-immediate-frame coerce-atom-string string-results subseq-numeric-run heap-compose \
    subseq-empty-entry subseq-root-push subseq-size-entry copy-returns \
    coerce-string-resume publication-string cons-records coerce-allocation active-frame \
    constructor-storage
