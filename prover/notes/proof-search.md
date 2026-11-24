# Fact lookup and proof search

The fact index stores earlier rules and shortening equations in
insertion order within each bucket. The search specializes those
rules, requests the evidence needed for their premises, and uses
specialized tactics and induction for formulas that need more.

Search calls returning a pair carry the updated library. A proof of
an arithmetic premise can add a lemma that is available to the next
premise even when the full arithmetic proof fails.
