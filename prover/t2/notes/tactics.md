# Termination tactic state

RulerFacts carries signed tests and evidence Steps. Learning a Step
also stores its consequences in order. Arithmetic and Countdown use
the request protocol in `prover/t2/sig/arithmetic.md` to query this evidence
and resume a recipe with the returned Library and RulerFacts.

The Generator attempt functions return the resulting Generator with the
proof or failure. This allows the caller to try selector, dyadic, and
floor-split recipes with the available measure information and lemmas.

A Proof context used for selector completion needs an axiom citation
rule. An attempt to use that rule with a bare Proof yields a failure.
