# Arithmetic proof context

Arithmetic supplies the conjunction and modus ponens citations used by
rational scaling and power transport. Proof operations on an Arithmetic
Library use these citations when deriving numeric and rational facts.

`t2-arithmetic-simplify` and `t2-arithmetic-simplify-first` accept the
Proof component and use the Arithmetic reflexive rule and the base
constant rule. Hypothesis queries accept an ordinary hypothesis context
or RulerFacts. A premises query needs RulerFacts or an explicit reply.
