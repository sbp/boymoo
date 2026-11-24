# L1 library sessions

`l1-api-open` admits distinct library lines into a ground WarrantProof. The session keeps the admitted facts, definitions, primitives, and choice rules. It indexes raw lines after removing trailing line feeds, and stores the helper names used for collision checks. An arithmetic Library supplies entries, facts, and definitions for measure proofs.

The prepared rewrite index holds equation directions, propositions, and structural induction data. Rule lists follow fact order and the order of directions from each fact. Replacing a fact retains its position and updates the affected call heads. The index records failures at their fact positions so that a tactic requiring the index sees the first failure in fact order.

The session also keeps one admitted `earlier` prefix. A growing prefix admits only its suffix. A shorter or divergent prefix starts from the prepared library. A cached parse of the last statement can be used when that statement becomes an earlier line. The session also keeps the table of stored measures for the most recent aid list that a definition used.

The driver uses `l1-api-open` and `l1-api-prove-open` over whole books, one session a book (`prover/OPEN.md`, "The test"). The test of the set is `sh prover/l1/test.sh`.
