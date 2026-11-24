# Evaluation of closed terms

The evaluator returns the equality Step for the closed term with
its remaining rewriting budget. An alist stores completed terms
during evaluation. When a closed term occurs more than once, its
stored Step serves later occurrences without charging again for
the completed work.
