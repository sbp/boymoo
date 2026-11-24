# Recipes and derivations

Recipes holds Search and a definition name map. Its derivation calls
configure Search and can return a Step, a failure, or an inherited
request. The association-list and arithmetic derivation requests use
that configuration when adding auxiliary facts. The index and maximum
lemma entry points return Recipes with the resulting state.
