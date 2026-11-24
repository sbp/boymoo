# Statement shapes

The shape dispatcher selects proof recipes from the form of the
obligation. Plain recipes are function symbols. Parameterized recipes
carry the additional arguments needed to apply the selected recipe.
`prover/b1/sig/shapes.md` gives the descriptor forms.

Shape and named dispatch can share a recipe symbol. The certificate
interface tries that recipe once. The dispatchers pass the FactIndex
to recipes that look up earlier rules or abstract list signatures.
