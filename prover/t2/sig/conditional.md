# Conditional equations

`lib` is a Library. Terms and Steps use the representations in the shared
proof signature. Neither operation changes the Library.

| Function | Arguments and result | Failure |
|---|---|---|
| `(t2-conditional-prove lib formula)` | A Step proving `formula` by moving a conditional argument outside an application, or `nil` if the recipe does not apply. | A failure from reading or constructing a proof. |
| `(t2-conditional-default-value lib domain outside-domain)` | A Step equating the left side of `outside-domain` with the conditional that retains that side when the `domain` term holds and gives its default otherwise. `outside-domain` is the equality Step for the default. | A failure from reading or constructing a proof. |
