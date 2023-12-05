import Mathlib

/-!

Examples:
- Metric spaces are uniform spaces
- Topological Groups are uniform spaces

Uniformity lets you formulte what it means for two points to be close to eachother with the following axioms:
1. Any point `x` should be close to itself.
2. If `x` is close to `y` then `y` is close to `x`.
3. If `x` is close to `y` and `y` is close to `z` then `x` is close to `z`.

Idea: The notion of "closeness" on `X` should be modeled as a filter on `X × X`.
-/

#check UniformSpace
