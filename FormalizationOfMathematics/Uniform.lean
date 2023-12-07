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

--#check UniformSpace

#check nhds_basis_uniformity

example {α : Type*} (U : UniformSpace.Core α) : UniformSpace α := UniformSpace.ofCore U
example {α : Type*} (U : UniformSpace.Core α) : TopologicalSpace α :=
  (UniformSpace.ofCore U).toTopologicalSpace

open scoped Topology Uniformity

example {α : Type*} [UniformSpace α] (x : α) :
  (𝓝 x).HasBasis (ι := Set α)
    (fun S => { p | p.fst = x ∧ p.snd ∈ S } ∈ 𝓤 α)
    id := by
  sorry

/-!

(Pseudo)Metric Spaces

-/

#check nhds_basis_uniformity

#check PseudoMetricSpace

#check Metric.nhds_basis_ball

example {α : Type*} [PseudoMetricSpace α] (x : α) :
    (𝓝 x).HasBasis (ι := ℝ) (fun ε => 0 < ε) (fun ε => Metric.ball x ε) :=
  Metric.nhds_basis_ball

example {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β)
    (H : ∀ (x : α) (ε : ℝ), 0 < ε → ∃ (δ : ℝ), 0 < δ ∧
        ∀ (y : α), dist y x < δ → dist (f y) (f x) < ε) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  specialize H x
  change Filter.Tendsto f _ _
  have hx := Metric.nhds_basis_ball (x := x)
  have hfx := Metric.nhds_basis_ball (x := f x)
  rw [hx.tendsto_iff hfx]
  exact H

/-!
Completions
-/

variable (α : Type*) [UniformSpace α]

/-

Intuition: Suppose that `X` is a metric space and `Y` is a complete metric space

Let `f : X → Y` be a function satisfying ...

Define `Xhat` = "the space of limits of cauchy sequenecs on `X`"

The map `ι : X → Xhat` is the function sending `x` to `lim x`.
The map `Xhat → Y` is going to be the function
`lim x_n` maps to `lim (f x_n)`.
-/

example : Type _ := UniformSpace.Completion α

noncomputable

example {β : Type*} [UniformSpace β] (f : α → β) :
  UniformSpace.Completion α → β := UniformSpace.Completion.extension f

example (x : α) : UniformSpace.Completion α := x

example {β : Type*} [UniformSpace β] [SeparatedSpace β] (f : α → β)
    (hf : UniformContinuous f)
    (x : α) :
    (UniformSpace.Completion.extension f) x = f x :=
  UniformSpace.Completion.extension_coe hf x

example {β : Type*} [UniformSpace β] [T2Space β] (f g : UniformSpace.Completion α → β)
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : α, f x = g x) : f = g :=
  UniformSpace.Completion.ext hf hg h

example {β : Type*} [UniformSpace β] [CompleteSpace β] (f : α → β) :
    UniformContinuous (UniformSpace.Completion.extension f) :=
  UniformSpace.Completion.uniformContinuous_extension

-- The relationship between cauchy sequences and cauchy filters
example (α : Type*) [MetricSpace α] (f : ℕ → α) : Prop :=
  Cauchy (Filter.atTop.map f)
