import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.PseudoMetric

#check Filter

variable (α : Type*)
#synth (CompleteLattice (Filter α))

open Filter

example (S : Set α) : Filter α := 𝓟 S

example : 𝓟 (∅ : Set α) = ⊥ := by simp

example {X Y : Type*} (f : X → Y) (F : Filter X) : Filter Y :=
  F.map f -- intuitively, this is the image of `F` under `f`.

def Filter.map' {X Y : Type*} (f : X → Y) (F : Filter X) : Filter Y where
  sets := { S | f ⁻¹' S ∈ F }
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

example {X Y : Type*} (f : X → Y) (F : Filter X) :
  F.map' f = F.map f := rfl

example {X Y : Type*} (f : X → Y) (S : Set X) :
    (𝓟 S).map f = 𝓟 (f '' S) := by simp only [map_principal]

example {X Y : Type*} (f : X → Y) (F : Filter Y) : Filter X :=
  F.comap f

example {X Y : Type*} (f : X → Y) (S : Set Y) :
    (𝓟 S).comap f = 𝓟 (f ⁻¹' S) := by simp only [comap_principal]

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    F.map f ≤ G ↔ F ≤ G.comap f :=
  map_le_iff_le_comap



/-!
# REMARK

An "ULTRAFILTER" is a minimal filter (w.r.t. partial order
as defined in mathlib) which is not equal to ⊥.
-/

#check Ultrafilter


/-!
# Continuity
-/

open Topology
variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

example (x : X) : Filter X := 𝓝 x

def ContinuousAt' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) :
    Prop :=
  (𝓝 x).map f ≤ 𝓝 (f x)

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) :
  ContinuousAt f x = ContinuousAt' f x := rfl

example (h : ∃ n : ℕ, n = n+2) : False := by
  obtain ⟨n,h⟩:= h
  simp at h

noncomputable
def hh (h : ∃ n : ℕ, n = n+2) : ℕ := by
  exact h.choose

#print axioms hh

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ (∀ x : X, ContinuousAt f x) := by
  constructor
  · intro hf
    intro x
    intro U hU
    simp only [mem_map]
    simp [mem_nhds_iff] at hU ⊢
    obtain ⟨V,hV1,hV2,hV3⟩ := hU
    refine ⟨f ⁻¹' V, ?_, hf.isOpen_preimage _ hV2, hV3⟩
    apply Set.preimage_mono
    assumption
  · intro hf
    constructor
    intro U hU
    by_cases h : Set.Nonempty (f ⁻¹' U)
    · sorry -- exercise
    · have : f ⁻¹' U = ∅ := by exact Set.not_nonempty_iff_eq_empty.mp h
      rw [this]
      exact isOpen_empty

example (f : ℝ → ℝ)
    (h : ∀ (x : ℝ) (ε : ℝ), 0 < ε → ∃ (δ : ℝ), 0 < δ ∧ ∀ (y : ℝ), |y - x| < δ → |f y - f x| < ε) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  specialize h x
  change Filter.Tendsto f _ _
  have h1 : (𝓝 x).HasBasis _ _ := Metric.nhds_basis_ball
  have h2 : (𝓝 (f x)).HasBasis _ _ := Metric.nhds_basis_ball
  rw [Filter.HasBasis.tendsto_iff h1 h2]
  dsimp [Metric.ball]
  have : ∀ x y : ℝ, dist x y = |x - y| := by intros ; rfl
  simp [this]
  exact h

/-!
# Tends To

"Tends to" is a way to talk about limits in topology is a way to talk about limits.
-/

/-!
Limits of real numbers

Suppose that `f : ℝ → ℝ` is a function.
And I have a point `x y : ℝ`,
What does it mean to say that

`lim_{z -> x} f z = y`.

If `f` is continuous at `x`:
This means that forall `ε > 0` there exists `δ > 0` such that
`|z - x| < δ → |f z - y| < ε`.

I can write this down as saying that `(𝓝 x).map f ≤ 𝓝 y`.

-/

/-!
Limits of sequences

`f : ℕ → ℝ`.

`lim (n -> ∞) (f n) = y`.

We can formulate this by saying that

`(atTop : Filter ℕ).map f ≤ 𝓝 y`

We can similarly talk about `lim (n -> ∞) (f n) = ∞` by writing
`(atTop : Filter ℕ).map f ≤ (atTop : Filter ℝ)`
-/

#check atTop


#check Tendsto
