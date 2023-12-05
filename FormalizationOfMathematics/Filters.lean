import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Tactic

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
#check atBot

#check Tendsto

example {α β : Type*} (F : Filter α) (G : Filter β) (f : α → β) :
  F.Tendsto f G ↔ F.map f ≤ G := Iff.rfl

/-!

Example : `f : ℝ → ℝ`,

lim (z -> x₀⁺) (f z) = y
-/

#check Set.Icc
#check Set.Ico
#check Set.Ioc
#check Set.Ioo
#check Set.Ici
#check Set.Iic

example (x₀ y : ℝ) (f : ℝ → ℝ) : Prop :=
  let ι : Set.Ici x₀ → ℝ := fun x => x
  let N : Filter (Set.Ici x₀) := (𝓝 x₀).comap ι
  Filter.Tendsto (f ∘ ι) N (𝓝 y)

example (x₀ y : ℝ) (f : ℝ → ℝ) : Prop :=
  let ι : Set.Ici x₀ → ℝ := fun x => x
  let N : Filter ℝ := (𝓝 x₀).comap ι |>.map ι
  Filter.Tendsto f N (𝓝 y)

example (S T : Set α) :
    let ι : S → α := fun x => x
    ι '' (ι ⁻¹' T) = T ∩ S := by simp only [Subtype.image_preimage_coe]

example (F : Filter α) (S : Set α) :
  let ι : S → α := fun x => x
  (F.comap ι).map ι = F ⊓ 𝓟 S := sorry -- exercise.

example (x₀ y : ℝ) (f : ℝ → ℝ) : Prop :=
  Filter.Tendsto f (𝓝 x₀ ⊓ 𝓟 (Set.Ici x₀)) (𝓝 y)


/-!

Composition

-/

-- The composition of two continuous functions is continuous.

example {f : α → β} {g : β → γ} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  constructor
  intro U hU
  rw [Set.preimage_comp]
  apply hf.isOpen_preimage
  apply hg.isOpen_preimage
  assumption

example {f : α → β} {g : β → γ} (F : Filter α) :
  F.map (g ∘ f) = (F.map f).map g := by simp?

example {f : α → β} {g : β → γ} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, Tendsto] at *
  intro x
  dsimp
  specialize hg (f x)
  specialize hf x
  refine le_trans ?_ hg
  rw [Filter.map_le_iff_le_comap] at hf ⊢
  refine le_trans hf ?_
  rw [← Filter.map_le_iff_le_comap, ← Filter.map_map, Filter.map_comap]
  apply Filter.map_mono
  exact inf_le_left

example {f : α → β} {g : β → γ} (F : Filter α) (G : Filter β) (H : Filter γ)
    (h1 : F.Tendsto f G) (h2 : G.Tendsto g H) : F.Tendsto (g ∘ f) H :=
  Tendsto.comp h2 h1

example {f : α → β} {g : β → γ} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt] at *
  intro x
  specialize hf x ; specialize hg (f x)
  exact hg.comp hf


/-!
# Products of Topolgical Spaces
-/

section

variable {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)]

example (α β : Type*) (f : α → β) [TopologicalSpace β] : TopologicalSpace α :=
  TopologicalSpace.induced f inferInstance

def aux (i₀ : ι) : TopologicalSpace ((i : ι) → X i) :=
  TopologicalSpace.induced (fun f =>  f i₀) inferInstance
  -- the topology on the product obtained by "pulling back" the topology on `X i₀`

--instance : TopologicalSpace ((i : ι) → X i) :=
--  ⨅ i : ι, TopologicalSpace.induced (fun f => f i) inferInstance

example (i₀ : ι) : Continuous (fun f : (i : ι) → X i => f i₀) := by
  apply continuous_iInf_dom (i := i₀)
  exact continuous_induced_dom

example {α : Type*} [TopologicalSpace α] (f : (i : ι) → α → X i) (hf : ∀ i, Continuous (f i)) :
    Continuous (fun (a : α) (i : ι) => f i a) := by
  exact continuous_pi hf

#check Filter.hasBasis_pi

example (x : (i : ι) → X i) : (𝓝 x) = (Filter.pi fun i => 𝓝 (x i)) := nhds_pi

#check Filter.hasBasis_pi

example
    -- For each `i : ι`, we fix an indexing type `T i`,
    (T : ι → Type)
    -- a filter `F i : Filter (X i)`,
    (F : (i : ι) → Filter (X i))
    -- a family of subsets of `X i` indexed by `T i`.
    (S : (i : ι) → T i → Set (X i))
    -- and a predicate `P i` on `T i`.
    (P : (i : ι) → T i → Prop)
    -- Assume that each `F i` has a basis given by the `S i` bounded by the predicate `P i`.
    (h : ∀ i, (F i).HasBasis (P i) (S i)) :
    -- Then `Filter.pi F` has a basis given by finite families of
    -- elements contained in the `S i` for `i` satisfying `P i`.
    (Filter.pi F).HasBasis
      (fun A : Set ι × ((i : ι) → T i) => A.1.Finite ∧ ∀ i ∈ A.1, P i (A.2 i))
      (fun A => Set.pi A.1 fun i : ι => S i (A.2 i)) :=
  Filter.hasBasis_pi h

-- Exercise: Look up the definition of `Set.pi` and understand it:
#check Set.pi

-- Let's combine these two observations to describe a nhds basis for the product topology:
example (x : (i : ι) → X i) :
    (𝓝 x).HasBasis
      (fun S => S.1.Finite ∧ ∀ i ∈ S.1, S.2 i ∈ 𝓝 (x i))
      (fun S : (Set ι) × ((i : ι) → Set (X i)) => Set.pi S.1 S.2) := by
  rw [nhds_pi]
  have h : ∀ i : ι, (𝓝 (x i)).HasBasis (fun S => S ∈ 𝓝 (x i)) id := fun i => basis_sets (𝓝 (x i))
  apply Filter.hasBasis_pi h

end
