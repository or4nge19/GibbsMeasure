/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.LinearAlgebra.FreeModule.SubgroupRange
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.LinearIndependentSeparated
public import GibbsMeasure.Specification.InvariantDecomposition

/-!
# The ergodic decomposition for a subgroup of the shifts (Georgii, the remark below (14.18))

Georgii states Chapter 14 for the full shift group `Θ = (θ_i)_{i ∈ S}` and then remarks, right
below Corollary (14.18):

> Theorem (14.17) and the preceding corollary still hold when the shift-group `Θ` is replaced by
> any finitely generated abelian subgroup of `T` which contains a non-trivial shift. This follows
> from the fact that Theorems (14.5), (14.10), and (14.15) as well as Proposition (14.9) remain
> valid under this replacement.

That remark is what the last statement of Theorem (18.25) — `|ex 𝒢_Θ̃(βΦ)| ≥ N` for the proper
subgroup `Θ̃ = ⋂_n Θ̃_n` of shifts preserving every member of the partition — appeals to, and it is
what this file supplies.

The tree's proofs of (14.9), (14.15), (14.17) and (14.18) are already stated for an arbitrary
countable subgroup `Θ ≤ T`, given two inputs:

* `Θ` moves every finite volume off itself (Proposition (14.9)) — `ErgodicGibbs.lean` has this
  for any subgroup containing a shift of infinite order
  (`exists_disjoint_sites_preimage_of_shift_mem`), which is exactly Georgii's "contains a
  non-trivial shift";
* a `(𝓟_Θ, 𝓘)`-kernel (Theorem (14.10)) — `InvariantDecomposition.lean` builds one for the shift
  group of the whole site group, from `isPAKernel_ergodicKernel`, which is stated for *any*
  countable abelian group acting measurably on a standard Borel space along a regular Følner
  sequence.

So the only genuinely missing piece was the second input for a subgroup, and it is obtained here
by feeding `isPAKernel_ergodicKernel` the action of `G` on `S → E` through an additive
homomorphism `ι : G →+ S`, `g +ᵥ ω = θ_{ι g} ω` (`AddAction.compHom`). The subgroup is then the
group `Θ` of shifts along the range of `ι`, given by the characterisation
`hΘ : τ ∈ Θ ↔ ∃ g, θ_{ι g} = τ`; the Følner sequence lives in `G`, not in `Θ`, which is what
makes this usable: for `S = ℤ^d` and a subgroup of finite index — Georgii's `Θ̃`, free abelian of
rank `d` — one takes `G = ℤ^d` with the cubes of `exists_monotone_regular_foelner_cube` and `ι` a
basis of the subgroup, and no Følner sequence inside the subgroup has to be built.

## Main results

* `exists_isPAKernel_invariantFields_of_shift_range` — **Theorem (14.10) for the subgroup**: a
  `(𝓟_Θ, 𝓘)`-kernel for the group `Θ` of shifts along the range of `ι`.
* `exists_disjoint_sites_preimage_of_shift_range` — **Proposition (14.9) for the subgroup**: `Θ`
  moves every finite volume off itself as soon as some `ι g` has infinite additive order.
* `le_encard_extremePoints_invariantG_of_shift_range_iff` — **Corollary (14.18) for the
  subgroup**: `|ex 𝒢_Θ(γ)| ≥ N` iff `𝒢_Θ(γ)` contains `N` linearly independent elements.
* `le_encard_extremePoints_invariantG_of_shift_range_of_separated` — the subgroup form of
  `le_encard_extremePoints_invariantG_shiftGroup_of_separated`: `N` `Θ`-invariant Gibbs measures
  separated by a family of events (the `i`-th carries the `i`-th event and misses the others,
  as mutually singular measures with disjoint supporting events do) give `|ex 𝒢_Θ(γ)| ≥ N`.
* `le_encard_extremePoints_invariantG_of_shift_range_of_separated_int` — the same on `ℤ^d`, with
  the cubes as Følner sequence, which is the form Theorem (18.25) consumes.

Intended home: `GibbsMeasure/Specification/InvariantDecomposition.lean`, next to the shift-group
corollaries of (14.10), (14.17), (14.18) and (14.25); kept in a separate module only so that the
many importers of that file are not rebuilt.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology Pointwise symmDiff

namespace MeasureTheory.GibbsMeasure

/-! ### Shifts along the range of an additive homomorphism -/

section ShiftRange

variable {S E G : Type*} [MeasurableSpace E] [AddCommGroup S] [AddCommGroup G]
  {ι : G →+ S} {Θ : Subgroup (Transformation S E)}

/-- A group of shifts along the range of `ι : G →+ S` is countable as soon as `G` is: Georgii's
`Θ̃` is countable, which is his Remark (14.3)(2) for the subgroup. -/
lemma countable_of_forall_mem_iff_exists_shift [Countable G]
    (hΘ : ∀ τ : Transformation S E, τ ∈ Θ ↔ ∃ g : G, shift E (ι g) = τ) : Countable Θ := by
  have hsub : (Θ : Set (Transformation S E)) ⊆ Set.range fun g : G ↦ shift E (ι g) :=
    fun τ hτ ↦ (hΘ τ).1 hτ
  exact ((Set.countable_range fun g : G ↦ shift E (ι g)).mono hsub).to_subtype

/-- **Georgii, Proposition (14.9) for a subgroup of the shifts.** The group of shifts along the
range of `ι` moves every finite volume off itself as soon as some `ι g` has infinite additive
order — Georgii's "any countable subgroup of `T` which contains a (non-trivial) shift". -/
lemma exists_disjoint_sites_preimage_of_shift_range
    (hΘ : ∀ τ : Transformation S E, τ ∈ Θ ↔ ∃ g : G, shift E (ι g) = τ)
    {g₀ : G} (hg₀ : ¬ IsOfFinAddOrder (ι g₀)) (Λ : Finset S) :
    ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S) :=
  exists_disjoint_sites_preimage_of_shift_mem hg₀ ((hΘ _).2 ⟨g₀, rfl⟩) Λ

variable [Countable S] [StandardBorelSpace E] [Countable G] [DecidableEq G]

attribute [local instance] shiftAddAction measurableConstVAdd_shift

variable {F : ℕ → Finset G} {C : ℝ≥0∞}

/-- **Georgii, Theorem (14.10), first assertion, for a subgroup of the shifts** — the remark below
Corollary (14.18). Let `Θ` be the group of shifts `θ_{ι g}` along the range of an additive
homomorphism `ι : G →+ S` from a countable abelian group carrying an increasing regular Følner
sequence (the cubes, when `G = ℤ^d`). Then there is a `(𝓟_Θ, 𝓘)`-kernel as soon as `𝓟_Θ ≠ ∅`.

The proof is `isPAKernel_ergodicKernel` for the action `g +ᵥ ω = θ_{ι g} ω` of `G` on
configuration space (`AddAction.compHom`), whose invariant σ-algebra is `𝓘 = invariantEvents Θ`
and whose invariant probability measures are `𝓟_Θ`; the Følner sequence is the one of `G`, so
none has to be built inside `Θ`. -/
theorem exists_isPAKernel_invariantFields_of_shift_range
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hΘ : ∀ τ : Transformation S E, τ ∈ Θ ↔ ∃ g : G, shift E (ι g) = τ)
    (hne' : (invariantFields Θ).Nonempty) :
    ∃ π : Kernel[invariantEvents Θ] (S → E) (S → E), IsMarkovKernel π ∧
      IsPAKernel (invariantFields Θ) (invariantEvents Θ) π := by
  let _ : AddAction G (S → E) := AddAction.compHom _ ι
  have : MeasurableConstVAdd G (S → E) := ⟨fun g ↦ (shift E (ι g)).measurable_toFun⟩
  -- Georgii (14.2) for `Θ`: the invariant σ-algebra of the `G`-action is `𝓘 = invariantEvents Θ`
  have hI : MeasurableSpace.smulInvariants (Multiplicative G) (S → E) = invariantEvents Θ := by
    refine (MeasurableSpace.ext fun A ↦ ?_).symm
    rw [measurableSet_invariantEvents, MeasurableSpace.measurableSet_smulInvariants]
    refine and_congr_right fun _ ↦
      ⟨fun h c ↦ h _ ((hΘ _).2 ⟨Multiplicative.toAdd c, rfl⟩), ?_⟩
    rintro h τ hτ
    obtain ⟨g, rfl⟩ := (hΘ τ).1 hτ
    exact h (Multiplicative.ofAdd g)
  -- Georgii (14.1) for `Θ`: the invariant random fields of the `G`-action are `𝓟_Θ`
  have hP : ∀ ν : Measure (S → E), ν ∈ invariantFields Θ ↔
      IsProbabilityMeasure ν ∧ VAddInvariantMeasure G (S → E) ν := by
    intro ν
    rw [mem_invariantFields_iff]
    refine and_congr_right fun _ ↦ ?_
    have h : VAddInvariantMeasure G (S → E) ν ↔
        ∀ g : G, MeasurePreserving (g +ᵥ · : (S → E) → S → E) ν ν :=
      (vaddInvariantMeasure_tfae G ν).out 1 7
    rw [h]
    refine ⟨fun hτ g ↦ hτ (shift E (ι g)) ((hΘ _).2 ⟨g, rfl⟩), fun hg τ hτ ↦ ?_⟩
    obtain ⟨g, rfl⟩ := (hΘ τ).1 hτ
    exact hg g
  obtain ⟨π, hMarkov, hπ⟩ :=
    exists_isPAKernel_of_vaddInvariant G (S → E) hFol hF hne hC hC' hP hne'
  refine ⟨π.comap id (measurable_id'' hI.le), inferInstance, fun μ hμ A hA ↦ ?_, hπ.2⟩
  have hce : μ[A.indicator (fun _ ↦ (1 : ℝ)) | invariantEvents Θ] =
      μ[A.indicator (fun _ ↦ (1 : ℝ)) |
        MeasurableSpace.smulInvariants (Multiplicative G) (S → E)] := by rw [hI]
  rw [hce]
  exact hπ.1 μ hμ A hA

/-- **Georgii, Corollary (14.18) for a subgroup of the shifts** — the remark below (14.18):
`|ex 𝒢_Θ(γ)| ≥ N` iff `𝒢_Θ(γ)` contains `N` linearly independent elements, for the group `Θ` of
shifts along the range of `ι : G →+ S`, provided some `ι g₀` has infinite additive order
(Georgii's "contains a non-trivial shift"). -/
theorem le_encard_extremePoints_invariantG_of_shift_range_iff {γ : Specification S E}
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hΘ : ∀ τ : Transformation S E, τ ∈ Θ ↔ ∃ g : G, shift E (ι g) = τ)
    {g₀ : G} (hg₀ : ¬ IsOfFinAddOrder (ι g₀)) (N : ℕ) :
    (N : ℕ∞) ≤ ((invariantG γ Θ).extremePoints ℝ≥0∞).encard ↔
      ∃ μ : Fin N → Measure (S → E), (∀ i, μ i ∈ invariantG γ Θ) ∧ LinearIndependent ℝ≥0∞ μ := by
  have : Countable Θ := countable_of_forall_mem_iff_exists_shift hΘ
  rcases (invariantG γ Θ).eq_empty_or_nonempty with h | hne'
  · rw [h, extremePoints_empty, encard_empty]
    constructor
    · intro hN
      have hN0 : N = 0 := by exact_mod_cast nonpos_iff_eq_zero.1 hN
      subst hN0
      exact ⟨Fin.elim0, fun i ↦ i.elim0, linearIndependent_empty_type⟩
    · rintro ⟨μ, hμ, -⟩
      cases N with
      | zero => simp
      | succ n => exact absurd (hμ 0) id
  · obtain ⟨π, hMarkov, hπ⟩ := exists_isPAKernel_invariantFields_of_shift_range hFol hF hne hC hC'
      hΘ ⟨hne'.some, hne'.some_mem.2⟩
    exact le_encard_extremePoints_invariantG_iff
      (exists_disjoint_sites_preimage_of_shift_range hΘ hg₀) hπ N

/-- **`N` `Θ`-invariant Gibbs measures separated by a family of events give `|ex 𝒢_Θ(γ)| ≥ N`**,
for the group `Θ` of shifts along the range of `ι : G →+ S`. The `i`-th measure carries the
`i`-th event and misses the others, so the family is linearly independent over `ℝ≥0∞`
(`linearIndependent_of_measure_eq_one_of_measure_eq_zero`), and Corollary (14.18) for the
subgroup turns that into the count.

This is the subgroup form of `le_encard_extremePoints_invariantG_shiftGroup_of_separated`, and
the general fact behind the last statement of Georgii's Theorem (18.25). -/
theorem le_encard_extremePoints_invariantG_of_shift_range_of_separated {γ : Specification S E}
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hΘ : ∀ τ : Transformation S E, τ ∈ Θ ↔ ∃ g : G, shift E (ι g) = τ)
    {g₀ : G} (hg₀ : ¬ IsOfFinAddOrder (ι g₀))
    {N : ℕ} {ρ : Fin N → Measure (S → E)} {A : Fin N → Set (S → E)}
    (hprob : ∀ i, IsProbabilityMeasure (ρ i))
    (hgibbs : ∀ i, Specification.IsGibbsMeasure γ (ρ i))
    (hinv : ∀ (i : Fin N) (g : G), MeasurePreserving (shift E (ι g)).toFun (ρ i) (ρ i))
    (hself : ∀ i, ρ i (A i) = 1) (hother : ∀ i j, i ≠ j → ρ j (A i) = 0) :
    (N : ℕ∞) ≤ ((invariantG γ Θ).extremePoints ℝ≥0∞).encard :=
  (le_encard_extremePoints_invariantG_of_shift_range_iff hFol hF hne hC hC' hΘ hg₀ N).2
    ⟨ρ, fun i ↦ mem_invariantG.2 ⟨hprob i, hgibbs i,
      smulInvariantMeasure_iff_forall_measurePreserving.2 fun τ hτ ↦ by
        obtain ⟨g, rfl⟩ := (hΘ τ).1 hτ; exact hinv i g⟩,
      linearIndependent_of_measure_eq_one_of_measure_eq_zero hself hother⟩

end ShiftRange

/-! ### The subgroups of the shifts of `ℤ^d` -/

section Cube

variable {d E G : Type*} [Finite d] [MeasurableSpace E]
  [StandardBorelSpace E] [AddCommGroup G] [Countable G] [DecidableEq G]
  {ι : G →+ (d → ℤ)} {Θ : Subgroup (Transformation (d → ℤ) E)}

/-- **The last statement of Georgii's Theorem (18.25), as a general fact about `ℤ^d`**: `N`
`Θ̃`-invariant Gibbs measures separated by a family of events give `|ex 𝒢_Θ̃(γ)| ≥ N`, for the
group `Θ̃` of shifts along the range of an additive homomorphism `ι : G →+ ℤ^d` from a countable
abelian group with a regular Følner sequence.

Georgii's `Θ̃ = ⋂_n Θ̃_n` of (18.25) is a subgroup of `ℤ^d` containing `2ℤ^d`, hence free abelian
of rank `d`, hence the range of an injective `ι : ℤ^d →+ ℤ^d`; the Følner sequence is then the
cube sequence `exists_monotone_regular_foelner_cube` of `G = ℤ^d`, and no Følner sequence inside
`Θ̃` is needed. -/
theorem le_encard_extremePoints_invariantG_of_shift_range_of_separated_int
    {γ : Specification (d → ℤ) E} {F : ℕ → Finset G} {C : ℝ≥0∞}
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hΘ : ∀ τ : Transformation (d → ℤ) E, τ ∈ Θ ↔ ∃ g : G, shift E (ι g) = τ)
    {g₀ : G} (hg₀ : ¬ IsOfFinAddOrder (ι g₀))
    {N : ℕ} {ρ : Fin N → Measure ((d → ℤ) → E)} {A : Fin N → Set ((d → ℤ) → E)}
    (hprob : ∀ i, IsProbabilityMeasure (ρ i))
    (hgibbs : ∀ i, Specification.IsGibbsMeasure γ (ρ i))
    (hinv : ∀ (i : Fin N) (g : G), MeasurePreserving (shift E (ι g)).toFun (ρ i) (ρ i))
    (hself : ∀ i, ρ i (A i) = 1) (hother : ∀ i j, i ≠ j → ρ j (A i) = 0) :
    (N : ℕ∞) ≤ ((invariantG γ Θ).extremePoints ℝ≥0∞).encard :=
  le_encard_extremePoints_invariantG_of_shift_range_of_separated hFol hF hne hC hC' hΘ hg₀
    hprob hgibbs hinv hself hother

/-- **The last statement of Georgii's Theorem (18.25) for an arbitrary subgroup of the shifts of
`ℤ^d`**, and his remark below Corollary (14.18) in the form it is used there: `N` Gibbs measures
invariant under the shifts along an additive subgroup `H ≤ ℤ^d` and separated by a family of
events give `|ex 𝒢_Θ(γ)| ≥ N`, where `Θ = {θ_a : a ∈ H}`.  The only requirement on `H` is that it
be non-trivial — Georgii's "contains a non-trivial shift".

No Følner sequence inside `H` is needed: `H`, a subgroup of a lattice, is free of some finite rank
`m` (`AddSubgroup.exists_addMonoidHom_fin_range_eq`), so it is the range of a homomorphism
`ℤ^m →+ ℤ^d`, and the Følner sequence is the cube sequence of `ℤ^m`. -/
theorem le_encard_extremePoints_invariantG_of_shift_subgroup_of_separated_int
    {γ : Specification (d → ℤ) E} {H : AddSubgroup (d → ℤ)}
    {Θ : Subgroup (Transformation (d → ℤ) E)}
    (hΘ : ∀ τ : Transformation (d → ℤ) E, τ ∈ Θ ↔ ∃ a ∈ H, shift E a = τ)
    {a₀ : d → ℤ} (ha₀ : a₀ ∈ H) (ha₀' : a₀ ≠ 0)
    {N : ℕ} {ρ : Fin N → Measure ((d → ℤ) → E)} {A : Fin N → Set ((d → ℤ) → E)}
    (hprob : ∀ i, IsProbabilityMeasure (ρ i))
    (hgibbs : ∀ i, Specification.IsGibbsMeasure γ (ρ i))
    (hinv : ∀ (i : Fin N), ∀ a ∈ H, MeasurePreserving (shift E a).toFun (ρ i) (ρ i))
    (hself : ∀ i, ρ i (A i) = 1) (hother : ∀ i j, i ≠ j → ρ j (A i) = 0) :
    (N : ℕ∞) ≤ ((invariantG γ Θ).extremePoints ℝ≥0∞).encard := by
  classical
  have : Fintype d := Fintype.ofFinite d
  obtain ⟨m, f, hf⟩ := H.exists_addMonoidHom_fin_range_eq
  obtain ⟨F, C, hF, hne, hFol, hC, hC', -⟩ := exists_monotone_regular_foelner_cube (ι := Fin m)
  have hmem : ∀ c : Fin m → ℤ, f c ∈ H := fun c ↦ by
    have : f c ∈ (H : Set (d → ℤ)) := hf ▸ Set.mem_range_self c
    exact this
  obtain ⟨c₀, hc₀⟩ : a₀ ∈ Set.range ⇑f := by rw [hf]; exact ha₀
  refine le_encard_extremePoints_invariantG_of_shift_range_of_separated (ι := f)
    hFol hF hne hC hC' (fun τ ↦ (hΘ τ).trans ⟨?_, ?_⟩)
    (g₀ := c₀) (not_isOfFinAddOrder_of_isAddTorsionFree (hc₀ ▸ ha₀'))
    hprob hgibbs (fun i c ↦ hinv i (f c) (hmem c)) hself hother
  · rintro ⟨a, haH, rfl⟩
    obtain ⟨c, rfl⟩ : a ∈ Set.range ⇑f := by rw [hf]; exact haH
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨f c, hmem c, rfl⟩

end Cube

end MeasureTheory.GibbsMeasure

end
