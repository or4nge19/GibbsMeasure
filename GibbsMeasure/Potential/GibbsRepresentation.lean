/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.ProductMeasure
public import GibbsMeasure.Potential.NearestNeighbour
public import GibbsMeasure.Potential.Quasilocal
public import GibbsMeasure.Potential.Space
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Georgii, Theorem (2.30): the Gibbs representation theorem

Let `λ` be an a priori measure on the single-spin space `(E, 𝓔)` and let `ρ = (ρ_Λ)` be a positive
quasilocal pre-modification with `λ_Λ ρ_Λ = 1` for every finite volume `Λ`.  Then for each
`a ∈ E` there is a *unique* `λ`-admissible gas potential `Φ^a` with vacuum state `a` such that
`ρ = ρ^{Φ^a}`.  If moreover `log ρ_Λ` is bounded, then for each `α ∈ 𝓟(E, 𝓔)` there is a *unique*
uniformly convergent `α`-normalized `λ`-admissible potential `Φ^α` with `ρ = ρ^{Φ^α}`.  In
particular every positive quasilocal `λ`-specification is Gibbsian.

The whole combinatorial part of Georgii's proof is carried out at a fixed *reference
configuration* `ζ` — the interaction `Φ^ζ_A = -p_A log ρ_A` of `Potential.gasPotentialCfg` — and
the two assertions of (2.30) are the two ways of specialising it: the gas potential `Φ^a` is the
constant reference configuration `a`, and the `α`-normalized potential `Φ^α` is the average of
`Φ^ζ` over the product measure `α^S` (`Potential.normalizedPotential_eq_integral`).

## Main results

* `Potential.exists_unique_isGasPotential_sigmaFinitePremodifierNorm_eq`: Theorem (2.30), first
  assertion.
* `Potential.exists_unique_isNormalized_sigmaFinitePremodifierNorm_eq`: Theorem (2.30), second
  assertion, for a general normalizing measure `α ∈ 𝓟(E, 𝓔)`.
* `Potential.eq_zero_of_isGasPotential`, `Potential.eq_zero_of_isNormalized`: Theorem (2.35)(a),
  for a Dirac measure and for a general `α` with a uniformly convergent potential.
* `Potential.exists_unique_isNormalized_of_finite`: Corollary (2.31), for a finite single-spin
  space, where Georgii's boundedness hypothesis is automatic and the Hamiltonians are quasilocal.
* `Potential.normalizedPotential_eq_zero_of_not_isClique`: Corollary (2.32), the potential of a
  Markovian pre-modification is a nearest-neighbour potential.

Georgii's kernels `α_Λ` and `α_{S∖C}` of Remark (1.25) are `Potential.avgOn` and
`Potential.avgOff`; they are averages against the infinite product measure `α^S`, and the
identities `α_{i} α_{S∖(C ∪ {i})} = α_{S∖C}`, `α_{S∖Λ} α_{i} = α_{S∖Λ}` and `α_B α_{i} = α_B`
that drive the proof all come from `MeasureTheory.Measure.map_update_prod_infinitePi`:
resampling one coordinate of an i.i.d. product from an independent copy does not change the law.
-/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E]

/-! ### The vacuum configurations `ω_C a_{S∖C}` -/

/-- The configuration which agrees with `η` on `C` and with the *reference configuration* `ζ`
off `C`; Georgii's `ω_C ζ_{S∖C}`.

Georgii's operator `p_A` in the proof of (2.30) is built from the kernels `α_{S∖C}` of Remark
(1.25).  For a Dirac a priori measure `α = δ_a` these are the evaluations at the constant
reference configuration `a`; for a general `α ∈ 𝓟(E, 𝓔)` they average over the configurations
`ω_C ζ_{S∖C}` with `ζ` distributed according to the product measure `α^S`.  The combinatorial
part of the proof of (2.30) is therefore carried out for an arbitrary reference configuration,
and the potential normalized by `α` is obtained by integrating over `ζ`. -/
def vacuumCfg (ζ : S → E) (C : Finset S) (η : S → E) : S → E := fun i ↦ if i ∈ C then η i else ζ i

omit [MeasurableSpace E] in
@[simp] lemma vacuumCfg_apply_of_mem {ζ : S → E} {C : Finset S} {η : S → E} {i : S} (hi : i ∈ C) :
    vacuumCfg ζ C η i = η i := by simp [vacuumCfg, hi]

omit [MeasurableSpace E] in
@[simp] lemma vacuumCfg_apply_of_notMem {ζ : S → E} {C : Finset S} {η : S → E} {i : S}
    (hi : i ∉ C) : vacuumCfg ζ C η i = ζ i := by simp [vacuumCfg, hi]

omit [MeasurableSpace E] in
@[simp] lemma vacuumCfg_empty (ζ η : S → E) : vacuumCfg ζ ∅ η = ζ := by funext i; simp [vacuumCfg]

omit [MeasurableSpace E] in
lemma vacuumCfg_congr {ζ : S → E} {C : Finset S} {x y : S → E} (h : ∀ i ∈ C, x i = y i) :
    vacuumCfg ζ C x = vacuumCfg ζ C y := by
  funext i
  by_cases hi : i ∈ C
  · simp [vacuumCfg, hi, h i hi]
  · simp [vacuumCfg, hi]

omit [MeasurableSpace E] in
/-- `vacuumCfg ζ C η` agrees with the reference configuration off `C`. -/
lemma vacuumCfg_eqOn_compl (ζ : S → E) (C : Finset S) (η : S → E) :
    ∀ i ∉ C, vacuumCfg ζ C η i = ζ i := fun _ hi ↦ vacuumCfg_apply_of_notMem hi

omit [MeasurableSpace E] in
/-- `vacuumCfg ζ C` only reads the coordinates in `C`. -/
lemma dependsOn_vacuumCfg (ζ : S → E) (C : Finset S) :
    DependsOn (fun η : S → E ↦ vacuumCfg ζ C η) (C : Set S) :=
  fun _ _ h ↦ vacuumCfg_congr fun i hi ↦ h i (by exact_mod_cast hi)

lemma measurable_vacuumCfg (ζ : S → E) (C : Finset S) :
    Measurable (fun η : S → E ↦ vacuumCfg ζ C η) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i ∈ C
  · simpa [vacuumCfg, hi] using measurable_pi_apply (X := fun _ : S ↦ E) i
  · simp [vacuumCfg, hi]

/-- `vacuumCfg ζ C η` is measurable in the reference configuration `ζ`. -/
lemma measurable_vacuumCfg_ref (C : Finset S) (η : S → E) :
    Measurable (fun ζ : S → E ↦ vacuumCfg ζ C η) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i ∈ C
  · simp [vacuumCfg, hi]
  · simpa [vacuumCfg, hi] using measurable_pi_apply (X := fun _ : S ↦ E) i

/-- `vacuumCfg ζ C η` is jointly measurable in the reference configuration and the argument. -/
lemma measurable_vacuumCfg_prod (C : Finset S) :
    Measurable (fun p : (S → E) × (S → E) ↦ vacuumCfg p.1 C p.2) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i ∈ C
  · simp only [vacuumCfg, hi, ite_true]
    exact (measurable_pi_apply (X := fun _ : S ↦ E) i).comp measurable_snd
  · simp only [vacuumCfg, hi, ite_false]
    exact (measurable_pi_apply (X := fun _ : S ↦ E) i).comp measurable_fst

/-- The configuration which agrees with `η` on `C` and takes the *vacuum state* `a` off `C`.

Georgii writes this `ω_C a_{S∖C}`.  For the Dirac a priori measure `α = δ_a`, Georgii's kernel
`α_{S∖C}` of Remark (1.25) acts on functions by `α_{S∖C} f (η) = f (vacuum a C η)`. -/
def vacuum (a : E) (C : Finset S) (η : S → E) : S → E := fun i ↦ if i ∈ C then η i else a

omit [MeasurableSpace E] in
@[simp] lemma vacuum_apply_of_mem {a : E} {C : Finset S} {η : S → E} {i : S} (hi : i ∈ C) :
    vacuum a C η i = η i := vacuumCfg_apply_of_mem (ζ := fun _ ↦ a) (η := η) hi

omit [MeasurableSpace E] in
@[simp] lemma vacuum_apply_of_notMem {a : E} {C : Finset S} {η : S → E} {i : S} (hi : i ∉ C) :
    vacuum a C η i = a := vacuumCfg_apply_of_notMem (ζ := fun _ ↦ a) (η := η) hi

omit [MeasurableSpace E] in
@[simp] lemma vacuum_empty (a : E) (η : S → E) : vacuum a ∅ η = fun _ ↦ a :=
  vacuumCfg_empty (fun _ ↦ a) η

omit [MeasurableSpace E] in
lemma vacuum_congr {a : E} {C : Finset S} {ζ η : S → E} (h : ∀ i ∈ C, ζ i = η i) :
    vacuum a C ζ = vacuum a C η := vacuumCfg_congr (ζ := fun _ ↦ a) h

omit [MeasurableSpace E] in
/-- Two vacuum configurations built from subsets of `A` agree off `A`. -/
lemma vacuum_eqOn_compl {a : E} {C D A : Finset S} (hC : C ⊆ A) (hD : D ⊆ A) (ζ η : S → E) :
    ∀ i ∉ A, vacuum a C ζ i = vacuum a D η i := by
  intro i hi
  rw [vacuum_apply_of_notMem fun h ↦ hi (hC h), vacuum_apply_of_notMem fun h ↦ hi (hD h)]

omit [MeasurableSpace E] in
/-- `vacuum a C` only reads the coordinates in `C`. -/
lemma dependsOn_vacuum (a : E) (C : Finset S) :
    DependsOn (fun η : S → E ↦ vacuum a C η) (C : Set S) := dependsOn_vacuumCfg (fun _ ↦ a) C

lemma measurable_vacuum (a : E) (C : Finset S) :
    Measurable (fun η : S → E ↦ vacuum a C η) := measurable_vacuumCfg (fun _ ↦ a) C

/-! ### Gas potentials -/

/-- **Georgii (2.28), (2.29)(1).** A potential `Φ` is a *gas potential with vacuum state `a`*, i.e.
is normalized by the Dirac measure `δ_a`, if and only if `Φ_A(ω) = 0` whenever `ω_i = a` for some
`i ∈ A`. -/
def IsGasPotential (a : E) (Φ : Potential S E) : Prop :=
  ∀ (A : Finset S) (η : S → E), (∃ i ∈ A, η i = a) → Φ A η = 0

omit [DecidableEq S] in
lemma IsGasPotential.sub {a : E} {Φ Ψ : Potential S E} (hΦ : IsGasPotential a Φ)
    (hΨ : IsGasPotential a Ψ) : IsGasPotential a (fun A η ↦ Φ A η - Ψ A η) := by
  intro A η h; simp [hΦ A η h, hΨ A η h]

omit [DecidableEq S] in
/-- A gas potential vanishes on the constant vacuum configuration, for every nonempty support. -/
lemma IsGasPotential.apply_const {a : E} {Φ : Potential S E} (hΦ : IsGasPotential a Φ)
    {A : Finset S} (hA : A.Nonempty) : Φ A (fun _ ↦ a) = 0 :=
  hΦ A _ (hA.imp fun _ hi ↦ ⟨hi, rfl⟩)

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E]

/-! ### Georgii's operator `p_A` (proof of (2.30), step 1) -/

omit [MeasurableSpace E] in
/-- `∑_{C ⊆ A} (-1)^{|A∖C|} = 0` for nonempty `A`; the alternating sum over a powerset. -/
lemma sum_powerset_neg_one_pow_card_sdiff (A : Finset S) :
    ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card = if A = ∅ then 1 else 0 := by
  have h : ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card
      = ∑ D ∈ A.powerset, (-1 : ℝ) ^ D.card := by
    refine Finset.sum_nbij' (fun C ↦ A \ C) (fun D ↦ A \ D) ?_ ?_ ?_ ?_ ?_
    · intro C _; simp
    · intro D _; simp
    · intro C hC; exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hC)
    · intro D hD; exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hD)
    · intro C _; rfl
  have h2 : ((∑ D ∈ A.powerset, (-1 : ℤ) ^ D.card : ℤ) : ℝ)
      = ∑ D ∈ A.powerset, (-1 : ℝ) ^ D.card := by push_cast; rfl
  rw [h, ← h2, Finset.sum_powerset_neg_one_pow_card]
  split <;> simp

omit [MeasurableSpace E] in
/-- The inner alternating sum in Georgii's inclusion–exclusion identity (2.30)(ii):
`∑_{C ⊆ A ⊆ Λ} (-1)^{|A∖C|} = δ_{C,Λ}`. -/
lemma sum_filter_superset_neg_one_pow_card_sdiff {C Λ : Finset S} (hCΛ : C ⊆ Λ) :
    ∑ A ∈ Λ.powerset.filter (fun A ↦ C ⊆ A), (-1 : ℝ) ^ (A \ C).card
      = if C = Λ then 1 else 0 := by
  have h : ∑ A ∈ Λ.powerset.filter (fun A ↦ C ⊆ A), (-1 : ℝ) ^ (A \ C).card
      = ∑ D ∈ (Λ \ C).powerset, (-1 : ℝ) ^ D.card := by
    refine Finset.sum_nbij' (fun A ↦ A \ C) (fun D ↦ D ∪ C) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_powerset] at hA
      exact Finset.mem_powerset.2 (Finset.sdiff_subset_sdiff hA.1 le_rfl)
    · intro D hD
      have hD' : D ⊆ Λ \ C := Finset.mem_powerset.1 hD
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, Finset.subset_union_right⟩
      exact Finset.union_subset (hD'.trans Finset.sdiff_subset) hCΛ
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_powerset] at hA
      exact Finset.sdiff_union_of_subset hA.2
    · intro D hD
      have hD' : D ⊆ Λ \ C := Finset.mem_powerset.1 hD
      have hdisj : Disjoint D C := Finset.disjoint_left.2 fun x hx hxC ↦
        (Finset.mem_sdiff.1 (hD' hx)).2 hxC
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hdisj]
    · intro A _; rfl
  have h2 : ((∑ D ∈ (Λ \ C).powerset, (-1 : ℤ) ^ D.card : ℤ) : ℝ)
      = ∑ D ∈ (Λ \ C).powerset, (-1 : ℝ) ^ D.card := by push_cast; rfl
  rw [h, ← h2, Finset.sum_powerset_neg_one_pow_card]
  have : (Λ \ C = ∅) ↔ (C = Λ) := by
    constructor
    · intro hEmpty
      exact le_antisymm hCΛ (by simpa [Finset.sdiff_eq_empty_iff_subset] using hEmpty)
    · rintro rfl; simp
  simp only [this]
  split <;> simp

/-- Georgii, proof of (2.30), step 1: the operator
`p_A f = ∑_{C ⊆ A} (-1)^{|A∖C|} α_{S∖C} f`, evaluated at a fixed reference configuration `ζ`,
that is, for the Dirac measure at `ζ` in place of the product measure `α^S`. -/
def mobiusCfg (ζ : S → E) (A : Finset S) (f : (S → E) → ℝ) (η : S → E) : ℝ :=
  ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * f (vacuumCfg ζ C η)

omit [MeasurableSpace E] in
@[simp] lemma mobiusCfg_empty (ζ : S → E) (f : (S → E) → ℝ) (η : S → E) :
    mobiusCfg ζ ∅ f η = f ζ := by simp [mobiusCfg]

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(i).** `p_A f` is `𝓕_A`-measurable. -/
lemma dependsOn_mobiusCfg (ζ : S → E) (A : Finset S) (f : (S → E) → ℝ) :
    DependsOn (mobiusCfg ζ A f) (A : Set S) := by
  intro x y h
  refine Finset.sum_congr rfl fun C hC ↦ ?_
  have hCA : C ⊆ A := Finset.mem_powerset.1 hC
  rw [vacuumCfg_congr (ζ := ζ) (C := C) fun i hi ↦ h i (by exact_mod_cast hCA hi)]

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(iii), combinatorial core.** Pairing the subsets `C` and `C ∪ {i}`
of `A`, which carry opposite signs, turns an alternating sum over the powerset of `A` into an
alternating sum of first differences over the powerset of `A ∖ {i}`. -/
lemma sum_powerset_neg_one_pow_mul_eq_sum_sub {A : Finset S} {i : S} (hiA : i ∈ A)
    (g : Finset S → ℝ) :
    ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * g C
      = ∑ C ∈ (A.erase i).powerset, (-1 : ℝ) ^ (A \ C).card * (g C - g (insert i C)) := by
  set B := A.erase i with hB
  have hiB : i ∉ B := Finset.notMem_erase i A
  have hAB : A = insert i B := (Finset.insert_erase hiA).symm
  have key : ∀ C ∈ B.powerset,
      (-1 : ℝ) ^ (A \ C).card * g C + (-1 : ℝ) ^ (A \ insert i C).card * g (insert i C)
        = (-1 : ℝ) ^ (A \ C).card * (g C - g (insert i C)) := by
    intro C hC
    have hCB : C ⊆ B := Finset.mem_powerset.1 hC
    have hiC : i ∉ C := fun h ↦ hiB (hCB h)
    have h1 : A \ C = insert i (B \ C) := by
      rw [hAB]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hx, hxC⟩
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hxC⟩
      · rintro (rfl | ⟨hx, hxC⟩)
        · exact ⟨Or.inl rfl, hiC⟩
        · exact ⟨Or.inr hx, hxC⟩
    have h2 : A \ insert i C = B \ C := by
      rw [hAB]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨hx, hxi, hxC⟩
        rcases hx with rfl | hx
        · exact absurd rfl hxi
        · exact ⟨hx, hxC⟩
      · rintro ⟨hx, hxC⟩
        exact ⟨Or.inr hx, by rintro rfl; exact hiB hx, hxC⟩
    have hcard : (A \ C).card = (B \ C).card + 1 := by
      rw [h1, Finset.card_insert_of_notMem (by simp [Finset.mem_sdiff, hiB])]
    rw [h2, hcard, pow_succ]
    ring
  rw [hAB, Finset.sum_powerset_insert hiB, ← hAB, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl key

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(iii), combinatorial core.** An alternating sum over the subsets of
`A` vanishes as soon as the summand is unchanged by adjoining a fixed site `i ∈ A`. -/
lemma sum_powerset_neg_one_pow_mul_eq_zero {A : Finset S} {i : S} (hiA : i ∈ A)
    {g : Finset S → ℝ} (hg : ∀ C ⊆ A.erase i, g (insert i C) = g C) :
    ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * g C = 0 := by
  rw [sum_powerset_neg_one_pow_mul_eq_sum_sub hiA g]
  refine Finset.sum_eq_zero fun C hC ↦ ?_
  rw [hg C (Finset.mem_powerset.1 hC), sub_self, mul_zero]

omit [MeasurableSpace E] in
/-- **Georgii, proof of Corollary (2.32), combinatorial core.** An alternating sum over the
subsets of `A` vanishes as soon as its second difference in two fixed distinct sites
`i, j ∈ A` vanishes. -/
lemma sum_powerset_neg_one_pow_mul_eq_zero_of_sub_sub {A : Finset S} {i j : S} (hiA : i ∈ A)
    (hjA : j ∈ A) (hji : j ≠ i) {g : Finset S → ℝ}
    (hg : ∀ C ⊆ (A.erase i).erase j,
      g C - g (insert i C) - (g (insert j C) - g (insert i (insert j C))) = 0) :
    ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * g C = 0 := by
  rw [sum_powerset_neg_one_pow_mul_eq_sum_sub hiA g]
  have hiB : i ∉ A.erase i := Finset.notMem_erase i A
  have hjB : j ∈ A.erase i := Finset.mem_erase.2 ⟨hji, hjA⟩
  have hsign : ∀ C ∈ (A.erase i).powerset,
      (-1 : ℝ) ^ (A \ C).card * (g C - g (insert i C))
        = -((-1 : ℝ) ^ ((A.erase i) \ C).card * (g C - g (insert i C))) := by
    intro C hC
    have hCB : C ⊆ A.erase i := Finset.mem_powerset.1 hC
    have hiC : i ∉ C := fun h ↦ hiB (hCB h)
    have h1 : A \ C = insert i ((A.erase i) \ C) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hx, hxC⟩
        by_cases hxi : x = i
        · exact Or.inl hxi
        · exact Or.inr ⟨⟨hxi, hx⟩, hxC⟩
      · rintro (rfl | ⟨⟨hxi, hx⟩, hxC⟩)
        · exact ⟨hiA, hiC⟩
        · exact ⟨hx, hxC⟩
    have hcard : (A \ C).card = ((A.erase i) \ C).card + 1 := by
      rw [h1, Finset.card_insert_of_notMem (by simp [Finset.mem_sdiff, hiB])]
    rw [hcard, pow_succ]
    ring
  rw [Finset.sum_congr rfl hsign, Finset.sum_neg_distrib, neg_eq_zero,
    sum_powerset_neg_one_pow_mul_eq_sum_sub hjB (fun C ↦ g C - g (insert i C))]
  refine Finset.sum_eq_zero fun C hC ↦ ?_
  rw [hg C (Finset.mem_powerset.1 hC), mul_zero]

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(iii).** `α_{i}(p_A f) = 0` for `i ∈ A`; at a fixed reference
configuration this says that `p_A f` vanishes at every configuration which agrees with the
reference configuration somewhere in `A`. -/
lemma mobiusCfg_eq_zero {ζ : S → E} {A : Finset S} (f : (S → E) → ℝ) {η : S → E} {i : S}
    (hiA : i ∈ A) (hη : η i = ζ i) : mobiusCfg ζ A f η = 0 := by
  refine sum_powerset_neg_one_pow_mul_eq_zero hiA fun C hC ↦ congrArg f ?_
  have hiC : i ∉ C := fun h ↦ Finset.notMem_erase i A (hC h)
  funext x
  by_cases hx : x ∈ insert i C
  · rcases Finset.mem_insert.1 hx with rfl | hx'
    · rw [vacuumCfg_apply_of_mem hx, vacuumCfg_apply_of_notMem hiC, hη]
    · rw [vacuumCfg_apply_of_mem hx, vacuumCfg_apply_of_mem hx']
  · have hxC : x ∉ C := fun h ↦ hx (Finset.mem_insert_of_mem h)
    rw [vacuumCfg_apply_of_notMem hx, vacuumCfg_apply_of_notMem hxC]

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(ii).** The inclusion–exclusion principle:
`α_{S∖Λ} f = ∑_{A ⊆ Λ} p_A f`. -/
lemma sum_powerset_mobiusCfg (ζ : S → E) (Λ : Finset S) (f : (S → E) → ℝ) (η : S → E) :
    ∑ A ∈ Λ.powerset, mobiusCfg ζ A f η = f (vacuumCfg ζ Λ η) := by
  have hswap : ∑ A ∈ Λ.powerset, ∑ C ∈ A.powerset,
        (-1 : ℝ) ^ (A \ C).card * f (vacuumCfg ζ C η)
      = ∑ C ∈ Λ.powerset, ∑ A ∈ Λ.powerset.filter (fun A ↦ C ⊆ A),
        (-1 : ℝ) ^ (A \ C).card * f (vacuumCfg ζ C η) := by
    refine Finset.sum_comm' ?_
    intro A C
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · rintro ⟨hA, hC⟩; exact ⟨⟨hA, hC⟩, hC.trans hA⟩
    · rintro ⟨⟨hA, hC⟩, -⟩; exact ⟨hA, hC⟩
  rw [show (∑ A ∈ Λ.powerset, mobiusCfg ζ A f η)
      = ∑ A ∈ Λ.powerset, ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * f (vacuumCfg ζ C η) from rfl,
    hswap]
  refine (Finset.sum_eq_single_of_mem Λ (Finset.mem_powerset_self Λ) ?_).trans ?_
  · intro C hC hCΛ
    rw [← Finset.sum_mul, sum_filter_superset_neg_one_pow_card_sdiff (Finset.mem_powerset.1 hC)]
    simp [hCΛ]
  · rw [← Finset.sum_mul, sum_filter_superset_neg_one_pow_card_sdiff (le_refl Λ)]
    simp

/-- Georgii, proof of (2.30), step 1: the operator
`p_A f = ∑_{C ⊆ A} (-1)^{|A∖C|} α_{S∖C} f`, specialized to the Dirac measure `α = δ_a`. -/
def mobius (a : E) (A : Finset S) (f : (S → E) → ℝ) (η : S → E) : ℝ :=
  ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * f (vacuum a C η)

omit [MeasurableSpace E] in
@[simp] lemma mobius_empty (a : E) (f : (S → E) → ℝ) (η : S → E) :
    mobius a ∅ f η = f (fun _ ↦ a) := mobiusCfg_empty (fun _ ↦ a) f η

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(i).** `p_A f` is `𝓕_A`-measurable. -/
lemma dependsOn_mobius (a : E) (A : Finset S) (f : (S → E) → ℝ) :
    DependsOn (mobius a A f) (A : Set S) := dependsOn_mobiusCfg (fun _ ↦ a) A f

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(iii).** `α_{\{i\}}(p_A f) = 0` for `i ∈ A`; for `α = δ_a` this says
that `p_A f` vanishes at every configuration carrying the vacuum state somewhere in `A`. -/
lemma mobius_eq_zero {a : E} {A : Finset S} (f : (S → E) → ℝ) {η : S → E} {i : S}
    (hiA : i ∈ A) (hη : η i = a) : mobius a A f η = 0 :=
  mobiusCfg_eq_zero (ζ := fun _ ↦ a) f hiA hη

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(ii).** The inclusion–exclusion principle:
`α_{S∖Λ} f = ∑_{A ⊆ Λ} p_A f`. -/
lemma sum_powerset_mobius (a : E) (Λ : Finset S) (f : (S → E) → ℝ) (η : S → E) :
    ∑ A ∈ Λ.powerset, mobius a A f η = f (vacuum a Λ η) :=
  sum_powerset_mobiusCfg (fun _ ↦ a) Λ f η

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E]

/-! ### Quasilocal limits along the net of finite volumes -/

/-- The configuration equal to the vacuum state `a` on `Λ` and to `η` off `Λ`; Georgii's
`a_Λ ω_{S∖Λ}`. -/
def vacuumOn (a : E) (Λ : Finset S) (η : S → E) : S → E := fun i ↦ if i ∈ Λ then a else η i

omit [MeasurableSpace E] in
@[simp] lemma vacuumOn_apply_of_mem {a : E} {Λ : Finset S} {η : S → E} {i : S} (hi : i ∈ Λ) :
    vacuumOn a Λ η i = a := by simp [vacuumOn, hi]

omit [MeasurableSpace E] in
@[simp] lemma vacuumOn_apply_of_notMem {a : E} {Λ : Finset S} {η : S → E} {i : S} (hi : i ∉ Λ) :
    vacuumOn a Λ η i = η i := by simp [vacuumOn, hi]

omit [MeasurableSpace E] in
lemma vacuumOn_eqOn_compl (a : E) (Λ : Finset S) (η : S → E) :
    ∀ i ∉ Λ, vacuumOn a Λ η i = η i := fun _ hi ↦ vacuumOn_apply_of_notMem hi

omit [MeasurableSpace E] in
/-- `ω_Δ a_{S∖Δ}` agrees with `ω` on `Δ`. -/
lemma vacuum_eqOn (a : E) (Δ : Finset S) (η : S → E) : ∀ i ∈ Δ, vacuum a Δ η i = η i :=
  fun _ hi ↦ vacuum_apply_of_mem hi

omit [MeasurableSpace E] in
/-- `ω_{Δ∖Λ} a_{S∖(Δ∖Λ)}` agrees with `a_Λ ω_{S∖Λ}` on `Δ`, provided `Λ ⊆ Δ`. -/
lemma vacuum_sdiff_eqOn (a : E) {Λ Δ : Finset S} (η : S → E) :
    ∀ i ∈ Δ, vacuum a (Δ \ Λ) η i = vacuumOn a Λ η i := by
  intro i hi
  by_cases hiΛ : i ∈ Λ
  · rw [vacuum_apply_of_notMem (by simp [Finset.mem_sdiff, hiΛ]), vacuumOn_apply_of_mem hiΛ]
  · rw [vacuum_apply_of_mem (Finset.mem_sdiff.2 ⟨hi, hiΛ⟩), vacuumOn_apply_of_notMem hiΛ]

omit [DecidableEq S] [MeasurableSpace E] in
/-- A quasilocal function is continuous along any net of configurations which eventually agree
with the limit configuration on any prescribed finite volume. -/
lemma tendsto_of_quasilocal {f : (S → E) → ℝ} (hf : IsQuasilocalFun f)
    (g : Finset S → (S → E)) (η : S → E)
    (hg : ∀ Δ₀ : Finset S, ∀ Δ : Finset S, Δ₀ ⊆ Δ → ∀ i ∈ Δ₀, g Δ i = η i) :
    Tendsto (fun Δ : Finset S ↦ f (g Δ)) atTop (nhds (f η)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Δ₀, hΔ₀⟩ := hf (ε / 2) (by positivity)
  refine ⟨Δ₀, fun Δ hΔ ↦ ?_⟩
  have := hΔ₀ (g Δ) η (hg Δ₀ Δ hΔ)
  rw [Real.dist_eq]
  linarith

omit [MeasurableSpace E] in
/-- Georgii's `lim_Δ ρ_Λ(ω_Δ a_{S∖Δ}) = ρ_Λ(ω)`. -/
lemma tendsto_vacuum_of_quasilocal {f : (S → E) → ℝ} (hf : IsQuasilocalFun f) (a : E)
    (η : S → E) : Tendsto (fun Δ : Finset S ↦ f (vacuum a Δ η)) atTop (nhds (f η)) :=
  tendsto_of_quasilocal hf _ η fun _ _ hΔ _i hi ↦ vacuum_apply_of_mem (hΔ hi)

omit [MeasurableSpace E] in
/-- Georgii's `lim_Δ ρ_Λ(ω_{Δ∖Λ} a_{S∖(Δ∖Λ)}) = ρ_Λ(a_Λ ω_{S∖Λ})`. -/
lemma tendsto_vacuum_sdiff_of_quasilocal {f : (S → E) → ℝ} (hf : IsQuasilocalFun f) (a : E)
    (Λ : Finset S) (η : S → E) :
    Tendsto (fun Δ : Finset S ↦ f (vacuum a (Δ \ Λ) η)) atTop (nhds (f (vacuumOn a Λ η))) := by
  refine tendsto_of_quasilocal hf _ _ fun Δ₀ Δ hΔ i hi ↦ ?_
  by_cases hiΛ : i ∈ Λ
  · rw [vacuum_apply_of_notMem (by simp [Finset.mem_sdiff, hiΛ]), vacuumOn_apply_of_mem hiΛ]
  · rw [vacuum_apply_of_mem (Finset.mem_sdiff.2 ⟨hΔ hi, hiΛ⟩), vacuumOn_apply_of_notMem hiΛ]

/-! ### The logarithm of a positive premodifier -/

/-- Georgii's `u_Λ = log ρ_Λ`. -/
noncomputable def logDensity (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) : ℝ :=
  Real.log (ρ Λ η).toReal

variable {ρ : Finset S → (S → E) → ℝ≥0∞}

omit [DecidableEq S] [MeasurableSpace E] in
lemma exp_logDensity (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (Λ : Finset S)
    (η : S → E) : Real.exp (logDensity ρ Λ η) = (ρ Λ η).toReal :=
  Real.exp_log (ENNReal.toReal_pos (hpos Λ η) (hfin Λ η))

omit [DecidableEq S] in
/-- **Georgii (1.31), in logarithmic form.** For a positive pre-modification,
`u_Λ(ζ) - u_Λ(ω) = u_Δ(ζ) - u_Δ(ω)` whenever `Λ ⊆ Δ` and `ζ = ω` off `Λ`. -/
lemma logDensity_sub_comm (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) {ζ η : S → E} (h : ∀ s ∉ Λ₁, ζ s = η s) :
    logDensity ρ Λ₂ ζ - logDensity ρ Λ₂ η = logDensity ρ Λ₁ ζ - logDensity ρ Λ₁ η := by
  have hcomm := hρ.comm_of_subset hΛ h
  have h2ζ : (0 : ℝ) < (ρ Λ₂ ζ).toReal := ENNReal.toReal_pos (hpos _ _) (hfin _ _)
  have h2η : (0 : ℝ) < (ρ Λ₂ η).toReal := ENNReal.toReal_pos (hpos _ _) (hfin _ _)
  have h1ζ : (0 : ℝ) < (ρ Λ₁ ζ).toReal := ENNReal.toReal_pos (hpos _ _) (hfin _ _)
  have h1η : (0 : ℝ) < (ρ Λ₁ η).toReal := ENNReal.toReal_pos (hpos _ _) (hfin _ _)
  have hreal : (ρ Λ₂ ζ).toReal * (ρ Λ₁ η).toReal = (ρ Λ₁ ζ).toReal * (ρ Λ₂ η).toReal := by
    rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, hcomm]
  have hlog : Real.log ((ρ Λ₂ ζ).toReal * (ρ Λ₁ η).toReal)
      = Real.log ((ρ Λ₁ ζ).toReal * (ρ Λ₂ η).toReal) := by rw [hreal]
  rw [Real.log_mul h2ζ.ne' h1η.ne', Real.log_mul h1ζ.ne' h2η.ne'] at hlog
  simp only [logDensity]
  linarith

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### The gas potential of a positive quasilocal pre-modification -/

/-! ### The interaction of a positive pre-modification at a reference configuration

Georgii's `Φ_A = -p_A u_A` with `u_A = log ρ_A`, computed at a fixed reference configuration
`ζ` instead of the product measure `α^S`.  The gas potentials `Φ^a` are the case of a constant
reference configuration, and the `α`-normalized potential of the second assertion of (2.30) is
the `α^S`-average over `ζ`. -/

/-- **Georgii (2.30).** `Φ^ζ_A = -p_A u_A` at the reference configuration `ζ`:

`Φ^ζ_A(ω) = - ∑_{C ⊆ A} (-1)^{|A∖C|} log ρ_A(ω_C ζ_{S∖C})`. -/
noncomputable def gasPotentialCfg (ρ : Finset S → (S → E) → ℝ≥0∞) (ζ : S → E) : Potential S E :=
  fun A η ↦ -mobiusCfg ζ A (logDensity ρ A) η

lemma gasPotentialCfg_apply (ζ : S → E) (A : Finset S) (η : S → E) :
    gasPotentialCfg ρ ζ A η
      = -∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card
          * Real.log ((ρ A (vacuumCfg ζ C η)).toReal) :=
  rfl

/-- **Georgii (2.30), step 2.** `Φ^ζ_A` vanishes at every configuration which agrees with the
reference configuration somewhere in `A`. -/
theorem gasPotentialCfg_eq_zero (ρ : Finset S → (S → E) → ℝ≥0∞) {ζ : S → E} {A : Finset S}
    {η : S → E} {i : S} (hiA : i ∈ A) (hη : η i = ζ i) : gasPotentialCfg ρ ζ A η = 0 := by
  simp [gasPotentialCfg, mobiusCfg_eq_zero (ζ := ζ) (logDensity ρ A) hiA hη]

lemma dependsOn_gasPotentialCfg (ζ : S → E) (A : Finset S) :
    DependsOn (gasPotentialCfg ρ ζ A) (A : Set S) :=
  DependsOn.comp (fun x : ℝ ↦ -x) (dependsOn_mobiusCfg ζ A (logDensity ρ A))

lemma measurable_gasPotentialCfg (hmeas : ∀ Λ, Measurable (ρ Λ)) (ζ : S → E) (A : Finset S) :
    Measurable (gasPotentialCfg ρ ζ A) := by
  rw [show gasPotentialCfg ρ ζ A = fun η : S → E ↦
      -∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card
        * Real.log ((ρ A (vacuumCfg ζ C η)).toReal) from rfl]
  refine Measurable.neg (Finset.measurable_sum _ fun C _ ↦ ?_)
  exact measurable_const.mul
    ((((hmeas A).comp (measurable_vacuumCfg ζ C)).ennreal_toReal).log)

/-- `Φ^ζ_A(η)` is jointly measurable in the reference configuration `ζ` and in `η`. -/
lemma measurable_gasPotentialCfg_prod (hmeas : ∀ Λ, Measurable (ρ Λ)) (A : Finset S) :
    Measurable (fun p : (S → E) × (S → E) ↦ gasPotentialCfg ρ p.1 A p.2) := by
  rw [show (fun p : (S → E) × (S → E) ↦ gasPotentialCfg ρ p.1 A p.2)
      = fun p : (S → E) × (S → E) ↦
        -∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card
          * Real.log ((ρ A (vacuumCfg p.1 C p.2)).toReal) from rfl]
  refine Measurable.neg (Finset.measurable_sum _ fun C _ ↦ ?_)
  exact measurable_const.mul
    ((((hmeas A).comp (measurable_vacuumCfg_prod C)).ennreal_toReal).log)

/-- **Georgii (2.30), step 3.** `Φ^ζ_A = -p_A u_Δ` whenever `∅ ≠ A ⊆ Δ`. -/
theorem gasPotentialCfg_eq_neg_mobiusCfg (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (ζ : S → E)
    {A Δ : Finset S} (hA : A.Nonempty) (hAΔ : A ⊆ Δ) (η : S → E) :
    gasPotentialCfg ρ ζ A η = -mobiusCfg ζ A (logDensity ρ Δ) η := by
  have key : ∀ C ∈ A.powerset,
      logDensity ρ A (vacuumCfg ζ C η) - logDensity ρ Δ (vacuumCfg ζ C η)
        = logDensity ρ A ζ - logDensity ρ Δ ζ := by
    intro C hC
    have hCA : C ⊆ A := Finset.mem_powerset.1 hC
    have hoff : ∀ s ∉ A, vacuumCfg ζ C η s = ζ s := fun s hs ↦
      vacuumCfg_apply_of_notMem fun h ↦ hs (hCA h)
    have h := logDensity_sub_comm hρ hpos hfin hAΔ hoff
    linarith
  have hzero : ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card = 0 := by
    rw [sum_powerset_neg_one_pow_card_sdiff]
    simp [Finset.nonempty_iff_ne_empty.1 hA]
  have hdiff : mobiusCfg ζ A (logDensity ρ A) η - mobiusCfg ζ A (logDensity ρ Δ) η
      = (logDensity ρ A ζ - logDensity ρ Δ ζ)
        * ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card := by
    rw [Finset.mul_sum, mobiusCfg, mobiusCfg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun C hC ↦ ?_
    rw [← mul_sub, key C hC]
    ring
  rw [hzero, mul_zero] at hdiff
  change -mobiusCfg ζ A (logDensity ρ A) η = -mobiusCfg ζ A (logDensity ρ Δ) η
  linarith

/-- The full sum of the interaction terms over the subsets of `Δ`, for `Φ = Φ^ζ`. -/
lemma sum_powerset_gasPotentialCfg (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (ζ : S → E)
    {Δ' Δ : Finset S} (hΔ' : Δ' ⊆ Δ) (η : S → E) :
    ∑ A ∈ Δ'.powerset, gasPotentialCfg ρ ζ A η
      = gasPotentialCfg ρ ζ ∅ η + logDensity ρ Δ ζ
        - logDensity ρ Δ (vacuumCfg ζ Δ' η) := by
  have hmem : (∅ : Finset S) ∈ Δ'.powerset := Finset.empty_mem_powerset _
  have h1 : ∑ A ∈ Δ'.powerset.erase ∅, gasPotentialCfg ρ ζ A η
      = ∑ A ∈ Δ'.powerset.erase ∅, -mobiusCfg ζ A (logDensity ρ Δ) η := by
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    have hA0 : A ≠ ∅ := Finset.ne_of_mem_erase hA
    have hAΔ' : A ⊆ Δ' := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA)
    exact gasPotentialCfg_eq_neg_mobiusCfg hρ hpos hfin ζ (Finset.nonempty_iff_ne_empty.2 hA0)
      (hAΔ'.trans hΔ') η
  have h2 : ∑ A ∈ Δ'.powerset, (-mobiusCfg ζ A (logDensity ρ Δ) η)
      = -logDensity ρ Δ (vacuumCfg ζ Δ' η) := by
    rw [Finset.sum_neg_distrib, sum_powerset_mobiusCfg]
  have e1 := Finset.sum_erase_add Δ'.powerset (fun A ↦ gasPotentialCfg ρ ζ A η) hmem
  have e2 := Finset.sum_erase_add Δ'.powerset (fun A ↦ -mobiusCfg ζ A (logDensity ρ Δ) η) hmem
  rw [h2] at e2
  rw [← e1, h1]
  have hm0 : mobiusCfg ζ ∅ (logDensity ρ Δ) η = logDensity ρ Δ ζ := mobiusCfg_empty _ _ _
  rw [hm0] at e2
  linarith

/-- **Georgii (2.30), step 4.** For `Λ ⊆ Δ` the partial Hamiltonian of `Φ^ζ` is

`H^Φ_{Λ,Δ}(ω) = log ρ_Λ(ω_{Δ∖Λ} ζ_{S∖(Δ∖Λ)}) - log ρ_Λ(ω_Δ ζ_{S∖Δ})`. -/
theorem sum_powerset_hamiltonianTerms_gasPotentialCfg (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (ζ : S → E)
    {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) (η : S → E) :
    ∑ A ∈ Δ.powerset, (gasPotentialCfg ρ ζ).hamiltonianTerms Λ η A
      = logDensity ρ Λ (vacuumCfg ζ (Δ \ Λ) η) - logDensity ρ Λ (vacuumCfg ζ Δ η) := by
  classical
  set Φ : Potential S E := gasPotentialCfg ρ ζ with hΦ
  have hsub : (Δ \ Λ).powerset ⊆ Δ.powerset :=
    Finset.powerset_mono.2 (Finset.sdiff_subset)
  have hzero : ∑ A ∈ (Δ \ Λ).powerset, Φ.hamiltonianTerms Λ η A = 0 := by
    refine Finset.sum_eq_zero fun A hA ↦ ?_
    have hA' : A ⊆ Δ \ Λ := Finset.mem_powerset.1 hA
    refine hamiltonianTerms_of_disjoint (Finset.disjoint_left.2 fun x hx hxΛ ↦ ?_) η
    exact (Finset.mem_sdiff.1 (hA' hx)).2 hxΛ
  have e1 : ∑ A ∈ Δ.powerset, Φ.hamiltonianTerms Λ η A
      = ∑ A ∈ Δ.powerset \ (Δ \ Λ).powerset, Φ.hamiltonianTerms Λ η A := by
    rw [← Finset.sum_sdiff hsub, hzero, add_zero]
  have e2 : ∑ A ∈ Δ.powerset \ (Δ \ Λ).powerset, Φ.hamiltonianTerms Λ η A
      = ∑ A ∈ Δ.powerset \ (Δ \ Λ).powerset, Φ A η := by
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    rw [Finset.mem_sdiff, Finset.mem_powerset, Finset.mem_powerset] at hA
    refine hamiltonianTerms_of_not_disjoint (fun hdisj ↦ hA.2 ?_) η
    intro x hx
    exact Finset.mem_sdiff.2 ⟨hA.1 hx, fun hxΛ ↦ (Finset.disjoint_left.1 hdisj hx) hxΛ⟩
  have e3 : ∑ A ∈ Δ.powerset \ (Δ \ Λ).powerset, Φ A η
      = ∑ A ∈ Δ.powerset, Φ A η - ∑ A ∈ (Δ \ Λ).powerset, Φ A η := by
    rw [eq_sub_iff_add_eq]; exact Finset.sum_sdiff hsub
  have hfull := sum_powerset_gasPotentialCfg hρ hpos hfin ζ (le_refl Δ) η
  have hpart := sum_powerset_gasPotentialCfg hρ hpos hfin ζ
    (Finset.sdiff_subset (s := Δ) (t := Λ)) η
  have hoff : ∀ s ∉ Λ, vacuumCfg ζ (Δ \ Λ) η s = vacuumCfg ζ Δ η s := by
    intro s hs
    by_cases hsΔ : s ∈ Δ
    · rw [vacuumCfg_apply_of_mem (Finset.mem_sdiff.2 ⟨hsΔ, hs⟩), vacuumCfg_apply_of_mem hsΔ]
    · rw [vacuumCfg_apply_of_notMem (fun h ↦ hsΔ (Finset.mem_sdiff.1 h).1),
        vacuumCfg_apply_of_notMem hsΔ]
  have hconv := logDensity_sub_comm hρ hpos hfin hΛΔ hoff
  rw [e1, e2, e3, hfull, hpart]
  linarith

/-- **Georgii (2.30).** The gas potential with vacuum state `a` associated with a positive
pre-modification `ρ`: `Φ^a_A = -p_A u_A` where `u_A = log ρ_A`.  Explicitly

`Φ^a_A(ω) = - ∑_{C ⊆ A} (-1)^{|A∖C|} log ρ_A(ω_C a_{S∖C})`. -/
noncomputable def gasPotential (ρ : Finset S → (S → E) → ℝ≥0∞) (a : E) : Potential S E :=
  fun A η ↦ -mobius a A (logDensity ρ A) η

lemma gasPotential_apply (a : E) (A : Finset S) (η : S → E) :
    gasPotential ρ a A η
      = -∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * Real.log ((ρ A (vacuum a C η)).toReal) :=
  rfl

/-- **Georgii (2.30), step 2.** `Φ^a` is a gas potential with vacuum state `a`. -/
theorem isGasPotential_gasPotential (ρ : Finset S → (S → E) → ℝ≥0∞) (a : E) :
    IsGasPotential a (gasPotential ρ a) := by
  rintro A η ⟨i, hiA, hη⟩
  have := mobius_eq_zero (a := a) (A := A) (logDensity ρ A) (η := η) hiA hη
  simp [gasPotential, this]

lemma dependsOn_gasPotential (a : E) (A : Finset S) :
    DependsOn (gasPotential ρ a A) (A : Set S) :=
  DependsOn.comp (fun x : ℝ ↦ -x) (dependsOn_mobius a A (logDensity ρ A))

lemma measurable_gasPotential (hmeas : ∀ Λ, Measurable (ρ Λ)) (a : E) (A : Finset S) :
    Measurable (gasPotential ρ a A) := by
  have hrw : gasPotential ρ a A = fun η : S → E ↦
      -∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * Real.log ((ρ A (vacuum a C η)).toReal) := rfl
  rw [hrw]
  refine Measurable.neg (Finset.measurable_sum _ fun C _ ↦ ?_)
  exact measurable_const.mul
    ((((hmeas A).comp (measurable_vacuum a C)).ennreal_toReal).log)

/-- **Georgii (2.30), step 2.** `Φ^a_A` is `𝓕_A`-measurable, i.e. `Φ^a` is a potential in the
sense of Georgii (2.2)(i). -/
theorem isPotential_gasPotential (hmeas : ∀ Λ, Measurable (ρ Λ)) (a : E) :
    IsPotential (gasPotential ρ a) where
  measurable A :=
    (measurable_gasPotential hmeas a A).cylinderEvents_of_dependsOn (dependsOn_gasPotential a A)

/-- **Georgii (2.30), step 3.** `Φ_A = -p_A u_Δ` whenever `∅ ≠ A ⊆ Δ`. -/
theorem gasPotential_eq_neg_mobius (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (a : E)
    {A Δ : Finset S} (hA : A.Nonempty) (hAΔ : A ⊆ Δ) (η : S → E) :
    gasPotential ρ a A η = -mobius a A (logDensity ρ Δ) η :=
  gasPotentialCfg_eq_neg_mobiusCfg hρ hpos hfin (fun _ ↦ a) hA hAΔ η

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### Georgii (2.30), step 4: the partial Hamiltonians -/

/-- The full sum of the interaction terms over the subsets of `Δ`, for `Φ = Φ^a`. -/
lemma sum_powerset_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (a : E)
    {Δ' Δ : Finset S} (hΔ' : Δ' ⊆ Δ) (η : S → E) :
    ∑ A ∈ Δ'.powerset, gasPotential ρ a A η
      = gasPotential ρ a ∅ η + logDensity ρ Δ (fun _ ↦ a)
        - logDensity ρ Δ (vacuum a Δ' η) :=
  sum_powerset_gasPotentialCfg hρ hpos hfin (fun _ ↦ a) hΔ' η

/-- **Georgii (2.30), step 4.** For `Λ ⊆ Δ` the partial Hamiltonian of `Φ^a` is
`H^Φ_{Λ,Δ} = α_{S∖Δ}(α_Λ u_Λ - u_Λ)`, explicitly
`H^Φ_{Λ,Δ}(ω) = log ρ_Λ(ω_{Δ∖Λ} a_{S∖(Δ∖Λ)}) - log ρ_Λ(ω_Δ a_{S∖Δ})`. -/
theorem sum_powerset_hamiltonianTerms_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (a : E)
    {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) (η : S → E) :
    ∑ A ∈ Δ.powerset, (gasPotential ρ a).hamiltonianTerms Λ η A
      = logDensity ρ Λ (vacuum a (Δ \ Λ) η) - logDensity ρ Λ (vacuum a Δ η) :=
  sum_powerset_hamiltonianTerms_gasPotentialCfg hρ hpos hfin (fun _ ↦ a) hΛΔ η

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### Georgii (2.30), step 4 (continued): the Hamiltonian of `Φ^a` -/

omit [MeasurableSpace E] in
/-- Georgii's `lim_Δ log ρ_Λ(ω_Δ a_{S∖Δ}) = log ρ_Λ(ω)`, from quasilocality and positivity of
`ρ_Λ` together with continuity of `log` on `(0, ∞)`. -/
lemma tendsto_logDensity_vacuum {Λ : Finset S}
    (hql : IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hpos : ∀ Λ η, ρ Λ η ≠ 0)
    (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (a : E) (η : S → E) :
    Tendsto (fun Δ : Finset S ↦ logDensity ρ Λ (vacuum a Δ η)) atTop
      (nhds (logDensity ρ Λ η)) := by
  refine Tendsto.comp ?_ (tendsto_vacuum_of_quasilocal hql a η)
  exact (Real.continuousAt_log (ENNReal.toReal_pos (hpos Λ η) (hfin Λ η)).ne').tendsto

omit [MeasurableSpace E] in
/-- Georgii's `lim_Δ log ρ_Λ(ω_{Δ∖Λ} a_{S∖(Δ∖Λ)}) = log ρ_Λ(a_Λ ω_{S∖Λ})`. -/
lemma tendsto_logDensity_vacuum_sdiff {Λ : Finset S}
    (hql : IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hpos : ∀ Λ η, ρ Λ η ≠ 0)
    (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (a : E) (η : S → E) :
    Tendsto (fun Δ : Finset S ↦ logDensity ρ Λ (vacuum a (Δ \ Λ) η)) atTop
      (nhds (logDensity ρ Λ (vacuumOn a Λ η))) := by
  refine Tendsto.comp ?_ (tendsto_vacuum_sdiff_of_quasilocal hql a Λ η)
  exact (Real.continuousAt_log
    (ENNReal.toReal_pos (hpos Λ (vacuumOn a Λ η)) (hfin Λ (vacuumOn a Λ η))).ne').tendsto

/-- **Georgii (2.30), step 4.** The Hamiltonian series of `Φ^a` converges in the sense of Georgii's
Convention (2.1), with sum `v_Λ = α_Λ u_Λ - u_Λ = log ρ_Λ(a_Λ ω_{S∖Λ}) - log ρ_Λ(ω)`. -/
theorem hasSum_hamiltonianTerms_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (a : E) (Λ : Finset S) (η : S → E) :
    HasSum ((gasPotential ρ a).hamiltonianTerms Λ η)
      (logDensity ρ Λ (vacuumOn a Λ η) - logDensity ρ Λ η) (SummationFilter.volume S) := by
  refine SummationFilter.tendsto_volume_filter ?_
  have hev : (fun Δ : Finset S ↦
        logDensity ρ Λ (vacuum a (Δ \ Λ) η) - logDensity ρ Λ (vacuum a Δ η))
      =ᶠ[atTop] fun Δ : Finset S ↦ ∑ A ∈ Δ.powerset, (gasPotential ρ a).hamiltonianTerms Λ η A := by
    filter_upwards [eventually_ge_atTop Λ] with Δ hΔ
    exact (sum_powerset_hamiltonianTerms_gasPotential hρ hpos hfin a hΔ η).symm
  refine Tendsto.congr' hev ?_
  exact (tendsto_logDensity_vacuum_sdiff (hql Λ) hpos hfin a η).sub
    (tendsto_logDensity_vacuum (hql Λ) hpos hfin a η)

/-- `Φ^a` satisfies Georgii's Definition (2.2)(ii): its Hamiltonian series converges. -/
theorem isSummable_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (a : E) :
    IsSummable (gasPotential ρ a) :=
  ⟨fun Λ η ↦ ⟨_, hasSum_hamiltonianTerms_gasPotential hρ hpos hfin hql a Λ η⟩⟩

/-- **Georgii (2.30), step 4.** `H_Λ^{Φ^a} = v_Λ = α_Λ u_Λ - log ρ_Λ`. -/
theorem hamiltonian_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (a : E) (Λ : Finset S) (η : S → E) :
    (gasPotential ρ a).hamiltonian Λ η
      = logDensity ρ Λ (vacuumOn a Λ η) - logDensity ρ Λ η :=
  (hasSum_hamiltonianTerms_gasPotential hρ hpos hfin hql a Λ η).tsum_eq

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### Georgii (2.30), step 4 (end): the partition function and `ρ^{Φ^a} = ρ` -/

lemma measurable_vacuumOn (a : E) (Λ : Finset S) :
    Measurable (fun η : S → E ↦ vacuumOn a Λ η) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i ∈ Λ
  · simp [vacuumOn, hi]
  · simpa [vacuumOn, hi] using measurable_pi_apply (X := fun _ : S ↦ E) i

omit [MeasurableSpace E] in
lemma vacuumOn_congr_of_eqOn_compl (a : E) (Λ : Finset S) {ζ η : S → E}
    (h : ∀ s ∉ Λ, ζ s = η s) : vacuumOn a Λ ζ = vacuumOn a Λ η := by
  funext i
  by_cases hi : i ∈ Λ
  · rw [vacuumOn_apply_of_mem hi, vacuumOn_apply_of_mem hi]
  · rw [vacuumOn_apply_of_notMem hi, vacuumOn_apply_of_notMem hi, h i hi]

/-- Georgii's `exp(-α_Λ u_Λ)`, the `𝓣_Λ`-measurable factor appearing in step 4 of the proof
of (2.30). -/
noncomputable def vacuumNorm (ρ : Finset S → (S → E) → ℝ≥0∞) (a : E) (Λ : Finset S) (η : S → E) :
    ℝ≥0∞ := ENNReal.ofReal (Real.exp (-logDensity ρ Λ (vacuumOn a Λ η)))

omit [MeasurableSpace E] in
lemma vacuumNorm_ne_zero (a : E) (Λ : Finset S) (η : S → E) : vacuumNorm ρ a Λ η ≠ 0 := by
  simp [vacuumNorm, Real.exp_pos]

omit [MeasurableSpace E] in
lemma vacuumNorm_ne_top (a : E) (Λ : Finset S) (η : S → E) : vacuumNorm ρ a Λ η ≠ ⊤ := by
  simp [vacuumNorm]

lemma measurable_vacuumNorm (hmeas : ∀ Λ, Measurable (ρ Λ)) (a : E) (Λ : Finset S) :
    Measurable (vacuumNorm ρ a Λ) := by
  have : Measurable (fun η : S → E ↦ Real.log ((ρ Λ (vacuumOn a Λ η)).toReal)) :=
    (((hmeas Λ).comp (measurable_vacuumOn a Λ)).ennreal_toReal).log
  exact (this.neg.exp).ennreal_ofReal

omit [MeasurableSpace E] in
lemma vacuumNorm_congr_of_eqOn_compl (a : E) (Λ : Finset S) {ζ η : S → E}
    (h : ∀ s ∉ Λ, ζ s = η s) : vacuumNorm ρ a Λ ζ = vacuumNorm ρ a Λ η := by
  rw [vacuumNorm, vacuumNorm, vacuumOn_congr_of_eqOn_compl a Λ h]

/-- **Georgii (2.30), step 4.** `h_Λ^{Φ^a} = ρ_Λ · exp(-α_Λ u_Λ)`. -/
theorem boltzmannFactor_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (a : E) (Λ : Finset S) (η : S → E) :
    (gasPotential ρ a).boltzmannFactor 1 Λ η = ρ Λ η * vacuumNorm ρ a Λ η := by
  rw [boltzmannFactor, hamiltonian_gasPotential hρ hpos hfin hql a Λ η, vacuumNorm]
  have hsplit : -(1 : ℝ) * (logDensity ρ Λ (vacuumOn a Λ η) - logDensity ρ Λ η)
      = logDensity ρ Λ η + -logDensity ρ Λ (vacuumOn a Λ η) := by ring
  rw [hsplit, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
    exp_logDensity hpos hfin Λ η, ENNReal.ofReal_toReal (hfin Λ η)]

variable (ν : Measure E) [SigmaFinite ν]

/-- **Georgii (2.30), step 4.** `Z_Λ^{Φ^a} = λ_Λ h_Λ^{Φ^a} = exp(-α_Λ u_Λ)`, using `λ_Λ ρ_Λ = 1`.

`α_Λ u_Λ` is `𝓣_Λ`-measurable, so it factors out of the `λ_Λ`-integral, and what is left is
`λ_Λ ρ_Λ = 1`. -/
theorem sigmaFiniteLambdaZ_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1)
    (a : E) (Λ : Finset S) (η : S → E) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
        ((gasPotential ρ a).boltzmannFactor 1) Λ η = vacuumNorm ρ a Λ η := by
  have hmeasρ : ∀ Λ, Measurable (ρ Λ) := hρ.measurable
  have hint : Measurable fun x : S → E ↦ ρ Λ x * vacuumNorm ρ a Λ x :=
    (hmeasρ Λ).mul (measurable_vacuumNorm hmeasρ a Λ)
  have hZρ := hnorm Λ η
  rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map (hmeasρ Λ) (Measurable.juxt (Λ := (Λ : Set S)) (η := η))] at hZρ
  have hgoal : Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
        ((gasPotential ρ a).boltzmannFactor 1) Λ η
      = ∫⁻ x, ρ Λ x * vacuumNorm ρ a Λ x
          ∂(Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) :=
    lintegral_congr fun x ↦ boltzmannFactor_gasPotential hρ hpos hfin hql a Λ x
  rw [hgoal, Specification.sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map hint (Measurable.juxt (Λ := (Λ : Set S)) (η := η))]
  have step : ∀ ζ, ρ Λ (juxt (Λ : Set S) η ζ) * vacuumNorm ρ a Λ (juxt (Λ : Set S) η ζ)
      = ρ Λ (juxt (Λ : Set S) η ζ) * vacuumNorm ρ a Λ η := fun ζ ↦ by
    rw [vacuumNorm_congr_of_eqOn_compl a Λ (juxt_agree_on_compl Λ η ζ)]
  have hmeasj : Measurable fun ζ ↦ ρ Λ (juxt (Λ : Set S) η ζ) :=
    (hmeasρ Λ).comp (Measurable.juxt (Λ := (Λ : Set S)) (η := η))
  rw [lintegral_congr step, lintegral_mul_const _ hmeasj, hZρ, one_mul]

/-- **Georgii (2.30).** `Φ^a` is `λ`-admissible: all partition functions are finite and nonzero. -/
theorem isSigmaFiniteLambdaAdmissible_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1)
    (a : E) :
    Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((gasPotential ρ a).boltzmannFactor 1) := by
  intro Λ η
  rw [sigmaFiniteLambdaZ_gasPotential ν hρ hpos hfin hql hnorm a Λ η]
  exact ⟨vacuumNorm_ne_zero a Λ η, vacuumNorm_ne_top a Λ η⟩

/-- **Georgii, Theorem (2.30): `ρ = ρ^{Φ^a}`.** -/
theorem sigmaFinitePremodifierNorm_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1)
    (a : E) :
    Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
      ((gasPotential ρ a).boltzmannFactor 1) = ρ := by
  funext Λ η
  rw [Specification.sigmaFinitePremodifierNorm,
    sigmaFiniteLambdaZ_gasPotential ν hρ hpos hfin hql hnorm a Λ η,
    boltzmannFactor_gasPotential hρ hpos hfin hql a Λ η,
    ENNReal.mul_div_cancel_right (vacuumNorm_ne_zero a Λ η) (vacuumNorm_ne_top a Λ η)]

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E]

/-! ### Georgii (2.35)(a): a gas potential with `𝓣_Λ`-measurable Hamiltonians vanishes

This is the uniqueness half of Theorem (2.30); Georgii deduces it from Theorems (2.34) and
(2.35)(a).  Note that Georgii's index set is `𝒮 = {Λ ⊆ S : 0 < |Λ| < ∞}` (equation (1.7)), so a
potential carries no term at `∅`; in the present `Potential` type the value at `∅` is invisible to
every Hamiltonian and is therefore only determined once it is normalized to `0`. -/

/-- **Georgii (2.36), for `α = δ_a`.** For a gas potential the partial Hamiltonians at the
configuration `ω_Λ a_{S∖Λ}` are eventually constant, equal to `∑_{∅ ≠ A ⊆ Λ} Φ_A(ω)`. -/
lemma sum_powerset_hamiltonianTerms_vacuum {Θ : Potential S E} [IsPotential Θ] {a : E}
    (hΘ : IsGasPotential a Θ) {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) (ω : S → E) :
    ∑ A ∈ Δ.powerset, Θ.hamiltonianTerms Λ (vacuum a Λ ω) A
      = ∑ A ∈ Λ.powerset.erase ∅, Θ A ω := by
  have hsub : Λ.powerset.erase ∅ ⊆ Δ.powerset := fun A hA ↦
    Finset.mem_powerset.2 ((Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA)).trans hΛΔ)
  have hzero : ∀ A ∈ Δ.powerset, A ∉ Λ.powerset.erase ∅ →
      Θ.hamiltonianTerms Λ (vacuum a Λ ω) A = 0 := by
    intro A _ hA
    by_cases hdisj : Disjoint A Λ
    · exact hamiltonianTerms_of_disjoint hdisj _
    rw [hamiltonianTerms_of_not_disjoint hdisj]
    obtain ⟨j, hjA, hjΛ⟩ := Finset.not_disjoint_iff.1 hdisj
    have hAne : A ≠ ∅ := fun h ↦ by simp [h] at hjA
    have hnotsub : ¬ A ⊆ Λ := fun h ↦ hA (Finset.mem_erase.2 ⟨hAne, Finset.mem_powerset.2 h⟩)
    obtain ⟨i, hiA, hiΛ⟩ := Finset.not_subset.1 hnotsub
    exact hΘ A _ ⟨i, hiA, vacuum_apply_of_notMem hiΛ⟩
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  have hAΛ : A ⊆ Λ := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA)
  have hAne : A ≠ ∅ := Finset.ne_of_mem_erase hA
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hAne
  rw [hamiltonianTerms_of_not_disjoint
      (Finset.not_disjoint_iff.2 ⟨i, hi, hAΛ hi⟩) (vacuum a Λ ω)]
  exact IsPotential.eq_of_eqOn (Φ := Θ) fun x hx ↦ vacuum_apply_of_mem (hAΛ hx)

/-- **Georgii (2.36), for `α = δ_a`.** `α_{S∖Λ} H_Λ^Φ = ∑_{∅ ≠ A ⊆ Λ} Φ_A`. -/
lemma hamiltonian_vacuum {Θ : Potential S E} [IsPotential Θ] [IsSummable Θ] {a : E}
    (hΘ : IsGasPotential a Θ) (Λ : Finset S) (ω : S → E) :
    Θ.hamiltonian Λ (vacuum a Λ ω) = ∑ A ∈ Λ.powerset.erase ∅, Θ A ω := by
  refine tendsto_nhds_unique (hasSum_hamiltonian (Φ := Θ) Λ (vacuum a Λ ω))
    (SummationFilter.tendsto_volume_filter (Tendsto.congr' ?_ tendsto_const_nhds))
  filter_upwards [eventually_ge_atTop Λ] with Δ hΔ
  exact (sum_powerset_hamiltonianTerms_vacuum hΘ hΔ ω).symm

omit [DecidableEq S] in
/-- A gas potential has vanishing Hamiltonians at the constant vacuum configuration. -/
lemma hamiltonian_const_vacuum {Θ : Potential S E} [IsSummable Θ] {a : E}
    (hΘ : IsGasPotential a Θ) (Λ : Finset S) : Θ.hamiltonian Λ (fun _ ↦ a) = 0 := by
  have hterm : Θ.hamiltonianTerms Λ (fun _ : S ↦ a) = fun _ ↦ (0 : ℝ) := by
    funext A
    by_cases hdisj : Disjoint A Λ
    · exact hamiltonianTerms_of_disjoint hdisj _
    rw [hamiltonianTerms_of_not_disjoint hdisj]
    obtain ⟨i, hiA, -⟩ := Finset.not_disjoint_iff.1 hdisj
    exact hΘ A _ ⟨i, hiA, rfl⟩
  rw [hamiltonian, hterm]
  exact tsum_zero

omit [DecidableEq S] in
/-- **Georgii (2.35)(a), for `α = δ_a`.** A gas potential with vacuum state `a` all of whose
Hamiltonians are `𝓣_Λ`-measurable vanishes on every nonempty support. -/
theorem eq_zero_of_isGasPotential {Θ : Potential S E} [IsPotential Θ] [IsSummable Θ] {a : E}
    (hΘ : IsGasPotential a Θ)
    (hdep : ∀ Λ : Finset S, DependsOn (Θ.hamiltonian Λ) ((Λ : Set S)ᶜ))
    {A : Finset S} (hA : A.Nonempty) (ω : S → E) : Θ A ω = 0 := by
  classical
  have main : ∀ B : Finset S, ∑ C ∈ B.powerset.erase ∅, Θ C ω = 0 := by
    intro B
    rw [← hamiltonian_vacuum hΘ B ω]
    rw [hdep B (y := fun _ ↦ a) fun i hi ↦ vacuum_apply_of_notMem (by simpa using hi)]
    exact hamiltonian_const_vacuum hΘ B
  suffices H : ∀ n : ℕ, ∀ B : Finset S, B.card ≤ n → B.Nonempty → Θ B ω = 0 from
    H A.card A le_rfl hA
  intro n
  induction n with
  | zero =>
    intro B hcard hB
    exact absurd (Finset.card_eq_zero.1 (Nat.le_zero.1 hcard))
      (Finset.nonempty_iff_ne_empty.1 hB)
  | succ n ih =>
    intro B hcard hB
    have hBmem : B ∈ B.powerset.erase ∅ :=
      Finset.mem_erase.2 ⟨Finset.nonempty_iff_ne_empty.1 hB, Finset.mem_powerset_self B⟩
    have hsplit := Finset.sum_erase_add (B.powerset.erase ∅) (fun C ↦ Θ C ω) hBmem
    have hzero : ∑ C ∈ (B.powerset.erase ∅).erase B, Θ C ω = 0 := by
      refine Finset.sum_eq_zero fun C hC ↦ ?_
      have hCB : C ≠ B := Finset.ne_of_mem_erase hC
      have hC' := Finset.mem_of_mem_erase hC
      have hC0 : C ≠ ∅ := Finset.ne_of_mem_erase hC'
      have hCsub : C ⊆ B := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hC')
      have hcardC : C.card < B.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hCsub, hCB⟩)
      exact ih C (by omega) (Finset.nonempty_iff_ne_empty.2 hC0)
    rw [hzero, zero_add] at hsplit
    rw [hsplit]
    exact main B

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {Φ Ψ : Potential S E}

/-! ### Differences of potentials -/

omit [DecidableEq S] in
lemma isPotential_sub [IsPotential Φ] [IsPotential Ψ] : IsPotential (Φ - Ψ) where
  measurable A :=
    (IsPotential.measurable (Φ := Φ) A).sub (IsPotential.measurable (Φ := Ψ) A)
end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E] {Φ Ψ : Potential S E}

/-! ### Georgii (2.34), (ii) ⇒ (i): `ρ^Φ = ρ^Ψ` implies `Φ ∼ Ψ`

Georgii's argument: from `ρ_Λ^Φ = ρ_Λ^Ψ` one gets
`H_Λ^{Φ-Ψ} = log (h_Λ^Ψ / h_Λ^Φ) = log (Z_Λ^Ψ / Z_Λ^Φ)`, and the right-hand side is
`𝓣_Λ`-measurable because the partition functions are. -/

omit [Countable S] [DecidableEq S] in
/-- `h_Λ^Φ` is the positive real number `exp(-β H_Λ^Φ)`. -/
lemma toReal_boltzmannFactor (Φ : Potential S E) (β : ℝ) (Λ : Finset S) (η : S → E) :
    (Φ.boltzmannFactor β Λ η).toReal = Real.exp (-β * Φ.hamiltonian Λ η) := by
  rw [boltzmannFactor, ENNReal.toReal_ofReal (Real.exp_pos _).le]

variable (ν : Measure E) [SigmaFinite ν]

omit [Countable S] [DecidableEq S] in
/-- **Georgii (2.34), (ii) ⇒ (i).** If two `λ`-admissible potentials define the same
`λ`-modification then `H_Λ^Φ - H_Λ^Ψ = log (Z_Λ^Ψ / Z_Λ^Φ)`. -/
theorem hamiltonian_sub_eq_log_sigmaFiniteLambdaZ [IsPotential Φ] [IsSummable Φ]
    [IsPotential Ψ] [IsSummable Ψ]
    (hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1))
    (hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    (heq : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1)
      = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    (Λ : Finset S) (η : S → E) :
    Φ.hamiltonian Λ η - Ψ.hamiltonian Λ η
      = Real.log (Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
            (Ψ.boltzmannFactor 1) Λ η).toReal
        - Real.log (Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
            (Φ.boltzmannFactor 1) Λ η).toReal := by
  set ZΦ := Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ η
    with hZΦ
  set ZΨ := Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Ψ.boltzmannFactor 1) Λ η
    with hZΨ
  have hZΦpos : (0 : ℝ) < ZΦ.toReal := ENNReal.toReal_pos (hΦ Λ η).1 (hΦ Λ η).2
  have hZΨpos : (0 : ℝ) < ZΨ.toReal := ENNReal.toReal_pos (hΨ Λ η).1 (hΨ Λ η).2
  have hquot : Φ.boltzmannFactor 1 Λ η / ZΦ = Ψ.boltzmannFactor 1 Λ η / ZΨ := by
    have := congrFun (congrFun heq Λ) η
    simpa [Specification.sigmaFinitePremodifierNorm, hZΦ, hZΨ] using this
  have hreal : Real.exp (-1 * Φ.hamiltonian Λ η) / ZΦ.toReal
      = Real.exp (-1 * Ψ.hamiltonian Λ η) / ZΨ.toReal := by
    have h := congrArg ENNReal.toReal hquot
    rwa [ENNReal.toReal_div, ENNReal.toReal_div, toReal_boltzmannFactor,
      toReal_boltzmannFactor] at h
  have hlog := congrArg Real.log hreal
  rw [Real.log_div (Real.exp_ne_zero _) hZΦpos.ne', Real.log_div (Real.exp_ne_zero _) hZΨpos.ne',
    Real.log_exp, Real.log_exp] at hlog
  linarith

omit [DecidableEq S] in
/-- **Georgii (2.34), (ii) ⇒ (i).** If two `λ`-admissible potentials define the same
`λ`-modification then they are equivalent in the sense of Georgii (2.33): the Hamiltonians of
`Φ - Ψ` are `𝓣_Λ`-measurable. -/
theorem dependsOn_hamiltonian_sub_of_sigmaFinitePremodifierNorm_eq [IsPotential Φ] [IsSummable Φ]
    [IsPotential Ψ] [IsSummable Ψ]
    (hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1))
    (hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    (heq : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1)
      = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    (Λ : Finset S) : DependsOn ((Φ - Ψ).hamiltonian Λ) ((Λ : Set S)ᶜ) := by
  intro x y hxy
  have hxy' : ∀ s ∉ Λ, x s = y s := fun s hs ↦ hxy s (by simpa using hs)
  rw [hamiltonian_sub _ _ Λ x, hamiltonian_sub _ _ Λ y,
    hamiltonian_sub_eq_log_sigmaFiniteLambdaZ ν hΦ hΨ heq Λ x,
    hamiltonian_sub_eq_log_sigmaFiniteLambdaZ ν hΦ hΨ heq Λ y,
    Specification.sigmaFiniteLambdaZ_congr_of_eqOn_compl (ρ := Φ.boltzmannFactor 1) ν
      (measurable_boltzmannFactor (Φ := Φ) 1 Λ) hxy',
    Specification.sigmaFiniteLambdaZ_congr_of_eqOn_compl (ρ := Ψ.boltzmannFactor 1) ν
      (measurable_boltzmannFactor (Φ := Ψ) 1 Λ) hxy']

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E]
  {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### Georgii (2.30), step 5: uniqueness -/

variable (ν : Measure E) [SigmaFinite ν]

omit [DecidableEq S] in
/-- **Georgii (2.30), step 5.**  Two `λ`-admissible gas potentials with the same vacuum state `a`
which define the same `λ`-modification coincide on every nonempty interaction support.

This is Georgii's deduction of uniqueness from Theorems (2.34) and (2.35)(a): the difference
`Φ - Ψ` is a gas potential with vacuum state `a` (Georgii (2.29)(1)) whose Hamiltonians are
`𝓣_Λ`-measurable by (2.34)(ii)⇒(i), hence it vanishes by (2.35)(a). -/
theorem eq_of_isGasPotential_of_sigmaFinitePremodifierNorm_eq
    {a : E} {Φ Ψ : Potential S E} [IsPotential Φ] [IsSummable Φ] [IsPotential Ψ] [IsSummable Ψ]
    (hΦgas : IsGasPotential a Φ) (hΨgas : IsGasPotential a Ψ)
    (hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1))
    (hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    (heq : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1)
      = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    {A : Finset S} (hA : A.Nonempty) (ω : S → E) : Φ A ω = Ψ A ω := by
  have : IsPotential (Φ - Ψ) := isPotential_sub
  have : IsSummable (Φ - Ψ) := isSummable_sub Φ Ψ
  have hgas : IsGasPotential a (Φ - Ψ) := hΦgas.sub hΨgas
  have h : (Φ - Ψ) A ω = 0 :=
    eq_zero_of_isGasPotential (Θ := (Φ - Ψ)) hgas
      (fun Λ ↦ dependsOn_hamiltonian_sub_of_sigmaFinitePremodifierNorm_eq ν hΦ hΨ heq Λ) hA ω
  have h' : Φ A ω - Ψ A ω = 0 := h
  linarith

/-! ### Georgii, Theorem (2.30) -/

omit [DecidableEq S] in
/-- **Georgii, Theorem (2.30): the Gibbs representation theorem.**

Let `λ = ν` be an a priori measure on the single-spin space `(E, 𝓔)` and let `ρ = (ρ_Λ)` be a
positive quasilocal pre-modification with `λ_Λ ρ_Λ = 1` for every finite volume `Λ`.  Then for
each `a ∈ E` there is a *unique* `λ`-admissible gas potential `Φ^a` with vacuum state `a` such
that `ρ = ρ^{Φ^a}`.

The potential is the explicit inclusion–exclusion (Möbius) expression of the proof of (2.30),

`Φ^a_A(ω) = - ∑_{C ⊆ A} (-1)^{|A ∖ C|} log ρ_A(ω_C a_{S∖C})`,

namely `Potential.gasPotential ρ a`.  Uniqueness is asserted on Georgii's index set
`𝒮 = {A : 0 < |A| < ∞}`; the value of a potential at `A = ∅` enters no Hamiltonian and is
therefore not determined by `ρ`. -/
theorem exists_unique_isGasPotential_sigmaFinitePremodifierNorm_eq
    (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1)
    (a : E) :
    ∃ Φ : Potential S E, IsPotential Φ ∧ IsSummable Φ ∧ IsGasPotential a Φ ∧
      Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1) ∧
      Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1) = ρ ∧
      ∀ Ψ : Potential S E, IsPotential Ψ → IsSummable Ψ → IsGasPotential a Ψ →
        Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1) →
        Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor 1) = ρ →
        ∀ A : Finset S, A.Nonempty → Ψ A = Φ A := by
  classical
  have hΦP : IsPotential (gasPotential ρ a) := isPotential_gasPotential hρ.measurable a
  have hΦS : IsSummable (gasPotential ρ a) := isSummable_gasPotential hρ hpos hfin hql a
  have hΦadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((gasPotential ρ a).boltzmannFactor 1) :=
    isSigmaFiniteLambdaAdmissible_gasPotential ν hρ hpos hfin hql hnorm a
  have hΦρ : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
      ((gasPotential ρ a).boltzmannFactor 1) = ρ :=
    sigmaFinitePremodifierNorm_gasPotential ν hρ hpos hfin hql hnorm a
  refine ⟨gasPotential ρ a, hΦP, hΦS, isGasPotential_gasPotential ρ a, hΦadm, hΦρ, ?_⟩
  intro Ψ hΨP hΨS hΨgas hΨadm hΨρ A hA
  have := hΨP
  have := hΨS
  funext ω
  exact eq_of_isGasPotential_of_sigmaFinitePremodifierNorm_eq ν hΨgas
    (isGasPotential_gasPotential ρ a) hΨadm hΦadm (hΨρ.trans hΦρ.symm) hA ω

/-- **Georgii (2.30): every positive quasilocal `λ`-specification is Gibbsian.**

The finite-volume Gibbs kernels of the potential `Φ^a` are literally the kernels
`γ_Λ(· | η) = λ_Λ(· | η) ρ_Λ` of the given `λ`-specification `γ = ρλ`. -/
theorem sigmaFinitePremodifierKernel_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1)
    (a : E) (Λ : Finset S) (η : S → E) :
    haveI : IsPotential (gasPotential ρ a) := isPotential_gasPotential hρ.measurable a
    haveI : IsSummable (gasPotential ρ a) := isSummable_gasPotential hρ hpos hfin hql a
    Specification.sigmaFinitePremodifierKernel (S := S) (E := E) ν
        ((gasPotential ρ a).boltzmannFactor 1)
        (isPremodifier_boltzmannFactor (Φ := gasPotential ρ a) 1) Λ η
      = (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η).withDensity (ρ Λ) := by
  have : IsPotential (gasPotential ρ a) := isPotential_gasPotential hρ.measurable a
  have : IsSummable (gasPotential ρ a) := isSummable_gasPotential hρ hpos hfin hql a
  rw [Specification.sigmaFinitePremodifierKernel_apply,
    sigmaFinitePremodifierNorm_gasPotential ν hρ hpos hfin hql hnorm a]

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E]

/-! ### Georgii's kernels `α_Λ` and `α_{S∖Λ}` of Remark (1.25)

For a single-site probability measure `α ∈ 𝓟(E, 𝓔)`, `α_B f (ω) = ∫ α^B(dζ) f(ζ_B ω_{S∖B})`
averages the sites of `B` independently over `α` while freezing `ω` off `B`.  Because the
coordinates off `B` are ignored, this average may equivalently be taken against the full
product measure `α^S = Measure.infinitePi (fun _ ↦ α)`, and that is the form used here.
Only the two shapes `B = Λ` and `B = S ∖ C` with `Λ`, `C` finite occur in Georgii's
Theorem (2.30) and Theorem (2.35). -/

omit [DecidableEq S] in
private lemma abs_integral_le_of_abs_le {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    {g : (S → E) → ℝ} {M : ℝ} (hgb : ∀ x, |g x| ≤ M) :
    |∫ x, g x ∂μ| ≤ M := by
  have h : ‖∫ x, g x ∂μ‖ ≤ M * μ.real Set.univ :=
    norm_integral_le_of_norm_le_const
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hgb x)
  simpa using h

omit [DecidableEq S] in
private lemma integrable_of_abs_le {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    {g : (S → E) → ℝ} {M : ℝ} (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ M) : Integrable g μ :=
  Integrable.mono' (integrable_const M) hgm.aestronglyMeasurable
    (.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hgb x)

omit [DecidableEq S] in
private lemma abs_integral_sub_le {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    {g h : (S → E) → ℝ} (hg : Integrable g μ) (hh : Integrable h μ) {ε : ℝ}
    (hgh : ∀ x, |g x - h x| ≤ ε) : |(∫ x, g x ∂μ) - ∫ x, h x ∂μ| ≤ ε := by
  rw [← integral_sub hg hh]
  have h : ‖∫ x, (g x - h x) ∂μ‖ ≤ ε * μ.real Set.univ :=
    norm_integral_le_of_norm_le_const
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hgh x)
  simpa using h

variable (α : Measure E) [IsProbabilityMeasure α]

/-- **Georgii, Remark (1.25).** The kernel `α_Λ` acting on functions:
`α_Λ f (ω) = ∫ α^Λ(dζ) f(ζ_Λ ω_{S∖Λ})`. -/
noncomputable def avgOn (Λ : Finset S) (f : (S → E) → ℝ) (η : S → E) : ℝ :=
  ∫ ζ, f (vacuumCfg η Λ ζ) ∂(Measure.infinitePi fun _ : S ↦ α)

/-- **Georgii, Remark (1.25).** The kernel `α_{S∖C}` acting on functions:
`α_{S∖C} f (ω) = ∫ α^{S∖C}(dζ) f(ω_C ζ_{S∖C})`. -/
noncomputable def avgOff (C : Finset S) (f : (S → E) → ℝ) (η : S → E) : ℝ :=
  ∫ ζ, f (vacuumCfg ζ C η) ∂(Measure.infinitePi fun _ : S ↦ α)

variable {α}

lemma integrable_comp_vacuumCfg_left {f : (S → E) → ℝ} {M : ℝ} (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ M) (Λ : Finset S) (η : S → E) :
    Integrable (fun ζ ↦ f (vacuumCfg η Λ ζ)) (Measure.infinitePi fun _ : S ↦ α) :=
  integrable_of_abs_le (hfm.comp (measurable_vacuumCfg η Λ)) fun _ ↦ hfb _

lemma integrable_comp_vacuumCfg_right {f : (S → E) → ℝ} {M : ℝ} (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ M) (C : Finset S) (η : S → E) :
    Integrable (fun ζ ↦ f (vacuumCfg ζ C η)) (Measure.infinitePi fun _ : S ↦ α) :=
  integrable_of_abs_le (hfm.comp (measurable_vacuumCfg_ref C η)) fun _ ↦ hfb _

omit [IsProbabilityMeasure α] in
/-- `α_{S∖C} f` is `𝓕_C`-measurable. -/
lemma dependsOn_avgOff (C : Finset S) (f : (S → E) → ℝ) :
    DependsOn (avgOff α C f) (C : Set S) := by
  intro x y h
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ ↦ ?_)
  exact congrArg f (vacuumCfg_congr (ζ := ζ) fun i hi ↦ h i (by exact_mod_cast hi))

omit [IsProbabilityMeasure α] in
/-- `α_Λ f` is `𝓣_Λ`-measurable. -/
lemma dependsOn_avgOn (Λ : Finset S) (f : (S → E) → ℝ) :
    DependsOn (avgOn α Λ f) ((Λ : Set S)ᶜ) := by
  intro x y h
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ ↦ ?_)
  refine congrArg f (funext fun i ↦ ?_)
  by_cases hi : i ∈ Λ
  · rw [vacuumCfg_apply_of_mem hi, vacuumCfg_apply_of_mem hi]
  · rw [vacuumCfg_apply_of_notMem hi, vacuumCfg_apply_of_notMem hi, h i (by simpa using hi)]

lemma measurable_avgOff {f : (S → E) → ℝ} (hfm : Measurable f) (C : Finset S) :
    Measurable (avgOff α C f) := by
  have h : StronglyMeasurable (fun p : (S → E) × (S → E) ↦ f (vacuumCfg p.2 C p.1)) :=
    (hfm.comp ((measurable_vacuumCfg_prod C).comp measurable_swap)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := Measure.infinitePi fun _ : S ↦ α)).measurable

lemma measurable_avgOn {f : (S → E) → ℝ} (hfm : Measurable f) (Λ : Finset S) :
    Measurable (avgOn α Λ f) := by
  have h : StronglyMeasurable (fun p : (S → E) × (S → E) ↦ f (vacuumCfg p.1 Λ p.2)) :=
    (hfm.comp (measurable_vacuumCfg_prod Λ)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := Measure.infinitePi fun _ : S ↦ α)).measurable

lemma abs_avgOff_le {f : (S → E) → ℝ} {M : ℝ} (hfb : ∀ x, |f x| ≤ M) (C : Finset S) (η : S → E) :
    |avgOff α C f η| ≤ M :=
  abs_integral_le_of_abs_le fun _ ↦ hfb _

lemma abs_avgOn_le {f : (S → E) → ℝ} {M : ℝ} (hfb : ∀ x, |f x| ≤ M) (Λ : Finset S) (η : S → E) :
    |avgOn α Λ f η| ≤ M :=
  abs_integral_le_of_abs_le fun _ ↦ hfb _

/-- **Georgii, proof of (2.35)(a).** `α_{S∖Λ} f = f` for an `𝓕_Λ`-measurable `f`. -/
lemma avgOff_eq_of_dependsOn {f : (S → E) → ℝ} {C : Finset S} (hf : DependsOn f (C : Set S)) :
    avgOff α C f = f := by
  funext η
  have h : ∀ ζ : S → E, f (vacuumCfg ζ C η) = f η := fun ζ ↦
    hf fun i hi ↦ vacuumCfg_apply_of_mem (by exact_mod_cast hi)
  simp [avgOff, h]

/-- `α_Λ f = f` for a `𝓣_Λ`-measurable `f`. -/
lemma avgOn_eq_of_dependsOn_compl {f : (S → E) → ℝ} {Λ : Finset S}
    (hf : DependsOn f ((Λ : Set S)ᶜ)) : avgOn α Λ f = f := by
  funext η
  have h : ∀ ζ : S → E, f (vacuumCfg η Λ ζ) = f η := fun ζ ↦
    hf fun i hi ↦ vacuumCfg_apply_of_notMem (by simpa using hi)
  simp [avgOn, h]

omit [IsProbabilityMeasure α] in
lemma avgOn_const_mul (c : ℝ) (f : (S → E) → ℝ) (Λ : Finset S) (η : S → E) :
    avgOn α Λ (fun x ↦ c * f x) η = c * avgOn α Λ f η := integral_const_mul _ _

omit [IsProbabilityMeasure α] in
lemma avgOff_const_mul (c : ℝ) (f : (S → E) → ℝ) (C : Finset S) (η : S → E) :
    avgOff α C (fun x ↦ c * f x) η = c * avgOff α C f η := integral_const_mul _ _

lemma avgOn_sub {f g : (S → E) → ℝ} {Mf Mg : ℝ} (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ Mf)
    (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ Mg) (Λ : Finset S) (η : S → E) :
    avgOn α Λ (fun x ↦ f x - g x) η = avgOn α Λ f η - avgOn α Λ g η :=
  integral_sub (integrable_comp_vacuumCfg_left hfm hfb Λ η)
    (integrable_comp_vacuumCfg_left hgm hgb Λ η)

lemma avgOff_finset_sum {ι : Type*} (s : Finset ι) (F : ι → (S → E) → ℝ) {M : ι → ℝ}
    (hFm : ∀ j, Measurable (F j)) (hFb : ∀ j x, |F j x| ≤ M j) (C : Finset S) (η : S → E) :
    avgOff α C (fun x ↦ ∑ j ∈ s, F j x) η = ∑ j ∈ s, avgOff α C (F j) η :=
  integral_finsetSum s fun j _ ↦ integrable_comp_vacuumCfg_right (hFm j) (hFb j) C η

lemma avgOn_finset_sum {ι : Type*} (s : Finset ι) (F : ι → (S → E) → ℝ) {M : ι → ℝ}
    (hFm : ∀ j, Measurable (F j)) (hFb : ∀ j x, |F j x| ≤ M j) (Λ : Finset S) (η : S → E) :
    avgOn α Λ (fun x ↦ ∑ j ∈ s, F j x) η = ∑ j ∈ s, avgOn α Λ (F j) η :=
  integral_finsetSum s fun j _ ↦ integrable_comp_vacuumCfg_left (hFm j) (hFb j) Λ η

omit [MeasurableSpace E] in
lemma vacuumCfg_singleton (η ζ : S → E) (i : S) :
    vacuumCfg η {i} ζ = Function.update η i (ζ i) := by
  funext x
  by_cases hx : x = i
  · subst hx; simp [vacuumCfg]
  · rw [vacuumCfg_apply_of_notMem (by simpa using hx), Function.update_of_ne hx]

/-- **Georgii, proof of (2.30), step 1(iii).** For `i ∉ C` one has
`α_{i} α_{S∖(C ∪ {i})} = α_{S∖C}`: resampling the site `i` after resampling everything outside
`C ∪ {i}` is the same as resampling everything outside `C`. -/
lemma avgOn_singleton_avgOff_insert {f : (S → E) → ℝ} {M : ℝ} (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ M) {C : Finset S} {i : S} (hi : i ∉ C) :
    avgOn α {i} (avgOff α (insert i C) f) = avgOff α C f := by
  funext η
  have hFind : ∀ (ω : S → E) (e x : E),
      f (vacuumCfg (Function.update ω i x) (insert i C) (Function.update η i e))
        = f (vacuumCfg ω (insert i C) (Function.update η i e)) := by
    intro ω e x
    refine congrArg f (funext fun y ↦ ?_)
    by_cases hy : y ∈ insert i C
    · rw [vacuumCfg_apply_of_mem hy, vacuumCfg_apply_of_mem hy]
    · have hyi : y ≠ i := fun h ↦ hy (by simp [h])
      rw [vacuumCfg_apply_of_notMem hy, vacuumCfg_apply_of_notMem hy,
        Function.update_of_ne hyi]
  have hdiag : ∀ ω : S → E,
      f (vacuumCfg ω (insert i C) (Function.update η i (ω i))) = f (vacuumCfg ω C η) := by
    intro ω
    refine congrArg f (funext fun y ↦ ?_)
    by_cases hy : y ∈ insert i C
    · rcases Finset.mem_insert.1 hy with rfl | hyC
      · rw [vacuumCfg_apply_of_mem hy, Function.update_self, vacuumCfg_apply_of_notMem hi]
      · have hyi : y ≠ i := fun h ↦ hi (h ▸ hyC)
        rw [vacuumCfg_apply_of_mem hy, Function.update_of_ne hyi, vacuumCfg_apply_of_mem hyC]
    · have hyi : y ≠ i := fun h ↦ hy (by simp [h])
      have hyC : y ∉ C := fun h ↦ hy (Finset.mem_insert_of_mem h)
      rw [vacuumCfg_apply_of_notMem hy, vacuumCfg_apply_of_notMem hyC]
  have hint : Integrable
      (fun ω : S → E ↦ f (vacuumCfg ω (insert i C) (Function.update η i (ω i))))
      (Measure.infinitePi fun _ : S ↦ α) := by
    simp only [hdiag]
    exact integrable_comp_vacuumCfg_right hfm hfb C η
  have h3 := Measure.integral_infinitePi_eval_diag' (fun _ : S ↦ α) i
    (F := fun ξ e ↦ f (vacuumCfg ξ (insert i C) (Function.update η i e))) hFind hint
  have hmu : Measurable (fun e : E ↦ Function.update η i e) := by fun_prop
  have h1a : avgOn α {i} (avgOff α (insert i C) f) η
      = ∫ ζ, avgOff α (insert i C) f (Function.update η i (ζ i))
          ∂(Measure.infinitePi fun _ : S ↦ α) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ζ ↦
      congrArg (avgOff α (insert i C) f) (vacuumCfg_singleton η ζ i))
  have h1b : ∫ ζ, avgOff α (insert i C) f (Function.update η i (ζ i))
          ∂(Measure.infinitePi fun _ : S ↦ α)
      = ∫ e, avgOff α (insert i C) f (Function.update η i e) ∂α :=
    Measure.integral_infinitePi_eval (fun _ : S ↦ α) i
      (((measurable_avgOff hfm (insert i C)).comp hmu).aestronglyMeasurable)
  have h1c : ∫ e, avgOff α (insert i C) f (Function.update η i e) ∂α
      = ∫ e, (∫ ω, f (vacuumCfg ω (insert i C) (Function.update η i e))
          ∂(Measure.infinitePi fun _ : S ↦ α)) ∂α := rfl
  rw [h1a, h1b, h1c, ← h3]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ hdiag ω)

/-- The common Fubini step behind `α_{S∖Λ} α_{i} = α_{S∖Λ}` (`i ∉ Λ`) and
`α_B α_{i} = α_B` (`i ∈ B`): if the site `i` of the resampled configuration `T ω` is read off
`ω` itself and `T` interacts with the coordinate `i` only there, then resampling it once more
changes nothing. -/
private lemma integral_comp_avgOn_singleton {f : (S → E) → ℝ} {M : ℝ} (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ M) (i : S) {T : (S → E) → (S → E)} (hTm : Measurable T)
    (hTi : ∀ ω, T ω i = ω i)
    (hTupd : ∀ (ω : S → E) (e x : E),
      Function.update (T (Function.update ω i x)) i e = Function.update (T ω) i e) :
    ∫ ω, avgOn α {i} f (T ω) ∂(Measure.infinitePi fun _ : S ↦ α)
      = ∫ ω, f (T ω) ∂(Measure.infinitePi fun _ : S ↦ α) := by
  have hFind : ∀ (ω : S → E) (e x : E),
      f (Function.update (T (Function.update ω i x)) i e) = f (Function.update (T ω) i e) :=
    fun ω e x ↦ congrArg f (hTupd ω e x)
  have hdiag : ∀ ω : S → E, f (Function.update (T ω) i (ω i)) = f (T ω) := by
    intro ω
    rw [show (ω i) = T ω i from (hTi ω).symm, Function.update_eq_self]
  have hint : Integrable (fun ω : S → E ↦ f (Function.update (T ω) i (ω i)))
      (Measure.infinitePi fun _ : S ↦ α) := by
    simp only [hdiag]
    exact integrable_of_abs_le (hfm.comp hTm) fun _ ↦ hfb _
  have h3 := Measure.integral_infinitePi_eval_diag (fun _ : S ↦ α) i
    (F := fun ω e ↦ f (Function.update (T ω) i e)) hFind hint
  have hinner : ∀ ω : S → E, avgOn α {i} f (T ω)
      = ∫ e, f (Function.update (T ω) i e) ∂α := by
    intro ω
    have hmu : Measurable (fun e : E ↦ Function.update (T ω) i e) := by fun_prop
    have ha : avgOn α {i} f (T ω)
        = ∫ ξ, f (Function.update (T ω) i (ξ i)) ∂(Measure.infinitePi fun _ : S ↦ α) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦
        congrArg f (vacuumCfg_singleton (T ω) ξ i))
    rw [ha]
    exact Measure.integral_infinitePi_eval (fun _ : S ↦ α) i
      ((hfm.comp hmu).aestronglyMeasurable)
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ hinner ω), ← h3]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ hdiag ω)

/-- **Georgii, proof of (2.35)(a).** For `i ∉ Λ` one has `α_{S∖Λ} α_{i} = α_{S∖Λ}`. -/
lemma avgOff_avgOn_singleton {f : (S → E) → ℝ} {M : ℝ} (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ M) {Λ : Finset S} {i : S} (hi : i ∉ Λ) :
    avgOff α Λ (avgOn α {i} f) = avgOff α Λ f := by
  funext η
  refine integral_comp_avgOn_singleton hfm hfb i (measurable_vacuumCfg_ref Λ η)
    (fun _ ↦ vacuumCfg_apply_of_notMem hi) fun ω e x ↦ ?_
  funext y
  by_cases hy : y = i
  · subst hy; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hy, Function.update_of_ne hy]
    by_cases hyΛ : y ∈ Λ
    · rw [vacuumCfg_apply_of_mem hyΛ, vacuumCfg_apply_of_mem hyΛ]
    · rw [vacuumCfg_apply_of_notMem hyΛ, vacuumCfg_apply_of_notMem hyΛ,
        Function.update_of_ne hy]

/-- **Georgii (2.29)(1).** For `i ∈ B` one has `α_B α_{i} = α_B`; this is why a potential is
`α`-normalized as soon as `α_{i} Φ_A = 0` for every `i ∈ A`. -/
lemma avgOn_avgOn_singleton {f : (S → E) → ℝ} {M : ℝ} (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ M) {B : Finset S} {i : S} (hi : i ∈ B) :
    avgOn α B (avgOn α {i} f) = avgOn α B f := by
  funext η
  refine integral_comp_avgOn_singleton hfm hfb i (measurable_vacuumCfg η B)
    (fun _ ↦ vacuumCfg_apply_of_mem hi) fun ω e x ↦ ?_
  funext y
  by_cases hy : y = i
  · subst hy; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hy, Function.update_of_ne hy]
    by_cases hyB : y ∈ B
    · rw [vacuumCfg_apply_of_mem hyB, vacuumCfg_apply_of_mem hyB, Function.update_of_ne hy]
    · rw [vacuumCfg_apply_of_notMem hyB, vacuumCfg_apply_of_notMem hyB]

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### Georgii (2.28) and (2.2)(ii): `α`-normalized and uniformly convergent potentials -/

/-- **Georgii (2.28).** A potential `Φ` is *`α`-normalized* when `α_B Φ_A = 0` whenever
`∅ ≠ B ⊆ A ∈ 𝒮`.  The gas potentials with vacuum state `a` are the case `α = δ_a`
(`Potential.IsGasPotential`). -/
def IsNormalized (α : Measure E) [IsProbabilityMeasure α] (Φ : Potential S E) : Prop :=
  ∀ A B : Finset S, B.Nonempty → B ⊆ A → avgOn α B (Φ A) = 0

/-- **Georgii (2.29)(1).** For bounded measurable interactions, `α`-normalization follows from
the single-site conditions `α_{i} Φ_A = 0`, `i ∈ A`. -/
lemma isNormalized_of_avgOn_singleton (α : Measure E) [IsProbabilityMeasure α]
    {Φ : Potential S E} (hΦm : ∀ A, Measurable (Φ A))
    (hΦb : ∀ A : Finset S, ∃ M : ℝ, ∀ η, |Φ A η| ≤ M)
    (h : ∀ A : Finset S, ∀ i ∈ A, avgOn α {i} (Φ A) = 0) : IsNormalized α Φ := by
  intro A B hB hBA
  obtain ⟨i, hiB⟩ := hB
  obtain ⟨M, hM⟩ := hΦb A
  rw [← avgOn_avgOn_singleton (hΦm A) hM hiB, h A i (hBA hiB)]
  funext η
  simp [avgOn]

/-- Georgii's extra hypothesis in the second assertion of (2.30): `log ρ_Λ` is bounded for every
finite volume `Λ`. -/
def HasBddLogDensity (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop :=
  ∀ Λ : Finset S, ∃ M : ℝ, ∀ η : S → E, |logDensity ρ Λ η| ≤ M

omit [DecidableEq S] in
lemma measurable_logDensity (hmeas : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) :
    Measurable (logDensity ρ Λ) := (((hmeas Λ).ennreal_toReal).log)

omit [DecidableEq S] [MeasurableSpace E] in
private lemma abs_log_sub_log_le {c x y : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  have key : ∀ u v : ℝ, c ≤ u → u ≤ v → Real.log v - Real.log u ≤ (v - u) / c := by
    intro u v hu huv
    have hu0 : 0 < u := lt_of_lt_of_le hc hu
    have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
    have h1 : Real.log v - Real.log u = Real.log (v / u) := (Real.log_div hv0.ne' hu0.ne').symm
    have h2 : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : v / u - 1 = (v - u) / u := by field_simp
    have h4 : (v - u) / u ≤ (v - u) / c :=
      div_le_div_of_nonneg_left (by linarith) hc hu
    linarith
  rcases le_total x y with h | h
  · have hlog : Real.log x ≤ Real.log y := Real.log_le_log (lt_of_lt_of_le hc hx) h
    have habs : |x - y| = y - x := by rw [abs_of_nonpos (by linarith)]; ring
    rw [abs_of_nonpos (by linarith), habs]
    have := key x y hx h
    linarith
  · have hlog : Real.log y ≤ Real.log x := Real.log_le_log (lt_of_lt_of_le hc hy) h
    have habs : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [abs_of_nonneg (by linarith), habs]
    exact key y x hy h

omit [DecidableEq S] [MeasurableSpace E] in
/-- **Georgii, proof of (2.30), step 4.** For a positive pre-modification with bounded
log-density, quasilocality of `ρ_Λ` entails quasilocality of `u_Λ = log ρ_Λ`. -/
lemma isQuasilocalFun_logDensity (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    {Λ : Finset S} (hql : IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) {M : ℝ}
    (hM : ∀ η, |logDensity ρ Λ η| ≤ M) : IsQuasilocalFun (logDensity ρ Λ) := by
  intro ε hε
  have hc : (0 : ℝ) < Real.exp (-M) := Real.exp_pos _
  have hlow : ∀ η, Real.exp (-M) ≤ (ρ Λ η).toReal := by
    intro η
    have h1 : -M ≤ logDensity ρ Λ η := neg_le_of_abs_le (hM η)
    calc Real.exp (-M) ≤ Real.exp (logDensity ρ Λ η) := Real.exp_le_exp.2 h1
      _ = (ρ Λ η).toReal := exp_logDensity hpos hfin Λ η
  obtain ⟨Δ, hΔ⟩ := hql (ε * Real.exp (-M)) (by positivity)
  refine ⟨Δ, fun ζ η h ↦ ?_⟩
  have h1 := hΔ ζ η h
  calc |logDensity ρ Λ ζ - logDensity ρ Λ η|
      ≤ |(ρ Λ ζ).toReal - (ρ Λ η).toReal| / Real.exp (-M) :=
        abs_log_sub_log_le hc (hlow ζ) (hlow η)
    _ ≤ (ε * Real.exp (-M)) / Real.exp (-M) := by
        exact div_le_div_of_nonneg_right h1 hc.le
    _ = ε := by field_simp

/-! ### Georgii (2.30), second assertion: the `α`-normalized interaction -/

/-- **Georgii, Theorem (2.30), second assertion.** The `α`-normalized interaction of a positive
pre-modification `ρ`: `Φ^α_A = -p_A u_A` with `p_A f = ∑_{C ⊆ A} (-1)^{|A∖C|} α_{S∖C} f` and
`u_A = log ρ_A`.  Explicitly

`Φ^α_A(ω) = - ∑_{C ⊆ A} (-1)^{|A∖C|} ∫ α^S(dζ) log ρ_A(ω_C ζ_{S∖C})`. -/
noncomputable def normalizedPotential (ρ : Finset S → (S → E) → ℝ≥0∞) (α : Measure E)
    [IsProbabilityMeasure α] : Potential S E :=
  fun A η ↦ -∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * avgOff α C (logDensity ρ A) η

variable (α : Measure E) [IsProbabilityMeasure α]

/-- **Georgii, Theorem (2.30), second assertion.** `Φ^α` is the average over `α^S` of the
interactions `Φ^ζ` at a reference configuration: the `α`-normalized potential is obtained from
the vacuum potentials by averaging the vacuum. -/
theorem normalizedPotential_eq_integral (hmeas : ∀ Λ, Measurable (ρ Λ))
    (hbdd : HasBddLogDensity ρ) (A : Finset S) (η : S → E) :
    normalizedPotential ρ α A η
      = ∫ ζ, gasPotentialCfg ρ ζ A η ∂(Measure.infinitePi fun _ : S ↦ α) := by
  obtain ⟨M, hM⟩ := hbdd A
  have hm := measurable_logDensity hmeas A
  have h : ∫ ζ, gasPotentialCfg ρ ζ A η ∂(Measure.infinitePi fun _ : S ↦ α)
      = ∫ ζ, -∑ C ∈ A.powerset,
          (-1 : ℝ) ^ (A \ C).card * logDensity ρ A (vacuumCfg ζ C η)
        ∂(Measure.infinitePi fun _ : S ↦ α) := rfl
  rw [h, integral_neg,
    integral_finsetSum (μ := Measure.infinitePi fun _ : S ↦ α) A.powerset
      (f := fun C : Finset S ↦ fun ζ ↦
        (-1 : ℝ) ^ (A \ C).card * logDensity ρ A (vacuumCfg ζ C η))
      fun C _ ↦ (integrable_comp_vacuumCfg_right hm hM C η).const_mul _]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun C _ ↦ ?_)
  exact (integral_const_mul ((-1 : ℝ) ^ (A \ C).card) _).symm

lemma measurable_normalizedPotential (hmeas : ∀ Λ, Measurable (ρ Λ)) (A : Finset S) :
    Measurable (normalizedPotential ρ α A) := by
  refine Measurable.neg (Finset.measurable_sum _ fun C _ ↦ ?_)
  exact measurable_const.mul (measurable_avgOff (measurable_logDensity hmeas A) C)

lemma dependsOn_normalizedPotential (A : Finset S) :
    DependsOn (normalizedPotential ρ α A) (A : Set S) := by
  refine DependsOn.comp (fun x : ℝ ↦ -x) (DependsOn.sum fun C hC ↦ ?_)
  exact DependsOn.comp (fun x : ℝ ↦ (-1 : ℝ) ^ (A \ C).card * x)
    ((dependsOn_avgOff C (logDensity ρ A)).mono
      (by exact_mod_cast Finset.mem_powerset.1 hC))

/-- `Φ^α_A` is bounded whenever `log ρ_A` is. -/
lemma bdd_normalizedPotential (hbdd : HasBddLogDensity ρ) (A : Finset S) :
    ∃ M : ℝ, ∀ η, |normalizedPotential ρ α A η| ≤ M := by
  obtain ⟨M, hM⟩ := hbdd A
  refine ⟨A.powerset.card * M, fun η ↦ ?_⟩
  rw [normalizedPotential, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ C ∈ A.powerset,
      |(-1 : ℝ) ^ (A \ C).card * avgOff α C (logDensity ρ A) η| ≤ M := by
    intro C _
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_avgOff_le hM C η
  calc ∑ C ∈ A.powerset, |(-1 : ℝ) ^ (A \ C).card * avgOff α C (logDensity ρ A) η|
      ≤ ∑ _C ∈ A.powerset, M := Finset.sum_le_sum hterm
    _ = A.powerset.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Georgii (2.30), step 2.** `Φ^α` is `α`-normalized. -/
theorem isNormalized_normalizedPotential (hmeas : ∀ Λ, Measurable (ρ Λ))
    (hbdd : HasBddLogDensity ρ) : IsNormalized α (normalizedPotential ρ α) := by
  refine isNormalized_of_avgOn_singleton α (measurable_normalizedPotential α hmeas)
    (bdd_normalizedPotential α hbdd) fun A i hiA ↦ ?_
  obtain ⟨M, hM⟩ := hbdd A
  have hm := measurable_logDensity hmeas A
  have hFm : ∀ C : Finset S,
      Measurable (fun x ↦ (-1 : ℝ) ^ (A \ C).card * avgOff α C (logDensity ρ A) x) :=
    fun C ↦ measurable_const.mul (measurable_avgOff hm C)
  have hFb : ∀ (C : Finset S) (x : S → E),
      |(-1 : ℝ) ^ (A \ C).card * avgOff α C (logDensity ρ A) x| ≤ M := by
    intro C x
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_avgOff_le hM C x
  funext η
  change avgOn α {i} (normalizedPotential ρ α A) η = 0
  have h1 : avgOn α {i} (normalizedPotential ρ α A) η
      = -avgOn α {i}
          (fun x ↦ ∑ C ∈ A.powerset,
            (-1 : ℝ) ^ (A \ C).card * avgOff α C (logDensity ρ A) x) η := by
    simp only [normalizedPotential, avgOn, integral_neg]
  rw [h1, avgOn_finset_sum (M := fun _ ↦ M)
      (F := fun C : Finset S ↦
        fun x ↦ (-1 : ℝ) ^ (A \ C).card * avgOff α C (logDensity ρ A) x)
      A.powerset hFm hFb ({i} : Finset S) η,
    neg_eq_zero]
  have h2 : ∀ C : Finset S,
      avgOn α {i} (fun x ↦ (-1 : ℝ) ^ (A \ C).card * avgOff α C (logDensity ρ A) x) η
        = (-1 : ℝ) ^ (A \ C).card * avgOn α {i} (avgOff α C (logDensity ρ A)) η :=
    fun C ↦ avgOn_const_mul _ _ _ _
  simp only [h2]
  refine sum_powerset_neg_one_pow_mul_eq_zero hiA fun C hC ↦ ?_
  have hiC : i ∉ C := fun h ↦ Finset.notMem_erase i A (hC h)
  have hdep : DependsOn (avgOff α C (logDensity ρ A)) ((({i} : Finset S) : Set S)ᶜ) := by
    refine (dependsOn_avgOff C (logDensity ρ A)).mono fun x hx ↦ ?_
    simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact hiC hx
  rw [show avgOn α {i} (avgOff α (insert i C) (logDensity ρ A)) η
      = avgOff α C (logDensity ρ A) η from
    congrFun (avgOn_singleton_avgOff_insert hm hM hiC) η,
    show avgOn α {i} (avgOff α C (logDensity ρ A)) η = avgOff α C (logDensity ρ A) η from
    congrFun (avgOn_eq_of_dependsOn_compl hdep) η]

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞}
/-! ### Georgii (2.30), second assertion, step 4: the Hamiltonian of `Φ^α` -/

lemma measurable_gasPotentialCfg_ref (hmeas : ∀ Λ, Measurable (ρ Λ)) (A : Finset S)
    (η : S → E) : Measurable (fun ζ : S → E ↦ gasPotentialCfg ρ ζ A η) := by
  rw [show (fun ζ : S → E ↦ gasPotentialCfg ρ ζ A η) = fun ζ : S → E ↦
      -∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card
        * Real.log ((ρ A (vacuumCfg ζ C η)).toReal) from rfl]
  refine Measurable.neg (Finset.measurable_sum _ fun C _ ↦ ?_)
  exact measurable_const.mul
    ((((hmeas A).comp (measurable_vacuumCfg_ref C η)).ennreal_toReal).log)

lemma bdd_gasPotentialCfg (hbdd : HasBddLogDensity ρ) (A : Finset S) :
    ∃ M : ℝ, ∀ ζ η : S → E, |gasPotentialCfg ρ ζ A η| ≤ M := by
  obtain ⟨M, hM⟩ := hbdd A
  refine ⟨A.powerset.card * M, fun ζ η ↦ ?_⟩
  rw [gasPotentialCfg, mobiusCfg, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ C ∈ A.powerset,
      |(-1 : ℝ) ^ (A \ C).card * logDensity ρ A (vacuumCfg ζ C η)| ≤ M := by
    intro C _
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hM _
  calc ∑ C ∈ A.powerset, |(-1 : ℝ) ^ (A \ C).card * logDensity ρ A (vacuumCfg ζ C η)|
      ≤ ∑ _C ∈ A.powerset, M := Finset.sum_le_sum hterm
    _ = A.powerset.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

variable (α : Measure E) [IsProbabilityMeasure α]

/-- **Georgii (2.30), step 4.** The partial Hamiltonians of `Φ^α` are the `α^S`-averages of the
partial Hamiltonians of the interactions `Φ^ζ` at a reference configuration. -/
theorem sum_powerset_hamiltonianTerms_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (hbdd : HasBddLogDensity ρ)
    {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) (η : S → E) :
    ∑ A ∈ Δ.powerset, (normalizedPotential ρ α).hamiltonianTerms Λ η A
      = ∫ ζ, (logDensity ρ Λ (vacuumCfg ζ (Δ \ Λ) η) - logDensity ρ Λ (vacuumCfg ζ Δ η))
          ∂(Measure.infinitePi fun _ : S ↦ α) := by
  have hmeas := hρ.measurable
  have hterm : ∀ A : Finset S, (normalizedPotential ρ α).hamiltonianTerms Λ η A
      = ∫ ζ, (gasPotentialCfg ρ ζ).hamiltonianTerms Λ η A
          ∂(Measure.infinitePi fun _ : S ↦ α) := by
    intro A
    by_cases hd : Disjoint A Λ
    · rw [hamiltonianTerms_of_disjoint hd]
      rw [integral_congr_ae (Filter.Eventually.of_forall fun ζ ↦
        hamiltonianTerms_of_disjoint (Φ := gasPotentialCfg ρ ζ) hd η)]
      simp
    · rw [hamiltonianTerms_of_not_disjoint hd,
        normalizedPotential_eq_integral α hmeas hbdd A η]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ζ ↦
        (hamiltonianTerms_of_not_disjoint (Φ := gasPotentialCfg ρ ζ) hd η).symm)
  have hint : ∀ A ∈ Δ.powerset,
      Integrable (fun ζ ↦ (gasPotentialCfg ρ ζ).hamiltonianTerms Λ η A)
        (Measure.infinitePi fun _ : S ↦ α) := by
    intro A _
    obtain ⟨M, hM⟩ := bdd_gasPotentialCfg hbdd A
    by_cases hd : Disjoint A Λ
    · simp only [hamiltonianTerms_of_disjoint hd]
      exact integrable_const 0
    · simp only [hamiltonianTerms_of_not_disjoint hd]
      exact integrable_of_abs_le (measurable_gasPotentialCfg_ref hmeas A η) fun ζ ↦ hM ζ η
  rw [Finset.sum_congr rfl fun A _ ↦ hterm A, ← integral_finsetSum Δ.powerset hint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ζ ↦
    sum_powerset_hamiltonianTerms_gasPotentialCfg hρ hpos hfin ζ hΛΔ η)

/-- **Georgii (2.30), step 4.** The partial Hamiltonians of `Φ^α` converge to
`v_Λ = α_Λ u_Λ - u_Λ` *uniformly* in the configuration. -/
theorem exists_forall_abs_sum_powerset_hamiltonianTerms_normalizedPotential_sub_le
    (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ)
    (Λ : Finset S) {ε : ℝ} (hε : 0 < ε) :
    ∃ Δ₀ : Finset S, ∀ Δ : Finset S, Δ₀ ⊆ Δ → ∀ η : S → E,
      |(∑ A ∈ Δ.powerset, (normalizedPotential ρ α).hamiltonianTerms Λ η A)
        - (avgOn α Λ (logDensity ρ Λ) η - logDensity ρ Λ η)| ≤ ε := by
  obtain ⟨M, hM⟩ := hbdd Λ
  have hm := measurable_logDensity hρ.measurable Λ
  have hqlu : IsQuasilocalFun (logDensity ρ Λ) :=
    isQuasilocalFun_logDensity hpos hfin (hql Λ) hM
  obtain ⟨Δ₁, hΔ₁⟩ := hqlu (ε / 2) (by positivity)
  refine ⟨Δ₁ ∪ Λ, fun Δ hΔ η ↦ ?_⟩
  have hΛΔ : Λ ⊆ Δ := Finset.subset_union_right.trans hΔ
  have hΔ₁Δ : Δ₁ ⊆ Δ := Finset.subset_union_left.trans hΔ
  have hi1 : Integrable (fun ζ ↦ logDensity ρ Λ (vacuumCfg ζ (Δ \ Λ) η))
      (Measure.infinitePi fun _ : S ↦ α) := integrable_comp_vacuumCfg_right hm hM _ η
  have hi2 : Integrable (fun ζ ↦ logDensity ρ Λ (vacuumCfg ζ Δ η))
      (Measure.infinitePi fun _ : S ↦ α) := integrable_comp_vacuumCfg_right hm hM _ η
  have hi3 : Integrable (fun ζ ↦ logDensity ρ Λ (vacuumCfg η Λ ζ))
      (Measure.infinitePi fun _ : S ↦ α) := integrable_comp_vacuumCfg_left hm hM _ η
  have e1 : |(∫ ζ, logDensity ρ Λ (vacuumCfg ζ (Δ \ Λ) η)
        ∂(Measure.infinitePi fun _ : S ↦ α))
      - ∫ ζ, logDensity ρ Λ (vacuumCfg η Λ ζ) ∂(Measure.infinitePi fun _ : S ↦ α)| ≤ ε / 2 := by
    refine abs_integral_sub_le hi1 hi3 fun ζ ↦ hΔ₁ _ _ fun i hi ↦ ?_
    by_cases hiΛ : i ∈ Λ
    · rw [vacuumCfg_apply_of_notMem (by simp [Finset.mem_sdiff, hiΛ]),
        vacuumCfg_apply_of_mem hiΛ]
    · rw [vacuumCfg_apply_of_mem (Finset.mem_sdiff.2 ⟨hΔ₁Δ hi, hiΛ⟩),
        vacuumCfg_apply_of_notMem hiΛ]
  have e2 : |(∫ ζ, logDensity ρ Λ (vacuumCfg ζ Δ η) ∂(Measure.infinitePi fun _ : S ↦ α))
      - logDensity ρ Λ η| ≤ ε / 2 := by
    have h := abs_integral_sub_le (μ := Measure.infinitePi fun _ : S ↦ α) hi2
      (integrable_const (logDensity ρ Λ η)) (ε := ε / 2)
      (fun ζ ↦ hΔ₁ _ _ fun i hi ↦ vacuumCfg_apply_of_mem (hΔ₁Δ hi))
    simpa using h
  rw [sum_powerset_hamiltonianTerms_normalizedPotential α hρ hpos hfin hbdd hΛΔ η,
    integral_sub hi1 hi2]
  have hv : avgOn α Λ (logDensity ρ Λ) η
      = ∫ ζ, logDensity ρ Λ (vacuumCfg η Λ ζ) ∂(Measure.infinitePi fun _ : S ↦ α) := rfl
  rw [hv]
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

/-- **Georgii (2.30), step 4.** The Hamiltonian series of `Φ^α` converges in the sense of
Georgii's Convention (2.1), with sum `v_Λ = α_Λ u_Λ - u_Λ`. -/
theorem hasSum_hamiltonianTerms_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ)
    (Λ : Finset S) (η : S → E) :
    HasSum ((normalizedPotential ρ α).hamiltonianTerms Λ η)
      (avgOn α Λ (logDensity ρ Λ) η - logDensity ρ Λ η) (SummationFilter.volume S) := by
  refine SummationFilter.tendsto_volume_filter ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Δ₀, hΔ₀⟩ := exists_forall_abs_sum_powerset_hamiltonianTerms_normalizedPotential_sub_le
    α hρ hpos hfin hql hbdd Λ (half_pos hε)
  refine ⟨Δ₀, fun Δ hΔ ↦ ?_⟩
  have := hΔ₀ Δ hΔ η
  rw [Real.dist_eq]
  linarith

/-- `Φ^α` satisfies Georgii's Definition (2.2)(ii): its Hamiltonian series converges. -/
theorem isSummable_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ) :
    IsSummable (normalizedPotential ρ α) :=
  ⟨fun Λ η ↦ ⟨_, hasSum_hamiltonianTerms_normalizedPotential α hρ hpos hfin hql hbdd Λ η⟩⟩

/-- **Georgii (2.30), step 4.** `H_Λ^{Φ^α} = v_Λ = α_Λ u_Λ - log ρ_Λ`. -/
theorem hamiltonian_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ)
    (Λ : Finset S) (η : S → E) :
    (normalizedPotential ρ α).hamiltonian Λ η
      = avgOn α Λ (logDensity ρ Λ) η - logDensity ρ Λ η :=
  (hasSum_hamiltonianTerms_normalizedPotential α hρ hpos hfin hql hbdd Λ η).tsum_eq

/-- **Georgii, Theorem (2.30), second assertion.** `Φ^α` is uniformly convergent. -/
theorem isUniformlyConvergent_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ) :
    IsUniformlyConvergent (normalizedPotential ρ α) := by
  intro Λ ε hε
  obtain ⟨Δ₀, hΔ₀⟩ := exists_forall_abs_sum_powerset_hamiltonianTerms_normalizedPotential_sub_le
    α hρ hpos hfin hql hbdd Λ hε
  refine ⟨Δ₀, fun Δ hΔ η ↦ ?_⟩
  rw [hamiltonian_normalizedPotential α hρ hpos hfin hql hbdd Λ η]
  exact hΔ₀ Δ hΔ η

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞}
variable (α : Measure E) [IsProbabilityMeasure α]

/-! ### Georgii (2.30), second assertion, step 4 (end): the partition function -/

/-- Georgii's `exp(-α_Λ u_Λ)`, the `𝓣_Λ`-measurable factor appearing in step 4 of the proof of
(2.30) for a general normalizing measure `α`. -/
noncomputable def avgNorm (ρ : Finset S → (S → E) → ℝ≥0∞) (α : Measure E)
    [IsProbabilityMeasure α] (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-avgOn α Λ (logDensity ρ Λ) η))

lemma avgNorm_ne_zero (Λ : Finset S) (η : S → E) : avgNorm ρ α Λ η ≠ 0 := by
  simp [avgNorm, Real.exp_pos]

lemma avgNorm_ne_top (Λ : Finset S) (η : S → E) : avgNorm ρ α Λ η ≠ ⊤ := by simp [avgNorm]

lemma measurable_avgNorm (hmeas : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) :
    Measurable (avgNorm ρ α Λ) :=
  ((measurable_avgOn (measurable_logDensity hmeas Λ) Λ).neg.exp).ennreal_ofReal

lemma avgNorm_congr_of_eqOn_compl (Λ : Finset S) {ζ η : S → E} (h : ∀ s ∉ Λ, ζ s = η s) :
    avgNorm ρ α Λ ζ = avgNorm ρ α Λ η := by
  rw [avgNorm, avgNorm, dependsOn_avgOn Λ (logDensity ρ Λ) fun s hs ↦ h s (by simpa using hs)]

/-- **Georgii (2.30), second assertion.** `Φ^α` is a potential in the sense of Georgii
(2.2)(i): `Φ^α_A` is `𝓕_A`-measurable. -/
theorem isPotential_normalizedPotential (hmeas : ∀ Λ, Measurable (ρ Λ)) :
    IsPotential (normalizedPotential ρ α) where
  measurable A := (measurable_normalizedPotential α hmeas A).cylinderEvents_of_dependsOn
    (dependsOn_normalizedPotential α A)

/-- **Georgii (2.30), step 4.** `h_Λ^{Φ^α} = ρ_Λ · exp(-α_Λ u_Λ)`. -/
theorem boltzmannFactor_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ)
    (Λ : Finset S) (η : S → E) :
    (normalizedPotential ρ α).boltzmannFactor 1 Λ η = ρ Λ η * avgNorm ρ α Λ η := by
  rw [boltzmannFactor, hamiltonian_normalizedPotential α hρ hpos hfin hql hbdd Λ η, avgNorm]
  have hsplit : -(1 : ℝ) * (avgOn α Λ (logDensity ρ Λ) η - logDensity ρ Λ η)
      = logDensity ρ Λ η + -avgOn α Λ (logDensity ρ Λ) η := by ring
  rw [hsplit, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
    exp_logDensity hpos hfin Λ η, ENNReal.ofReal_toReal (hfin Λ η)]

variable (ν : Measure E) [SigmaFinite ν]

/-- **Georgii (2.30), step 4.** `Z_Λ^{Φ^α} = λ_Λ h_Λ^{Φ^α} = exp(-α_Λ u_Λ)`, using
`λ_Λ ρ_Λ = 1`: the factor `α_Λ u_Λ` is `𝓣_Λ`-measurable and comes out of the integral. -/
theorem sigmaFiniteLambdaZ_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1)
    (Λ : Finset S) (η : S → E) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
        ((normalizedPotential ρ α).boltzmannFactor 1) Λ η = avgNorm ρ α Λ η := by
  have hmeasρ : ∀ Λ, Measurable (ρ Λ) := hρ.measurable
  have hint : Measurable fun x : S → E ↦ ρ Λ x * avgNorm ρ α Λ x :=
    (hmeasρ Λ).mul (measurable_avgNorm α hmeasρ Λ)
  have hZρ := hnorm Λ η
  rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map (hmeasρ Λ) (Measurable.juxt (Λ := (Λ : Set S)) (η := η))] at hZρ
  have hgoal : Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
        ((normalizedPotential ρ α).boltzmannFactor 1) Λ η
      = ∫⁻ x, ρ Λ x * avgNorm ρ α Λ x
          ∂(Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) :=
    lintegral_congr fun x ↦
      boltzmannFactor_normalizedPotential α hρ hpos hfin hql hbdd Λ x
  rw [hgoal, Specification.sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map hint (Measurable.juxt (Λ := (Λ : Set S)) (η := η))]
  have step : ∀ ζ, ρ Λ (juxt (Λ : Set S) η ζ) * avgNorm ρ α Λ (juxt (Λ : Set S) η ζ)
      = ρ Λ (juxt (Λ : Set S) η ζ) * avgNorm ρ α Λ η := fun ζ ↦ by
    rw [avgNorm_congr_of_eqOn_compl α Λ (juxt_agree_on_compl Λ η ζ)]
  have hmeasj : Measurable fun ζ ↦ ρ Λ (juxt (Λ : Set S) η ζ) :=
    (hmeasρ Λ).comp (Measurable.juxt (Λ := (Λ : Set S)) (η := η))
  rw [lintegral_congr step, lintegral_mul_const _ hmeasj, hZρ, one_mul]

/-- **Georgii (2.30), second assertion.** `Φ^α` is `λ`-admissible. -/
theorem isSigmaFiniteLambdaAdmissible_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1) :
    Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((normalizedPotential ρ α).boltzmannFactor 1) := by
  intro Λ η
  rw [sigmaFiniteLambdaZ_normalizedPotential α ν hρ hpos hfin hql hbdd hnorm Λ η]
  exact ⟨avgNorm_ne_zero α Λ η, avgNorm_ne_top α Λ η⟩

/-- **Georgii, Theorem (2.30), second assertion: `ρ = ρ^{Φ^α}`.** -/
theorem sigmaFinitePremodifierNorm_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1) :
    Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
      ((normalizedPotential ρ α).boltzmannFactor 1) = ρ := by
  funext Λ η
  rw [Specification.sigmaFinitePremodifierNorm,
    sigmaFiniteLambdaZ_normalizedPotential α ν hρ hpos hfin hql hbdd hnorm Λ η,
    boltzmannFactor_normalizedPotential α hρ hpos hfin hql hbdd Λ η,
    ENNReal.mul_div_cancel_right (avgNorm_ne_zero α Λ η) (avgNorm_ne_top α Λ η)]

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E]
variable (α : Measure E) [IsProbabilityMeasure α]

/-! ### Georgii (2.35)(a) for a general normalizing measure `α`

An `α`-normalized uniformly convergent potential with bounded interactions and
`𝓣_Λ`-measurable Hamiltonians vanishes.  Georgii's proof of (2.36) is the identity
`α_{S∖Λ} H_Λ^Φ = ∑_{∅ ≠ A ⊆ Λ} Φ_A`: the terms with `A ⊆ Λ` survive because `Φ_A` is
`𝓕_A`-measurable, and the terms meeting `S ∖ Λ` are killed by the normalization through
`α_{S∖Λ} Φ_A = α_{S∖Λ} α_{i} Φ_A = 0`.  Since the left-hand side is constant when `H_Λ^Φ` is
`𝓣_Λ`-measurable, an induction on `|A|` gives `Φ = 0`. -/

variable {Θ : Potential S E}

omit [DecidableEq S] in
private lemma measurable_potential_apply [IsPotential Θ] (A : Finset S) : Measurable (Θ A) :=
  (IsPotential.measurable (Φ := Θ) A).mono cylinderEvents_le_pi le_rfl

/-- **Georgii (2.36).** For `Λ ⊆ Δ`, `α_{S∖Λ} H^Φ_{Λ,Δ} = ∑_{∅ ≠ A ⊆ Λ} Φ_A`. -/
private lemma avgOff_sum_powerset_hamiltonianTerms [IsPotential Θ] {M : Finset S → ℝ}
    (hM : ∀ (A : Finset S) (η : S → E), |Θ A η| ≤ M A) (hM0 : ∀ A, 0 ≤ M A)
    (hΘn : IsNormalized α Θ) {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) (η : S → E) :
    avgOff α Λ (fun x ↦ ∑ A ∈ Δ.powerset, Θ.hamiltonianTerms Λ x A) η
      = ∑ A ∈ Λ.powerset.erase ∅, Θ A η := by
  have hFm : ∀ A : Finset S, Measurable (fun x : S → E ↦ Θ.hamiltonianTerms Λ x A) := by
    intro A
    by_cases hd : Disjoint A Λ
    · simpa only [hamiltonianTerms_of_disjoint hd] using measurable_const (a := (0 : ℝ))
    · simpa only [hamiltonianTerms_of_not_disjoint hd] using measurable_potential_apply (Θ := Θ) A
  have hFb : ∀ (A : Finset S) (x : S → E), |Θ.hamiltonianTerms Λ x A| ≤ M A := by
    intro A x
    by_cases hd : Disjoint A Λ
    · rw [hamiltonianTerms_of_disjoint hd]; simpa using hM0 A
    · rw [hamiltonianTerms_of_not_disjoint hd]; exact hM A x
  have hsub : Λ.powerset.erase ∅ ⊆ Δ.powerset := fun A hA ↦
    Finset.mem_powerset.2 ((Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA)).trans hΛΔ)
  have hzero : ∀ A ∈ Δ.powerset, A ∉ Λ.powerset.erase ∅ →
      avgOff α Λ (fun x ↦ Θ.hamiltonianTerms Λ x A) η = 0 := by
    intro A _ hnot
    by_cases hd : Disjoint A Λ
    · simp only [hamiltonianTerms_of_disjoint hd]
      simp [avgOff]
    · simp only [hamiltonianTerms_of_not_disjoint hd]
      have hAne : A ≠ ∅ := by rintro rfl; exact hd (Finset.disjoint_left.2 (by simp))
      have hnotsub : ¬ A ⊆ Λ := fun h ↦ hnot (Finset.mem_erase.2 ⟨hAne, Finset.mem_powerset.2 h⟩)
      obtain ⟨j, hjA, hjΛ⟩ := Finset.not_subset.1 hnotsub
      have h1 := avgOff_avgOn_singleton (α := α) (measurable_potential_apply (Θ := Θ) A)
        (hM A) hjΛ
      rw [← h1, hΘn A {j} ⟨j, Finset.mem_singleton_self j⟩ (by simpa using hjA)]
      simp [avgOff]
  rw [avgOff_finset_sum (M := M) Δ.powerset (fun A ↦ fun x ↦ Θ.hamiltonianTerms Λ x A) hFm hFb Λ η,
    ← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  have hAΛ : A ⊆ Λ := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA)
  have hAne : A ≠ ∅ := Finset.ne_of_mem_erase hA
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hAne
  have hnd : ¬ Disjoint A Λ := Finset.not_disjoint_iff.2 ⟨i, hi, hAΛ hi⟩
  simp only [hamiltonianTerms_of_not_disjoint hnd]
  exact congrFun (avgOff_eq_of_dependsOn
    ((IsPotential.dependsOn (Φ := Θ) A).mono (by exact_mod_cast hAΛ))) η

omit [IsProbabilityMeasure α] in
private lemma bdd_hamiltonian [IsSummable Θ] {M : Finset S → ℝ}
    (hM : ∀ (A : Finset S) (η : S → E), |Θ A η| ≤ M A) (hM0 : ∀ A, 0 ≤ M A)
    (hΘu : IsUniformlyConvergent Θ) (Λ : Finset S) :
    ∃ K : ℝ, ∀ η, |Θ.hamiltonian Λ η| ≤ K := by
  obtain ⟨Δ₀, hΔ₀⟩ := hΘu Λ (ε := 1) one_pos
  refine ⟨(∑ A ∈ Δ₀.powerset, M A) + 1, fun η ↦ ?_⟩
  have h1 := hΔ₀ Δ₀ (le_refl Δ₀) η
  have h2 : |∑ A ∈ Δ₀.powerset, Θ.hamiltonianTerms Λ η A| ≤ ∑ A ∈ Δ₀.powerset, M A := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun A _ ↦ ?_)
    by_cases hd : Disjoint A Λ
    · rw [hamiltonianTerms_of_disjoint hd]; simpa using hM0 A
    · rw [hamiltonianTerms_of_not_disjoint hd]; exact hM A η
  have h3 := abs_sub_abs_le_abs_sub (Θ.hamiltonian Λ η)
    (∑ A ∈ Δ₀.powerset, Θ.hamiltonianTerms Λ η A)
  rw [abs_sub_comm] at h3
  linarith

/-- **Georgii (2.36).** `α_{S∖Λ} H_Λ^Φ = ∑_{∅ ≠ A ⊆ Λ} Φ_A`, the interchange of integration and
summation being justified by the uniform convergence of `Φ`. -/
private lemma avgOff_hamiltonian_eq_sum [Countable S] [IsPotential Θ] [IsSummable Θ]
    {M : Finset S → ℝ} (hM : ∀ (A : Finset S) (η : S → E), |Θ A η| ≤ M A) (hM0 : ∀ A, 0 ≤ M A)
    (hΘn : IsNormalized α Θ) (hΘu : IsUniformlyConvergent Θ) (Λ : Finset S) (η : S → E) :
    avgOff α Λ (Θ.hamiltonian Λ) η = ∑ A ∈ Λ.powerset.erase ∅, Θ A η := by
  obtain ⟨K, hK⟩ := bdd_hamiltonian hM hM0 hΘu Λ
  have hHm : Measurable (Θ.hamiltonian Λ) := measurable_hamiltonian (Φ := Θ) Λ
  have key : ∀ ε : ℝ, 0 < ε →
      |avgOff α Λ (Θ.hamiltonian Λ) η - ∑ A ∈ Λ.powerset.erase ∅, Θ A η| ≤ ε := by
    intro ε hε
    obtain ⟨Δ₀, hΔ₀⟩ := hΘu Λ hε
    have hΛΔ : Λ ⊆ Δ₀ ∪ Λ := Finset.subset_union_right
    have hSb : ∀ x : S → E,
        |∑ A ∈ (Δ₀ ∪ Λ).powerset, Θ.hamiltonianTerms Λ x A|
          ≤ ∑ A ∈ (Δ₀ ∪ Λ).powerset, M A := by
      intro x
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun A _ ↦ ?_)
      by_cases hd : Disjoint A Λ
      · rw [hamiltonianTerms_of_disjoint hd]; simpa using hM0 A
      · rw [hamiltonianTerms_of_not_disjoint hd]; exact hM A x
    rw [← avgOff_sum_powerset_hamiltonianTerms α hM hM0 hΘn hΛΔ η]
    refine abs_integral_sub_le (integrable_comp_vacuumCfg_right hHm hK Λ η)
      (integrable_comp_vacuumCfg_right
        (measurable_sum_hamiltonianTerms (Φ := Θ) Λ (Δ₀ ∪ Λ).powerset) hSb Λ η) fun ζ ↦ ?_
    rw [abs_sub_comm]
    exact hΔ₀ (Δ₀ ∪ Λ) Finset.subset_union_left (vacuumCfg ζ Λ η)
  have hle : |avgOff α Λ (Θ.hamiltonian Λ) η - ∑ A ∈ Λ.powerset.erase ∅, Θ A η| ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε ↦ by simpa using key ε hε
  have := abs_nonpos_iff.1 hle
  linarith [sub_eq_zero.1 this]

/-- The partial sums `∑_{∅ ≠ A ⊆ Λ} Φ_A` do not depend on the configuration when the
Hamiltonians are `𝓣_Λ`-measurable. -/
private lemma sum_powerset_erase_const [Countable S] [IsPotential Θ] [IsSummable Θ]
    {M : Finset S → ℝ} (hM : ∀ (A : Finset S) (η : S → E), |Θ A η| ≤ M A) (hM0 : ∀ A, 0 ≤ M A)
    (hΘn : IsNormalized α Θ) (hΘu : IsUniformlyConvergent Θ)
    (hdep : ∀ Λ : Finset S, DependsOn (Θ.hamiltonian Λ) ((Λ : Set S)ᶜ))
    (Λ : Finset S) (x y : S → E) :
    ∑ A ∈ Λ.powerset.erase ∅, Θ A x = ∑ A ∈ Λ.powerset.erase ∅, Θ A y := by
  rw [← avgOff_hamiltonian_eq_sum α hM hM0 hΘn hΘu Λ x,
    ← avgOff_hamiltonian_eq_sum α hM hM0 hΘn hΘu Λ y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ ↦ ?_)
  refine hdep Λ fun i hi ↦ ?_
  rw [vacuumCfg_apply_of_notMem (by simpa using hi),
    vacuumCfg_apply_of_notMem (by simpa using hi)]

/-- **Georgii (2.35)(a).** An `α`-normalized uniformly convergent potential with bounded
interactions whose Hamiltonians are all `𝓣_Λ`-measurable vanishes on every nonempty support. -/
theorem eq_zero_of_isNormalized [Countable S] [IsPotential Θ] [IsSummable Θ]
    (hΘb : ∀ A : Finset S, ∃ M : ℝ, ∀ η, |Θ A η| ≤ M)
    (hΘn : IsNormalized α Θ) (hΘu : IsUniformlyConvergent Θ)
    (hdep : ∀ Λ : Finset S, DependsOn (Θ.hamiltonian Λ) ((Λ : Set S)ᶜ))
    {A : Finset S} (hA : A.Nonempty) (ω : S → E) : Θ A ω = 0 := by
  classical
  choose M₀ hM₀ using hΘb
  have hM : ∀ (B : Finset S) (η : S → E), |Θ B η| ≤ |M₀ B| :=
    fun B η ↦ (hM₀ B η).trans (le_abs_self _)
  have hM0 : ∀ B : Finset S, (0 : ℝ) ≤ |M₀ B| := fun B ↦ abs_nonneg _
  have hconst := sum_powerset_erase_const α hM hM0 hΘn hΘu hdep
  suffices H : ∀ n : ℕ, ∀ B : Finset S, B.card ≤ n → B.Nonempty → ∀ x, Θ B x = 0 from
    H A.card A le_rfl hA ω
  intro n
  induction n with
  | zero =>
    intro B hcard hB
    exact absurd (Finset.card_eq_zero.1 (Nat.le_zero.1 hcard))
      (Finset.nonempty_iff_ne_empty.1 hB)
  | succ n ih =>
    intro B hcard hB x
    have hsplit : ∀ y : S → E, ∑ C ∈ B.powerset.erase ∅, Θ C y = Θ B y := by
      intro y
      have hBmem : B ∈ B.powerset.erase ∅ :=
        Finset.mem_erase.2 ⟨Finset.nonempty_iff_ne_empty.1 hB, Finset.mem_powerset_self B⟩
      have h := Finset.sum_erase_add (B.powerset.erase ∅) (fun C ↦ Θ C y) hBmem
      have hzero : ∑ C ∈ (B.powerset.erase ∅).erase B, Θ C y = 0 := by
        refine Finset.sum_eq_zero fun C hC ↦ ?_
        have hCB : C ≠ B := Finset.ne_of_mem_erase hC
        have hC' := Finset.mem_of_mem_erase hC
        have hC0 : C ≠ ∅ := Finset.ne_of_mem_erase hC'
        have hCsub : C ⊆ B := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hC')
        have hcardC : C.card < B.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hCsub, hCB⟩)
        exact ih C (by omega) (Finset.nonempty_iff_ne_empty.2 hC0) y
      rw [hzero, zero_add] at h
      exact h.symm ▸ rfl
    have hΘconst : ∀ y z : S → E, Θ B y = Θ B z := by
      intro y z
      rw [← hsplit y, ← hsplit z]
      exact hconst B y z
    obtain ⟨i, hiB⟩ := hB
    have h0 : avgOn α {i} (Θ B) x = 0 :=
      congrFun (hΘn B {i} ⟨i, Finset.mem_singleton_self i⟩ (by simpa using hiB)) x
    rw [avgOn, integral_congr_ae (Filter.Eventually.of_forall fun ζ ↦ hΘconst _ x)] at h0
    simpa using h0

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E]
variable (α : Measure E) [IsProbabilityMeasure α]

/-! ### Closure properties of `α`-normalization and uniform convergence -/

lemma IsNormalized.sub {Φ Ψ : Potential S E} [IsPotential Φ] [IsPotential Ψ]
    (hΦb : ∀ A : Finset S, ∃ M : ℝ, ∀ η, |Φ A η| ≤ M)
    (hΨb : ∀ A : Finset S, ∃ M : ℝ, ∀ η, |Ψ A η| ≤ M)
    (hΦ : IsNormalized α Φ) (hΨ : IsNormalized α Ψ) : IsNormalized α (Φ - Ψ) := by
  intro A B hB hBA
  obtain ⟨MΦ, hMΦ⟩ := hΦb A
  obtain ⟨MΨ, hMΨ⟩ := hΨb A
  funext η
  have hrw : (Φ - Ψ) A = fun x ↦ Φ A x - Ψ A x := rfl
  rw [hrw, avgOn_sub (measurable_potential_apply (Θ := Φ) A) hMΦ
      (measurable_potential_apply (Θ := Ψ) A) hMΨ B η,
    congrFun (hΦ A B hB hBA) η, congrFun (hΨ A B hB hBA) η]
  simp

/-! ### Georgii (2.30), second assertion: uniqueness -/

variable (ν : Measure E) [SigmaFinite ν]

/-- **Georgii (2.30), step 5, for a general normalizing measure.** Two `λ`-admissible,
`α`-normalized, uniformly convergent potentials with bounded interactions which define the same
`λ`-modification coincide on every nonempty interaction support.

This is Georgii's deduction of uniqueness from Theorems (2.34) and (2.35)(a): the difference is
`α`-normalized and uniformly convergent, and its Hamiltonians are `𝓣_Λ`-measurable by
(2.34)(ii)⇒(i), hence it vanishes by (2.35)(a). -/
theorem eq_of_isNormalized_of_sigmaFinitePremodifierNorm_eq [Countable S]
    {Φ Ψ : Potential S E} [IsPotential Φ] [IsSummable Φ] [IsPotential Ψ] [IsSummable Ψ]
    (hΦb : ∀ A : Finset S, ∃ M : ℝ, ∀ η, |Φ A η| ≤ M)
    (hΨb : ∀ A : Finset S, ∃ M : ℝ, ∀ η, |Ψ A η| ≤ M)
    (hΦn : IsNormalized α Φ) (hΨn : IsNormalized α Ψ)
    (hΦu : IsUniformlyConvergent Φ) (hΨu : IsUniformlyConvergent Ψ)
    (hΦa : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1))
    (hΨa : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    (heq : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1)
      = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    {A : Finset S} (hA : A.Nonempty) (ω : S → E) : Φ A ω = Ψ A ω := by
  have : IsPotential (Φ - Ψ) := isPotential_sub
  have : IsSummable (Φ - Ψ) := isSummable_sub Φ Ψ
  have hsubb : ∀ B : Finset S, ∃ M : ℝ, ∀ η, |(Φ - Ψ) B η| ≤ M := by
    intro B
    obtain ⟨M1, h1⟩ := hΦb B
    obtain ⟨M2, h2⟩ := hΨb B
    refine ⟨M1 + M2, fun η ↦ ?_⟩
    calc |(Φ - Ψ) B η| = |Φ B η - Ψ B η| := rfl
      _ ≤ |Φ B η| + |Ψ B η| := abs_sub _ _
      _ ≤ M1 + M2 := add_le_add (h1 η) (h2 η)
  have h : (Φ - Ψ) A ω = 0 :=
    eq_zero_of_isNormalized α hsubb (IsNormalized.sub α hΦb hΨb hΦn hΨn)
        (IsUniformlyConvergent.sub hΦu hΨu)
      (fun Λ ↦ dependsOn_hamiltonian_sub_of_sigmaFinitePremodifierNorm_eq ν hΦa hΨa heq Λ) hA ω
  have h' : Φ A ω - Ψ A ω = 0 := h
  linarith

/-! ### Georgii, Theorem (2.30), second assertion -/

variable {ρ : Finset S → (S → E) → ℝ≥0∞}

/-- **Georgii, Theorem (2.30), second assertion.**

Let `λ = ν` be an a priori measure on `(E, 𝓔)` and let `ρ = (ρ_Λ)` be a positive quasilocal
pre-modification with `λ_Λ ρ_Λ = 1` for every finite volume `Λ` and with `log ρ_Λ` *bounded*.
Then for each `α ∈ 𝓟(E, 𝓔)` there is a *unique* uniformly convergent `α`-normalized
`λ`-admissible potential `Φ^α` with `ρ = ρ^{Φ^α}`.

The potential is the inclusion–exclusion (Möbius) expression of the proof of (2.30),

`Φ^α_A(ω) = - ∑_{C ⊆ A} (-1)^{|A ∖ C|} ∫ α^S(dζ) log ρ_A(ω_C ζ_{S∖C})`,

namely `Potential.normalizedPotential ρ α`; equivalently it is the `α^S`-average of the
interactions `Φ^ζ` at a reference configuration (`normalizedPotential_eq_integral`).  As in the
first assertion, uniqueness is asserted on Georgii's index set `𝒮 = {A : 0 < |A| < ∞}`.  The
comparison potentials are required to have bounded interactions, which is exactly the
integrability implicit in Georgii's Definition (2.28) of `α`-normalization and holds for `Φ^α`
itself (`bdd_normalizedPotential`). -/
theorem exists_unique_isNormalized_sigmaFinitePremodifierNorm_eq [Countable S]
    (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1) :
    ∃ Φ : Potential S E, IsPotential Φ ∧ IsSummable Φ ∧ IsNormalized α Φ ∧
      IsUniformlyConvergent Φ ∧ (∀ A : Finset S, ∃ M : ℝ, ∀ η, |Φ A η| ≤ M) ∧
      Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1) ∧
      Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1) = ρ ∧
      ∀ Ψ : Potential S E, IsPotential Ψ → IsSummable Ψ → IsNormalized α Ψ →
        IsUniformlyConvergent Ψ → (∀ A : Finset S, ∃ M : ℝ, ∀ η, |Ψ A η| ≤ M) →
        Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1) →
        Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor 1) = ρ →
        ∀ A : Finset S, A.Nonempty → Ψ A = Φ A := by
  classical
  have hΦP : IsPotential (normalizedPotential ρ α) :=
    isPotential_normalizedPotential α hρ.measurable
  have hΦS : IsSummable (normalizedPotential ρ α) :=
    isSummable_normalizedPotential α hρ hpos hfin hql hbdd
  have hΦU : IsUniformlyConvergent (normalizedPotential ρ α) :=
    isUniformlyConvergent_normalizedPotential α hρ hpos hfin hql hbdd
  have hΦB : ∀ A : Finset S, ∃ M : ℝ, ∀ η, |normalizedPotential ρ α A η| ≤ M :=
    bdd_normalizedPotential α hbdd
  have hΦN : IsNormalized α (normalizedPotential ρ α) :=
    isNormalized_normalizedPotential α hρ.measurable hbdd
  have hΦadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((normalizedPotential ρ α).boltzmannFactor 1) :=
    isSigmaFiniteLambdaAdmissible_normalizedPotential α ν hρ hpos hfin hql hbdd hnorm
  have hΦρ : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
      ((normalizedPotential ρ α).boltzmannFactor 1) = ρ :=
    sigmaFinitePremodifierNorm_normalizedPotential α ν hρ hpos hfin hql hbdd hnorm
  refine ⟨normalizedPotential ρ α, hΦP, hΦS, hΦN, hΦU, hΦB, hΦadm, hΦρ, ?_⟩
  intro Ψ hΨP hΨS hΨN hΨU hΨB hΨadm hΨρ A hA
  have := hΨP
  have := hΨS
  funext ω
  exact eq_of_isNormalized_of_sigmaFinitePremodifierNorm_eq α ν hΨB hΦB hΨN hΦN hΨU hΦU
    hΨadm hΦadm (hΨρ.trans hΦρ.symm) hA ω

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### Georgii, Corollary (2.32): a Markovian pre-modification has a nearest-neighbour potential

Let `S` be the vertex set of a simple graph `G` with closed neighbourhoods
`B(i) = {i} ∪ {j : G.Adj i j}`, and let `ρ` be a positive pre-modification which is *Markovian*
in the sense that `ρ_{i}` is `𝓕_{B(i)}`-measurable for every site `i`.  Then the interaction
`Φ_A` vanishes unless `A` is a complete subgraph of `G`, i.e. `Φ` is a nearest-neighbour
potential in the sense of Georgii (2.17).

The statement is proved at a fixed reference configuration; the gas potentials `Φ^a` and the
`α`-normalized potentials `Φ^α` are then covered by specialization and by integration. -/

/-- **Georgii, Corollary (2.32).** For a Markovian positive pre-modification the interaction at
a reference configuration is supported on the complete subgraphs of the graph. -/
theorem gasPotentialCfg_eq_zero_of_not_isClique (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) {G : SimpleGraph S}
    (hmark : ∀ i : S, DependsOn (ρ {i}) (insert i (G.neighborSet i)))
    (ζ : S → E) {A : Finset S} (hA : ¬ G.IsClique (A : Set S)) (η : S → E) :
    gasPotentialCfg ρ ζ A η = 0 := by
  rw [SimpleGraph.isClique_iff, Set.Pairwise] at hA
  push Not at hA
  obtain ⟨i, hiA, j, hjA, hij, hadj⟩ := hA
  have hiA' : i ∈ A := by exact_mod_cast hiA
  have hjA' : j ∈ A := by exact_mod_cast hjA
  rw [gasPotentialCfg, mobiusCfg, neg_eq_zero]
  refine sum_powerset_neg_one_pow_mul_eq_zero_of_sub_sub hiA' hjA' (Ne.symm hij) fun C hC ↦ ?_
  have hjC : j ∉ C := fun h ↦ Finset.notMem_erase j (A.erase i) (hC h)
  have hiC : i ∉ C := fun h ↦
    Finset.notMem_erase i A (Finset.mem_of_mem_erase (hC h))
  have hiA'' : ({i} : Finset S) ⊆ A := by simpa using hiA'
  have hiji : i ∉ insert j C := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hij, hiC⟩
  -- the two first differences in the site `i` are computed by the single-site interaction
  have hoff1 : ∀ s ∉ ({i} : Finset S),
      vacuumCfg ζ C η s = vacuumCfg ζ (insert i C) η s := by
    intro s hs
    have hsi : s ≠ i := by simpa using hs
    by_cases hsC : s ∈ C
    · rw [vacuumCfg_apply_of_mem hsC, vacuumCfg_apply_of_mem (Finset.mem_insert_of_mem hsC)]
    · rw [vacuumCfg_apply_of_notMem hsC,
        vacuumCfg_apply_of_notMem (by simp [Finset.mem_insert, hsi, hsC])]
  have hoff2 : ∀ s ∉ ({i} : Finset S),
      vacuumCfg ζ (insert j C) η s = vacuumCfg ζ (insert i (insert j C)) η s := by
    intro s hs
    have hsi : s ≠ i := by simpa using hs
    by_cases hsC : s ∈ insert j C
    · rw [vacuumCfg_apply_of_mem hsC, vacuumCfg_apply_of_mem (Finset.mem_insert_of_mem hsC)]
    · rw [vacuumCfg_apply_of_notMem hsC,
        vacuumCfg_apply_of_notMem (by simp [Finset.mem_insert, hsi, hsC])]
  have h1 := logDensity_sub_comm hρ hpos hfin hiA'' hoff1
  have h2 := logDensity_sub_comm hρ hpos hfin hiA'' hoff2
  -- the single-site interaction does not see the site `j`
  have hdep : DependsOn (logDensity ρ {i}) (insert i (G.neighborSet i)) :=
    DependsOn.comp (fun x : ℝ≥0∞ ↦ Real.log x.toReal) (hmark i)
  have hjnot : j ∉ insert i (G.neighborSet i) := by
    simp only [Set.mem_insert_iff, SimpleGraph.mem_neighborSet, not_or]
    exact ⟨Ne.symm hij, fun h ↦ hadj h⟩
  have h3 : logDensity ρ {i} (vacuumCfg ζ C η)
      = logDensity ρ {i} (vacuumCfg ζ (insert j C) η) := by
    refine hdep fun s hs ↦ ?_
    have hsj : s ≠ j := fun h ↦ hjnot (h ▸ hs)
    by_cases hsC : s ∈ C
    · rw [vacuumCfg_apply_of_mem hsC, vacuumCfg_apply_of_mem (Finset.mem_insert_of_mem hsC)]
    · rw [vacuumCfg_apply_of_notMem hsC,
        vacuumCfg_apply_of_notMem (by simp [Finset.mem_insert, hsj, hsC])]
  have h4 : logDensity ρ {i} (vacuumCfg ζ (insert i C) η)
      = logDensity ρ {i} (vacuumCfg ζ (insert i (insert j C)) η) := by
    refine hdep fun s hs ↦ ?_
    have hsj : s ≠ j := fun h ↦ hjnot (h ▸ hs)
    by_cases hsC : s ∈ insert i C
    · rw [vacuumCfg_apply_of_mem hsC, vacuumCfg_apply_of_mem ?_]
      rcases Finset.mem_insert.1 hsC with rfl | hsC'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hsC')
    · rw [vacuumCfg_apply_of_notMem hsC, vacuumCfg_apply_of_notMem ?_]
      simp only [Finset.mem_insert, not_or]
      simp only [Finset.mem_insert, not_or] at hsC
      exact ⟨hsC.1, hsj, hsC.2⟩
  linarith

/-- **Georgii, Corollary (2.32), for the gas potential with vacuum state `a`.** -/
theorem gasPotential_eq_zero_of_not_isClique (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) {G : SimpleGraph S}
    (hmark : ∀ i : S, DependsOn (ρ {i}) (insert i (G.neighborSet i)))
    (a : E) {A : Finset S} (hA : ¬ G.IsClique (A : Set S)) (η : S → E) :
    gasPotential ρ a A η = 0 :=
  gasPotentialCfg_eq_zero_of_not_isClique hρ hpos hfin hmark (fun _ ↦ a) hA η

/-- **Georgii, Corollary (2.32).** The `α`-normalized potential of a Markovian positive
pre-modification with bounded log-density is a nearest-neighbour potential: `Φ^α_A = 0` unless
`A` is a complete subgraph of the graph. -/
theorem normalizedPotential_eq_zero_of_not_isClique (α : Measure E) [IsProbabilityMeasure α]
    (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (hbdd : HasBddLogDensity ρ)
    {G : SimpleGraph S} (hmark : ∀ i : S, DependsOn (ρ {i}) (insert i (G.neighborSet i)))
    {A : Finset S} (hA : ¬ G.IsClique (A : Set S)) (η : S → E) :
    normalizedPotential ρ α A η = 0 := by
  rw [normalizedPotential_eq_integral α hρ.measurable hbdd A η,
    integral_congr_ae (Filter.Eventually.of_forall fun ζ ↦
      gasPotentialCfg_eq_zero_of_not_isClique hρ hpos hfin hmark ζ hA η)]
  simp

/-- **Georgii, Corollary (2.32).** The `α`-normalised potential representing a quasilocal Markov
premodifier is a *nearest-neighbour* potential in the sense of Georgii (2.17): `Φ_A = 0` unless
`A` is a complete subgraph of the Markov graph. -/
theorem isNearestNeighbour_normalizedPotential (α : Measure E) [IsProbabilityMeasure α]
    (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (hbdd : HasBddLogDensity ρ)
    {G : SimpleGraph S} (hmark : ∀ i : S, DependsOn (ρ {i}) (insert i (G.neighborSet i))) :
    IsNearestNeighbour G (normalizedPotential ρ α) := fun _A hA ↦
  funext fun η ↦ normalizedPotential_eq_zero_of_not_isClique α hρ hpos hfin hbdd hmark hA η

/-- **Georgii, Corollary (2.32)** for the gas potential `Φ^a`, at weaker hypotheses: no
boundedness of the log-densities is needed. -/
theorem isNearestNeighbour_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) {G : SimpleGraph S}
    (hmark : ∀ i : S, DependsOn (ρ {i}) (insert i (G.neighborSet i))) (a : E) :
    IsNearestNeighbour G (gasPotential ρ a) := fun _A hA ↦
  funext fun η ↦ gasPotential_eq_zero_of_not_isClique hρ hpos hfin hmark a hA η

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### Georgii, Corollary (2.31): a finite state space

For a finite (hence compact discrete) single-spin space every quasilocal observable is
continuous, so a *positive* quasilocal pre-modification has log-densities that are bounded, and
the second assertion of Theorem (2.30) applies for every `α ∈ 𝓟(E, 𝓔)`.  Georgii states (2.31)
for a positive quasilocal *specification* `γ` and the counting measure; the passage from `γ` to
its `λ`-modification `ρ` — Georgii's paragraph below (1.31) together with Proposition
(2.24)(c) — happens at the level of specifications and is not part of this file, so the
corollary is stated here for the modification `ρ` itself. -/

omit [DecidableEq S] [MeasurableSpace E] in
/-- **Georgii, Remark (2.21)(3).** Over a discrete single-spin space a quasilocal observable is
continuous for the product topology. -/
lemma continuous_of_isQuasilocalFun [TopologicalSpace E] [DiscreteTopology E]
    {f : (S → E) → ℝ} (hf : IsQuasilocalFun f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro η
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Δ, hΔ⟩ := hf (ε / 2) (by positivity)
  have hset : {ζ : S → E | ∀ i ∈ (Δ : Set S), ζ i = η i}
      = Set.pi (Δ : Set S) fun i ↦ ({η i} : Set E) := by
    ext ζ
    simp [Set.mem_pi]
  have hopen : IsOpen {ζ : S → E | ∀ i ∈ (Δ : Set S), ζ i = η i} := by
    rw [hset]
    exact isOpen_set_pi Δ.finite_toSet fun i _ ↦ isOpen_discrete _
  refine Filter.eventually_iff_exists_mem.2 ⟨_, hopen.mem_nhds (by simp), fun ζ hζ ↦ ?_⟩
  have h := hΔ ζ η fun i hi ↦ hζ i (by exact_mod_cast hi)
  rw [Real.dist_eq]
  linarith

omit [DecidableEq S] [MeasurableSpace E] in
/-- **Georgii, Corollary (2.31).** Over a finite single-spin space a positive quasilocal
pre-modification has bounded log-densities: `log ρ_Λ` is continuous on the compact space
`Ω = E^S`, hence bounded, and it is finite because `ρ_Λ` is positive and finite. -/
theorem hasBddLogDensity_of_finite [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) : HasBddLogDensity ρ := by
  intro Λ
  rcases isEmpty_or_nonempty (S → E) with hE | hE
  · exact ⟨0, fun η ↦ (hE.false η).elim⟩
  · have hcont : Continuous fun η : S → E ↦ (ρ Λ η).toReal :=
      continuous_of_isQuasilocalFun (hql Λ)
    obtain ⟨η₁, -, hmin⟩ :=
      isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := S → E)) hcont.continuousOn
    obtain ⟨η₂, -, hmax⟩ :=
      isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := S → E)) hcont.continuousOn
    refine ⟨max |Real.log ((ρ Λ η₁).toReal)| |Real.log ((ρ Λ η₂).toReal)|, fun η ↦ ?_⟩
    have h1 : (0 : ℝ) < (ρ Λ η₁).toReal := ENNReal.toReal_pos (hpos _ _) (hfin _ _)
    have h2 : (ρ Λ η₁).toReal ≤ (ρ Λ η).toReal := hmin (Set.mem_univ η)
    have h3 : (ρ Λ η).toReal ≤ (ρ Λ η₂).toReal := hmax (Set.mem_univ η)
    have hlog1 : Real.log ((ρ Λ η₁).toReal) ≤ logDensity ρ Λ η := Real.log_le_log h1 h2
    have hlog2 : logDensity ρ Λ η ≤ Real.log ((ρ Λ η₂).toReal) :=
      Real.log_le_log (lt_of_lt_of_le h1 h2) h3
    rw [abs_le]
    have hb1 := neg_abs_le (Real.log ((ρ Λ η₁).toReal))
    have hb2 := le_abs_self (Real.log ((ρ Λ η₂).toReal))
    have hm1 := le_max_left |Real.log ((ρ Λ η₁).toReal)| |Real.log ((ρ Λ η₂).toReal)|
    have hm2 := le_max_right |Real.log ((ρ Λ η₁).toReal)| |Real.log ((ρ Λ η₂).toReal)|
    constructor <;> linarith

/-! ### Quasilocality of the Hamiltonians of `Φ^α` -/

variable (α : Measure E) [IsProbabilityMeasure α]

lemma isQuasilocalFun_avgOn {f : (S → E) → ℝ} {M : ℝ} (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ M) (hf : IsQuasilocalFun f) (Λ : Finset S) :
    IsQuasilocalFun (avgOn α Λ f) := by
  intro ε hε
  obtain ⟨Δ, hΔ⟩ := hf ε hε
  refine ⟨Δ, fun x y h ↦ ?_⟩
  refine abs_integral_sub_le (integrable_comp_vacuumCfg_left hfm hfb Λ x)
    (integrable_comp_vacuumCfg_left hfm hfb Λ y) fun ζ ↦ hΔ _ _ fun i hi ↦ ?_
  by_cases hiΛ : i ∈ Λ
  · rw [vacuumCfg_apply_of_mem hiΛ, vacuumCfg_apply_of_mem hiΛ]
  · rw [vacuumCfg_apply_of_notMem hiΛ, vacuumCfg_apply_of_notMem hiΛ, h i hi]

/-- **Georgii, Corollary (2.31).** The Hamiltonians of `Φ^α` are quasilocal, being the
difference of the quasilocal observables `α_Λ u_Λ` and `u_Λ`. -/
theorem isQuasilocalFun_hamiltonian_normalizedPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal) (hbdd : HasBddLogDensity ρ)
    (Λ : Finset S) : IsQuasilocalFun ((normalizedPotential ρ α).hamiltonian Λ) := by
  obtain ⟨M, hM⟩ := hbdd Λ
  have hu : IsQuasilocalFun (logDensity ρ Λ) := isQuasilocalFun_logDensity hpos hfin (hql Λ) hM
  intro ε hε
  obtain ⟨Δ₁, h1⟩ := isQuasilocalFun_avgOn α (measurable_logDensity hρ.measurable Λ) hM hu Λ
    (ε / 2) (by positivity)
  obtain ⟨Δ₂, h2⟩ := hu (ε / 2) (by positivity)
  refine ⟨Δ₁ ∪ Δ₂, fun x y h ↦ ?_⟩
  rw [hamiltonian_normalizedPotential α hρ hpos hfin hql hbdd Λ x,
    hamiltonian_normalizedPotential α hρ hpos hfin hql hbdd Λ y]
  have e1 := h1 x y fun i hi ↦ h i (Finset.mem_union_left _ hi)
  have e2 := h2 x y fun i hi ↦ h i (Finset.mem_union_right _ hi)
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

/-! ### Georgii, Corollary (2.31) -/

variable (ν : Measure E) [SigmaFinite ν]

/-- **Georgii, Corollary (2.31).**  Let the single-spin space `E` be finite and let `ρ` be a
positive quasilocal pre-modification with `λ_Λ ρ_Λ = 1` for every finite volume `Λ`.  Then for
each `α ∈ 𝓟(E, 𝓔)` there is a unique `α`-normalized `λ`-admissible potential `Φ` with
`ρ = ρ^Φ`; it is uniformly convergent and all its Hamiltonians `H_Λ^Φ` are quasilocal.

Georgii's boundedness hypothesis of (2.30) is automatic here: `log ρ_Λ` is continuous on the
compact space `Ω = E^S`.  Uniqueness is asserted on Georgii's index set
`𝒮 = {A : 0 < |A| < ∞}`. -/
theorem exists_unique_isNormalized_of_finite [Countable S] [TopologicalSpace E]
    [DiscreteTopology E] [Finite E] (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤)
    (hql : ∀ Λ, IsQuasilocalFun fun η ↦ (ρ Λ η).toReal)
    (hnorm : ∀ Λ η, Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1) :
    ∃ Φ : Potential S E, IsPotential Φ ∧ IsSummable Φ ∧ IsNormalized α Φ ∧
      IsUniformlyConvergent Φ ∧ (∀ A : Finset S, ∃ M : ℝ, ∀ η, |Φ A η| ≤ M) ∧
      (∀ Λ : Finset S, IsQuasilocalFun (Φ.hamiltonian Λ)) ∧
      Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1) ∧
      Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1) = ρ ∧
      ∀ Ψ : Potential S E, IsPotential Ψ → IsSummable Ψ → IsNormalized α Ψ →
        IsUniformlyConvergent Ψ → (∀ A : Finset S, ∃ M : ℝ, ∀ η, |Ψ A η| ≤ M) →
        Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1) →
        Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor 1) = ρ →
        ∀ A : Finset S, A.Nonempty → Ψ A = Φ A := by
  have hbdd : HasBddLogDensity ρ := hasBddLogDensity_of_finite hpos hfin hql
  have hΦP : IsPotential (normalizedPotential ρ α) :=
    isPotential_normalizedPotential α hρ.measurable
  have hΦS : IsSummable (normalizedPotential ρ α) :=
    isSummable_normalizedPotential α hρ hpos hfin hql hbdd
  have hΦN : IsNormalized α (normalizedPotential ρ α) :=
    isNormalized_normalizedPotential α hρ.measurable hbdd
  have hΦU : IsUniformlyConvergent (normalizedPotential ρ α) :=
    isUniformlyConvergent_normalizedPotential α hρ hpos hfin hql hbdd
  have hΦB : ∀ A : Finset S, ∃ M : ℝ, ∀ η, |normalizedPotential ρ α A η| ≤ M :=
    bdd_normalizedPotential α hbdd
  have hΦadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((normalizedPotential ρ α).boltzmannFactor 1) :=
    isSigmaFiniteLambdaAdmissible_normalizedPotential α ν hρ hpos hfin hql hbdd hnorm
  have hΦρ : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
      ((normalizedPotential ρ α).boltzmannFactor 1) = ρ :=
    sigmaFinitePremodifierNorm_normalizedPotential α ν hρ hpos hfin hql hbdd hnorm
  refine ⟨normalizedPotential ρ α, hΦP, hΦS, hΦN, hΦU, hΦB,
    fun Λ ↦ isQuasilocalFun_hamiltonian_normalizedPotential α hρ hpos hfin hql hbdd Λ,
    hΦadm, hΦρ, ?_⟩
  intro Ψ hΨP hΨS hΨN hΨU hΨB hΨadm hΨρ A hA
  have := hΨP
  have := hΨS
  funext ω
  exact eq_of_isNormalized_of_sigmaFinitePremodifierNorm_eq α ν hΨB hΦB hΨN hΦN hΨU hΦU
    hΨadm hΦadm (hΨρ.trans hΦρ.symm) hA ω

end Potential
