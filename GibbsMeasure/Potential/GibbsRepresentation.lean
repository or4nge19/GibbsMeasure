/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Quasilocal
public import GibbsMeasure.Potential.Space

/-!
# Georgii, Theorem (2.30): the Gibbs representation theorem

Let `λ` be an a priori measure on the single-spin space `(E, 𝓔)` and let `ρ = (ρ_Λ)` be a positive
quasilocal pre-modification with `λ_Λ ρ_Λ = 1` for every finite volume `Λ`.  Then for each
`a ∈ E` there is a *unique* `λ`-admissible gas potential `Φ^a` with vacuum state `a` such that
`ρ = ρ^{Φ^a}`.  In particular every positive quasilocal `λ`-specification is Gibbsian.
-/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Potential

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E]

/-! ### The vacuum configurations `ω_C a_{S∖C}` -/

/-- The configuration which agrees with `η` on `C` and takes the *vacuum state* `a` off `C`.

Georgii writes this `ω_C a_{S∖C}`.  For the Dirac a priori measure `α = δ_a`, Georgii's kernel
`α_{S∖C}` of Remark (1.25) acts on functions by `α_{S∖C} f (η) = f (vacuum a C η)`. -/
def vacuum (a : E) (C : Finset S) (η : S → E) : S → E := fun i ↦ if i ∈ C then η i else a

omit [MeasurableSpace E] in
@[simp] lemma vacuum_apply_of_mem {a : E} {C : Finset S} {η : S → E} {i : S} (hi : i ∈ C) :
    vacuum a C η i = η i := by simp [vacuum, hi]

omit [MeasurableSpace E] in
@[simp] lemma vacuum_apply_of_notMem {a : E} {C : Finset S} {η : S → E} {i : S} (hi : i ∉ C) :
    vacuum a C η i = a := by simp [vacuum, hi]

omit [MeasurableSpace E] in
@[simp] lemma vacuum_empty (a : E) (η : S → E) : vacuum a ∅ η = fun _ ↦ a := by
  funext i; simp [vacuum]

omit [MeasurableSpace E] in
lemma vacuum_congr {a : E} {C : Finset S} {ζ η : S → E} (h : ∀ i ∈ C, ζ i = η i) :
    vacuum a C ζ = vacuum a C η := by
  funext i
  by_cases hi : i ∈ C
  · simp [vacuum, hi, h i hi]
  · simp [vacuum, hi]

omit [MeasurableSpace E] in
/-- Two vacuum configurations built from subsets of `A` agree off `A`. -/
lemma vacuum_eqOn_compl {a : E} {C D A : Finset S} (hC : C ⊆ A) (hD : D ⊆ A) (ζ η : S → E) :
    ∀ i ∉ A, vacuum a C ζ i = vacuum a D η i := by
  intro i hi
  rw [vacuum_apply_of_notMem fun h ↦ hi (hC h), vacuum_apply_of_notMem fun h ↦ hi (hD h)]

omit [MeasurableSpace E] in
/-- `vacuum a C` only reads the coordinates in `C`. -/
lemma dependsOn_vacuum (a : E) (C : Finset S) :
    DependsOn (fun η : S → E ↦ vacuum a C η) (C : Set S) := by
  intro x y h
  funext i
  show vacuum a C x i = vacuum a C y i
  by_cases hi : i ∈ C
  · rw [vacuum_apply_of_mem hi, vacuum_apply_of_mem hi, h i (by simpa using hi)]
  · rw [vacuum_apply_of_notMem hi, vacuum_apply_of_notMem hi]

lemma measurable_vacuum (a : E) (C : Finset S) :
    Measurable (fun η : S → E ↦ vacuum a C η) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i ∈ C
  · simpa [vacuum, hi] using measurable_pi_apply (X := fun _ : S ↦ E) i
  · simp [vacuum, hi]

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
`p_A f = ∑_{C ⊆ A} (-1)^{|A∖C|} α_{S∖C} f`, specialized to the Dirac measure `α = δ_a`. -/
def mobius (a : E) (A : Finset S) (f : (S → E) → ℝ) (η : S → E) : ℝ :=
  ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * f (vacuum a C η)

omit [MeasurableSpace E] in
@[simp] lemma mobius_empty (a : E) (f : (S → E) → ℝ) (η : S → E) :
    mobius a ∅ f η = f (fun _ ↦ a) := by simp [mobius]

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(i).** `p_A f` is `𝓕_A`-measurable. -/
lemma dependsOn_mobius (a : E) (A : Finset S) (f : (S → E) → ℝ) :
    DependsOn (mobius a A f) (A : Set S) := by
  intro x y h
  refine Finset.sum_congr rfl fun C hC ↦ ?_
  have hCA : C ⊆ A := Finset.mem_powerset.1 hC
  rw [vacuum_congr (a := a) (C := C) fun i hi ↦ h i (by exact_mod_cast hCA hi)]

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(iii).** `α_{\{i\}}(p_A f) = 0` for `i ∈ A`; for `α = δ_a` this says
that `p_A f` vanishes at every configuration carrying the vacuum state somewhere in `A`. -/
lemma mobius_eq_zero {a : E} {A : Finset S} (f : (S → E) → ℝ) {η : S → E} {i : S}
    (hiA : i ∈ A) (hη : η i = a) : mobius a A f η = 0 := by
  set B := A.erase i with hB
  have hiB : i ∉ B := Finset.notMem_erase i A
  have hAB : A = insert i B := (Finset.insert_erase hiA).symm
  have key : ∀ C ∈ B.powerset,
      (-1 : ℝ) ^ (A \ C).card * f (vacuum a C η)
        + (-1 : ℝ) ^ (A \ insert i C).card * f (vacuum a (insert i C) η) = 0 := by
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
    have h3 : vacuum a (insert i C) η = vacuum a C η := by
      funext x
      by_cases hx : x ∈ insert i C
      · rcases Finset.mem_insert.1 hx with rfl | hx'
        · rw [vacuum_apply_of_mem hx, vacuum_apply_of_notMem hiC, hη]
        · rw [vacuum_apply_of_mem hx, vacuum_apply_of_mem hx']
      · have hxC : x ∉ C := fun h ↦ hx (Finset.mem_insert_of_mem h)
        rw [vacuum_apply_of_notMem hx, vacuum_apply_of_notMem hxC]
    have hcard : (A \ C).card = (B \ C).card + 1 := by
      rw [h1, Finset.card_insert_of_notMem (by simp [Finset.mem_sdiff, hiB])]
    rw [h2, h3, hcard, pow_succ]
    ring
  rw [mobius, hAB, Finset.sum_powerset_insert hiB, ← hAB, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero key

omit [MeasurableSpace E] in
/-- **Georgii (2.30), step 1(ii).** The inclusion–exclusion principle:
`α_{S∖Λ} f = ∑_{A ⊆ Λ} p_A f`. -/
lemma sum_powerset_mobius (a : E) (Λ : Finset S) (f : (S → E) → ℝ) (η : S → E) :
    ∑ A ∈ Λ.powerset, mobius a A f η = f (vacuum a Λ η) := by
  have hswap : ∑ A ∈ Λ.powerset, ∑ C ∈ A.powerset,
        (-1 : ℝ) ^ (A \ C).card * f (vacuum a C η)
      = ∑ C ∈ Λ.powerset, ∑ A ∈ Λ.powerset.filter (fun A ↦ C ⊆ A),
        (-1 : ℝ) ^ (A \ C).card * f (vacuum a C η) := by
    refine Finset.sum_comm' ?_
    intro A C
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · rintro ⟨hA, hC⟩; exact ⟨⟨hA, hC⟩, hC.trans hA⟩
    · rintro ⟨⟨hA, hC⟩, -⟩; exact ⟨hA, hC⟩
  rw [show (∑ A ∈ Λ.powerset, mobius a A f η)
      = ∑ A ∈ Λ.powerset, ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card * f (vacuum a C η) from rfl,
    hswap]
  refine (Finset.sum_eq_single_of_mem Λ (Finset.mem_powerset_self Λ) ?_).trans ?_
  · intro C hC hCΛ
    rw [← Finset.sum_mul, sum_filter_superset_neg_one_pow_card_sdiff (Finset.mem_powerset.1 hC)]
    simp [hCΛ]
  · rw [← Finset.sum_mul, sum_filter_superset_neg_one_pow_card_sdiff (le_refl Λ)]
    simp

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

omit [MeasurableSpace E] in
/-- A quasilocal function is continuous along any net of configurations which eventually agree
with the limit configuration on any prescribed finite volume. -/
lemma tendsto_of_quasilocal {f : (S → E) → ℝ} (hf : IsQuasilocalFun f)
    (g : Finset S → (S → E)) (η : S → E)
    (hg : ∀ Δ₀ : Finset S, ∀ Δ : Finset S, Δ₀ ⊆ Δ → ∀ i ∈ Δ₀, g Δ i = η i) :
    Tendsto (fun Δ : Finset S ↦ f (g Δ)) atTop (nhds (f η)) := by
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
    gasPotential ρ a A η = -mobius a A (logDensity ρ Δ) η := by
  have key : ∀ C ∈ A.powerset,
      logDensity ρ A (vacuum a C η) - logDensity ρ Δ (vacuum a C η)
        = logDensity ρ A (fun _ ↦ a) - logDensity ρ Δ (fun _ ↦ a) := by
    intro C hC
    have hCA : C ⊆ A := Finset.mem_powerset.1 hC
    have hoff : ∀ s ∉ A, vacuum a C η s = (fun _ : S ↦ a) s := fun s hs ↦
      vacuum_apply_of_notMem fun h ↦ hs (hCA h)
    have h := logDensity_sub_comm hρ hpos hfin hAΔ hoff
    linarith
  have hzero : ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card = 0 := by
    rw [sum_powerset_neg_one_pow_card_sdiff]
    simp [Finset.nonempty_iff_ne_empty.1 hA]
  have hdiff : mobius a A (logDensity ρ A) η - mobius a A (logDensity ρ Δ) η
      = (logDensity ρ A (fun _ ↦ a) - logDensity ρ Δ (fun _ ↦ a))
        * ∑ C ∈ A.powerset, (-1 : ℝ) ^ (A \ C).card := by
    rw [Finset.mul_sum, mobius, mobius, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun C hC ↦ ?_
    rw [← mul_sub, key C hC]
    ring
  rw [hzero, mul_zero] at hdiff
  show -mobius a A (logDensity ρ A) η = -mobius a A (logDensity ρ Δ) η
  linarith

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
        - logDensity ρ Δ (vacuum a Δ' η) := by
  have hmem : (∅ : Finset S) ∈ Δ'.powerset := Finset.empty_mem_powerset _
  have h1 : ∑ A ∈ Δ'.powerset.erase ∅, gasPotential ρ a A η
      = ∑ A ∈ Δ'.powerset.erase ∅, -mobius a A (logDensity ρ Δ) η := by
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    have hA0 : A ≠ ∅ := Finset.ne_of_mem_erase hA
    have hAΔ' : A ⊆ Δ' := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA)
    exact gasPotential_eq_neg_mobius hρ hpos hfin a (Finset.nonempty_iff_ne_empty.2 hA0)
      (hAΔ'.trans hΔ') η
  have h2 : ∑ A ∈ Δ'.powerset, (-mobius a A (logDensity ρ Δ) η)
      = -logDensity ρ Δ (vacuum a Δ' η) := by
    rw [Finset.sum_neg_distrib, sum_powerset_mobius]
  have e1 := Finset.sum_erase_add Δ'.powerset (fun A ↦ gasPotential ρ a A η) hmem
  have e2 := Finset.sum_erase_add Δ'.powerset (fun A ↦ -mobius a A (logDensity ρ Δ) η) hmem
  rw [h2] at e2
  rw [← e1, h1]
  have hm0 : mobius a ∅ (logDensity ρ Δ) η = logDensity ρ Δ (fun _ ↦ a) := mobius_empty _ _ _
  rw [hm0] at e2
  linarith

/-- **Georgii (2.30), step 4.** For `Λ ⊆ Δ` the partial Hamiltonian of `Φ^a` is
`H^Φ_{Λ,Δ} = α_{S∖Δ}(α_Λ u_Λ - u_Λ)`, explicitly
`H^Φ_{Λ,Δ}(ω) = log ρ_Λ(ω_{Δ∖Λ} a_{S∖(Δ∖Λ)}) - log ρ_Λ(ω_Δ a_{S∖Δ})`. -/
theorem sum_powerset_hamiltonianTerms_gasPotential (hρ : Specification.IsPremodifier ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (hfin : ∀ Λ η, ρ Λ η ≠ ⊤) (a : E)
    {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) (η : S → E) :
    ∑ A ∈ Δ.powerset, (gasPotential ρ a).hamiltonianTerms Λ η A
      = logDensity ρ Λ (vacuum a (Δ \ Λ) η) - logDensity ρ Λ (vacuum a Δ η) := by
  classical
  set Φ : Potential S E := gasPotential ρ a with hΦ
  have hsub : (Δ \ Λ).powerset ⊆ Δ.powerset :=
    Finset.powerset_mono.2 (Finset.sdiff_subset)
  -- the terms supported in `Δ \ Λ` do not contribute
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
  have hfull := sum_powerset_gasPotential hρ hpos hfin a (le_refl Δ) η
  have hpart := sum_powerset_gasPotential hρ hpos hfin a
    (Finset.sdiff_subset (s := Δ) (t := Λ)) η
  -- pass from `u_Δ` to `u_Λ`
  have hoff : ∀ s ∉ Λ, vacuum a (Δ \ Λ) η s = vacuum a Δ η s := by
    intro s hs
    by_cases hsΔ : s ∈ Δ
    · rw [vacuum_apply_of_mem (Finset.mem_sdiff.2 ⟨hsΔ, hs⟩), vacuum_apply_of_mem hsΔ]
    · rw [vacuum_apply_of_notMem (fun h ↦ hsΔ (Finset.mem_sdiff.1 h).1),
        vacuum_apply_of_notMem hsΔ]
  have hconv := logDensity_sub_comm hρ hpos hfin hΛΔ hoff
  rw [e1, e2, e3, hfull, hpart]
  linarith

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

/-- **Georgii (2.35)(a), for `α = δ_a`.** A gas potential with vacuum state `a` all of whose
Hamiltonians are `𝓣_Λ`-measurable vanishes on every nonempty support. -/
theorem eq_zero_of_isGasPotential {Θ : Potential S E} [IsPotential Θ] [IsSummable Θ] {a : E}
    (hΘ : IsGasPotential a Θ)
    (hdep : ∀ Λ : Finset S, DependsOn (Θ.hamiltonian Λ) ((Λ : Set S)ᶜ))
    {A : Finset S} (hA : A.Nonempty) (ω : S → E) : Θ A ω = 0 := by
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

lemma hamiltonianTerms_sub' (Φ Ψ : Potential S E) (Λ : Finset S) (η : S → E) (A : Finset S) :
    (Φ - Ψ).hamiltonianTerms Λ η A
      = Φ.hamiltonianTerms Λ η A - Ψ.hamiltonianTerms Λ η A := by
  by_cases h : Disjoint A Λ
  · rw [hamiltonianTerms_of_disjoint h, hamiltonianTerms_of_disjoint h,
      hamiltonianTerms_of_disjoint h, sub_zero]
  · rw [hamiltonianTerms_of_not_disjoint h, hamiltonianTerms_of_not_disjoint h,
      hamiltonianTerms_of_not_disjoint h, sub_apply]

lemma hasSum_hamiltonianTerms_sub [IsSummable Φ] [IsSummable Ψ] (Λ : Finset S) (η : S → E) :
    HasSum ((Φ - Ψ).hamiltonianTerms Λ η) (Φ.hamiltonian Λ η - Ψ.hamiltonian Λ η)
      (SummationFilter.volume S) := by
  have h := (hasSum_hamiltonian (Φ := Φ) Λ η).sub (hasSum_hamiltonian (Φ := Ψ) Λ η)
  refine h.congr_fun fun A ↦ ?_
  exact hamiltonianTerms_sub' Φ Ψ Λ η A

lemma isSummable_sub [IsSummable Φ] [IsSummable Ψ] : IsSummable (Φ - Ψ) :=
  ⟨fun Λ η ↦ ⟨_, hasSum_hamiltonianTerms_sub Λ η⟩⟩

lemma hamiltonian_sub' [IsSummable Φ] [IsSummable Ψ] (Λ : Finset S) (η : S → E) :
    (Φ - Ψ).hamiltonian Λ η = Φ.hamiltonian Λ η - Ψ.hamiltonian Λ η :=
  (hasSum_hamiltonianTerms_sub Λ η).tsum_eq

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
  rw [hamiltonian_sub' Λ x, hamiltonian_sub' Λ y,
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
  have : IsSummable (Φ - Ψ) := isSummable_sub
  have hgas : IsGasPotential a (Φ - Ψ) := hΦgas.sub hΨgas
  have h : (Φ - Ψ) A ω = 0 :=
    eq_zero_of_isGasPotential (Θ := (Φ - Ψ)) hgas
      (fun Λ ↦ dependsOn_hamiltonian_sub_of_sigmaFinitePremodifierNorm_eq ν hΦ hΨ heq Λ) hA ω
  have h' : Φ A ω - Ψ A ω = 0 := h
  linarith

/-! ### Georgii, Theorem (2.30) -/

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
