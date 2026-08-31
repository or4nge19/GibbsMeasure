/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Equivalence
public import GibbsMeasure.Potential.PerSiteExistence
public import GibbsMeasure.Specification.Dobrushin
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.Rescaling
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Georgii, Section 8.3: uniqueness in one dimension

## Main results

* `MeasureTheory.GibbsMeasure.subsingleton_G_of_isUniformlyDominated`: Georgii Prop. (8.38). If
  there is `c > 0` such that every cylinder event `A` admits a volume `Λ` with
  `γ_Λ(A | ζ) ≥ c γ_Λ(A | η)` for all boundary conditions `ζ, η`, then `|𝒢(γ)| ≤ 1`. The proof
  shows that conditioning a Gibbs measure on a tail event of positive mass produces a Gibbs
  measure `ν ≥ c μ` (Georgii Thm. (7.7)(b), `isGibbsMeasure_cond_of_tail`), so every Gibbs measure
  is tail trivial and hence unique in its absolute-continuity class
  (`eq_of_absolutelyContinuous_of_isTailTrivial`).
* `MeasureTheory.GibbsMeasure.subsingleton_G_lambdaSpecification_of_iSup_oscSpan_ne_top`: Georgii
  Thm. (8.39), first half, at Georgii's own hypotheses: `Φ` is a potential in the sense of
  Definition (2.2) over an arbitrary σ-finite non-zero a priori measure `λ`, `λ`-admissible, and
  (8.40) holds: `s := sup_i ∑_{A : min A ≤ i < max A} δ(Φ_A) < ∞` (`oscSpan`). Then `|𝒢(Φ)| ≤ 1`.
* `MeasureTheory.GibbsMeasure.existsUnique_mem_GP_lambdaSpecification_of_iSup_oscSpan_ne_top`:
  Georgii Thm. (8.39) in full, at his own hypotheses — a potential in the sense of (2.2),
  `λ`-admissible over a probability a priori measure on a standard Borel state space, with (8.40),
  has exactly one Gibbs measure. Existence is Georgii's reduction: (8.40) makes the recentred
  many-body part absolutely summable (`isAbsolutelySummable_centre_manyBody`) and the self-energies
  go into the a priori measure (`Potential.GP_lambdaSpecification_nonempty`).
* `MeasureTheory.GibbsMeasure.existsUnique_mem_GP_of_iSup_oscSpan_ne_top`: the same for an
  absolutely summable potential, where existence is (4.23)(a) directly.
* `MeasureTheory.GibbsMeasure.iSup_oscSpan_ne_top_of_oscSpanDiam_ne_top`: Georgii Comment
  (8.41)(1). For a potential on `ℤ` with shift-invariant oscillations, Georgii's simpler condition
  (8.42), `∑_{A : min A = 0} diam A · δ(Φ_A) < ∞` (`oscSpanDiam`), implies (8.40).
* `MeasureTheory.GibbsMeasure.oscSpanDiam_eq_tsum_pair` and
  `MeasureTheory.GibbsMeasure.subsingleton_G_of_pair_rpow_le`: Georgii Comment (8.41)(2). For a
  pair potential, (8.42) reads `∑_{n ≥ 1} n · δ(Φ_{{0,n}})`, so `δ(Φ_{{0,n}}) ≤ c n^{-p}` with
  `p > 2` gives uniqueness — far past nearest-neighbour interactions.

The one-dimensional input is `MeasureTheory.GibbsMeasure.HasBoundedBoundary`: `S` is exhausted by
intervals with a bounded number `m` of boundary sites, so the Hamiltonian `H_Λ` varies by at most
`m · s` when the boundary condition changes (`abs_hamiltonian_sub_le_of_hasBoundedBoundary`); this
gives the ratio bound `e^{-2 m |β| s}` required by (8.38). Georgii's two cases are
`hasBoundedBoundary_int` (`S = ℤ`, `Λ = ]-n, n]`, `m = 2`) and `hasBoundedBoundary_nat`
(`S = ℕ`, `Λ = [0, n]`, `m = 1`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal symmDiff Topology

namespace MeasureTheory
namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

local notation3 "Ω" => (S → E)

/-! ### Georgii (8.38) -/

variable {γ : Specification S E} {c : ℝ≥0∞}

/-- Georgii's hypothesis in Proposition (8.38): there is `c > 0` such that every cylinder event
`A` admits a volume `Λ` with `γ_Λ(A | ζ) ≥ c γ_Λ(A | η)` for all boundary conditions `ζ, η`. -/
def IsUniformlyDominated (γ : Specification S E) (c : ℝ≥0∞) : Prop :=
  ∀ A ∈ localEvents S E, ∃ Λ : Finset S, ∀ ζ η : S → E, c * γ Λ η A ≤ γ Λ ζ A

variable {μ ν : Measure (S → E)}

/-- Under the hypothesis of Georgii (8.38), any two Gibbs measures satisfy `ν ≥ c μ` on cylinder
events. -/
lemma mul_measure_le_of_isLocalEvent (hγ : IsUniformlyDominated γ c)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : _root_.Specification.IsGibbsMeasure γ μ) (hν : _root_.Specification.IsGibbsMeasure γ ν)
    {A : Set Ω} (hA : A ∈ localEvents S E) : c * μ A ≤ ν A := by
  obtain ⟨Λ, hΛ⟩ := hγ A hA
  have hAm : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  have hκ : Measurable (γ Λ) :=
    (ProbabilityTheory.Kernel.measurable (γ Λ)).mono cylinderEvents_le_pi le_rfl
  have hbindμ : μ.bind (γ Λ) = μ :=
    (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)).1 hμ Λ
  have hbindν : ν.bind (γ Λ) = ν :=
    (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)).1 hν Λ
  have hμA : μ A = ∫⁻ η, γ Λ η A ∂μ := by
    conv_lhs => rw [← hbindμ]
    exact Measure.bind_apply hAm hκ.aemeasurable
  have hνA : ν A = ∫⁻ ζ, γ Λ ζ A ∂ν := by
    conv_lhs => rw [← hbindν]
    exact Measure.bind_apply hAm hκ.aemeasurable
  have key : ∀ η : Ω, c * γ Λ η A ≤ ν A := by
    intro η
    calc c * γ Λ η A = ∫⁻ _ : Ω, c * γ Λ η A ∂ν := by simp
      _ ≤ ∫⁻ ζ, γ Λ ζ A ∂ν := lintegral_mono fun ζ ↦ hΛ ζ η
      _ = ν A := hνA.symm
  calc c * μ A = c * ∫⁻ η, γ Λ η A ∂μ := by rw [hμA]
    _ ≤ ∫⁻ η, c * γ Λ η A ∂μ := lintegral_const_mul_le _ _
    _ ≤ ∫⁻ _ : Ω, ν A ∂μ := lintegral_mono key
    _ = ν A := by simp

/-- Under the hypothesis of Georgii (8.38), any two Gibbs measures satisfy `ν ≥ c μ` on the whole
configuration σ-algebra. This is the monotone class step in Georgii's proof. -/
lemma smul_le_of_isUniformlyDominated (hc : c ≠ ⊤) (hγ : IsUniformlyDominated γ c)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : _root_.Specification.IsGibbsMeasure γ μ) (hν : _root_.Specification.IsGibbsMeasure γ ν) :
    c • μ ≤ ν := by
  refine Measure.le_iff.2 fun A hA ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  set ρ : Measure Ω := μ + ν with hρ
  have hρfin : IsFiniteMeasure ρ := by rw [hρ]; infer_instance
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / (1 + c) with hδdef
  have hone_add : (1 + c) ≠ ⊤ := by simp [hc]
  have hδ : 0 < δ := by
    rw [hδdef, ENNReal.div_pos_iff]
    exact ⟨by simpa using hε.ne', hone_add⟩
  obtain ⟨t, htC, ht⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := ρ) isSetRing_measurableCylinders
      ⟨{Set.univ}, Set.countable_singleton _,
        Set.singleton_subset_iff.2 (univ_mem_measurableCylinders (fun _ : S ↦ E)), by simp⟩
      generateFrom_measurableCylinders.symm hA hδ
  have hμsymm : μ (t ∆ A) ≤ δ := le_of_lt (lt_of_le_of_lt (by
    simp only [hρ] at ht ⊢
    exact le_trans (le_add_right le_rfl) (le_of_eq (Measure.add_apply μ ν _).symm)) ht)
  have hνsymm : ν (t ∆ A) ≤ δ := le_of_lt (lt_of_le_of_lt (by
    simp only [hρ] at ht ⊢
    exact le_trans (le_add_left le_rfl) (le_of_eq (Measure.add_apply μ ν _).symm)) ht)
  have h1 : c * μ t ≤ ν t :=
    mul_measure_le_of_isLocalEvent hγ hμ hν htC
  have hAsub : A ⊆ t ∪ (t ∆ A) := by
    intro x hx
    by_cases hxt : x ∈ t
    · exact Or.inl hxt
    · exact Or.inr (Or.inr ⟨hx, hxt⟩)
  have htsub : t ⊆ A ∪ (t ∆ A) := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr (Or.inl ⟨hx, hxA⟩)
  have hμle : μ A ≤ μ t + μ (t ∆ A) :=
    le_trans (measure_mono hAsub) (measure_union_le _ _)
  have hνle : ν t ≤ ν A + ν (t ∆ A) :=
    le_trans (measure_mono htsub) (measure_union_le _ _)
  calc c * μ A ≤ c * (μ t + μ (t ∆ A)) := by gcongr
    _ = c * μ t + c * μ (t ∆ A) := by rw [mul_add]
    _ ≤ ν t + c * δ := by gcongr
    _ ≤ (ν A + ν (t ∆ A)) + c * δ := by gcongr
    _ ≤ ν A + δ + c * δ := by gcongr
    _ = ν A + (1 + c) * δ := by rw [add_mul, one_mul, add_assoc]
    _ = ν A + ε := by
        rw [hδdef, ENNReal.mul_div_cancel' (by simp) (by simp [hone_add])]

/-- Under the hypothesis of Georgii (8.38), every Gibbs measure is tail trivial. -/
lemma isTailTrivial_of_isUniformlyDominated [Countable S] (hc0 : c ≠ 0) (hc : c ≠ ⊤)
    (hγ : IsUniformlyDominated γ c) (μ : ProbabilityMeasure Ω)
    (hμ : _root_.Specification.IsGibbsMeasure γ (μ : Measure Ω)) :
    IsTailTrivial (S := S) (E := E) μ := by
  intro B hB
  set m : Measure Ω := (μ : Measure Ω) with hm
  by_cases hB0 : m B = 0
  · exact Or.inl hB0
  refine Or.inr ?_
  have hBmeas : MeasurableSet B := measurableSet_of_measurableSet_tail (S := S) (E := E) hB
  have hcond : _root_.Specification.IsGibbsMeasure γ (ProbabilityTheory.cond m B) :=
    isGibbsMeasure_cond_of_tail (γ := γ) m hμ hB hB0
  have : IsProbabilityMeasure (ProbabilityTheory.cond m B) :=
    ProbabilityTheory.cond_isProbabilityMeasure hB0
  have hle : c • m ≤ ProbabilityTheory.cond m B :=
    smul_le_of_isUniformlyDominated hc hγ hμ hcond
  have hzero : (ProbabilityTheory.cond m B) Bᶜ = 0 := by
    rw [ProbabilityTheory.cond_apply hBmeas]
    simp
  have : c * m Bᶜ ≤ 0 := by
    have := hle Bᶜ
    rwa [Measure.smul_apply, smul_eq_mul, hzero] at this
  have hcompl : m Bᶜ = 0 := by
    rcases mul_eq_zero.1 (le_antisymm this bot_le) with h | h
    · exact absurd h hc0
    · exact h
  exact (prob_compl_eq_zero_iff (μ := m) hBmeas).1 hcompl

/-- **Georgii, Proposition (8.38).** If there is `c > 0` such that every cylinder event `A` admits
a volume `Λ` with `γ_Λ(A | ζ) ≥ c γ_Λ(A | η)` for all `ζ, η`, then `γ` has at most one Gibbs
measure. -/
theorem subsingleton_G_of_isUniformlyDominated [Countable S] (hc0 : c ≠ 0)
    (hγ : IsUniformlyDominated γ c) : (G (γ := γ)).Subsingleton := by
  rcases isEmpty_or_nonempty (S → E) with hΩ | ⟨⟨η₀⟩⟩
  · rintro μ ⟨hμp, -⟩ -- no probability measure lives on an empty configuration space
    have h10 : (1 : ℝ≥0∞) = 0 := by
      rw [← hμp.measure_univ, Set.univ_eq_empty_iff.2 hΩ, measure_empty]
    simp at h10
  -- Testing the hypothesis on `A = Ω` gives `c ≤ 1`, in particular `c ≠ ∞`.
  have hc : c ≠ ⊤ := by
    obtain ⟨Λ, hΛ⟩ := hγ Set.univ (univ_mem_measurableCylinders (fun _ : S ↦ E))
    have h := hΛ η₀ η₀
    simp only [measure_univ, mul_one] at h
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h
  rintro μ ⟨hμp, hμg⟩ ν ⟨hνp, hνg⟩
  have : IsProbabilityMeasure μ := hμp
  have : IsProbabilityMeasure ν := hνp
  have hμtail : IsTailTrivial (S := S) (E := E) (⟨μ, hμp⟩ : ProbabilityMeasure Ω) :=
    isTailTrivial_of_isUniformlyDominated hc0 hc hγ _ hμg
  have habs : ν ≪ μ := by
    intro s hs
    have hle : c • ν ≤ μ := smul_le_of_isUniformlyDominated hc hγ hνg hμg
    have := hle s
    rw [Measure.smul_apply, smul_eq_mul, hs] at this
    rcases mul_eq_zero.1 (le_antisymm this bot_le) with h | h
    · exact absurd h hc0
    · exact h
  exact (eq_of_absolutelyContinuous_of_isTailTrivial (γ := γ) hμg hνg hμtail habs).symm

/-! ### Oscillation of the Hamiltonian under a change of boundary condition -/

open Potential in
/-- Only the interaction terms that meet `Λ` **and** leave `Λ` contribute to the difference of
`H_Λ` between two configurations agreeing on `Λ`; each contributes at most its oscillation
`δ(Φ_A)`.

The Hamiltonian is only assumed summable in Georgii's sense (Definition (2.2)(ii)): the bound holds
for every partial sum over a finite volume `Δ`, hence for the limit along `SummationFilter.volume`.
-/
lemma enorm_hamiltonian_sub_le_tsum_osc {Φ : Potential S E} [Potential.IsPotential Φ]
    [Potential.IsSummable Φ] (Λ : Finset S) {x y : S → E}
    (hxy : ∀ i ∈ Λ, x i = y i) :
    ‖Φ.hamiltonian Λ x - Φ.hamiltonian Λ y‖ₑ ≤
      ∑' A : Finset S, {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ}.indicator
        (fun A ↦ Dobrushin.osc (Φ A)) A := by
  classical
  set b : ℝ≥0∞ := ∑' A : Finset S, {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ}.indicator
    (fun A ↦ Dobrushin.osc (Φ A)) A with hbdef
  have hterm : ∀ A : Finset S,
      ‖Φ.hamiltonianTerms Λ x A - Φ.hamiltonianTerms Λ y A‖ₑ ≤
        {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ}.indicator
          (fun A ↦ Dobrushin.osc (Φ A)) A := by
    intro A
    by_cases hd : Disjoint A Λ
    · rw [Potential.hamiltonianTerms_of_disjoint hd, Potential.hamiltonianTerms_of_disjoint hd]
      simp
    · rw [Potential.hamiltonianTerms_of_not_disjoint hd,
        Potential.hamiltonianTerms_of_not_disjoint hd]
      by_cases hsub : A ⊆ Λ
      · have hΦ : Φ A x = Φ A y :=
          Potential.IsPotential.eq_of_eqOn fun k hk ↦ hxy k (hsub hk)
        rw [hΦ]
        simp
      · rw [Set.indicator_of_mem
          (show A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ} from ⟨hd, hsub⟩),
          Real.enorm_eq_ofReal_abs]
        exact Dobrushin.le_osc _ _ _
  have hpart : ∀ Δ : Finset S,
      ‖(∑ A ∈ Δ.powerset, Φ.hamiltonianTerms Λ x A)
          - ∑ A ∈ Δ.powerset, Φ.hamiltonianTerms Λ y A‖ₑ ≤ b := by
    intro Δ
    rw [← Finset.sum_sub_distrib]
    exact le_trans (enorm_sum_le _ _)
      (le_trans (Finset.sum_le_sum fun A _ ↦ hterm A) (ENNReal.sum_le_tsum _))
  have htend : ∀ z : S → E,
      Filter.Tendsto (fun Δ : Finset S ↦ ∑ A ∈ Δ.powerset, Φ.hamiltonianTerms Λ z A)
        Filter.atTop (nhds (Φ.hamiltonian Λ z)) := by
    intro z
    have h : Filter.Tendsto (fun t : Finset (Finset S) ↦ ∑ A ∈ t, Φ.hamiltonianTerms Λ z A)
        (Filter.map Finset.powerset Filter.atTop) (nhds (Φ.hamiltonian Λ z)) :=
      Potential.hasSum_hamiltonian (Φ := Φ) Λ z
    exact h.comp Filter.tendsto_map
  have hlim := (ContinuousENorm.continuous_enorm (E := ℝ)).tendsto _
    |>.comp ((htend x).sub (htend y))
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hpart)

/-- A bound on the oscillation of the Hamiltonian bounds the ratio of Boltzmann factors. -/
lemma boltzmannFactor_le_of_abs_hamiltonian_sub_le {Φ : Potential S E} (β : ℝ) (Λ : Finset S)
    {x y : S → E} {t : ℝ} (ht : |Φ.hamiltonian Λ x - Φ.hamiltonian Λ y| ≤ t) :
    Φ.boltzmannFactor β Λ x ≤
      ENNReal.ofReal (Real.exp (|β| * t)) * Φ.boltzmannFactor β Λ y := by
  rw [Potential.boltzmannFactor, Potential.boltzmannFactor,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hd : -β * (Φ.hamiltonian Λ x - Φ.hamiltonian Λ y) ≤ |β| * t := by
    calc -β * (Φ.hamiltonian Λ x - Φ.hamiltonian Λ y)
        ≤ |-β * (Φ.hamiltonian Λ x - Φ.hamiltonian Λ y)| := le_abs_self _
      _ = |β| * |Φ.hamiltonian Λ x - Φ.hamiltonian Λ y| := by rw [abs_mul, abs_neg]
      _ ≤ |β| * t := mul_le_mul_of_nonneg_left ht (abs_nonneg β)
  linarith

/-! ### From a uniform ratio bound on the density to the hypothesis of (8.38) -/

section Gibbsian

variable {lam : Measure E} [SigmaFinite lam] {ρ : Finset S → (S → E) → ℝ≥0∞}

/-- Georgii's reference kernel `λ_Λ(· | ξ)` is the image of the product measure `λ^Λ` under
`juxt`. -/
lemma lintegral_sigmaFiniteLambdaFun_eq_lintegral_pi (Λ : Finset S) (ξ : S → E)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ ξ)
      = ∫⁻ ω, f (juxt (Λ : Set S) ξ ω) ∂(Measure.pi fun _ : Λ ↦ lam) := by
  rw [_root_.Specification.sigmaFiniteLambdaFun_apply_eq_map]
  exact lintegral_map hf Measurable.juxt

variable {K : ℝ≥0∞}

/-- **Georgii's estimate in the proof of (8.39).** If the unnormalised density `ρ_Λ` varies by at
most a factor `K` between configurations agreeing on `Λ`, then the normalised λ-kernels satisfy
`γ_Λ(A | ζ) ≥ K⁻² γ_Λ(A | η)` for every `A ∈ 𝓕_Λ`. -/
lemma mul_withDensity_sigmaFinitePremodifierNorm_le_of_ratio
    (hρ : _root_.Specification.IsPremodifier ρ)
    {Λ : Finset S} (hK0 : K ≠ 0) (hK : K ≠ ⊤)
    (hratio : ∀ x y : S → E, (∀ i ∈ Λ, x i = y i) → ρ Λ x ≤ K * ρ Λ y)
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A)
    (ζ η : S → E) :
    (K * K)⁻¹ *
        ((_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ η).withDensity
          (_root_.Specification.sigmaFinitePremodifierNorm (S := S) (E := E) lam ρ Λ)) A ≤
      ((_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ ζ).withDensity
          (_root_.Specification.sigmaFinitePremodifierNorm (S := S) (E := E) lam ρ Λ)) A := by
  classical
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hmeasρ : Measurable (ρ Λ) := hρ.measurable Λ
  have hagree : ∀ (ξ₁ ξ₂ : S → E) (ω : Λ → E),
      ∀ i ∈ Λ, juxt (Λ : Set S) ξ₁ ω i = juxt (Λ : Set S) ξ₂ ω i := by
    intro ξ₁ ξ₂ ω i hi
    have hi' : i ∈ (Λ : Set S) := by simpa using hi
    simp [juxt_apply_of_mem hi']
  -- The partition functions differ by at most a factor `K`.
  have hZle : _root_.Specification.sigmaFiniteLambdaZ (S := S) (E := E) lam ρ Λ ζ ≤
      K * _root_.Specification.sigmaFiniteLambdaZ (S := S) (E := E) lam ρ Λ η := by
    rw [_root_.Specification.sigmaFiniteLambdaZ, _root_.Specification.sigmaFiniteLambdaZ,
      lintegral_sigmaFiniteLambdaFun_eq_lintegral_pi (lam := lam) Λ ζ hmeasρ,
      lintegral_sigmaFiniteLambdaFun_eq_lintegral_pi (lam := lam) Λ η hmeasρ,
      ← lintegral_const_mul' _ _ hK]
    exact lintegral_mono fun ω ↦ hratio _ _ (hagree ζ η ω)
  -- So do the restricted integrals of the density over an `𝓕_Λ`-event.
  have hIle :
      (∫⁻ y in A, ρ Λ y
          ∂(_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ η)) ≤
        K * ∫⁻ y in A, ρ Λ y
          ∂(_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ ζ) := by
    rw [← lintegral_indicator hAm, ← lintegral_indicator hAm,
      lintegral_sigmaFiniteLambdaFun_eq_lintegral_pi (lam := lam) Λ η (hmeasρ.indicator hAm),
      lintegral_sigmaFiniteLambdaFun_eq_lintegral_pi (lam := lam) Λ ζ (hmeasρ.indicator hAm),
      ← lintegral_const_mul' _ _ hK]
    refine lintegral_mono fun ω ↦ ?_
    by_cases hmem : juxt (Λ : Set S) η ω ∈ A
    · have hmem' : juxt (Λ : Set S) ζ ω ∈ A :=
        (mem_congr_of_measurableSet_cylinderEvents hA
          (fun i hi ↦ hagree η ζ ω i (by simpa using hi))).1 hmem
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
      exact hratio _ _ (hagree η ζ ω)
    · rw [Set.indicator_of_notMem hmem]
      exact bot_le
  rw [_root_.Specification.withDensity_sigmaFinitePremodifierNorm_apply lam hρ hAm,
    _root_.Specification.withDensity_sigmaFinitePremodifierNorm_apply lam hρ hAm]
  have hstep1 : K⁻¹ * (_root_.Specification.sigmaFiniteLambdaZ (S := S) (E := E) lam ρ Λ η)⁻¹ ≤
      (_root_.Specification.sigmaFiniteLambdaZ (S := S) (E := E) lam ρ Λ ζ)⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl hK0) (Or.inl hK)]
    exact ENNReal.inv_le_inv.2 hZle
  have hstep2 : K⁻¹ * (∫⁻ y in A, ρ Λ y
        ∂(_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ η)) ≤
      ∫⁻ y in A, ρ Λ y
        ∂(_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ ζ) := by
    calc K⁻¹ * (∫⁻ y in A, ρ Λ y
          ∂(_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ η))
        ≤ K⁻¹ * (K * ∫⁻ y in A, ρ Λ y
            ∂(_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ ζ)) := by gcongr
      _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hK0 hK, one_mul]
  calc (K * K)⁻¹ *
        ((_root_.Specification.sigmaFiniteLambdaZ (S := S) (E := E) lam ρ Λ η)⁻¹ *
          ∫⁻ y in A, ρ Λ y
            ∂(_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ η))
      = (K⁻¹ * (_root_.Specification.sigmaFiniteLambdaZ (S := S) (E := E) lam ρ Λ η)⁻¹) *
        (K⁻¹ * ∫⁻ y in A, ρ Λ y
          ∂(_root_.Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ η)) := by
        rw [ENNReal.mul_inv (Or.inl hK0) (Or.inl hK)]; ring
    _ ≤ _ := mul_le_mul' hstep1 hstep2

/-- If arbitrarily large volumes carry a uniform ratio bound `K` for the density, then the
λ-specification satisfies the hypothesis of Georgii (8.38) with `c = K⁻²`. -/
lemma isUniformlyDominated_lambdaSpecification_of_forall_exists_ratio [NeZero lam]
    (hρ : _root_.Specification.IsPremodifier ρ)
    (hZ : _root_.Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam ρ)
    (hK0 : K ≠ 0) (hK : K ≠ ⊤)
    (h : ∀ Λ₀ : Finset S, ∃ Λ : Finset S, Λ₀ ⊆ Λ ∧
      ∀ x y : S → E, (∀ i ∈ Λ, x i = y i) → ρ Λ x ≤ K * ρ Λ y) :
    IsUniformlyDominated
      (_root_.Specification.lambdaSpecification (S := S) (E := E) lam ρ hρ hZ) (K * K)⁻¹ := by
  rintro A hA
  obtain ⟨Λ₀, hA₀⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  obtain ⟨Λ, hΛ₀, hratio⟩ := h Λ₀
  refine ⟨Λ, fun ζ η ↦ ?_⟩
  have hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A :=
    cylinderEvents_mono (X := fun _ : S ↦ E) (by exact_mod_cast hΛ₀) _ hA₀
  have hkey := mul_withDensity_sigmaFinitePremodifierNorm_le_of_ratio (lam := lam) hρ hK0 hK
    hratio hA ζ η
  rwa [_root_.Specification.lambdaSpecification_apply,
    _root_.Specification.lambdaSpecification_apply]

end Gibbsian

/-! ### Georgii (8.39): the one-dimensional structure -/

section OneDimensional

variable [Preorder S]

/-- `A` **spans** the site `i`, i.e. `min A ≤ i < max A`: `A` has an element `≤ i` and an element
`> i`. (For `A = ∅` this is false, matching `min ∅ = ∞`.) -/
def Spans (A : Finset S) (i : S) : Prop := (∃ a ∈ A, a ≤ i) ∧ ∃ b ∈ A, i < b

/-- The sum appearing in Georgii (8.40): `∑_{A : min A ≤ i < max A} δ(Φ_A)`. -/
noncomputable def oscSpan (Φ : Potential S E) (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S, {A : Finset S | Spans A i}.indicator (fun A ↦ Dobrushin.osc (Φ A)) A

variable (S) in
/-- **Georgii's one-dimensional input.** `S` is exhausted by intervals with at most `m` boundary
sites: every finite `Λ₀` is contained in a volume `Λ` admitting a set `D` of at most `m` sites such
that every interaction support meeting `Λ` and leaving `Λ` spans a site of `D`.

Georgii's two cases are `S = ℤ` with `Λ = ]-n, n]` and `D = {-n, n}` (`m = 2`,
`hasBoundedBoundary_int`) and `S = ℕ` with `Λ = [0, n]` and `D = {n}` (`m = 1`,
`hasBoundedBoundary_nat`). -/
def HasBoundedBoundary (m : ℕ) : Prop :=
  ∀ Λ₀ : Finset S, ∃ Λ : Finset S, Λ₀ ⊆ Λ ∧ ∃ D : Finset S, D.card ≤ m ∧
    ∀ A : Finset S, ¬ Disjoint A Λ → ¬ A ⊆ Λ → ∃ k ∈ D, Spans A k

private lemma tsum_finsetSum_ennreal {ι κ : Type*} (D : Finset κ) (g : κ → ι → ℝ≥0∞) :
    ∑' i : ι, ∑ k ∈ D, g k i = ∑ k ∈ D, ∑' i : ι, g k i := by
  classical
  induction D using Finset.induction with
  | empty => simp
  | insert k D hk ih =>
      simp_rw [Finset.sum_insert hk]
      rw [ENNReal.tsum_add, ih]

/-- **Georgii's estimate** `∑_{A ∩ Λ ≠ ∅, A ∖ Λ ≠ ∅} δ(Φ_A) ≤ ∑_{k ∈ D} ∑_{min A ≤ k < max A}
δ(Φ_A)` for a volume `Λ` whose boundary sites are contained in `D`. -/
lemma tsum_osc_boundary_le_sum_oscSpan (Φ : Potential S E) {Λ D : Finset S}
    (hD : ∀ A : Finset S, ¬ Disjoint A Λ → ¬ A ⊆ Λ → ∃ k ∈ D, Spans A k) :
    ∑' A : Finset S, {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ}.indicator
        (fun A ↦ Dobrushin.osc (Φ A)) A
      ≤ ∑ k ∈ D, oscSpan Φ k := by
  classical
  simp only [oscSpan]
  rw [← tsum_finsetSum_ennreal D
    (fun k A ↦ {A : Finset S | Spans A k}.indicator (fun A ↦ Dobrushin.osc (Φ A)) A)]
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases hA : ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ
  · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ} from hA)]
    obtain ⟨k, hkD, hk⟩ := hD A hA.1 hA.2
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun k ↦ {A : Finset S | Spans A k}.indicator
        (fun A ↦ Dobrushin.osc (Φ A)) A) (fun _ _ ↦ bot_le) hkD)
    exact (Set.indicator_of_mem (show A ∈ {A : Finset S | Spans A k} from hk)
      (fun A : Finset S ↦ Dobrushin.osc (Φ A))).symm
  · rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ} from hA)]
    exact bot_le

/-- **Georgii's key one-dimensional bound.** Under (8.40) with bound `s` and an exhaustion by
volumes with at most `m` boundary sites, the Hamiltonian of arbitrarily large volumes varies by at
most `m · s` when the boundary condition changes. -/
lemma abs_hamiltonian_sub_le_of_hasBoundedBoundary {m : ℕ} (hexh : HasBoundedBoundary S m)
    {Φ : Potential S E} [Potential.IsPotential Φ] [Potential.IsSummable Φ] {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ∀ i : S, oscSpan Φ i ≤ ENNReal.ofReal s) (Λ₀ : Finset S) :
    ∃ Λ : Finset S, Λ₀ ⊆ Λ ∧ ∀ x y : S → E, (∀ i ∈ Λ, x i = y i) →
      |Φ.hamiltonian Λ x - Φ.hamiltonian Λ y| ≤ m * s := by
  obtain ⟨Λ, hΛ₀, D, hDcard, hD⟩ := hexh Λ₀
  refine ⟨Λ, hΛ₀, fun x y hxy ↦ ?_⟩
  have hmul : (m : ℝ≥0∞) * ENNReal.ofReal s = ENNReal.ofReal (m * s) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have hb : ‖Φ.hamiltonian Λ x - Φ.hamiltonian Λ y‖ₑ ≤ ENNReal.ofReal (m * s) :=
    calc ‖Φ.hamiltonian Λ x - Φ.hamiltonian Λ y‖ₑ
        ≤ _ := enorm_hamiltonian_sub_le_tsum_osc _ hxy
      _ ≤ ∑ k ∈ D, oscSpan Φ k := tsum_osc_boundary_le_sum_oscSpan Φ hD
      _ ≤ D.card • ENNReal.ofReal s := Finset.sum_le_card_nsmul _ _ _ fun k _ ↦ hs k
      _ = (D.card : ℝ≥0∞) * ENNReal.ofReal s := by rw [nsmul_eq_mul]
      _ ≤ (m : ℝ≥0∞) * ENNReal.ofReal s :=
        mul_le_mul' (by exact_mod_cast hDcard) le_rfl
      _ = ENNReal.ofReal (m * s) := hmul
  rw [Real.enorm_eq_ofReal_abs] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb

variable {Φ : Potential S E}

/-- **Georgii, Theorem (8.39)**, first half, at Georgii's hypotheses: a potential `Φ` in the sense
of Definition (2.2), `λ`-admissible over a σ-finite non-zero a priori measure `λ`, whose
oscillations satisfy `∑_{A : min A ≤ i < max A} δ(Φ_A) ≤ s` for every site `i` (Georgii (8.40)),
has at most one Gibbs measure. -/
theorem subsingleton_G_lambdaSpecification_of_oscSpan_le [Countable S] {m : ℕ}
    (hexh : HasBoundedBoundary S m)
    [Potential.IsPotential Φ] [Potential.IsSummable Φ]
    (lam : Measure E) [SigmaFinite lam] [NeZero lam] (β : ℝ)
    (hZ : _root_.Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam
      (Φ.boltzmannFactor β))
    {s : ℝ} (hs0 : 0 ≤ s) (hs : ∀ i : S, oscSpan Φ i ≤ ENNReal.ofReal s) :
    (G (γ := _root_.Specification.lambdaSpecification (S := S) (E := E) lam
      (Φ.boltzmannFactor β) (Potential.isPremodifier_boltzmannFactor (Φ := Φ) β) hZ)).Subsingleton
    := by
  set K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|β| * (m * s))) with hKdef
  have hK0 : K ≠ 0 := by
    rw [hKdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  have hK : K ≠ ⊤ := by simp [hKdef]
  have hratio : ∀ Λ₀ : Finset S, ∃ Λ : Finset S, Λ₀ ⊆ Λ ∧
      ∀ x y : S → E, (∀ i ∈ Λ, x i = y i) →
        Φ.boltzmannFactor β Λ x ≤ K * Φ.boltzmannFactor β Λ y := by
    intro Λ₀
    obtain ⟨Λ, hΛ₀, hosc⟩ :=
      abs_hamiltonian_sub_le_of_hasBoundedBoundary (E := E) hexh hs0 hs Λ₀
    exact ⟨Λ, hΛ₀, fun x y hxy ↦
      boltzmannFactor_le_of_abs_hamiltonian_sub_le (Φ := Φ) β _ (hosc x y hxy)⟩
  have hdom := isUniformlyDominated_lambdaSpecification_of_forall_exists_ratio (lam := lam)
    (Potential.isPremodifier_boltzmannFactor (Φ := Φ) β) hZ hK0 hK hratio
  exact subsingleton_G_of_isUniformlyDominated
    (ENNReal.inv_ne_zero.2 (ENNReal.mul_ne_top hK hK)) hdom

/-- **Georgii, Theorem (8.39)**, first half, stated with condition (8.40) in Georgii's form
`sup_i ∑_{A : min A ≤ i < max A} δ(Φ_A) < ∞`. -/
theorem subsingleton_G_lambdaSpecification_of_iSup_oscSpan_ne_top [Countable S] {m : ℕ}
    (hexh : HasBoundedBoundary S m)
    [Potential.IsPotential Φ] [Potential.IsSummable Φ]
    (lam : Measure E) [SigmaFinite lam] [NeZero lam] (β : ℝ)
    (hZ : _root_.Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam
      (Φ.boltzmannFactor β))
    (h840 : ⨆ i : S, oscSpan Φ i ≠ ⊤) :
    (G (γ := _root_.Specification.lambdaSpecification (S := S) (E := E) lam
      (Φ.boltzmannFactor β) (Potential.isPremodifier_boltzmannFactor (Φ := Φ) β) hZ)).Subsingleton
    := by
  refine subsingleton_G_lambdaSpecification_of_oscSpan_le hexh lam β hZ
    (s := (⨆ i : S, oscSpan Φ i).toReal) ENNReal.toReal_nonneg fun i ↦ ?_
  rw [ENNReal.ofReal_toReal h840]
  exact le_iSup (fun j : S ↦ oscSpan Φ j) i

/-- **Georgii, Theorem (8.39)**, first half, for the set `𝒢(Φ)` of Gibbs probability measures. -/
theorem subsingleton_GP_lambdaSpecification_of_iSup_oscSpan_ne_top [Countable S] {m : ℕ}
    (hexh : HasBoundedBoundary S m)
    [Potential.IsPotential Φ] [Potential.IsSummable Φ]
    (lam : Measure E) [SigmaFinite lam] [NeZero lam] (β : ℝ)
    (hZ : _root_.Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam
      (Φ.boltzmannFactor β))
    (h840 : ⨆ i : S, oscSpan Φ i ≠ ⊤) :
    (GP (_root_.Specification.lambdaSpecification (S := S) (E := E) lam (Φ.boltzmannFactor β)
      (Potential.isPremodifier_boltzmannFactor (Φ := Φ) β) hZ)).Subsingleton := by
  intro μ hμ ν hν
  exact ProbabilityMeasure.toMeasure_injective
    (subsingleton_G_lambdaSpecification_of_iSup_oscSpan_ne_top hexh lam β hZ h840
      ⟨inferInstance, hμ⟩ ⟨inferInstance, hν⟩)

end OneDimensional

/-! ### Georgii's two chain structures: `S = ℤ` and `S = ℕ` -/

section Chains

/-- An interaction support that meets the interval `]-n, n]` and leaves it spans one of the two
boundary sites `-n`, `n`. -/
lemma spans_of_not_disjoint_of_not_subset_Ioc {A : Finset ℤ} {n : ℤ}
    (hd : ¬ Disjoint A (Finset.Ioc (-n) n)) (hsub : ¬ A ⊆ Finset.Ioc (-n) n) :
    Spans A (-n) ∨ Spans A n := by
  obtain ⟨m, hmA, hmΛ⟩ := Finset.not_disjoint_iff.1 hd
  obtain ⟨p, hpA, hpΛ⟩ := Finset.not_subset.1 hsub
  rw [Finset.mem_Ioc] at hmΛ
  rw [Finset.mem_Ioc, not_and, not_le] at hpΛ
  by_cases hp : -n < p
  · exact Or.inr ⟨⟨m, hmA, hmΛ.2⟩, ⟨p, hpA, hpΛ hp⟩⟩
  · exact Or.inl ⟨⟨p, hpA, not_lt.1 hp⟩, ⟨m, hmA, hmΛ.1⟩⟩

/-- `ℤ` is exhausted by the intervals `]-n, n]`, each with the two boundary sites `-n` and `n`. -/
theorem hasBoundedBoundary_int : HasBoundedBoundary ℤ 2 := by
  classical
  intro Λ₀
  set m : ℕ := Λ₀.sup Int.natAbs with hm
  set n : ℤ := (m : ℤ) + 1 with hn
  refine ⟨Finset.Ioc (-n) n, fun i hi ↦ ?_, {-n, n}, ?_, ?_⟩
  · have h1 : (i.natAbs : ℤ) ≤ (m : ℤ) := by
      exact_mod_cast Finset.le_sup (f := Int.natAbs) hi
    rw [Int.natCast_natAbs] at h1
    rw [Finset.mem_Ioc, hn]
    constructor
    · have := (abs_le.1 h1).1; omega
    · have := (abs_le.1 h1).2; omega
  · exact (Finset.card_insert_le _ _).trans (by simp)
  · intro A hd hsub
    rcases spans_of_not_disjoint_of_not_subset_Ioc hd hsub with h | h
    · exact ⟨-n, by simp, h⟩
    · exact ⟨n, by simp, h⟩

/-- `ℕ` is exhausted by the intervals `[0, n]`, each with the single boundary site `n`. -/
theorem hasBoundedBoundary_nat : HasBoundedBoundary ℕ 1 := by
  classical
  intro Λ₀
  refine ⟨Finset.Iic (Λ₀.sup id), fun i hi ↦ Finset.mem_Iic.2 (Finset.le_sup (f := id) hi),
    {Λ₀.sup id}, by simp, ?_⟩
  intro A hd hsub
  obtain ⟨q, hqA, hqΛ⟩ := Finset.not_disjoint_iff.1 hd
  obtain ⟨p, hpA, hpΛ⟩ := Finset.not_subset.1 hsub
  refine ⟨Λ₀.sup id, by simp, ⟨q, hqA, Finset.mem_Iic.1 hqΛ⟩, ⟨p, hpA, ?_⟩⟩
  simpa [Finset.mem_Iic] using hpΛ

end Chains

/-! ### Georgii (8.39), existence: the many-body part is absolutely summable

Georgii's first step in the existence half of (8.39) is to replace `Φ` by an equivalent potential
whose interaction terms are centred, and to absorb the self-energies `Φ_{i}` into the a priori
measure. Condition (8.40) makes what is left absolutely summable: a volume of at least two sites
containing `i` spans `i` or spans its predecessor, so `∑_{A ∋ i, |A| ≥ 2} δ(Φ_A) ≤ 2s`. -/

section ManyBody

variable {S E : Type*} [MeasurableSpace E] [LinearOrder S] [PredOrder S] {Φ : Potential S E}

/-- A volume of at least two sites containing `i` spans `i` or spans its predecessor. -/
lemma spans_or_spans_pred {A : Finset S} {i : S} (hi : i ∈ A) (hcard : 1 < A.card) :
    Spans A i ∨ Spans A (Order.pred i) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  obtain ⟨j, hj, hji⟩ : ∃ j ∈ A, j ≠ i := by
    rcases eq_or_ne a i with rfl | h
    · exact ⟨b, hb, hab.symm⟩
    · exact ⟨a, ha, h⟩
  rcases hji.lt_or_gt with hlt | hlt
  · exact Or.inr ⟨⟨j, hj, Order.le_pred_of_lt hlt⟩,
      ⟨i, hi, Order.pred_lt_of_not_isMin (not_isMin_of_lt hlt)⟩⟩
  · exact Or.inl ⟨⟨i, hi, le_rfl⟩, ⟨j, hj, hlt⟩⟩

/-- **Georgii (8.40) bounds the many-body oscillation.** -/
lemma oscNormAt_manyBody_le (Φ : Potential S E) (i : S) :
    Φ.manyBody.oscNormAt i ≤ oscSpan Φ i + oscSpan Φ (Order.pred i) := by
  rw [Potential.oscNormAt, oscSpan, oscSpan, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases hiA : A ∈ ({A : Finset S | i ∈ A} : Set (Finset S))
  swap
  · rw [Set.indicator_of_notMem hiA]; exact zero_le'
  rw [Set.indicator_of_mem hiA]
  rcases le_or_gt A.card 1 with hcard | hcard
  · have h0 : _root_.oscOutside (∅ : Set S) (Φ.manyBody A) = 0 := by
      rw [Potential.manyBody_of_card_le hcard]; exact Dobrushin.osc_const 0
    rw [h0]; exact zero_le'
  rw [Potential.manyBody_of_one_lt_card hcard]
  rcases spans_or_spans_pred hiA hcard with hs | hs
  · rw [Set.indicator_of_mem (show A ∈ ({A : Finset S | Spans A i} : Set (Finset S)) from hs)]
    exact self_le_add_right _ _
  · rw [Set.indicator_of_mem
      (show A ∈ ({A : Finset S | Spans A (Order.pred i)} : Set (Finset S)) from hs)]
    exact self_le_add_left _ _

/-- **Georgii (8.39), the reduction to `ℬ`.** Under (8.40) the many-body part of `Φ`, recentred at
any configuration, is absolutely summable — an element of Georgii's space `ℬ` equivalent to
`Φ.manyBody`. -/
theorem isAbsolutelySummable_centre_manyBody (h840 : ⨆ i : S, oscSpan Φ i ≠ ⊤) (η₀ : S → E) :
    (Φ.manyBody.centre η₀).IsAbsolutelySummable := by
  refine ⟨fun i ↦ ne_top_of_le_ne_top ?_ (Potential.normAt_centre_le η₀ i)⟩
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h840 ∘ (eq_top_mono (le_iSup _ i)),
    h840 ∘ (eq_top_mono (le_iSup _ (Order.pred i)))⟩) (oscNormAt_manyBody_le Φ i)

/-- **Georgii, Theorem (8.39)**, at his own hypotheses: a potential in the sense of Definition
(2.2), `λ`-admissible over a probability a priori measure on a standard Borel state space, whose
oscillations satisfy (8.40), has exactly one Gibbs measure. No absolute summability is assumed:
(8.40) makes the recentred many-body part absolutely summable, and the self-energies go into the a
priori measure. -/
theorem existsUnique_mem_GP_lambdaSpecification_of_iSup_oscSpan_ne_top [Countable S]
    [StandardBorelSpace E] {m : ℕ} (hexh : HasBoundedBoundary S m)
    [Potential.IsPotential Φ] [Potential.IsSummable Φ]
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (hZ : _root_.Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam
      (Φ.boltzmannFactor β))
    (h840 : ⨆ i : S, oscSpan Φ i ≠ ⊤) :
    ∃! μ : ProbabilityMeasure (S → E),
      μ ∈ GP (_root_.Specification.lambdaSpecification (S := S) (E := E) lam
        (Φ.boltzmannFactor β) (Potential.isPremodifier_boltzmannFactor (Φ := Φ) β) hZ) := by
  classical
  have hE : Nonempty E := lam.nonempty_of_neZero
  set η₀ : S → E := fun _ ↦ Classical.arbitrary E with hη₀
  haveI : Potential.IsAbsolutelySummable ((Potential.manyBody Φ).centre η₀) :=
    isAbsolutelySummable_centre_manyBody h840 η₀
  obtain ⟨μ, hμ⟩ := Potential.GP_lambdaSpecification_nonempty (Φ := Φ) (β := β) (η₀ := η₀)
    (lam := lam)
  exact ⟨μ, hμ, fun ν hν ↦ subsingleton_GP_lambdaSpecification_of_iSup_oscSpan_ne_top hexh lam β
    hZ h840 hν hμ⟩

end ManyBody

/-! ### Georgii, Comments (8.41): the shift-invariant reformulation and pair potentials -/

section Comments

variable {E : Type*} [MeasurableSpace E]

/-- The smallest site of a finite set of integers (`0` by convention on `∅`). -/
noncomputable def minSite (A : Finset ℤ) : ℤ := if h : A.Nonempty then A.min' h else 0

/-- The largest site of a finite set of integers (`0` by convention on `∅`). -/
noncomputable def maxSite (A : Finset ℤ) : ℤ := if h : A.Nonempty then A.max' h else 0

/-- Georgii's `diam A = max A - min A`. -/
noncomputable def diamSite (A : Finset ℤ) : ℕ := (maxSite A - minSite A).toNat

/-- The translate `A + n` of a finite set of integers. -/
def shiftFinset (n : ℤ) (A : Finset ℤ) : Finset ℤ := A.map (Equiv.addRight n).toEmbedding

@[simp] lemma mem_shiftFinset {n x : ℤ} {A : Finset ℤ} : x ∈ shiftFinset n A ↔ x - n ∈ A := by
  rw [shiftFinset, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨x - n, h, by simp⟩

@[simp] lemma shiftFinset_zero (A : Finset ℤ) : shiftFinset 0 A = A := by
  ext x; simp

lemma shiftFinset_shiftFinset (m n : ℤ) (A : Finset ℤ) :
    shiftFinset m (shiftFinset n A) = shiftFinset (n + m) A := by
  ext x
  simp only [mem_shiftFinset]
  rw [show x - m - n = x - (n + m) by ring]

@[simp] lemma nonempty_shiftFinset {n : ℤ} {A : Finset ℤ} :
    (shiftFinset n A).Nonempty ↔ A.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x - n, mem_shiftFinset.1 hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x + n, mem_shiftFinset.2 (by simpa using hx)⟩

lemma minSite_of_nonempty {A : Finset ℤ} (hA : A.Nonempty) : minSite A = A.min' hA := by
  simp [minSite, hA]

lemma maxSite_of_nonempty {A : Finset ℤ} (hA : A.Nonempty) : maxSite A = A.max' hA := by
  simp [maxSite, hA]

lemma minSite_mem {A : Finset ℤ} (hA : A.Nonempty) : minSite A ∈ A := by
  rw [minSite_of_nonempty hA]; exact A.min'_mem hA

lemma maxSite_mem {A : Finset ℤ} (hA : A.Nonempty) : maxSite A ∈ A := by
  rw [maxSite_of_nonempty hA]; exact A.max'_mem hA

lemma minSite_le {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) : minSite A ≤ a := by
  rw [minSite_of_nonempty ⟨a, ha⟩]; exact A.min'_le a ha

lemma le_maxSite {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) : a ≤ maxSite A := by
  rw [maxSite_of_nonempty ⟨a, ha⟩]; exact A.le_max' a ha

lemma minSite_le_maxSite {A : Finset ℤ} (hA : A.Nonempty) : minSite A ≤ maxSite A :=
  le_maxSite (minSite_mem hA)

lemma minSite_shiftFinset {A : Finset ℤ} (hA : A.Nonempty) (n : ℤ) :
    minSite (shiftFinset n A) = minSite A + n := by
  refine le_antisymm (minSite_le (mem_shiftFinset.2 (by simpa using minSite_mem hA))) ?_
  have hA' : (shiftFinset n A).Nonempty := nonempty_shiftFinset.2 hA
  have hmem : minSite (shiftFinset n A) - n ∈ A := mem_shiftFinset.1 (minSite_mem hA')
  have := minSite_le hmem
  omega

lemma maxSite_shiftFinset {A : Finset ℤ} (hA : A.Nonempty) (n : ℤ) :
    maxSite (shiftFinset n A) = maxSite A + n := by
  refine le_antisymm ?_ (le_maxSite (mem_shiftFinset.2 (by simpa using maxSite_mem hA)))
  have hA' : (shiftFinset n A).Nonempty := nonempty_shiftFinset.2 hA
  have hmem : maxSite (shiftFinset n A) - n ∈ A := mem_shiftFinset.1 (maxSite_mem hA')
  have := le_maxSite hmem
  omega

lemma diamSite_shiftFinset {A : Finset ℤ} (hA : A.Nonempty) (n : ℤ) :
    diamSite (shiftFinset n A) = diamSite A := by
  rw [diamSite, diamSite, minSite_shiftFinset hA, maxSite_shiftFinset hA]
  congr 1
  ring

/-- The normalizing translation `A ↦ (A - min A, min A)`. It is injective, which is what turns
Georgii's "the sum (8.40) counts `diam A` translates of each `A`" into an inequality between the
sums (8.40) and (8.42). -/
noncomputable def normalizeSite (A : Finset ℤ) : Finset ℤ × ℤ :=
  (shiftFinset (-minSite A) A, minSite A)

lemma normalizeSite_injective : Function.Injective normalizeSite := by
  intro A B h
  have h1 : shiftFinset (-minSite A) A = shiftFinset (-minSite B) B := congrArg Prod.fst h
  have h2 : minSite A = minSite B := congrArg Prod.snd h
  have hA : shiftFinset (minSite A) (shiftFinset (-minSite A) A) = A := by
    rw [shiftFinset_shiftFinset]; simp
  have hB : shiftFinset (minSite B) (shiftFinset (-minSite B) B) = B := by
    rw [shiftFinset_shiftFinset]; simp
  calc A = shiftFinset (minSite A) (shiftFinset (-minSite A) A) := hA.symm
    _ = shiftFinset (minSite B) (shiftFinset (-minSite B) B) := by rw [h1, h2]
    _ = B := hB

/-- Georgii (8.42): `∑_{A : min A = 0} diam A · δ(Φ_A)`. -/
noncomputable def oscSpanDiam (Φ : Potential ℤ E) : ℝ≥0∞ :=
  ∑' A : Finset ℤ, {A : Finset ℤ | minSite A = 0}.indicator
    (fun A ↦ diamSite A * Dobrushin.osc (Φ A)) A

lemma minSite_pair {a b : ℤ} (hab : a < b) : minSite ({a, b} : Finset ℤ) = a := by
  have hne : ({a, b} : Finset ℤ).Nonempty := ⟨a, by simp⟩
  refine le_antisymm (minSite_le (by simp)) ?_
  have hm := minSite_mem hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h <;> omega

lemma maxSite_pair {a b : ℤ} (hab : a < b) : maxSite ({a, b} : Finset ℤ) = b := by
  have hne : ({a, b} : Finset ℤ).Nonempty := ⟨a, by simp⟩
  refine le_antisymm ?_ (le_maxSite (by simp))
  have hm := maxSite_mem hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h <;> omega

lemma diamSite_pair {a b : ℤ} (hab : a < b) : diamSite ({a, b} : Finset ℤ) = (b - a).toNat := by
  rw [diamSite, minSite_pair hab, maxSite_pair hab]

/-- **Georgii, Comment (8.41)(2), termwise.** A pair `{0, n}` with `n > 0` contributes
`n · δ(Φ_{{0,n}})` to the sum (8.42). -/
theorem oscSpanDiam_indicator_pair {Φ : Potential ℤ E} {n : ℕ} (hn : 0 < n) :
    {A : Finset ℤ | minSite A = 0}.indicator
        (fun A ↦ diamSite A * Dobrushin.osc (Φ A)) {0, (n : ℤ)} =
      (n : ℝ≥0∞) * Dobrushin.osc (Φ {0, (n : ℤ)}) := by
  have hn' : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.2 hn
  rw [Set.indicator_of_mem (show _ ∈ {A : Finset ℤ | minSite A = 0} from minSite_pair hn'),
    diamSite_pair hn', sub_zero, Int.toNat_natCast]

lemma injective_pairZero : Function.Injective (fun n : ℕ ↦ ({0, (n : ℤ)} : Finset ℤ)) := by
  intro n m h
  have h' : ({0, (n : ℤ)} : Finset ℤ) = {0, (m : ℤ)} := h
  have h1 : ((n : ℤ)) ∈ ({0, (m : ℤ)} : Finset ℤ) := by rw [← h']; simp
  have h2 : ((m : ℤ)) ∈ ({0, (n : ℤ)} : Finset ℤ) := by rw [h']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  omega

/-- **Georgii, Comment (8.41)(2).** For a *pair* potential on `ℤ` — one whose interaction terms
other than the two-point ones have vanishing oscillation — the sum (8.42) is
`∑_{n ≥ 1} n · δ(Φ_{{0,n}})`. In Georgii's example `δ(Φ_{{i,j}}) = |i − j|^{-p} δ(φ)` this is
`δ(φ) ∑_{n ≥ 1} n^{1-p}`. -/
theorem oscSpanDiam_eq_tsum_pair {Φ : Potential ℤ E}
    (hpair : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → Dobrushin.osc (Φ A) = 0) :
    oscSpanDiam Φ = ∑' n : ℕ, (n : ℝ≥0∞) * Dobrushin.osc (Φ {0, (n : ℤ)}) := by
  classical
  have hsupp : Function.support
      ({A : Finset ℤ | minSite A = 0}.indicator
        (fun A ↦ (diamSite A : ℝ≥0∞) * Dobrushin.osc (Φ A)))
      ⊆ Set.range (fun n : ℕ ↦ ({0, (n : ℤ)} : Finset ℤ)) := by
    refine Function.support_subset_iff.2 fun A hA ↦ ?_
    by_cases hmem : minSite A = 0
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset ℤ | minSite A = 0} from hmem)] at hA
      have hosc : Dobrushin.osc (Φ A) ≠ 0 := fun h ↦ hA (by rw [h, mul_zero])
      obtain ⟨a, b, hab, rfl⟩ : ∃ a b : ℤ, a < b ∧ A = {a, b} := by
        by_contra hcon
        exact hosc (hpair A fun a b hab hA' ↦ hcon ⟨a, b, hab, hA'⟩)
      have ha : a = 0 := by rw [minSite_pair hab] at hmem; exact hmem
      subst ha
      refine ⟨b.toNat, ?_⟩
      change ({0, ((b.toNat : ℕ) : ℤ)} : Finset ℤ) = {0, b}
      rw [Int.toNat_of_nonneg hab.le]
    · rw [Set.indicator_of_notMem (show A ∉ {A : Finset ℤ | minSite A = 0} from hmem)] at hA
      exact absurd rfl hA
  rw [oscSpanDiam, ← injective_pairZero.tsum_eq hsupp]
  refine tsum_congr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h00 : ({0, ((0 : ℕ) : ℤ)} : Finset ℤ) = {0} := by norm_num
    have hne : ({0} : Finset ℤ).Nonempty := ⟨0, by simp⟩
    have hmin : minSite ({0} : Finset ℤ) = 0 := by
      rw [minSite_of_nonempty hne]; simp
    have hmax : maxSite ({0} : Finset ℤ) = 0 := by
      rw [maxSite_of_nonempty hne]; simp
    simp only [h00, Set.indicator_of_mem (show ({0} : Finset ℤ) ∈
      {A : Finset ℤ | minSite A = 0} from hmin), diamSite, hmin, hmax]
    simp
  · exact oscSpanDiam_indicator_pair (Φ := Φ) hn

/-- **Georgii, Comment (8.41)(2): the pair potential `Φ_{{i,j}} = |i − j|^{-p} φ(σ_i, σ_j)`.**
If the two-point oscillations decay as `δ(Φ_{{0,n}}) ≤ c n^{-p}` with `p > 2`, then the sum (8.42)
is finite, since it is `∑_{n ≥ 1} n · δ(Φ_{{0,n}}) ≤ c ∑_{n ≥ 1} n^{1-p} < ∞`. -/
theorem oscSpanDiam_ne_top_of_pair_rpow_le {Φ : Potential ℤ E}
    (hpair : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → Dobrushin.osc (Φ A) = 0)
    {c p : ℝ} (hp : 2 < p)
    (hbd : ∀ n : ℕ, 0 < n →
      Dobrushin.osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p))) :
    oscSpanDiam Φ ≠ ⊤ := by
  have hsum : Summable (fun n : ℕ ↦ c * (n : ℝ) ^ (1 - p)) :=
    (Real.summable_nat_rpow.2 (by linarith)).mul_left c
  refine ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top ?_
  rw [oscSpanDiam_eq_tsum_pair hpair]
  refine ENNReal.tsum_le_tsum fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrpow : (n : ℝ) * (n : ℝ) ^ (-p) = (n : ℝ) ^ (1 - p) := by
    rw [show (1 : ℝ) - p = 1 + -p by ring, Real.rpow_add hnpos, Real.rpow_one]
  calc (n : ℝ≥0∞) * Dobrushin.osc (Φ {0, (n : ℤ)})
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal (c * (n : ℝ) ^ (-p)) := by gcongr; exact hbd n hn
    _ = ENNReal.ofReal (c * (n : ℝ) ^ (1 - p)) := by
        rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul hnpos.le]
        congr 1
        rw [show (n : ℝ) * (c * (n : ℝ) ^ (-p)) = c * ((n : ℝ) * (n : ℝ) ^ (-p)) by ring, hrpow]

/-- The set of pairs `(B, d)` accounting for the translates `B + d` that span the site `i`:
`B` is normalized (`min B = 0`) and `d = min (B + d)` ranges over the `diam B` integers in
`]i − diam B, i]`. -/
def spanBoxSet (i : ℤ) : Set (Finset ℤ × ℤ) :=
  {p | minSite p.1 = 0 ∧ p.2 ∈ Finset.Ioc (i - diamSite p.1) i}

lemma mem_spanBoxSet {i : ℤ} {p : Finset ℤ × ℤ} :
    p ∈ spanBoxSet i ↔ minSite p.1 = 0 ∧ p.2 ∈ Finset.Ioc (i - diamSite p.1) i := Iff.rfl

/-- The summand of Georgii (8.42), spread over the pairs of `spanBoxSet`. -/
noncomputable def spanBox (Φ : Potential ℤ E) (i : ℤ) (p : Finset ℤ × ℤ) : ℝ≥0∞ :=
  (spanBoxSet i).indicator (fun q ↦ Dobrushin.osc (Φ q.1)) p

lemma spanBox_apply (Φ : Potential ℤ E) (i : ℤ) (p : Finset ℤ × ℤ) :
    spanBox Φ i p = (spanBoxSet i).indicator (fun q ↦ Dobrushin.osc (Φ q.1)) p := rfl

lemma tsum_spanBox (Φ : Potential ℤ E) (i : ℤ) :
    ∑' p : Finset ℤ × ℤ, spanBox Φ i p = oscSpanDiam Φ := by
  classical
  rw [ENNReal.tsum_prod', oscSpanDiam]
  refine tsum_congr fun B ↦ ?_
  by_cases hB : minSite B = 0
  · rw [Set.indicator_of_mem (show B ∈ {A : Finset ℤ | minSite A = 0} from hB)]
    have hzero : ∀ d ∉ Finset.Ioc (i - (diamSite B : ℤ)) i, spanBox Φ i (B, d) = 0 := by
      intro d hd
      have hnot : ((B, d) : Finset ℤ × ℤ) ∉ spanBoxSet i := fun h ↦
        hd (mem_spanBoxSet.1 h).2
      rw [spanBox_apply]
      exact Set.indicator_of_notMem hnot _
    have hval : ∀ d ∈ Finset.Ioc (i - (diamSite B : ℤ)) i,
        spanBox Φ i (B, d) = Dobrushin.osc (Φ B) := by
      intro d hd
      have hmem : ((B, d) : Finset ℤ × ℤ) ∈ spanBoxSet i := mem_spanBoxSet.2 ⟨hB, hd⟩
      rw [spanBox_apply]
      exact Set.indicator_of_mem hmem _
    have hcard : (Finset.Ioc (i - (diamSite B : ℤ)) i).card = diamSite B := by
      rw [Int.card_Ioc]; omega
    rw [tsum_eq_sum hzero, Finset.sum_congr rfl hval, Finset.sum_const, hcard, nsmul_eq_mul]
  · rw [Set.indicator_of_notMem (show B ∉ {A : Finset ℤ | minSite A = 0} from hB)]
    have hzero : ∀ d : ℤ, spanBox Φ i (B, d) = 0 := by
      intro d
      have hnot : ((B, d) : Finset ℤ × ℤ) ∉ spanBoxSet i := fun h ↦
        hB (mem_spanBoxSet.1 h).1
      rw [spanBox_apply]
      exact Set.indicator_of_notMem hnot _
    simp [hzero]

/-- **Georgii, Comment (8.41)(1).** For a potential on `ℤ` whose oscillations are shift invariant,
the sum (8.40) at any site `i` is at most the sum (8.42): the sum (8.40) takes separate account of
the `diam A` translates of each `A` with `min A = 0`. -/
theorem oscSpan_le_oscSpanDiam {Φ : Potential ℤ E}
    (hshift : ∀ (n : ℤ) (A : Finset ℤ),
      Dobrushin.osc (Φ (shiftFinset n A)) = Dobrushin.osc (Φ A))
    (i : ℤ) : oscSpan Φ i ≤ oscSpanDiam Φ := by
  classical
  have hstep : ∀ A : Finset ℤ,
      {A : Finset ℤ | Spans A i}.indicator (fun A ↦ Dobrushin.osc (Φ A)) A
        ≤ spanBox Φ i (normalizeSite A) := by
    intro A
    by_cases hA : Spans A i
    · obtain ⟨⟨a, haA, hai⟩, ⟨b, hbA, hib⟩⟩ := hA
      have hne : A.Nonempty := ⟨a, haA⟩
      have hmin : minSite A ≤ i := le_trans (minSite_le haA) hai
      have hmax : i < maxSite A := lt_of_lt_of_le hib (le_maxSite hbA)
      have hdiam : (diamSite A : ℤ) = maxSite A - minSite A := by
        rw [diamSite, Int.toNat_of_nonneg (by have := minSite_le_maxSite hne; omega)]
      have hd : diamSite (shiftFinset (-minSite A) A) = diamSite A := diamSite_shiftFinset hne _
      have hmemP : normalizeSite A ∈ spanBoxSet i := by
        refine mem_spanBoxSet.2 ⟨?_, ?_⟩
        · simpa [normalizeSite] using minSite_shiftFinset hne (-minSite A)
        · simp only [normalizeSite, hd, Finset.mem_Ioc]
          omega
      have hval : spanBox Φ i (normalizeSite A)
          = Dobrushin.osc (Φ (normalizeSite A).1) := by
        rw [spanBox_apply]
        exact Set.indicator_of_mem hmemP _
      rw [Set.indicator_of_mem (show A ∈ {A : Finset ℤ | Spans A i} from
        ⟨⟨a, haA, hai⟩, ⟨b, hbA, hib⟩⟩), hval]
      exact le_of_eq (hshift (-minSite A) A).symm
    · rw [Set.indicator_of_notMem (show A ∉ {A : Finset ℤ | Spans A i} from hA)]
      exact bot_le
  calc oscSpan Φ i ≤ ∑' A : Finset ℤ, spanBox Φ i (normalizeSite A) :=
        ENNReal.tsum_le_tsum hstep
    _ ≤ ∑' p : Finset ℤ × ℤ, spanBox Φ i p :=
        ENNReal.tsum_comp_le_tsum_of_injective normalizeSite_injective _
    _ = oscSpanDiam Φ := tsum_spanBox Φ i

/-- **Georgii, Comment (8.41)(1).** For a potential on `ℤ` with shift-invariant oscillations,
condition (8.42) implies condition (8.40). -/
theorem iSup_oscSpan_ne_top_of_oscSpanDiam_ne_top {Φ : Potential ℤ E}
    (hshift : ∀ (n : ℤ) (A : Finset ℤ),
      Dobrushin.osc (Φ (shiftFinset n A)) = Dobrushin.osc (Φ A))
    (h842 : oscSpanDiam Φ ≠ ⊤) : ⨆ i : ℤ, oscSpan Φ i ≠ ⊤ :=
  ne_top_of_le_ne_top h842 (iSup_le fun i ↦ oscSpan_le_oscSpanDiam hshift i)

end Comments

/-! ### Georgii (8.39) for a probability a priori measure and `Φ ∈ ℬ` -/

section Probability

variable {E : Type*} [MeasurableSpace E] {Φ : Potential ℤ E}

/-- The Gibbsian specification of an absolutely summable potential over a probability a priori
measure is the λ-specification of `Φ.boltzmannFactor β`. -/
lemma gibbsSpecificationOfAbsolutelySummable_eq_lambdaSpecification
    [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (hZ : _root_.Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ) (E := E) lam
      (Φ.boltzmannFactor β)) :
    Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam β =
      _root_.Specification.lambdaSpecification (S := ℤ) (E := E) lam (Φ.boltzmannFactor β)
        (Potential.isPremodifier_boltzmannFactor (Φ := Φ) β) hZ :=
  (_root_.Specification.lambdaSpecification_eq_modification_isssd (S := ℤ) (E := E) lam
    (Potential.isPremodifier_boltzmannFactor (Φ := Φ) β) hZ
    (Potential.isPremodifierAdmissible_boltzmannFactor (Φ := Φ) lam β)).symm

/-- **Georgii, Theorem (8.39)**, first half, for an absolutely summable potential and a probability
a priori measure on `ℤ`. -/
theorem subsingleton_G_of_iSup_oscSpan_ne_top
    [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (h840 : ⨆ i : ℤ, oscSpan Φ i ≠ ⊤) :
    (G (γ := Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam β)).Subsingleton := by
  have hZ : _root_.Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ) (E := E) lam
      (Φ.boltzmannFactor β) :=
    (_root_.Specification.isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible
      (S := ℤ) (E := E) lam _).1
      (Potential.isPremodifierAdmissible_boltzmannFactor (Φ := Φ) lam β)
  rw [gibbsSpecificationOfAbsolutelySummable_eq_lambdaSpecification lam β hZ]
  exact subsingleton_G_lambdaSpecification_of_iSup_oscSpan_ne_top hasBoundedBoundary_int lam β hZ
    h840

/-- **Georgii, Theorem (8.39)**, first half, for the set `𝒢(Φ)` of Gibbs probability measures. -/
theorem subsingleton_GP_of_iSup_oscSpan_ne_top
    [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (h840 : ⨆ i : ℤ, oscSpan Φ i ≠ ⊤) :
    (GP (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam β)).Subsingleton := by
  intro μ hμ ν hν
  exact ProbabilityMeasure.toMeasure_injective
    (subsingleton_G_of_iSup_oscSpan_ne_top lam β h840 ⟨inferInstance, hμ⟩ ⟨inferInstance, hν⟩)

/-- **Georgii, Theorem (8.39) with Comments (8.41): uniqueness far past nearest-neighbour.**
An absolutely summable pair potential on `ℤ` whose oscillations are shift invariant and decay as
`δ(Φ_{{0,n}}) ≤ c n^{-p}` with `p > 2` has at most one Gibbs measure. -/
theorem subsingleton_G_of_pair_rpow_le
    [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (hshift : ∀ (n : ℤ) (A : Finset ℤ),
      Dobrushin.osc (Φ (shiftFinset n A)) = Dobrushin.osc (Φ A))
    (hpair : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → Dobrushin.osc (Φ A) = 0)
    {c p : ℝ} (hp : 2 < p)
    (hbd : ∀ n : ℕ, 0 < n →
      Dobrushin.osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p))) :
    (G (γ := Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam β)).Subsingleton :=
  subsingleton_G_of_iSup_oscSpan_ne_top lam β
    (iSup_oscSpan_ne_top_of_oscSpanDiam_ne_top hshift
      (oscSpanDiam_ne_top_of_pair_rpow_le hpair hp hbd))

/-- **Georgii, Theorem (8.39)**, second half: over a standard Borel state space the Gibbs measure
exists, so `|𝒢(Φ)| = 1`. Existence is Georgii (4.23)(a). -/
theorem existsUnique_mem_GP_of_iSup_oscSpan_ne_top [StandardBorelSpace E]
    [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (h840 : ⨆ i : ℤ, oscSpan Φ i ≠ ⊤) :
    ∃! μ : ProbabilityMeasure (ℤ → E),
      μ ∈ GP (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam β) := by
  obtain ⟨μ, hμ⟩ := Potential.GP_gibbsSpecification_nonempty (Φ := Φ) lam β
  exact ⟨μ, hμ, fun ν hν ↦ subsingleton_GP_of_iSup_oscSpan_ne_top lam β h840 hν hμ⟩

end Probability

end GibbsMeasure
end MeasureTheory
