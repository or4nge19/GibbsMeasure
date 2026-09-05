/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.SpitzerCox
public import GibbsMeasure.Model.BoundaryLawMarkovProperty
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.Tilted
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Independence.Basic

/-!
# Georgii Corollary (11.33): the Markov chains among the Spitzer–Cox Gibbs measures

Sites `ℤ`, state space `E = ℤ₊ = ℕ`, `0 < p < 1`, and the Spitzer–Cox matrix `Q` of (11.26)
(`GibbsMeasure/Model/SpitzerCox.lean`). By Theorem (11.31) every `μ ∈ 𝒢(Q)` is
`μ = ∫_{[0,∞[²} μ^{u,v} m(du, dv)` with `m = limitLaw p μ` the law of the boundary limits
`(U, V) = (lim_{i → -∞} σ_i p^{-i}, lim_{i → ∞} σ_i p^i)`.

**Corollary (11.33).** For `μ ∈ 𝒢(Q)` the following are equivalent:

* (a) `μ` is a Markov chain;
* (b) `U` and `V` are independent under `μ̃ = e^{-UV} μ / μ(e^{-UV})`;
* (c) `μ = ∫ m₁(du) ∫ m₂(dv) e^{uv} μ^{u,v}` for suitable (finite) measures `m₁, m₂` on `[0, ∞[`.

Georgii's point is the failure of two converses: not every Markov chain in `𝒢(Q)` is extreme
(`exists_isMarkovChain_notMem_extremePoints_G`: the mixture `½μ^{0,0} + ½μ^{1,0}` is a Markov
chain by (c) and is not extreme), and not every Markov field in `𝒢(Q)` is a Markov chain
(`exists_mem_G_not_isMarkovChain`: `½μ^{0,0} + ½μ^{1,1}` is in `𝒢(Q)` but fails (c)); so the
converses of Remark (10.9)(3) and of Theorem (10.21) fail in general. The extreme points
`μ^{u,v}` themselves *are* Markov chains (`chainFamily_isMarkovChain`), by (c) with
`m₁ = e^{-uv}δ_u`, `m₂ = δ_v`.

## The formalisation

* `μ̃` is Mathlib's exponential tilt `μ.tilted (fun ω ↦ -(U ω * V ω))`
  (`MeasureTheory.Measure.tilted`), so (b) is `IndepFun (limAtBot p) (limAtTop p) μ̃`.
* (c) is `μ = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1)` with
  `expWeight (u, v) = e^{uv}` and `IsFiniteMeasure m₁`, `IsFiniteMeasure m₂`. Georgii writes
  "suitable measures", and `isMarkovChain_tfae` carries both readings: clause (c) with finite
  `m₁, m₂` and clause (c') with merely `s`-finite ones. They are equivalent, because finiteness
  is *forced*: `e^{uv} ≥ 1` and `μ` is a probability measure, so
  `m₁([0,∞[) m₂([0,∞[) ≤ ∫ e^{uv} d(m₁ ⊗ m₂) = 1` with both factors non-zero
  (`isFiniteMeasure_of_bind_chainFamily_eq`).
* (a) is `∃ P : ℤ → Kernel ℕ ℕ, (∀ i, IsMarkovKernel (P i)) ∧ IsMarkovChain P μ`, Georgii's
  Definition (10.4).

**(a) ⇒ (c)** is Georgii's argument. For a Markov chain `μ`, Theorem (11.9)(b) represents it by a
boundary law, and the past `𝓕_{]-∞,0]}` and the future `𝓕_{[0,∞[}` of the measure (11.10) are
conditionally independent given `σ_0` (`IsBoundaryLaw.measure_inter_inter_preimage_mul`,
`GibbsMeasure/Model/BoundaryLawMarkovProperty.lean`). Since `U` is a function of the past and `V`
one of the future, the measure `m̄(du, dv) = e^{-(1+u)(1+v)} m(du, dv)` — which is the law of
`(U, V)` on the event `{σ_0 = 0}`, because `μ^{u,v}(σ_0 = 0) = e^{-(1+u)(1+v)}` by (11.30) — is a
product measure: `m̄(A × B) m̄(univ) = m̄(A × univ) m̄(univ × B)` (`limitLawZero_prod_mul`,
`smul_limitLawZero_eq_prod`). Undoing the density gives (c) with `m₁ = e^{1+u} m̄₁`,
`m₂ = e^{v} m̄₂ / m̄(univ)` (`exists_prod_of_isMarkovChain`).

**(c) ⇒ (a)**: `ℓ_i = ∫ ℓ^u_i m₁(du)`, `r_i = ∫ r^v_i m₂(dv)` (`leftMixture`, `rightMixture`) is a
boundary law for `Q` (`isBoundaryLaw_mixture`), and `μ` is its measure (11.10) because the weights
`e^{uv}` and `e^{-uv}` cancel in the cylinder probabilities (`bind_chainFamily_intervalCylinder`);
Theorem (11.9)(a) makes it a Markov chain (`exists_isMarkovChain_of_prod`). Only `SFinite m₁`,
`SFinite m₂` is needed here.

**(b) ⇔ (c)** is "immediate from Theorem (11.31)": the law of `(U, V)` under `μ̃` is the tilt
`e^{-uv} m / Z` of `m` (`map_limPair_tilted`), and by the uniqueness of the representing measure
(`eq_limitLaw_of_join_map_chainFamily_eq`) (c) says exactly that `e^{-uv} m` is a product measure
(`indepFun_tilted_of_prod`, `exists_prod_of_indepFun_tilted`).

The three clauses are collected in `isMarkovChain_tfae`.

## Main declarations

* `measurable_cylinderEvents_Iic_limAtBot`, `measurable_cylinderEvents_Ici_limAtTop`: `U` is
  `𝓕_{]-∞,0]}`-measurable and `V` is `𝓕_{[0,∞[}`-measurable.
* `measure_limPair_preimage_inter`: `μ({(U, V) ∈ S} ∩ A) = ∫_S μ^{u,v}(A) m(du, dv)`.
* `zeroWeight`, `limitLawZero`, `limitLawZero_apply`: Georgii's `m̄`, the law of `(U, V)` on
  `{σ_0 = 0}`.
* `limitLawZero_prod_mul`, `smul_limitLawZero_eq_prod`: for a Markov chain, `m̄` is a product.
* `expWeight`, `exists_prod_of_isMarkovChain`: **(11.33), (a) ⇒ (c)**.
* `leftMixture`, `rightMixture`, `isBoundaryLaw_mixture`, `bind_chainFamily_intervalCylinder`,
  `exists_isMarkovChain_of_prod`: **(11.33), (c) ⇒ (a)**.
* `map_limPair_tilted`, `indepFun_tilted_of_prod`, `exists_prod_of_indepFun_tilted`:
  **(11.33), (b) ⇔ (c)**.
* `one_le_expWeight`, `lintegral_expWeight_eq_one`, `isFiniteMeasure_of_bind_chainFamily_eq`:
  Georgii's "suitable measures" in (c) are automatically finite.
* `isMarkovChain_tfae`: **Georgii Corollary (11.33)**, with clause (c) in both the finite and the
  `s`-finite reading.
* `chainFamily_isMarkovChain`: every extreme point `μ^{u,v}` is a Markov chain.
* `expWeight_snd_zero`, `bind_chainFamily_two_point`, `notMem_extremePoints_half_add_half`,
  `exists_isMarkovChain_notMem_extremePoints_G`, `exists_mem_G_not_isMarkovChain`: **the two
  conclusions Georgii draws from (11.33)** — the converses of Theorem (10.21) and of Remark
  (10.9)(3) both fail.

Membership in `𝒢(γ^Q)` is what "Markov field for `Q`" means in Georgii §11. The general
implication `𝒢(γ^Q) ⊆ {μ | IsMarkovField μ}` is not formalised here: it needs
`DependsOn (γ^Q_{]i,k[}(·, A)) {i, k}` for every `A ∈ 𝓕_{]i,k[}`, and only the one-site case
`dependsOn_transferSpecification_Ioo_preimage_singleton`
(`GibbsMeasure/Model/BoundaryLawLimits.lean`) is available.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov.SpitzerCox

variable {p : ℝ}

/-! ## `U` is a function of the past, `V` a function of the future -/

/-- `U = lim_{i → -∞} σ_i p^{-i}` is measurable for the σ-algebra `𝓕_{]-∞,0]}` of the coordinates
at the sites `≤ 0`. -/
lemma measurable_cylinderEvents_Iic_limAtBot (p : ℝ) :
    Measurable[cylinderEvents (X := fun _ : ℤ ↦ ℕ) (Set.Iic 0)] (limAtBot p) :=
  continuous_real_toNNReal.measurable.comp
    (@Measurable.limsup ℝ (ℤ → ℕ) _ _ _ (cylinderEvents (Set.Iic 0)) _ _ _ _ fun n ↦
      (measurable_of_countable fun k : ℕ ↦ (k : ℝ) * p ^ n).comp
        (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ ℕ)
          (show -(n : ℤ) ∈ Set.Iic 0 by simp)))

/-- `V = lim_{i → ∞} σ_i p^i` is measurable for the σ-algebra `𝓕_{[0,∞[}` of the coordinates at
the sites `≥ 0`. -/
lemma measurable_cylinderEvents_Ici_limAtTop (p : ℝ) :
    Measurable[cylinderEvents (X := fun _ : ℤ ↦ ℕ) (Set.Ici 0)] (limAtTop p) :=
  continuous_real_toNNReal.measurable.comp
    (@Measurable.limsup ℝ (ℤ → ℕ) _ _ _ (cylinderEvents (Set.Ici 0)) _ _ _ _ fun n ↦
      (measurable_of_countable fun k : ℕ ↦ (k : ℝ) * p ^ n).comp
        (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ ℕ)
          (show (n : ℤ) ∈ Set.Ici 0 by simp)))

/-! ## The law of `(U, V)` jointly with an event -/

/-- Under `μ^{u,v}` the pair `(U, V)` is almost surely `(u, v)`, so `{(U, V) ∈ S} ∩ A` has
probability `μ^{u,v}(A)` if `(u, v) ∈ S` and `0` otherwise. -/
lemma chainFamily_limPair_preimage_inter (hp0 : 0 < p) (hp1 : p < 1) (t : ℝ≥0 × ℝ≥0)
    (S : Set (ℝ≥0 × ℝ≥0)) (A : Set (ℤ → ℕ)) :
    chainFamily hp0 hp1 t (limPair p ⁻¹' S ∩ A)
      = S.indicator (fun s ↦ chainFamily hp0 hp1 s A) t := by
  have hae : ∀ᵐ ω ∂(chainFamily hp0 hp1 t), limPair p ω = t := by
    have h := limPair_ae_chain hp0 hp1 t.1.coe_nonneg t.2.coe_nonneg
    simp only [Real.toNNReal_coe, Prod.mk.eta] at h
    exact h
  have hnull : chainFamily hp0 hp1 t {ω | ¬ limPair p ω = t} = 0 := ae_iff.1 hae
  by_cases hS : t ∈ S
  · rw [Set.indicator_of_mem hS, Set.inter_comm]
    refine measure_inter_conull (measure_mono_null ?_ hnull)
    intro ω hω h
    exact hω (by rw [Set.mem_preimage, h]; exact hS)
  · rw [Set.indicator_of_notMem hS]
    refine measure_mono_null ?_ hnull
    intro ω hω h
    exact hS (by rw [← h]; exact hω.1)

/-- **The law of `(U, V)` jointly with an event, under a Gibbs measure.** For `μ ∈ 𝒢(Q)`,
`μ({(U, V) ∈ S} ∩ A) = ∫_S μ^{u,v}(A) m(du, dv)`, `m = limitLaw p μ` the law of `(U, V)`. -/
theorem measure_limPair_preimage_inter (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)))
    {S : Set (ℝ≥0 × ℝ≥0)} (hS : MeasurableSet S) {A : Set (ℤ → ℕ)} (hA : MeasurableSet A) :
    μ (limPair p ⁻¹' S ∩ A) = ∫⁻ t in S, chainFamily hp0 hp1 t A ∂(limitLaw p μ) := by
  rw [measure_eq_lintegral_chainFamily hp0 hp1 hμ ((measurable_limPair p hS).inter hA)]
  simp_rw [chainFamily_limPair_preimage_inter hp0 hp1 _ S A]
  exact lintegral_indicator hS _

/-! ## Georgii's `m̄`: the law of `(U, V)` on the event `{σ_0 = 0}` -/

/-- The weight `e^{-(1+u)(1+v)} = μ^{u,v}(σ_0 = 0)` (Georgii (11.30) at the site `0`). -/
def zeroWeight (t : ℝ≥0 × ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((1 + (t.1 : ℝ)) * (1 + (t.2 : ℝ)))))

lemma measurable_zeroWeight : Measurable zeroWeight :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.add measurable_fst.coe_nnreal_real).mul
      (measurable_const.add measurable_snd.coe_nnreal_real)).neg)

lemma zeroWeight_pos (t : ℝ≥0 × ℝ≥0) : 0 < zeroWeight t := ENNReal.ofReal_pos.2 (Real.exp_pos _)

lemma zeroWeight_ne_top (t : ℝ≥0 × ℝ≥0) : zeroWeight t ≠ ⊤ := ENNReal.ofReal_ne_top

lemma zeroWeight_le_one (t : ℝ≥0 × ℝ≥0) : zeroWeight t ≤ 1 :=
  ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by
    have h1 := t.1.coe_nonneg
    have h2 := t.2.coe_nonneg
    nlinarith))

/-- The inverse of the weight `e^{-(1+u)(1+v)}` is `e^{(1+u)(1+v)}`. -/
lemma zeroWeight_inv (t : ℝ≥0 × ℝ≥0) :
    (zeroWeight t)⁻¹ = ENNReal.ofReal (Real.exp ((1 + (t.1 : ℝ)) * (1 + (t.2 : ℝ)))) := by
  rw [zeroWeight, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), Real.exp_neg, inv_inv]

/-- `μ^{u,v}(σ_0 = 0) = e^{-(1+u)(1+v)}`: Georgii (11.30) at the site `0`. -/
lemma chainFamily_preimage_zero (hp0 : 0 < p) (hp1 : p < 1) (t : ℝ≥0 × ℝ≥0) :
    chainFamily hp0 hp1 t ((fun ω : ℤ → ℕ ↦ ω 0) ⁻¹' {0}) = zeroWeight t := by
  rw [chainFamily, chain_preimage_singleton hp0 hp1 _ _ 0 0, poissonWeight_zero, zeroWeight]
  simp

/-- **Georgii's `m̄(du, dv) = e^{-(1+u)(1+v)} m(du, dv)`**, `m = limitLaw p μ`: the law of `(U, V)`
under `μ` on the event `{σ_0 = 0}` (`limitLawZero_apply`). -/
abbrev limitLawZero (p : ℝ) (μ : Measure (ℤ → ℕ)) : Measure (ℝ≥0 × ℝ≥0) :=
  (limitLaw p μ).withDensity zeroWeight

instance isFiniteMeasure_limitLawZero (p : ℝ) (μ : Measure (ℤ → ℕ)) [IsProbabilityMeasure μ] :
    IsFiniteMeasure (limitLawZero p μ) :=
  isFiniteMeasure_withDensity (ne_top_of_le_ne_top (measure_ne_top (limitLaw p μ) univ)
    ((lintegral_mono fun t ↦ zeroWeight_le_one t).trans_eq lintegral_one))

/-- `m̄(S) = μ((U, V) ∈ S, σ_0 = 0)`. -/
theorem limitLawZero_apply (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)))
    {S : Set (ℝ≥0 × ℝ≥0)} (hS : MeasurableSet S) :
    limitLawZero p μ S = μ (limPair p ⁻¹' S ∩ (fun ω : ℤ → ℕ ↦ ω 0) ⁻¹' {0}) := by
  rw [limitLawZero, withDensity_apply _ hS, measure_limPair_preimage_inter hp0 hp1 hμ hS
    (measurable_pi_apply 0 (measurableSet_singleton 0))]
  exact setLIntegral_congr_fun hS fun t _ ↦ (chainFamily_preimage_zero hp0 hp1 t).symm

/-- `m̄(univ) = μ(σ_0 = 0)`. -/
lemma limitLawZero_univ (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1))) :
    limitLawZero p μ univ = μ ((fun ω : ℤ → ℕ ↦ ω 0) ⁻¹' {0}) := by
  rw [limitLawZero_apply hp0 hp1 hμ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]

/-- `m̄(univ) = μ(σ_0 = 0) > 0`: a Gibbs measure for the positive matrix `Q` charges every
cylinder. -/
lemma limitLawZero_univ_ne_zero (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1))) :
    limitLawZero p μ univ ≠ 0 := by
  rw [limitLawZero_univ hp0 hp1 hμ]
  have := measure_intervalCylinder_pos_of_isGibbsMeasure (isTransferMatrix hp0 hp1) hμ.2 0 0
    (fun _ ↦ 0)
  rw [intervalCylinder_self] at this
  exact this.ne'

/-- `m = e^{(1+u)(1+v)} m̄`: the density defining `m̄` inverts. -/
lemma limitLaw_eq_withDensity_limitLawZero (p : ℝ) (μ : Measure (ℤ → ℕ)) :
    limitLaw p μ = (limitLawZero p μ).withDensity fun t ↦
      ENNReal.ofReal (Real.exp ((1 + (t.1 : ℝ)) * (1 + (t.2 : ℝ)))) := by
  simp_rw [← zeroWeight_inv]
  exact (withDensity_inv_same measurable_zeroWeight (ae_of_all _ fun t ↦ (zeroWeight_pos t).ne')
    (ae_of_all _ fun t ↦ zeroWeight_ne_top t)).symm

/-! ## For a Markov chain, `m̄` is a product measure -/

/-- **Georgii's computation in (a) ⇒ (c).** For a Markov chain `μ ∈ 𝒢(Q)`,
`m̄(A × B) m̄(univ) = m̄(A × univ) m̄(univ × B)`: `{U ∈ A}` is an event of the past `𝓕_{]-∞,0]}`,
`{V ∈ B}` one of the future `𝓕_{[0,∞[}`, and for the measure (11.10) representing `μ` (Theorem
(11.9)(b)) the two are conditionally independent given `σ_0`
(`IsBoundaryLaw.measure_inter_inter_preimage_mul`). -/
theorem limitLawZero_prod_mul (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)))
    {P : ℤ → Kernel ℕ ℕ} [∀ i, IsMarkovKernel (P i)] (hP : IsMarkovChain P μ)
    {A B : Set ℝ≥0} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    limitLawZero p μ (A ×ˢ B) * limitLawZero p μ univ
      = limitLawZero p μ (A ×ˢ univ) * limitLawZero p μ (univ ×ˢ B) := by
  obtain ⟨ℓ, r, hbl, hμeq, -⟩ :=
    hP.exists_isBoundaryLaw_eq_boundaryLawMeasure (isTransferMatrix hp0 hp1) hμ.2
  rw [limitLawZero_apply hp0 hp1 hμ (hA.prod hB), limitLawZero_univ hp0 hp1 hμ,
    limitLawZero_apply hp0 hp1 hμ (hA.prod MeasurableSet.univ),
    limitLawZero_apply hp0 hp1 hμ (MeasurableSet.univ.prod hB)]
  have h1 : limPair p ⁻¹' (A ×ˢ B) = limAtBot p ⁻¹' A ∩ limAtTop p ⁻¹' B := by
    ext ω
    simp only [limPair, Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
  have h2 : limPair p ⁻¹' (A ×ˢ univ) = limAtBot p ⁻¹' A := by
    ext ω
    simp only [limPair, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  have h3 : limPair p ⁻¹' (univ ×ˢ B) = limAtTop p ⁻¹' B := by
    ext ω
    simp only [limPair, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
  rw [h1, h2, h3, hμeq]
  exact hbl.measure_inter_inter_preimage_mul 0 0 (measurable_cylinderEvents_Iic_limAtBot p hA)
    (measurable_cylinderEvents_Ici_limAtTop p hB)

/-- **For a Markov chain `μ ∈ 𝒢(Q)`, Georgii's `m̄` is the product of its two marginals**, up to
the total mass: `m̄(univ) m̄ = m̄₁ ⊗ m̄₂`. -/
theorem smul_limitLawZero_eq_prod (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)))
    {P : ℤ → Kernel ℕ ℕ} [∀ i, IsMarkovKernel (P i)] (hP : IsMarkovChain P μ) :
    limitLawZero p μ univ • limitLawZero p μ
      = (limitLawZero p μ).fst.prod (limitLawZero p μ).snd := by
  symm
  refine Measure.prod_eq fun A B hA hB ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.fst_apply hA, Measure.snd_apply hB,
    ← Set.prod_univ, ← Set.univ_prod, mul_comm]
  exact limitLawZero_prod_mul hp0 hp1 hμ hP hA hB

/-! ## (a) ⇒ (c) -/

/-- The weight `e^{uv}` of Georgii's representation (11.33)(c). -/
def expWeight (t : ℝ≥0 × ℝ≥0) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((t.1 : ℝ) * (t.2 : ℝ)))

lemma measurable_expWeight : Measurable expWeight :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_fst.coe_nnreal_real.mul measurable_snd.coe_nnreal_real))

lemma expWeight_pos (t : ℝ≥0 × ℝ≥0) : 0 < expWeight t := ENNReal.ofReal_pos.2 (Real.exp_pos _)

lemma expWeight_ne_top (t : ℝ≥0 × ℝ≥0) : expWeight t ≠ ⊤ := ENNReal.ofReal_ne_top

/-- `e^{uv} e^{-uv} = 1` in `ℝ≥0∞`. -/
lemma expWeight_mul_ofReal_exp_neg (t : ℝ≥0 × ℝ≥0) :
    expWeight t * ENNReal.ofReal (Real.exp (-((t.1 : ℝ) * (t.2 : ℝ)))) = 1 := by
  rw [expWeight, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, ENNReal.ofReal_one]

/-- `e^{1+u} e^{v} e^{uv} = e^{(1+u)(1+v)}`. -/
lemma ofReal_exp_mul_ofReal_exp_mul_expWeight (t : ℝ≥0 × ℝ≥0) :
    ENNReal.ofReal (Real.exp (1 + (t.1 : ℝ))) * ENNReal.ofReal (Real.exp (t.2 : ℝ))
        * expWeight t
      = ENNReal.ofReal (Real.exp ((1 + (t.1 : ℝ)) * (1 + (t.2 : ℝ)))) := by
  rw [expWeight, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- **Georgii Corollary (11.33), (a) ⇒ (c).** A Markov chain `μ ∈ 𝒢(Q)` is
`μ = ∫ m₁(du) ∫ m₂(dv) e^{uv} μ^{u,v}` for finite measures `m₁, m₂` on `[0, ∞[`: with
`m̄(du, dv) = e^{-(1+u)(1+v)} m(du, dv)` a product `m̄₁ ⊗ m̄₂ / m̄(univ)`
(`smul_limitLawZero_eq_prod`), take `m₁ = e^{1+u} m̄₁` and `m₂ = e^{v} m̄₂ / m̄(univ)`. -/
theorem exists_prod_of_isMarkovChain (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)))
    {P : ℤ → Kernel ℕ ℕ} [∀ i, IsMarkovKernel (P i)] (hP : IsMarkovChain P μ) :
    ∃ (m₁ m₂ : Measure ℝ≥0), IsFiniteMeasure m₁ ∧ IsFiniteMeasure m₂ ∧
      μ = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1) := by
  have hZ0 : limitLawZero p μ univ ≠ 0 := limitLawZero_univ_ne_zero hp0 hp1 hμ
  have hZt : limitLawZero p μ univ ≠ ⊤ := measure_ne_top _ _
  have hf₁m : Measurable fun u : ℝ≥0 ↦ ENNReal.ofReal (Real.exp (1 + (u : ℝ))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.add measurable_id.coe_nnreal_real))
  have hf₂m : Measurable fun v : ℝ≥0 ↦ ENNReal.ofReal (Real.exp (v : ℝ)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_id.coe_nnreal_real)
  -- the two factors have finite mass: `e^{1+u} e^{-(1+u)(1+v)} ≤ 1` and `e^{v} e^{-(1+u)(1+v)} ≤ 1`
  have hb₁ : ∫⁻ u, ENNReal.ofReal (Real.exp (1 + (u : ℝ))) ∂(limitLawZero p μ).fst ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top (limitLaw p μ) univ) ?_
    rw [Measure.fst, lintegral_map hf₁m measurable_fst, limitLawZero,
      lintegral_withDensity_eq_lintegral_mul _ measurable_zeroWeight
        (g := fun t : ℝ≥0 × ℝ≥0 ↦ ENNReal.ofReal (Real.exp (1 + (t.1 : ℝ))))
        (hf₁m.comp measurable_fst), ← lintegral_one]
    refine lintegral_mono fun t ↦ ?_
    simp only [Pi.mul_apply, zeroWeight]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
    have h1 := t.1.coe_nonneg
    have h2 := t.2.coe_nonneg
    nlinarith
  have hb₂ : ∫⁻ v, ENNReal.ofReal (Real.exp (v : ℝ)) ∂(limitLawZero p μ).snd ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top (limitLaw p μ) univ) ?_
    rw [Measure.snd, lintegral_map hf₂m measurable_snd, limitLawZero,
      lintegral_withDensity_eq_lintegral_mul _ measurable_zeroWeight
        (g := fun t : ℝ≥0 × ℝ≥0 ↦ ENNReal.ofReal (Real.exp (t.2 : ℝ)))
        (hf₂m.comp measurable_snd), ← lintegral_one]
    refine lintegral_mono fun t ↦ ?_
    simp only [Pi.mul_apply, zeroWeight]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
    have h1 := t.1.coe_nonneg
    have h2 := t.2.coe_nonneg
    nlinarith
  have hfin₂ : IsFiniteMeasure ((limitLawZero p μ).snd.withDensity
      fun v : ℝ≥0 ↦ ENNReal.ofReal (Real.exp (v : ℝ))) := isFiniteMeasure_withDensity hb₂
  refine ⟨(limitLawZero p μ).fst.withDensity fun u : ℝ≥0 ↦ ENNReal.ofReal (Real.exp (1 + (u : ℝ))),
    (limitLawZero p μ univ)⁻¹ • (limitLawZero p μ).snd.withDensity
      fun v : ℝ≥0 ↦ ENNReal.ofReal (Real.exp (v : ℝ)),
    isFiniteMeasure_withDensity hb₁, Measure.smul_finite _ (ENNReal.inv_ne_top.2 hZ0), ?_⟩
  conv_lhs => rw [← bind_chainFamily_limitLaw hp0 hp1 hμ]
  congr 1
  rw [Measure.prod_smul_right, prod_withDensity hf₁m hf₂m,
    ← smul_limitLawZero_eq_prod hp0 hp1 hμ hP, withDensity_smul_measure,
    withDensity_smul_measure, withDensity_smul_measure, smul_smul,
    ENNReal.inv_mul_cancel hZ0 hZt, one_smul,
    ← withDensity_mul _
      (f := fun z : ℝ≥0 × ℝ≥0 ↦
        ENNReal.ofReal (Real.exp (1 + (z.1 : ℝ))) * ENNReal.ofReal (Real.exp (z.2 : ℝ)))
      ((hf₁m.comp measurable_fst).mul (hf₂m.comp measurable_snd))
      measurable_expWeight, limitLaw_eq_withDensity_limitLawZero]
  congr 1
  funext t
  exact (ofReal_exp_mul_ofReal_exp_mul_expWeight t).symm

/-! ## (c) ⇒ (a): the boundary law `ℓ_i = ∫ ℓ^u_i m₁(du)`, `r_i = ∫ r^v_i m₂(dv)` -/

lemma measurable_entrance_coe (i : ℤ) (x : ℕ) :
    Measurable fun u : ℝ≥0 ↦ entrance p (u : ℝ) i x :=
  ENNReal.measurable_ofReal.comp ((continuous_poissonWeight x).measurable.comp
    (measurable_const.add (measurable_id.coe_nnreal_real.mul measurable_const)))

lemma measurable_ofReal_rightReal_coe (i : ℤ) (x : ℕ) :
    Measurable fun v : ℝ≥0 ↦ ENNReal.ofReal (rightReal p (v : ℝ) i x) :=
  ENNReal.measurable_ofReal.comp
    ((continuous_rightReal i x).measurable.comp measurable_id.coe_nnreal_real)

/-- At `u = 0` Georgii's right vector carries no `e^{-uv}` factor: `r_i = r^v_i`. -/
lemma right_zero_left (p v : ℝ) (i : ℤ) (x : ℕ) :
    right p 0 v i x = ENNReal.ofReal (rightReal p v i x) := by
  simp [right]

/-- Georgii's left vectors in the proof of (c) ⇒ (a): `ℓ_i = ∫ m₁(du) ℓ^u_i`. -/
def leftMixture (p : ℝ) (m₁ : Measure ℝ≥0) (i : ℤ) (x : ℕ) : ℝ≥0∞ :=
  ∫⁻ u, entrance p (u : ℝ) i x ∂m₁

/-- Georgii's right vectors in the proof of (c) ⇒ (a): `r_i = ∫ m₂(dv) r^v_i`. -/
def rightMixture (p : ℝ) (m₂ : Measure ℝ≥0) (i : ℤ) (x : ℕ) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (rightReal p (v : ℝ) i x) ∂m₂

/-- The cylinder probabilities of `μ^{u,v}`, Georgii (11.10) for the boundary law (11.29). -/
lemma chainFamily_intervalCylinder (hp0 : 0 < p) (hp1 : p < 1) (t : ℝ≥0 × ℝ≥0) {a b : ℤ}
    (hab : a ≤ b) (σ : ℤ → ℕ) :
    chainFamily hp0 hp1 t (intervalCylinder a b σ)
      = entrance p t.1 a (σ a) * pathProd (matrix p) a b σ * right p t.1 t.2 b (σ b) :=
  (isBoundaryLaw hp0 hp1 t.1.coe_nonneg t.2.coe_nonneg).boundaryLawMeasure_intervalCylinder hab σ

/-- **The cylinder probabilities of the representation (c).** The weights `e^{uv}` and `e^{-uv}`
cancel, and the cylinder probabilities factor as in (11.10) with the mixtures `ℓ_i`, `r_i`. -/
theorem bind_chainFamily_intervalCylinder (hp0 : 0 < p) (hp1 : p < 1)
    {m₁ m₂ : Measure ℝ≥0} [SFinite m₂] {a b : ℤ} (hab : a ≤ b) (σ : ℤ → ℕ) :
    ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1) (intervalCylinder a b σ)
      = leftMixture p m₁ a (σ a) * pathProd (matrix p) a b σ * rightMixture p m₂ b (σ b) := by
  have hcyl := measurableSet_intervalCylinder a b σ
  rw [Measure.bind_apply hcyl (measurable_chainFamily hp0 hp1).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ measurable_expWeight
      (g := fun t ↦ chainFamily hp0 hp1 t (intervalCylinder a b σ))
      ((Measure.measurable_coe hcyl).comp (measurable_chainFamily hp0 hp1))]
  have hpt : ∀ t : ℝ≥0 × ℝ≥0,
      (expWeight * fun t ↦ chainFamily hp0 hp1 t (intervalCylinder a b σ)) t
        = entrance p (t.1 : ℝ) a (σ a)
          * (pathProd (matrix p) a b σ * ENNReal.ofReal (rightReal p (t.2 : ℝ) b (σ b))) := by
    intro t
    simp only [Pi.mul_apply]
    rw [chainFamily_intervalCylinder hp0 hp1 t hab σ, right,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    calc expWeight t * (entrance p (t.1 : ℝ) a (σ a) * pathProd (matrix p) a b σ
          * (ENNReal.ofReal (Real.exp (-((t.1 : ℝ) * (t.2 : ℝ))))
            * ENNReal.ofReal (rightReal p (t.2 : ℝ) b (σ b))))
        = (expWeight t * ENNReal.ofReal (Real.exp (-((t.1 : ℝ) * (t.2 : ℝ)))))
          * (entrance p (t.1 : ℝ) a (σ a)
            * (pathProd (matrix p) a b σ * ENNReal.ofReal (rightReal p (t.2 : ℝ) b (σ b)))) := by
          ring
      _ = _ := by rw [expWeight_mul_ofReal_exp_neg, one_mul]
  have hprod := lintegral_prod_mul (μ := m₁) (ν := m₂)
    (f := fun u : ℝ≥0 ↦ entrance p (u : ℝ) a (σ a))
    (g := fun v : ℝ≥0 ↦ pathProd (matrix p) a b σ * ENNReal.ofReal (rightReal p (v : ℝ) b (σ b)))
    (measurable_entrance_coe a (σ a)).aemeasurable
    (measurable_const.mul (measurable_ofReal_rightReal_coe b (σ b))).aemeasurable
  rw [lintegral_congr hpt, hprod, lintegral_const_mul _ (measurable_ofReal_rightReal_coe b (σ b))]
  simp only [leftMixture, rightMixture]
  ring

/-- `∑_x ℓ^u_i(x) r^v_i(x) = e^{uv}`: the normalisation `ℓ^u_i (e^{-uv} r^v_i) = 1` of Georgii's
boundary law (11.29), without the factor `e^{-uv}`. -/
lemma tsum_entrance_mul_ofReal_rightReal (hp0 : 0 < p) (hp1 : p < 1) (i : ℤ) (t : ℝ≥0 × ℝ≥0) :
    ∑' x : ℕ, entrance p (t.1 : ℝ) i x * ENNReal.ofReal (rightReal p (t.2 : ℝ) i x)
      = expWeight t := by
  have h1 := (isBoundaryLaw hp0 hp1 t.1.coe_nonneg t.2.coe_nonneg).tsum_left_mul_right i
  have h2 : ∀ x : ℕ, entrance p (t.1 : ℝ) i x * right p (t.1 : ℝ) (t.2 : ℝ) i x
      = ENNReal.ofReal (Real.exp (-((t.1 : ℝ) * (t.2 : ℝ))))
        * (entrance p (t.1 : ℝ) i x * ENNReal.ofReal (rightReal p (t.2 : ℝ) i x)) := by
    intro x
    rw [right, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  simp_rw [h2] at h1
  rw [ENNReal.tsum_mul_left] at h1
  calc ∑' x : ℕ, entrance p (t.1 : ℝ) i x * ENNReal.ofReal (rightReal p (t.2 : ℝ) i x)
      = (expWeight t * ENNReal.ofReal (Real.exp (-((t.1 : ℝ) * (t.2 : ℝ)))))
        * ∑' x : ℕ, entrance p (t.1 : ℝ) i x * ENNReal.ofReal (rightReal p (t.2 : ℝ) i x) := by
        rw [expWeight_mul_ofReal_exp_neg, one_mul]
    _ = expWeight t := by rw [mul_assoc, h1, mul_one]

/-- The normalisation `∑_x ℓ_i(x) r_i(x) = ∫ e^{uv} d(m₁ ⊗ m₂)` of the mixtures. -/
lemma tsum_leftMixture_mul_rightMixture (hp0 : 0 < p) (hp1 : p < 1) (m₁ m₂ : Measure ℝ≥0)
    [SFinite m₂] (i : ℤ) :
    ∑' x : ℕ, leftMixture p m₁ i x * rightMixture p m₂ i x = ∫⁻ t, expWeight t ∂(m₁.prod m₂) := by
  calc ∑' x : ℕ, leftMixture p m₁ i x * rightMixture p m₂ i x
      = ∑' x : ℕ, ∫⁻ t, entrance p (t.1 : ℝ) i x * ENNReal.ofReal (rightReal p (t.2 : ℝ) i x)
          ∂(m₁.prod m₂) := by
        refine tsum_congr fun x ↦ ?_
        exact (lintegral_prod_mul (measurable_entrance_coe i x).aemeasurable
          (measurable_ofReal_rightReal_coe i x).aemeasurable).symm
    _ = ∫⁻ t, ∑' x : ℕ, entrance p (t.1 : ℝ) i x * ENNReal.ofReal (rightReal p (t.2 : ℝ) i x)
          ∂(m₁.prod m₂) :=
        (lintegral_tsum fun x ↦ (((measurable_entrance_coe i x).comp measurable_fst).mul
          ((measurable_ofReal_rightReal_coe i x).comp measurable_snd)).aemeasurable).symm
    _ = ∫⁻ t, expWeight t ∂(m₁.prod m₂) :=
        lintegral_congr fun t ↦ tsum_entrance_mul_ofReal_rightReal hp0 hp1 i t

/-- `ℓ_i Q = ℓ_{i+1}` for the mixtures, from `ℓ^u_i Q = ℓ^u_{i+1}` (Georgii (11.29)). -/
lemma tsum_leftMixture_mul (hp0 : 0 < p) (hp1 : p < 1) (m₁ : Measure ℝ≥0) (i : ℤ) (y : ℕ) :
    ∑' x : ℕ, leftMixture p m₁ i x * matrix p x y = leftMixture p m₁ (i + 1) y := by
  calc ∑' x : ℕ, leftMixture p m₁ i x * matrix p x y
      = ∑' x : ℕ, ∫⁻ u, entrance p (u : ℝ) i x * matrix p x y ∂m₁ := by
        refine tsum_congr fun x ↦ ?_
        rw [leftMixture, lintegral_mul_const _ (measurable_entrance_coe i x)]
    _ = ∫⁻ u, ∑' x : ℕ, entrance p (u : ℝ) i x * matrix p x y ∂m₁ :=
        (lintegral_tsum fun x ↦ ((measurable_entrance_coe i x).mul_const _).aemeasurable).symm
    _ = leftMixture p m₁ (i + 1) y :=
        lintegral_congr fun u ↦ (isEntranceLaw hp0 hp1 u.coe_nonneg).step i y

/-- `Q r_i = r_{i-1}` for the mixtures, from `Q r^v_i = r^v_{i-1}` (Georgii (11.29)). -/
lemma tsum_matrix_mul_rightMixture (hp0 : 0 < p) (hp1 : p < 1) (m₂ : Measure ℝ≥0) (i : ℤ)
    (x : ℕ) :
    ∑' y : ℕ, matrix p x y * rightMixture p m₂ i y = rightMixture p m₂ (i - 1) x := by
  calc ∑' y : ℕ, matrix p x y * rightMixture p m₂ i y
      = ∑' y : ℕ, ∫⁻ v, matrix p x y * ENNReal.ofReal (rightReal p (v : ℝ) i y) ∂m₂ := by
        refine tsum_congr fun y ↦ ?_
        rw [rightMixture, lintegral_const_mul _ (measurable_ofReal_rightReal_coe i y)]
    _ = ∫⁻ v, ∑' y : ℕ, matrix p x y * ENNReal.ofReal (rightReal p (v : ℝ) i y) ∂m₂ :=
        (lintegral_tsum fun y ↦
          ((measurable_ofReal_rightReal_coe i y).const_mul _).aemeasurable).symm
    _ = rightMixture p m₂ (i - 1) x := by
        refine lintegral_congr fun v ↦ ?_
        have h := (isBoundaryLaw hp0 hp1 (le_refl (0 : ℝ)) v.coe_nonneg).tsum_mul_right i x
        simp_rw [right_zero_left] at h
        exact h

/-- **The mixtures form a boundary law** for `Q` as soon as `m₁, m₂ ≠ 0` and
`∫ e^{uv} d(m₁ ⊗ m₂) = 1`; the latter is the normalisation `μ(univ) = 1` of (c). -/
theorem isBoundaryLaw_mixture (hp0 : 0 < p) (hp1 : p < 1) {m₁ m₂ : Measure ℝ≥0} [SFinite m₂]
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hmass : ∫⁻ t, expWeight t ∂(m₁.prod m₂) = 1) :
    IsBoundaryLaw (matrix p) (leftMixture p m₁) (rightMixture p m₂) := by
  have hℓr : ∀ i, ∑' x : ℕ, leftMixture p m₁ i x * rightMixture p m₂ i x = 1 := fun i ↦ by
    rw [tsum_leftMixture_mul_rightMixture hp0 hp1 m₁ m₂ i, hmass]
  have hℓpos : ∀ i x, 0 < leftMixture p m₁ i x := fun i x ↦ by
    rw [leftMixture, lintegral_pos_iff_support (measurable_entrance_coe i x)]
    have hsupp : Function.support (fun u : ℝ≥0 ↦ entrance p (u : ℝ) i x) = univ :=
      Set.eq_univ_of_forall fun u ↦
        (ENNReal.ofReal_pos.2 (poissonWeight_pos (rate_pos hp0 u.coe_nonneg i) x)).ne'
    rw [hsupp]
    exact Measure.measure_univ_pos.2 hm₁
  have hrpos : ∀ i x, 0 < rightMixture p m₂ i x := fun i x ↦ by
    rw [rightMixture, lintegral_pos_iff_support (measurable_ofReal_rightReal_coe i x)]
    have hsupp : Function.support (fun v : ℝ≥0 ↦ ENNReal.ofReal (rightReal p (v : ℝ) i x))
        = univ :=
      Set.eq_univ_of_forall fun v ↦
        (ENNReal.ofReal_pos.2 (rightReal_pos hp0 v.coe_nonneg i x)).ne'
    rw [hsupp]
    exact Measure.measure_univ_pos.2 hm₂
  have hle : ∀ i x, leftMixture p m₁ i x * rightMixture p m₂ i x ≤ 1 := fun i x ↦
    (hℓr i) ▸ ENNReal.le_tsum x
  refine IsBoundaryLaw.of_tsum hℓpos (fun i x ↦ ?_) hrpos (fun i x ↦ ?_)
    (tsum_leftMixture_mul hp0 hp1 m₁) (tsum_matrix_mul_rightMixture hp0 hp1 m₂) hℓr
  · intro htop
    have := hle i x
    rw [htop, ENNReal.top_mul (hrpos i x).ne'] at this
    exact absurd this (by simp)
  · intro htop
    have := hle i x
    rw [htop, ENNReal.mul_top (hℓpos i x).ne'] at this
    exact absurd this (by simp)

/-- `e^{uv} ≥ 1` on `[0, ∞[²`: the density of Georgii's representation (11.33)(c) is at least
one, which is what forces the "suitable measures" `m₁, m₂` to be finite. -/
lemma one_le_expWeight (t : ℝ≥0 × ℝ≥0) : 1 ≤ expWeight t :=
  ENNReal.one_le_ofReal.2 (Real.one_le_exp (mul_nonneg t.1.coe_nonneg t.2.coe_nonneg))

/-- **The normalisation of Georgii's representation (11.33)(c).** If
`μ = ∫ m₁(du) ∫ m₂(dv) e^{uv} μ^{u,v}` is a probability measure then `∫ e^{uv} d(m₁ ⊗ m₂) = 1`,
because every `μ^{u,v}` is a probability measure. No finiteness of `m₁, m₂` is used. -/
lemma lintegral_expWeight_eq_one (hp0 : 0 < p) (hp1 : p < 1) {μ : Measure (ℤ → ℕ)}
    [IsProbabilityMeasure μ] {m₁ m₂ : Measure ℝ≥0}
    (h : μ = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1)) :
    ∫⁻ t, expWeight t ∂(m₁.prod m₂) = 1 := by
  have hμ1 : μ univ = 1 := measure_univ
  rw [h, Measure.bind_apply MeasurableSet.univ
    (measurable_chainFamily hp0 hp1).aemeasurable] at hμ1
  simp only [measure_univ] at hμ1
  rwa [lintegral_one, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hμ1

/-- **Georgii's "suitable measures" in (11.33)(c) are automatically finite.** Georgii states (c)
for "suitable measures `m₁, m₂` on `[0, ∞[`"; finiteness is not an extra requirement but a
consequence. Indeed `e^{uv} ≥ 1` there (`one_le_expWeight`), so
`(m₁ ⊗ m₂)([0, ∞[²) ≤ ∫ e^{uv} d(m₁ ⊗ m₂) = 1`; and `m₁ ⊗ m₂ ≠ 0`, since otherwise that integral
would vanish instead of being `1`. Hence `m₁([0, ∞[) · m₂([0, ∞[) ≤ 1` with both factors
non-zero, and neither factor can be infinite. -/
theorem isFiniteMeasure_of_bind_chainFamily_eq (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)} [IsProbabilityMeasure μ] {m₁ m₂ : Measure ℝ≥0} [SFinite m₂]
    (h : μ = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1)) :
    IsFiniteMeasure m₁ ∧ IsFiniteMeasure m₂ := by
  have hmass := lintegral_expWeight_eq_one hp0 hp1 h
  have hprod : (m₁.prod m₂) univ = m₁ univ * m₂ univ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
  have hle : (m₁.prod m₂) univ ≤ 1 :=
    calc (m₁.prod m₂) univ = ∫⁻ _, 1 ∂(m₁.prod m₂) := lintegral_one.symm
      _ ≤ ∫⁻ t, expWeight t ∂(m₁.prod m₂) := lintegral_mono one_le_expWeight
      _ = 1 := hmass
  have hne : (m₁.prod m₂) univ ≠ 0 := fun h0 ↦ by
    rw [Measure.measure_univ_eq_zero.1 h0, lintegral_zero_measure] at hmass
    exact zero_ne_one hmass
  rw [hprod] at hle hne
  refine ⟨⟨lt_top_iff_ne_top.2 fun htop ↦ ?_⟩, ⟨lt_top_iff_ne_top.2 fun htop ↦ ?_⟩⟩
  · rw [htop, ENNReal.top_mul (right_ne_zero_of_mul hne)] at hle
    simp at hle
  · rw [htop, ENNReal.mul_top (left_ne_zero_of_mul hne)] at hle
    simp at hle

/-- **Georgii Corollary (11.33), (c) ⇒ (a).** A measure of the form
`μ = ∫ m₁(du) ∫ m₂(dv) e^{uv} μ^{u,v}` is a Markov chain: it is the measure (11.10) of the boundary
law `ℓ_i = ∫ ℓ^u_i m₁(du)`, `r_i = ∫ r^v_i m₂(dv)`, and Theorem (11.9)(a) applies. Only
`s`-finiteness of `m₁`, `m₂` is used. -/
theorem exists_isMarkovChain_of_prod (hp0 : 0 < p) (hp1 : p < 1) {μ : Measure (ℤ → ℕ)}
    [IsProbabilityMeasure μ] {m₁ m₂ : Measure ℝ≥0} [SFinite m₁] [SFinite m₂]
    (h : μ = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1)) :
    ∃ P : ℤ → Kernel ℕ ℕ, (∀ i, IsMarkovKernel (P i)) ∧ IsMarkovChain P μ := by
  have hμ1 : μ univ = 1 := measure_univ
  have hm₁ : m₁ ≠ 0 := by
    rintro rfl
    rw [h, Measure.zero_prod] at hμ1
    simp at hμ1
  have hm₂ : m₂ ≠ 0 := by
    rintro rfl
    rw [h, Measure.prod_zero] at hμ1
    simp at hμ1
  have hmass : ∫⁻ t, expWeight t ∂(m₁.prod m₂) = 1 := lintegral_expWeight_eq_one hp0 hp1 h
  have hbl := isBoundaryLaw_mixture hp0 hp1 hm₁ hm₂ hmass
  have hμeq : μ = boundaryLawMeasure hbl :=
    hbl.eq_boundaryLawMeasure_of_forall_intervalCylinder fun a b hab σ ↦ by
      rw [h, bind_chainFamily_intervalCylinder hp0 hp1 hab σ]
  refine ⟨fun i ↦ Kernel.ofMatrix (transitionMatrix (matrix p) (rightMixture p m₂) i),
    fun i ↦ hbl.isMarkovKernel_ofMatrix_transitionMatrix i, ?_⟩
  rw [hμeq]
  exact hbl.isMarkovChain_boundaryLawMeasure

/-! ## (b) ⇔ (c): Georgii's `μ̃ = e^{-UV} μ / μ(e^{-UV})` -/

/-- The exponent `-uv` of Georgii's tilt, as a function on `[0, ∞[²`. -/
def negProd (t : ℝ≥0 × ℝ≥0) : ℝ := -((t.1 : ℝ) * (t.2 : ℝ))

lemma measurable_negProd : Measurable negProd :=
  (measurable_fst.coe_nnreal_real.mul measurable_snd.coe_nnreal_real).neg

lemma negProd_nonpos (t : ℝ≥0 × ℝ≥0) : negProd t ≤ 0 :=
  neg_nonpos.2 (mul_nonneg t.1.coe_nonneg t.2.coe_nonneg)

/-- `e^{-uv} ≤ 1` is integrable for every finite measure on `[0, ∞[²`. -/
lemma integrable_exp_negProd (ν : Measure (ℝ≥0 × ℝ≥0)) [IsFiniteMeasure ν] :
    Integrable (fun t ↦ Real.exp (negProd t)) ν :=
  (integrable_const (1 : ℝ)).mono'
    (Real.measurable_exp.comp measurable_negProd).aestronglyMeasurable
    (ae_of_all _ fun t ↦ by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.2 (negProd_nonpos t))

/-- `e^{-UV} ≤ 1` is integrable for every finite measure on `E^ℤ`. -/
lemma integrable_exp_negProd_comp (μ : Measure (ℤ → ℕ)) [IsFiniteMeasure μ] :
    Integrable (fun ω ↦ Real.exp ((negProd ∘ limPair p) ω)) μ :=
  (integrable_const (1 : ℝ)).mono'
    (Real.measurable_exp.comp (measurable_negProd.comp (measurable_limPair p))).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.2 (negProd_nonpos _))

/-- **The law of `(U, V)` under Georgii's `μ̃`** is the tilt `e^{-uv} m / m(e^{-uv})` of the law
`m` of `(U, V)` under `μ`. -/
theorem map_limPair_tilted (μ : Measure (ℤ → ℕ)) :
    (μ.tilted (negProd ∘ limPair p)).map (limPair p) = (limitLaw p μ).tilted negProd :=
  map_tilted_comp (measurable_limPair p) measurable_negProd

/-- The two marginals of the law of `(U, V)` under `μ̃` are the laws of `U` and of `V`. -/
lemma map_limAtBot_tilted (μ : Measure (ℤ → ℕ)) :
    (μ.tilted (negProd ∘ limPair p)).map (limAtBot p)
      = ((μ.tilted (negProd ∘ limPair p)).map (limPair p)).fst := by
  rw [Measure.fst, Measure.map_map measurable_fst (measurable_limPair p)]
  rfl

lemma map_limAtTop_tilted (μ : Measure (ℤ → ℕ)) :
    (μ.tilted (negProd ∘ limPair p)).map (limAtTop p)
      = ((μ.tilted (negProd ∘ limPair p)).map (limPair p)).snd := by
  rw [Measure.snd, Measure.map_map measurable_snd (measurable_limPair p)]
  rfl

/-- **Georgii Corollary (11.33), (c) ⇒ (b).** If `μ = ∫ m₁(du) ∫ m₂(dv) e^{uv} μ^{u,v}`, then the
law of `(U, V)` under `μ` is `e^{uv} m₁ ⊗ m₂` (by the uniqueness of the representing measure), so
its tilt by `e^{-uv}` is a multiple of `m₁ ⊗ m₂`, a product: `U` and `V` are independent under
`μ̃`. -/
theorem indepFun_tilted_of_prod (hp0 : 0 < p) (hp1 : p < 1) {μ : Measure (ℤ → ℕ)}
    [IsProbabilityMeasure μ] {m₁ m₂ : Measure ℝ≥0} [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    (h : μ = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1)) :
    IndepFun (limAtBot p) (limAtTop p) (μ.tilted (negProd ∘ limPair p)) := by
  have hlaw : limitLaw p μ = (m₁.prod m₂).withDensity expWeight :=
    eq_limitLaw_of_join_map_chainFamily_eq hp0 hp1 h.symm
  have hprob : IsProbabilityMeasure (μ.tilted (negProd ∘ limPair p)) :=
    isProbabilityMeasure_tilted (integrable_exp_negProd_comp μ)
  have hρprob : IsProbabilityMeasure ((μ.tilted (negProd ∘ limPair p)).map (limPair p)) :=
    Measure.isProbabilityMeasure_map (measurable_limPair p).aemeasurable
  set Z : ℝ := ∫ t, Real.exp (negProd t) ∂(limitLaw p μ) with hZ
  have hmeas : Measurable fun t : ℝ≥0 × ℝ≥0 ↦ ENNReal.ofReal (Real.exp (negProd t) / Z) :=
    ((Real.measurable_exp.comp measurable_negProd).div_const _).ennreal_ofReal
  have hρ : (μ.tilted (negProd ∘ limPair p)).map (limPair p)
      = (ENNReal.ofReal Z⁻¹ • m₁).prod m₂ := by
    rw [map_limPair_tilted, Measure.tilted, ← hZ, hlaw,
      ← withDensity_mul _ measurable_expWeight hmeas, Measure.prod_smul_left,
      ← withDensity_const]
    congr 1
    funext t
    simp only [Pi.mul_apply, expWeight, negProd]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_neg, div_eq_mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (Real.exp_pos _).ne', one_mul]
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_limAtBot p).aemeasurable
    (measurable_limAtTop p).aemeasurable, map_limAtBot_tilted, map_limAtTop_tilted]
  change (μ.tilted (negProd ∘ limPair p)).map (limPair p) = _
  exact Measure.eq_fst_prod_snd_of_eq_prod hρ

/-- **Georgii Corollary (11.33), (b) ⇒ (c).** If `U` and `V` are independent under `μ̃`, the law
of `(U, V)` under `μ̃` — the tilt `e^{-uv} m / Z` of the representing measure `m` — is the product
of its marginals `ρ₁ ⊗ ρ₂`; hence `m = Z e^{uv} ρ₁ ⊗ ρ₂` and
`μ = ∫ m(du, dv) μ^{u,v} = ∫ (Z ρ₁)(du) ∫ ρ₂(dv) e^{uv} μ^{u,v}`. -/
theorem exists_prod_of_indepFun_tilted (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)))
    (h : IndepFun (limAtBot p) (limAtTop p) (μ.tilted (negProd ∘ limPair p))) :
    ∃ (m₁ m₂ : Measure ℝ≥0), IsFiniteMeasure m₁ ∧ IsFiniteMeasure m₂ ∧
      μ = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1) := by
  have hprob : IsProbabilityMeasure (μ.tilted (negProd ∘ limPair p)) :=
    isProbabilityMeasure_tilted (integrable_exp_negProd_comp μ)
  set ρ : Measure (ℝ≥0 × ℝ≥0) := (limitLaw p μ).tilted negProd with hρ_def
  have hρprob : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted (integrable_exp_negProd _)
  set Z : ℝ := ∫ t, Real.exp (negProd t) ∂(limitLaw p μ) with hZ
  have hZpos : 0 < Z := integral_exp_pos (integrable_exp_negProd _)
  -- (b): the law of `(U, V)` under `μ̃` is the product of its marginals
  have hρprod : ρ = ρ.fst.prod ρ.snd := by
    rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_limAtBot p).aemeasurable
      (measurable_limAtTop p).aemeasurable] at h
    have h' : (μ.tilted (negProd ∘ limPair p)).map (limPair p)
        = ((μ.tilted (negProd ∘ limPair p)).map (limAtBot p)).prod
          ((μ.tilted (negProd ∘ limPair p)).map (limAtTop p)) := h
    rw [map_limAtBot_tilted, map_limAtTop_tilted, map_limPair_tilted] at h'
    exact h'
  -- undo the tilt: `m = Z e^{uv} ρ`
  have hmeas : Measurable fun t : ℝ≥0 × ℝ≥0 ↦ ENNReal.ofReal (Real.exp (negProd t) / Z) :=
    ((Real.measurable_exp.comp measurable_negProd).div_const _).ennreal_ofReal
  have hinv : limitLaw p μ = ρ.withDensity fun t ↦ ENNReal.ofReal Z * expWeight t := by
    have hdens : ρ = (limitLaw p μ).withDensity
        fun t ↦ ENNReal.ofReal (Real.exp (negProd t) / Z) := by
      rw [hρ_def, Measure.tilted, ← hZ]
    have := withDensity_inv_same (μ := limitLaw p μ) hmeas
      (ae_of_all _ fun t ↦ (ENNReal.ofReal_pos.2 (div_pos (Real.exp_pos _) hZpos)).ne')
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_ne_top)
    rw [← hdens] at this
    rw [← this]
    congr 1
    funext t
    rw [← ENNReal.ofReal_inv_of_pos (div_pos (Real.exp_pos _) hZpos), inv_div, expWeight, negProd,
      Real.exp_neg, div_inv_eq_mul, ENNReal.ofReal_mul hZpos.le]
  refine ⟨ENNReal.ofReal Z • ρ.fst, ρ.snd, Measure.smul_finite _ ENNReal.ofReal_ne_top,
    inferInstance, ?_⟩
  conv_lhs => rw [← bind_chainFamily_limitLaw hp0 hp1 hμ]
  congr 1
  rw [hinv, Measure.prod_smul_left, withDensity_smul_measure,
    ← withDensity_smul _ measurable_expWeight]
  conv_lhs => rw [hρprod]
  rfl

/-! ## Corollary (11.33) -/

/-- **Georgii Corollary (11.33).** For `μ ∈ 𝒢(Q)`, `Q` the Spitzer–Cox matrix (11.26), the
following are equivalent:

(a) `μ` is a Markov chain;
(b) the boundary limits `U`, `V` are independent under `μ̃ = e^{-UV} μ / μ(e^{-UV})`;
(c) `μ = ∫ m₁(du) ∫ m₂(dv) e^{uv} μ^{u,v}` for finite measures `m₁, m₂` on `[0, ∞[`;
(c') the same for merely `s`-finite `m₁, m₂` — Georgii's "suitable measures".

The equivalence of the last two clauses is `isFiniteMeasure_of_bind_chainFamily_eq`: the
finiteness in (c) is not a hypothesis one has to arrange but a consequence of the representation,
so (c') is the form of (c) with the weakest hypotheses and (c) the form with the strongest
conclusions. -/
theorem isMarkovChain_tfae (hp0 : 0 < p) (hp1 : p < 1)
    {μ : Measure (ℤ → ℕ)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1))) :
    [(∃ P : ℤ → Kernel ℕ ℕ, (∀ i, IsMarkovKernel (P i)) ∧ IsMarkovChain P μ),
      IndepFun (limAtBot p) (limAtTop p)
        (μ.tilted fun ω ↦ -((limAtBot p ω : ℝ) * (limAtTop p ω : ℝ))),
      (∃ (m₁ m₂ : Measure ℝ≥0), IsFiniteMeasure m₁ ∧ IsFiniteMeasure m₂ ∧
        μ = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1)),
      (∃ (m₁ m₂ : Measure ℝ≥0), SFinite m₁ ∧ SFinite m₂ ∧
        μ = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1))].TFAE := by
  tfae_have 1 → 3 := by
    rintro ⟨P, hP, hμP⟩
    have : ∀ i, IsMarkovKernel (P i) := hP
    exact exists_prod_of_isMarkovChain hp0 hp1 hμ hμP
  tfae_have 3 → 1 := by
    rintro ⟨m₁, m₂, h₁, h₂, h⟩
    exact exists_isMarkovChain_of_prod hp0 hp1 h
  tfae_have 3 → 4 := by
    rintro ⟨m₁, m₂, h₁, h₂, h⟩
    exact ⟨m₁, m₂, inferInstance, inferInstance, h⟩
  tfae_have 4 → 3 := by
    rintro ⟨m₁, m₂, h₁, h₂, h⟩
    obtain ⟨hf₁, hf₂⟩ := isFiniteMeasure_of_bind_chainFamily_eq hp0 hp1 h
    exact ⟨m₁, m₂, hf₁, hf₂, h⟩
  tfae_have 3 → 2 := by
    rintro ⟨m₁, m₂, h₁, h₂, h⟩
    exact indepFun_tilted_of_prod hp0 hp1 h
  tfae_have 2 → 3 := fun h ↦ exists_prod_of_indepFun_tilted hp0 hp1 hμ h
  tfae_finish

/-! ## The two converses that fail

Georgii reads two counterexamples off Corollary (11.33): *not every Markov chain in `𝒢(Q)` is
extreme* (the converse of Theorem (10.21)) and *not every Markov field for `Q` is a Markov chain*
(the converse of Remark (10.9)(3)). Both witnesses are two-atom mixtures of extreme points.

Membership in `𝒢(γ^Q)` is what "Markov field for `Q`" means in Georgii §11; the general
implication `𝒢(γ^Q) ⊆ {Markov fields}` in the sense of
`MeasureTheory.GibbsMeasure.Markov.IsMarkovField` is *not* available in this tree — it needs
`DependsOn (γ^Q_{]i,k[}(·, A)) {i, k}` for every `A ∈ 𝓕_{]i,k[}`, of which only the one-site case
`dependsOn_transferSpecification_Ioo_preimage_singleton`
(`GibbsMeasure/Model/BoundaryLawLimits.lean`) is proved. The statement below therefore says
"an element of `𝒢(γ^Q)` which is not a Markov chain". -/

/-- `e^{u·0} = 1`: on the line `v = 0` the weight of (11.33)(c) is trivial. -/
@[simp] lemma expWeight_snd_zero (u : ℝ≥0) : expWeight (u, 0) = 1 := by
  simp [expWeight]

/-- **Every `μ^{u,v}` is a Markov chain**, by (11.33)(c) with `m₁ = e^{-uv} δ_u` and `m₂ = δ_v`.
(This is also Georgii (11.29): the boundary law defining `μ^{u,v}` makes it a Markov chain by
Theorem (11.9)(a). The point of deriving it from (11.33) is that it is the extreme case of the
representation, so the failure of the converse of Theorem (10.21) below is not a failure of
(11.33) itself.) -/
theorem chainFamily_isMarkovChain (hp0 : 0 < p) (hp1 : p < 1) (t : ℝ≥0 × ℝ≥0) :
    ∃ P : ℤ → Kernel ℕ ℕ, (∀ i, IsMarkovKernel (P i)) ∧
      IsMarkovChain P (chainFamily hp0 hp1 t) := by
  have hc : ∃ (m₁ m₂ : Measure ℝ≥0), SFinite m₁ ∧ SFinite m₂ ∧
      chainFamily hp0 hp1 t
        = ((m₁.prod m₂).withDensity expWeight).bind (chainFamily hp0 hp1) := by
    refine ⟨ENNReal.ofReal (Real.exp (-((t.1 : ℝ) * (t.2 : ℝ)))) • Measure.dirac t.1,
      Measure.dirac t.2, inferInstance, inferInstance, ?_⟩
    rw [Measure.prod_smul_left, withDensity_smul_measure, Measure.dirac_prod_dirac,
      MeasureTheory.dirac_withDensity' measurable_expWeight, Measure.bind_smul, Measure.bind_smul,
      Measure.dirac_bind (measurable_chainFamily hp0 hp1), smul_smul, expWeight,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  exact ((isMarkovChain_tfae hp0 hp1 (mem_G_chainFamily hp0 hp1 t)).out 4 1).1 hc

/-- A two-atom instance of the representation (11.33)(c) on the line `v = 0`, where the weight
`e^{uv}` is `1`: with `m₁ = a δ_{u₁} + b δ_{u₂}` and `m₂ = δ_0` the mixture is
`a μ^{u₁,0} + b μ^{u₂,0}`. -/
lemma bind_chainFamily_two_point (hp0 : 0 < p) (hp1 : p < 1) (a b : ℝ≥0∞) (u₁ u₂ : ℝ≥0) :
    (((a • Measure.dirac u₁ + b • Measure.dirac u₂).prod
        (Measure.dirac (0 : ℝ≥0))).withDensity expWeight).bind (chainFamily hp0 hp1)
      = a • chainFamily hp0 hp1 (u₁, 0) + b • chainFamily hp0 hp1 (u₂, 0) := by
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left, Measure.dirac_prod_dirac,
    Measure.dirac_prod_dirac, withDensity_add_measure, withDensity_smul_measure,
    withDensity_smul_measure, MeasureTheory.dirac_withDensity' measurable_expWeight,
    MeasureTheory.dirac_withDensity' measurable_expWeight, Measure.bind_add _ _ _
      (measurable_chainFamily hp0 hp1), Measure.bind_smul, Measure.bind_smul, Measure.bind_smul,
    Measure.bind_smul, Measure.dirac_bind (measurable_chainFamily hp0 hp1),
    Measure.dirac_bind (measurable_chainFamily hp0 hp1)]
  simp

/-- A nontrivial convex combination of two *distinct* extreme points `μ^s ≠ μ^t` of `𝒢(Q)` is not
extreme. -/
theorem notMem_extremePoints_half_add_half (hp0 : 0 < p) (hp1 : p < 1) {s t : ℝ≥0 × ℝ≥0}
    (hst : s ≠ t) :
    (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 s + (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 t
      ∉ (G (transferSpecification (matrix p)
        (isTransferMatrix hp0 hp1))).extremePoints ℝ≥0∞ := by
  intro hextreme
  have hopen : (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 s + (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 t
      ∈ openSegment ℝ≥0∞ (chainFamily hp0 hp1 s) (chainFamily hp0 hp1 t) :=
    ⟨(2 : ℝ≥0∞)⁻¹, (2 : ℝ≥0∞)⁻¹, ENNReal.inv_pos.2 (by norm_num), ENNReal.inv_pos.2 (by norm_num),
      ENNReal.inv_two_add_inv_two, rfl⟩
  have heq := (mem_extremePoints_iff_left.1 hextreme).2 _ (mem_G_chainFamily hp0 hp1 s)
    _ (mem_G_chainFamily hp0 hp1 t) hopen
  have heq' := (mem_extremePoints_iff_left.1 hextreme).2 _ (mem_G_chainFamily hp0 hp1 t)
    _ (mem_G_chainFamily hp0 hp1 s) (by rwa [openSegment_symm])
  exact hst (chainFamily_injective hp0 hp1 (heq.trans heq'.symm))

/-- **The converse of Georgii Theorem (10.21) fails.** `½μ^{0,0} + ½μ^{1,0}` is a Markov chain in
`𝒢(Q)` — it satisfies (11.33)(c) with `m₁ = ½δ_0 + ½δ_1` and `m₂ = δ_0`, the weight `e^{uv}` being
`1` on the line `v = 0` — but it is a nontrivial convex combination of the two distinct extreme
points `μ^{0,0} ≠ μ^{1,0}` and hence not extreme. So a Markov chain in `𝒢(γ)` need not be extreme
in `𝒢(γ)`. -/
theorem exists_isMarkovChain_notMem_extremePoints_G (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)),
      (∃ P : ℤ → Kernel ℕ ℕ, (∀ i, IsMarkovKernel (P i)) ∧ IsMarkovChain P μ) ∧
        μ ∉ (G (transferSpecification (matrix p)
          (isTransferMatrix hp0 hp1))).extremePoints ℝ≥0∞ := by
  have hμG : (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 (0, 0) + (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 (1, 0)
      ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)) :=
    add_smul_mem_G (mem_G_chainFamily hp0 hp1 _) (mem_G_chainFamily hp0 hp1 _)
      ENNReal.inv_two_add_inv_two
  have hprob : IsProbabilityMeasure ((2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 (0, 0)
      + (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 (1, 0)) := hμG.1
  refine ⟨_, hμG, ((isMarkovChain_tfae hp0 hp1 hμG).out 4 1).1 ?_,
    notMem_extremePoints_half_add_half hp0 hp1 (by simp)⟩
  exact ⟨(2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1, Measure.dirac 0,
    inferInstance, inferInstance, (bind_chainFamily_two_point hp0 hp1 _ _ 0 1).symm⟩

/-- **The converse of Georgii Remark (10.9)(3) fails.** `½μ^{0,0} + ½μ^{1,1}` belongs to `𝒢(Q)`
but is not a Markov chain: its representing measure is `m = ½δ_{(0,0)} + ½δ_{(1,1)}`, and by the
uniqueness of `m` (`eq_limitLaw_of_join_map_chainFamily_eq`) clause (11.33)(c) would force
`m = (m₁ ⊗ m₂) e^{uv}`. Since `e^{uv} ≥ 1` and `m` gives no mass to `{(1, 0)}`, that would make
`m₁{1} · m₂{0} = 0`; but `m{(0,0)} ≠ 0` and `m{(1,1)} ≠ 0` force `m₂{0} ≠ 0` and `m₁{1} ≠ 0`,
because `(m₁ ⊗ m₂) e^{uv} ≪ m₁ ⊗ m₂`. -/
theorem exists_mem_G_not_isMarkovChain (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ μ ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)),
      ¬ ∃ P : ℤ → Kernel ℕ ℕ, (∀ i, IsMarkovKernel (P i)) ∧ IsMarkovChain P μ := by
  have hμG : (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 (0, 0) + (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 (1, 1)
      ∈ G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)) :=
    add_smul_mem_G (mem_G_chainFamily hp0 hp1 _) (mem_G_chainFamily hp0 hp1 _)
      ENNReal.inv_two_add_inv_two
  have hprob : IsProbabilityMeasure ((2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 (0, 0)
      + (2 : ℝ≥0∞)⁻¹ • chainFamily hp0 hp1 (1, 1)) := hμG.1
  refine ⟨_, hμG, fun hchain ↦ ?_⟩
  obtain ⟨m₁, m₂, hs₁, hs₂, h⟩ := ((isMarkovChain_tfae hp0 hp1 hμG).out 1 4).1 hchain
  have hlaw := eq_limitLaw_of_join_map_chainFamily_eq hp0 hp1 h.symm
  rw [limitLaw_add_smul, limitLaw_chainFamily, limitLaw_chainFamily] at hlaw
  have hmeas : ∀ a b : ℝ≥0, MeasurableSet ((({a} : Set ℝ≥0)) ×ˢ (({b} : Set ℝ≥0))) :=
    fun a b ↦ (measurableSet_singleton a).prod (measurableSet_singleton b)
  have hmono : ∀ a b : ℝ≥0, (m₁.prod m₂) ((({a} : Set ℝ≥0)) ×ˢ (({b} : Set ℝ≥0)))
      ≤ ((m₁.prod m₂).withDensity expWeight) ((({a} : Set ℝ≥0)) ×ˢ (({b} : Set ℝ≥0))) :=
    fun a b ↦ by
      rw [withDensity_apply _ (hmeas a b), ← setLIntegral_one]
      exact lintegral_mono fun t ↦ one_le_expWeight t
  have hcalc : ∀ a b : ℝ≥0,
      ((2 : ℝ≥0∞)⁻¹ • Measure.dirac ((0 : ℝ≥0), (0 : ℝ≥0))
        + (2 : ℝ≥0∞)⁻¹ • Measure.dirac ((1 : ℝ≥0), (1 : ℝ≥0)))
          ((({a} : Set ℝ≥0)) ×ˢ (({b} : Set ℝ≥0)))
      = ((m₁.prod m₂).withDensity expWeight) ((({a} : Set ℝ≥0)) ×ˢ (({b} : Set ℝ≥0))) :=
    fun a b ↦ by rw [hlaw]
  -- the "off-diagonal" point `(1, 0)` carries no mass, so `m₁{1} · m₂{0} = 0`
  have hz : ((2 : ℝ≥0∞)⁻¹ • Measure.dirac ((0 : ℝ≥0), (0 : ℝ≥0))
      + (2 : ℝ≥0∞)⁻¹ • Measure.dirac ((1 : ℝ≥0), (1 : ℝ≥0)))
        ((({1} : Set ℝ≥0)) ×ˢ (({0} : Set ℝ≥0))) = 0 := by simp
  have h10 : m₁ ({1} : Set ℝ≥0) * m₂ ({0} : Set ℝ≥0) = 0 := by
    rw [← Measure.prod_prod]
    exact le_antisymm ((hmono 1 0).trans_eq ((hcalc 1 0).symm.trans hz)) bot_le
  -- but `(0, 0)` and `(1, 1)` do carry mass, so `m₂{0} ≠ 0` and `m₁{1} ≠ 0`
  have h00 : m₁ ({0} : Set ℝ≥0) * m₂ ({0} : Set ℝ≥0) ≠ 0 := by
    rw [← Measure.prod_prod]
    intro h0
    have hac := (withDensity_absolutelyContinuous (m₁.prod m₂) expWeight) h0
    rw [← hcalc 0 0] at hac
    simp at hac
  have h11 : m₁ ({1} : Set ℝ≥0) * m₂ ({1} : Set ℝ≥0) ≠ 0 := by
    rw [← Measure.prod_prod]
    intro h0
    have hac := (withDensity_absolutelyContinuous (m₁.prod m₂) expWeight) h0
    rw [← hcalc 1 1] at hac
    simp at hac
  exact mul_ne_zero (left_ne_zero_of_mul h11) (right_ne_zero_of_mul h00) h10

end MeasureTheory.GibbsMeasure.Markov.SpitzerCox

end
