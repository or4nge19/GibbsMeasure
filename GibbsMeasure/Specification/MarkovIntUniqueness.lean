/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.MarkovIntChains
public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix.Recurrence

/-!
# Georgii §10.2 (10.23)–(10.26) and §10.3: uniqueness of the shift-invariant Markov field

## What is proved

* **(10.23)** homogeneity/irreducibility of a Markovian `λ`-modification on `ℤ`:
  `Specification.IsHomogeneousInt`, `Specification.IsIrreducibleInt`, and the propagation of the
  irreducibility bound to an arbitrary site (`marginalDensity_Ioo_ge_of_homogeneous`).
* **(10.26)** Georgii's backward-martingale criterion, in full, at the general hypotheses stated
  in the book: `MeasureTheory.GibbsMeasure.Markov.exists_ae_eq_pair_of_isIrreducibleInt`. Its
  two applications, (10.25) and (10.34), are both instances of this one statement.
* **(10.25)** every `μ ∈ 𝒢_Θ(γ)` is a Markov chain for a kernel `P(x, ·) = p(x, ·) λ`:
  `exists_isMarkovChain_of_measurePreserving_shift` (shift-invariance phrased as
  `MeasurePreserving`, Georgii's `𝒢_Θ`).
* **(10.29)–(10.32)** the `n`-step density `Kernel.densityPow`, the invariant marginal `α = rλ`
  (`stationaryDensity`, `map_eval_eq_withDensity_stationaryDensity`) and
  `r = ν_0(ρ_{{0}} | 𝓕_{{0}})` (`toReal_stationaryDensity_ae_eq_condExp`).
* **(10.33)** positivity of `r` on `{h_N > 0}` for large `N`
  (`mul_le_stationaryDensity_of_irreducibility`).
* **(10.34)** the ergodic theorem for `P`, in full, both parts: `tendsto_lintegral_tvDensity`
  (mean total-variation convergence) and its Fatou-lemma corollary for `α`-almost every `x`.
* **§10.3, (10.36)–(10.37)**: the covariance/mixing bound, assembled from the two-boundary-point
  estimate (10.37) (`measure_inter_pair_le`) via the Markov property
  (`measureReal_inter_sub_le_of_isMarkovOn`, already in the file) and Theorem (10.34), first for
  cylinder events (`eventually_abs_measureReal_inter_sub_le_of_mem_localEvents`, Georgii's literal
  (10.36)) and then for *every* measurable set, by approximating in measure with a cylinder event
  (`eventually_abs_measureReal_inter_sub_le`) — the missing half-page Georgii elides ("Proposition
  (7.9)" needs the asymptotic-independence hypothesis for every measurable set, not just cylinder
  events; `exists_mem_localEvents_measure_symmDiff_lt` supplies the approximation).
* **(10.35)**, both directions:
  - `mem_extremePoints_G_of_measurePreserving_shift`: `𝒢_Θ(γ) ⊆ ex 𝒢(γ)` (Georgii, Theorem (7.9)
    turns the covariance bound into tail-triviality, then Theorem (7.7) turns tail-triviality into
    extremality).
  - `eq_of_isGibbsMeasure_of_measurePreserving_shift`: **`|𝒢_Θ(γ)| ≤ 1`**. Two distinct
    shift-invariant Gibbs measures would make their midpoint a shift-invariant Gibbs measure lying
    in the *open* segment between them; the mixture is Gibbs (`Measure.bind_add`/`bind_smul`) and
    shift-invariant (`Measure.map_add`/`map_smul`), so it is itself extreme by the first bullet —
    but an extreme point cannot be a nontrivial combination of two distinct points, contradiction.

## What is not proved: Examples (10.24)

Georgii's two examples package extra structure into `IsIrreducibleInt`'s witnesses
`(C_N, n(N), h_N)`, and neither closes at the generality of this file without a genuine additional
input:

* **(10.24)(1)** (nearest-neighbour potentials). Georgii takes `ρ = ρ^Φ` the Gibbsian modification
  of a shift-invariant nearest-neighbour potential `Φ` (`Φ_{\{0\}} = 0`, `Φ_A = 0` unless
  `A = \{i, i+1\}`), and shows `sup_ω Z^Φ_{\{0\}}(ω) < ∞` together with
  `sup_{ω_0, ω_1 ∈ C_N} Φ_{\{0,1\}}(ω) < ∞` (for some `C_N ↑ E`) forces irreducibility with
  `n(N) = 1` and `h_N = 1_{C_N} e^{-2c_N}/c`. Formalizing this needs the Gibbsian formula
  `ρ_Λ = e^{-H_Λ}/Z_Λ` from `GibbsMeasure/Potential/NearestNeighbour.lean`; importing it here
  would invert the dependency (`Potential/` sits above `Specification/`), so the instance belongs
  in `Potential/NearestNeighbour.lean`, stated against `IsIrreducibleInt` from this file.
* **(10.24)(2)** (countable-state Markov chains). Georgii takes `E` countable, `λ` *counting*
  measure, `ρ` built from a stochastic matrix `P` via `ρ_{[i,k[} = ∏ P(ω_{j-1},ω_j) / P^{k-i}(ω_i,
  ω_k)`, and cites (Breiman 1968, Ch. 7 — not reproved there either) that an aperiodic irreducible
  `P` satisfies `∀ x y, ∃ n(x,y), ∀ n ≥ n(x,y), P^n(x,y) > 0`; from that fact alone,
  irreducibility of `ρ` follows with `C_N ↑ E` finite, `n(N) = max_{x,y ∈ C_N} n(x,y)`. Two gaps
  remain in this library: (a) `IsIrreducibleInt` requires `[IsProbabilityMeasure ν]`, so counting
  measure on an infinite `E` must first be replaced by an equivalent probability measure with the
  matching Radon–Nikodym adjustment to `ρ` — Georgii's own "without loss `λ ∈ 𝒫(E,𝓔)`" reduction
  from the setup before (10.13), not part of Example (10.24)(2) itself; (b) the aperiodic-implies-
  eventually-positive fact has no Mathlib home yet (`GibbsMeasure/Mathlib/Probability/Kernel/
  CountableMatrix/Recurrence.lean` has irreducibility/recurrence, not periodicity). Given (a) and
  (b), *from* the Breiman fact `IsIrreducibleInt` is an easy corollary; neither (a) nor (b) is
  proved here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology symmDiff

noncomputable section

/-! ## Missing Mathlib

The properness of `ProbabilityTheory.condExpKernel` and the conditionally independent
self-coupling `ν̃` it defines. Intended home: `Mathlib/Probability/Kernel/Condexp.lean`. -/


namespace MeasureTheory

/-- Measurability of `x ↦ ENNReal.ofReal |u x|`. -/
theorem measurable_ofReal_abs {X : Type*} [MeasurableSpace X] {u : X → ℝ} (hu : Measurable u) :
    Measurable fun x ↦ ENNReal.ofReal |u x| :=
  ENNReal.measurable_ofReal.comp (by simpa only [Real.norm_eq_abs] using hu.norm)

/-- Measurability of `x ↦ ENNReal.ofReal |u x - w x|`. -/
theorem measurable_ofReal_abs_sub {X : Type*} [MeasurableSpace X] {u w : X → ℝ}
    (hu : Measurable u) (hw : Measurable w) :
    Measurable fun x ↦ ENNReal.ofReal |u x - w x| :=
  ENNReal.measurable_ofReal.comp (by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hu.sub hw).norm)

/-- The `L¹`-contraction property of the conditional expectation, in `ℝ≥0∞` form.
Intended home: `Mathlib/MeasureTheory/Function/ConditionalExpectation/Real.lean`. -/
theorem lintegral_ofReal_abs_condExp_le {Ω : Type*} {m m0 : MeasurableSpace Ω} {w : Measure Ω}
    (f : Ω → ℝ) :
    ∫⁻ x, ENNReal.ofReal |(w[f | m]) x| ∂w ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂w := by
  simpa only [eLpNorm_one_eq_lintegral_enorm, Real.enorm_eq_ofReal_abs] using
    eLpNorm_condExp_le_eLpNorm (m := m) (μ := w) f le_rfl

/-- A pair of two-sided `ℝ≥0∞` bounds `μ (A ∩ C) ≤ μ A * μ C + D` and `μ A * μ C ≤ μ (A ∩ C) + D`
(with `D` finite) gives the real absolute-value bound `|μ.real (A ∩ C) - μ.real A * μ.real C| ≤
D.toReal`. The two-sided form is what a truncated-subtraction estimate naturally produces; this
converts it to the form used by a covariance/mixing bound. Intended home:
`Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`, next to
`abs_measureReal_sub_le_measureReal_symmDiff`. -/
theorem abs_measureReal_inter_sub_mul_le {X : Type*} {mX : MeasurableSpace X} {w : Measure X}
    [IsFiniteMeasure w] {A C : Set X} {D : ℝ≥0∞} (hD : D ≠ ⊤)
    (h1 : w (A ∩ C) ≤ w A * w C + D) (h2 : w A * w C ≤ w (A ∩ C) + D) :
    |w.real (A ∩ C) - w.real A * w.real C| ≤ D.toReal := by
  have hmul : w.real A * w.real C = (w A * w C).toReal := (ENNReal.toReal_mul).symm
  rw [Measure.real, hmul]
  have hxtop : w (A ∩ C) ≠ ⊤ := measure_ne_top _ _
  have hytop : w A * w C ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hb1 : w (A ∩ C) - w A * w C ≤ D := tsub_le_iff_left.2 h1
  have hb2 : w A * w C - w (A ∩ C) ≤ D := tsub_le_iff_left.2 h2
  rcases le_total (w (A ∩ C)) (w A * w C) with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.2 ((ENNReal.toReal_le_toReal hxtop hytop).2 hle)),
      neg_sub, ← ENNReal.toReal_sub_of_le hle hytop]
    exact ENNReal.toReal_mono hD hb2
  · rw [abs_of_nonneg (sub_nonneg.2 ((ENNReal.toReal_le_toReal hytop hxtop).2 hle)),
      ← ENNReal.toReal_sub_of_le hle hxtop]
    exact ENNReal.toReal_mono hD hb1

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The conditional expectation kernel is **proper**: for an `m`-measurable map `r` into a space
with measurable diagonal, `condExpKernel μ m ω` is `μ`-almost surely concentrated on the fibre
of `r` through `ω`. -/
theorem condExpKernel_ae_ae_eq [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {β : Type*}
    [MeasurableSpace β] [MeasurableEq β] {r : Ω → β} (hr : Measurable[m] r) :
    ∀ᵐ ω ∂μ, ∀ᵐ ζ ∂(condExpKernel μ m ω), r ζ = r ω := by
  classical
  set D : Set (Ω × Ω) := {p | r p.2 = r p.1} with hD_def
  have hrΩ : Measurable r := hr.mono hm le_rfl
  have hD : MeasurableSet[m.prod mΩ] D :=
    measurableSet_eq_fun (β := β) (hrΩ.comp measurable_snd) (hr.comp measurable_fst)
  have hdiag : ((Function.diag : Ω → Ω × Ω) ⁻¹' D) = Set.univ := by
    ext ω; simp [hD_def, Function.diag]
  have hmeas : Measurable[m] fun ω ↦ condExpKernel μ m ω (Prod.mk ω ⁻¹' D) :=
    Kernel.measurable_kernel_prodMk_left hD
  have hcomp : ∫⁻ ω, condExpKernel μ m ω (Prod.mk ω ⁻¹' D) ∂μ = 1 := by
    have hdiagmeas : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
      Measurable.prodMk (measurable_id'' hm) measurable_id
    have h0 : (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) D = 1 := by
      rw [Measure.map_apply hdiagmeas hD, hdiag, measure_univ]
    rw [← compProd_trim_condExpKernel hm, Measure.compProd_apply hD,
      lintegral_trim hm hmeas] at h0
    exact h0
  have hle : ∀ ω, condExpKernel μ m ω (Prod.mk ω ⁻¹' D) ≤ 1 := fun ω ↦ prob_le_one
  have hμ : ∀ᵐ ω ∂μ, condExpKernel μ m ω (Prod.mk ω ⁻¹' D) = 1 := by
    have hmeas' : Measurable fun ω ↦ condExpKernel μ m ω (Prod.mk ω ⁻¹' D) :=
      hmeas.mono hm le_rfl
    have hsub : ∫⁻ ω, (1 - condExpKernel μ m ω (Prod.mk ω ⁻¹' D)) ∂μ = 0 := by
      rw [lintegral_sub hmeas' (by rw [hcomp]; exact ENNReal.one_ne_top)
        (Eventually.of_forall hle), hcomp, lintegral_const, measure_univ, mul_one, tsub_self]
    filter_upwards [(lintegral_eq_zero_iff (by fun_prop : Measurable fun ω ↦
      1 - condExpKernel μ m ω (Prod.mk ω ⁻¹' D))).1 hsub] with ω hω
    exact le_antisymm (hle ω) (by simpa using tsub_eq_zero_iff_le.1 hω)
  filter_upwards [hμ] with ω hω
  have : (condExpKernel μ m ω) {ζ | r ζ = r ω}ᶜ = 0 := by
    have h1 : Prod.mk ω ⁻¹' D = {ζ | r ζ = r ω} := by ext ζ; simp [hD_def]
    have := prob_compl_eq_zero_iff (μ := condExpKernel μ m ω)
      (s := Prod.mk ω ⁻¹' D) (by rw [h1]; exact measurableSet_eq_fun hrΩ measurable_const)
    rw [h1] at this
    exact this.2 (h1 ▸ hω)
  rwa [ae_iff]

end ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Averaging the conditional expectation kernel over `μ` returns `μ`. -/
theorem lintegral_lintegral_condExpKernel (hm : m ≤ mΩ) {g : Ω → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, (∫⁻ ζ, g ζ ∂(condExpKernel μ m ω)) ∂μ = ∫⁻ ω, g ω ∂μ := by
  have h1 : Measurable[m] fun ω ↦ ∫⁻ ζ, g ζ ∂(condExpKernel μ m ω) := hg.lintegral_kernel
  rw [← lintegral_trim hm h1, ← Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]
  congr 1
  exact condExpKernel_comp_trim hm

/-- Averaging the conditional expectation kernel over `μ` returns `μ` (Bochner form). -/
theorem integral_integral_condExpKernel (hm : m ≤ mΩ) {F : Ω → ℝ} (hF : Integrable F μ) :
    ∫ ω, (∫ ζ, F ζ ∂(condExpKernel μ m ω)) ∂μ = ∫ ω, F ω ∂μ := by
  rw [← integral_congr_ae (condExp_ae_eq_integral_condExpKernel hm hF), integral_condExp hm]

/-- **Georgii's `ν̃`** (in the proof of (10.26)): the *conditionally independent self-coupling* of
`μ` given the σ-algebra `m`, `ν̃ = ∫ μ(dω) π(·|ω) × π(·|ω)`, where `π = condExpKernel μ m` is a
regular version of `μ(·|m)`. Both marginals of `ν̃` are `μ`, and `ν̃` sits on the set where the two
coordinates agree on every `m`-measurable function. -/
def condSelfCoupling (μ : Measure Ω) [IsProbabilityMeasure μ] (m' : MeasurableSpace Ω) :
    @Measure (Ω × Ω) (@Prod.instMeasurableSpace Ω Ω mΩ mΩ) :=
  μ.bind fun ω ↦ (condExpKernel (mΩ := mΩ) μ m' ×ₖ condExpKernel (mΩ := mΩ) μ m') ω

lemma aemeasurable_condSelfKernel (hm : m ≤ mΩ) :
    @AEMeasurable Ω (Measure (Ω × Ω)) _ mΩ
      (fun ω ↦ (condExpKernel μ m ×ₖ condExpKernel μ m) ω) μ :=
  (((condExpKernel μ m ×ₖ condExpKernel μ m).measurable).mono hm le_rfl).aemeasurable

theorem lintegral_condSelfCoupling (hm : m ≤ mΩ) {f : Ω × Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(condSelfCoupling μ m)
      = ∫⁻ ω, ∫⁻ ζ, ∫⁻ η, f (ζ, η) ∂(condExpKernel μ m ω) ∂(condExpKernel μ m ω) ∂μ := by
  rw [condSelfCoupling,
    Measure.lintegral_bind (aemeasurable_condSelfKernel hm) hf.aemeasurable]
  refine lintegral_congr fun ω ↦ ?_
  rw [Kernel.prod_apply, lintegral_prod _ hf.aemeasurable]

theorem lintegral_fst_condSelfCoupling (hm : m ≤ mΩ) {g : Ω → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p.1 ∂(condSelfCoupling μ m) = ∫⁻ ω, g ω ∂μ := by
  rw [lintegral_condSelfCoupling hm
    (show Measurable fun p : Ω × Ω ↦ g p.1 from hg.comp measurable_fst)]
  have h1 : ∀ ω ζ : Ω, ∫⁻ _ : Ω, g ζ ∂(condExpKernel μ m ω) = g ζ := fun ω ζ ↦ by
    rw [lintegral_const, measure_univ, mul_one]
  simp_rw [h1]
  exact lintegral_lintegral_condExpKernel hm hg

theorem lintegral_snd_condSelfCoupling (hm : m ≤ mΩ) {g : Ω → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p.2 ∂(condSelfCoupling μ m) = ∫⁻ ω, g ω ∂μ := by
  rw [lintegral_condSelfCoupling hm
    (show Measurable fun p : Ω × Ω ↦ g p.2 from hg.comp measurable_snd)]
  have h1 : ∀ ω : Ω, ∫⁻ _ : Ω, (∫⁻ η, g η ∂(condExpKernel μ m ω)) ∂(condExpKernel μ m ω)
      = ∫⁻ η, g η ∂(condExpKernel μ m ω) := fun ω ↦ by
    rw [lintegral_const, measure_univ, mul_one]
  simp_rw [h1]
  exact lintegral_lintegral_condExpKernel hm hg

theorem condSelfCoupling_preimage_fst (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet A) :
    condSelfCoupling μ m (Prod.fst ⁻¹' A) = μ A := by
  have h : (Prod.fst ⁻¹' A).indicator (1 : Ω × Ω → ℝ≥0∞)
      = fun p : Ω × Ω ↦ A.indicator (1 : Ω → ℝ≥0∞) p.1 :=
    funext fun p ↦ by by_cases hp : p.1 ∈ A <;> simp [Set.indicator, hp]
  rw [← lintegral_indicator_one (measurable_fst hA), h,
    lintegral_fst_condSelfCoupling hm (measurable_one.indicator hA),
    lintegral_indicator_one hA]

theorem condSelfCoupling_preimage_snd (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet A) :
    condSelfCoupling μ m (Prod.snd ⁻¹' A) = μ A := by
  have h : (Prod.snd ⁻¹' A).indicator (1 : Ω × Ω → ℝ≥0∞)
      = fun p : Ω × Ω ↦ A.indicator (1 : Ω → ℝ≥0∞) p.2 :=
    funext fun p ↦ by by_cases hp : p.2 ∈ A <;> simp [Set.indicator, hp]
  rw [← lintegral_indicator_one (measurable_snd hA), h,
    lintegral_snd_condSelfCoupling hm (measurable_one.indicator hA),
    lintegral_indicator_one hA]

theorem isProbabilityMeasure_condSelfCoupling (hm : m ≤ mΩ) :
    IsProbabilityMeasure (condSelfCoupling μ m) := by
  constructor
  rw [show (Set.univ : Set (Ω × Ω)) = Prod.fst ⁻¹' Set.univ from rfl,
    condSelfCoupling_preimage_fst hm MeasurableSet.univ, measure_univ]

/-- The two coordinates of `ν̃` agree on every `m`-measurable function: the conditionally
independent self-coupling sits on the "same `m`-fibre" set. -/
theorem ae_eq_condSelfCoupling (hm : m ≤ mΩ) {β : Type*} [MeasurableSpace β] [MeasurableEq β]
    {r : Ω → β} (hr : Measurable[m] r) :
    ∀ᵐ p ∂(condSelfCoupling μ m), r p.1 = r p.2 := by
  classical
  have hrΩ : Measurable r := hr.mono hm le_rfl
  set B : Set (Ω × Ω) := {p : Ω × Ω | r p.1 = r p.2}ᶜ with hB_def
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun (hrΩ.comp measurable_fst) (hrΩ.comp measurable_snd)).compl
  have hzero : condSelfCoupling μ m B = 0 := by
    rw [← lintegral_indicator_one hB,
      lintegral_condSelfCoupling hm (measurable_one.indicator hB)]
    have hae : (fun ω ↦ ∫⁻ ζ, ∫⁻ η, B.indicator (1 : Ω × Ω → ℝ≥0∞) (ζ, η)
        ∂(condExpKernel μ m ω) ∂(condExpKernel μ m ω)) =ᵐ[μ] 0 := by
      filter_upwards [condExpKernel_ae_ae_eq hm hr] with ω hω
      have h0 : (fun ζ ↦ ∫⁻ η, B.indicator (1 : Ω × Ω → ℝ≥0∞) (ζ, η)
          ∂(condExpKernel μ m ω)) =ᵐ[condExpKernel μ m ω] 0 := by
        filter_upwards [hω] with ζ hζ
        have h1 : (fun η ↦ B.indicator (1 : Ω × Ω → ℝ≥0∞) (ζ, η))
            =ᵐ[condExpKernel μ m ω] 0 := by
          filter_upwards [hω] with η hη
          have : (ζ, η) ∉ B := by simp [hB_def, hζ, hη]
          simp [Set.indicator_of_notMem this]
        rw [lintegral_congr_ae h1]
        simp
      rw [lintegral_congr_ae h0]
      simp
    rw [lintegral_congr_ae hae]
    simp
  rwa [ae_iff]

/-- **Georgii's estimate in the proof of (10.26)**: `ν(|f - π f|) ≤ ν̃(|f(ζ) - f(η)|)`, where
`π = condExpKernel μ m` and `ν̃` is the conditionally independent self-coupling. -/
theorem lintegral_ofReal_abs_sub_condExp_le (hm : m ≤ mΩ) {f : Ω → ℝ}
    (hfm : StronglyMeasurable f) (hf : Integrable f μ) :
    ∫⁻ ω, ENNReal.ofReal |f ω - (μ[f | m]) ω| ∂μ
      ≤ ∫⁻ p, ENNReal.ofReal |f p.1 - f p.2| ∂(condSelfCoupling μ m) := by
  classical
  set g : Ω → ℝ := fun ω ↦ ∫ ζ, f ζ ∂(condExpKernel μ m ω) with hg_def
  have hgm : StronglyMeasurable[m] g := hfm.integral_condExpKernel
  have hgmeas : Measurable g := (hgm.mono hm).measurable
  have hfmeas : Measurable f := hfm.measurable
  have hstep0 : ∫⁻ ω, ENNReal.ofReal |f ω - (μ[f | m]) ω| ∂μ
      = ∫⁻ ω, ENNReal.ofReal |f ω - g ω| ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [condExp_ae_eq_integral_condExpKernel hm hf] with ω hω
    rw [hω]
  have hmeas1 : Measurable fun ζ ↦ ENNReal.ofReal |f ζ - g ζ| :=
    ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun ζ ↦ |f ζ - g ζ|)
  have hmeas2 : Measurable fun p : Ω × Ω ↦ ENNReal.ofReal |f p.1 - f p.2| :=
    ENNReal.measurable_ofReal.comp
      (by fun_prop : Measurable fun p : Ω × Ω ↦ |f p.1 - f p.2|)
  rw [hstep0, ← lintegral_lintegral_condExpKernel hm hmeas1,
    lintegral_condSelfCoupling hm hmeas2]
  refine lintegral_mono_ae ?_
  filter_upwards [condExpKernel_ae_ae_eq hm hgm.measurable, hf.condExpKernel_ae]
    with ω hω hωint
  calc ∫⁻ ζ, ENNReal.ofReal |f ζ - g ζ| ∂(condExpKernel μ m ω)
      = ∫⁻ ζ, ENNReal.ofReal |f ζ - g ω| ∂(condExpKernel μ m ω) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hω] with ζ hζ
        rw [hζ]
    _ ≤ ∫⁻ ζ, ∫⁻ η, ENNReal.ofReal |f ζ - f η| ∂(condExpKernel μ m ω)
          ∂(condExpKernel μ m ω) := by
        refine lintegral_mono fun ζ ↦ ?_
        have hfint : Integrable (fun η ↦ f ζ - f η) (condExpKernel μ m ω) :=
          (integrable_const _).sub hωint
        have heq : f ζ - g ω = ∫ η, (f ζ - f η) ∂(condExpKernel μ m ω) := by
          rw [integral_sub (integrable_const _) hωint, integral_const]
          simp [hg_def]
        rw [heq]
        calc ENNReal.ofReal |∫ η, (f ζ - f η) ∂(condExpKernel μ m ω)|
            ≤ ENNReal.ofReal (∫ η, |f ζ - f η| ∂(condExpKernel μ m ω)) := by
              gcongr
              exact abs_integral_le_integral_abs
          _ = ∫⁻ η, ENNReal.ofReal |f ζ - f η| ∂(condExpKernel μ m ω) :=
              ofReal_integral_eq_lintegral_ofReal hfint.abs
                (Eventually.of_forall fun _ ↦ abs_nonneg _)

end ProbabilityTheory

/-! ## Missing Mathlib: `n`-step densities of a kernel

A transition kernel `P` on `E` with a density `p` with respect to a fixed measure `ν`
(`P x = p(x, ·) ν`) has `n`-step densities obtained by the convolution recursion
`p^{n+1}(x, y) = ∫ p^n(x, u) p(u, y) ν(du)`, and any mixture `α P` has the density
`y ↦ ∫ p(u, y) α(du)`. Intended home: `Mathlib/Probability/Kernel/WithDensity.lean`. -/

namespace MeasureTheory

/-- The `ν`-density of a mixture `α P` of a kernel `P` whose values have `ν`-densities `p x`. -/
theorem Measure.bind_eq_withDensity_lintegral {E F : Type*} [MeasurableSpace E]
    [MeasurableSpace F] {ν : Measure F} [SFinite ν] {p : E → F → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) {P : Kernel E F}
    (hP : ∀ x, P x = ν.withDensity (p x)) (α : Measure E) [SFinite α] :
    α.bind P = ν.withDensity fun y ↦ ∫⁻ u, p u y ∂α := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), withDensity_apply _ hs]
  have h1 : ∀ u, P u s = ∫⁻ y in s, p u y ∂ν := fun u ↦ by rw [hP u, withDensity_apply _ hs]
  simp_rw [h1]
  exact lintegral_lintegral_swap hp.aemeasurable

end MeasureTheory

namespace ProbabilityTheory

/-- Powers of a Markov kernel are Markov kernels. Intended home:
`Mathlib/Probability/Kernel/Basic.lean`, next to the other `IsMarkovKernel` closure instances
(`IsMarkovKernel.comp`, `IsMarkovKernel.compProd`, `IsMarkovKernel.piecewise`). -/
theorem isMarkovKernel_pow {α : Type*} [MeasurableSpace α] {Q : Kernel α α} [IsMarkovKernel Q] :
    ∀ {n : ℕ}, 1 ≤ n → IsMarkovKernel (Q ^ n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa using (inferInstance : IsMarkovKernel Q)
  | succ n _ _ => rw [pow_succ]; exact ProbabilityTheory.Kernel.IsMarkovKernel.comp (Q ^ n) Q

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {p : E → E → ℝ≥0∞}

/-- The `n`-step transition density of a kernel `P` with `P x = p(x, ·) ν`, defined by the
convolution recursion `p^{n+1}(x, y) = ∫ p^n(x, u) p(u, y) ν(du)` — Georgii **(10.29)**.
The value at `n = 0` is junk (`P ^ 0` is the identity kernel, which has no `ν`-density);
every statement about `Kernel.densityPow` carries the hypothesis `1 ≤ n`. -/
noncomputable def Kernel.densityPow (ν : Measure E) (p : E → E → ℝ≥0∞) :
    ℕ → E → E → ℝ≥0∞
  | 0 => fun _ _ ↦ 0
  | 1 => p
  | (n + 2) => fun x y ↦ ∫⁻ u, Kernel.densityPow ν p (n + 1) x u * p u y ∂ν

@[simp] lemma Kernel.densityPow_one : Kernel.densityPow ν p 1 = p := rfl

/-- The convolution recursion `p^{n+1}(x, y) = ∫ p^n(x, u) p(u, y) ν(du)`, `n ≥ 1`. -/
lemma Kernel.densityPow_succ {n : ℕ} (hn : 1 ≤ n) (x y : E) :
    Kernel.densityPow ν p (n + 1) x y = ∫⁻ u, Kernel.densityPow ν p n x u * p u y ∂ν := by
  cases n with
  | zero => exact absurd hn (by norm_num)
  | succ m => rfl

lemma Kernel.measurable_uncurry_densityPow [SFinite ν] (hp : Measurable (Function.uncurry p))
    (n : ℕ) : Measurable (Function.uncurry (Kernel.densityPow ν p n)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      cases n with
      | zero => exact hp
      | succ m =>
          change Measurable fun q : E × E ↦
            ∫⁻ u, Kernel.densityPow ν p (m + 1) q.1 u * p u q.2 ∂ν
          refine Measurable.lintegral_prod_right' (f := fun q : (E × E) × E ↦
            Kernel.densityPow ν p (m + 1) q.1.1 q.2 * p q.2 q.1.2) ?_
          exact (ih.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
            (hp.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))

/-- `P ^ n` has the `ν`-density `p^n` of `Kernel.densityPow`, for every `n ≥ 1`. -/
theorem Kernel.pow_apply_eq_withDensity_densityPow [SFinite ν]
    (hp : Measurable (Function.uncurry p)) {P : Kernel E E}
    (hP : ∀ x, P x = ν.withDensity (p x)) :
    ∀ {n : ℕ}, 1 ≤ n → ∀ x, (P ^ n) x = ν.withDensity (Kernel.densityPow ν p n x) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa using hP
  | succ n hn ih =>
      intro x
      ext s hs
      have hdn : Measurable (Kernel.densityPow ν p n x) :=
        (Kernel.measurable_uncurry_densityPow hp n).comp (measurable_const.prodMk measurable_id)
      have hPs : Measurable fun b ↦ P b s := Kernel.measurable_coe P hs
      have hpb : ∀ b : E, Measurable (p b) := fun b ↦
        hp.comp (measurable_const.prodMk measurable_id)
      have hL : ∀ b : E, Kernel.densityPow ν p n x b * P b s
          = ∫⁻ y in s, Kernel.densityPow ν p n x b * p b y ∂ν := fun b ↦ by
        rw [hP b, withDensity_apply _ hs, lintegral_const_mul _ (hpb b)]
      rw [Kernel.pow_succ_apply_eq_lintegral P n x hs, ih x,
        lintegral_withDensity_eq_lintegral_mul _ hdn hPs, withDensity_apply _ hs]
      simp only [Pi.mul_apply]
      rw [lintegral_congr hL, lintegral_lintegral_swap]
      · exact lintegral_congr fun y ↦ (Kernel.densityPow_succ hn x y).symm
      · exact (((Kernel.measurable_uncurry_densityPow hp n).comp
          (measurable_const.prodMk measurable_fst)).mul
          (hp.comp (measurable_fst.prodMk measurable_snd))).aemeasurable

end ProbabilityTheory

/-! ## Missing Mathlib: a π-system criterion for set integrals -/

namespace MeasureTheory

/-- Two measurable `ℝ≥0∞`-valued functions with finite integrals which have the same integral over
every set of a π-system generating `m`, and over `univ`, have the same integral over every
`m`-measurable set. The `ℝ`-valued analogue is
`MeasureTheory.setIntegral_eq_of_generateFrom`. Intended home:
`Mathlib/MeasureTheory/Function/AEEqOfLIntegral.lean`. -/
lemma setLIntegral_eq_of_generateFrom {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {𝒞 : Set (Set Ω)}
    (h𝒞 : IsPiSystem 𝒞) (hgen : m = MeasurableSpace.generateFrom 𝒞) {f g : Ω → ℝ≥0∞}
    (hftop : ∫⁻ x, f x ∂μ ≠ ⊤)
    (h : ∀ s ∈ 𝒞, ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ)
    (huniv : ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ) :
    ∀ s, MeasurableSet[m] s → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ := by
  refine MeasurableSpace.induction_on_inter (m := m)
    (C := fun s _ ↦ ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) hgen h𝒞 (by simp)
    (fun t ht ↦ h t ht) (fun t ht hts ↦ ?_) (fun s hd hs hts ↦ ?_)
  · have hf' := lintegral_add_compl (μ := μ) f (hm _ ht)
    have hg' := lintegral_add_compl (μ := μ) g (hm _ ht)
    have hfne : ∫⁻ x in t, f x ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top hftop (hf' ▸ le_self_add)
    refine (ENNReal.add_right_inj hfne).1 ?_
    rw [hf', huniv, ← hg', hts]
  · rw [lintegral_iUnion (fun i ↦ hm _ (hs i)) hd, lintegral_iUnion (fun i ↦ hm _ (hs i)) hd]
    exact tsum_congr hts

end MeasureTheory

/-! ## Georgii (10.23): homogeneity and irreducibility -/

namespace Specification

variable {E : Type*} [MeasurableSpace E] {ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞}

open scoped Classical in
/-- **Georgii, §10.2**: a `λ`-modification `ρ` on `ℤ` is *homogeneous* (shift-invariant) if
`ρ_{Λ + a}(ω) = ρ_Λ(θ_{-a} ω)`, where `(θ_{-a} ω)_i = ω_{i+a}`. -/
def IsHomogeneousInt (ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞) : Prop :=
  ∀ (Λ : Finset ℤ) (a : ℤ) (ω : ℤ → E), ρ (Λ.image (· + a)) ω = ρ Λ fun i ↦ ω (i + a)

open scoped Classical in
/-- **Georgii, Definition (10.23).** A homogeneous Markovian `λ`-modification `ρ` on `ℤ` is
*irreducible* if for each `N ≥ 1` there is a set `C_N ∈ 𝓔`, an integer `n(N) ≥ 1` and a
measurable `h_N : E → [0, ∞[` such that `C_N ↑ E`, `λ(h_N) > 0` for all large `N`, and

`ρ^0_{]-n(N), n(N)[}(ω) ≥ h_N(ω_0)`   whenever `ω_{-n(N)} ∈ C_N` and `ω_{n(N)} ∈ C_N`. -/
def IsIrreducibleInt (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞) : Prop :=
  ∃ (C : ℕ → Set E) (n : ℕ → ℕ) (h : ℕ → E → ℝ≥0∞),
    (∀ N, MeasurableSet (C N)) ∧ Monotone C ∧ ⋃ N, C N = Set.univ ∧
      (∀ N, Measurable (h N)) ∧ (∀ N, 1 ≤ n N) ∧
      (∀ᶠ N in Filter.atTop, 0 < ∫⁻ x, h N x ∂ν) ∧
      ∀ (N : ℕ) (ω : ℤ → E), ω (-(n N : ℤ)) ∈ C N → ω (n N : ℤ) ∈ C N →
        h N (ω 0) ≤ marginalDensity ν ρ (Finset.Ioo (-(n N : ℤ)) (n N : ℤ)) 0 ω

open scoped Classical in
/-- The form in which irreducibility is used in Step 2 of the proof of Georgii (10.26) and in
(10.33): given any probability measure `α` on `E` (there, the one-dimensional marginal of `μ`)
and any `ε < 1`, one of the `C_N` has `α`-measure `> ε` and a companion `h_N` of positive
`λ`-integral. -/
theorem IsIrreducibleInt.exists_of_lt_one {ν : Measure E} [IsProbabilityMeasure ν]
    (hirr : IsIrreducibleInt ν ρ) (α : Measure E) [IsProbabilityMeasure α] {ε : ℝ≥0∞}
    (hε : ε < 1) :
    ∃ (C : Set E) (n : ℕ) (h : E → ℝ≥0∞), MeasurableSet C ∧ 1 ≤ n ∧ Measurable h ∧
      0 < ∫⁻ x, h x ∂ν ∧ ε < α C ∧
      ∀ ω : ℤ → E, ω (-(n : ℤ)) ∈ C → ω (n : ℤ) ∈ C →
        h (ω 0) ≤ marginalDensity ν ρ (Finset.Ioo (-(n : ℤ)) (n : ℤ)) 0 ω := by
  obtain ⟨C, n, h, hCmeas, hCmono, hCunion, hhmeas, hn, hpos, hbound⟩ := hirr
  have htend : Filter.Tendsto (fun N ↦ α (C N)) Filter.atTop (nhds (1 : ℝ≥0∞)) := by
    have := MeasureTheory.tendsto_measure_iUnion_atTop (μ := α) hCmono
    rwa [hCunion, measure_univ] at this
  obtain ⟨N, hN1, hN2⟩ := (hpos.and (htend.eventually_const_lt hε)).exists
  exact ⟨C N, n N, h N, hCmeas N, hn N, hhmeas N, hN1, hN2, hbound N⟩

end Specification

namespace MeasureTheory.GibbsMeasure.Markov

open Specification

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
  {ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞} {γ : Specification ℤ E} {μ : Measure (ℤ → E)}

variable (E) in
/-- Georgii's shift `θ_{-a}` in coordinates, `(θ_{-a} ω)_i = ω_{i+a}`; an abbreviation for
`(GibbsMeasure.shift E (-a)).toFun`. -/
abbrev transl (a : ℤ) (ω : ℤ → E) : ℤ → E := (shift E (-a)).toFun ω

@[simp] lemma transl_apply (a : ℤ) (ω : ℤ → E) (i : ℤ) : transl E a ω i = ω (i + a) := by
  simp [sub_neg_eq_add]

lemma measurable_transl (a : ℤ) : Measurable (transl E a) :=
  (shift E (-a)).measurable_toFun

/-- Resampling no site at all leaves the configuration alone. -/
lemma isssd_empty {S : Type*} (ω : S → E) : isssd (S := S) ν ∅ ω = Measure.dirac ω := by
  refine Measure.ext fun A hA ↦ ?_
  have hA' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (((∅ : Finset S) : Set S)ᶜ)] A := by
    rwa [Finset.coe_empty, Set.compl_empty, cylinderEvents_univ]
  rw [((isssd (S := S) ν).isProper ∅).apply_eq_indicator_mul_univ cylinderEvents_le_pi hA',
    measure_univ, mul_one, Measure.dirac_apply' ω hA]

lemma map_transl_isssd_singleton (a j : ℤ) (ω : ℤ → E) :
    (isssd ν ({j + a} : Finset ℤ) ω).map (transl E a) = isssd ν ({j} : Finset ℤ) (transl E a ω)
        := by
  rw [isssd_singleton_eq_map, isssd_singleton_eq_map,
    Measure.map_map (measurable_transl a) (measurable_update (a := j + a) ω)]
  congr 1
  funext y i
  simp only [Function.comp_apply, transl_apply]
  by_cases h : i = j
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne (by omega : i + a ≠ j + a), transl_apply]

open scoped Classical in
/-- **Shift equivariance of the independent specification**: `θ_{-a}` maps `λ_{Λ+a}(·|ω)` to
`λ_Λ(·|θ_{-a} ω)`. -/
lemma map_transl_isssd (a : ℤ) (Λ : Finset ℤ) (ω : ℤ → E) :
    (isssd ν (Λ.image (· + a)) ω).map (transl E a) = isssd ν Λ (transl E a ω) := by
  classical
  induction Λ using Finset.induction_on generalizing ω with
  | empty =>
      rw [Finset.image_empty, isssd_empty, isssd_empty, Measure.map_dirac' (measurable_transl a)]
  | insert j Λ hj ih =>
      rw [Finset.image_insert, isssd_insert, isssd_insert,
        Measure.map_bind (measurable_isssd_coe _) (measurable_transl a)]
      have h1 : (fun σ : ℤ → E ↦ (isssd ν (Λ.image (· + a)) σ).map (transl E a))
          = ⇑(isssd ν Λ) ∘ transl E a := funext fun σ ↦ ih σ
      rw [h1, ← Measure.bind_map (measurable_transl a) (measurable_isssd_coe Λ),
        map_transl_isssd_singleton]

open scoped Classical in
/-- The marginal densities of a homogeneous `λ`-modification are translates of each other:
`ρ^{j+a}_{Λ+a}(ω) = ρ^j_Λ(θ_{-a} ω)`. -/
lemma marginalDensity_translate (hhom : IsHomogeneousInt ρ) (hρ : ∀ Λ, Measurable (ρ Λ))
    (Λ : Finset ℤ) (j a : ℤ) (ω : ℤ → E) :
    marginalDensity ν ρ (Λ.image (· + a)) (j + a) ω
      = marginalDensity ν ρ Λ j (transl E a ω) := by
  classical
  have herase : (Λ.image (· + a)).erase (j + a) = (Λ.erase j).image (· + a) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hx, y, hy, rfl⟩
      exact ⟨y, ⟨fun h ↦ hx (by rw [h]), hy⟩, rfl⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨fun h ↦ hy1 (by omega), y, hy2, rfl⟩
  have hfun : ∀ σ : ℤ → E, ρ (Λ.image (· + a)) σ = ρ Λ (transl E a σ) := fun σ ↦ by
    rw [hhom Λ a σ]
    congr 1
    funext i
    simp
  simp only [marginalDensity]
  rw [lintegral_congr hfun, herase, ← map_transl_isssd a (Λ.erase j) ω,
    lintegral_map (hρ Λ) (measurable_transl a)]

open scoped Classical in
/-- **Georgii (10.23) at an arbitrary site.** For a homogeneous `ρ` the irreducibility bound
around the origin propagates to every site `k`:
`ρ^k_{]k-n, k+n[}(ω) ≥ h(ω_k)` as soon as `ω_{k-n}, ω_{k+n} ∈ C`. -/
lemma marginalDensity_Ioo_ge_of_homogeneous (hhom : IsHomogeneousInt ρ)
    (hρ : ∀ Λ, Measurable (ρ Λ)) {C : Set E} {h : E → ℝ≥0∞} {n : ℕ}
    (hb : ∀ ω : ℤ → E, ω (-(n : ℤ)) ∈ C → ω (n : ℤ) ∈ C →
      h (ω 0) ≤ marginalDensity ν ρ (Finset.Ioo (-(n : ℤ)) (n : ℤ)) 0 ω)
    (k : ℤ) (ω : ℤ → E) (h1 : ω (k - n) ∈ C) (h2 : ω (k + n) ∈ C) :
    h (ω k) ≤ marginalDensity ν ρ (Finset.Ioo (k - n) (k + n)) k ω := by
  have hb' := hb (transl E k ω)
    (by simpa [show -(n : ℤ) + k = k - n by ring] using h1)
    (by simpa [show (n : ℤ) + k = k + n by ring] using h2)
  have himg : (Finset.Ioo (-(n : ℤ)) (n : ℤ)).image (· + k) = Finset.Ioo (k - n) (k + n) := by
    rw [Finset.image_add_right_Ioo]
    congr 1 <;> ring
  rw [← marginalDensity_translate hhom hρ (Finset.Ioo (-(n : ℤ)) (n : ℤ)) 0 k ω, himg,
    zero_add] at hb'
  simpa using hb'

/-! ### Two resampling identities used throughout the proof of (10.26) -/

/-- **Georgii (10.12), integrated form.** For `b ∈ V` and an integrand `g` which does not depend
on the sites of `V ∖ {b}`, integrating `ρ^b_V · g` against the single-site resampling `m λ_{{b}}`
is the same as integrating `ρ_V · g` against the full resampling `m λ_V`. -/
lemma lintegral_marginalDensity_mul {V : Finset ℤ} {b : ℤ} (hb : b ∈ V)
    (hρV : Measurable (ρ V)) {g : (ℤ → E) → ℝ≥0∞} (hg : Measurable g)
    (hgdep : ∀ σ ω : ℤ → E, (∀ i ∉ V.erase b, σ i = ω i) → g σ = g ω) (m : Measure (ℤ → E)) :
    ∫⁻ σ, marginalDensity ν ρ V b σ * g σ ∂(m.bind (isssd ν {b}))
      = ∫⁻ σ, ρ V σ * g σ ∂(m.bind (isssd ν V)) := by
  classical
  have hVe : (V.erase b) ∪ {b} = V := by
    rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hb]
  have hmd : Measurable (marginalDensity ν ρ V b) := measurable_marginalDensity hρV b
  have hm1 : Measurable fun σ : ℤ → E ↦ marginalDensity ν ρ V b σ * g σ := hmd.mul hg
  have hm2 : Measurable fun σ : ℤ → E ↦ ρ V σ * g σ := hρV.mul hg
  rw [Measure.lintegral_bind (measurable_isssd_coe _).aemeasurable hm1.aemeasurable,
    Measure.lintegral_bind (measurable_isssd_coe _).aemeasurable hm2.aemeasurable]
  refine lintegral_congr fun η ↦ ?_
  have h' : isssd ν V η = (isssd ν {b} η).bind (isssd ν (V.erase b)) := by
    rw [isssd_bind_isssd, hVe]
  rw [h', Measure.lintegral_bind (measurable_isssd_coe _).aemeasurable hm2.aemeasurable]
  refine lintegral_congr fun ω ↦ Eq.symm ?_
  calc ∫⁻ σ, ρ V σ * g σ ∂(isssd ν (V.erase b) ω)
      = ∫⁻ σ, ρ V σ * g ω ∂(isssd ν (V.erase b) ω) := by
        refine lintegral_isssd_congr_of_eqOn ω (hρV.mul hg) (hρV.mul measurable_const)
          fun σ hσ ↦ ?_
        rw [hgdep σ ω hσ]
    _ = marginalDensity ν ρ V b ω * g ω := by
        rw [marginalDensity, ← lintegral_mul_const _ hρV]

/-- **Georgii's identity `ν γ_V = ν`** in the proof of Step 1 of (10.26): if the density `ρ_V`
does not depend on the coordinate `j`, then resampling the volume `V` (with the density `ρ_V`)
leaves the measure `ν_j = μ λ_{{j}}` invariant, for every `μ ∈ 𝒢(ρλ)`. -/
lemma lintegral_mul_bind_isssd_of_isGibbsMeasure [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hμ : γ.IsGibbsMeasure μ) {V : Finset ℤ} {j : ℤ}
    (hVdep : ∀ σ ω : ℤ → E, (∀ i ∉ ({j} : Finset ℤ), σ i = ω i) → ρ V σ = ρ V ω)
    {G : (ℤ → E) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ σ, ρ V σ * G σ ∂((μ.bind (isssd ν {j})).bind (isssd ν V))
      = ∫⁻ σ, G σ ∂(μ.bind (isssd ν {j})) := by
  classical
  have hswap : (μ.bind (isssd ν ({j} : Finset ℤ))).bind (isssd ν V)
      = (μ.bind (isssd ν V)).bind (isssd ν ({j} : Finset ℤ)) := by
    rw [Measure.bind_bind (measurable_isssd_coe _).aemeasurable
        (measurable_isssd_coe _).aemeasurable,
      Measure.bind_bind (measurable_isssd_coe _).aemeasurable
        (measurable_isssd_coe _).aemeasurable]
    refine congrArg _ (funext fun η ↦ ?_)
    rw [isssd_bind_isssd, isssd_bind_isssd, Finset.union_comm]
  have hHmeas : Measurable fun τ : ℤ → E ↦ ∫⁻ σ, G σ ∂(isssd ν ({j} : Finset ℤ) τ) :=
    (Measurable.lintegral_kernel (κ := isssd ν ({j} : Finset ℤ)) hG).mono
      cylinderEvents_le_pi le_rfl
  have hmG : Measurable fun σ : ℤ → E ↦ ρ V σ * G σ := (hρ V).mul hG
  rw [hswap, Measure.lintegral_bind (measurable_isssd_coe _).aemeasurable hmG.aemeasurable]
  have hstep : ∀ τ : ℤ → E, ∫⁻ σ, ρ V σ * G σ ∂(isssd ν ({j} : Finset ℤ) τ)
      = ρ V τ * ∫⁻ σ, G σ ∂(isssd ν ({j} : Finset ℤ) τ) := fun τ ↦ by
    rw [show (fun σ : ℤ → E ↦ ρ V σ * G σ) = fun σ ↦ ρ V σ * G σ from rfl]
    calc ∫⁻ σ, ρ V σ * G σ ∂(isssd ν ({j} : Finset ℤ) τ)
        = ∫⁻ σ, ρ V τ * G σ ∂(isssd ν ({j} : Finset ℤ) τ) := by
          refine lintegral_isssd_congr_of_eqOn τ ((hρ V).mul hG) (measurable_const.mul hG)
            fun σ hσ ↦ ?_
          rw [hVdep σ τ hσ]
      _ = ρ V τ * ∫⁻ σ, G σ ∂(isssd ν ({j} : Finset ℤ) τ) := lintegral_const_mul _ hG
  simp_rw [hstep]
  have hwd : ∫⁻ a, (ρ V * fun τ ↦ ∫⁻ σ, G σ ∂(isssd ν ({j} : Finset ℤ) τ)) a
        ∂(μ.bind (isssd ν V))
      = ∫⁻ a, (∫⁻ σ, G σ ∂(isssd ν ({j} : Finset ℤ) a))
        ∂((μ.bind (isssd ν V)).withDensity (ρ V)) :=
    (lintegral_withDensity_eq_lintegral_mul _ (hρ V) hHmeas).symm
  simp only [Pi.mul_apply] at hwd
  rw [hwd, ← hμ.eq_withDensity_bind_isssd hγ hρ V,
    Measure.lintegral_bind (measurable_isssd_coe _).aemeasurable hG.aemeasurable]

/-! ### Georgii (10.26), Step 1: the estimate (10.28)

Georgii's `φ_n^k(x, ζ) = ρ^k_{]k-n,k+n[}(x ζ_{ℤ∖{k}})`, its "meet" `φ̃` over two boundary
conditions and the `λ`-integral `φ̄` of the meet. -/

variable (ν ρ) in
/-- Georgii's `φ_n^k(x, ζ) = ρ^k_{]k-n,k+n[}(x ζ_{ℤ∖{k}})`. -/
def phi (n : ℕ) (k : ℤ) (x : E) (ζ : ℤ → E) : ℝ≥0∞ :=
  marginalDensity ν ρ (Finset.Ioo (k - n) (k + n)) k (Function.update ζ k x)

variable (ν ρ) in
/-- Georgii's `φ̄_n^k(ζ, η) = λ(φ_n^k(·, ζ) ∧ φ_n^k(·, η))`. -/
def phiBar (n : ℕ) (k : ℤ) (p : (ℤ → E) × (ℤ → E)) : ℝ≥0∞ :=
  ∫⁻ x, min (phi ν ρ n k x p.1) (phi ν ρ n k x p.2) ∂ν

lemma measurable_phi (hρ : ∀ Λ, Measurable (ρ Λ)) (n : ℕ) (k : ℤ) :
    Measurable fun q : (ℤ → E) × E ↦ phi ν ρ n k q.2 q.1 :=
  (measurable_marginalDensity (hρ _) k).comp measurable_update'

lemma measurable_phiBar (hρ : ∀ Λ, Measurable (ρ Λ)) (n : ℕ) (k : ℤ) :
    Measurable (phiBar ν ρ n k) := by
  refine Measurable.lintegral_prod_right' (f := fun q : ((ℤ → E) × (ℤ → E)) × E ↦
    min (phi ν ρ n k q.2 q.1.1) (phi ν ρ n k q.2 q.1.2)) ?_
  exact ((measurable_phi hρ n k).comp ((measurable_fst.comp measurable_fst).prodMk
    measurable_snd)).min ((measurable_phi hρ n k).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-- The pointwise inequality behind (10.28): if `ζ¹` and `ζ²` agree on `Δ` and `f'` depends only
on `Δ ∪ {b'}`, then `φ̄ · |f(ζ¹) - f(ζ²)|` is dominated by the sum of the two one-sided
quantities `Ψ(ζ^i) = λ(φ_n^{b'}(·, ζ^i) |f(ζ^i) - f'(· ζ^i_{ℤ∖{b'}})|)`. -/
lemma phiBar_mul_le (hρ : ∀ Λ, Measurable (ρ Λ)) {n : ℕ} {b' : ℤ} {Δ : Finset ℤ}
    (hb' : b' ∉ Δ) {f f' : (ℤ → E) → ℝ} (hf' : Measurable f')
    (hf'dep : DependsOn f' ((Δ : Set ℤ) ∪ {b'}))
    {ζ₁ ζ₂ : ℤ → E} (hζ : ∀ i ∈ Δ, ζ₁ i = ζ₂ i) :
    phiBar ν ρ n b' (ζ₁, ζ₂) * ENNReal.ofReal |f ζ₁ - f ζ₂|
      ≤ (∫⁻ x, phi ν ρ n b' x ζ₁ * ENNReal.ofReal |f ζ₁ - f' (Function.update ζ₁ b' x)| ∂ν)
        + ∫⁻ x, phi ν ρ n b' x ζ₂
            * ENNReal.ofReal |f ζ₂ - f' (Function.update ζ₂ b' x)| ∂ν := by
  classical
  have hmin : Measurable fun x ↦ min (phi ν ρ n b' x ζ₁) (phi ν ρ n b' x ζ₂) :=
    ((measurable_phi hρ n b').comp (measurable_const.prodMk measurable_id)).min
      ((measurable_phi hρ n b').comp (measurable_const.prodMk measurable_id))
  have hm1 : Measurable fun x ↦ phi ν ρ n b' x ζ₁
      * ENNReal.ofReal |f ζ₁ - f' (Function.update ζ₁ b' x)| :=
    (((measurable_phi hρ n b').comp (measurable_const.prodMk measurable_id))).mul
      (ENNReal.measurable_ofReal.comp
        (by fun_prop : Measurable fun x ↦ |f ζ₁ - f' (Function.update ζ₁ b' x)|))
  have hm2 : Measurable fun x ↦ phi ν ρ n b' x ζ₂
      * ENNReal.ofReal |f ζ₂ - f' (Function.update ζ₂ b' x)| :=
    (((measurable_phi hρ n b').comp (measurable_const.prodMk measurable_id))).mul
      (ENNReal.measurable_ofReal.comp
        (by fun_prop : Measurable fun x ↦ |f ζ₂ - f' (Function.update ζ₂ b' x)|))
  rw [phiBar, ← lintegral_mul_const _ hmin, ← lintegral_add_left hm1]
  refine lintegral_mono fun x ↦ ?_
  have hupd : f' (Function.update ζ₁ b' x) = f' (Function.update ζ₂ b' x) := by
    refine hf'dep fun i hi ↦ ?_
    rcases hi with hi | hi
    · have hib' : i ≠ b' := fun h ↦ hb' (h ▸ hi)
      rw [Function.update_of_ne hib', Function.update_of_ne hib']
      exact hζ i hi
    · rw [Set.mem_singleton_iff] at hi
      subst hi
      rw [Function.update_self, Function.update_self]
  have habs : |f ζ₁ - f ζ₂| ≤ |f ζ₁ - f' (Function.update ζ₁ b' x)|
      + |f ζ₂ - f' (Function.update ζ₂ b' x)| := by
    calc |f ζ₁ - f ζ₂|
        ≤ |f ζ₁ - f' (Function.update ζ₁ b' x)|
          + |f' (Function.update ζ₁ b' x) - f ζ₂| := abs_sub_le _ _ _
      _ = |f ζ₁ - f' (Function.update ζ₁ b' x)|
          + |f ζ₂ - f' (Function.update ζ₂ b' x)| := by
            rw [hupd, abs_sub_comm (f' (Function.update ζ₂ b' x)) (f ζ₂)]
  calc min (phi ν ρ n b' x ζ₁) (phi ν ρ n b' x ζ₂) * ENNReal.ofReal |f ζ₁ - f ζ₂|
      ≤ min (phi ν ρ n b' x ζ₁) (phi ν ρ n b' x ζ₂)
        * (ENNReal.ofReal |f ζ₁ - f' (Function.update ζ₁ b' x)|
          + ENNReal.ofReal |f ζ₂ - f' (Function.update ζ₂ b' x)|) := by
        gcongr
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal habs
    _ = min (phi ν ρ n b' x ζ₁) (phi ν ρ n b' x ζ₂)
          * ENNReal.ofReal |f ζ₁ - f' (Function.update ζ₁ b' x)|
        + min (phi ν ρ n b' x ζ₁) (phi ν ρ n b' x ζ₂)
          * ENNReal.ofReal |f ζ₂ - f' (Function.update ζ₂ b' x)| := by ring
    _ ≤ phi ν ρ n b' x ζ₁ * ENNReal.ofReal |f ζ₁ - f' (Function.update ζ₁ b' x)|
        + phi ν ρ n b' x ζ₂ * ENNReal.ofReal |f ζ₂ - f' (Function.update ζ₂ b' x)| := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _

section Step1

variable [StandardBorelSpace E] [IsProbabilityMeasure μ]

omit [StandardBorelSpace E] in
/-- The chain of identities in Georgii's Step 1: integrating `φ_n^{b'}(x, ζ) H(x ζ_{ℤ∖{b'}})`
against `λ ⊗ ν_j` returns `ν_j(H)`, for any `H` not depending on the sites of
`]b'-n, b'+n[ ∖ {b'}`, provided the resampled site `j` lies outside `[b'-n, b'+n]`.

This is Georgii's `ν λ_{{b'}}(ρ^{b'}_Λ H) = ν λ_Λ(ρ_Λ H) = ν γ_Λ(H) = ν(H)`. -/
theorem lintegral_lintegral_phi_mul
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hM : IsMarkovianInt ρ) (hμ : γ.IsGibbsMeasure μ)
    {n : ℕ} (hn : 1 ≤ n) {b' j : ℤ} (hj : j ∉ Set.Icc (b' - n) (b' + n))
    {H : (ℤ → E) → ℝ≥0∞} (hH : Measurable H)
    (hHdep : ∀ σ ω : ℤ → E,
      (∀ i ∉ (Finset.Ioo (b' - n) (b' + n)).erase b', σ i = ω i) → H σ = H ω) :
    ∫⁻ ζ, (∫⁻ x, phi ν ρ n b' x ζ * H (Function.update ζ b' x) ∂ν) ∂(μ.bind (isssd ν {j}))
      = ∫⁻ σ, H σ ∂(μ.bind (isssd ν {j})) := by
  classical
  set V : Finset ℤ := Finset.Ioo (b' - n) (b' + n) with hV_def
  have hb'V : b' ∈ V := by
    simp only [hV_def, Finset.mem_Ioo]
    omega
  have hlt : b' - (n : ℤ) + 1 < b' + n := by omega
  have hmd : Measurable (marginalDensity ν ρ V b') := measurable_marginalDensity (hρ V) b'
  have hF : Measurable fun σ : ℤ → E ↦ marginalDensity ν ρ V b' σ * H σ := hmd.mul hH
  have hVdep : ∀ σ ω : ℤ → E, (∀ i ∉ ({j} : Finset ℤ), σ i = ω i) → ρ V σ = ρ V ω := by
    intro σ ω h
    refine hM.dependsOn hlt fun i hi ↦ h i ?_
    simp only [Finset.mem_singleton]
    rintro rfl
    refine hj ?_
    simp only [Finset.coe_Ioo, Set.mem_union, Set.mem_Ioo, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi
    simp only [Set.mem_Icc]
    omega
  have hstep : ∀ ζ : ℤ → E, (∫⁻ x, phi ν ρ n b' x ζ * H (Function.update ζ b' x) ∂ν)
      = ∫⁻ x, (fun σ ↦ marginalDensity ν ρ V b' σ * H σ) (Function.update ζ b' x) ∂ν :=
    fun ζ ↦ rfl
  simp_rw [hstep]
  rw [← lintegral_bind_isssd_singleton (μ := μ.bind (isssd ν {j})) b' hF,
    lintegral_marginalDensity_mul hb'V (hρ V) hH hHdep,
    lintegral_mul_bind_isssd_of_isGibbsMeasure hγ hρ hμ hVdep hH]

/-- **Georgii (10.28)** (Step 1 of the proof of (10.26)). Here `Δ` is the finite set of sites of
the hypothesis (ii) of (10.26), `b'` the site that gets resampled, `b = b' ± n` the site the
"far" function `f` lives on, and `j` the site defining `ν_j = μ λ_{{j}}`. -/
theorem lintegral_phiBar_mul_le
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hM : IsMarkovianInt ρ) (hμ : γ.IsGibbsMeasure μ)
    {n : ℕ} (hn : 1 ≤ n) {b b' j : ℤ} {Δ : Finset ℤ}
    (hΔ : ∀ i ∈ Δ, i ∉ Set.Icc (b' - n) (b' + n))
    (hb : b ∉ Finset.Ioo (b' - n) (b' + n)) (hj : j ∉ Set.Icc (b' - n) (b' + n))
    {f f' : (ℤ → E) → ℝ} (hf : Measurable f) (hf' : Measurable f')
    (hfdep : DependsOn f ((Δ : Set ℤ) ∪ {b})) (hf'dep : DependsOn f' ((Δ : Set ℤ) ∪ {b'})) :
    ∫⁻ p, phiBar ν ρ n b' p * ENNReal.ofReal |f p.1 - f p.2|
        ∂(condSelfCoupling (μ.bind (isssd ν {j})) (cylinderEvents (X := fun _ : ℤ ↦ E)
          (Δ : Set ℤ)))
      ≤ 2 * ∫⁻ σ, ENNReal.ofReal |f σ - f' σ| ∂(μ.bind (isssd ν {j})) := by
  classical
  set v : Measure (ℤ → E) := μ.bind (isssd ν {j}) with hv_def
  have hmle : cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hb'Δ : b' ∉ Δ := fun h ↦ hΔ b' h (by simp only [Set.mem_Icc]; omega)
  have hb'b : b ≠ b' := by
    rintro rfl
    exact hb (by simp only [Finset.mem_Ioo]; omega)
  -- `f` does not depend on the site `b'`
  have hfb' : ∀ (ζ : ℤ → E) (x : E), f (Function.update ζ b' x) = f ζ := fun ζ x ↦ by
    refine hfdep fun i hi ↦ ?_
    have : i ≠ b' := by
      rcases hi with hi | hi
      · exact fun h ↦ hb'Δ (h ▸ hi)
      · rw [Set.mem_singleton_iff] at hi; subst hi; exact hb'b
    rw [Function.update_of_ne this]
  set H : (ℤ → E) → ℝ≥0∞ := fun σ ↦ ENNReal.ofReal |f σ - f' σ| with hH_def
  have habs : Measurable fun σ : ℤ → E ↦ |f σ - f' σ| := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hf.sub hf').norm
  have hHmeas : Measurable H := ENNReal.measurable_ofReal.comp habs
  have hnotin : ∀ i : ℤ, i ∉ Finset.Ioo (b' - n) (b' + n) →
      i ∉ (Finset.Ioo (b' - n) (b' + n)).erase b' := fun i hi h ↦ hi (Finset.mem_of_mem_erase h)
  have hΔnot : ∀ i ∈ Δ, i ∉ (Finset.Ioo (b' - n) (b' + n)).erase b' := by
    intro i hi
    refine hnotin i ?_
    have h1 := hΔ i hi
    simp only [Set.mem_Icc] at h1
    simp only [Finset.mem_Ioo]
    omega
  have hHdep : ∀ σ ω : ℤ → E,
      (∀ i ∉ (Finset.Ioo (b' - n) (b' + n)).erase b', σ i = ω i) → H σ = H ω := by
    intro σ ω h
    have h1 : f σ = f ω := by
      refine hfdep fun i hi ↦ h i ?_
      rcases hi with hi | hi
      · exact hΔnot i hi
      · rw [Set.mem_singleton_iff] at hi
        subst hi
        exact hnotin _ hb
    have h2 : f' σ = f' ω := by
      refine hf'dep fun i hi ↦ h i ?_
      rcases hi with hi | hi
      · exact hΔnot i hi
      · rw [Set.mem_singleton_iff] at hi
        subst hi
        simp
    simp only [hH_def, h1, h2]
  set Ψ : (ℤ → E) → ℝ≥0∞ :=
    fun ζ ↦ ∫⁻ x, phi ν ρ n b' x ζ * H (Function.update ζ b' x) ∂ν with hΨ_def
  have hΨmeas : Measurable Ψ := by
    refine Measurable.lintegral_prod_right' (f := fun q : (ℤ → E) × E ↦
      phi ν ρ n b' q.2 q.1 * H (Function.update q.1 b' q.2)) ?_
    exact (measurable_phi hρ n b').mul (hHmeas.comp measurable_update')
  set ν2 : Measure ((ℤ → E) × (ℤ → E)) :=
    condSelfCoupling v (cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)) with hν2_def
  have hpointwise : ∀ᵐ p ∂ν2,
      phiBar ν ρ n b' p * ENNReal.ofReal |f p.1 - f p.2| ≤ Ψ p.1 + Ψ p.2 := by
    have hagree : ∀ᵐ p ∂ν2, ∀ i ∈ Δ, p.1 i = p.2 i := by
      rw [Filter.eventually_all_finset]
      intro i hi
      exact ae_eq_condSelfCoupling hmle (r := fun ω : ℤ → E ↦ ω i)
        (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by simpa using hi))
    filter_upwards [hagree] with p hp
    have hkey := phiBar_mul_le (ν := ν) (ρ := ρ) (n := n) (b' := b') (Δ := Δ) hρ hb'Δ
      (f := f) (f' := f') hf' hf'dep (ζ₁ := p.1) (ζ₂ := p.2) hp
    simpa only [hΨ_def, hH_def, hfb'] using hkey
  calc ∫⁻ p, phiBar ν ρ n b' p * ENNReal.ofReal |f p.1 - f p.2| ∂ν2
      ≤ ∫⁻ p, (Ψ p.1 + Ψ p.2) ∂ν2 := lintegral_mono_ae hpointwise
    _ = (∫⁻ p, Ψ p.1 ∂ν2) + ∫⁻ p, Ψ p.2 ∂ν2 :=
        lintegral_add_left (hΨmeas.comp measurable_fst) _
    _ = 2 * ∫⁻ σ, H σ ∂v := by
        rw [hν2_def, lintegral_fst_condSelfCoupling hmle hΨmeas,
          lintegral_snd_condSelfCoupling hmle hΨmeas,
          lintegral_lintegral_phi_mul hγ hρ hM hμ hn hj hHmeas hHdep, two_mul]

/-! ### Georgii (10.26), Step 2: irreducibility makes `φ̄` bounded away from `0` -/

/-- **Georgii (10.26), Step 2.** For every `ε > 0` there are `n ≥ 1` and `δ ∈ ]0, 1]` such that
`ν̃(φ̄_n^k < δ) < ε` for every site `k` at distance `≠ n` from the resampled site `j`.

Georgii's bound `ν̃(φ̄_n^k ≥ δ) ≥ (2α(C_N) - 1)²` (Cauchy–Schwarz on the conditional
probabilities) is replaced by the union bound `ν̃((B × B)ᶜ) ≤ 2 μ(Bᶜ)`, which only uses that
both marginals of `ν̃` are `ν_j`; the resulting constant is different, the statement is the
same. The one-dimensional marginals of `μ` are assumed to be all equal — this is the only use of
shift-invariance of `μ` in the proof of (10.26). -/
theorem exists_lt_of_isIrreducibleInt (hρ : ∀ Λ, Measurable (ρ Λ))
    (hhom : IsHomogeneousInt ρ) (hirr : IsIrreducibleInt ν ρ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (Δ : Finset ℤ) (j : ℤ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (δ : ℝ≥0∞), 1 ≤ n ∧ 0 < δ ∧ δ ≤ 1 ∧ ∀ k : ℤ, j ≠ k - n → j ≠ k + n →
      (condSelfCoupling (μ.bind (isssd ν {j}))
        (cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ))) {p | phiBar ν ρ n k p < δ} < ε := by
  classical
  set α : Measure E := μ.map (fun ω ↦ ω (0 : ℤ)) with hα_def
  have hαprob : IsProbabilityMeasure α :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℤ)).aemeasurable
  have hlt : (1 : ℝ≥0∞) - ε / 4 < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  obtain ⟨C, n, h, hCmeas, hn, hhmeas, hhpos, hαC, hbound⟩ := hirr.exists_of_lt_one α hlt
  have hn' : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  refine ⟨n, min (∫⁻ x, h x ∂ν) 1, hn, lt_min hhpos one_pos, min_le_right _ _, fun k hk1 hk2 ↦ ?_⟩
  set B : Set (ℤ → E) := {σ : ℤ → E | σ (k - n) ∈ C} ∩ {σ : ℤ → E | σ (k + n) ∈ C} with hB_def
  have hB1c : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
      ((({j} : Finset ℤ) : Set ℤ)ᶜ)] {σ : ℤ → E | σ (k - n) ∈ C} :=
    measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by simpa using fun hc ↦ hk1 hc.symm) hCmeas
  have hB2c : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
      ((({j} : Finset ℤ) : Set ℤ)ᶜ)] {σ : ℤ → E | σ (k + n) ∈ C} :=
    measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by simpa using fun hc ↦ hk2 hc.symm) hCmeas
  have hBc : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
      ((({j} : Finset ℤ) : Set ℤ)ᶜ)] Bᶜ := (hB1c.inter hB2c).compl
  have hBmeas : MeasurableSet Bᶜ := cylinderEvents_le_pi _ hBc
  -- the two one-dimensional estimates
  have hone : ∀ i : ℤ, μ {σ : ℤ → E | σ i ∈ C}ᶜ = 1 - α C := by
    intro i
    have hmi : MeasurableSet {σ : ℤ → E | σ i ∈ C} := (measurable_pi_apply i) hCmeas
    have heq : μ {σ : ℤ → E | σ i ∈ C} = α C := by
      rw [← hmarg i, Measure.map_apply (measurable_pi_apply i) hCmeas]
      rfl
    rw [prob_compl_eq_one_sub hmi, heq]
  have hBcle : μ Bᶜ ≤ 2 * (1 - α C) := by
    have hsub : Bᶜ ⊆ {σ : ℤ → E | σ (k - n) ∈ C}ᶜ ∪ {σ : ℤ → E | σ (k + n) ∈ C}ᶜ := by
      rw [hB_def, Set.compl_inter]
    calc μ Bᶜ ≤ μ ({σ : ℤ → E | σ (k - n) ∈ C}ᶜ ∪ {σ : ℤ → E | σ (k + n) ∈ C}ᶜ) :=
          measure_mono hsub
      _ ≤ μ {σ : ℤ → E | σ (k - n) ∈ C}ᶜ + μ {σ : ℤ → E | σ (k + n) ∈ C}ᶜ := measure_union_le _ _
      _ = 2 * (1 - α C) := by rw [hone, hone, two_mul]
  -- `B × B` is contained in `{φ̄ ≥ δ}`
  have hincl : {p : (ℤ → E) × (ℤ → E) | phiBar ν ρ n k p < min (∫⁻ x, h x ∂ν) 1}
      ⊆ Prod.fst ⁻¹' Bᶜ ∪ Prod.snd ⁻¹' Bᶜ := by
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hge : ∀ x : E, h x ≤ min (phi ν ρ n k x p.1) (phi ν ρ n k x p.2) := by
      intro x
      have hupd : ∀ ζ : ℤ → E, ζ ∈ B →
          h x ≤ phi ν ρ n k x ζ := by
        intro ζ hζ
        have hkn : k - (n : ℤ) ≠ k := by omega
        have hkp : k + (n : ℤ) ≠ k := by omega
        have := marginalDensity_Ioo_ge_of_homogeneous (ν := ν) hhom hρ hbound k
          (Function.update ζ k x)
          (by rw [Function.update_of_ne hkn]; exact hζ.1)
          (by rw [Function.update_of_ne hkp]; exact hζ.2)
        rwa [Function.update_self] at this
      exact le_min (hupd p.1 h1) (hupd p.2 h2)
    have : min (∫⁻ x, h x ∂ν) 1 ≤ phiBar ν ρ n k p :=
      le_trans (min_le_left _ _) (lintegral_mono hge)
    exact absurd hp (not_lt.2 this)
  -- conclude
  calc (condSelfCoupling (μ.bind (isssd ν {j}))
        (cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)))
        {p | phiBar ν ρ n k p < min (∫⁻ x, h x ∂ν) 1}
      ≤ (condSelfCoupling (μ.bind (isssd ν {j}))
          (cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)))
          (Prod.fst ⁻¹' Bᶜ ∪ Prod.snd ⁻¹' Bᶜ) := measure_mono hincl
    _ ≤ (condSelfCoupling (μ.bind (isssd ν {j}))
          (cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ))) (Prod.fst ⁻¹' Bᶜ)
        + (condSelfCoupling (μ.bind (isssd ν {j}))
          (cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ))) (Prod.snd ⁻¹' Bᶜ) :=
        measure_union_le _ _
    _ = 2 * μ Bᶜ := by
        rw [condSelfCoupling_preimage_fst cylinderEvents_le_pi hBmeas,
          condSelfCoupling_preimage_snd cylinderEvents_le_pi hBmeas,
          bind_isssd_apply_of_measurableSet_compl hBc, two_mul]
    _ ≤ 2 * (2 * (1 - α C)) := by gcongr
    _ = 4 * (1 - α C) := by ring
    _ < 4 * (ε / 4) := by
        have hsum : (1 : ℝ≥0∞) < α C + ε / 4 := by
          rcases le_or_gt (ε / 4) 1 with hle | hgt
          · exact (ENNReal.sub_lt_iff_lt_right (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
              hle).1 hαC
          · exact lt_of_lt_of_le hgt le_add_self
        have h1 : (1 : ℝ≥0∞) - α C < ε / 4 :=
          (ENNReal.sub_lt_iff_lt_right (measure_ne_top α C) prob_le_one).2
            (by rwa [add_comm] at hsum)
        exact ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) h1
    _ = ε := ENNReal.mul_div_cancel' (by norm_num) (by norm_num)

/-! ### Georgii (10.26), Step 3 and the proposition itself -/

/-- **Georgii, Proposition (10.26).** Let `ρ` be an irreducible homogeneous Markovian
`λ`-modification, `γ = ρλ`, `μ ∈ 𝒢(γ)` with all one-dimensional marginals equal (this is all
that is used of shift-invariance), and `ν_j = μ λ_{{j}}`. Let `(F_m)` be `ν_j`-integrable
functions with

* (i) `F_m → F_∞` in `L¹(ν_j)`;
* (ii) `F_m` is `𝓕_{Δ ∪ {c m}}`-measurable, where `Δ` is a fixed finite set of sites and
  `c m = c 0 ± m` runs off to infinity in one direction.

Then `F_∞` is `𝓕_Δ`-measurable `ν_j`-almost surely.

Georgii states (ii) with `Δ ∋ 0` and `c m = m` (resp. `c m = -m`), and runs the argument at the
site `0`; the site `j` at which the a priori measure is resampled and the direction `±` are kept
free here, which is what makes both cases of (ii) — and both applications, (10.25) and
(10.34) — instances of a single statement. -/
theorem ae_eq_condExp_of_tendsto
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hM : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμ : γ.IsGibbsMeasure μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    {Δ : Finset ℤ} {j : ℤ} {c : ℕ → ℤ} {sgn : ℤ} (hsgn : sgn = 1 ∨ sgn = -1)
    (hc : ∀ m : ℕ, c m = c 0 + sgn * m)
    {F : ℕ → (ℤ → E) → ℝ} {Finf : (ℤ → E) → ℝ}
    (hFmeas : ∀ m, Measurable (F m)) (hFinfmeas : Measurable Finf)
    (hFdep : ∀ m, DependsOn (F m) ((Δ : Set ℤ) ∪ {c m}))
    (hFint : ∀ m, Integrable (F m) (μ.bind (isssd ν {j})))
    (hFinfint : Integrable Finf (μ.bind (isssd ν {j})))
    (hL1 : Filter.Tendsto
      (fun m ↦ ∫⁻ σ, ENNReal.ofReal |F m σ - Finf σ| ∂(μ.bind (isssd ν {j})))
      Filter.atTop (nhds 0)) :
    Finf =ᵐ[μ.bind (isssd ν {j})] (μ.bind (isssd ν {j}))[Finf |
      cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)] := by
  classical
  set v : Measure (ℤ → E) := μ.bind (isssd ν {j}) with hv_def
  set ν2 : Measure ((ℤ → E) × (ℤ → E)) :=
    condSelfCoupling v (cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)) with hν2_def
  have hmle : cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  set D : ℕ → ℝ≥0∞ := fun m ↦ ∫⁻ σ, ENNReal.ofReal |F m σ - Finf σ| ∂v with hD_def
  set g : ℕ → ((ℤ → E) × (ℤ → E)) → ℝ≥0∞ :=
    fun m p ↦ ENNReal.ofReal |F m p.1 - F m p.2| with hg_def
  set ginf : ((ℤ → E) × (ℤ → E)) → ℝ≥0∞ := fun p ↦ ENNReal.ofReal |Finf p.1 - Finf p.2| with
      hginf_def
  set L : ℝ≥0∞ := ∫⁻ σ, ENNReal.ofReal |Finf σ
    - (v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ| ∂v with hL_def
  have hEmeas : ∀ (G : (ℤ → E) → ℝ),
      Measurable (v[G | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) :=
    fun G ↦ (stronglyMeasurable_condExp.mono hmle).measurable
  have hFinf1 : Measurable fun p : (ℤ → E) × (ℤ → E) ↦ Finf p.1 := hFinfmeas.comp measurable_fst
  have hFinf2 : Measurable fun p : (ℤ → E) × (ℤ → E) ↦ Finf p.2 := hFinfmeas.comp measurable_snd
  have hF1 : ∀ m, Measurable fun p : (ℤ → E) × (ℤ → E) ↦ F m p.1 :=
    fun m ↦ (hFmeas m).comp measurable_fst
  have hF2 : ∀ m, Measurable fun p : (ℤ → E) × (ℤ → E) ↦ F m p.2 :=
    fun m ↦ (hFmeas m).comp measurable_snd
  have hgm : ∀ m, Measurable (g m) := fun m ↦ measurable_ofReal_abs_sub (hF1 m) (hF2 m)
  have hginfm : Measurable ginf := measurable_ofReal_abs_sub hFinf1 hFinf2
  -- finiteness of the `L¹`-norm of `Finf` and of `ginf`
  have hIFinf : ∫⁻ σ, ENNReal.ofReal |Finf σ| ∂v ≠ ⊤ := by
    have h := hFinfint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    simpa only [Real.enorm_eq_ofReal_abs] using h.ne
  have hGinf : ∫⁻ p, ginf p ∂ν2 ≠ ⊤ := by
    have hle : ∫⁻ p, ginf p ∂ν2
        ≤ (∫⁻ p, ENNReal.ofReal |Finf p.1| ∂ν2) + ∫⁻ p, ENNReal.ofReal |Finf p.2| ∂ν2 := by
      rw [← lintegral_add_left (measurable_ofReal_abs hFinf1) _]
      refine lintegral_mono fun p ↦ ?_
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (abs_sub _ _)
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_fst_condSelfCoupling hmle (measurable_ofReal_abs hFinfmeas),
      lintegral_snd_condSelfCoupling hmle (measurable_ofReal_abs hFinfmeas)]
    exact ENNReal.add_ne_top.2 ⟨hIFinf, hIFinf⟩
  have hLtop : L ≠ ⊤ := by
    have hle : L ≤ (∫⁻ σ, ENNReal.ofReal |Finf σ| ∂v)
        + ∫⁻ σ, ENNReal.ofReal |(v[Finf |
          cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ| ∂v := by
      rw [hL_def, ← lintegral_add_left (measurable_ofReal_abs hFinfmeas) _]
      refine lintegral_mono fun σ ↦ ?_
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (abs_sub _ _)
    refine ne_top_of_le_ne_top ?_ hle
    exact ENNReal.add_ne_top.2 ⟨hIFinf,
      ne_top_of_le_ne_top hIFinf (lintegral_ofReal_abs_condExp_le Finf)⟩
  -- the bound `L ≤ 2 D_m + ν̃(g_m)`
  have hLbound : ∀ m : ℕ, L ≤ 2 * D m + ∫⁻ p, g m p ∂ν2 := by
    intro m
    have hcs : (v[F m | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)])
        - (v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)])
        =ᵐ[v] v[F m - Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)] :=
      (condExp_sub (hFint m) hFinfint _).symm
    have hM2 : ∫⁻ σ, ENNReal.ofReal |F m σ
        - (v[F m | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ| ∂v
        ≤ ∫⁻ p, g m p ∂ν2 :=
      lintegral_ofReal_abs_sub_condExp_le hmle (hFmeas m).stronglyMeasurable (hFint m)
    have hthird : ∫⁻ σ, ENNReal.ofReal |(v[F m |
          cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ
        - (v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ| ∂v ≤ D m := by
      have h1 : ∫⁻ σ, ENNReal.ofReal |(v[F m |
            cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ
          - (v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ| ∂v
          = ∫⁻ σ, ENNReal.ofReal |(v[F m - Finf |
            cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ| ∂v := by
        refine lintegral_congr_ae ?_
        filter_upwards [hcs] with σ hσ
        rw [← hσ]
        rfl
      rw [h1, hD_def]
      exact le_trans (lintegral_ofReal_abs_condExp_le (F m - Finf))
        (le_of_eq (lintegral_congr fun σ ↦ rfl))
    calc L ≤ ∫⁻ σ, (ENNReal.ofReal |Finf σ - F m σ|
            + ENNReal.ofReal |F m σ
              - (v[F m | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ|
            + ENNReal.ofReal |(v[F m | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ
              - (v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ|) ∂v := by
          rw [hL_def]
          refine lintegral_mono fun σ ↦ ?_
          rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
            ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc |Finf σ - (v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ|
              ≤ |Finf σ - F m σ|
                + |F m σ - (v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ| :=
                abs_sub_le _ _ _
            _ ≤ _ := by
                have := abs_sub_le (F m σ)
                  ((v[F m | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ)
                  ((v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ)
                linarith
      _ = (∫⁻ σ, ENNReal.ofReal |Finf σ - F m σ| ∂v)
            + (∫⁻ σ, ENNReal.ofReal |F m σ
              - (v[F m | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ| ∂v)
            + ∫⁻ σ, ENNReal.ofReal |(v[F m |
              cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ
              - (v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) (Δ : Set ℤ)]) σ| ∂v := by
          rw [lintegral_add_left, lintegral_add_left]
          · exact measurable_ofReal_abs_sub hFinfmeas (hFmeas m)
          · exact (measurable_ofReal_abs_sub hFinfmeas (hFmeas m)).add
              (measurable_ofReal_abs_sub (hFmeas m) (hEmeas (F m)))
      _ ≤ D m + ∫⁻ p, g m p ∂ν2 + D m := by
          refine add_le_add (add_le_add ?_ hM2) hthird
          rw [hD_def]
          exact le_of_eq (lintegral_congr fun σ ↦ by rw [abs_sub_comm])
      _ = 2 * D m + ∫⁻ p, g m p ∂ν2 := by ring
  -- the sites of `Δ ∪ {j}` are eventually far from `c m`
  obtain ⟨R, hR⟩ : ∃ R : ℤ, ∀ i ∈ insert j Δ, |i| ≤ R := by
    obtain ⟨R, hR⟩ := ((insert j Δ).image fun i : ℤ ↦ |i|).exists_le
    exact ⟨R, fun i hi ↦ hR _ (Finset.mem_image_of_mem _ hi)⟩
  have hsites : ∀ n : ℕ, ∀ᶠ m : ℕ in Filter.atTop,
      (∀ i ∈ Δ, i ∉ Set.Icc (c m - n) (c m + n)) ∧ j ∉ Set.Icc (c m - n) (c m + n) := by
    intro n
    refine Filter.eventually_atTop.2 ⟨(R + n + |c 0| + 1).toNat, fun m hm ↦ ?_⟩
    have hm' : (R + n + |c 0| + 1 : ℤ) ≤ (m : ℤ) := Int.toNat_le.mp hm
    have h0 : c 0 ≤ |c 0| := le_abs_self _
    have h0' : -|c 0| ≤ c 0 := neg_abs_le _
    have hcm := hc m
    have key : ∀ i : ℤ, |i| ≤ R → i ∉ Set.Icc (c m - n) (c m + n) := by
      intro i hi
      rw [abs_le] at hi
      simp only [Set.mem_Icc, not_and, not_le]
      rcases hsgn with rfl | rfl <;> rw [hcm] <;> omega
    exact ⟨fun i hi ↦ key i (hR i (Finset.mem_insert_of_mem hi)),
      key j (hR j (Finset.mem_insert_self _ _))⟩
  -- the main estimate: `L ≤ ε` for every `ε > 0`
  have hmain : ∀ ε : ℝ≥0∞, 0 < ε → L ≤ ε := by
    intro ε hε
    obtain ⟨η, hη, hηlt⟩ := exists_pos_setLIntegral_lt_of_measure_lt (μ := ν2) (f := ginf) hGinf
      (ε := ε / 2) (by simp [ENNReal.div_eq_zero_iff, hε.ne'])
    obtain ⟨n, δ, hn, hδ0, hδ1, hδ⟩ :=
      exists_lt_of_isIrreducibleInt hρ hhom hirr hmarg Δ j hη
    set K : ℝ≥0∞ := 4 + 4 * δ⁻¹ with hK_def
    have hKtop : K ≠ ⊤ := by
      refine ENNReal.add_ne_top.2 ⟨by norm_num, ?_⟩
      exact ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.2 hδ0.ne')
    have hK0 : K ≠ 0 := by
      simp only [hK_def]
      positivity
    set ε₁ : ℝ≥0∞ := (ε / 2) / K with hε₁_def
    have hε₁ : 0 < ε₁ := by
      rw [hε₁_def]
      exact ENNReal.div_pos (by simp [ENNReal.div_eq_zero_iff, hε.ne']) hKtop
    have hDsmall : ∀ᶠ m : ℕ in Filter.atTop, D m < ε₁ :=
      hL1.eventually (eventually_lt_nhds hε₁)
    have hDsmall' : ∀ᶠ m : ℕ in Filter.atTop, D (m + n) < ε₁ :=
      (Filter.tendsto_add_atTop_nat n).eventually hDsmall
    obtain ⟨m, ⟨hsm, hjm⟩, hDm, hDmn⟩ :=
      ((hsites n).and (hDsmall.and hDsmall')).exists
    -- Step 1 applies to the pair of sites `c (m + n)`, `c m`
    have hb : c (m + n) ∉ Finset.Ioo (c m - n) (c m + n) := by
      have h1 : c (m + n) = c m + sgn * n := by
        rw [hc (m + n), hc m]
        push_cast
        ring
      simp only [Finset.mem_Ioo, not_and, not_lt]
      rcases hsgn with rfl | rfl <;> rw [h1] <;> omega
    have hstep1 := lintegral_phiBar_mul_le (ν := ν) (ρ := ρ) (γ := γ) (μ := μ) hγ hρ hM hμ hn
      (b := c (m + n)) (b' := c m) (j := j) (Δ := Δ) hsm hb hjm (hFmeas (m + n)) (hFmeas m)
      (hFdep (m + n)) (hFdep m)
    -- Step 3
    set S : Set ((ℤ → E) × (ℤ → E)) := {p | phiBar ν ρ n (c m) p < δ} with hS_def
    have hSmeas : MeasurableSet S := measurableSet_lt (measurable_phiBar hρ n (c m))
        measurable_const
    have hSsmall : ν2 S < η := hδ (c m)
      (by rintro rfl; exact hjm (by simp only [Set.mem_Icc]; omega))
      (by rintro rfl; exact hjm (by simp only [Set.mem_Icc]; omega))
    -- (a) the part where `φ̄` is large
    have hpartA : ∫⁻ p in Sᶜ, g (m + n) p ∂ν2 ≤ δ⁻¹ * (2 * (D (m + n) + D m)) := by
      have h1 : ∫⁻ p in Sᶜ, g (m + n) p ∂ν2
          ≤ ∫⁻ p in Sᶜ, δ⁻¹ * (phiBar ν ρ n (c m) p * g (m + n) p) ∂ν2 := by
        refine setLIntegral_mono' hSmeas.compl fun p hp ↦ ?_
        simp only [hS_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hp
        calc g (m + n) p = δ⁻¹ * δ * g (m + n) p := by
              rw [ENNReal.inv_mul_cancel hδ0.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top hδ1),
                one_mul]
          _ ≤ δ⁻¹ * (phiBar ν ρ n (c m) p * g (m + n) p) := by
              rw [mul_assoc]
              gcongr
      have h2 : ∫⁻ p in Sᶜ, δ⁻¹ * (phiBar ν ρ n (c m) p * g (m + n) p) ∂ν2
          ≤ δ⁻¹ * ∫⁻ p, phiBar ν ρ n (c m) p * g (m + n) p ∂ν2 :=
        le_trans (setLIntegral_le_lintegral (μ := ν2) Sᶜ
            (fun p ↦ δ⁻¹ * (phiBar ν ρ n (c m) p * g (m + n) p)))
          (le_of_eq (lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hδ0.ne')))
      refine le_trans (le_trans h1 h2) ?_
      gcongr
      refine le_trans hstep1 ?_
      gcongr
      calc ∫⁻ σ, ENNReal.ofReal |F (m + n) σ - F m σ| ∂v
          ≤ ∫⁻ σ, (ENNReal.ofReal |F (m + n) σ - Finf σ|
              + ENNReal.ofReal |F m σ - Finf σ|) ∂v := by
            refine lintegral_mono fun σ ↦ ?_
            rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hab := abs_sub_le (F (m + n) σ) (Finf σ) (F m σ)
            rw [abs_sub_comm (Finf σ) (F m σ)] at hab
            exact hab
        _ = D (m + n) + D m :=
            lintegral_add_left (measurable_ofReal_abs_sub (hFmeas (m + n)) hFinfmeas) _
    -- (b) the part where `φ̄` is small
    have hpartB : ∫⁻ p in S, g (m + n) p ∂ν2 ≤ ε / 2 + 2 * D (m + n) := by
      have hptwise : ∀ p, g (m + n) p ≤ ginf p + (ENNReal.ofReal |F (m + n) p.1 - Finf p.1|
          + ENNReal.ofReal |F (m + n) p.2 - Finf p.2|) := by
        intro p
        rw [hg_def, hginf_def]
        simp only
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
          ← ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := abs_sub_le (F (m + n) p.1) (Finf p.1) (F (m + n) p.2)
        have h2 := abs_sub_le (Finf p.1) (Finf p.2) (F (m + n) p.2)
        rw [abs_sub_comm (Finf p.2) (F (m + n) p.2)] at h2
        linarith
      calc ∫⁻ p in S, g (m + n) p ∂ν2
          ≤ ∫⁻ p in S, (ginf p + (ENNReal.ofReal |F (m + n) p.1 - Finf p.1|
              + ENNReal.ofReal |F (m + n) p.2 - Finf p.2|)) ∂ν2 :=
            lintegral_mono fun p ↦ hptwise p
        _ = (∫⁻ p in S, ginf p ∂ν2) + ∫⁻ p in S, (ENNReal.ofReal |F (m + n) p.1 - Finf p.1|
              + ENNReal.ofReal |F (m + n) p.2 - Finf p.2|) ∂ν2 :=
            lintegral_add_left hginfm _
        _ ≤ (ε / 2) + ∫⁻ p, (ENNReal.ofReal |F (m + n) p.1 - Finf p.1|
              + ENNReal.ofReal |F (m + n) p.2 - Finf p.2|) ∂ν2 := by
            exact add_le_add (hηlt S hSsmall).le
              (setLIntegral_le_lintegral (μ := ν2) S _)
        _ = ε / 2 + 2 * D (m + n) := by
            rw [lintegral_add_left (measurable_ofReal_abs_sub (hF1 (m + n)) hFinf1),
              lintegral_fst_condSelfCoupling hmle
                (measurable_ofReal_abs_sub (hFmeas (m + n)) hFinfmeas),
              lintegral_snd_condSelfCoupling hmle
                (measurable_ofReal_abs_sub (hFmeas (m + n)) hFinfmeas), two_mul]
    -- combine
    have hG : ∫⁻ p, g (m + n) p ∂ν2 ≤ ε / 2 + 2 * D (m + n) + δ⁻¹ * (2 * (D (m + n) + D m)) := by
      rw [← lintegral_add_compl _ hSmeas]
      gcongr
    calc L ≤ 2 * D (m + n) + ∫⁻ p, g (m + n) p ∂ν2 := hLbound (m + n)
      _ ≤ 2 * D (m + n) + (ε / 2 + 2 * D (m + n) + δ⁻¹ * (2 * (D (m + n) + D m))) := by gcongr
      _ ≤ 2 * ε₁ + (ε / 2 + 2 * ε₁ + δ⁻¹ * (2 * (ε₁ + ε₁))) := by
          have h1 : D (m + n) ≤ ε₁ := hDmn.le
          have h2 : D m ≤ ε₁ := hDm.le
          gcongr
      _ = ε / 2 + K * ε₁ := by rw [hK_def]; ring
      _ ≤ ε / 2 + ε / 2 := by
          gcongr
          rw [hε₁_def, ENNReal.mul_div_cancel' (fun h ↦ absurd h hK0) (fun h ↦ absurd h hKtop)]
      _ = ε := ENNReal.add_halves ε
  -- conclude
  have hL0 : L = 0 := by
    by_contra hne
    have hpos : 0 < L := pos_iff_ne_zero.2 hne
    exact absurd (hmain (L / 2) (ENNReal.div_pos hne (by norm_num)))
      (not_le.2 (ENNReal.half_lt_self hne hLtop))
  filter_upwards [(lintegral_eq_zero_iff
    (measurable_ofReal_abs_sub hFinfmeas (hEmeas Finf))).1 (hL_def ▸ hL0)] with σ hσ
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hσ
  exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm hσ (abs_nonneg _)))

/-! ### Georgii (10.25): shift-invariant Gibbs measures are Markov chains -/

omit [StandardBorelSpace E] [IsProbabilityMeasure μ] in
/-- All one-dimensional marginals of a shift-invariant random field coincide. -/
lemma map_eval_eq_of_measurePreserving_shift
    (hshift : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ μ) (i : ℤ) :
    μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)) := by
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.map_apply (measurable_pi_apply i) hA,
    Measure.map_apply (measurable_pi_apply (0 : ℤ)) hA]
  have hpre : (shift E (-i)).toFun ⁻¹' ((fun ω : ℤ → E ↦ ω (0 : ℤ)) ⁻¹' A)
      = (fun ω : ℤ → E ↦ ω i) ⁻¹' A := by
    ext ω
    simp
  rw [← hpre, (hshift (-i)).measure_preimage
    ((measurable_pi_apply (0 : ℤ) hA).nullMeasurableSet)]

omit [StandardBorelSpace E] [IsProbabilityMeasure μ] in
/-- A Markov chain whose law is shift-invariant is a **homogeneous** Markov chain: the family
`(P_i)_{i ∈ ℤ}` may be replaced by the single kernel `P_0`. -/
theorem IsMarkovChain.const_zero_of_measurePreserving_shift {P : ℤ → Kernel E E}
    [∀ k, IsMarkovKernel (P k)] (hchain : IsMarkovChain P μ)
    (hshift : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    IsMarkovChain (fun _ ↦ P 0) μ := by
  classical
  have hmarg := map_eval_eq_of_measurePreserving_shift hshift
  -- the two-coordinate marginals of `μ` do not depend on the position
  have hpair : ∀ (i : ℤ) (A B : Set E), MeasurableSet A → MeasurableSet B →
      μ ((fun σ : ℤ → E ↦ σ i) ⁻¹' A ∩ (fun σ : ℤ → E ↦ σ (i - 1)) ⁻¹' B)
        = μ ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A ∩ (fun σ : ℤ → E ↦ σ (-1 : ℤ)) ⁻¹' B) := by
    intro i A B hA hB
    have hpre : (shift E (-i)).toFun ⁻¹' ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A
        ∩ (fun σ : ℤ → E ↦ σ (-1 : ℤ)) ⁻¹' B)
        = (fun σ : ℤ → E ↦ σ i) ⁻¹' A ∩ (fun σ : ℤ → E ↦ σ (i - 1)) ⁻¹' B := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_inter_iff, shift_toFun_apply, sub_neg_eq_add,
        zero_add]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by simpa [show (-1 : ℤ) + i = i - 1 by ring] using h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by simpa [show (-1 : ℤ) + i = i - 1 by ring] using h2⟩
    have hms : MeasurableSet ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A
        ∩ (fun σ : ℤ → E ↦ σ (-1 : ℤ)) ⁻¹' B) :=
      (measurable_pi_apply (0 : ℤ) hA).inter (measurable_pi_apply (-1 : ℤ) hB)
    rw [← hpre, (hshift (-i)).measure_preimage hms.nullMeasurableSet]
  have hprob := hchain.isProbabilityMeasure
  rw [isMarkovChain_iff_forall_measure_inter]
  intro i A hA t ht
  -- `P i · A` and `P 0 · A` agree almost surely for the common one-dimensional marginal
  have hind : ∀ (Q : Kernel E E) (a : ℤ) (B : Set E), MeasurableSet B →
      ∫⁻ x in B, Q x A ∂(μ.map fun ω : ℤ → E ↦ ω a)
        = ∫⁻ σ in (fun σ : ℤ → E ↦ σ a) ⁻¹' B, Q (σ a) A ∂μ := by
    intro Q a B hB
    have hf : Measurable (B.indicator fun x ↦ Q x A) :=
      (Kernel.measurable_coe Q hA).indicator hB
    rw [← lintegral_indicator hB, ← lintegral_indicator (measurable_pi_apply a hB),
      lintegral_map hf (measurable_pi_apply a)]
    refine lintegral_congr fun σ ↦ ?_
    by_cases hσ : σ a ∈ B
    · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem (by exact hσ)]
    · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem (by exact hσ)]
  have hae : (fun x ↦ P i x A) =ᵐ[μ.map fun ω ↦ ω (i - 1)] fun x ↦ P 0 x A := by
    refine ae_eq_of_forall_setLIntegral_eq_of_le (m := inferInstance) le_rfl
      (Kernel.measurable_coe (P i) hA) (Kernel.measurable_coe (P 0) hA) fun B hB ↦ ?_
    have h1 : ∫⁻ x in B, P i x A ∂(μ.map fun ω ↦ ω (i - 1))
        = μ ((fun σ : ℤ → E ↦ σ i) ⁻¹' A ∩ (fun σ : ℤ → E ↦ σ (i - 1)) ⁻¹' B) := by
      rw [hind (P i) (i - 1) B hB, hchain.measure_preimage_inter i hA
        (t := (fun σ : ℤ → E ↦ σ (i - 1)) ⁻¹' B)
        (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E)
          (show i - 1 ∈ Set.Iio i by simp) hB)]
    have h2 : ∫⁻ x in B, P 0 x A ∂(μ.map fun ω ↦ ω (i - 1))
        = μ ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A ∩ (fun σ : ℤ → E ↦ σ (-1 : ℤ)) ⁻¹' B) := by
      rw [hmarg (i - 1), ← hmarg (-1 : ℤ), hind (P 0) (-1 : ℤ) B hB]
      have := hchain.measure_preimage_inter (0 : ℤ) hA
        (t := (fun σ : ℤ → E ↦ σ (-1 : ℤ)) ⁻¹' B)
        (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E)
          (show (-1 : ℤ) ∈ Set.Iio (0 : ℤ) by simp) hB)
      simp only [zero_sub] at this
      rw [this]
    rw [h1, h2, hpair i A B hA hB]
  have haeμ : (fun σ : ℤ → E ↦ P i (σ (i - 1)) A) =ᵐ[μ] fun σ ↦ P 0 (σ (i - 1)) A :=
    (ae_map_iff (μ := μ) (f := fun ω : ℤ → E ↦ ω (i - 1))
      (measurable_pi_apply (i - 1)).aemeasurable
      (p := fun x ↦ P i x A = P 0 x A)
      (measurableSet_eq_fun (Kernel.measurable_coe (P i) hA)
        (Kernel.measurable_coe (P 0) hA))).1 hae
  rw [hchain.measure_preimage_inter i hA ht]
  exact setLIntegral_congr_fun_ae (cylinderEvents_le_pi _ ht) (haeμ.mono fun σ hσ _ ↦ hσ)

/-- **Georgii's verification of (10.19)** for a shift-invariant Gibbs measure of an irreducible
homogeneous Markovian `λ`-modification: the limit `ρ^j_{]j-1,∞[}` is `ν_j`-almost surely a
measurable function of the two coordinates `j - 1`, `j`.

This is Proposition (10.26) applied to the backward martingale `F_m = ρ^j_{]j-1, j+1+m[}` with
`Δ = {j - 1, j}`. -/
theorem exists_ae_eq_pair_of_isIrreducibleInt
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hM : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμ : γ.IsGibbsMeasure μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ))) (j : ℤ) :
    ∃ q : E → E → ℝ, Measurable (Function.uncurry q) ∧
      (fun ω ↦ q (ω (j - 1)) (ω j)) =ᵐ[μ.bind (isssd ν {j})]
        (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal | ⨅ n : ℕ,
          cylinderEvents (X := fun _ : ℤ ↦ E)
            (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ] := by
  classical
  set v : Measure (ℤ → E) := μ.bind (isssd ν {j}) with hv_def
  set g : (ℤ → E) → ℝ := fun ω ↦ (ρ {j} ω).toReal with hg_def
  set ℱ : ℕ → MeasurableSpace (ℤ → E) := fun n ↦ cylinderEvents (X := fun _ : ℤ ↦ E)
    (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ with hℱ_def
  set Finf : (ℤ → E) → ℝ := v[g | ⨅ n, ℱ n] with hFinf_def
  set F : ℕ → (ℤ → E) → ℝ :=
    fun m ω ↦ (marginalDensity ν ρ (Finset.Ioo (j - 1) (j + 1 + m)) j ω).toReal with hF_def
  have hjmem : ∀ m : ℕ, j ∈ Finset.Ioo (j - 1) (j + 1 + (m : ℤ)) := fun m ↦ by
    simp only [Finset.mem_Ioo]
    omega
  have hFmeas : ∀ m, Measurable (F m) := fun m ↦
    (measurable_marginalDensity (hρ _) j).ennreal_toReal
  have hFinfmeas : Measurable Finf :=
    (stronglyMeasurable_condExp.mono ((iInf_le ℱ 0).trans cylinderEvents_le_pi)).measurable
  have hFcond : ∀ m, F m =ᵐ[v] v[g | ℱ m] := fun m ↦
    hμ.toReal_marginalDensity_ae_eq_condExp hγ hρ (hjmem m)
  have hFint : ∀ m, Integrable (F m) v := fun m ↦
    integrable_toReal_of_lintegral_ne_top (measurable_marginalDensity (hρ _) j).aemeasurable
      (by rw [hμ.lintegral_marginalDensity hγ hρ (hjmem m)]; exact ENNReal.one_ne_top)
  have hFdep : ∀ m : ℕ, DependsOn (F m)
      ((({j - 1, j} : Finset ℤ) : Set ℤ) ∪ {j + 1 + (m : ℤ)}) := by
    intro m
    refine ((measurable_marginalDensity_Ioo hρ hM (i := j - 1) (k := j + 1 + (m : ℤ))
      (by omega) (by omega)).ennreal_toReal.dependsOn_of_cylinderEvents).mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have hL1 : Filter.Tendsto (fun m ↦ ∫⁻ σ, ENNReal.ofReal |F m σ - Finf σ| ∂v)
      Filter.atTop (nhds 0) := by
    refine (tendsto_eLpNorm_condExp_of_antitone (μ := v) g
      (antitone_cylinderEvents_compl_erase (j - 1) j)
      (fun _ ↦ cylinderEvents_le_pi)).congr fun m ↦ ?_
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr_ae ?_
    filter_upwards [hFcond m] with σ hσ
    simp only [Pi.sub_apply, Real.enorm_eq_ofReal_abs, hσ, hFinf_def, hℱ_def]
  have h1026 := ae_eq_condExp_of_tendsto hγ hρ hM hhom hirr hμ hmarg
    (Δ := ({j - 1, j} : Finset ℤ)) (j := j) (c := fun m : ℕ ↦ j + 1 + (m : ℤ)) (sgn := 1)
    (Or.inl rfl) (fun m ↦ by push_cast; ring) hFmeas hFinfmeas hFdep hFint integrable_condExp hL1
  have hcoe : ((({j - 1, j} : Finset ℤ) : Set ℤ)) = ({j - 1, j} : Set ℤ) := by simp
  obtain ⟨q, hqmeas, hq⟩ := exists_eq_pair_of_measurable_cylinderEvents (E := E)
    (a := j - 1) (b := j) (by omega)
    (g := v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) ((({j - 1, j} : Finset ℤ) : Set ℤ))])
    (hcoe ▸ (stronglyMeasurable_condExp (m := cylinderEvents (X := fun _ : ℤ ↦ E)
      ((({j - 1, j} : Finset ℤ) : Set ℤ))) (μ := v) (f := Finf)).measurable)
  refine ⟨q, hqmeas, ?_⟩
  filter_upwards [h1026] with σ hσ
  rw [← hq σ, ← hσ]

/-! ### Georgii, Theorem (10.25) -/

/-- **Georgii, Theorem (10.25).** Let `(E, 𝓔)` be standard Borel, `λ` an a priori probability
measure, `ρ` an irreducible homogeneous Markovian `λ`-modification on `ℤ` and `γ = ρλ`. Then
every shift-invariant `μ ∈ 𝒢_Θ(γ)` is a Markov chain for a *single* transition kernel
`P(x, ·) = p(x, ·) λ` with a measurable density `p`. -/
theorem exists_isMarkovChain_of_measurePreserving_shift
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hM : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμ : γ.IsGibbsMeasure μ)
    (hshift : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    ∃ (p : E → E → ℝ≥0∞) (P : Kernel E E), Measurable (Function.uncurry p) ∧
      (∀ x, P x = ν.withDensity (p x)) ∧ IsMarkovKernel P ∧ IsMarkovChain (fun _ ↦ P) μ := by
  have hmarg := map_eval_eq_of_measurePreserving_shift hshift
  obtain ⟨p, P, hpmeas, hPapply, hPmarkov, -, hchain⟩ :=
    IsGibbsMeasure.exists_isMarkovChain_of_forall_exists_ae_eq hγ hρ hμ
      (exists_ae_eq_pair_of_isIrreducibleInt hγ hρ hM hhom hirr hμ hmarg)
  have _ : ∀ k, IsMarkovKernel (P k) := hPmarkov
  exact ⟨p 0, P 0, hpmeas 0, hPapply 0, hPmarkov 0,
    hchain.const_zero_of_measurePreserving_shift hshift⟩

end Step1

/-! ## Georgii §10.3: uniqueness of the shift-invariant Markov field

Throughout, `μ` is a shift-invariant Gibbs measure for `γ = ρλ` with `ρ` an irreducible
homogeneous Markovian `λ`-modification, and `P(x, ·) = p(x, ·) λ` is the transition kernel
provided by Theorem (10.25). The `n`-step densities `p^n` are `Kernel.densityPow ν p n`
(Georgii **(10.29)**). -/

section Chain

variable {P : ℤ → Kernel E E}

/-- One step of a Markov chain, in `ℝ≥0∞`-integral form: for `t ∈ 𝓕_{]-∞,i[}` and measurable
`f ≥ 0`, `∫_t f(σ_i) dμ = ∫_t P_i(σ_{i-1}, f) dμ`. -/
theorem IsMarkovChain.setLIntegral_comp_eval [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ)
    (i : ℤ) {f : E → ℝ≥0∞} (hf : Measurable f) {t : Set (ℤ → E)}
    (ht : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iio i)] t) :
    ∫⁻ σ in t, f (σ i) ∂μ = ∫⁻ σ in t, (∫⁻ y, f y ∂(P i (σ (i - 1)))) ∂μ := by
  have hprob := h.isProbabilityMeasure
  have hker : Measurable fun σ : ℤ → E ↦ P i (σ (i - 1)) :=
    (P i).measurable.comp (measurable_pi_apply (i - 1))
  have hm : (μ.restrict t).map (fun σ : ℤ → E ↦ σ i)
      = (μ.restrict t).bind (fun σ ↦ P i (σ (i - 1))) := by
    ext A hA
    rw [Measure.map_apply (measurable_pi_apply i) hA,
      Measure.restrict_apply (measurable_pi_apply i hA),
      Measure.bind_apply hA hker.aemeasurable, h.measure_preimage_inter i hA ht]
  rw [← lintegral_map hf (measurable_pi_apply i), hm,
    Measure.lintegral_bind hker.aemeasurable hf.aemeasurable]

/-- The `n`-step transition property of a homogeneous Markov chain: for `t ∈ 𝓕_{]-∞,i-n]}`,
`μ({σ_i ∈ A} ∩ t) = ∫_t P^n(σ_{i-n}, A) dμ`. -/
theorem IsMarkovChain.measure_preimage_inter_pow {Q : Kernel E E} [IsMarkovKernel Q]
    (h : IsMarkovChain (fun _ ↦ Q) μ) (i : ℤ) (n : ℕ) {A : Set E} (hA : MeasurableSet A)
    {t : Set (ℤ → E)}
    (ht : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (i - n))] t) :
    μ ((fun σ : ℤ → E ↦ σ i) ⁻¹' A ∩ t) = ∫⁻ σ in t, (Q ^ n) (σ (i - n)) A ∂μ := by
  have hprob := h.isProbabilityMeasure
  induction n generalizing t with
  | zero =>
      simp only [Nat.cast_zero, sub_zero, pow_zero] at ht ⊢
      have hmeas : MeasurableSet t := cylinderEvents_le_pi _ ht
      have hfun : ∀ σ : ℤ → E, ((1 : Kernel E E) (σ i)) A
          = ((fun σ : ℤ → E ↦ σ i) ⁻¹' A).indicator (1 : (ℤ → E) → ℝ≥0∞) σ := by
        intro σ
        change (Kernel.id (σ i)) A = _
        rw [Kernel.id_apply, Measure.dirac_apply' _ hA]
        by_cases hσ : σ i ∈ A <;> simp [Set.indicator, hσ]
      rw [lintegral_congr hfun, lintegral_indicator (measurable_pi_apply i hA)]
      simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply_univ]
      rw [Measure.restrict_apply (measurable_pi_apply i hA)]
  | succ n ih =>
      have hcast : i - ((n + 1 : ℕ) : ℤ) = i - (n : ℤ) - 1 := by push_cast; ring
      have htIio : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
          (Set.Iio (i - (n : ℤ)))] t := by
        refine cylinderEvents_mono ?_ _ ht
        intro x hx
        simp only [Set.mem_Iic] at hx
        simp only [Set.mem_Iio]
        omega
      have htIic : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
          (Set.Iic (i - (n : ℤ)))] t :=
        cylinderEvents_mono Set.Iio_subset_Iic_self _ htIio
      have hf : Measurable fun y ↦ (Q ^ n) y A := Kernel.measurable_coe _ hA
      have key : ∀ z : E, (Q ^ (n + 1)) z A = ∫⁻ y, (Q ^ n) y A ∂(Q z) := fun z ↦ by
        have h1 := Kernel.pow_add_apply_eq_lintegral Q 1 n z hA
        rwa [pow_one, add_comm 1 n] at h1
      rw [ih htIic, h.setLIntegral_comp_eval (i - (n : ℤ)) hf htIio]
      refine lintegral_congr fun σ ↦ ?_
      rw [hcast, key]

end Chain

/-! ### Georgii (10.31)–(10.32): the invariant one-dimensional marginal -/

section Marginal

variable {p : E → E → ℝ≥0∞}

/-- Resampling the single coordinate `j` inside a set which does not constrain `j`.
(Intended home: next to `Specification.lintegral_bind_isssd_singleton`.) -/
lemma setLIntegral_bind_isssd_singleton {j : ℤ} {D : Set (ℤ → E)}
    (hD : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (({j} : Set ℤ)ᶜ)] D)
    {F : (ℤ → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ σ in D, F σ ∂(μ.bind (isssd ν {j}))
      = ∫⁻ ω in D, (∫⁻ y, F (Function.update ω j y) ∂ν) ∂μ := by
  classical
  have hDm : MeasurableSet D := cylinderEvents_le_pi _ hD
  have hjD : ∀ (ω : ℤ → E) (y : E), Function.update ω j y ∈ D ↔ ω ∈ D := fun ω y ↦
    update_mem_iff_of_measurableSet_cylinderEvents hD (by simp) ω y
  have hinner : Measurable fun ω : ℤ → E ↦ ∫⁻ y, F (Function.update ω j y) ∂ν := by
    refine Measurable.lintegral_prod_right' (f := fun q : (ℤ → E) × E ↦
      F (Function.update q.1 j q.2)) ?_
    exact hF.comp measurable_update'
  rw [← lintegral_indicator hDm, lintegral_bind_isssd_singleton j (hF.indicator hDm),
    ← lintegral_indicator hDm]
  refine lintegral_congr fun ω ↦ ?_
  by_cases hω : ω ∈ D
  · rw [Set.indicator_of_mem hω]
    refine lintegral_congr fun y ↦ ?_
    rw [Set.indicator_of_mem ((hjD ω y).2 hω)]
  · rw [Set.indicator_of_notMem hω]
    refine (lintegral_congr fun y ↦ ?_).trans lintegral_zero
    rw [Set.indicator_of_notMem fun h ↦ hω ((hjD ω y).1 h)]

variable (p) in
/-- **Georgii (10.31).** The `λ`-density `r(x) = ∫ α(du) p(u, x)` of the mixture `α P` of a
kernel `P(x, ·) = p(x, ·) λ`. When `α` is `P`-invariant — which is the case for the
one-dimensional marginal `α = σ_0(μ)` of a shift-invariant Markov chain `μ` — this is the
`λ`-density of `α` itself, Georgii **(10.32)**. -/
def stationaryDensity (α : Measure E) (p : E → E → ℝ≥0∞) (x : E) : ℝ≥0∞ := ∫⁻ u, p u x ∂α

lemma measurable_stationaryDensity {α : Measure E} [SFinite α]
    (hp : Measurable (Function.uncurry p)) : Measurable (stationaryDensity α p) :=
  Measurable.lintegral_prod_right' (f := fun q : E × E ↦ p q.2 q.1)
    (hp.comp (measurable_snd.prodMk measurable_fst))

/-- **Georgii's `α P = α`**: the one-dimensional marginal of a shift-invariant Markov chain is
invariant for its transition kernel. -/
theorem IsMarkovChain.bind_map_eval_eq {Q : Kernel E E} [IsMarkovKernel Q]
    (h : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ))) :
    (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)).bind Q = μ.map fun ω : ℤ → E ↦ ω (0 : ℤ) := by
  have hprob := h.isProbabilityMeasure
  ext A hA
  have h1 : μ ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) = ∫⁻ σ, Q (σ (-1 : ℤ)) A ∂μ := by
    have h2 := h.measure_preimage_inter (0 : ℤ) hA (t := Set.univ) MeasurableSet.univ
    simpa only [Set.inter_univ, Measure.restrict_univ, zero_sub] using h2
  have h3 : ∫⁻ σ, Q (σ (-1 : ℤ)) A ∂μ
      = ∫⁻ x, Q x A ∂(μ.map fun ω : ℤ → E ↦ ω (-1 : ℤ)) :=
    (lintegral_map (Kernel.measurable_coe Q hA) (measurable_pi_apply (-1 : ℤ))).symm
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe Q hA) (measurable_pi_apply (0 : ℤ)),
    Measure.map_apply (measurable_pi_apply (0 : ℤ)) hA, h1, h3, hmarg (-1 : ℤ),
    lintegral_map (Kernel.measurable_coe Q hA) (measurable_pi_apply (0 : ℤ))]

/-- **Georgii (10.32)**, first half: the one-dimensional marginal `α` of a shift-invariant Markov
chain has the `λ`-density `r`. -/
theorem map_eval_eq_withDensity_stationaryDensity {Q : Kernel E E} [IsMarkovKernel Q]
    (h : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x)) :
    (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ))
      = ν.withDensity (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) := by
  have hprob := h.isProbabilityMeasure
  have : IsProbabilityMeasure (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℤ)).aemeasurable
  calc (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ))
      = (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)).bind Q := (h.bind_map_eval_eq hmarg).symm
    _ = ν.withDensity (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) :=
        Measure.bind_eq_withDensity_lintegral hp hQ _

end Marginal

/-! ### Georgii (10.30): the `n`-step density is a backward martingale -/

section BackwardMartingale

variable {p : E → E → ℝ≥0∞} {Q : Kernel E E}

/-- `σ ↦ p^n(σ_{-n}, σ_0)` is `𝓕_{]-∞,-n] ∪ {0}}`-measurable. -/
lemma measurable_densityPow_eval (hp : Measurable (Function.uncurry p)) (n : ℕ) :
    Measurable[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-(n : ℤ)) ∪ {0})]
      fun σ : ℤ → E ↦ Kernel.densityPow ν p n (σ (-(n : ℤ))) (σ 0) := by
  have hmemL : (-(n : ℤ)) ∈ Set.Iic (-(n : ℤ)) ∪ ({0} : Set ℤ) :=
    Set.mem_union_left _ (Set.mem_Iic.2 le_rfl)
  have hmemR : (0 : ℤ) ∈ Set.Iic (-(n : ℤ)) ∪ ({0} : Set ℤ) :=
    Set.mem_union_right _ rfl
  have h1 : Measurable[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-(n : ℤ)) ∪ {0})]
      fun σ : ℤ → E ↦ (σ (-(n : ℤ)), σ (0 : ℤ)) :=
    (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) hmemL).prodMk
      (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) hmemR)
  exact (Kernel.measurable_uncurry_densityPow hp n).comp h1

lemma measurable_densityPow_eval' (hp : Measurable (Function.uncurry p)) (n : ℕ) :
    Measurable fun σ : ℤ → E ↦ Kernel.densityPow ν p n (σ (-(n : ℤ))) (σ 0) := by
  have h1 : Measurable fun σ : ℤ → E ↦ (σ (-(n : ℤ)), σ (0 : ℤ)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  exact (Kernel.measurable_uncurry_densityPow hp n).comp h1

/-- The generating π-system for `𝓕_{]-∞,-n] ∪ {0}}`. -/
private lemma cylinderEvents_Iic_union_zero_eq_generateFrom (n : ℕ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-(n : ℤ)) ∪ {0})
      = MeasurableSpace.generateFrom
        (interSets (cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-(n : ℤ))))
          (cylinderEvents (X := fun _ : ℤ ↦ E) ({0} : Set ℤ))) := by
  rw [cylinderEvents_union]
  exact sup_eq_generateFrom_interSets _ _

/-- **Georgii (10.30)** on the generating π-system: for `B ∈ 𝓕_{]-∞,-n]}` and `A ∈ 𝓔`,
`∫_{B ∩ {σ_0 ∈ A}} p^n(σ_{-n}, σ_0) dν_0 = μ(B ∩ {σ_0 ∈ A})`. -/
theorem setLIntegral_densityPow_inter [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ) (hp : Measurable (Function.uncurry p))
    (hQ : ∀ x, Q x = ν.withDensity (p x)) {n : ℕ} (hn : 1 ≤ n)
    {B : Set (ℤ → E)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-(n : ℤ)))] B)
    {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ σ in B ∩ (fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A,
        Kernel.densityPow ν p n (σ (-(n : ℤ))) (σ 0) ∂(μ.bind (isssd ν {(0 : ℤ)}))
      = μ (B ∩ (fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) := by
  classical
  have hprob := hchain.isProbabilityMeasure
  have hnZ : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hBm : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hSm : MeasurableSet ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) := measurable_pi_apply 0 hA
  have hn0 : (0 : ℤ) ∉ Set.Iic (-(n : ℤ)) := by
    simp only [Set.mem_Iic, not_le]
    omega
  have hne : (-(n : ℤ)) ≠ 0 := by omega
  have hgm := measurable_densityPow_eval' (ν := ν) hp n
  rw [← lintegral_indicator (hBm.inter hSm),
    lintegral_bind_isssd_singleton (0 : ℤ) (hgm.indicator (hBm.inter hSm))]
  have hstep : ∀ ω : ℤ → E,
      (∫⁻ y, (B ∩ (fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A).indicator
          (fun σ : ℤ → E ↦ Kernel.densityPow ν p n (σ (-(n : ℤ))) (σ 0))
          (Function.update ω (0 : ℤ) y) ∂ν)
        = B.indicator (fun ω : ℤ → E ↦ (Q ^ n) (ω (-(n : ℤ))) A) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      have hupd : ∀ y : E, Function.update ω (0 : ℤ) y ∈ B := fun y ↦
        (update_mem_iff_of_measurableSet_cylinderEvents hB hn0 ω y).2 hω
      have hpt : ∀ y : E, (B ∩ (fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A).indicator
          (fun σ : ℤ → E ↦ Kernel.densityPow ν p n (σ (-(n : ℤ))) (σ 0))
          (Function.update ω (0 : ℤ) y)
          = A.indicator (fun y ↦ Kernel.densityPow ν p n (ω (-(n : ℤ))) y) y := by
        intro y
        have hy0 : (Function.update ω (0 : ℤ) y) (0 : ℤ) = y := Function.update_self _ _ _
        have hyn : (Function.update ω (0 : ℤ) y) (-(n : ℤ)) = ω (-(n : ℤ)) :=
          Function.update_of_ne hne _ _
        by_cases hy : y ∈ A
        · have hmem : Function.update ω (0 : ℤ) y ∈ B ∩ (fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A := by
            refine ⟨hupd y, ?_⟩
            simp only [Set.mem_preimage, hy0]
            exact hy
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hy, hy0, hyn]
        · refine (Set.indicator_of_notMem ?_ _).trans (Set.indicator_of_notMem hy _).symm
          rintro ⟨-, hc⟩
          exact hy (by simpa only [Set.mem_preimage, hy0] using hc)
      rw [lintegral_congr hpt, lintegral_indicator hA, ← withDensity_apply _ hA,
        ← Kernel.pow_apply_eq_withDensity_densityPow hp hQ hn]
    · rw [Set.indicator_of_notMem hω]
      refine (lintegral_congr fun y ↦ ?_).trans lintegral_zero
      exact Set.indicator_of_notMem
        (fun hc ↦ hω ((update_mem_iff_of_measurableSet_cylinderEvents hB hn0 ω y).1 hc.1)) _
  rw [lintegral_congr hstep, lintegral_indicator hBm]
  have hBIic : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
      (Set.Iic ((0 : ℤ) - (n : ℤ)))] B := by rwa [zero_sub]
  have hkey := hchain.measure_preimage_inter_pow (0 : ℤ) n hA hBIic
  rw [zero_sub] at hkey
  rw [Set.inter_comm, hkey]

/-- **Georgii (10.30).** `p^n(σ_{-n}, σ_0)` integrates to `μ` over every
`𝓕_{]-∞,-n] ∪ {0}}`-measurable set. -/
theorem setLIntegral_densityPow_eq_measure [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ) (hp : Measurable (Function.uncurry p))
    (hQ : ∀ x, Q x = ν.withDensity (p x)) {n : ℕ} (hn : 1 ≤ n) {D : Set (ℤ → E)}
    (hD : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-(n : ℤ)) ∪ {0})] D) :
    ∫⁻ σ in D, Kernel.densityPow ν p n (σ (-(n : ℤ))) (σ 0) ∂(μ.bind (isssd ν {(0 : ℤ)}))
      = μ D := by
  classical
  have hprob := hchain.isProbabilityMeasure
  have hgm := measurable_densityPow_eval' (ν := ν) hp n
  set W : Measure (ℤ → E) := (μ.bind (isssd ν {(0 : ℤ)})).withDensity
    (fun σ ↦ Kernel.densityPow ν p n (σ (-(n : ℤ))) (σ 0)) with hW_def
  have hWapply : ∀ {D : Set (ℤ → E)}, MeasurableSet D →
      W D = ∫⁻ σ in D, Kernel.densityPow ν p n (σ (-(n : ℤ))) (σ 0)
        ∂(μ.bind (isssd ν {(0 : ℤ)})) := fun hD ↦ withDensity_apply _ hD
  have huniv : W Set.univ = 1 := by
    have h1 := setLIntegral_densityPow_inter hchain hp hQ hn
      (B := Set.univ) (MeasurableSet.univ) (A := Set.univ) MeasurableSet.univ
    rw [hWapply MeasurableSet.univ]
    simpa using h1
  have hWprob : IsProbabilityMeasure W := ⟨huniv⟩
  have hle : cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-(n : ℤ)) ∪ {0})
      ≤ MeasurableSpace.pi := cylinderEvents_le_pi
  have hmain : ∀ D, MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
      (Set.Iic (-(n : ℤ)) ∪ {0})] D → W D = μ D := by
    refine MeasurableSpace.induction_on_inter
      (m := cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-(n : ℤ)) ∪ {0}))
      (C := fun D _ ↦ W D = μ D) (cylinderEvents_Iic_union_zero_eq_generateFrom (E := E) n)
      (isPiSystem_interSets _ _) (by simp) (fun t ht ↦ ?_) (fun t ht hts ↦ ?_)
      (fun s hd hs hts ↦ ?_)
    · obtain ⟨B, C, hB, hC, rfl⟩ := ht
      obtain ⟨A, hA, rfl⟩ := measurableSet_cylinderEvents_singleton_iff.1 hC
      rw [hWapply ((cylinderEvents_le_pi _ hB).inter (measurable_pi_apply 0 hA))]
      exact setLIntegral_densityPow_inter hchain hp hQ hn hB hA
    · rw [prob_compl_eq_one_sub (μ := W) (hle _ ht), prob_compl_eq_one_sub (μ := μ) (hle _ ht),
        hts]
    · rw [measure_iUnion hd fun i ↦ hle _ (hs i), measure_iUnion hd fun i ↦ hle _ (hs i)]
      exact tsum_congr hts
  rw [← hWapply (hle _ hD)]
  exact hmain D hD

end BackwardMartingale

/-! ### The single-site marginal of `ν_j`, and Georgii (10.32) as a conditional expectation -/

section SingleSite

variable {p : E → E → ℝ≥0∞} {Q : Kernel E E}

/-- Under `ν_j = μ λ_{{j}}` the coordinate `j` is `λ`-distributed. -/
lemma setLIntegral_eval_bind_isssd_singleton [IsProbabilityMeasure μ] (j : ℤ)
    {F : E → ℝ≥0∞} (hF : Measurable F) {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ σ in (fun σ : ℤ → E ↦ σ j) ⁻¹' A, F (σ j) ∂(μ.bind (isssd ν {j}))
      = ∫⁻ y in A, F y ∂ν := by
  classical
  have hSm : MeasurableSet ((fun σ : ℤ → E ↦ σ j) ⁻¹' A) := measurable_pi_apply j hA
  have hFm : Measurable fun σ : ℤ → E ↦ F (σ j) := hF.comp (measurable_pi_apply j)
  rw [← lintegral_indicator hSm, lintegral_bind_isssd_singleton j (hFm.indicator hSm),
    ← lintegral_indicator hA]
  refine (lintegral_congr fun ω ↦ ?_).trans (by rw [lintegral_const, measure_univ, mul_one])
  refine lintegral_congr fun y ↦ ?_
  have hy0 : (Function.update ω j y) j = y := Function.update_self _ _ _
  by_cases hy : y ∈ A
  · rw [Set.indicator_of_mem (by simp only [Set.mem_preimage, hy0]; exact hy),
      Set.indicator_of_mem hy, hy0]
  · rw [Set.indicator_of_notMem (by simp only [Set.mem_preimage, hy0]; exact hy),
      Set.indicator_of_notMem hy]

lemma lintegral_eval_bind_isssd_singleton [IsProbabilityMeasure μ] (j : ℤ)
    {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ σ, F (σ j) ∂(μ.bind (isssd ν {j})) = ∫⁻ y, F y ∂ν := by
  have h := setLIntegral_eval_bind_isssd_singleton (μ := μ) (ν := ν) j hF MeasurableSet.univ
  simpa using h

/-- **Georgii (10.30)** as a conditional expectation: `p^n(σ_{-n}, σ_0)` is a version of
`ν_0(ρ_{{0}} | 𝓕_{]-∞,-n] ∪ {0}})`. -/
theorem toReal_densityPow_ae_eq_condExp [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hμ : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ) (hp : Measurable (Function.uncurry p))
    (hQ : ∀ x, Q x = ν.withDensity (p x)) {n : ℕ} (hn : 1 ≤ n) :
    (fun σ : ℤ → E ↦ (Kernel.densityPow ν p n (σ (-(n : ℤ))) (σ 0)).toReal)
      =ᵐ[μ.bind (isssd ν {(0 : ℤ)})]
      (μ.bind (isssd ν {(0 : ℤ)}))[fun σ ↦ (ρ {(0 : ℤ)} σ).toReal |
        cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-(n : ℤ)) ∪ {0})] := by
  refine toReal_ae_eq_condExp_toReal_of_forall_setLIntegral_eq cylinderEvents_le_pi
    (hρ {(0 : ℤ)}).aemeasurable (measurable_densityPow_eval hp n) ?_ ?_ fun t ht ↦ ?_
  · rw [hμ.lintegral_bind_isssd hγ hρ {(0 : ℤ)}]; exact ENNReal.one_ne_top
  · have h := setLIntegral_densityPow_eq_measure hchain hp hQ hn
      (D := Set.univ) MeasurableSet.univ
    rw [Measure.restrict_univ] at h
    rw [h, measure_univ]
    exact ENNReal.one_ne_top
  · rw [setLIntegral_densityPow_eq_measure hchain hp hQ hn ht,
      hμ.measure_eq_setLIntegral_bind_isssd hγ hρ {(0 : ℤ)} (cylinderEvents_le_pi _ ht)]

/-- **Georgii (10.32)**, second half: `r(σ_0) = ν_0(ρ_{{0}} | 𝓕_{{0}})` `ν_0`-almost surely. -/
theorem toReal_stationaryDensity_ae_eq_condExp [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hμ : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x)) :
    (fun σ : ℤ → E ↦ (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p (σ 0)).toReal)
      =ᵐ[μ.bind (isssd ν {(0 : ℤ)})]
      (μ.bind (isssd ν {(0 : ℤ)}))[fun σ ↦ (ρ {(0 : ℤ)} σ).toReal |
        cylinderEvents (X := fun _ : ℤ ↦ E) ({0} : Set ℤ)] := by
  classical
  have hαprob : IsProbabilityMeasure (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℤ)).aemeasurable
  set α : Measure E := μ.map fun ω : ℤ → E ↦ ω (0 : ℤ) with hα_def
  have hrmeas : Measurable (stationaryDensity α p) := measurable_stationaryDensity hp
  have hαr : α = ν.withDensity (stationaryDensity α p) :=
    map_eval_eq_withDensity_stationaryDensity hchain hmarg hp hQ
  have hkey : ∀ {A : Set E}, MeasurableSet A →
      ∫⁻ σ in (fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A, stationaryDensity α p (σ 0)
        ∂(μ.bind (isssd ν {(0 : ℤ)})) = μ ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) := by
    intro A hA
    rw [setLIntegral_eval_bind_isssd_singleton (0 : ℤ) hrmeas hA, ← withDensity_apply _ hA,
      ← hαr, hα_def, Measure.map_apply (measurable_pi_apply (0 : ℤ)) hA]
  refine toReal_ae_eq_condExp_toReal_of_forall_setLIntegral_eq cylinderEvents_le_pi
    (hρ {(0 : ℤ)}).aemeasurable
    ((hrmeas.comp (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) rfl)) :
      Measurable[cylinderEvents (X := fun _ : ℤ ↦ E) ({0} : Set ℤ)] _) ?_ ?_ fun t ht ↦ ?_
  · rw [hμ.lintegral_bind_isssd hγ hρ {(0 : ℤ)}]; exact ENNReal.one_ne_top
  · have h := hkey (A := Set.univ) MeasurableSet.univ
    rw [Set.preimage_univ, Measure.restrict_univ] at h
    rw [h, measure_univ]
    exact ENNReal.one_ne_top
  · obtain ⟨A, hA, rfl⟩ := measurableSet_cylinderEvents_singleton_iff.1 ht
    rw [hkey hA, hμ.measure_eq_setLIntegral_bind_isssd hγ hρ {(0 : ℤ)}
      (measurable_pi_apply (0 : ℤ) hA)]

end SingleSite

/-! ### Georgii, Theorem (10.34): the ergodic theorem for `P` -/

section ErgodicTheorem

variable {p : E → E → ℝ≥0∞} {Q : Kernel E E}

/-- Under `ν_0 = μ λ_{{0}}` the pair `(σ_i, σ_0)` (`i ≠ 0`) has law `α ⊗ λ`, where `α` is the
common one-dimensional marginal of the shift-invariant `μ`. -/
lemma lintegral_pair_bind_isssd_singleton_zero [IsProbabilityMeasure μ] {i : ℤ} (hi : i ≠ 0)
    (hmarg : ∀ k : ℤ, μ.map (fun ω ↦ ω k) = μ.map (fun ω ↦ ω (0 : ℤ)))
    {G : E → E → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) :
    ∫⁻ σ, G (σ i) (σ 0) ∂(μ.bind (isssd ν {(0 : ℤ)}))
      = ∫⁻ x, ∫⁻ y, G x y ∂ν ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) := by
  classical
  have hpair : Measurable fun σ : ℤ → E ↦ (σ i, σ (0 : ℤ)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply (0 : ℤ))
  have hGm : Measurable fun σ : ℤ → E ↦ G (σ i) (σ 0) := hG.comp hpair
  have hinner : Measurable fun x : E ↦ ∫⁻ y, G x y ∂ν :=
    Measurable.lintegral_prod_right' (f := fun q : E × E ↦ G q.1 q.2) hG
  rw [lintegral_bind_isssd_singleton (0 : ℤ) hGm]
  have hcongr : ∀ ω : ℤ → E,
      (∫⁻ y, G ((Function.update ω (0 : ℤ) y) i) ((Function.update ω (0 : ℤ) y) 0) ∂ν)
        = ∫⁻ y, G (ω i) y ∂ν := by
    intro ω
    refine lintegral_congr fun y ↦ ?_
    rw [Function.update_of_ne hi, Function.update_self]
  rw [lintegral_congr hcongr, ← hmarg i, lintegral_map hinner (measurable_pi_apply i)]

variable [StandardBorelSpace E] [IsProbabilityMeasure μ]

/-- **Georgii, Theorem (10.34)**, first part. For a shift-invariant Gibbs measure `μ` of an
irreducible homogeneous Markovian `λ`-modification, which by Theorem (10.25) is a Markov chain
for a kernel `P(x, ·) = p(x, ·) λ`, the `n`-step densities converge to `r` in the mean:
`∫ α(dx) λ(|p^n(x, ·) - r|) → 0`, where `α = σ_0(μ)` and `r` is the `λ`-density (10.31) of `α`.
Since `λ(|p^n(x, ·) - r|)` is the total variation distance of `P^n(x, ·)` and `α`, this says that
`P^n(x, ·) → α` in total variation, in `L¹(α)`. -/
theorem tendsto_lintegral_ofReal_abs_densityPow_sub
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hM : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμ : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x)) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫⁻ x, ∫⁻ y, ENNReal.ofReal
          |(Kernel.densityPow ν p n x y).toReal
            - (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p y).toReal| ∂ν
        ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)))
      Filter.atTop (nhds 0) := by
  classical
  set v : Measure (ℤ → E) := μ.bind (isssd ν {(0 : ℤ)}) with hv_def
  set α : Measure E := μ.map fun ω : ℤ → E ↦ ω (0 : ℤ) with hα_def
  set r : E → ℝ≥0∞ := stationaryDensity α p with hr_def
  have hrmeas : Measurable r := measurable_stationaryDensity hp
  set g : (ℤ → E) → ℝ := fun σ ↦ (ρ {(0 : ℤ)} σ).toReal with hg_def
  set 𝓖 : ℕ → MeasurableSpace (ℤ → E) := fun m ↦
    cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (-((m + 1 : ℕ) : ℤ)) ∪ {0}) with h𝓖_def
  set F : ℕ → (ℤ → E) → ℝ := fun m σ ↦
    (Kernel.densityPow ν p (m + 1) (σ (-((m + 1 : ℕ) : ℤ))) (σ 0)).toReal with hF_def
  set Finf : (ℤ → E) → ℝ := v[g | ⨅ m, 𝓖 m] with hFinf_def
  have hle : ∀ m, 𝓖 m ≤ MeasurableSpace.pi := fun _ ↦ cylinderEvents_le_pi
  have hanti : Antitone 𝓖 := by
    intro a b hab
    refine cylinderEvents_mono ?_
    rintro x (hx | hx)
    · refine Or.inl ?_
      simp only [Set.mem_Iic] at hx ⊢
      omega
    · exact Or.inr hx
  have hFmeas : ∀ m, Measurable (F m) := fun m ↦
    (measurable_densityPow_eval' (ν := ν) hp (m + 1)).ennreal_toReal
  have hFinfmeas : Measurable Finf :=
    (stronglyMeasurable_condExp.mono ((iInf_le 𝓖 0).trans (hle 0))).measurable
  have hmass : ∀ m : ℕ, ∫⁻ σ, Kernel.densityPow ν p (m + 1) (σ (-((m + 1 : ℕ) : ℤ))) (σ 0) ∂v
      = 1 := by
    intro m
    have h := setLIntegral_densityPow_eq_measure (μ := μ) (ν := ν) hchain hp hQ
      (n := m + 1) (Nat.le_add_left 1 m) (D := Set.univ) MeasurableSet.univ
    rw [Measure.restrict_univ, measure_univ] at h
    exact h
  have hFint : ∀ m, Integrable (F m) v := fun m ↦
    integrable_toReal_of_lintegral_ne_top
      (measurable_densityPow_eval' (ν := ν) hp (m + 1)).aemeasurable
      (by rw [hmass m]; exact ENNReal.one_ne_top)
  have hFcond : ∀ m, F m =ᵐ[v] v[g | 𝓖 m] := fun m ↦
    toReal_densityPow_ae_eq_condExp hγ hρ hμ hchain hp hQ (Nat.le_add_left 1 m)
  have hFdep : ∀ m : ℕ, DependsOn (F m)
      (((({0} : Finset ℤ)) : Set ℤ) ∪ {-((m + 1 : ℕ) : ℤ)}) := by
    intro m σ τ h
    have h1 : σ (-((m + 1 : ℕ) : ℤ)) = τ (-((m + 1 : ℕ) : ℤ)) :=
      h _ (Or.inr rfl)
    have h2 : σ (0 : ℤ) = τ (0 : ℤ) := h _ (Or.inl (by simp))
    simp only [hF_def, h1, h2]
  have hL1 : Filter.Tendsto (fun m ↦ ∫⁻ σ, ENNReal.ofReal |F m σ - Finf σ| ∂v)
      Filter.atTop (nhds 0) := by
    refine (tendsto_eLpNorm_condExp_of_antitone (μ := v) g hanti hle).congr fun m ↦ ?_
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr_ae ?_
    filter_upwards [hFcond m] with σ hσ
    simp only [Pi.sub_apply, Real.enorm_eq_ofReal_abs, hσ, hFinf_def]
  have h1026 := ae_eq_condExp_of_tendsto hγ hρ hM hhom hirr hμ hmarg
    (Δ := ({0} : Finset ℤ)) (j := (0 : ℤ)) (c := fun m : ℕ ↦ -((m + 1 : ℕ) : ℤ)) (sgn := -1)
    (Or.inr rfl) (fun m ↦ by push_cast; ring) hFmeas hFinfmeas hFdep hFint integrable_condExp hL1
  have hcyl : cylinderEvents (X := fun _ : ℤ ↦ E) ((({0} : Finset ℤ)) : Set ℤ)
      = cylinderEvents (X := fun _ : ℤ ↦ E) ({0} : Set ℤ) := by simp
  rw [hcyl] at h1026
  have hle0 : cylinderEvents (X := fun _ : ℤ ↦ E) ({0} : Set ℤ) ≤ ⨅ m, 𝓖 m := by
    refine le_iInf fun m ↦ cylinderEvents_mono ?_
    intro x hx
    exact Or.inr hx
  have htower : v[Finf | cylinderEvents (X := fun _ : ℤ ↦ E) ({0} : Set ℤ)]
      =ᵐ[v] v[g | cylinderEvents (X := fun _ : ℤ ↦ E) ({0} : Set ℤ)] :=
    condExp_condExp_of_le hle0 ((iInf_le 𝓖 0).trans (hle 0))
  have hrcond : v[g | cylinderEvents (X := fun _ : ℤ ↦ E) ({0} : Set ℤ)]
      =ᵐ[v] fun σ : ℤ → E ↦ (r (σ 0)).toReal :=
    (toReal_stationaryDensity_ae_eq_condExp hγ hρ hμ hchain hmarg hp hQ).symm
  have hFinfr : Finf =ᵐ[v] fun σ : ℤ → E ↦ (r (σ 0)).toReal :=
    h1026.trans (htower.trans hrcond)
  have hstep : ∀ m : ℕ, ∫⁻ σ, ENNReal.ofReal |F m σ - Finf σ| ∂v
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal
          |(Kernel.densityPow ν p (m + 1) x y).toReal - (r y).toReal| ∂ν ∂α := by
    intro m
    have hG : Measurable (Function.uncurry fun x y : E ↦ ENNReal.ofReal
        |(Kernel.densityPow ν p (m + 1) x y).toReal - (r y).toReal|) := by
      refine measurable_ofReal_abs_sub ?_ ?_
      · exact (Kernel.measurable_uncurry_densityPow hp (m + 1)).ennreal_toReal
      · exact (hrmeas.ennreal_toReal).comp measurable_snd
    have hi : (-((m + 1 : ℕ) : ℤ)) ≠ 0 := by
      simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
      omega
    calc ∫⁻ σ, ENNReal.ofReal |F m σ - Finf σ| ∂v
        = ∫⁻ σ, ENNReal.ofReal |F m σ - (r (σ 0)).toReal| ∂v := by
          refine lintegral_congr_ae ?_
          filter_upwards [hFinfr] with σ hσ
          rw [hσ]
      _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal
            |(Kernel.densityPow ν p (m + 1) x y).toReal - (r y).toReal| ∂ν ∂α :=
          lintegral_pair_bind_isssd_singleton_zero hi hmarg hG
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact hL1.congr hstep

end ErgodicTheorem

/-! ### Georgii (10.33): positivity of the invariant density -/

section Positivity

variable {p : E → E → ℝ≥0∞} {Q : Kernel E E}

/-- **Georgii (10.33).** With `C`, `n`, `h` an irreducibility datum of (10.23) and
`α = σ_0(μ)` the one-dimensional marginal, the `λ`-density `r` of `α` satisfies
`r ≥ (2α(C) - 1) h` `λ`-almost surely. In particular `r > 0` `λ`-a.s. on `{h > 0}` as soon as
`2α(C) > 1`, and if `{h_N > 0} ↑ E` then `α` and `λ` are equivalent. -/
theorem mul_le_stationaryDensity_of_irreducibility [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hμ : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x))
    {C : Set E} (hC : MeasurableSet C) {n : ℕ} (hn : 1 ≤ n) {h : E → ℝ≥0∞}
    (hhmeas : Measurable h)
    (hb : ∀ ω : ℤ → E, ω (-(n : ℤ)) ∈ C → ω (n : ℤ) ∈ C →
      h (ω 0) ≤ marginalDensity ν ρ (Finset.Ioo (-(n : ℤ)) (n : ℤ)) 0 ω) :
    (fun x ↦ (2 * (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) C - 1) * h x)
      ≤ᵐ[ν] stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p := by
  classical
  set α : Measure E := μ.map fun ω : ℤ → E ↦ ω (0 : ℤ) with hα_def
  have : IsProbabilityMeasure α :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℤ)).aemeasurable
  set Λ : Finset ℤ := Finset.Ioo (-(n : ℤ)) (n : ℤ) with hΛ_def
  set B : Set (ℤ → E) := {σ : ℤ → E | σ (-(n : ℤ)) ∈ C} ∩ {σ : ℤ → E | σ (n : ℤ) ∈ C} with hB_def
  have hnZ : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hmemΛ : (0 : ℤ) ∈ Λ := by simp only [hΛ_def, Finset.mem_Ioo]; omega
  -- `B` does not constrain the coordinate `0`
  have hnot1 : (-(n : ℤ)) ∈ ((({(0 : ℤ)} : Finset ℤ) : Set ℤ)ᶜ) := by
    simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff]
    omega
  have hnot2 : ((n : ℤ)) ∈ ((({(0 : ℤ)} : Finset ℤ) : Set ℤ)ᶜ) := by
    simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff]
    omega
  have hBc : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
      ((({(0 : ℤ)} : Finset ℤ) : Set ℤ)ᶜ)] B :=
    (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) hnot1 hC).inter
      (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) hnot2 hC)
  have hBm : MeasurableSet B := cylinderEvents_le_pi _ hBc
  -- `μ(B) ≥ 2 α(C) - 1`
  have hμB : 2 * α C - 1 ≤ μ B := by
    have hm2 : MeasurableSet {σ : ℤ → E | σ (n : ℤ) ∈ C} := (measurable_pi_apply _) hC
    have heq : ∀ i : ℤ, μ {σ : ℤ → E | σ i ∈ C} = α C := by
      intro i
      rw [← hmarg i, Measure.map_apply (measurable_pi_apply i) hC]
      rfl
    have hu := measure_union_add_inter (μ := μ) {σ : ℤ → E | σ (-(n : ℤ)) ∈ C} hm2
    rw [heq, heq, ← hB_def] at hu
    refine tsub_le_iff_right.2 ?_
    rw [two_mul, ← hu, add_comm]
    gcongr
    exact prob_le_one
  -- the main estimate on set integrals
  have hrmeas : Measurable (stationaryDensity α p) := measurable_stationaryDensity hp
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (measurable_const.mul hhmeas)
    fun A hA _ ↦ ?_
  have hAcyl : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
      (((Λ.erase (0 : ℤ)) : Finset ℤ) : Set ℤ)ᶜ] ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) :=
    measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by simp) hA
  have hAm : MeasurableSet ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) := measurable_pi_apply 0 hA
  have hmd : Measurable (marginalDensity ν ρ Λ (0 : ℤ)) := measurable_marginalDensity (hρ Λ) 0
  -- `∫_A r dλ = α A = μ(σ_0 ∈ A) = ∫_{σ_0 ∈ A} ρ^0_Λ dν_0`
  have hright : ∫⁻ x in A, stationaryDensity α p x ∂ν
      = ∫⁻ σ in (fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A, marginalDensity ν ρ Λ (0 : ℤ) σ
        ∂(μ.bind (isssd ν {(0 : ℤ)})) := by
    rw [← hμ.measure_eq_setLIntegral_marginalDensity hγ hρ hmemΛ hAcyl, ← withDensity_apply _ hA,
      ← map_eval_eq_withDensity_stationaryDensity hchain hmarg hp hQ,
      Measure.map_apply (measurable_pi_apply (0 : ℤ)) hA]
  -- `∫_A (μ B) h dλ ≤ ∫_{σ_0 ∈ A} ρ^0_Λ dν_0`
  have hleft : μ B * ∫⁻ x in A, h x ∂ν
      ≤ ∫⁻ σ in (fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A, marginalDensity ν ρ Λ (0 : ℤ) σ
        ∂(μ.bind (isssd ν {(0 : ℤ)})) := by
    have hsub : ∫⁻ σ in ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) ∩ B,
          marginalDensity ν ρ Λ (0 : ℤ) σ ∂(μ.bind (isssd ν {(0 : ℤ)}))
        ≤ ∫⁻ σ in (fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A, marginalDensity ν ρ Λ (0 : ℤ) σ
          ∂(μ.bind (isssd ν {(0 : ℤ)})) :=
      lintegral_mono_set Set.inter_subset_left
    refine le_trans ?_ hsub
    have hpt : ∀ σ ∈ ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) ∩ B,
        h (σ 0) ≤ marginalDensity ν ρ Λ (0 : ℤ) σ := fun σ hσ ↦ hb σ hσ.2.1 hσ.2.2
    have hmono : ∫⁻ σ in ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) ∩ B, h (σ 0)
          ∂(μ.bind (isssd ν {(0 : ℤ)}))
        ≤ ∫⁻ σ in ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) ∩ B, marginalDensity ν ρ Λ (0 : ℤ) σ
          ∂(μ.bind (isssd ν {(0 : ℤ)})) :=
      setLIntegral_mono' (hAm.inter hBm) hpt
    refine le_trans (le_of_eq ?_) hmono
    -- compute the left-hand side by resampling the coordinate `0`
    have hmeas : Measurable fun σ : ℤ → E ↦ h (σ 0) := hhmeas.comp (measurable_pi_apply 0)
    rw [← lintegral_indicator (hAm.inter hBm),
      lintegral_bind_isssd_singleton (0 : ℤ) (hmeas.indicator (hAm.inter hBm))]
    have hstep : ∀ ω : ℤ → E,
        (∫⁻ y, (((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) ∩ B).indicator
          (fun σ : ℤ → E ↦ h (σ 0)) (Function.update ω (0 : ℤ) y) ∂ν)
          = B.indicator (fun _ : ℤ → E ↦ ∫⁻ y in A, h y ∂ν) ω := by
      intro ω
      have hupd : ∀ y : E, Function.update ω (0 : ℤ) y ∈ B ↔ ω ∈ B := fun y ↦
        update_mem_iff_of_measurableSet_cylinderEvents hBc (by simp) ω y
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω, ← lintegral_indicator hA]
        refine lintegral_congr fun y ↦ ?_
        have hy0 : (Function.update ω (0 : ℤ) y) (0 : ℤ) = y := Function.update_self _ _ _
        by_cases hy : y ∈ A
        · have hmem : Function.update ω (0 : ℤ) y
              ∈ ((fun σ : ℤ → E ↦ σ (0 : ℤ)) ⁻¹' A) ∩ B := by
            refine ⟨?_, (hupd y).2 hω⟩
            simp only [Set.mem_preimage, hy0]
            exact hy
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hy, hy0]
        · rw [Set.indicator_of_notMem (fun hc ↦ hy (by
            simpa only [Set.mem_preimage, hy0] using hc.1)), Set.indicator_of_notMem hy]
      · rw [Set.indicator_of_notMem hω]
        refine (lintegral_congr fun y ↦ ?_).trans lintegral_zero
        exact Set.indicator_of_notMem (fun hc ↦ hω ((hupd y).1 hc.2)) _
    rw [lintegral_congr hstep, lintegral_indicator hBm, setLIntegral_const, mul_comm]
  calc ∫⁻ x in A, (2 * α C - 1) * h x ∂ν
      = (2 * α C - 1) * ∫⁻ x in A, h x ∂ν := lintegral_const_mul _ hhmeas
    _ ≤ μ B * ∫⁻ x in A, h x ∂ν := by gcongr
    _ ≤ _ := hleft.trans (le_of_eq hright.symm)

end Positivity

/-! ### Georgii §10.3, Theorem (10.35): tools -/

section Uniqueness

variable {p : E → E → ℝ≥0∞} {Q : Kernel E E}

/-- The `n`-step property of a homogeneous Markov chain for a general nonnegative integrand:
`∫_t f(σ_i) dμ = ∫_t (P^n f)(σ_{i-n}) dμ` for `t ∈ 𝓕_{]-∞,i-n]}`. -/
theorem IsMarkovChain.setLIntegral_comp_eval_pow [IsMarkovKernel Q]
    (h : IsMarkovChain (fun _ ↦ Q) μ) (i : ℤ) (n : ℕ) {f : E → ℝ≥0∞} (hf : Measurable f)
    {t : Set (ℤ → E)}
    (ht : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (i - n))] t) :
    ∫⁻ σ in t, f (σ i) ∂μ = ∫⁻ σ in t, (∫⁻ y, f y ∂((Q ^ n) (σ (i - n)))) ∂μ := by
  have hprob := h.isProbabilityMeasure
  induction n generalizing t with
  | zero =>
      simp only [Nat.cast_zero, sub_zero, pow_zero] at ht ⊢
      refine lintegral_congr fun σ ↦ ?_
      rw [show ((1 : Kernel E E) (σ i)) = Measure.dirac (σ i) from Kernel.id_apply _,
        lintegral_dirac' _ hf]
  | succ n ih =>
      have hcast : i - ((n + 1 : ℕ) : ℤ) = i - (n : ℤ) - 1 := by push_cast; ring
      have htIio : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
          (Set.Iio (i - (n : ℤ)))] t := by
        refine cylinderEvents_mono ?_ _ ht
        intro x hx
        simp only [Set.mem_Iic] at hx
        simp only [Set.mem_Iio]
        omega
      have htIic : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
          (Set.Iic (i - (n : ℤ)))] t :=
        cylinderEvents_mono Set.Iio_subset_Iic_self _ htIio
      have hg : Measurable fun y ↦ ∫⁻ z, f z ∂((Q ^ n) y) := hf.lintegral_kernel
      have key : ∀ x : E, ∫⁻ y, (∫⁻ z, f z ∂((Q ^ n) y)) ∂(Q x)
          = ∫⁻ z, f z ∂((Q ^ (n + 1)) x) := by
        intro x
        have hcomp : (Q ^ (n + 1)) = (Q ^ n) ∘ₖ Q := by rw [pow_succ]; rfl
        rw [hcomp, Kernel.comp_apply,
          Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
      rw [ih htIic, h.setLIntegral_comp_eval (i - (n : ℤ)) hg htIio]
      refine lintegral_congr fun σ ↦ ?_
      rw [hcast, key]

/-- **Doob–Dynkin for a one-point cylinder σ-algebra.** A real function measurable for `𝓕_{{j}}`
is a measurable function of the coordinate `j`. -/
lemma exists_eq_of_measurable_cylinderEvents_singleton {j : ℤ} {g : (ℤ → E) → ℝ}
    (hg : Measurable[cylinderEvents (X := fun _ : ℤ ↦ E) ({j} : Set ℤ)] g) :
    ∃ w : E → ℝ, Measurable w ∧ ∀ σ, g σ = w (σ j) := by
  classical
  by_cases hne : Nonempty (ℤ → E)
  · obtain ⟨ω₀⟩ := hne
    have hdep : DependsOn g ({j} : Set ℤ) := hg.dependsOn_of_cylinderEvents
    have hg' : Measurable g := hg.mono cylinderEvents_le_pi le_rfl
    refine ⟨fun x ↦ g (Function.update ω₀ j x), hg'.comp (measurable_update ω₀), fun σ ↦ ?_⟩
    refine hdep fun i hi ↦ ?_
    simp only [Set.mem_singleton_iff] at hi
    subst hi
    rw [Function.update_self]
  · rw [not_nonempty_iff] at hne
    exact ⟨fun _ ↦ 0, measurable_const, fun σ ↦ isEmptyElim σ⟩

/-- **The left conditional density of a right-local event.** For a Markov chain `μ` and
`A ∈ 𝓕_{[j,∞[}` there is a measurable `w : E → [0,1]` with
`μ(A ∩ t) = ∫_t w(σ_j) dμ` for every `t ∈ 𝓕_{]-∞,j]}`; this is the one-sided Markov
property (10.7) together with Doob–Dynkin. -/
theorem exists_leftDensity [IsProbabilityMeasure μ] [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ) (j : ℤ) {A : Set (ℤ → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Ici j)] A) :
    ∃ w : E → ℝ≥0∞, Measurable w ∧ (∀ x, w x ≤ 1) ∧
      ∀ t, MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)] t →
        μ (A ∩ t) = ∫⁻ σ in t, w (σ j) ∂μ := by
  classical
  have hleft : IsLeftMarkov μ := hchain.isLeftMarkov
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  set f : (ℤ → E) → ℝ := A.indicator 1 with hf_def
  have hfint : Integrable f μ := integrable_indicator_one hAm
  set u : (ℤ → E) → ℝ := μ[f | cylinderEvents (X := fun _ : ℤ ↦ E) ({j} : Set ℤ)] with hu_def
  have humeas : Measurable[cylinderEvents (X := fun _ : ℤ ↦ E) ({j} : Set ℤ)] u :=
    stronglyMeasurable_condExp.measurable
  obtain ⟨w₀, hw₀meas, hw₀⟩ := exists_eq_of_measurable_cylinderEvents_singleton humeas
  set wr : E → ℝ := fun x ↦ min (max (w₀ x) 0) 1 with hwr_def
  have hwrmeas : Measurable wr := (hw₀meas.max measurable_const).min measurable_const
  have hwr0 : ∀ x, 0 ≤ wr x := fun x ↦ le_min (le_max_right _ _) zero_le_one
  have hwr1 : ∀ x, wr x ≤ 1 := fun x ↦ min_le_right _ _
  have hue : (fun σ : ℤ → E ↦ wr (σ j)) =ᵐ[μ] u := by
    have h0 : (0 : (ℤ → E) → ℝ) ≤ᵐ[μ] u := condExp_nonneg (by
      filter_upwards with σ
      by_cases hσ : σ ∈ A <;> simp [hf_def, hσ])
    filter_upwards [h0, ae_abs_condExp_indicator_one_le (μ := μ)
      (cylinderEvents (X := fun _ : ℤ ↦ E) ({j} : Set ℤ)) A] with σ hσ0 hσ1
    have h1 : u σ ≤ 1 := (abs_le.1 hσ1).2
    have h2 : (0 : ℝ) ≤ u σ := hσ0
    rw [hwr_def]
    simp only [← hw₀ σ]
    rw [max_eq_left h2, min_eq_left h1]
  refine ⟨fun x ↦ ENNReal.ofReal (wr x), ENNReal.measurable_ofReal.comp hwrmeas,
    fun x ↦ by simpa using ENNReal.ofReal_le_ofReal (hwr1 x), fun t ht ↦ ?_⟩
  have htm : MeasurableSet t := cylinderEvents_le_pi _ ht
  have hle : cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hcond : μ[f | cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)] =ᵐ[μ] u := hleft j A hA
  have hreal : μ.real (A ∩ t) = ∫ σ in t, wr (σ j) ∂μ := by
    rw [← setIntegral_indicator_one' hAm t, ← setIntegral_condExp hle hfint ht]
    refine setIntegral_congr_ae htm ?_
    filter_upwards [hcond, hue] with σ h1 h2 _
    rw [h1, ← h2]
  have hint : Integrable (fun σ : ℤ → E ↦ wr (σ j)) (μ.restrict t) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact (hwrmeas.comp (measurable_pi_apply j)).aestronglyMeasurable
    · filter_upwards with σ
      rw [Real.norm_eq_abs, abs_of_nonneg (hwr0 _)]
      exact hwr1 _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun σ ↦ hwr0 (σ j)), ← hreal, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]


/-- **Integrating out the far-future coordinate.** For a homogeneous Markov chain, `m ≤ k` and
`t ∈ 𝓕_{]-∞,k]}`, the pair `(σ_m, σ_{k+N})` may be replaced by `(σ_m, ·)` distributed according
to `P^N(σ_k, ·)`. -/
theorem setLIntegral_indicator_pair_eval [IsProbabilityMeasure μ] [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ) {m k : ℤ} (hmk : m ≤ k) (N : ℕ)
    {t : Set (ℤ → E)} (ht : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic k)] t)
    {S : Set (E × E)} (hS : MeasurableSet S) :
    ∫⁻ σ in t, S.indicator (1 : E × E → ℝ≥0∞) (σ m, σ (k + N)) ∂μ
      = ∫⁻ σ in t, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) ∂μ := by
  classical
  have htm : MeasurableSet t := cylinderEvents_le_pi _ ht
  set κ : Kernel (ℤ → E) (E × E) :=
    Kernel.deterministic (fun σ : ℤ → E ↦ σ m) (measurable_pi_apply m)
      ×ₖ (Q ^ N).comap (fun σ : ℤ → E ↦ σ k) (measurable_pi_apply k) with hκ_def
  have hκapply : ∀ (σ : ℤ → E) {S' : Set (E × E)}, MeasurableSet S' →
      κ σ S' = (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S') := by
    intro σ S' hS'
    rw [hκ_def, Kernel.prod_apply, Measure.prod_apply hS', Kernel.deterministic_apply,
      Kernel.comap_apply,
      lintegral_dirac' _ (measurable_measure_prodMk_left (ν := (Q ^ N) (σ k)) hS')]
  set f : (ℤ → E) → E × E := fun σ ↦ (σ m, σ (k + N)) with hf_def
  have hfmeas : Measurable f := (measurable_pi_apply m).prodMk (measurable_pi_apply (k + N))
  set Pone : Measure (E × E) := (μ.restrict t).map f with hPone_def
  set Ptwo : Measure (E × E) := (μ.restrict t).bind κ with hPtwo_def
  have hPoneapply : ∀ {S' : Set (E × E)}, MeasurableSet S' →
      Pone S' = ∫⁻ σ in t, S'.indicator (1 : E × E → ℝ≥0∞) (σ m, σ (k + N)) ∂μ := by
    intro S' hS'
    rw [hPone_def, Measure.map_apply hfmeas hS', ← lintegral_indicator_one (hfmeas hS')]
    rfl
  have hPtwoapply : ∀ {S' : Set (E × E)}, MeasurableSet S' →
      Ptwo S' = ∫⁻ σ in t, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S') ∂μ := by
    intro S' hS'
    rw [hPtwo_def, Measure.bind_apply hS' κ.aemeasurable]
    exact lintegral_congr fun σ ↦ hκapply σ hS'
  have hfin : IsFiniteMeasure Pone := by
    constructor
    rw [hPoneapply MeasurableSet.univ]
    calc ∫⁻ σ in t, (Set.univ : Set (E × E)).indicator (1 : E × E → ℝ≥0∞) (σ m, σ (k + N)) ∂μ
        ≤ ∫⁻ _ : ℤ → E, 1 ∂μ := by
          refine le_trans (setLIntegral_le_lintegral _ _) (lintegral_mono fun σ ↦ ?_)
          simp
      _ < ⊤ := by simp [lintegral_const]
  have hkey : Pone = Ptwo := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨S₁, hS₁, S₂, hS₂, rfl⟩
      have hS₁m : MeasurableSet S₁ := hS₁
      have hS₂m : MeasurableSet S₂ := hS₂
      have hrect : MeasurableSet (S₁ ×ˢ S₂) := hS₁m.prod hS₂m
      have ht' : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
          (Set.Iic ((k + (N : ℤ)) - (N : ℤ)))] (t ∩ (fun σ : ℤ → E ↦ σ m) ⁻¹' S₁) := by
        rw [add_sub_cancel_right]
        exact ht.inter (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E)
          (Set.mem_Iic.2 hmk) hS₁m)
      have hchainEq := hchain.measure_preimage_inter_pow (k + (N : ℤ)) N hS₂m ht'
      rw [add_sub_cancel_right] at hchainEq
      rw [hPoneapply hrect, hPtwoapply hrect]
      have hL : ∫⁻ σ in t, (S₁ ×ˢ S₂).indicator (1 : E × E → ℝ≥0∞) (σ m, σ (k + N)) ∂μ
          = μ ((fun σ : ℤ → E ↦ σ (k + (N : ℤ))) ⁻¹' S₂ ∩ (t ∩ (fun σ : ℤ → E ↦ σ m) ⁻¹' S₁)) := by
        have hset : MeasurableSet ((fun σ : ℤ → E ↦ σ (k + (N : ℤ))) ⁻¹' S₂
            ∩ (t ∩ (fun σ : ℤ → E ↦ σ m) ⁻¹' S₁)) :=
          (measurable_pi_apply (k + (N : ℤ)) hS₂m).inter
            (htm.inter (measurable_pi_apply m hS₁m))
        rw [← lintegral_indicator_one hset, ← lintegral_indicator htm]
        refine lintegral_congr fun σ ↦ ?_
        by_cases hσt : σ ∈ t
        · by_cases h1 : σ m ∈ S₁ <;> by_cases h2 : σ (k + (N : ℤ)) ∈ S₂ <;>
            simp [Set.indicator, hσt, h1, h2, Set.mem_prod]
        · simp [Set.indicator, hσt]
      have hR : ∫⁻ σ in t, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' (S₁ ×ˢ S₂)) ∂μ
          = ∫⁻ σ in t ∩ (fun σ : ℤ → E ↦ σ m) ⁻¹' S₁, (Q ^ N) (σ k) S₂ ∂μ := by
        rw [← lintegral_indicator htm, ← lintegral_indicator
          (htm.inter (measurable_pi_apply m hS₁m))]
        refine lintegral_congr fun σ ↦ ?_
        by_cases hσt : σ ∈ t
        · by_cases h1 : σ m ∈ S₁
          · have hpre : Prod.mk (σ m) ⁻¹' (S₁ ×ˢ S₂) = S₂ := by
              ext z; simp [h1]
            simp [Set.indicator, hσt, h1, hpre]
          · have hpre : Prod.mk (σ m) ⁻¹' (S₁ ×ˢ S₂) = (∅ : Set E) := by
              ext z; simp [h1]
            simp [Set.indicator, hσt, h1, hpre]
        · simp [Set.indicator, hσt]
      rw [hL, hR, hchainEq]
    · rw [hPoneapply MeasurableSet.univ, hPtwoapply MeasurableSet.univ]
      have h1 : ∀ σ : ℤ → E, (Set.univ : Set (E × E)).indicator (1 : E × E → ℝ≥0∞)
          (σ m, σ (k + N)) = 1 := fun σ ↦ by simp
      have h2 : ∀ σ : ℤ → E, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' (Set.univ : Set (E × E))) = 1 := by
        intro σ
        simp only [Set.preimage_univ]
        exact measure_univ
      simp only [h1, h2]
  rw [← hPoneapply hS, ← hPtwoapply hS, hkey]

/-- The `ℝ≥0∞` "absolute difference" `(a - b) + (b - a)` is `|a - b|` for finite `a`, `b`. -/
lemma ENNReal.tsub_add_tsub_eq_ofReal_abs {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a - b) + (b - a) = ENNReal.ofReal |a.toReal - b.toReal| := by
  rcases le_total a b with hab | hab
  · rw [tsub_eq_zero_of_le hab, zero_add, abs_of_nonpos (by
      simpa using (ENNReal.toReal_le_toReal ha hb).2 hab), neg_sub,
      ← ENNReal.toReal_sub_of_le hab hb, ENNReal.ofReal_toReal (by
        exact ne_top_of_le_ne_top hb tsub_le_self)]
  · rw [tsub_eq_zero_of_le hab, add_zero, abs_of_nonneg (by
      simpa using sub_nonneg.2 ((ENNReal.toReal_le_toReal hb ha).2 hab)),
      ← ENNReal.toReal_sub_of_le hab ha, ENNReal.ofReal_toReal (by
        exact ne_top_of_le_ne_top ha tsub_le_self)]

variable (ν p) in
/-- The total variation distance `λ(|p^N(y, ·) - r|)` between `P^N(y, ·)` and `α = rλ`, in the
truncated-subtraction form `∫ ((p^N - r) + (r - p^N)) dλ`. -/
def tvDensity (ν : Measure E) (p : E → E → ℝ≥0∞) (r : E → ℝ≥0∞) (N : ℕ) (y : E) : ℝ≥0∞ :=
  ∫⁻ z, ((Kernel.densityPow ν p N y z - r z) + (r z - Kernel.densityPow ν p N y z)) ∂ν

lemma measurable_tvDensity (hp : Measurable (Function.uncurry p)) {r : E → ℝ≥0∞}
    (hr : Measurable r) (N : ℕ) : Measurable (tvDensity ν p r N) := by
  refine Measurable.lintegral_prod_right' (f := fun q : E × E ↦
    ((Kernel.densityPow ν p N q.1 q.2 - r q.2) + (r q.2 - Kernel.densityPow ν p N q.1 q.2))) ?_
  have h1 : Measurable fun q : E × E ↦ Kernel.densityPow ν p N q.1 q.2 :=
    Kernel.measurable_uncurry_densityPow hp N
  have h2 : Measurable fun q : E × E ↦ r q.2 := hr.comp measurable_snd
  exact (h1.sub h2).add (h2.sub h1)

/-- Integrating a function bounded by `1` against `P^N(y, ·)` or against `α` differs by at most
the total variation distance. -/
lemma lintegral_le_lintegral_add_tvDensity {Q : Kernel E E}
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x))
    {r : E → ℝ≥0∞} (hr : Measurable r) {α : Measure E} (hα : α = ν.withDensity r)
    {N : ℕ} (hN : 1 ≤ N) {q : E → ℝ≥0∞} (hq : Measurable q) (hq1 : ∀ z, q z ≤ 1) (y : E) :
    ∫⁻ z, q z ∂((Q ^ N) y) ≤ (∫⁻ z, q z ∂α) + tvDensity ν p r N y ∧
      (∫⁻ z, q z ∂α) ≤ (∫⁻ z, q z ∂((Q ^ N) y)) + tvDensity ν p r N y := by
  have hdn : Measurable (Kernel.densityPow ν p N y) :=
    (Kernel.measurable_uncurry_densityPow hp N).comp (measurable_const.prodMk measurable_id)
  have hQy : ∫⁻ z, q z ∂((Q ^ N) y) = ∫⁻ z, Kernel.densityPow ν p N y z * q z ∂ν := by
    rw [Kernel.pow_apply_eq_withDensity_densityPow hp hQ hN y,
      lintegral_withDensity_eq_lintegral_mul _ hdn hq]
    rfl
  have hαy : ∫⁻ z, q z ∂α = ∫⁻ z, r z * q z ∂ν := by
    rw [hα, lintegral_withDensity_eq_lintegral_mul _ hr hq]
    rfl
  have hkey : ∀ a b c : ℝ≥0∞, c ≤ 1 → a * c ≤ b * c + (a - b) := by
    intro a b c hc
    have h1 : a ≤ b + (a - b) := by rw [add_comm]; exact le_tsub_add
    have h2 : (a - b) * c ≤ a - b := by
      calc (a - b) * c ≤ (a - b) * 1 := by gcongr
        _ = a - b := mul_one _
    calc a * c ≤ (b + (a - b)) * c := by gcongr
      _ = b * c + (a - b) * c := by rw [add_mul]
      _ ≤ b * c + (a - b) := by gcongr
  constructor
  · rw [hQy, hαy]
    calc ∫⁻ z, Kernel.densityPow ν p N y z * q z ∂ν
        ≤ ∫⁻ z, (r z * q z + (Kernel.densityPow ν p N y z - r z)) ∂ν :=
          lintegral_mono fun z ↦ hkey _ _ _ (hq1 z)
      _ = (∫⁻ z, r z * q z ∂ν) + ∫⁻ z, (Kernel.densityPow ν p N y z - r z) ∂ν :=
          lintegral_add_left (hr.mul hq) _
      _ ≤ (∫⁻ z, r z * q z ∂ν) + tvDensity ν p r N y := by
          gcongr
          exact lintegral_mono fun z ↦ le_self_add
  · rw [hQy, hαy]
    calc ∫⁻ z, r z * q z ∂ν
        ≤ ∫⁻ z, (Kernel.densityPow ν p N y z * q z + (r z - Kernel.densityPow ν p N y z)) ∂ν :=
          lintegral_mono fun z ↦ hkey _ _ _ (hq1 z)
      _ = (∫⁻ z, Kernel.densityPow ν p N y z * q z ∂ν)
            + ∫⁻ z, (r z - Kernel.densityPow ν p N y z) ∂ν :=
          lintegral_add_left (hdn.mul hq) _
      _ ≤ (∫⁻ z, Kernel.densityPow ν p N y z * q z ∂ν) + tvDensity ν p r N y := by
          gcongr
          exact lintegral_mono fun z ↦ le_add_self

/-- The truncated-subtraction total variation distance `tvDensity` is bounded by `2` at every
point, since `(a - b) + (b - a) ≤ a + b` and both `∫ P^N(y, ·)` and `∫ α` are `1`. -/
lemma tvDensity_le_two [IsMarkovKernel Q] {r : E → ℝ≥0∞} (hp : Measurable (Function.uncurry p))
    (hQ : ∀ x, Q x = ν.withDensity (p x)) {α : Measure E} [IsProbabilityMeasure α]
    (_hr : Measurable r) (hα : α = ν.withDensity r) {N : ℕ} (hN : 1 ≤ N) (y : E) :
    tvDensity ν p r N y ≤ 2 := by
  have := isMarkovKernel_pow (Q := Q) hN
  have hdn : Measurable (Kernel.densityPow ν p N y) :=
    (Kernel.measurable_uncurry_densityPow hp N).comp (measurable_const.prodMk measurable_id)
  have h1 : ∫⁻ z, Kernel.densityPow ν p N y z ∂ν = 1 := by
    have h1' := Kernel.pow_apply_eq_withDensity_densityPow hp hQ hN y
    have h2' := withDensity_apply (μ := ν) (Kernel.densityPow ν p N y)
      (MeasurableSet.univ (α := E))
    rw [← h1', Measure.restrict_univ] at h2'
    rw [← h2']; exact measure_univ
  have h2 : ∫⁻ z, r z ∂ν = 1 := by
    have h2' := withDensity_apply (μ := ν) r (MeasurableSet.univ (α := E))
    rw [← hα, Measure.restrict_univ] at h2'
    rw [← h2']; exact measure_univ
  calc tvDensity ν p r N y
      ≤ ∫⁻ z, (Kernel.densityPow ν p N y z + r z) ∂ν := by
        refine lintegral_mono fun z ↦ ?_
        exact add_le_add tsub_le_self tsub_le_self
    _ = (∫⁻ z, Kernel.densityPow ν p N y z ∂ν) + ∫⁻ z, r z ∂ν := lintegral_add_left hdn _
    _ = 2 := by rw [h1, h2]; norm_num

/-- The mean total variation distance `∫ tvDensity N dα` is finite (`≤ 2`), for every `N ≥ 1`. -/
lemma lintegral_tvDensity_ne_top [IsMarkovKernel Q] {r : E → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p))
    (hQ : ∀ x, Q x = ν.withDensity (p x)) {α : Measure E} [IsProbabilityMeasure α]
    (hr : Measurable r) (hα : α = ν.withDensity r) {N : ℕ} (hN : 1 ≤ N) :
    (∫⁻ y, tvDensity ν p r N y ∂α) ≠ ⊤ := by
  have hle : ∫⁻ y, tvDensity ν p r N y ∂α ≤ 2 :=
    calc ∫⁻ y, tvDensity ν p r N y ∂α ≤ ∫⁻ _ : E, (2 : ℝ≥0∞) ∂α :=
          lintegral_mono fun y ↦ tvDensity_le_two hp hQ hr hα hN y
      _ = 2 := by rw [lintegral_const, measure_univ, mul_one]
  exact ne_top_of_le_ne_top (by norm_num) hle

/-- **Theorem (10.34)** in truncated-subtraction form: the mean total variation distance of
`P^N(y, ·)` and `α` tends to `0`. -/
theorem tendsto_lintegral_tvDensity [StandardBorelSpace E] [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hMk : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμ : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x)) :
    Filter.Tendsto (fun N : ℕ ↦ ∫⁻ y, tvDensity ν p
        (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) N y
        ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ))) Filter.atTop (nhds 0) := by
  classical
  set α : Measure E := μ.map fun ω : ℤ → E ↦ ω (0 : ℤ) with hα_def
  have hαprob : IsProbabilityMeasure α :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℤ)).aemeasurable
  set r : E → ℝ≥0∞ := stationaryDensity α p with hr_def
  have hrmeas : Measurable r := measurable_stationaryDensity hp
  have hαr : α = ν.withDensity r := map_eval_eq_withDensity_stationaryDensity hchain hmarg hp hQ
  have hrint : ∫⁻ z, r z ∂ν = 1 := by
    have := withDensity_apply (μ := ν) r (MeasurableSet.univ (α := E))
    rw [← hαr, Measure.restrict_univ] at this
    rw [← this, measure_univ]
  have hfinr : ∀ᵐ z ∂ν, r z ≠ ⊤ := by
    filter_upwards [ae_lt_top hrmeas (by rw [hrint]; exact ENNReal.one_ne_top)] with z hz
    exact hz.ne
  have hfin1 : ∀ (N : ℕ) (y : E), ∀ᵐ z ∂ν, Kernel.densityPow ν p N y z ≠ ⊤ := by
    intro N y
    have hdn : Measurable (Kernel.densityPow ν p N y) :=
      (Kernel.measurable_uncurry_densityPow hp N).comp (measurable_const.prodMk measurable_id)
    have hint : ∫⁻ z, Kernel.densityPow ν p N y z ∂ν ≠ ⊤ := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp [Kernel.densityPow]
      · have h1 := Kernel.pow_apply_eq_withDensity_densityPow hp hQ hN y
        have h2 := withDensity_apply (μ := ν) (Kernel.densityPow ν p N y)
          (MeasurableSet.univ (α := E))
        rw [← h1, Measure.restrict_univ] at h2
        rw [← h2]
        exact measure_ne_top _ _
    filter_upwards [ae_lt_top hdn hint] with z hz
    exact hz.ne
  refine (tendsto_lintegral_ofReal_abs_densityPow_sub hγ hρ hMk hhom hirr hμ hchain hmarg
    hp hQ).congr fun N ↦ ?_
  refine lintegral_congr fun y ↦ ?_
  refine (lintegral_congr_ae ?_).symm
  filter_upwards [hfin1 N y, hfinr] with z h1 h2
  exact ENNReal.tsub_add_tsub_eq_ofReal_abs h1 h2

/-- **Georgii's estimate (10.37)** for the two boundary coordinates. Let `A ∈ 𝓕_{[i,k]}`, let
`m = i - 1 - M` be `M ≥ 1` steps to the left of `A` and `n = k + N` be `N ≥ 1` steps to its right,
and let `C ∈ 𝓕_{{m,n}}`. Then `μ(A ∩ C)` and `μ(A) μ(C)` differ by at most
`Δ_M + 2 Δ_N`, where `Δ_J = ∫ α(dy) λ(|p^J(y, ·) - r|)`. -/
theorem measure_inter_pair_le [IsProbabilityMeasure μ] [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x))
    {i k m : ℤ} {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hm : m = i - 1 - (M : ℤ))
    {A : Set (ℤ → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Icc i k)] A)
    (hik : i ≤ k) {S : Set (E × E)} (hS : MeasurableSet S) :
    μ (A ∩ (fun σ : ℤ → E ↦ (σ m, σ (k + (N : ℤ)))) ⁻¹' S)
        ≤ μ A * μ ((fun σ : ℤ → E ↦ (σ m, σ (k + (N : ℤ)))) ⁻¹' S)
          + ((∫⁻ y, tvDensity ν p (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) M y
              ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)))
            + 2 * ∫⁻ y, tvDensity ν p (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) N y
              ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ))) ∧
      μ A * μ ((fun σ : ℤ → E ↦ (σ m, σ (k + (N : ℤ)))) ⁻¹' S)
        ≤ μ (A ∩ (fun σ : ℤ → E ↦ (σ m, σ (k + (N : ℤ)))) ⁻¹' S)
          + ((∫⁻ y, tvDensity ν p (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) M y
              ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)))
            + 2 * ∫⁻ y, tvDensity ν p (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) N y
              ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ))) := by
  classical
  set α : Measure E := μ.map fun ω : ℤ → E ↦ ω (0 : ℤ) with hα_def
  have hαprob : IsProbabilityMeasure α :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℤ)).aemeasurable
  set r : E → ℝ≥0∞ := stationaryDensity α p with hr_def
  have hrmeas : Measurable r := measurable_stationaryDensity hp
  have hαr : α = ν.withDensity r := map_eval_eq_withDensity_stationaryDensity hchain hmarg hp hQ
  set DM : ℝ≥0∞ := ∫⁻ y, tvDensity ν p r M y ∂α with hDM_def
  set DN : ℝ≥0∞ := ∫⁻ y, tvDensity ν p r N y ∂α with hDN_def
  set j : ℤ := i - 1 with hj_def
  set n : ℤ := k + (N : ℤ) with hn_def
  set C : Set (ℤ → E) := (fun σ : ℤ → E ↦ (σ m, σ n)) ⁻¹' S with hC_def
  have hmj : m ≤ j := by omega
  have hmk : m ≤ k := by omega
  have htvM : Measurable (tvDensity ν p r M) := measurable_tvDensity hp hrmeas M
  have htvN : Measurable (tvDensity ν p r N) := measurable_tvDensity hp hrmeas N
  -- 1. the left conditional density of `A` at the site `j = i - 1`
  have hAIci : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Ici j)] A := by
    refine cylinderEvents_mono ?_ _ hA
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ici, hj_def]
    omega
  have hAIic : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic k)] A := by
    refine cylinderEvents_mono ?_ _ hA
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Iic]
    omega
  obtain ⟨w, hwmeas, hw1, hwt⟩ := exists_leftDensity hchain j hAIci
  -- 2. transporting it `M` steps further to the left
  set wm : E → ℝ≥0∞ := fun x ↦ ∫⁻ y, w y ∂((Q ^ M) x) with hwm_def
  have hwmmeas : Measurable wm := hwmeas.lintegral_kernel
  have hwm1 : ∀ x, wm x ≤ 1 := by
    intro x
    calc wm x ≤ ∫⁻ _ : E, 1 ∂((Q ^ M) x) := lintegral_mono hw1
      _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
  have hwmt : ∀ t, MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic m)] t →
      μ (A ∩ t) = ∫⁻ σ in t, wm (σ m) ∂μ := by
    intro t ht
    have htj : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)] t :=
      cylinderEvents_mono (Set.Iic_subset_Iic.2 hmj) _ ht
    have htM : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic (j - (M : ℤ)))] t := by
      rw [show j - (M : ℤ) = m by omega]
      exact ht
    rw [hwt t htj, hchain.setLIntegral_comp_eval_pow j M hwmeas htM]
    refine lintegral_congr fun σ ↦ ?_
    rw [show j - (M : ℤ) = m by omega]
  -- 3. `μ A` as an integral of `w` and of `wm`
  have huniv : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic m)] Set.univ :=
    MeasurableSet.univ
  have hAw : μ A = ∫⁻ y, w y ∂α := by
    have h1 := hwt Set.univ MeasurableSet.univ
    rw [Set.inter_univ, Measure.restrict_univ] at h1
    rw [h1, ← lintegral_map hwmeas (measurable_pi_apply j), hmarg j]
  have hAwm : μ A = ∫⁻ x, wm x ∂α := by
    have h1 := hwmt Set.univ MeasurableSet.univ
    rw [Set.inter_univ, Measure.restrict_univ] at h1
    rw [h1, ← lintegral_map hwmmeas (measurable_pi_apply m), hmarg m]
  -- 4. the total-variation bound for `wm`
  have hwmbound : ∀ x : E, wm x ≤ μ A + tvDensity ν p r M x ∧
      μ A ≤ wm x + tvDensity ν p r M x := by
    intro x
    have h := lintegral_le_lintegral_add_tvDensity hp hQ hrmeas hαr hM hwmeas hw1 x
    rw [← hAw] at h
    exact h
  -- 5. the right-hand conditional probability `ψ`
  set ψ : E → ℝ≥0∞ := fun x ↦ α (Prod.mk x ⁻¹' S) with hψ_def
  have hψmeas : Measurable ψ := measurable_measure_prodMk_left hS
  have hψ1 : ∀ x, ψ x ≤ 1 := fun x ↦ prob_le_one
  have hψbound : ∀ x y : E, (Q ^ N) y (Prod.mk x ⁻¹' S) ≤ ψ x + tvDensity ν p r N y ∧
      ψ x ≤ (Q ^ N) y (Prod.mk x ⁻¹' S) + tvDensity ν p r N y := by
    intro x y
    have hpre : MeasurableSet (Prod.mk x ⁻¹' S) := measurable_prodMk_left hS
    have h := lintegral_le_lintegral_add_tvDensity hp hQ hrmeas hαr hN
      (q := (Prod.mk x ⁻¹' S).indicator (1 : E → ℝ≥0∞)) (measurable_one.indicator hpre)
      (fun z ↦ by by_cases hz : z ∈ Prod.mk x ⁻¹' S <;> simp [Set.indicator, hz]) y
    rwa [lintegral_indicator_one hpre, lintegral_indicator_one hpre] at h
  -- 6. the mean total-variation bounds
  have htvint : ∀ (J : ℕ) (l : ℤ), ∫⁻ σ : ℤ → E, tvDensity ν p r J (σ l) ∂μ
      = ∫⁻ y, tvDensity ν p r J y ∂α := by
    intro J l
    rw [← lintegral_map (measurable_tvDensity hp hrmeas J) (measurable_pi_apply l), hmarg l]
  have hFmeas : Measurable fun σ : ℤ → E ↦ (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) := by
    have hind : Measurable fun q : (E × E) × E ↦ S.indicator (1 : E × E → ℝ≥0∞) (q.1.1, q.2) :=
      (measurable_one.indicator hS).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    set κ' : Kernel (E × E) E := (Q ^ N).comap (Prod.snd : E × E → E) measurable_snd with hκ'_def
    have h1 : Measurable fun q : E × E ↦
        ∫⁻ z, S.indicator (1 : E × E → ℝ≥0∞) (q.1, z) ∂(κ' q) :=
      Measurable.lintegral_kernel_prod_right (κ := κ') hind
    have h2 : ∀ q : E × E, ∫⁻ z, S.indicator (1 : E × E → ℝ≥0∞) (q.1, z) ∂(κ' q)
        = (Q ^ N) q.2 (Prod.mk q.1 ⁻¹' S) := by
      intro q
      rw [hκ'_def, Kernel.comap_apply, ← lintegral_indicator_one (measurable_prodMk_left hS)]
      refine lintegral_congr fun z ↦ ?_
      by_cases hz : (q.1, z) ∈ S
      · rw [Set.indicator_of_mem hz,
          Set.indicator_of_mem (show z ∈ Prod.mk q.1 ⁻¹' S from hz)]
        rfl
      · rw [Set.indicator_of_notMem hz,
          Set.indicator_of_notMem (show z ∉ Prod.mk q.1 ⁻¹' S from hz)]
    have heq : (fun q : E × E ↦ ∫⁻ z, S.indicator (1 : E × E → ℝ≥0∞) (q.1, z) ∂(κ' q))
        = fun q : E × E ↦ (Q ^ N) q.2 (Prod.mk q.1 ⁻¹' S) := funext h2
    rw [heq] at h1
    have h3 : Measurable fun σ : ℤ → E ↦ ((σ m, σ k) : E × E) :=
      (measurable_pi_apply m).prodMk (measurable_pi_apply k)
    exact h1.comp h3
  have hψα : ∫⁻ σ : ℤ → E, ψ (σ m) ∂μ = ∫⁻ x, ψ x ∂α := by
    rw [← hmarg m, lintegral_map hψmeas (measurable_pi_apply m)]
  have htvα : ∫⁻ σ : ℤ → E, tvDensity ν p r N (σ k) ∂μ = DN := by
    rw [hDN_def]; exact htvint N k
  -- 7. `μ (A ∩ C)` compared with `∫_A ψ(σ_m)`
  have hACeq : μ (A ∩ C) = ∫⁻ σ in A, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) ∂μ := by
    have hAm : MeasurableSet A := cylinderEvents_le_pi _ hAIic
    have hCm : MeasurableSet C := ((measurable_pi_apply m).prodMk (measurable_pi_apply n)) hS
    have hind : ∀ σ : ℤ → E, S.indicator (1 : E × E → ℝ≥0∞) (σ m, σ n)
        = C.indicator (1 : (ℤ → E) → ℝ≥0∞) σ := by
      intro σ
      by_cases hσ : σ ∈ C
      · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem (show (σ m, σ n) ∈ S from hσ)]
        rfl
      · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem (show (σ m, σ n) ∉ S from hσ)]
    have h1 : μ (A ∩ C) = ∫⁻ σ in A, S.indicator (1 : E × E → ℝ≥0∞) (σ m, σ n) ∂μ := by
      rw [lintegral_congr hind, lintegral_indicator_one hCm, Measure.restrict_apply hCm,
        Set.inter_comm C A]
    rw [h1, hn_def, setLIntegral_indicator_pair_eval hchain hmk N hAIic hS]
  have hψAupper : μ (A ∩ C) ≤ (∫⁻ σ in A, ψ (σ m) ∂μ) + DN := by
    have hAm : MeasurableSet A := cylinderEvents_le_pi _ hAIic
    calc μ (A ∩ C) = ∫⁻ σ in A, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) ∂μ := hACeq
      _ ≤ ∫⁻ σ in A, (ψ (σ m) + tvDensity ν p r N (σ k)) ∂μ :=
          lintegral_mono fun σ ↦ (hψbound (σ m) (σ k)).1
      _ = (∫⁻ σ in A, ψ (σ m) ∂μ) + ∫⁻ σ in A, tvDensity ν p r N (σ k) ∂μ :=
          lintegral_add_left (hψmeas.comp (measurable_pi_apply m)) _
      _ ≤ (∫⁻ σ in A, ψ (σ m) ∂μ) + DN := by
          gcongr
          rw [hDN_def, ← htvint N k]
          exact setLIntegral_le_lintegral _ _
  have hψAlower : (∫⁻ σ in A, ψ (σ m) ∂μ) ≤ μ (A ∩ C) + DN := by
    have hAm : MeasurableSet A := cylinderEvents_le_pi _ hAIic
    calc (∫⁻ σ in A, ψ (σ m) ∂μ)
        ≤ ∫⁻ σ in A, ((Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) + tvDensity ν p r N (σ k)) ∂μ :=
          lintegral_mono fun σ ↦ (hψbound (σ m) (σ k)).2
      _ = (∫⁻ σ in A, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) ∂μ)
            + ∫⁻ σ in A, tvDensity ν p r N (σ k) ∂μ := by
          exact lintegral_add_left hFmeas _
      _ ≤ μ (A ∩ C) + DN := by
          rw [← hACeq]
          gcongr
          rw [hDN_def, ← htvint N k]
          exact setLIntegral_le_lintegral _ _
  -- 8. `∫_A ψ(σ_m) dμ = ∫ wm ψ dα`
  have hmapeq : (μ.restrict A).map (fun σ : ℤ → E ↦ σ m) = α.withDensity wm := by
    have hAm : MeasurableSet A := cylinderEvents_le_pi _ hAIic
    ext T hT
    have ht : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic m)]
        ((fun σ : ℤ → E ↦ σ m) ⁻¹' T) :=
      measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (Set.mem_Iic.2 le_rfl) hT
    rw [Measure.map_apply (measurable_pi_apply m) hT,
      Measure.restrict_apply (measurable_pi_apply m hT), Set.inter_comm, hwmt _ ht,
      withDensity_apply _ hT, ← lintegral_indicator (measurable_pi_apply m hT),
      ← lintegral_indicator hT, ← hmarg m,
      lintegral_map (hwmmeas.indicator hT) (measurable_pi_apply m)]
    refine lintegral_congr fun σ ↦ ?_
    by_cases hσ : σ m ∈ T
    · rw [Set.indicator_of_mem (by exact hσ), Set.indicator_of_mem hσ]
    · rw [Set.indicator_of_notMem (by exact hσ), Set.indicator_of_notMem hσ]
  have hψA : (∫⁻ σ in A, ψ (σ m) ∂μ) = ∫⁻ x, wm x * ψ x ∂α := by
    have e : ∫⁻ σ in A, ψ (σ m) ∂μ
        = ∫⁻ x, ψ x ∂((μ.restrict A).map (fun σ : ℤ → E ↦ σ m)) :=
      (lintegral_map hψmeas (measurable_pi_apply m)).symm
    rw [e, hmapeq, lintegral_withDensity_eq_lintegral_mul _ hwmmeas hψmeas]
    rfl
  -- 9. comparing `∫ wm ψ dα` with `μ(A) ∫ ψ dα`
  have hprod_upper : (∫⁻ x, wm x * ψ x ∂α) ≤ μ A * (∫⁻ x, ψ x ∂α) + DM := by
    calc (∫⁻ x, wm x * ψ x ∂α)
        ≤ ∫⁻ x, (μ A * ψ x + tvDensity ν p r M x) ∂α := by
          refine lintegral_mono fun x ↦ ?_
          calc wm x * ψ x ≤ (μ A + tvDensity ν p r M x) * ψ x := by gcongr; exact (hwmbound x).1
            _ = μ A * ψ x + tvDensity ν p r M x * ψ x := by rw [add_mul]
            _ ≤ μ A * ψ x + tvDensity ν p r M x := by
                gcongr
                calc tvDensity ν p r M x * ψ x ≤ tvDensity ν p r M x * 1 := by gcongr; exact hψ1 x
                  _ = tvDensity ν p r M x := mul_one _
      _ = μ A * (∫⁻ x, ψ x ∂α) + DM := by
          rw [lintegral_add_left (hψmeas.const_mul (μ A)), lintegral_const_mul _ hψmeas]
  have hprod_lower : μ A * (∫⁻ x, ψ x ∂α) ≤ (∫⁻ x, wm x * ψ x ∂α) + DM := by
    calc μ A * (∫⁻ x, ψ x ∂α) = ∫⁻ x, μ A * ψ x ∂α := (lintegral_const_mul _ hψmeas).symm
      _ ≤ ∫⁻ x, (wm x * ψ x + tvDensity ν p r M x) ∂α := by
          refine lintegral_mono fun x ↦ ?_
          calc μ A * ψ x ≤ (wm x + tvDensity ν p r M x) * ψ x := by gcongr; exact (hwmbound x).2
            _ = wm x * ψ x + tvDensity ν p r M x * ψ x := by rw [add_mul]
            _ ≤ wm x * ψ x + tvDensity ν p r M x := by
                gcongr
                calc tvDensity ν p r M x * ψ x ≤ tvDensity ν p r M x * 1 := by gcongr; exact hψ1 x
                  _ = tvDensity ν p r M x := mul_one _
      _ = (∫⁻ x, wm x * ψ x ∂α) + DM :=
          lintegral_add_left (hwmmeas.mul hψmeas) _
  -- 10. `μ C` compared with `∫ ψ dα`
  have hCeq : μ C = ∫⁻ σ : ℤ → E, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) ∂μ := by
    have hCm : MeasurableSet C := ((measurable_pi_apply m).prodMk (measurable_pi_apply n)) hS
    have hind : ∀ σ : ℤ → E, S.indicator (1 : E × E → ℝ≥0∞) (σ m, σ n)
        = C.indicator (1 : (ℤ → E) → ℝ≥0∞) σ := by
      intro σ
      by_cases hσ : σ ∈ C
      · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem (show (σ m, σ n) ∈ S from hσ)]
        rfl
      · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem (show (σ m, σ n) ∉ S from hσ)]
    have h1 : μ C = ∫⁻ σ : ℤ → E, S.indicator (1 : E × E → ℝ≥0∞) (σ m, σ n) ∂μ := by
      rw [lintegral_congr hind, lintegral_indicator_one hCm]
    have h2 := setLIntegral_indicator_pair_eval (μ := μ) hchain hmk N
      (t := Set.univ) MeasurableSet.univ hS
    rw [Measure.restrict_univ] at h2
    rw [h1, hn_def, h2]
  have hCupper : μ C ≤ (∫⁻ x, ψ x ∂α) + DN := by
    calc μ C = ∫⁻ σ : ℤ → E, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) ∂μ := hCeq
      _ ≤ ∫⁻ σ : ℤ → E, (ψ (σ m) + tvDensity ν p r N (σ k)) ∂μ :=
          lintegral_mono fun σ ↦ (hψbound (σ m) (σ k)).1
      _ = (∫⁻ σ : ℤ → E, ψ (σ m) ∂μ) + ∫⁻ σ : ℤ → E, tvDensity ν p r N (σ k) ∂μ :=
          lintegral_add_left (hψmeas.comp (measurable_pi_apply m)) _
      _ = (∫⁻ x, ψ x ∂α) + DN := by rw [hψα, htvα]
  have hClower : (∫⁻ x, ψ x ∂α) ≤ μ C + DN := by
    calc (∫⁻ x, ψ x ∂α) = ∫⁻ σ : ℤ → E, ψ (σ m) ∂μ := hψα.symm
      _ ≤ ∫⁻ σ : ℤ → E, ((Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) + tvDensity ν p r N (σ k)) ∂μ :=
          lintegral_mono fun σ ↦ (hψbound (σ m) (σ k)).2
      _ = (∫⁻ σ : ℤ → E, (Q ^ N) (σ k) (Prod.mk (σ m) ⁻¹' S) ∂μ)
            + ∫⁻ σ : ℤ → E, tvDensity ν p r N (σ k) ∂μ := by
          exact lintegral_add_left hFmeas _
      _ = μ C + DN := by rw [← hCeq, htvα]
  -- 11. assembling
  have hAle : μ A ≤ 1 := prob_le_one
  constructor
  · calc μ (A ∩ C) ≤ (∫⁻ σ in A, ψ (σ m) ∂μ) + DN := hψAupper
      _ = (∫⁻ x, wm x * ψ x ∂α) + DN := by rw [hψA]
      _ ≤ (μ A * (∫⁻ x, ψ x ∂α) + DM) + DN := by gcongr
      _ ≤ (μ A * (μ C + DN) + DM) + DN := by gcongr
      _ = ((μ A * μ C + μ A * DN) + DM) + DN := by rw [mul_add]
      _ ≤ ((μ A * μ C + DN) + DM) + DN := by
          gcongr
          calc μ A * DN ≤ 1 * DN := by gcongr
            _ = DN := one_mul _
      _ = μ A * μ C + (DM + 2 * DN) := by ring
  · calc μ A * μ C ≤ μ A * ((∫⁻ x, ψ x ∂α) + DN) := by gcongr
      _ = μ A * (∫⁻ x, ψ x ∂α) + μ A * DN := by rw [mul_add]
      _ ≤ μ A * (∫⁻ x, ψ x ∂α) + DN := by
          gcongr
          calc μ A * DN ≤ 1 * DN := by gcongr
            _ = DN := one_mul _
      _ ≤ ((∫⁻ x, wm x * ψ x ∂α) + DM) + DN := by gcongr
      _ = ((∫⁻ σ in A, ψ (σ m) ∂μ) + DM) + DN := by rw [hψA]
      _ ≤ ((μ (A ∩ C) + DN) + DM) + DN := by gcongr
      _ = μ (A ∩ C) + (DM + 2 * DN) := by ring

omit [IsProbabilityMeasure ν] in
/-- **Reduction of Georgii (10.36) to the two boundary coordinates.** For a Markov field, an
estimate `|μ(A ∩ C) - μ(A) μ(C)| ≤ ε` valid for all `C ∈ 𝓕_{{m,n}}` automatically holds for all
`B ∈ 𝓕_{]m,n[ᶜ}`: the conditional expectation of `1_A` given the exterior is `𝓕_{{m,n}}`-measurable,
so the extremal `B` may be taken in `𝓕_{{m,n}}`. -/
theorem measureReal_inter_sub_le_of_isMarkovOn [IsProbabilityMeasure μ] {m n : ℤ}
    (hmn : m + 1 < n) (hMark : IsMarkovOn μ (Set.Ioo m n))
    {A : Set (ℤ → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Ioo m n)] A)
    {e : ℝ}
    (hbound : ∀ C, MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ({m, n} : Set ℤ)] C →
      |μ.real (A ∩ C) - μ.real A * μ.real C| ≤ e)
    {B : Set (ℤ → E)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ((Set.Ioo m n)ᶜ)] B) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ e := by
  classical
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hBm : MeasurableSet B := cylinderEvents_le_pi _ hB
  set f : (ℤ → E) → ℝ := A.indicator 1 with hf_def
  have hfint : Integrable f μ := integrable_indicator_one hAm
  have hbd : boundarySet (Set.Ioo m n) = ({m, n} : Set ℤ) := boundarySet_Ioo hmn
  have hcond : μ[f | cylinderEvents (X := fun _ : ℤ ↦ E) ((Set.Ioo m n)ᶜ)]
      =ᵐ[μ] μ[f | cylinderEvents (X := fun _ : ℤ ↦ E) ({m, n} : Set ℤ)] := by
    have h := hMark A hA
    rwa [hbd] at h
  set g : (ℤ → E) → ℝ := μ[f | cylinderEvents (X := fun _ : ℤ ↦ E) ({m, n} : Set ℤ)] with hg_def
  have hgsm : StronglyMeasurable[cylinderEvents (X := fun _ : ℤ ↦ E) ({m, n} : Set ℤ)] g :=
    stronglyMeasurable_condExp
  have hgint : Integrable g μ := integrable_condExp
  set c : ℝ := μ.real A with hc_def
  have hsubint : Integrable (fun σ : ℤ → E ↦ g σ - c) μ := hgint.sub (integrable_const c)
  have hpairsub : ({m, n} : Set ℤ) ⊆ (Set.Ioo m n)ᶜ := by
    intro x hx
    rcases hx with hx | hx
    · subst hx; simp
    · simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp
  have hkey : ∀ D : Set (ℤ → E),
      MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ((Set.Ioo m n)ᶜ)] D →
      ∫ σ in D, (g σ - c) ∂μ = μ.real (A ∩ D) - μ.real A * μ.real D := by
    intro D hD
    have hDm : MeasurableSet D := cylinderEvents_le_pi _ hD
    have h1 : ∫ σ in D, g σ ∂μ = μ.real (A ∩ D) := by
      have e1 : ∫ σ in D, g σ ∂μ
          = ∫ σ in D, (μ[f | cylinderEvents (X := fun _ : ℤ ↦ E) ((Set.Ioo m n)ᶜ)]) σ ∂μ :=
        setIntegral_congr_ae hDm (hcond.mono fun σ hσ _ ↦ hσ.symm)
      rw [e1, setIntegral_condExp cylinderEvents_le_pi hfint hD,
        setIntegral_indicator_one' hAm D]
    rw [integral_sub hgint.integrableOn (integrable_const c).integrableOn, h1, setIntegral_const,
      smul_eq_mul, hc_def]
    ring
  set Cp : Set (ℤ → E) := {σ : ℤ → E | c ≤ g σ} with hCp_def
  have hCpB : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ({m, n} : Set ℤ)] Cp :=
    measurableSet_le measurable_const hgsm.measurable
  have hCpm : MeasurableSet Cp := cylinderEvents_le_pi _ hCpB
  have hCpOuter : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ((Set.Ioo m n)ᶜ)] Cp :=
    cylinderEvents_mono hpairsub _ hCpB
  have hCcB : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ({m, n} : Set ℤ)] Cpᶜ :=
    hCpB.compl
  have hCcm : MeasurableSet Cpᶜ := hCpm.compl
  have hCcOuter : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ((Set.Ioo m n)ᶜ)] Cpᶜ :=
    cylinderEvents_mono hpairsub _ hCcB
  have hupper : ∫ σ in B, (g σ - c) ∂μ ≤ e := by
    have hsplit : (∫ σ in B ∩ Cp, (g σ - c) ∂μ) + ∫ σ in B \ Cp, (g σ - c) ∂μ
        = ∫ σ in B, (g σ - c) ∂μ := integral_inter_add_sdiff hCpm hsubint.integrableOn
    have hneg : ∫ σ in B \ Cp, (g σ - c) ∂μ ≤ 0 := by
      refine setIntegral_nonpos (hBm.diff hCpm) fun σ hσ ↦ ?_
      have h2 : σ ∉ Cp := hσ.2
      simp only [hCp_def, Set.mem_ofPred_eq, not_le] at h2
      linarith
    have hmono : ∫ σ in B ∩ Cp, (g σ - c) ∂μ ≤ ∫ σ in Cp, (g σ - c) ∂μ := by
      refine setIntegral_mono_set hsubint.integrableOn ?_
        (LE.le.eventuallyLE Set.inter_subset_right)
      refine (ae_restrict_iff' hCpm).2 (Eventually.of_forall fun σ hσ ↦ ?_)
      simp only [hCp_def, Set.mem_ofPred_eq] at hσ
      simp only [Pi.zero_apply]
      linarith
    calc ∫ σ in B, (g σ - c) ∂μ
        = (∫ σ in B ∩ Cp, (g σ - c) ∂μ) + ∫ σ in B \ Cp, (g σ - c) ∂μ := hsplit.symm
      _ ≤ (∫ σ in Cp, (g σ - c) ∂μ) + 0 := add_le_add hmono hneg
      _ = μ.real (A ∩ Cp) - μ.real A * μ.real Cp := by rw [add_zero, hkey Cp hCpOuter]
      _ ≤ e := le_trans (le_abs_self _) (hbound Cp hCpB)
  have hlower : -e ≤ ∫ σ in B, (g σ - c) ∂μ := by
    have hsplit : (∫ σ in B ∩ Cpᶜ, (g σ - c) ∂μ) + ∫ σ in B \ Cpᶜ, (g σ - c) ∂μ
        = ∫ σ in B, (g σ - c) ∂μ := integral_inter_add_sdiff hCcm hsubint.integrableOn
    have hpos : 0 ≤ ∫ σ in B \ Cpᶜ, (g σ - c) ∂μ := by
      refine setIntegral_nonneg (hBm.diff hCcm) fun σ hσ ↦ ?_
      have h2 : σ ∉ Cpᶜ := hσ.2
      simp only [Set.mem_compl_iff, not_not, hCp_def, Set.mem_ofPred_eq] at h2
      linarith
    have hmono : ∫ σ in Cpᶜ, (g σ - c) ∂μ ≤ ∫ σ in B ∩ Cpᶜ, (g σ - c) ∂μ := by
      have hle : ∫ σ in B ∩ Cpᶜ, (-(g σ - c)) ∂μ ≤ ∫ σ in Cpᶜ, (-(g σ - c)) ∂μ := by
        refine setIntegral_mono_set hsubint.neg.integrableOn ?_
          (LE.le.eventuallyLE Set.inter_subset_right)
        refine (ae_restrict_iff' hCcm).2 (Eventually.of_forall fun σ hσ ↦ ?_)
        simp only [Set.mem_compl_iff, hCp_def, Set.mem_ofPred_eq, not_le] at hσ
        simp only [Pi.zero_apply]
        linarith
      rw [integral_neg, integral_neg] at hle
      linarith
    have hCc : ∫ σ in Cpᶜ, (g σ - c) ∂μ = μ.real (A ∩ Cpᶜ) - μ.real A * μ.real Cpᶜ :=
      hkey Cpᶜ hCcOuter
    have hbdd : -e ≤ μ.real (A ∩ Cpᶜ) - μ.real A * μ.real Cpᶜ :=
      neg_le_of_abs_le (hbound Cpᶜ hCcB)
    calc -e ≤ μ.real (A ∩ Cpᶜ) - μ.real A * μ.real Cpᶜ := hbdd
      _ = ∫ σ in Cpᶜ, (g σ - c) ∂μ := hCc.symm
      _ ≤ ∫ σ in B ∩ Cpᶜ, (g σ - c) ∂μ := hmono
      _ ≤ (∫ σ in B ∩ Cpᶜ, (g σ - c) ∂μ) + ∫ σ in B \ Cpᶜ, (g σ - c) ∂μ := le_add_of_nonneg_right
          hpos
      _ = ∫ σ in B, (g σ - c) ∂μ := hsplit
  rw [← hkey B hB]
  exact abs_le.2 ⟨hlower, hupper⟩

omit [IsProbabilityMeasure ν] in
/-- The two-point cylinder σ-algebra is the σ-algebra generated by the pair of coordinates. -/
lemma cylinderEvents_pair_eq_comap (a b : ℤ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) ({a, b} : Set ℤ)
      = MeasurableSpace.comap (fun σ : ℤ → E ↦ (σ a, σ b)) inferInstance := by
  have h1 : ({a, b} : Set ℤ) = ({a} : Set ℤ) ∪ ({b} : Set ℤ) := rfl
  rw [h1, cylinderEvents_union, cylinderEvents_singleton_int, cylinderEvents_singleton_int]
  have h2 : (inferInstance : MeasurableSpace (E × E))
      = MeasurableSpace.comap Prod.fst inferInstance
        ⊔ MeasurableSpace.comap Prod.snd inferInstance := rfl
  rw [h2, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  rfl

omit [IsProbabilityMeasure ν] in
lemma measurableSet_cylinderEvents_pair_iff {a b : ℤ} {C : Set (ℤ → E)} :
    MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ({a, b} : Set ℤ)] C
      ↔ ∃ S : Set (E × E), MeasurableSet S ∧ C = (fun σ : ℤ → E ↦ (σ a, σ b)) ⁻¹' S := by
  rw [cylinderEvents_pair_eq_comap, MeasurableSpace.measurableSet_comap]
  constructor
  · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩
  · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩

/-! ### Georgii §10.3, Theorem (10.35): assembling (10.36)–(10.37) -/

variable (ν p μ) in
/-- The `ℝ≥0∞` mixing bound `Δ_M + 2 Δ_N` of `measure_inter_pair_le`, abbreviated. -/
noncomputable def mixBound (ν : Measure E) (p : E → E → ℝ≥0∞) (μ : Measure (ℤ → E)) (M N : ℕ) :
    ℝ≥0∞ :=
  (∫⁻ y, tvDensity ν p (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) M y
      ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)))
    + 2 * ∫⁻ y, tvDensity ν p (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) N y
      ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ))

lemma mixBound_ne_top [IsProbabilityMeasure μ] [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x))
    {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) : mixBound ν p μ M N ≠ ⊤ := by
  have hαprob : IsProbabilityMeasure (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℤ)).aemeasurable
  have hrmeas : Measurable (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) :=
    measurable_stationaryDensity hp
  have hαr : (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ))
      = ν.withDensity (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) :=
    map_eval_eq_withDensity_stationaryDensity hchain hmarg hp hQ
  exact ENNReal.add_ne_top.2
    ⟨lintegral_tvDensity_ne_top hp hQ hrmeas hαr hM,
      ENNReal.mul_ne_top (by norm_num) (lintegral_tvDensity_ne_top hp hQ hrmeas hαr hN)⟩

/-- **Georgii's estimate (10.37)**, real absolute-value form, for an arbitrary `C ∈ 𝓕_{{m, k+N}}`
(not just the events used in Step 1 of the proof, `{i} × 𝓔` etc.: any pair-cylinder event). -/
theorem abs_measureReal_inter_pair_sub_le [IsProbabilityMeasure μ] [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x))
    {i k m : ℤ} {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hm : m = i - 1 - (M : ℤ))
    {A : Set (ℤ → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Icc i k)] A)
    (hik : i ≤ k)
    {C : Set (ℤ → E)}
    (hC : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ({m, k + (N : ℤ)} : Set ℤ)] C) :
    |μ.real (A ∩ C) - μ.real A * μ.real C| ≤ (mixBound ν p μ M N).toReal := by
  obtain ⟨S, hS, rfl⟩ := measurableSet_cylinderEvents_pair_iff.1 hC
  obtain ⟨h1, h2⟩ := measure_inter_pair_le hchain hmarg hp hQ hM hN hm hA hik hS
  exact abs_measureReal_inter_sub_mul_le (mixBound_ne_top hchain hmarg hp hQ hM hN) h1 h2

/-- **Georgii (10.36)–(10.37) assembled.** For `A` a cylinder event on `[i, k]` and `M, N ≥ 1`,
the covariance bound `Δ_M + 2 Δ_N` holds for *every* exterior event `B`, not just the two boundary
coordinates `{m, n}`: this is the reduction of (10.37) to a general `B ∈ 𝓕_{]m,n[ᶜ}` via the
Markov property, `measureReal_inter_sub_le_of_isMarkovOn`. -/
theorem abs_measureReal_inter_sub_le_of_cylinderEvents [IsProbabilityMeasure μ] [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x))
    {i k : ℤ} {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    {A : Set (ℤ → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Icc i k)] A)
    (hik : i ≤ k)
    {B : Set (ℤ → E)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
      ((Set.Ioo (i - 1 - (M : ℤ)) (k + (N : ℤ)))ᶜ)] B) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ (mixBound ν p μ M N).toReal := by
  have hmn : (i - 1 - (M : ℤ)) + 1 < k + (N : ℤ) := by
    have : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    have : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    omega
  have hMark : IsMarkovOn μ (Set.Ioo (i - 1 - (M : ℤ)) (k + (N : ℤ))) :=
    (hchain.isMarkovField (P := fun _ : ℤ ↦ Q)).isMarkovOn_Ioo _ _
  have hAIoo : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
      (Set.Ioo (i - 1 - (M : ℤ)) (k + (N : ℤ)))] A := by
    refine cylinderEvents_mono ?_ _ hA
    intro x hx
    simp only [Set.mem_Icc] at hx
    have hMz : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    have hNz : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    simp only [Set.mem_Ioo]
    omega
  exact measureReal_inter_sub_le_of_isMarkovOn hmn hMark hAIoo
    (fun C hC ↦ abs_measureReal_inter_pair_sub_le hchain hmarg hp hQ hM hN rfl hA hik hC) hB

/-- **Georgii (10.36) for a fixed cylinder event.** For a cylinder event `A ∈ 𝓕_{[i,k]}` and
`ε > 0`, some interval `]i - 1 - n₀, k + n₀[` has the property that every `B` outside it satisfies
`|μ(A ∩ B) - μ(A) μ(B)| ≤ ε`. Georgii, Theorem (10.34) supplies the vanishing of the mixing bound
`Δ_n + 2 Δ_n`. -/
theorem exists_abs_measureReal_inter_sub_le_of_cylinderEvents [StandardBorelSpace E]
    [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hMk : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμ : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x))
    {i k : ℤ} {A : Set (ℤ → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Icc i k)] A) (hik : i ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ B, MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E)
        ((Set.Ioo (i - 1 - (n₀ : ℤ)) (k + (n₀ : ℤ)))ᶜ)] B →
      |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ ε := by
  have htend := tendsto_lintegral_tvDensity hγ hρ hMk hhom hirr hμ hchain hmarg hp hQ
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    ((ENNReal.tendsto_nhds_zero.1 htend) (ENNReal.ofReal (ε / 3))
      (ENNReal.ofReal_pos.2 (by linarith)))
  set n₀ : ℕ := max n₁ 1 with hn₀_def
  have hn₀1 : 1 ≤ n₀ := le_max_right _ _
  have hn₀n₁ : n₁ ≤ n₀ := le_max_left _ _
  have hbound : (∫⁻ y, tvDensity ν p (stationaryDensity (μ.map fun ω : ℤ → E ↦ ω (0 : ℤ)) p) n₀ y
      ∂(μ.map fun ω : ℤ → E ↦ ω (0 : ℤ))) ≤ ENNReal.ofReal (ε / 3) := hn₁ n₀ hn₀n₁
  have hmix : mixBound ν p μ n₀ n₀ ≤ ENNReal.ofReal ε := by
    have hstep : ENNReal.ofReal (ε / 3) + 2 * ENNReal.ofReal (ε / 3) = ENNReal.ofReal ε := by
      rw [show (2 : ℝ≥0∞) * ENNReal.ofReal (ε / 3) = ENNReal.ofReal (2 * (ε / 3)) by
          rw [ENNReal.ofReal_mul (by norm_num)]; norm_num,
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
      ring_nf
    calc mixBound ν p μ n₀ n₀ ≤ ENNReal.ofReal (ε / 3) + 2 * ENNReal.ofReal (ε / 3) := by
          unfold mixBound; gcongr
      _ = ENNReal.ofReal ε := hstep
  have htoReal : (mixBound ν p μ n₀ n₀).toReal ≤ ε := by
    calc (mixBound ν p μ n₀ n₀).toReal ≤ (ENNReal.ofReal ε).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hmix
      _ = ε := ENNReal.toReal_ofReal hε.le
  refine ⟨n₀, hn₀1, fun B hB ↦ ?_⟩
  exact le_trans
    (abs_measureReal_inter_sub_le_of_cylinderEvents hchain hmarg hp hQ hn₀1 hn₀1 hA hik hB)
    htoReal

/-- **Georgii (10.36).** For every cylinder event `A` and `ε > 0`, all large enough finite volumes
`Λ` satisfy `|μ(A ∩ B) - μ(A) μ(B)| ≤ ε` for every `B ∈ 𝓕_{Λᶜ}`. -/
theorem eventually_abs_measureReal_inter_sub_le_of_mem_localEvents [StandardBorelSpace E]
    [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hMk : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμ : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x))
    {A : Set (ℤ → E)} (hA : A ∈ localEvents ℤ E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Λ : Finset ℤ in Filter.atTop,
      ∀ B, MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ((Λ : Set ℤ)ᶜ)] B →
        |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ ε := by
  classical
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  obtain ⟨i, k, hik, hsub⟩ : ∃ i k : ℤ, i ≤ k ∧ (Λ : Set ℤ) ⊆ Set.Icc i k := by
    rcases Λ.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 0, le_refl _, by simp⟩
    · exact ⟨Λ.min' hne, Λ.max' hne, Λ.min'_le_max' hne,
        fun x hx ↦ ⟨Λ.min'_le x hx, Λ.le_max' x hx⟩⟩
  have hAIcc : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Icc i k)] A :=
    cylinderEvents_mono hsub _ hΛ
  obtain ⟨n₀, hn₀1, hn₀⟩ := exists_abs_measureReal_inter_sub_le_of_cylinderEvents
    hγ hρ hMk hhom hirr hμ hchain hmarg hp hQ hAIcc hik hε
  set Λ₀ : Finset ℤ := Finset.Icc (i - 1 - (n₀ : ℤ)) (k + (n₀ : ℤ)) with hΛ₀_def
  filter_upwards [Filter.eventually_ge_atTop Λ₀] with Λ' hΛ' B hB
  have hsubΛ' : Set.Ioo (i - 1 - (n₀ : ℤ)) (k + (n₀ : ℤ)) ⊆ (Λ' : Set ℤ) := by
    intro x hx
    have hxΛ₀ : x ∈ Λ₀ := by
      simp only [hΛ₀_def, Finset.mem_Icc]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact Finset.mem_coe.2 (Finset.mem_of_subset hΛ' hxΛ₀)
  exact hn₀ B (cylinderEvents_mono (compl_subset_compl.2 hsubΛ') _ hB)

/-- **Georgii (7.9)'s hypothesis, checked.** (10.36) extends from cylinder events to *all*
measurable `A`: approximate `A` in measure by a cylinder event `A'`
(`exists_mem_localEvents_measure_symmDiff_lt`, Georgii's "well-known corollary of Carathéodory's
extension theorem") and transfer the bound at the cost of `2 μ (A ∆ A')`. -/
theorem eventually_abs_measureReal_inter_sub_le [StandardBorelSpace E] [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hMk : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμ : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x))
    {A : Set (ℤ → E)} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Λ : Finset ℤ in Filter.atTop,
      ∀ B, MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ((Λ : Set ℤ)ᶜ)] B →
        |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ ε := by
  classical
  obtain ⟨A', hA'loc, hA'sd⟩ := exists_mem_localEvents_measure_symmDiff_lt μ hA
    (ε := ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.2 (by linarith))
  obtain ⟨Λ', hΛ'⟩ := mem_localEvents_iff_cylinderEvents.1 hA'loc
  have hA'm : MeasurableSet A' := cylinderEvents_le_pi _ hΛ'
  have hA'sdreal : μ.real (A ∆ A') < ε / 4 := by
    have h1 : (μ (A ∆ A')).toReal < (ENNReal.ofReal (ε / 4)).toReal :=
      (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).2 hA'sd
    rwa [ENNReal.toReal_ofReal (by linarith)] at h1
  have h := eventually_abs_measureReal_inter_sub_le_of_mem_localEvents hγ hρ hMk hhom hirr hμ
    hchain hmarg hp hQ hA'loc (ε := ε / 2) (by linarith)
  filter_upwards [h] with Λ hΛ B hB
  have hBm : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hstep1 : |μ.real (A ∩ B) - μ.real (A' ∩ B)| ≤ μ.real (A ∆ A') := by
    have hne : NullMeasurableSet (A ∩ B) μ := (hA.inter hBm).nullMeasurableSet
    have hne' : NullMeasurableSet (A' ∩ B) μ := (hA'm.inter hBm).nullMeasurableSet
    calc |μ.real (A ∩ B) - μ.real (A' ∩ B)|
        ≤ μ.real ((A ∩ B) ∆ (A' ∩ B)) := abs_measureReal_sub_le_measureReal_symmDiff hne hne'
      _ = μ.real ((A ∆ A') ∩ B) := by rw [inter_symmDiff_distrib_right]
      _ ≤ μ.real (A ∆ A') := measureReal_mono Set.inter_subset_left (measure_ne_top μ _)
  have hstep2 : |μ.real A - μ.real A'| ≤ μ.real (A ∆ A') :=
    abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet hA'm.nullMeasurableSet
  have hBle1 : μ.real B ≤ 1 := by
    have := prob_le_one (μ := μ) (s := B)
    simpa [measureReal_def] using ENNReal.toReal_mono ENNReal.one_ne_top this
  have hstep3 : |μ.real A * μ.real B - μ.real A' * μ.real B| ≤ μ.real (A ∆ A') := by
    have hBnn : 0 ≤ μ.real B := measureReal_nonneg
    calc |μ.real A * μ.real B - μ.real A' * μ.real B|
        = |μ.real A - μ.real A'| * μ.real B := by rw [← sub_mul, abs_mul, abs_of_nonneg hBnn]
      _ ≤ μ.real (A ∆ A') * μ.real B := by gcongr
      _ ≤ μ.real (A ∆ A') * 1 := by gcongr
      _ = μ.real (A ∆ A') := mul_one _
  calc |μ.real (A ∩ B) - μ.real A * μ.real B|
      ≤ |μ.real (A ∩ B) - μ.real (A' ∩ B)|
          + |μ.real (A' ∩ B) - μ.real A' * μ.real B|
          + |μ.real A' * μ.real B - μ.real A * μ.real B| := by
        have := abs_sub_le (μ.real (A ∩ B)) (μ.real (A' ∩ B)) (μ.real A * μ.real B)
        have h2 := abs_sub_le (μ.real (A' ∩ B)) (μ.real A' * μ.real B) (μ.real A * μ.real B)
        calc |μ.real (A ∩ B) - μ.real A * μ.real B|
            ≤ |μ.real (A ∩ B) - μ.real (A' ∩ B)| + |μ.real (A' ∩ B) - μ.real A * μ.real B| := this
          _ ≤ |μ.real (A ∩ B) - μ.real (A' ∩ B)|
              + (|μ.real (A' ∩ B) - μ.real A' * μ.real B|
                + |μ.real A' * μ.real B - μ.real A * μ.real B|) := by gcongr
          _ = |μ.real (A ∩ B) - μ.real (A' ∩ B)| + |μ.real (A' ∩ B) - μ.real A' * μ.real B|
              + |μ.real A' * μ.real B - μ.real A * μ.real B| := by ring
    _ ≤ μ.real (A ∆ A') + (ε / 2) + μ.real (A ∆ A') := by
        gcongr
        · exact hΛ B hB
        · rw [abs_sub_comm]; exact hstep3
    _ ≤ ε / 4 + ε / 2 + ε / 4 := by
        have := hA'sdreal.le
        gcongr
    _ = ε := by ring

/-- **Georgii, Proposition (7.9), checked.** A shift-invariant Gibbs measure of an irreducible
homogeneous Markovian `λ`-modification, seen as a Markov chain (Theorem (10.25)), is trivial on
the tail σ-algebra. -/
theorem isTailTrivial_of_isMarkovChain [StandardBorelSpace E] [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hMk : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμGibbs : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x)) :
    IsTailTrivial (S := ℤ) (E := E)
      (⟨μ, ‹IsProbabilityMeasure μ›⟩ : ProbabilityMeasure (ℤ → E)) := by
  have h : ∀ A, MeasurableSet[@tailSigmaAlgebra ℤ E _] A → μ A = 0 ∨ μ A = 1 :=
    forall_tail_measure_eq_zero_or_one_iff (μ := μ) |>.2
      (fun A hA ε hε ↦ eventually_abs_measureReal_inter_sub_le hγ hρ hMk hhom hirr hμGibbs
        hchain hmarg hp hQ hA hε)
  exact h

/-- **Georgii, §10.3, main step**: `𝒢_Θ(γ) ⊆ ex 𝒢(γ)`, pointwise. Every shift-invariant Gibbs
measure of an irreducible homogeneous Markovian `λ`-modification is *extreme* in `𝒢(γ)`. Combined
with the shift-invariance and Gibbs property of `μ`, this is what makes `𝒢_Θ(γ)` a subsingleton
(Georgii, Theorem (10.35)): two distinct such measures would make their midpoint a shift-invariant
Gibbs measure that is a proper convex combination of two points of `G(γ)`, hence not extreme,
contradicting `𝒢_Θ(γ) ⊆ ex 𝒢(γ)`. -/
theorem mem_extremePoints_G_of_isMarkovChain [StandardBorelSpace E] [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hMk : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμGibbs : γ.IsGibbsMeasure μ) [IsMarkovKernel Q]
    (hchain : IsMarkovChain (fun _ ↦ Q) μ)
    (hmarg : ∀ i : ℤ, μ.map (fun ω ↦ ω i) = μ.map (fun ω ↦ ω (0 : ℤ)))
    (hp : Measurable (Function.uncurry p)) (hQ : ∀ x, Q x = ν.withDensity (p x)) :
    μ ∈ (MeasureTheory.GibbsMeasure.G (γ := γ)).extremePoints ℝ≥0∞ := by
  have hμG : μ ∈ MeasureTheory.GibbsMeasure.G (γ := γ) := ⟨‹IsProbabilityMeasure μ›, hμGibbs⟩
  exact MeasureTheory.GibbsMeasure.mem_extremePoints_G_of_isTailTrivial hμG
    (isTailTrivial_of_isMarkovChain hγ hρ hMk hhom hirr hμGibbs hchain hmarg hp hQ)

/-- **Georgii, §10.3, main step, at Georgii's actual hypotheses.** For `γ = ρλ` with `ρ` an
irreducible homogeneous Markovian `λ`-modification, every shift-invariant `μ ∈ 𝒢(γ)` is extreme in
`𝒢(γ)`: `𝒢_Θ(γ) ⊆ ex 𝒢(γ)`. Theorem (10.25) supplies the transition kernel; the rest is
`mem_extremePoints_G_of_isMarkovChain`. -/
theorem mem_extremePoints_G_of_measurePreserving_shift [StandardBorelSpace E]
    [IsProbabilityMeasure μ]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hMk : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ) (hμGibbs : γ.IsGibbsMeasure μ)
    (hshift : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    μ ∈ (MeasureTheory.GibbsMeasure.G (γ := γ)).extremePoints ℝ≥0∞ := by
  obtain ⟨p, P, hpmeas, hPapply, hPmarkov, hchain⟩ :=
    exists_isMarkovChain_of_measurePreserving_shift hγ hρ hMk hhom hirr hμGibbs hshift
  exact mem_extremePoints_G_of_isMarkovChain hγ hρ hMk hhom hirr hμGibbs (Q := P) hchain
    (map_eval_eq_of_measurePreserving_shift hshift) hpmeas hPapply

/-- **Georgii, Theorem (10.35).** For `γ = ρλ` with `ρ` an irreducible homogeneous Markovian
`λ`-modification on a standard Borel `(E, 𝓔)`, there is at most one shift-invariant Gibbs measure:
`𝒢_Θ(γ)` is a subsingleton.

Georgii's proof: two distinct shift-invariant Gibbs measures `μ₁ ≠ μ₂` would make the midpoint
`m = (μ₁ + μ₂) / 2` a shift-invariant Gibbs measure lying in the *open* segment between `μ₁` and
`μ₂`, both in `𝒢(γ)`. But `m` is extreme in `𝒢(γ)` (the pointwise step above), and an extreme
point cannot be a nontrivial convex combination of two *distinct* points of the ambient set — so
`μ₁ = m = μ₂`, contradiction. -/
theorem eq_of_isGibbsMeasure_of_measurePreserving_shift [StandardBorelSpace E]
    (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
    (hρ : ∀ Λ, Measurable (ρ Λ)) (hMk : IsMarkovianInt ρ) (hhom : IsHomogeneousInt ρ)
    (hirr : IsIrreducibleInt ν ρ)
    {μ₁ μ₂ : Measure (ℤ → E)} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : γ.IsGibbsMeasure μ₁) (hμ₂ : γ.IsGibbsMeasure μ₂)
    (hshift₁ : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ₁ μ₁)
    (hshift₂ : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ₂ μ₂) :
    μ₁ = μ₂ := by
  by_contra hne
  set s : ℝ≥0∞ := 2⁻¹ with hs_def
  have hs2 : s + s = 1 := by
    rw [hs_def, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero (by norm_num)]
  have hspos : 0 < s := by rw [hs_def]; exact ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  set m : Measure (ℤ → E) := s • μ₁ + s • μ₂ with hm_def
  have hmprob : IsProbabilityMeasure m := by
    constructor
    rw [hm_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul, measure_univ, measure_univ, mul_one, hs2]
  have hmGibbs : γ.IsGibbsMeasure m := by
    rw [Specification.isGibbsMeasure_iff_forall_bind_eq]
    intro Λ
    have h1 : μ₁.bind (γ Λ) = μ₁ := (Specification.isGibbsMeasure_iff_forall_bind_eq).1 hμ₁ Λ
    have h2 : μ₂.bind (γ Λ) = μ₂ := (Specification.isGibbsMeasure_iff_forall_bind_eq).1 hμ₂ Λ
    rw [hm_def, Measure.bind_add (s • μ₁) (s • μ₂) (γ Λ) (γ.measurable_kernel_toMeasure Λ),
      Measure.bind_smul, Measure.bind_smul, h1, h2]
  have hmshift : ∀ a : ℤ, MeasurePreserving (shift E a).toFun m m := by
    intro a
    have hmeasa : Measurable (shift E a).toFun := (shift E a).measurable_toFun
    refine ⟨hmeasa, ?_⟩
    rw [hm_def, Measure.map_add _ _ hmeasa, Measure.map_smul, Measure.map_smul,
      (hshift₁ a).2, (hshift₂ a).2]
  have hmext := mem_extremePoints_G_of_measurePreserving_shift hγ hρ hMk hhom hirr hmGibbs hmshift
  have hseg : m ∈ openSegment ℝ≥0∞ μ₁ μ₂ := ⟨s, s, hspos, hspos, hs2, hm_def⟩
  have hμ₁G : μ₁ ∈ MeasureTheory.GibbsMeasure.G (γ := γ) := ⟨inferInstance, hμ₁⟩
  have hμ₂G : μ₂ ∈ MeasureTheory.GibbsMeasure.G (γ := γ) := ⟨inferInstance, hμ₂⟩
  have hboth := (mem_extremePoints.1 hmext).2 μ₁ hμ₁G μ₂ hμ₂G hseg
  exact hne (hboth.1.trans hboth.2.symm)

end Uniqueness

end MeasureTheory.GibbsMeasure.Markov
