/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.SetwiseConvergence
public import GibbsMeasure.Specification.UniformLocalLimits
public import GibbsMeasure.Specification.ErgodicDense
public import GibbsMeasure.Specification.Transformation
public import GibbsMeasure.Mathlib.Dynamics.Ergodic.Pointwise
public import GibbsMeasure.Mathlib.Probability.Martingale.DominatedBackward

/-!
# Georgii, Theorem (14.20): ergodic Gibbs measures as limits of averaged Gibbs distributions

Let `γ` be a specification on `S → E` over a countable abelian group of sites `S` (Georgii:
`ℤ^d`), `Θ` its shift group, and `μ ∈ ex 𝒢_Θ(γ)` an extreme shift-invariant Gibbs measure — by
Theorem (14.15)(a), a Gibbs measure which is shift-invariant and **ergodic**, i.e. trivial on the
invariant σ-algebra `𝓘`. Let `F n` be an increasing regular Følner sequence of finite sets of sites
(Georgii: the cubes `Λ_n = [-n, n]^d`) and `Λ n` an increasing sequence of volumes (Georgii takes
`Λ n = F n`; nothing forces this, so the two roles are kept apart). Then, as `n → ∞`:

* **(a)** `γ_{Λ n}(|F n|⁻¹ ∑_{i ∈ F n} f ∘ θ_i) → μ(f)` `μ`-a.s. for every bounded measurable `f`
  (`MeasureTheory.GibbsMeasure.ae_tendsto_integral_kernel_inv_card_smul_sum_shift`, and the
  version `…_inv_card_smul_sum_vadd` for an arbitrary measure-preserving action);
* **(b)** if `E` is compact metrizable and `γ` is shift-invariant, the averaged Gibbs
  distributions `|F n|⁻¹ ∑_{i ∈ F n} γ_{Λ n + i}(· | θ_i ω)` (`Specification.shiftAverage`)
  converge **weakly** to `μ` for `μ`-almost all `ω`
  (`MeasureTheory.GibbsMeasure.ae_tendsto_shiftAverage_weakly`);
* **(c)** if `γ = ρ λ` is a λ-specification, they converge to `μ` **in the topology of local
  convergence** for `μ`-almost all `ω`
  (`Specification.ae_tendsto_shiftAverage_withLocalConvergence`, and
  `…_lambdaSpecification` for Georgii's λ-specifications of Definition (1.27)), provided that for
  every site `δ` the fraction of `i ∈ F n` with `δ ∉ Λ n + i` vanishes.

The cubes of `ℤ^d` are the instance (`…_cube`, section `Lattice`).

## The proofs

**(a)** is Georgii's: the pointwise ergodic theorem (14.A8)
(`MeasureTheory.ae_tendsto_inv_card_smul_sum_vadd_condExp`) makes the ergodic averages
`f_n = |F n|⁻¹ ∑ f ∘ θ_i` converge a.s. to `μ(f | 𝓘) = μ(f)`; the DLR equation identifies
`γ_{Λ n} f_n` with `μ(f_n | 𝓣_{Λ n})`; and dominated convergence for reversed martingales, Lemma
(14.19) (`MeasureTheory.tendsto_ae_condExp_of_antitone_of_dominated`), along the decreasing
σ-algebras `𝓣_{Λ n}` finishes. Neither the shift-invariance of `γ` nor the cofinality of `Λ` is
used. The combination of (14.A8) and (14.19) is stated on its own as
`MeasureTheory.ae_tendsto_condExp_inv_card_smul_sum_vadd`.

**(b)** follows from (a) through Georgii (5.5): for a shift-invariant `γ`,
`γ_{Λ + i}(f | θ_i ω) = γ_Λ(f ∘ θ_i | ω)`
(`Specification.integral_shiftAverage_eq_integral_kernel`), and a countable sup-norm dense set of
bounded continuous functions, as in (7.12)(b).

**(c)** is Georgii's density argument on the product space `ν̃ = μ ⊗ λ^Δ` of boundary conditions
and inner configurations. For a finite volume `Δ` and the covering indices
`Λ'_n = {i ∈ F n : Λ n + i ⊇ Δ}` (`Specification.coveringIndices`), the averaged density
`ρ̃^n_Δ(ω, ζ) = |Λ'_n|⁻¹ ∑_{i ∈ Λ'_n} ρ_Δ^{Λ n + i}(ζ (θ_i ω)_{S∖Δ})`
(`Specification.shiftAvgCondDensity`) is the conditional expectation, given the product σ-algebra
`𝓣_{Λ n} × 𝓕_Δ` (`Specification.tailProdEvents`), of the ergodic average
`|Λ'_n|⁻¹ ∑ ρ̃_Δ ∘ θ̃_i` of `ρ̃_Δ(ω, ζ) = ρ_Δ(ζ ω_{S∖Δ})` (14.22,
`Specification.toReal_shiftAvgCondDensity_ae_eq_condExp`); these averages converge `ν̃`-a.s. to
`ρ̄_Δ(ζ) = ∫ μ(dη) ρ_Δ(ζ η_{S∖Δ})` (`Specification.avgKernel`) by the ergodic theorem for `μ`
applied at each fixed inner configuration `ζ` and Fubini (14.23)–(14.24); Lemma (14.19) and
Scheffé's lemma then give `λ^Δ(|ρ̃^n_Δ(ω, ·) - ρ̄_Δ|) → 0` for `μ`-a.a. `ω`, which controls the
averaged distributions on all events of `Δ` at once
(`Specification.abs_shiftAverage_real_sub_le_integral_abs`); `Countable S` lets one `μ`-full set
serve every `Δ`.

### A gap in Georgii's proof of (c)

Georgii applies Lemma (14.19) to `f_n = |Λ'_n|⁻¹ ∑ ρ̃_Δ ∘ θ̃_i`. Its hypothesis (i), `|f_n| ≤ g`
with `g` integrable, asks for the ergodic maximal function of `ρ̃_Δ` to be integrable, which fails
for a general λ-modification `ρ` (it needs `ρ_Δ ∈ L log L`). The dominated hypothesis **is**
available for the truncations `min ρ_Δ M`, and for these (14.19) gives
`liminf_n ρ̃^n_Δ ≥ ρ̄^M_Δ` by monotonicity of conditional expectations; letting `M → ∞` yields the
one-sided bound `liminf_n ρ̃^n_Δ ≥ ρ̄_Δ`
(`Specification.ae_forall_lt_eventually_le_toReal_shiftAvgCondDensity`). A one-sided bound is
all Scheffé's lemma needs when the integrals agree
(`MeasureTheory.tendsto_integral_abs_sub_of_forall_lt_eventually_le`): the negative parts
`(ρ̃^n_Δ - ρ̄_Δ)⁻ ≤ ρ̄_Δ` vanish a.e., hence in `L¹`, and the positive parts have the same
integrals. The theorem is therefore proved as stated; only the route through (14.19) is repaired.

## Hypotheses

The ergodicity of `μ` enters only through triviality on `invariantEvents (shiftGroup S E)`, the
form of Definition (14.6) / Theorem (14.15)(a); `μ ∈ ex 𝒢_Θ(γ)` is the corollary
(`…_of_mem_extremePoints_invariantG`, which needs `Infinite S` for Proposition (14.9)). The
Følner and Tempelman hypotheses on `F` are those of the ergodic theorem
`GibbsMeasure/Mathlib/Dynamics/Ergodic/Pointwise.lean`. In (c) the a priori measure `λ` is a
probability measure, as Georgii assumes without loss by Remark (1.28)(3)
(`Specification.lambdaSpecification_probNormalize`).

The general measure-theoretic lemmas of the section *measure-theoretic tools* — set integrals on
a product of sub-σ-algebras, the one-sided Scheffé lemma, the measurability of the set of
convergence — are Mathlib material kept here with the theorem that needs them.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal Topology symmDiff Pointwise BoundedContinuousFunction

namespace MeasureTheory

/-! ### Conditional expectations under a zero-one law -/

/-! ### Ergodic averages conditioned along a decreasing filtration -/

section ErgodicAverages

variable {G Ω : Type*} [AddCommGroup G] [AddAction G Ω] [MeasurableSpace Ω] {μ : Measure Ω}
  [MeasurableConstVAdd G Ω] [VAddInvariantMeasure G Ω μ]

/-- The ergodic averages `R_n f = |F n|⁻¹ ∑_{i ∈ F n} f ∘ (i +ᵥ ·)` of an a.e. strongly
measurable function are a.e. strongly measurable. -/
lemma aestronglyMeasurable_inv_card_smul_sum_vadd {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (s : Finset G) :
    AEStronglyMeasurable (fun ω ↦ (s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω)) μ := by
  have h : (fun ω ↦ (s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω)) =
      (s.card : ℝ)⁻¹ • ∑ i ∈ s, f ∘ (fun x ↦ i +ᵥ x) := by
    funext ω; simp [Finset.sum_apply]
  rw [h]
  exact (Finset.aestronglyMeasurable_sum s fun i _ ↦
    hf.comp_quasiMeasurePreserving (measurePreserving_vadd i μ).quasiMeasurePreserving).const_smul _

/-- The ergodic averages of a function a.e. bounded by `M` are a.e. bounded by `M`, on the
non-empty averaging sets. -/
lemma ae_norm_inv_card_smul_sum_vadd_le [Countable G] {f : Ω → ℝ} {M : ℝ} (hM : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M)
    {s : Finset G} (hs : s.Nonempty) :
    ∀ᵐ ω ∂μ, ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω)‖ ≤ M := by
  have h : ∀ᵐ ω ∂μ, ∀ i : G, ‖f (i +ᵥ ω)‖ ≤ M :=
    ae_all_iff.2 fun i ↦ (measurePreserving_vadd i μ).quasiMeasurePreserving.ae hM
  filter_upwards [h] with ω hω
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_le_iff₀ hcard]
  calc ‖∑ i ∈ s, f (i +ᵥ ω)‖ ≤ ∑ i ∈ s, ‖f (i +ᵥ ω)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ s, M := Finset.sum_le_sum fun i _ ↦ hω i
    _ = s.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

variable [IsFiniteMeasure μ] [Countable G] [DecidableEq G] {F : ℕ → Finset G} {C : ℝ≥0∞}

/-- **Ergodic averages conditioned along a decreasing filtration.** Let `F` be an increasing
regular Følner sequence for a measure-preserving action of `G` on a finite measure space and
`ℱ` a decreasing sequence of sub-σ-algebras. For an a.e. bounded `f`, the conditional
expectations `μ[R_n f | ℱ n]` of the ergodic averages converge a.e. to
`μ[μ[f | 𝓘] | ⨅ n, ℱ n]`: the pointwise ergodic theorem (Georgii (14.A8)) identifies the a.e.
limit of `R_n f`, and dominated convergence for reversed martingales (Georgii (14.19)) passes it
through the diagonal conditional expectations. -/
theorem ae_tendsto_condExp_inv_card_smul_sum_vadd
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {ℱ : ℕ → MeasurableSpace Ω} (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ ‹MeasurableSpace Ω›)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ} (hM : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (μ[fun x ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ x) | ℱ n]) ω)
      atTop (𝓝 ((μ[μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω] | ⨅ n, ℱ n]) ω)) := by
  have hfi : Integrable f μ := .of_bound hf M hM
  have hne' : ∀ n, (F n).Nonempty := fun n ↦ hne.mono (hF (Nat.zero_le n))
  exact tendsto_ae_condExp_of_antitone_of_dominated hℱ hle
    (fun n ↦ aestronglyMeasurable_inv_card_smul_sum_vadd hf (F n)) (integrable_const M)
    (fun n ↦ ae_norm_inv_card_smul_sum_vadd_le hM (hne' n))
    (ae_tendsto_inv_card_smul_sum_vadd_condExp hF hne hFol hC hC' hfi)

/-- **Ergodic averages conditioned along a decreasing filtration, ergodic case.** If moreover the
probability measure `μ` is trivial on the invariant σ-algebra `𝓘` (ergodic, Georgii (14.6)), the
limit is the constant `∫ f dμ`. -/
theorem ae_tendsto_condExp_inv_card_smul_sum_vadd_of_forall_measure_eq_zero_or_one
    [IsProbabilityMeasure μ] (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (htriv : ∀ A, MeasurableSet[MeasurableSpace.smulInvariants (Multiplicative G) Ω] A →
      μ A = 0 ∨ μ A = 1)
    {ℱ : ℕ → MeasurableSpace Ω} (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ ‹MeasurableSpace Ω›)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ} (hM : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (μ[fun x ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ x) | ℱ n]) ω)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hfi : Integrable f μ := .of_bound hf M hM
  have hne' : ∀ n, (F n).Nonempty := fun n ↦ hne.mono (hF (Nat.zero_le n))
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω)) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
    filter_upwards [ae_tendsto_inv_card_smul_sum_vadd_condExp hF hne hFol hC hC' hfi,
      condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one
        MeasurableSpace.smulInvariants_le htriv f] with ω hω hc
    rwa [hc] at hω
  have h := tendsto_ae_condExp_of_antitone_of_dominated hℱ hle
    (fun n ↦ aestronglyMeasurable_inv_card_smul_sum_vadd hf (F n)) (integrable_const M)
    (fun n ↦ ae_norm_inv_card_smul_sum_vadd_le hM (hne' n)) hlim
  rwa [condExp_const ((iInf_le ℱ 0).trans (hle 0))] at h

end ErgodicAverages

end MeasureTheory

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ### Georgii (14.20)(a): a measure-preserving action with a regular Følner sequence -/

section PartAGeneral

variable {G : Type*} [AddCommGroup G] [Countable G] [DecidableEq G] [AddAction G (S → E)]
  [MeasurableConstVAdd G (S → E)] {μ : Measure (S → E)} {γ : Specification S E}
  {F : ℕ → Finset G} {C : ℝ≥0∞}

/-- **Georgii, Theorem (14.20)(a)**, for an arbitrary measure-preserving action with an increasing
regular Følner sequence `F`. Let `μ ∈ 𝒢(γ)` be invariant and ergodic under the action, `f` an
a.e. bounded measurable function and `Λ` an increasing sequence of volumes. Then
`γ_{Λ n}(|F n|⁻¹ ∑_{i ∈ F n} f ∘ (i +ᵥ ·)) → μ(f)` `μ`-a.s.

No invariance of `γ` and no cofinality of `Λ` is needed: the ergodic theorem (14.A8) makes the
averages converge to `μ(f)`, the DLR equation identifies `γ_{Λ n} f_n` with `μ(f_n | 𝓣_{Λ n})`,
and Lemma (14.19) with the decreasing σ-algebras `𝓣_{Λ n}` finishes. -/
theorem ae_tendsto_integral_kernel_inv_card_smul_sum_vadd [IsProbabilityMeasure μ]
    [VAddInvariantMeasure G (S → E) μ] (hμ : γ.IsGibbsMeasure μ)
    (htriv : ∀ A, MeasurableSet[MeasurableSpace.smulInvariants (Multiplicative G) (S → E)] A →
      μ A = 0 ∨ μ A = 1)
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ)
    {f : (S → E) → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ} (hM : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ x, ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ x) ∂(γ (Λ n) ω))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hne' : ∀ n, (F n).Nonempty := fun n ↦ hne.mono (hF (Nat.zero_le n))
  have h := ae_tendsto_condExp_inv_card_smul_sum_vadd_of_forall_measure_eq_zero_or_one hF hne hFol
    hC hC' htriv (antitone_cylinderEvents_compl (E := E) hmono) (fun _ ↦ cylinderEvents_le_pi) hf hM
  have h2 : ∀ᵐ ω ∂μ, ∀ n,
      (μ[fun x ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ x) |
        cylinderEvents (X := fun _ : S ↦ E) ((Λ n : Set S)ᶜ)]) ω =
        ∫ x, ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ x) ∂(γ (Λ n) ω) := by
    refine ae_all_iff.2 fun n ↦ ?_
    have : (γ (Λ n)).IsCondExp μ := hμ _
    exact Kernel.condExp_ae_eq_integral (γ.isProper _) cylinderEvents_le_pi _
      (.of_bound (aestronglyMeasurable_inv_card_smul_sum_vadd hf (F n)) M
        (ae_norm_inv_card_smul_sum_vadd_le hM (hne' n)))
  filter_upwards [h, h2] with ω hω h2ω
  exact hω.congr h2ω

end PartAGeneral

attribute [local instance] shiftAddAction measurableConstVAdd_shift

/-! ### Georgii (14.20)(a) for the shift group -/

section PartAShift

variable [AddCommGroup S] [Countable S] [DecidableEq S] {μ : Measure (S → E)}
  {γ : Specification S E} {F : ℕ → Finset S} {C : ℝ≥0∞}

/-- **Georgii, Theorem (14.20)(a)** for the shift group `Θ` of a countable abelian group of
sites. Let `μ ∈ 𝒢(γ)` be shift-invariant and trivial on `𝓘` — by (14.15)(a), `μ ∈ ex 𝒢_Θ(γ)` —
let `F` be an increasing regular Følner sequence of finite sets of sites and `Λ` an increasing
sequence of volumes. Then, for every a.e. bounded measurable `f`,
`γ_{Λ n}(|F n|⁻¹ ∑_{i ∈ F n} f ∘ θ_i) → μ(f)` `μ`-a.s. -/
theorem ae_tendsto_integral_kernel_inv_card_smul_sum_shift [IsProbabilityMeasure μ]
    (hμ : γ.IsGibbsMeasure μ) (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    (htriv : μ ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ)
    {f : (S → E) → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ} (hM : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦
      ∫ x, ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f ((shift E i).toFun x) ∂(γ (Λ n) ω))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  let := shiftAddAction (S := S) (E := E)
  have := vaddInvariantMeasure_of_forall_measurePreserving_shift hμinv
  rw [mem_trivialOn, smulInvariants_multiplicative_eq_invariantEvents_shiftGroup.symm] at htriv
  exact ae_tendsto_integral_kernel_inv_card_smul_sum_vadd hμ htriv hF hne hFol hC hC' hmono hf hM

/-- **Georgii, Theorem (14.20)(a)** as stated: for a shift-invariant specification `γ` on a
countable infinite abelian group of sites and `μ ∈ ex 𝒢_Θ(γ)`. -/
theorem ae_tendsto_integral_kernel_inv_card_smul_sum_shift_of_mem_extremePoints_invariantG
    [Infinite S] (hμ : μ ∈ (invariantG γ (shiftGroup S E)).extremePoints ℝ≥0∞)
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ)
    {f : (S → E) → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ} (hM : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦
      ∫ x, ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f ((shift E i).toFun x) ∂(γ (Λ n) ω))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hμG : μ ∈ invariantG γ (shiftGroup S E) := hμ.1
  have : IsProbabilityMeasure μ := hμG.1.1
  exact ae_tendsto_integral_kernel_inv_card_smul_sum_shift hμG.1.2
    (mem_invariantFields_shiftGroup.1 hμG.2).2
    ((mem_extremePoints_invariantG_iff_mem_trivialOn
      (shiftGroup_exists_disjoint_sites_preimage (E := E)) hμG).1 hμ) hF hne hFol hC hC' hmono hf hM

end PartAShift

end MeasureTheory.GibbsMeasure

/-! ### Georgii's averaged Gibbs distributions `|F|⁻¹ ∑_{i ∈ F} γ_{Λ + i}(· | θ_i ω)` -/

namespace Specification

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] [AddGroup S]

/-- **Georgii, Theorem (14.20)(b),(c): the averaged finite-volume Gibbs distributions**
`|F|⁻¹ ∑_{i ∈ F} γ_{Λ + i}(· | θ_i ω)`, the uniform average over `i ∈ F` of the Gibbs
distributions in the translated volumes `Λ + i` with the shifted boundary conditions `θ_i ω`. -/
noncomputable abbrev shiftAverage (γ : Specification S E) (F Λ : Finset S) (ω : S → E) :
    Measure (S → E) :=
  MeasureTheory.uniformAverage
    (fun i ↦ γ (Λ.map (Equiv.addRight i).toEmbedding) ((shift E i).toFun ω)) F

variable {γ : Specification S E} {F Λ : Finset S} {ω : S → E}

lemma shiftAverage_apply (A : Set (S → E)) :
    γ.shiftAverage F Λ ω A =
      (F.card : ℝ≥0∞)⁻¹ *
        ∑ i ∈ F, γ (Λ.map (Equiv.addRight i).toEmbedding) ((shift E i).toFun ω) A :=
  MeasureTheory.uniformAverage_apply _ F A

lemma isProbabilityMeasure_shiftAverage (hF : F.Nonempty) :
    IsProbabilityMeasure (γ.shiftAverage F Λ ω) :=
  MeasureTheory.isProbabilityMeasure_uniformAverage _ (fun _ ↦ inferInstance) hF

lemma shiftAverage_real_apply (A : Set (S → E)) :
    (γ.shiftAverage F Λ ω).real A =
      (F.card : ℝ)⁻¹ * ∑ i ∈ F,
        (γ (Λ.map (Equiv.addRight i).toEmbedding) ((shift E i).toFun ω)).real A :=
  MeasureTheory.uniformAverage_real_apply _ (fun _ ↦ inferInstance) F A

/-- The integral against the averaged Gibbs distribution is the average of the integrals. -/
lemma integral_shiftAverage {f : (S → E) → ℝ}
    (hf : ∀ i ∈ F, Integrable f (γ (Λ.map (Equiv.addRight i).toEmbedding) ((shift E i).toFun ω))) :
    ∫ x, f x ∂(γ.shiftAverage F Λ ω) =
      (F.card : ℝ)⁻¹ • ∑ i ∈ F,
        ∫ x, f x ∂(γ (Λ.map (Equiv.addRight i).toEmbedding) ((shift E i).toFun ω)) := by
  unfold shiftAverage MeasureTheory.uniformAverage
  rw [integral_smul_measure, integral_finsetSum_measure hf, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

/-- The averaged Gibbs distribution over a non-empty family, as a probability measure. -/
noncomputable def shiftAveragePM (γ : Specification S E) (hF : F.Nonempty) (Λ : Finset S)
    (ω : S → E) : ProbabilityMeasure (S → E) :=
  ⟨γ.shiftAverage F Λ ω, isProbabilityMeasure_shiftAverage hF⟩

@[simp] lemma coe_shiftAveragePM (hF : F.Nonempty) :
    (γ.shiftAveragePM hF Λ ω : Measure (S → E)) = γ.shiftAverage F Λ ω := rfl

end Specification

namespace Specification

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] {γ : Specification S E}
  {F Λ : Finset S} {ω : S → E}

/-- **Georgii (5.5) for the averaged Gibbs distributions.** For a shift-invariant `γ`,
`γ_{Λ + i}(f | θ_i ω) = γ_Λ(f ∘ θ_i | ω)`, so the averaged Gibbs distribution integrates `f` as
`γ_Λ(· | ω)` integrates the ergodic average `|F|⁻¹ ∑_{i ∈ F} f ∘ θ_i`. -/
lemma integral_shiftAverage_eq_integral_kernel
    (hγ : ∀ j : S, IsInvariant (shift E j) γ) {f : (S → E) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) :
    ∫ x, f x ∂(γ.shiftAverage F Λ ω) =
      ∫ x, (F.card : ℝ)⁻¹ • ∑ i ∈ F, f ((shift E i).toFun x) ∂(γ Λ ω) := by
  have hterm : ∀ i : S, ∫ x, f x ∂(γ (Λ.map (Equiv.addRight i).toEmbedding) ((shift E i).toFun ω))
      = ∫ x, f ((shift E i).toFun x) ∂(γ Λ ω) := by
    intro i
    have h := isInvariant_iff.1 (hγ i) Λ ω
    rw [show Λ.map (Equiv.addRight i).toEmbedding = Λ.map (shift E i).sites.toEmbedding from rfl,
      ← h, integral_map (shift E i).measurable_toFun.aemeasurable hf.aestronglyMeasurable]
  rw [integral_shiftAverage fun i _ ↦ .of_bound hf.aestronglyMeasurable M (ae_of_all _ hM),
    integral_smul, integral_finsetSum F (f := fun i x ↦ f ((shift E i).toFun x)) fun i _ ↦
      .of_bound (hf.comp (shift E i).measurable_toFun).aestronglyMeasurable M
        (ae_of_all _ fun x ↦ hM _)]
  simp only [hterm]

end Specification

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ### Georgii (14.20)(b): weak convergence of the averaged Gibbs distributions -/

section PartB

variable [AddCommGroup S] [Countable S] [DecidableEq S] [TopologicalSpace E] [CompactSpace E]
  [TopologicalSpace.MetrizableSpace E] [BorelSpace E] {γ : Specification S E}
  {F : ℕ → Finset S} {C : ℝ≥0∞}

/-- **Georgii, Theorem (14.20)(b)**, unfolded: for a shift-invariant specification `γ` over a
compact metrizable state space, `μ ∈ 𝒢(γ)` shift-invariant and ergodic, an increasing regular
Følner sequence `F` and an increasing sequence of volumes `Λ`, for `μ`-almost all `ω`,
`|F n|⁻¹ ∑_{i ∈ F n} γ_{Λ n + i}(f | θ_i ω) → μ(f)` for **every** bounded continuous `f`. -/
theorem ae_forall_tendsto_integral_boundedContinuous_shiftAverage
    (hγ : ∀ j : S, Specification.IsInvariant (shift E j) γ) {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hμ : γ.IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    (htriv : μ ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) :
    ∀ᵐ ω ∂μ, ∀ f : (S → E) →ᵇ ℝ,
      Tendsto (fun n ↦ ∫ x, f x ∂(γ.shiftAverage (F n) (Λ n) ω)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have : TopologicalSpace.SeparableSpace ((S → E) →ᵇ ℝ) :=
    separableSpace_boundedContinuousFunction
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ((S → E) →ᵇ ℝ)
  have : Countable D := hDc.to_subtype
  have h : ∀ᵐ ω ∂μ, ∀ f : D,
      Tendsto (fun n ↦ ∫ x, (f : (S → E) →ᵇ ℝ) x ∂(γ.shiftAverage (F n) (Λ n) ω)) atTop
        (𝓝 (∫ x, (f : (S → E) →ᵇ ℝ) x ∂μ)) := by
    refine ae_all_iff.2 fun f ↦ ?_
    have hfm : Measurable (f : (S → E) →ᵇ ℝ) := (f : (S → E) →ᵇ ℝ).continuous.measurable
    filter_upwards [ae_tendsto_integral_kernel_inv_card_smul_sum_shift hμ hμinv htriv hF hne hFol
      hC hC' hmono hfm.aestronglyMeasurable
      (ae_of_all _ (f : (S → E) →ᵇ ℝ).norm_coe_le_norm)] with ω hω
    refine hω.congr fun n ↦ ?_
    exact (Specification.integral_shiftAverage_eq_integral_kernel hγ hfm
      (f : (S → E) →ᵇ ℝ).norm_coe_le_norm).symm
  filter_upwards [h] with ω hω
  have hne' : ∀ n, (F n).Nonempty := fun n ↦ hne.mono (hF (Nat.zero_le n))
  have hlim := ProbabilityMeasure.tendsto_of_forall_mem_dense_tendsto_integral
    (νs := fun n ↦ γ.shiftAveragePM (hne' n) (Λ n) ω)
    (μ := ⟨μ, inferInstance⟩) hDd fun f hf ↦ hω ⟨f, hf⟩
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim

/-- **Georgii, Theorem (14.20)(b).** Let `γ` be a shift-invariant specification over a compact
metrizable state space `E` with its Borel σ-algebra, `μ ∈ 𝒢(γ)` shift-invariant and ergodic —
by (14.15)(a), `μ ∈ ex 𝒢_Θ(γ)` — `F` an increasing regular Følner sequence of finite sets of
sites and `Λ` an increasing sequence of volumes. Then
`|F n|⁻¹ ∑_{i ∈ F n} γ_{Λ n + i}(· | θ_i ω) → μ` **weakly** for `μ`-almost all `ω`.

Georgii's proof: by (5.5) the averaged distribution integrates `f` as `γ_{Λ n}(· | ω)`
integrates the ergodic average `|F n|⁻¹ ∑ f ∘ θ_i`, so this is (14.20)(a) on a countable dense
set of bounded continuous functions, as in the proof of (7.12)(b). -/
theorem ae_tendsto_shiftAverage_weakly
    (hγ : ∀ j : S, Specification.IsInvariant (shift E j) γ) {μ : ProbabilityMeasure (S → E)}
    (hμ : γ.IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun (μ : Measure (S → E)) μ)
    (htriv : (μ : Measure (S → E)) ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) :
    ∀ᵐ ω ∂(μ : Measure (S → E)), Tendsto
      (fun n ↦ γ.shiftAveragePM (hne.mono (hF (Nat.zero_le n))) (Λ n) ω) atTop (𝓝 μ) := by
  filter_upwards [ae_forall_tendsto_integral_boundedContinuous_shiftAverage hγ hμ hμinv htriv hF
    hne hFol hC hC' hmono] with ω hω
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 hω

/-- **Georgii, Theorem (14.20)(b)** as stated: for a shift-invariant specification on a
countable infinite abelian group of sites and `μ ∈ ex 𝒢_Θ(γ)`. -/
theorem ae_tendsto_shiftAverage_weakly_of_mem_extremePoints_invariantG [Infinite S]
    (hγ : ∀ j : S, Specification.IsInvariant (shift E j) γ) {μ : ProbabilityMeasure (S → E)}
    (hμ : (μ : Measure (S → E)) ∈ (invariantG γ (shiftGroup S E)).extremePoints ℝ≥0∞)
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) :
    ∀ᵐ ω ∂(μ : Measure (S → E)), Tendsto
      (fun n ↦ γ.shiftAveragePM (hne.mono (hF (Nat.zero_le n))) (Λ n) ω) atTop (𝓝 μ) :=
  ae_tendsto_shiftAverage_weakly hγ hμ.1.1.2 (mem_invariantFields_shiftGroup.1 hμ.1.2).2
    ((mem_extremePoints_invariantG_iff_mem_trivialOn
      (shiftGroup_exists_disjoint_sites_preimage (E := E)) hμ.1).1 hμ) hF hne hFol hC hC' hmono

end PartB

end MeasureTheory.GibbsMeasure

/-! ### Georgii (14.20)(c): measure-theoretic tools -/

namespace ENNReal

/-- `⨆ n : ℕ, min x n = x` in `ℝ≥0∞`: the truncations at the natural numbers exhaust `x`. -/
lemma iSup_min_natCast (x : ℝ≥0∞) : ⨆ n : ℕ, min x n = x := by
  refine le_antisymm (iSup_le fun n ↦ min_le_left _ _) ?_
  rcases eq_or_ne x ∞ with rfl | hx
  · simp [ENNReal.iSup_natCast]
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx
    exact le_iSup_of_le n (by rw [min_eq_left hn.le])

end ENNReal

/-! ### The set of convergence of a sequence of measurable functions -/

/-- The set where a sequence of measurable real functions converges to a measurable function is
measurable. -/
lemma measurableSet_tendsto_nhds {α : Type*} [MeasurableSpace α] {u : ℕ → α → ℝ} {v : α → ℝ}
    (hu : ∀ n, Measurable (u n)) (hv : Measurable v) :
    MeasurableSet {x | Tendsto (fun n ↦ u n x) atTop (𝓝 (v x))} := by
  have h : {x | Tendsto (fun n ↦ u n x) atTop (𝓝 (v x))} =
      {x | Tendsto (fun n ↦ u n x - v x) atTop (𝓝 0)} := by
    ext x; exact tendsto_sub_nhds_zero_iff.symm
  rw [h]
  exact measurableSet_tendsto (𝓝 0) fun n ↦ (hu n).sub hv

namespace MeasureTheory

/-! #### Set integrals on the product of two sub-σ-algebras -/

/-- Two measurable `ℝ≥0∞`-valued functions of finite integral with equal set integrals on every
rectangle `s ×ˢ t`, `s ∈ m₁`, `t ∈ m₂`, have equal set integrals on every set of the product
σ-algebra `m₁.prod m₂`: the rectangles are a π-system generating it. -/
lemma setLIntegral_eq_of_forall_prod {α β : Type*} {m₁ : MeasurableSpace α}
    {m₂ : MeasurableSpace β} [mα : MeasurableSpace α] [mβ : MeasurableSpace β] (h₁ : m₁ ≤ mα)
    (h₂ : m₂ ≤ mβ) {ν : Measure (α × β)} {f g : α × β → ℝ≥0∞} (hfin : ∫⁻ x, f x ∂ν ≠ ∞)
    (h : ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t →
      ∫⁻ x in s ×ˢ t, f x ∂ν = ∫⁻ x in s ×ˢ t, g x ∂ν)
    {u : Set (α × β)} (hu : MeasurableSet[m₁.prod m₂] u) :
    ∫⁻ x in u, f x ∂ν = ∫⁻ x in u, g x ∂ν := by
  have hle : m₁.prod m₂ ≤ mα.prod mβ :=
    sup_le_sup (MeasurableSpace.comap_mono h₁) (MeasurableSpace.comap_mono h₂)
  have huniv := h univ univ MeasurableSet.univ MeasurableSet.univ
  rw [univ_prod_univ, Measure.restrict_univ] at huniv
  let μf : Measure[m₁.prod m₂] (α × β) := (ν.withDensity f).trim hle
  let μg : Measure[m₁.prod m₂] (α × β) := (ν.withDensity g).trim hle
  have hμf : ∀ u, MeasurableSet[m₁.prod m₂] u → μf u = ∫⁻ x in u, f x ∂ν := fun u hu ↦ by
    simp only [μf]
    rw [trim_measurableSet_eq hle hu, withDensity_apply _ (hle _ hu)]
  have hμg : ∀ u, MeasurableSet[m₁.prod m₂] u → μg u = ∫⁻ x in u, g x ∂ν := fun u hu ↦ by
    simp only [μg]
    rw [trim_measurableSet_eq hle hu, withDensity_apply _ (hle _ hu)]
  have : IsFiniteMeasure μf := ⟨by
    rw [hμf _ MeasurableSet.univ, Measure.restrict_univ]; exact hfin.lt_top⟩
  have heq : μf = μg := by
    refine ext_of_generate_finite _ (@generateFrom_prod α β m₁ m₂).symm
      (@isPiSystem_prod α β m₁ m₂) ?_ ?_
    · rintro _ ⟨s, hs, t, ht, rfl⟩
      rw [hμf _ (@MeasurableSet.prod α β m₁ m₂ _ _ hs ht),
        hμg _ (@MeasurableSet.prod α β m₁ m₂ _ _ hs ht)]
      exact h s t hs ht
    · rw [hμf _ MeasurableSet.univ, hμg _ MeasurableSet.univ, Measure.restrict_univ, huniv]
  rw [← hμf u hu, ← hμg u hu, heq]

/-- A version of `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq` for `ℝ≥0∞`-valued
functions on a product, with the conditioning σ-algebra a product `m₁.prod m₂` of sub-σ-algebras:
if `g` is `m₁.prod m₂`-measurable and `∫_{s ×ˢ t} g = ∫_{s ×ˢ t} f` on all rectangles, then
`g.toReal` is a version of the conditional expectation `ν[f.toReal | m₁.prod m₂]`. -/
lemma toReal_ae_eq_condExp_toReal_of_forall_prod {α β : Type*} {m₁ : MeasurableSpace α}
    {m₂ : MeasurableSpace β} [mα : MeasurableSpace α] [mβ : MeasurableSpace β] (h₁ : m₁ ≤ mα)
    (h₂ : m₂ ≤ mβ) {ν : Measure (α × β)} [IsFiniteMeasure ν] {f g : α × β → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable[m₁.prod m₂] g) (hfin : ∫⁻ x, f x ∂ν ≠ ∞)
    (h : ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t →
      ∫⁻ x in s ×ˢ t, g x ∂ν = ∫⁻ x in s ×ˢ t, f x ∂ν) :
    (fun x ↦ (g x).toReal) =ᵐ[ν] ν[fun x ↦ (f x).toReal | m₁.prod m₂] := by
  have hle : m₁.prod m₂ ≤ mα.prod mβ :=
    sup_le_sup (MeasurableSpace.comap_mono h₁) (MeasurableSpace.comap_mono h₂)
  have hg' : Measurable g := hg.mono hle le_rfl
  have hgfin : ∫⁻ x, g x ∂ν ≠ ∞ := by
    have huniv := h univ univ MeasurableSet.univ MeasurableSet.univ
    rw [univ_prod_univ, Measure.restrict_univ] at huniv
    rwa [huniv]
  refine ae_eq_condExp_of_forall_setIntegral_eq hle
    (integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfin)
    (fun s _ _ ↦ (integrable_toReal_of_lintegral_ne_top hg'.aemeasurable hgfin).integrableOn)
    (fun s hs _ ↦ ?_) hg.ennreal_toReal.stronglyMeasurable.aestronglyMeasurable
  rw [integral_toReal hg'.aemeasurable.restrict
      (ae_restrict_of_ae (ae_lt_top' hg'.aemeasurable hgfin)),
    integral_toReal hf.aemeasurable.restrict (ae_restrict_of_ae (ae_lt_top' hf.aemeasurable hfin)),
    setLIntegral_eq_of_forall_prod h₁ h₂ hgfin h hs]

/-! #### Scheffé's lemma from a one-sided limit -/

/-- **Scheffé's lemma with a lower limit only.** Let `f n ≥ 0` and `g` be integrable with
`∫ f n = ∫ g` eventually, and suppose that a.e. `liminf f n ≥ g` in the sense that every `a < g x`
is eventually below `f n x`. Then `f n → g` in `L¹`.

Only a lower bound on the limit is needed: the negative parts `(f n - g)⁻ ≤ g` tend to `0` a.e.,
so their integrals vanish by dominated convergence, and `∫ |f n - g| = ∫ (f n - g) + 2 ∫ (f n - g)⁻`
with `∫ (f n - g) = 0`. This is the form of Scheffé's lemma needed in Georgii's proof of Theorem
(14.20)(c), where the dominated convergence hypothesis of Lemma (14.19) is only available after
truncation, and truncation yields the lower bound. -/
theorem tendsto_integral_abs_sub_of_forall_lt_eventually_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hg : Integrable g μ) (hf0 : ∀ n, 0 ≤ᵐ[μ] f n)
    (hint : ∀ᶠ n in atTop, ∫ x, f n x ∂μ = ∫ x, g x ∂μ)
    (hlim : ∀ᵐ x ∂μ, ∀ a < g x, ∀ᶠ n in atTop, a ≤ f n x) :
    Tendsto (fun n ↦ ∫ x, |f n x - g x| ∂μ) atTop (𝓝 0) := by
  set h : ℕ → α → ℝ := fun n x ↦ max (g x - f n x) 0 with hh
  have hhi : ∀ n, Integrable (h n) μ := fun n ↦ (hg.sub (hf n)).pos_part
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖h n x‖ ≤ |g x| := fun n ↦ by
    filter_upwards [hf0 n] with x hx
    rw [hh, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by simp only [Pi.zero_apply] at hx; linarith [le_abs_self (g x)]) (abs_nonneg _)
  have hlim' : ∀ᵐ x ∂μ, Tendsto (fun n ↦ h n x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦ ha.trans_le (le_max_right _ _),
      fun a ha ↦ ?_⟩
    filter_upwards [hx (g x - a / 2) (by linarith)] with n hn
    simp only [hh, max_lt_iff]
    exact ⟨by linarith, ha⟩
  have hint0 : Tendsto (fun n ↦ ∫ x, h n x ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun x ↦ |g x|)
      (fun n ↦ (hhi n).aestronglyMeasurable) hg.abs hbound hlim'
    simpa using this
  have hid : ∀ n, ∫ x, |f n x - g x| ∂μ = (∫ x, f n x ∂μ - ∫ x, g x ∂μ) + 2 * ∫ x, h n x ∂μ := by
    intro n
    have hfun : (fun x ↦ |f n x - g x|) = fun x ↦ (f n x - g x) + 2 * h n x := by
      funext x
      simp only [hh]
      rcases le_or_gt 0 (f n x - g x) with hx | hx
      · rw [abs_of_nonneg hx, max_eq_right (by linarith)]; ring
      · rw [abs_of_neg hx, max_eq_left (by linarith)]; ring
    rw [hfun, integral_add (f := fun x ↦ f n x - g x) (g := fun x ↦ 2 * h n x) ((hf n).sub hg)
      ((hhi n).const_mul 2), integral_sub (hf n) hg, integral_const_mul]
  have : Tendsto (fun n ↦ (∫ x, f n x ∂μ - ∫ x, g x ∂μ) + 2 * ∫ x, h n x ∂μ) atTop (𝓝 0) := by
    have h2 := hint0.const_mul 2
    rw [mul_zero] at h2
    refine (Tendsto.congr' ?_ h2)
    filter_upwards [hint] with n hn
    rw [hn, sub_self, zero_add]
  exact this.congr fun n ↦ (hid n).symm

/-! #### Averages over a subset of the index set -/

/-- Uniform averages of a function with values in `[0, M]` over `F' ⊆ F` and over `F` differ by
at most `M |F \ F'| / |F|`. -/
lemma abs_inv_card_mul_sum_sub_inv_card_mul_sum_le {ι : Type*} [DecidableEq ι] {F' F : Finset ι}
    (hsub : F' ⊆ F) {h : ι → ℝ} {M : ℝ} (h0 : ∀ i ∈ F, 0 ≤ h i) (hM : ∀ i ∈ F, h i ≤ M) :
    |(F'.card : ℝ)⁻¹ * ∑ i ∈ F', h i - (F.card : ℝ)⁻¹ * ∑ i ∈ F, h i| ≤
      M * (((F \ F').card : ℝ) / F.card) := by
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · rw [Finset.subset_empty.1 hsub]; simp
  have hFpos : (0 : ℝ) < F.card := by exact_mod_cast hFne.card_pos
  obtain ⟨i₀, hi₀⟩ := hFne
  have hM0 : 0 ≤ M := (h0 _ hi₀).trans (hM _ hi₀)
  set a := (F'.card : ℝ)⁻¹ * ∑ i ∈ F', h i with ha
  set T := ∑ i ∈ F \ F', h i with hT
  set r := ((F \ F').card : ℝ) / F.card with hr
  have hsum : ∑ i ∈ F, h i = ∑ i ∈ F', h i + T := by rw [hT, ← Finset.sum_sdiff hsub, add_comm]
  have ha0 : 0 ≤ a :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i hi ↦ h0 i (hsub hi))
  have haM : a ≤ M := by
    rcases F'.eq_empty_or_nonempty with hF' | hF'
    · rw [ha, hF']; simpa using hM0
    · have hpos : (0 : ℝ) < F'.card := by exact_mod_cast hF'.card_pos
      rw [ha, inv_mul_le_iff₀ hpos]
      calc ∑ i ∈ F', h i ≤ ∑ _ ∈ F', M := Finset.sum_le_sum fun i hi ↦ hM i (hsub hi)
        _ = F'.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i hi ↦ h0 i (Finset.sdiff_subset hi)
  have hTM : T ≤ (F \ F').card * M := by
    calc T ≤ ∑ _ ∈ F \ F', M := Finset.sum_le_sum fun i hi ↦ hM i (Finset.sdiff_subset hi)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((F \ F').card : ℝ) = F.card - F'.card := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  have hr0 : 0 ≤ r := by positivity
  have hr1 : (F'.card : ℝ) / F.card = 1 - r := by
    rw [hr, hcard]; field_simp; ring
  have hb : (F.card : ℝ)⁻¹ * ∑ i ∈ F, h i = (1 - r) * a + T / F.card := by
    rw [← hr1, hsum, ha]
    rcases F'.eq_empty_or_nonempty with hF' | hF'
    · simp [hF', div_eq_inv_mul]
    · have hpos : (F'.card : ℝ) ≠ 0 := by exact_mod_cast hF'.card_pos.ne'
      field_simp
  have ht0 : 0 ≤ T / F.card := by positivity
  have htM : T / F.card ≤ M * r := by
    calc T / F.card ≤ ((F \ F').card * M) / F.card := div_le_div_of_nonneg_right hTM hFpos.le
      _ = M * r := by rw [hr]; ring
  rw [hb, abs_le]
  have h1 := mul_nonneg ha0 hr0
  have h2 := mul_le_mul_of_nonneg_right haM hr0
  constructor <;> nlinarith

/-- A uniform average of `ℝ≥0∞`-valued terms bounded by `M` is bounded by `M`, whatever the
index set. -/
lemma inv_card_mul_sum_le_of_forall_le {ι : Type*} {F : Finset ι} {h : ι → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : ∀ i ∈ F, h i ≤ M) : (F.card : ℝ≥0∞)⁻¹ * ∑ i ∈ F, h i ≤ M := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  have h0 : (F.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hF.card_pos.ne'
  calc (F.card : ℝ≥0∞)⁻¹ * ∑ i ∈ F, h i ≤ (F.card : ℝ≥0∞)⁻¹ * ∑ _ ∈ F, M := by
        gcongr with i hi; exact hM i hi
    _ = M := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _), one_mul]

end MeasureTheory

/-! ### Georgii (14.20)(c): the averaged densities on the product space -/

namespace Specification

open MeasureTheory.GibbsMeasure

section DLR

variable {S E : Type*} [MeasurableSpace E]

/-- **The DLR equation as a set integral**: for `μ ∈ 𝒢(γ)`, `A` measurable and `B ∈ 𝓣_Λ`,
`∫_B γ_Λ(A | ω) μ(dω) = μ(A ∩ B)`, by properness and `μ γ_Λ = μ`. -/
lemma IsGibbsMeasure.setLIntegral_kernel_eq_measure_inter {γ : Specification S E}
    {μ : Measure (S → E)} [IsProbabilityMeasure μ] (hμ : γ.IsGibbsMeasure μ) (Λ : Finset S)
    {A B : Set (S → E)} (hA : MeasurableSet A)
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B) :
    ∫⁻ ω in B, γ Λ ω A ∂μ = μ (A ∩ B) := by
  have hB' : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hbind : μ.bind (γ Λ) = μ := (isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)).1 hμ Λ
  calc ∫⁻ ω in B, γ Λ ω A ∂μ = ∫⁻ ω, B.indicator 1 ω * γ Λ ω A ∂μ := by
        rw [← lintegral_indicator hB']
        refine lintegral_congr fun ω ↦ ?_
        by_cases h : ω ∈ B <;> simp [h]
    _ = ∫⁻ ω, γ Λ ω (A ∩ B) ∂μ := lintegral_congr fun ω ↦
        ((γ.isProper Λ).inter_eq_indicator_mul cylinderEvents_le_pi hA hB ω).symm
    _ = μ.bind (γ Λ) (A ∩ B) := (Measure.bind_apply (hA.inter hB')
        ((γ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable).symm
    _ = μ (A ∩ B) := by rw [hbind]

end DLR

section Translate

variable {S E : Type*} [MeasurableSpace E] [AddGroup S]

/-- Membership in the translate `Λ + i = Λ.map (Equiv.addRight i)`. -/
lemma mem_map_addRight {Λ : Finset S} {i x : S} :
    x ∈ Λ.map (Equiv.addRight i).toEmbedding ↔ x - i ∈ Λ := by
  rw [Finset.mem_map_equiv, Equiv.addRight_symm, Equiv.coe_addRight, sub_eq_add_neg]

/-- The spatial part of `θ_i⁻¹` pulls the complement of `Λ` back to the complement of
`Λ + i`. -/
lemma shift_inv_sites_preimage_compl (i : S) (Λ : Finset S) :
    (shift E i).inv.sites ⁻¹' ((Λ : Set S)ᶜ) =
      ((Λ.map (Equiv.addRight i).toEmbedding : Finset S) : Set S)ᶜ := by
  ext x
  simp [Transformation.inv, shift]

/-- `θ_i⁻¹` transports the events outside `Λ` to events outside `Λ + i`
(Georgii, remark after (5.1)). -/
lemma measurableSet_cylinderEvents_compl_preimage_shift_inv (i : S) (Λ : Finset S)
    {B : Set (S → E)} (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E)
      ((Λ.map (Equiv.addRight i).toEmbedding : Finset S) : Set S)ᶜ]
      ((shift E i).inv.toFun ⁻¹' B) := by
  rw [← shift_inv_sites_preimage_compl (E := E) i Λ]
  exact (shift E i).inv.measurable_toFun_cylinderEvents _ hB

lemma shift_toFun_preimage_inv_toFun_preimage (i : S) (B : Set (S → E)) :
    (shift E i).toFun ⁻¹' ((shift E i).inv.toFun ⁻¹' B) = B := by
  ext ω; simp [Transformation.inv_toFun_toFun]

/-- Georgii's `Λ' = {i ∈ F : Λ + i ⊇ Δ}` in the proof of (14.20)(c): the indices whose
translated volume covers `Δ`. -/
def coveringIndices [DecidableEq S] (Δ F Λ : Finset S) : Finset S :=
  F.filter fun i ↦ Δ ⊆ Λ.map (Equiv.addRight i).toEmbedding

lemma coveringIndices_subset [DecidableEq S] (Δ F Λ : Finset S) : coveringIndices Δ F Λ ⊆ F :=
  Finset.filter_subset _ _

lemma subset_of_mem_coveringIndices [DecidableEq S] {Δ F Λ : Finset S} {i : S}
    (hi : i ∈ coveringIndices Δ F Λ) : Δ ⊆ Λ.map (Equiv.addRight i).toEmbedding :=
  (Finset.mem_filter.1 hi).2

/-- The fraction of indices whose translate does not cover `Δ` vanishes as soon as it does for
every single site: `F \ Λ' ⊆ ⋃_{δ ∈ Δ} {i ∈ F : δ - i ∉ Λ}`. -/
lemma tendsto_card_sdiff_coveringIndices_div [DecidableEq S] {F Λ : ℕ → Finset S}
    (hcouple : ∀ δ : S, Tendsto (fun n ↦ (((F n).filter fun i ↦ δ - i ∉ Λ n).card : ℝ) /
      (F n).card) atTop (𝓝 0)) (Δ : Finset S) :
    Tendsto (fun n ↦ ((F n \ coveringIndices Δ (F n) (Λ n)).card : ℝ) / (F n).card) atTop
      (𝓝 0) := by
  have hsub : ∀ n, F n \ coveringIndices Δ (F n) (Λ n) ⊆
      Δ.biUnion fun δ ↦ (F n).filter fun i ↦ δ - i ∉ Λ n := fun n i hi ↦ by
    rw [Finset.mem_sdiff, coveringIndices, Finset.mem_filter, not_and] at hi
    obtain ⟨δ, hδ, hδi⟩ := Finset.not_subset.1 (hi.2 hi.1)
    exact Finset.mem_biUnion.2
      ⟨δ, hδ, Finset.mem_filter.2 ⟨hi.1, fun h ↦ hδi (mem_map_addRight.2 h)⟩⟩
  have hbound : ∀ n, ((F n \ coveringIndices Δ (F n) (Λ n)).card : ℝ) / (F n).card ≤
      ∑ δ ∈ Δ, (((F n).filter fun i ↦ δ - i ∉ Λ n).card : ℝ) / (F n).card := fun n ↦ by
    rw [← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact_mod_cast (Finset.card_le_card (hsub n)).trans Finset.card_biUnion_le
  refine squeeze_zero (fun n ↦ by positivity) hbound ?_
  simpa using tendsto_finsetSum Δ fun δ _ ↦ hcouple δ

/-- The covering indices are eventually non-empty once their complement has vanishing
fraction. -/
lemma eventually_nonempty_coveringIndices [DecidableEq S] {F Λ : ℕ → Finset S}
    (hne : ∀ n, (F n).Nonempty) {Δ : Finset S}
    (hsdiff : Tendsto (fun n ↦ ((F n \ coveringIndices Δ (F n) (Λ n)).card : ℝ) / (F n).card)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, (coveringIndices Δ (F n) (Λ n)).Nonempty := by
  filter_upwards [hsdiff.eventually (eventually_lt_nhds one_pos)] with n hn
  rw [Finset.nonempty_iff_ne_empty]
  rintro h
  rw [h, Finset.sdiff_empty, div_self (by exact_mod_cast (hne n).card_pos.ne')] at hn
  exact lt_irrefl _ hn

end Translate

section TailProd

variable {S E : Type*} [MeasurableSpace E]


/-- **Georgii's σ-algebra `𝓣_Λ × 𝓕_Δ` of (14.22)**: the product of the events outside `Λ` on the
boundary condition with the full σ-algebra on the inner configuration `E^Δ`. -/
abbrev tailProdEvents (Λ Δ : Finset S) : MeasurableSpace ((S → E) × (Δ → E)) :=
  (cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)).prod inferInstance

lemma tailProdEvents_le (Λ Δ : Finset S) :
    tailProdEvents (S := S) (E := E) Λ Δ ≤ Prod.instMeasurableSpace :=
  sup_le_sup (MeasurableSpace.comap_mono cylinderEvents_le_pi) le_rfl

lemma antitone_tailProdEvents {Λ : ℕ → Finset S} (hmono : Monotone Λ) (Δ : Finset S) :
    Antitone fun n ↦ tailProdEvents (S := S) (E := E) (Λ n) Δ := fun _ _ hmn ↦
  sup_le_sup (MeasurableSpace.comap_mono (antitone_cylinderEvents_compl (E := E) hmono hmn)) le_rfl

/-- The fibre of an event of `Δ` over an inner configuration does not depend on the boundary
condition. -/
lemma juxt_preimage_eq_of_measurableSet_cylinderEvents {Δ : Finset S} {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) (η ω : S → E) :
    juxt (Δ : Set S) η ⁻¹' A = juxt (Δ : Set S) ω ⁻¹' A := by
  ext ζ
  exact mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦ by
    rw [juxt_apply_of_mem hi, juxt_apply_of_mem hi]

end TailProd

section AvgKernel

variable {S E : Type*} [MeasurableSpace E] {ρ : Finset S → (S → E) → ℝ≥0∞} {μ : Measure (S → E)}

/-- `ρ̄_Δ` is the supremum of its truncations `ρ̄^M_Δ`, by monotone convergence. -/
lemma avgKernel_eq_iSup_min {Δ : Finset S} (hρ : Measurable (ρ Δ)) (ζ : Δ → E) :
    avgKernel ρ μ Δ ζ = ⨆ M : ℕ, avgKernel (fun Λ σ ↦ min (ρ Λ σ) M) μ Δ ζ := by
  have hm : ∀ M : ℕ, Measurable fun η ↦ min (ρ Δ (juxt (Δ : Set S) η ζ)) (M : ℝ≥0∞) := fun M ↦
    (hρ.comp (measurable_juxt_boundary ζ)).min measurable_const
  change ∫⁻ η, ρ Δ (juxt (Δ : Set S) η ζ) ∂μ =
    ⨆ M : ℕ, ∫⁻ η, min (ρ Δ (juxt (Δ : Set S) η ζ)) (M : ℝ≥0∞) ∂μ
  rw [← lintegral_iSup hm fun M M' hMM' η ↦ min_le_min_left _ (by exact_mod_cast hMM')]
  exact lintegral_congr fun η ↦ (ENNReal.iSup_min_natCast _).symm

variable [IsProbabilityMeasure μ]

/-- The truncated `ρ̄^M_Δ(ζ) = ∫ μ(dη) min (ρ_Δ(ζ η_{S∖Δ})) M` is bounded by `M`. -/
lemma avgKernel_min_le (Δ : Finset S) (M : ℝ≥0∞) (ζ : Δ → E) :
    avgKernel (fun Λ σ ↦ min (ρ Λ σ) M) μ Δ ζ ≤ M := by
  refine (lintegral_mono fun η ↦ min_le_right _ _).trans ?_
  simp

end AvgKernel

section CondDensity

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S] {ν : Measure E} [IsProbabilityMeasure ν]
  {ρ : Finset S → (S → E) → ℝ≥0∞}


/-- `γ_Λ(A | η)` as a set integral of the conditional density `ρ_Δ^Λ` against `λ_Δ`, for events
`A` of `Δ ⊆ Λ`. -/
lemma modification_apply_eq_setLIntegral_condDensity (hmod : (isssd ν).IsModifier ρ)
    {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ) (η : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    (isssd ν).modification ρ hmod Λ η A = ∫⁻ σ in A, condDensity ν ρ Δ Λ σ ∂(isssd ν Δ η) := by
  have hAΛ : MeasurableSet[cylinderEvents (((Λ \ Δ : Finset S) : Set S))ᶜ] A :=
    cylinderEvents_le_compl_sdiff Δ Λ _ hA
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hind : Measurable[cylinderEvents (((Λ \ Δ : Finset S) : Set S))ᶜ]
      (A.indicator (1 : (S → E) → ℝ≥0∞)) := Measurable.indicator measurable_const hAΛ
  have h := lintegral_modificationKer_isssd (ν := ν) (ρ := ρ) hmod.measurable hΔ hind η
  rw [lintegral_indicator_one hA'] at h
  rw [show (fun σ ↦ condDensity ν ρ Δ Λ σ * A.indicator (1 : (S → E) → ℝ≥0∞) σ)
      = A.indicator (condDensity ν ρ Δ Λ) by
    funext σ; by_cases hσ : σ ∈ A <;> simp [hσ], lintegral_indicator hA'] at h
  exact h

/-- `γ_Λ(A | η)` as an integral over the inner configurations `ζ ∈ E^Δ`. -/
lemma modification_apply_eq_lintegral_condDensity_juxt (hmod : (isssd ν).IsModifier ρ)
    {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ) (η : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    (isssd ν).modification ρ hmod Λ η A =
      ∫⁻ ζ in juxt (Δ : Set S) η ⁻¹' A, condDensity ν ρ Δ Λ (juxt (Δ : Set S) η ζ)
        ∂(Measure.pi fun _ : Δ ↦ ν) := by
  rw [modification_apply_eq_setLIntegral_condDensity hmod hΔ η hA,
    setLIntegral_isssd_eq_setLIntegral_juxt ν
      ((measurable_condDensity hmod.measurable Δ Λ).mono cylinderEvents_le_pi le_rfl)
      (cylinderEvents_le_pi _ hA) η]

/-- `λ^Δ ρ_Δ^Λ(· η_{S∖Δ}) = 1`: the conditional density is a probability density on the inner
configurations, for every boundary condition. -/
lemma lintegral_condDensity_juxt (hmod : (isssd ν).IsModifier ρ) {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ)
    (η : S → E) :
    ∫⁻ ζ, condDensity ν ρ Δ Λ (juxt (Δ : Set S) η ζ) ∂(Measure.pi fun _ : Δ ↦ ν) = 1 := by
  rw [← lintegral_isssd_eq Δ η
    ((measurable_condDensity hmod.measurable Δ Λ).mono cylinderEvents_le_pi le_rfl)]
  exact lintegral_condDensity hmod hΔ η

end CondDensity

section AvgKernelDensity

variable {S E : Type*} [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
  {ρ : Finset S → (S → E) → ℝ≥0∞} {μ : Measure (S → E)} [IsProbabilityMeasure μ]



/-- `μ(A)` as an integral of `ρ̄_Δ` over the inner configurations, for events `A` of `Δ`. -/
lemma measure_apply_eq_lintegral_avgKernel (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ) {Δ : Finset S} (ω : S → E)
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    μ A = ∫⁻ ζ in juxt (Δ : Set S) ω ⁻¹' A, avgKernel ρ μ Δ ζ ∂(Measure.pi fun _ : Δ ↦ ν) := by
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hindΔ : Measurable[cylinderEvents ((Δ : Finset S) : Set S)]
      (A.indicator (1 : (S → E) → ℝ≥0∞)) := Measurable.indicator measurable_const hA
  have h := lintegral_avgDensity_mul hmod hμ hindΔ ω
  rw [lintegral_indicator_one hA'] at h
  rw [show (fun σ ↦ avgDensity ρ μ Δ σ * A.indicator (1 : (S → E) → ℝ≥0∞) σ)
      = A.indicator (avgDensity ρ μ Δ) by
    funext σ; by_cases hσ : σ ∈ A <;> simp [hσ], lintegral_indicator hA',
    setLIntegral_isssd_eq_setLIntegral_juxt ν
      ((measurable_avgDensity μ (hmod.measurable Δ)).mono cylinderEvents_le_pi le_rfl) hA' ω] at h
  rw [← h]
  exact lintegral_congr fun ζ ↦ by rw [avgDensity_juxt]

/-- `λ^Δ ρ̄_Δ = 1`: `ρ̄_Δ` is a probability density on the inner configurations. -/
lemma lintegral_avgKernel (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ) (Δ : Finset S) :
    ∫⁻ ζ, avgKernel ρ μ Δ ζ ∂(Measure.pi fun _ : Δ ↦ ν) = 1 := by
  obtain ⟨ω⟩ : Nonempty (S → E) := Measure.nonempty_of_neZero μ
  have h := lintegral_avgDensity hmod hμ Δ ω
  rw [lintegral_isssd_eq Δ ω
    ((measurable_avgDensity μ (hmod.measurable Δ)).mono cylinderEvents_le_pi le_rfl)] at h
  simpa only [avgDensity_juxt] using h

end AvgKernelDensity

section ShiftDensities

variable {S E : Type*} [MeasurableSpace E] [AddGroup S] {ν : Measure E} [IsProbabilityMeasure ν]
  (ρ : Finset S → (S → E) → ℝ≥0∞)



/-- **The ergodic average `|F|⁻¹ ∑_{i ∈ F} ρ̃_Δ ∘ θ̃_i` of Georgii's (14.22)**, where
`ρ̃_Δ(ω, ζ) = ρ_Δ(ζ_Δ ω_{S∖Δ})` and `θ̃_i(ω, ζ) = (θ_i ω, ζ)`. -/
noncomputable def shiftAvgDensity (Δ F : Finset S) (p : (S → E) × (Δ → E)) : ℝ≥0∞ :=
  (F.card : ℝ≥0∞)⁻¹ * ∑ i ∈ F, ρ Δ (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2)

variable {ρ}



lemma measurable_juxt_shift (Δ : Finset S) (i : S) :
    Measurable fun p : (S → E) × (Δ → E) ↦ juxt (Δ : Set S) ((shift E i).toFun p.1) p.2 :=
  (measurable_juxt_snd Δ).comp (measurable_snd.prodMk ((shift E i).measurable_toFun.comp
    measurable_fst))

/-- The truncated averages are bounded by the truncation level. -/
lemma shiftAvgDensity_min_le (Δ F : Finset S) (M : ℝ≥0∞) (p : (S → E) × (Δ → E)) :
    shiftAvgDensity (fun Λ σ ↦ min (ρ Λ σ) M) Δ F p ≤ M :=
  MeasureTheory.inv_card_mul_sum_le_of_forall_le fun _ _ ↦ min_le_right _ _

lemma toReal_shiftAvgDensity_min (Δ F : Finset S) (M : ℕ) (p : (S → E) × (Δ → E)) :
    (shiftAvgDensity (fun Λ σ ↦ min (ρ Λ σ) M) Δ F p).toReal =
      (F.card : ℝ)⁻¹ *
        ∑ i ∈ F, (min (ρ Δ (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2)) M).toReal := by
  rw [shiftAvgDensity, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun i _ ↦ ne_top_of_le_ne_top (ENNReal.natCast_ne_top M) (min_le_right _ _)]

lemma measurable_shiftAvgDensity {Δ : Finset S} (hρ : Measurable (ρ Δ)) (F : Finset S) :
    Measurable (shiftAvgDensity ρ Δ F) :=
  Measurable.const_mul (Finset.measurable_sum F fun i _ ↦ hρ.comp (measurable_juxt_shift Δ i)) _

/-! #### The averaged densities integrate to `1` -/

variable {μ : Measure (S → E)} [IsProbabilityMeasure μ]



/-- Integrating a function of `ζ_Δ (θ_i ω)_{S∖Δ}` against `μ ⊗ λ^Δ` is integrating it against
`μ λ_Δ`, by the shift-invariance of `μ`. -/
lemma lintegral_prod_juxt_shift (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    (Δ : Finset S) (i : S) {g : (S → E) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2) ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν))
      = ∫⁻ σ, g σ ∂(μ.bind (isssd ν Δ)) := by
  have hmp : MeasurePreserving (Prod.map (shift E i).toFun id) (μ.prod (Measure.pi fun _ : Δ ↦ ν))
      (μ.prod (Measure.pi fun _ : Δ ↦ ν)) := (hμinv i).prod (MeasurePreserving.id _)
  have hf : Measurable fun p : (S → E) × (Δ → E) ↦ g (juxt (Δ : Set S) p.1 p.2) :=
    hg.comp ((measurable_juxt_snd Δ).comp measurable_swap)
  calc ∫⁻ p, g (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2) ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν))
      = ∫⁻ p, g (juxt (Δ : Set S) p.1 p.2) ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) :=
        hmp.lintegral_comp hf
    _ = ∫⁻ ω, ∫⁻ ζ, g (juxt (Δ : Set S) ω ζ) ∂(Measure.pi fun _ : Δ ↦ ν) ∂μ :=
        lintegral_prod _ hf.aemeasurable
    _ = ∫⁻ σ, g σ ∂(μ.bind (isssd ν Δ)) := (lintegral_bind_isssd μ Δ hg).symm

lemma lintegral_shiftAvgDensity_eq (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    {Δ : Finset S} (hρ : Measurable (ρ Δ)) (F : Finset S) :
    ∫⁻ p, shiftAvgDensity ρ Δ F p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) =
      (F.card : ℝ≥0∞)⁻¹ * ∑ _ ∈ F, ∫⁻ σ, ρ Δ σ ∂(μ.bind (isssd ν Δ)) := by
  unfold shiftAvgDensity
  have hm : ∀ i, Measurable fun p : (S → E) × (Δ → E) ↦
      ρ Δ (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2) := fun i ↦
    hρ.comp (measurable_juxt_shift Δ i)
  rw [lintegral_const_mul _ (Finset.measurable_sum F fun i _ ↦ hm i),
    lintegral_finsetSum _ fun i _ ↦ hm i]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ lintegral_prod_juxt_shift hμinv Δ i hρ

lemma lintegral_shiftAvgDensity (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ) (Δ : Finset S) {F : Finset S}
    (hF : F.Nonempty) :
    ∫⁻ p, shiftAvgDensity ρ Δ F p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) = 1 := by
  rw [lintegral_shiftAvgDensity_eq hμinv (hmod.measurable Δ), lintegral_rho_bind hmod hμ Δ,
    Finset.sum_const, nsmul_eq_mul, mul_one,
    ENNReal.inv_mul_cancel (by exact_mod_cast hF.card_pos.ne') (ENNReal.natCast_ne_top _)]

lemma lintegral_shiftAvgDensity_ne_top (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ) (Δ F : Finset S) :
    ∫⁻ p, shiftAvgDensity ρ Δ F p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) ≠ ∞ := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [shiftAvgDensity]
  · rw [lintegral_shiftAvgDensity hmod hμ hμinv Δ hF]; exact ENNReal.one_ne_top

lemma lintegral_shiftAvgDensity_min_le (Δ F : Finset S) (M : ℝ≥0∞) :
    ∫⁻ p, shiftAvgDensity (fun Λ σ ↦ min (ρ Λ σ) M) Δ F p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν))
      ≤ M := by
  refine (lintegral_mono fun p ↦ shiftAvgDensity_min_le Δ F M p).trans ?_
  simp

variable [DecidableEq S] (ν ρ)



/-- **Georgii's averaged density `ρ̃^n_Δ` of (14.21)**: on the product space
`(ω, ζ) ∈ Ω × E^Δ`, the average over `i ∈ F` of the conditional densities
`ρ_Δ^{Λ + i}(ζ_Δ (θ_i ω)_{S ∖ Δ}) = λ_{(Λ+i) ∖ Δ}(ρ_{Λ+i} | ζ_Δ (θ_i ω)_{S∖Δ})`. -/
noncomputable def shiftAvgCondDensity (Δ F Λ : Finset S) (p : (S → E) × (Δ → E)) : ℝ≥0∞ :=
  (F.card : ℝ≥0∞)⁻¹ * ∑ i ∈ F, condDensity ν ρ Δ (Λ.map (Equiv.addRight i).toEmbedding)
    (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2)

variable {ν ρ}



/-- The map `(ω, ζ) ↦ ζ_Δ (θ_i ω)_{S∖Δ}` is measurable from `𝓣_Λ × 𝓕_Δ` to the events outside
`(Λ + i) ∖ Δ`: outside `Δ` it reads `ω` at `k - i ∉ Λ`. -/
lemma measurable_juxt_shift_tailProdEvents (Δ Λ : Finset S) (i : S) :
    Measurable[tailProdEvents (S := S) (E := E) Λ Δ, cylinderEvents (X := fun _ : S ↦ E)
      (((Λ.map (Equiv.addRight i).toEmbedding \ Δ : Finset S) : Set S)ᶜ)]
      (fun p : (S → E) × (Δ → E) ↦ juxt (Δ : Set S) ((shift E i).toFun p.1) p.2) := by
  rw [measurable_cylinderEvents_iff]
  intro k hk
  by_cases hkΔ : k ∈ (Δ : Set S)
  · have h : (fun p : (S → E) × (Δ → E) ↦ juxt (Δ : Set S) ((shift E i).toFun p.1) p.2 k) =
        fun p ↦ p.2 ⟨k, hkΔ⟩ := funext fun p ↦ juxt_apply_of_mem hkΔ _
    rw [h]
    exact (measurable_pi_apply _).comp
      (@measurable_snd _ _ (cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) _)
  · have hkΛ : k - i ∈ ((Λ : Set S)ᶜ) := by
      simp only [Finset.coe_sdiff, Set.mem_compl_iff, Set.mem_sdiff, Finset.mem_coe, not_and,
        not_not] at hk
      simp only [Set.mem_compl_iff, Finset.mem_coe]
      exact fun h ↦ hkΔ (hk (mem_map_addRight.2 h))
    have h : (fun p : (S → E) × (Δ → E) ↦ juxt (Δ : Set S) ((shift E i).toFun p.1) p.2 k) =
        fun p ↦ p.1 (k - i) := funext fun p ↦ by
      rw [juxt_apply_of_not_mem hkΔ, shift_toFun_apply]
    rw [h]
    exact (measurable_cylinderEvent_apply hkΛ).comp
      (@measurable_fst _ _ (cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) _)

lemma measurable_shiftAvgCondDensity_tailProdEvents (hρ : ∀ Λ, Measurable (ρ Λ))
    (Δ F Λ : Finset S) :
    Measurable[tailProdEvents (S := S) (E := E) Λ Δ] (shiftAvgCondDensity ν ρ Δ F Λ) :=
  Measurable.const_mul (Finset.measurable_sum F fun i _ ↦
    (measurable_condDensity hρ Δ _).comp (measurable_juxt_shift_tailProdEvents Δ Λ i)) _

lemma measurable_shiftAvgCondDensity (hρ : ∀ Λ, Measurable (ρ Λ)) (Δ F Λ : Finset S) :
    Measurable (shiftAvgCondDensity ν ρ Δ F Λ) :=
  (measurable_shiftAvgCondDensity_tailProdEvents hρ Δ F Λ).mono (tailProdEvents_le Λ Δ) le_rfl

/-- For a fixed boundary condition `ω`, the averaged density `ρ̃_Δ(ω, ·)` is a probability
density on the inner configurations. -/
lemma lintegral_shiftAvgCondDensity_snd (hmod : (isssd ν).IsModifier ρ) {Δ F Λ : Finset S}
    (hF : ∀ i ∈ F, Δ ⊆ Λ.map (Equiv.addRight i).toEmbedding) (hFne : F.Nonempty) (ω : S → E) :
    ∫⁻ ζ, shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ) ∂(Measure.pi fun _ : Δ ↦ ν) = 1 := by
  unfold shiftAvgCondDensity
  have hm : ∀ i, Measurable fun ζ : Δ → E ↦ condDensity ν ρ Δ (Λ.map (Equiv.addRight i).toEmbedding)
      (juxt (Δ : Set S) ((shift E i).toFun ω) ζ) := fun i ↦
    ((measurable_condDensity hmod.measurable Δ _).mono cylinderEvents_le_pi le_rfl).comp
      Measurable.juxt
  rw [lintegral_const_mul _ (Finset.measurable_sum F fun i _ ↦ hm i),
    lintegral_finsetSum _ fun i _ ↦ hm i,
    Finset.sum_congr rfl fun i hi ↦ lintegral_condDensity_juxt hmod (hF i hi) _,
    Finset.sum_const, nsmul_eq_mul, mul_one,
    ENNReal.inv_mul_cancel (by exact_mod_cast hFne.card_pos.ne') (ENNReal.natCast_ne_top _)]

lemma lintegral_shiftAvgCondDensity_snd_le_one (hmod : (isssd ν).IsModifier ρ)
    {Δ F Λ : Finset S} (hF : ∀ i ∈ F, Δ ⊆ Λ.map (Equiv.addRight i).toEmbedding) (ω : S → E) :
    ∫⁻ ζ, shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ) ∂(Measure.pi fun _ : Δ ↦ ν) ≤ 1 := by
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · simp [shiftAvgCondDensity]
  · exact (lintegral_shiftAvgCondDensity_snd hmod hF hFne ω).le

/-- **Georgii's bound in the proof of (14.20)(c)**: on the events of `Δ`, the averaged Gibbs
distribution over the covering indices and `μ` differ by at most
`λ^Δ(|ρ̃^n_Δ(ω, ·) - ρ̄_Δ|)`. -/
lemma abs_shiftAverage_real_sub_le_integral_abs (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ) {Δ F Λ : Finset S}
    (hF : ∀ i ∈ F, Δ ⊆ Λ.map (Equiv.addRight i).toEmbedding) (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    |(((isssd ν).modification ρ hmod).shiftAverage F Λ ω).real A - μ.real A| ≤
      ∫ ζ, |(shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ)).toReal - (avgKernel ρ μ Δ ζ).toReal|
        ∂(Measure.pi fun _ : Δ ↦ ν) := by
  set lam : Measure (Δ → E) := Measure.pi fun _ : Δ ↦ ν with hlam
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  set Aω : Set (Δ → E) := juxt (Δ : Set S) ω ⁻¹' A with hAω
  have hAωm : MeasurableSet Aω := Measurable.juxt hA'
  have hm : ∀ i, Measurable fun ζ : Δ → E ↦ condDensity ν ρ Δ (Λ.map (Equiv.addRight i).toEmbedding)
      (juxt (Δ : Set S) ((shift E i).toFun ω) ζ) := fun i ↦
    ((measurable_condDensity hmod.measurable Δ _).mono cylinderEvents_le_pi le_rfl).comp
      Measurable.juxt
  have hRm : Measurable fun ζ ↦ shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ) :=
    (measurable_shiftAvgCondDensity hmod.measurable Δ F Λ).comp measurable_prodMk_left
  have hKm : Measurable (avgKernel ρ μ Δ) := measurable_avgKernel μ (hmod.measurable Δ)
  have hRfin : ∫⁻ ζ, shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ) ∂lam ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (lintegral_shiftAvgCondDensity_snd_le_one hmod hF ω)
  have hKfin : ∫⁻ ζ, avgKernel ρ μ Δ ζ ∂lam ≠ ∞ := by
    rw [lintegral_avgKernel hmod hμ Δ]; exact ENNReal.one_ne_top
  have hRint : Integrable (fun ζ ↦ (shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ)).toReal) lam :=
    integrable_toReal_of_lintegral_ne_top hRm.aemeasurable hRfin
  have hKint : Integrable (fun ζ ↦ (avgKernel ρ μ Δ ζ).toReal) lam :=
    integrable_toReal_of_lintegral_ne_top hKm.aemeasurable hKfin
  -- the averaged distribution on `A`
  have h1 : ((isssd ν).modification ρ hmod).shiftAverage F Λ ω A =
      ∫⁻ ζ in Aω, shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ) ∂lam := by
    rw [shiftAverage_apply]
    unfold shiftAvgCondDensity
    rw [lintegral_const_mul _ (Finset.measurable_sum F fun i _ ↦ hm i),
      lintegral_finsetSum _ fun i _ ↦ hm i]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [modification_apply_eq_lintegral_condDensity_juxt hmod (hF i hi) _ hA,
      juxt_preimage_eq_of_measurableSet_cylinderEvents hA _ ω]
  have h2 : μ A = ∫⁻ ζ in Aω, avgKernel ρ μ Δ ζ ∂lam :=
    measure_apply_eq_lintegral_avgKernel hmod hμ ω hA
  rw [measureReal_def, measureReal_def, h1, h2,
    ← integral_toReal hRm.aemeasurable.restrict
      (ae_restrict_of_ae (ae_lt_top' hRm.aemeasurable hRfin)),
    ← integral_toReal hKm.aemeasurable.restrict
      (ae_restrict_of_ae (ae_lt_top' hKm.aemeasurable hKfin)),
    ← integral_sub hRint.integrableOn hKint.integrableOn]
  calc |∫ ζ in Aω, ((shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ)).toReal - (avgKernel ρ μ Δ ζ).toReal)
          ∂lam|
      ≤ ∫ ζ in Aω, |(shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ)).toReal - (avgKernel ρ μ Δ ζ).toReal|
          ∂lam := by
        simpa using abs_integral_le_integral_abs (μ := lam.restrict Aω)
          (f := fun ζ ↦ (shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ)).toReal - (avgKernel ρ μ Δ ζ).toReal)
    _ ≤ ∫ ζ, |(shiftAvgCondDensity ν ρ Δ F Λ (ω, ζ)).toReal - (avgKernel ρ μ Δ ζ).toReal| ∂lam :=
        setIntegral_le_integral (hRint.sub hKint).abs (Eventually.of_forall fun _ ↦ abs_nonneg _)

/-! #### Georgii (14.22): the averaged density is a conditional expectation on `𝓣_Λ × 𝓕_Δ` -/



/-- **Georgii (14.22), one term.** For `Δ ⊆ Λ + i`, `B ∈ 𝓣_Λ` and `A ⊆ E^Δ` measurable,
`∫_{B × A} ρ_Δ^{Λ+i}(ζ (θ_i ω)) dνp = ∫_{B × A} ρ_Δ(ζ (θ_i ω)) dνp` for `νp = μ ⊗ λ^Δ`. Both sides
are `μ(Ã ∩ θ_i B)`, `Ã = {σ : σ_Δ ∈ A}`: the shift-invariance of `μ` moves `θ_i` onto `B`, and the
DLR equations for the volumes `Λ + i` and `Δ` (the tower property) evaluate both integrals. -/
lemma setLIntegral_prod_condDensity_juxt_shift (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ) {Δ Λ : Finset S} {i : S}
    (hΔ : Δ ⊆ Λ.map (Equiv.addRight i).toEmbedding) {B : Set (S → E)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B)
    {A : Set (Δ → E)} (hA : MeasurableSet A) :
    ∫⁻ p in B ×ˢ A, condDensity ν ρ Δ (Λ.map (Equiv.addRight i).toEmbedding)
        (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2) ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) =
      ∫⁻ p in B ×ˢ A, ρ Δ (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2)
        ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) := by
  set Λ' := Λ.map (Equiv.addRight i).toEmbedding with hΛ'
  set Ã : Set (S → E) := Δ.restrict ⁻¹' A with hÃdef
  have hrestrict : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)]
      (Δ.restrict : (S → E) → Δ → E) := by
    let : MeasurableSpace (S → E) := cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)
    exact measurable_pi_lambda _ fun k ↦ measurable_cylinderEvent_apply k.2
  have hÃ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] Ã := hrestrict hA
  have hÃ' : MeasurableSet Ã := cylinderEvents_le_pi _ hÃ
  have hpre : ∀ η, juxt (Δ : Set S) η ⁻¹' Ã = A := fun η ↦ by
    ext ζ; simp [hÃdef, restrict_juxt]
  have hcond : Measurable (condDensity ν ρ Δ Λ') :=
    (measurable_condDensity hmod.measurable Δ Λ').mono cylinderEvents_le_pi le_rfl
  have hinner₁ : ∀ η, ∫⁻ ζ in A, condDensity ν ρ Δ Λ' (juxt (Δ : Set S) η ζ)
      ∂(Measure.pi fun _ : Δ ↦ ν) = (isssd ν).modification ρ hmod Λ' η Ã := fun η ↦ by
    rw [modification_apply_eq_lintegral_condDensity_juxt hmod hΔ η hÃ, hpre]
  have hinner₂ : ∀ η, ∫⁻ ζ in A, ρ Δ (juxt (Δ : Set S) η ζ) ∂(Measure.pi fun _ : Δ ↦ ν) =
      (isssd ν).modification ρ hmod Δ η Ã := fun η ↦ by
    rw [modification_apply, withDensity_apply _ hÃ',
      setLIntegral_isssd_eq_setLIntegral_juxt ν (hmod.measurable Δ) hÃ' η, hpre]
  have hF₁ : ∫⁻ p in B ×ˢ A, condDensity ν ρ Δ Λ' (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2)
      ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) =
      ∫⁻ ω in B, (isssd ν).modification ρ hmod Λ' ((shift E i).toFun ω) Ã ∂μ := by
    have hm : Measurable fun p : (S → E) × (Δ → E) ↦
        condDensity ν ρ Δ Λ' (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2) :=
      hcond.comp (measurable_juxt_shift Δ i)
    rw [← Measure.prod_restrict, lintegral_prod _ hm.aemeasurable]
    exact lintegral_congr fun ω ↦ hinner₁ _
  have hF₂ : ∫⁻ p in B ×ˢ A, ρ Δ (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2)
      ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) =
      ∫⁻ ω in B, (isssd ν).modification ρ hmod Δ ((shift E i).toFun ω) Ã ∂μ := by
    have hm : Measurable fun p : (S → E) × (Δ → E) ↦
        ρ Δ (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2) :=
      (hmod.measurable Δ).comp (measurable_juxt_shift Δ i)
    rw [← Measure.prod_restrict, lintegral_prod _ hm.aemeasurable]
    exact lintegral_congr fun ω ↦ hinner₂ _
  set B' := (shift E i).inv.toFun ⁻¹' B with hB'def
  have hBB' : B = (shift E i).toFun ⁻¹' B' := (shift_toFun_preimage_inv_toFun_preimage i B).symm
  have hB'Λ' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ' : Set S)ᶜ)] B' :=
    measurableSet_cylinderEvents_compl_preimage_shift_inv i Λ hB
  have hB'Δ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Set S)ᶜ)] B' :=
    cylinderEvents_mono (compl_subset_compl.2 (Finset.coe_subset.2 hΔ)) _ hB'Λ'
  have hB'm : MeasurableSet B' := cylinderEvents_le_pi _ hB'Λ'
  have hmeas₁ : Measurable fun η ↦ (isssd ν).modification ρ hmod Λ' η Ã :=
    (((isssd ν).modification ρ hmod Λ').measurable_coe hÃ').mono cylinderEvents_le_pi le_rfl
  have hmeas₂ : Measurable fun η ↦ (isssd ν).modification ρ hmod Δ η Ã :=
    (((isssd ν).modification ρ hmod Δ).measurable_coe hÃ').mono cylinderEvents_le_pi le_rfl
  have h₁ : ∫⁻ ω in (shift E i).toFun ⁻¹' B', (isssd ν).modification ρ hmod Λ'
      ((shift E i).toFun ω) Ã ∂μ = ∫⁻ η in B', (isssd ν).modification ρ hmod Λ' η Ã ∂μ :=
    (hμinv i).setLIntegral_comp_preimage hB'm hmeas₁
  have h₂ : ∫⁻ ω in (shift E i).toFun ⁻¹' B', (isssd ν).modification ρ hmod Δ
      ((shift E i).toFun ω) Ã ∂μ = ∫⁻ η in B', (isssd ν).modification ρ hmod Δ η Ã ∂μ :=
    (hμinv i).setLIntegral_comp_preimage hB'm hmeas₂
  rw [hF₁, hF₂, hBB', h₁, h₂,
    IsGibbsMeasure.setLIntegral_kernel_eq_measure_inter hμ Λ' hÃ' hB'Λ',
    IsGibbsMeasure.setLIntegral_kernel_eq_measure_inter hμ Δ hÃ' hB'Δ]

/-- **Georgii (14.22)**, set-integral form: on every rectangle `B × A`, `B ∈ 𝓣_Λ`, the averaged
density `ρ̃_Δ` integrates like the ergodic average `|F|⁻¹ ∑_{i ∈ F} ρ̃_Δ ∘ θ̃_i`, provided every
`Λ + i`, `i ∈ F`, covers `Δ`. -/
lemma setLIntegral_prod_shiftAvgCondDensity (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ) {Δ F Λ : Finset S}
    (hF : ∀ i ∈ F, Δ ⊆ Λ.map (Equiv.addRight i).toEmbedding) {B : Set (S → E)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B)
    {A : Set (Δ → E)} (hA : MeasurableSet A) :
    ∫⁻ p in B ×ˢ A, shiftAvgCondDensity ν ρ Δ F Λ p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) =
      ∫⁻ p in B ×ˢ A, shiftAvgDensity ρ Δ F p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) := by
  unfold shiftAvgCondDensity shiftAvgDensity
  have hm₁ : ∀ i, Measurable fun p : (S → E) × (Δ → E) ↦
      condDensity ν ρ Δ (Λ.map (Equiv.addRight i).toEmbedding)
        (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2) := fun i ↦
    ((measurable_condDensity hmod.measurable Δ _).mono cylinderEvents_le_pi le_rfl).comp
      (measurable_juxt_shift Δ i)
  have hm₂ : ∀ i, Measurable fun p : (S → E) × (Δ → E) ↦
      ρ Δ (juxt (Δ : Set S) ((shift E i).toFun p.1) p.2) := fun i ↦
    (hmod.measurable Δ).comp (measurable_juxt_shift Δ i)
  rw [lintegral_const_mul _ (Finset.measurable_sum F fun i _ ↦ hm₁ i),
    lintegral_const_mul _ (Finset.measurable_sum F fun i _ ↦ hm₂ i),
    lintegral_finsetSum _ fun i _ ↦ hm₁ i, lintegral_finsetSum _ fun i _ ↦ hm₂ i]
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦
    setLIntegral_prod_condDensity_juxt_shift hmod hμ hμinv (hF i hi) hB hA

lemma lintegral_shiftAvgCondDensity (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ) {Δ F Λ : Finset S}
    (hF : ∀ i ∈ F, Δ ⊆ Λ.map (Equiv.addRight i).toEmbedding) :
    ∫⁻ p, shiftAvgCondDensity ν ρ Δ F Λ p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) =
      ∫⁻ p, shiftAvgDensity ρ Δ F p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)) := by
  have h := setLIntegral_prod_shiftAvgCondDensity hmod hμ hμinv hF MeasurableSet.univ
    (MeasurableSet.univ (α := Δ → E))
  rwa [univ_prod_univ, Measure.restrict_univ] at h

/-- **Georgii (14.22)**: `ρ̃^n_Δ = νp(|Λ'|⁻¹ ∑_{i ∈ Λ'} ρ̃_Δ ∘ θ̃_i | 𝓣_Λ × 𝓕_Δ)` `νp`-a.s., for
`νp = μ ⊗ λ^Δ` and `Λ + i ⊇ Δ` for all `i ∈ Λ'`. -/
lemma toReal_shiftAvgCondDensity_ae_eq_condExp (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ) {Δ F Λ : Finset S}
    (hF : ∀ i ∈ F, Δ ⊆ Λ.map (Equiv.addRight i).toEmbedding) :
    (fun p ↦ (shiftAvgCondDensity ν ρ Δ F Λ p).toReal) =ᵐ[μ.prod (Measure.pi fun _ : Δ ↦ ν)]
      (μ.prod (Measure.pi fun _ : Δ ↦ ν))[fun p ↦ (shiftAvgDensity ρ Δ F p).toReal |
        tailProdEvents Λ Δ] :=
  toReal_ae_eq_condExp_toReal_of_forall_prod cylinderEvents_le_pi le_rfl
    (measurable_shiftAvgDensity (hmod.measurable Δ) F)
    (measurable_shiftAvgCondDensity_tailProdEvents hmod.measurable Δ F Λ)
    (lintegral_shiftAvgDensity_ne_top hmod hμ hμinv Δ F)
    fun _ _ hs ht ↦ setLIntegral_prod_shiftAvgCondDensity hmod hμ hμinv hF hs ht

end ShiftDensities

end Specification

/-! ### Georgii (14.20)(c): the ergodic theorem for the shift on a fixed inner configuration -/

namespace MeasureTheory.GibbsMeasure

section ShiftErgodic

attribute [local instance] shiftAddAction measurableConstVAdd_shift

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [Countable S] [DecidableEq S]
  {μ : Measure (S → E)} {F : ℕ → Finset S} {C : ℝ≥0∞}

/-- **Georgii, Theorem (14.A8) for an ergodic shift-invariant random field**: the averages
`|F n|⁻¹ ∑_{i ∈ F n} f ∘ θ_i` of an a.e. bounded measurable `f` along an increasing regular Følner
sequence converge `μ`-a.s. to the constant `μ(f)`. -/
theorem ae_tendsto_inv_card_smul_sum_shift_of_mem_trivialOn [IsProbabilityMeasure μ]
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    (htriv : μ ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {f : (S → E) → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ} (hM : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f ((shift E i).toFun ω)) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  let := shiftAddAction (S := S) (E := E)
  have := vaddInvariantMeasure_of_forall_measurePreserving_shift hμinv
  rw [mem_trivialOn, smulInvariants_multiplicative_eq_invariantEvents_shiftGroup.symm] at htriv
  filter_upwards [ae_tendsto_inv_card_smul_sum_vadd_condExp hF hne hFol hC hC'
    (Integrable.of_bound hf M hM), condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one
      MeasurableSpace.smulInvariants_le htriv f] with ω hω hc
  rwa [hc] at hω

/-- **Georgii, Theorem (14.A8) for an ergodic shift-invariant random field, integrable case.**
The averages `|F n|⁻¹ ∑_{i ∈ F n} f ∘ θ_i` of a merely *integrable* measurable `f` along an
increasing regular Følner sequence converge `μ`-a.s. to the constant `μ(f)`. Generalises
`ae_tendsto_inv_card_smul_sum_shift_of_mem_trivialOn`, which specialises this to bounded `f` via
`Integrable.of_bound`. -/
theorem ae_tendsto_inv_card_smul_sum_shift_of_mem_trivialOn_of_integrable [IsProbabilityMeasure μ]
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    (htriv : μ ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {f : (S → E) → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f ((shift E i).toFun ω)) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  let := shiftAddAction (S := S) (E := E)
  have := vaddInvariantMeasure_of_forall_measurePreserving_shift hμinv
  rw [mem_trivialOn, smulInvariants_multiplicative_eq_invariantEvents_shiftGroup.symm] at htriv
  filter_upwards [ae_tendsto_inv_card_smul_sum_vadd_condExp hF hne hFol hC hC' hf,
    condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one
      MeasurableSpace.smulInvariants_le htriv f] with ω hω hc
  rwa [hc] at hω

end ShiftErgodic

end MeasureTheory.GibbsMeasure

namespace Specification

open MeasureTheory.GibbsMeasure

section Convergence

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [Countable S] [DecidableEq S]
  {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
  {μ : Measure (S → E)} [IsProbabilityMeasure μ] {F Λ : ℕ → Finset S} {C : ℝ≥0∞}

/-- **Georgii (14.23)–(14.24) for the truncated densities.** For every inner configuration `ζ`,
the ergodic theorem for the ergodic shift-invariant `μ` on `Ω` gives, `μ`-a.s. in `ω`,
`|F n|⁻¹ ∑_{i ∈ F n} min (ρ_Δ(ζ (θ_i ω)_{S∖Δ})) M → ρ̄^M_Δ(ζ)`; the averages over the covering
indices `Λ'_n ⊆ F n` have the same limit since `|F n \ Λ'_n| / |F n| → 0` and the summands are
bounded by `M`. Fubini turns this into a `μ ⊗ λ^Δ`-a.s. statement. -/
lemma ae_tendsto_toReal_shiftAvgDensity_min (hρ : ∀ Λ, Measurable (ρ Λ))
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    (htriv : μ ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞) {Δ : Finset S}
    (hsdiff : Tendsto (fun n ↦ ((F n \ coveringIndices Δ (F n) (Λ n)).card : ℝ) / (F n).card)
      atTop (𝓝 0)) (M : ℕ) :
    ∀ᵐ p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)), Tendsto (fun n ↦
      (shiftAvgDensity (fun Λ σ ↦ min (ρ Λ σ) M) Δ (coveringIndices Δ (F n) (Λ n)) p).toReal)
      atTop (𝓝 ((avgKernel (fun Λ σ ↦ min (ρ Λ σ) M) μ Δ p.2).toReal)) := by
  set ρM : Finset S → (S → E) → ℝ≥0∞ := fun Λ σ ↦ min (ρ Λ σ) M with hρM
  have hρMm : ∀ Λ, Measurable (ρM Λ) := fun Λ ↦ (hρ Λ).min measurable_const
  -- the ergodic theorem on `Ω` for the bounded function `ω ↦ min (ρ_Δ(ζ ω_{S∖Δ})) M`
  have hstep : ∀ ζ : Δ → E, ∀ᵐ ω ∂μ, Tendsto (fun n ↦
      (shiftAvgDensity ρM Δ (coveringIndices Δ (F n) (Λ n)) (ω, ζ)).toReal) atTop
      (𝓝 ((avgKernel ρM μ Δ ζ).toReal)) := by
    intro ζ
    set h : (S → E) → ℝ := fun ω ↦ (ρM Δ (juxt (Δ : Set S) ω ζ)).toReal with hh
    have hhm : Measurable h := ((hρMm Δ).comp (measurable_juxt_boundary ζ)).ennreal_toReal
    have hh0 : ∀ ω, 0 ≤ h ω := fun ω ↦ ENNReal.toReal_nonneg
    have hhM : ∀ ω, h ω ≤ M := fun ω ↦ by
      rw [hh]
      exact (ENNReal.toReal_mono (ENNReal.natCast_ne_top M) (min_le_right _ _)).trans
        (by rw [ENNReal.toReal_natCast])
    have hint : ∫ ω, h ω ∂μ = (avgKernel ρM μ Δ ζ).toReal := by
      have hm : Measurable fun ω ↦ ρM Δ (juxt (Δ : Set S) ω ζ) :=
        (hρMm Δ).comp (measurable_juxt_boundary ζ)
      simp only [hh]
      rw [integral_toReal hm.aemeasurable
        (ae_of_all _ fun ω ↦ (min_le_right _ _).trans_lt (ENNReal.natCast_lt_top M))]
      rfl
    have herg := ae_tendsto_inv_card_smul_sum_shift_of_mem_trivialOn hμinv htriv hF hne hFol hC
      hC' hhm.aestronglyMeasurable (M := M) (ae_of_all _ fun ω ↦ by
        rw [Real.norm_of_nonneg (hh0 ω)]; exact hhM ω)
    filter_upwards [herg] with ω hω
    rw [hint] at hω
    -- pass from the average over `F n` to the average over the covering indices
    refine hω.congr_dist (squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
      (by simpa using hsdiff.const_mul (M : ℝ)))
    rw [Real.dist_eq, toReal_shiftAvgDensity_min, smul_eq_mul, abs_sub_comm]
    exact MeasureTheory.abs_inv_card_mul_sum_sub_inv_card_mul_sum_le
      (coveringIndices_subset Δ (F n) (Λ n)) (h := fun i ↦ h ((shift E i).toFun ω))
      (fun i _ ↦ hh0 _) (fun i _ ↦ hhM _)
  -- Fubini
  have hmeas : MeasurableSet {p : (S → E) × (Δ → E) | Tendsto (fun n ↦
      (shiftAvgDensity ρM Δ (coveringIndices Δ (F n) (Λ n)) p).toReal) atTop
      (𝓝 ((avgKernel ρM μ Δ p.2).toReal))} :=
    measurableSet_tendsto_nhds
      (fun n ↦ (measurable_shiftAvgDensity (hρMm Δ) _).ennreal_toReal)
      (((measurable_avgKernel μ (hρMm Δ)).comp measurable_snd).ennreal_toReal)
  exact (Measure.ae_prod_iff_ae_ae hmeas).2 ((Measure.ae_ae_comm hmeas).2 (ae_of_all _ hstep))

/-- **Georgii (14.22)–(14.24) combined with Lemma (14.19), lower half.** For
`νp = μ ⊗ λ^Δ`-almost every `(ω, ζ)`, every `a < ρ̄_Δ(ζ)` is eventually below the averaged
densities `ρ̃^n_Δ(ω, ζ)`.

Georgii applies (14.19) directly to the unbounded averages `|Λ'_n|⁻¹ ∑ ρ̃_Δ ∘ θ̃_i`, whose
dominating function is the (in general non-integrable) ergodic maximal function; the domination
hypothesis (i) of (14.19) is only available for the **truncated** densities `min ρ_Δ M`. These
give `liminf ρ̃^n_Δ ≥ ρ̄^M_Δ` for every `M` by monotonicity of conditional expectations, and
`ρ̄^M_Δ ↑ ρ̄_Δ`. -/
lemma ae_forall_lt_eventually_le_toReal_shiftAvgCondDensity (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    (htriv : μ ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hmono : Monotone Λ) {Δ : Finset S}
    (hsdiff : Tendsto (fun n ↦ ((F n \ coveringIndices Δ (F n) (Λ n)).card : ℝ) / (F n).card)
      atTop (𝓝 0)) :
    ∀ᵐ p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)), ∀ a < (avgKernel ρ μ Δ p.2).toReal,
      ∀ᶠ n in atTop,
        a ≤ (shiftAvgCondDensity ν ρ Δ (coveringIndices Δ (F n) (Λ n)) (Λ n) p).toReal := by
  set νp := μ.prod (Measure.pi fun _ : Δ ↦ ν) with hνp
  set F' : ℕ → Finset S := fun n ↦ coveringIndices Δ (F n) (Λ n) with hF'
  have hF'cov : ∀ n, ∀ i ∈ F' n, Δ ⊆ (Λ n).map (Equiv.addRight i).toEmbedding := fun n i hi ↦
    subset_of_mem_coveringIndices hi
  have hle : ∀ n, tailProdEvents (S := S) (E := E) (Λ n) Δ ≤ Prod.instMeasurableSpace := fun n ↦
    tailProdEvents_le _ _
  have hiInf_le : (⨅ n, tailProdEvents (S := S) (E := E) (Λ n) Δ) ≤ Prod.instMeasurableSpace :=
    (iInf_le _ 0).trans (hle 0)
  -- the untruncated averages are a.e. finite, with `ρ̃^n_Δ` as conditional expectation
  have hfin : ∀ n, ∀ᵐ p ∂νp, shiftAvgDensity ρ Δ (F' n) p < ∞ := fun n ↦
    ae_lt_top' (measurable_shiftAvgDensity (hmod.measurable Δ) _).aemeasurable
      (lintegral_shiftAvgDensity_ne_top hmod hμ hμinv Δ _)
  have hcond : ∀ n, (fun p ↦ (shiftAvgCondDensity ν ρ Δ (F' n) (Λ n) p).toReal) =ᵐ[νp]
      νp[fun p ↦ (shiftAvgDensity ρ Δ (F' n) p).toReal | tailProdEvents (Λ n) Δ] := fun n ↦
    toReal_shiftAvgCondDensity_ae_eq_condExp hmod hμ hμinv (hF'cov n)
  have hint : ∀ n, Integrable (fun p ↦ (shiftAvgDensity ρ Δ (F' n) p).toReal) νp := fun n ↦
    integrable_toReal_of_lintegral_ne_top
      (measurable_shiftAvgDensity (hmod.measurable Δ) _).aemeasurable
      (lintegral_shiftAvgDensity_ne_top hmod hμ hμinv Δ _)
  -- the truncated averages: (14.19) applies
  have hM : ∀ M : ℕ, ∀ᵐ p ∂νp, ∀ a < (avgKernel (fun Λ σ ↦ min (ρ Λ σ) M) μ Δ p.2).toReal,
      ∀ᶠ n in atTop, a ≤ (shiftAvgCondDensity ν ρ Δ (F' n) (Λ n) p).toReal := by
    intro M
    set ρM : Finset S → (S → E) → ℝ≥0∞ := fun Λ σ ↦ min (ρ Λ σ) M with hρM
    have hρMm : ∀ Λ, Measurable (ρM Λ) := fun Λ ↦ (hmod.measurable Λ).min measurable_const
    set G : (S → E) × (Δ → E) → ℝ := fun p ↦ (avgKernel ρM μ Δ p.2).toReal with hG
    have hGm : ∀ Λ' : Finset S, Measurable[tailProdEvents (S := S) (E := E) Λ' Δ] G := fun Λ' ↦
      ((measurable_avgKernel μ (hρMm Δ)).comp
        (@measurable_snd _ _ (cylinderEvents (X := fun _ : S ↦ E) ((Λ' : Set S)ᶜ))
          _)).ennreal_toReal
    have hGi : Integrable G νp := by
      refine Integrable.of_bound (((hGm (Λ 0)).mono (hle 0) le_rfl).aestronglyMeasurable) M
        (ae_of_all _ fun p ↦ ?_)
      rw [hG, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact (ENNReal.toReal_mono (ENNReal.natCast_ne_top M) (avgKernel_min_le Δ M p.2)).trans
        (by rw [ENNReal.toReal_natCast])
    have hGcond : νp[G | ⨅ n, tailProdEvents (Λ n) Δ] = G :=
      condExp_of_stronglyMeasurable hiInf_le
        ((measurable_iInf_iff_forall _).2 fun n ↦ hGm (Λ n)).stronglyMeasurable hGi
    have hintM : ∀ n, Integrable (fun p ↦ (shiftAvgDensity ρM Δ (F' n) p).toReal) νp := fun n ↦
      integrable_toReal_of_lintegral_ne_top (measurable_shiftAvgDensity (hρMm Δ) _).aemeasurable
        (ne_top_of_le_ne_top (ENNReal.natCast_ne_top M)
          (lintegral_shiftAvgDensity_min_le Δ _ M))
    have hbound : ∀ n, ∀ᵐ p ∂νp, ‖(shiftAvgDensity ρM Δ (F' n) p).toReal‖ ≤ M := fun n ↦
      ae_of_all _ fun p ↦ by
        rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact (ENNReal.toReal_mono (ENNReal.natCast_ne_top M)
          (shiftAvgDensity_min_le Δ _ M p)).trans (by rw [ENNReal.toReal_natCast])
    have hlim := ae_tendsto_toReal_shiftAvgDensity_min (ν := ν) hmod.measurable hμinv htriv hF hne
      hFol hC hC' hsdiff M
    have hconv := tendsto_ae_condExp_of_antitone_of_dominated (μ := νp)
      (antitone_tailProdEvents hmono Δ) hle (fun n ↦ (hintM n).aestronglyMeasurable)
      (integrable_const (M : ℝ)) hbound hlim
    rw [hGcond] at hconv
    -- monotonicity: the truncated conditional expectations are below `ρ̃^n_Δ`
    have hmono' : ∀ n, ∀ᵐ p ∂νp, (νp[fun p ↦ (shiftAvgDensity ρM Δ (F' n) p).toReal |
        tailProdEvents (Λ n) Δ]) p ≤ (shiftAvgCondDensity ν ρ Δ (F' n) (Λ n) p).toReal := by
      intro n
      have h := condExp_mono (m := tailProdEvents (Λ n) Δ) (hintM n) (hint n) ?_
      · filter_upwards [h, hcond n] with p hp hp'
        rw [hp']; exact hp
      · filter_upwards [hfin n] with p hp
        refine ENNReal.toReal_mono hp.ne ?_
        unfold shiftAvgDensity
        gcongr with i _
        exact min_le_left _ _
    filter_upwards [hconv, ae_all_iff.2 hmono'] with p hp hp' a ha
    filter_upwards [hp.eventually_const_lt ha] with n hn
    exact hn.le.trans (hp' n)
  -- pass to the supremum over the truncation levels
  have hfinK : ∀ᵐ p ∂νp, avgKernel ρ μ Δ p.2 < ∞ := by
    have h : ∀ᵐ ζ ∂(Measure.pi fun _ : Δ ↦ ν), avgKernel ρ μ Δ ζ < ∞ :=
      ae_lt_top' (measurable_avgKernel μ (hmod.measurable Δ)).aemeasurable
        (by rw [lintegral_avgKernel hmod hμ Δ]; exact ENNReal.one_ne_top)
    exact Measure.quasiMeasurePreserving_snd.ae h
  filter_upwards [ae_all_iff.2 hM, hfinK] with p hp hfinp a ha
  rcases lt_or_ge a 0 with ha0 | ha0
  · exact Eventually.of_forall fun n ↦ ha0.le.trans ENNReal.toReal_nonneg
  have h1 : ENNReal.ofReal a < avgKernel ρ μ Δ p.2 :=
    (ENNReal.ofReal_lt_iff_lt_toReal ha0 hfinp.ne).2 ha
  rw [avgKernel_eq_iSup_min (hmod.measurable Δ), lt_iSup_iff] at h1
  obtain ⟨M, hM'⟩ := h1
  refine hp M a ((ENNReal.ofReal_lt_iff_lt_toReal ha0 ?_).1 hM')
  exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top M) (avgKernel_min_le Δ M p.2)

/-- **Georgii (14.20)(c), one finite volume `Δ`**: for `μ`-almost every boundary condition `ω`,
the averaged Gibbs distributions `|F n|⁻¹ ∑_{i ∈ F n} γ_{Λ n + i}(A | θ_i ω)` converge to `μ(A)`
for **every** event `A` of `Δ` simultaneously. Scheffé's lemma turns the lower limit of the
averaged densities into `L¹(λ^Δ)`-convergence to `ρ̄_Δ`; the events of `Δ` see only the
covering indices `Λ'_n ⊆ F n`, whose complement has vanishing fraction. -/
theorem ae_forall_tendsto_shiftAverage_real_of_measurableSet_cylinderEvents
    (hmod : (isssd ν).IsModifier ρ) (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    (htriv : μ ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hmono : Monotone Λ)
    (hcouple : ∀ δ : S, Tendsto (fun n ↦ (((F n).filter fun i ↦ δ - i ∉ Λ n).card : ℝ) /
      (F n).card) atTop (𝓝 0)) (Δ : Finset S) :
    ∀ᵐ ω ∂μ, ∀ A, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A →
      Tendsto (fun n ↦ (((isssd ν).modification ρ hmod).shiftAverage (F n) (Λ n) ω).real A) atTop
        (𝓝 (μ.real A)) := by
  set lam : Measure (Δ → E) := Measure.pi fun _ : Δ ↦ ν with hlam
  set F' : ℕ → Finset S := fun n ↦ coveringIndices Δ (F n) (Λ n) with hF'
  have hne' : ∀ n, (F n).Nonempty := fun n ↦ hne.mono (hF (Nat.zero_le n))
  have hsdiff := tendsto_card_sdiff_coveringIndices_div hcouple Δ
  have hev : ∀ᶠ n in atTop, (F' n).Nonempty := eventually_nonempty_coveringIndices hne' hsdiff
  have hF'cov : ∀ n, ∀ i ∈ F' n, Δ ⊆ (Λ n).map (Equiv.addRight i).toEmbedding := fun n i hi ↦
    subset_of_mem_coveringIndices hi
  have hKm : Measurable (avgKernel ρ μ Δ) := measurable_avgKernel μ (hmod.measurable Δ)
  have hKint : Integrable (fun ζ ↦ (avgKernel ρ μ Δ ζ).toReal) lam :=
    integrable_toReal_of_lintegral_ne_top hKm.aemeasurable
      (by rw [lintegral_avgKernel hmod hμ Δ]; exact ENNReal.one_ne_top)
  have hlim := Measure.ae_ae_of_ae_prod (ae_forall_lt_eventually_le_toReal_shiftAvgCondDensity
    hmod hμ hμinv htriv hF hne hFol hC hC' hmono hsdiff)
  filter_upwards [hlim] with ω hω
  -- Scheffé: `L¹(λ^Δ)`-convergence of the averaged densities
  have hRm : ∀ n, Measurable fun ζ ↦ shiftAvgCondDensity ν ρ Δ (F' n) (Λ n) (ω, ζ) := fun n ↦
    (measurable_shiftAvgCondDensity hmod.measurable Δ _ _).comp measurable_prodMk_left
  have hRint : ∀ n, Integrable (fun ζ ↦ (shiftAvgCondDensity ν ρ Δ (F' n) (Λ n) (ω, ζ)).toReal)
      lam := fun n ↦ integrable_toReal_of_lintegral_ne_top (hRm n).aemeasurable
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      (lintegral_shiftAvgCondDensity_snd_le_one hmod (hF'cov n) ω))
  have hL1 : Tendsto (fun n ↦ ∫ ζ, |(shiftAvgCondDensity ν ρ Δ (F' n) (Λ n) (ω, ζ)).toReal -
      (avgKernel ρ μ Δ ζ).toReal| ∂lam) atTop (𝓝 0) := by
    refine MeasureTheory.tendsto_integral_abs_sub_of_forall_lt_eventually_le hRint hKint
      (fun n ↦ ae_of_all _ fun ζ ↦ ENNReal.toReal_nonneg) ?_ hω
    filter_upwards [hev] with n hn
    rw [integral_toReal (hRm n).aemeasurable (ae_lt_top' (hRm n).aemeasurable
        (ne_top_of_le_ne_top ENNReal.one_ne_top
          (lintegral_shiftAvgCondDensity_snd_le_one hmod (hF'cov n) ω))),
      integral_toReal hKm.aemeasurable (ae_lt_top' hKm.aemeasurable
        (by rw [lintegral_avgKernel hmod hμ Δ]; exact ENNReal.one_ne_top)),
      lintegral_shiftAvgCondDensity_snd hmod (hF'cov n) hn ω, lintegral_avgKernel hmod hμ Δ]
  intro A hA
  -- the events of `Δ`: pass from the covering indices to all of `F n`
  have hprob : ∀ n, ∀ i, IsProbabilityMeasure ((isssd ν).modification ρ hmod
      ((Λ n).map (Equiv.addRight i).toEmbedding) ((shift E i).toFun ω)) := fun _ _ ↦ inferInstance
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun n ↦ 2 * (((F n \ F' n).card : ℝ) / (F n).card) + ∫ ζ,
      |(shiftAvgCondDensity ν ρ Δ (F' n) (Λ n) (ω, ζ)).toReal - (avgKernel ρ μ Δ ζ).toReal| ∂lam)
    (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ ?_
  · filter_upwards [hev] with n hn
    have hsub : F' n ⊆ F n := coveringIndices_subset Δ (F n) (Λ n)
    have hb1 := MeasureTheory.abs_uniformAverage_real_sub_le_of_subset
      (fun i ↦ (isssd ν).modification ρ hmod ((Λ n).map (Equiv.addRight i).toEmbedding)
        ((shift E i).toFun ω)) (hprob n) hn hsub A
    have hb2 := abs_shiftAverage_real_sub_le_integral_abs hmod hμ (hF'cov n) ω hA
    have hcard : 1 - ((F' n).card : ℝ) / (F n).card = ((F n \ F' n).card : ℝ) / (F n).card := by
      rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), sub_div,
        div_self (by exact_mod_cast (hne' n).card_pos.ne')]
    rw [hcard] at hb1
    rw [Real.norm_eq_abs]
    calc |(((isssd ν).modification ρ hmod).shiftAverage (F n) (Λ n) ω).real A - μ.real A|
        ≤ |(((isssd ν).modification ρ hmod).shiftAverage (F n) (Λ n) ω).real A -
            (((isssd ν).modification ρ hmod).shiftAverage (F' n) (Λ n) ω).real A| +
          |(((isssd ν).modification ρ hmod).shiftAverage (F' n) (Λ n) ω).real A - μ.real A| :=
          abs_sub_le _ _ _
      _ ≤ 2 * (((F n \ F' n).card : ℝ) / (F n).card) + ∫ ζ,
          |(shiftAvgCondDensity ν ρ Δ (F' n) (Λ n) (ω, ζ)).toReal - (avgKernel ρ μ Δ ζ).toReal|
            ∂lam := add_le_add hb1 hb2
  · simpa using (hsdiff.const_mul 2).add hL1

/-- **Georgii, Theorem (14.20)(c).** Let `γ = ρ λ` be a λ-specification with a probability a
priori measure `λ`, `μ ∈ 𝒢(γ)` shift-invariant and ergodic — by (14.15)(a), `μ ∈ ex 𝒢_Θ(γ)` —
`F` an increasing regular Følner sequence of finite sets of sites, `Λ` an increasing sequence
of volumes such that, for every site `δ`, the fraction of `i ∈ F n` with `δ ∉ Λ n + i` vanishes.
Then `|F n|⁻¹ ∑_{i ∈ F n} γ_{Λ n + i}(· | θ_i ω) → μ` **in the topology of local convergence**
for `μ`-almost all `ω`. No shift-invariance of `γ` is used.

Georgii's proof: for each finite volume `Δ`, the averaged densities `ρ̃^n_Δ` are conditional
expectations on `𝓣_{Λ n} × 𝓕_Δ` of the ergodic averages of `ρ̃_Δ` under `μ ⊗ λ^Δ` (14.22), which
converge to `ρ̄_Δ(ζ)` by the ergodic theorem (14.A8) and the ergodicity of `μ` (14.23)–(14.24);
Lemma (14.19) — applied after truncation, see
`Specification.ae_forall_lt_eventually_le_toReal_shiftAvgCondDensity` — and Scheffé's lemma give
`λ^Δ(|ρ̃^n_Δ(ω, ·) - ρ̄_Δ|) → 0` for `μ`-a.a. `ω`, which controls all events of `Δ` at once. -/
theorem ae_tendsto_shiftAverage_withLocalConvergence (hmod : (isssd ν).IsModifier ρ)
    {μ : ProbabilityMeasure (S → E)} (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun (μ : Measure (S → E)) μ)
    (htriv : (μ : Measure (S → E)) ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hmono : Monotone Λ)
    (hcouple : ∀ δ : S, Tendsto (fun n ↦ (((F n).filter fun i ↦ δ - i ∉ Λ n).card : ℝ) /
      (F n).card) atTop (𝓝 0)) :
    ∀ᵐ ω ∂(μ : Measure (S → E)), Tendsto (fun n ↦ (WithSetwiseTopology.ofMeasure
      (((isssd ν).modification ρ hmod).shiftAveragePM (hne.mono (hF (Nat.zero_le n))) (Λ n) ω) :
        WithLocalConvergence S E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  have h : ∀ᵐ ω ∂(μ : Measure (S → E)), ∀ Δ : Finset S, ∀ A,
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A →
      Tendsto (fun n ↦ (((isssd ν).modification ρ hmod).shiftAverage (F n) (Λ n) ω).real A) atTop
        (𝓝 ((μ : Measure (S → E)).real A)) :=
    ae_all_iff.2 fun Δ ↦ ae_forall_tendsto_shiftAverage_real_of_measurableSet_cylinderEvents hmod
      hμ hμinv htriv hF hne hFol hC hC' hmono hcouple Δ
  filter_upwards [h] with ω hω
  refine tendsto_withLocalConvergence_iff.2 fun A hA ↦ ?_
  obtain ⟨Δ, hΔ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  have := hω Δ A hΔ
  simp only [measureReal_def] at this
  exact (ENNReal.tendsto_toReal_iff (fun n ↦ measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- **Georgii, Theorem (14.20)(c)** stated for a λ-specification `γ = ρ λ` in the sense of
Definition (1.27) with a probability a priori measure `λ`. By Remark (1.28)(3),
`Specification.lambdaSpecification_probNormalize`, this covers every finite non-zero a priori
measure. -/
theorem ae_tendsto_shiftAverage_withLocalConvergence_lambdaSpecification
    (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) {μ : ProbabilityMeasure (S → E)}
    (hμ : (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun (μ : Measure (S → E)) μ)
    (htriv : (μ : Measure (S → E)) ∈ trivialOn (invariantEvents (shiftGroup S E)))
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hmono : Monotone Λ)
    (hcouple : ∀ δ : S, Tendsto (fun n ↦ (((F n).filter fun i ↦ δ - i ∉ Λ n).card : ℝ) /
      (F n).card) atTop (𝓝 0)) :
    ∀ᵐ ω ∂(μ : Measure (S → E)), Tendsto (fun n ↦ (WithSetwiseTopology.ofMeasure
      ((lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).shiftAveragePM
        (hne.mono (hF (Nat.zero_le n))) (Λ n) ω) :
        WithLocalConvergence S E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  rw [lambdaSpecification_eq_modification_isssd (S := S) (E := E) ν hρ hZ] at hμ ⊢
  exact ae_tendsto_shiftAverage_withLocalConvergence _ hμ hμinv htriv hF hne hFol hC hC' hmono
    hcouple

/-- **Georgii, Theorem (14.20)(c)** as stated: for a λ-specification on a countable infinite
abelian group of sites and `μ ∈ ex 𝒢_Θ(γ)`. -/
theorem ae_tendsto_shiftAverage_withLocalConvergence_of_mem_extremePoints_invariantG [Infinite S]
    (hmod : (isssd ν).IsModifier ρ) {μ : ProbabilityMeasure (S → E)}
    (hμ : (μ : Measure (S → E)) ∈
      (invariantG ((isssd ν).modification ρ hmod) (shiftGroup S E)).extremePoints ℝ≥0∞)
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hmono : Monotone Λ)
    (hcouple : ∀ δ : S, Tendsto (fun n ↦ (((F n).filter fun i ↦ δ - i ∉ Λ n).card : ℝ) /
      (F n).card) atTop (𝓝 0)) :
    ∀ᵐ ω ∂(μ : Measure (S → E)), Tendsto (fun n ↦ (WithSetwiseTopology.ofMeasure
      (((isssd ν).modification ρ hmod).shiftAveragePM (hne.mono (hF (Nat.zero_le n))) (Λ n) ω) :
        WithLocalConvergence S E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) :=
  ae_tendsto_shiftAverage_withLocalConvergence hmod hμ.1.1.2
    (mem_invariantFields_shiftGroup.1 hμ.1.2).2
    ((mem_extremePoints_invariantG_iff_mem_trivialOn
      (shiftGroup_exists_disjoint_sites_preimage (E := E)) hμ.1).1 hμ) hF hne hFol hC hC' hmono
    hcouple

end Convergence

end Specification

/-! ### Georgii's setting: the cubes `Λ_n = [-n, n]^d` of `ℤ^d` -/

namespace MeasureTheory.GibbsMeasure

section Lattice

attribute [local instance] shiftAddAction measurableConstVAdd_shift

variable {E : Type*} [MeasurableSpace E] {d : ℕ}

open Finset in
/-- The cube `[-n, n]^d` is the translate by `(-n, …, -n)` of the cube `[0, 2n + 1)^d`. -/
lemma piFinset_Icc_eq_vadd_piFinset_Ico (n : ℕ) :
    (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) =
      (fun _ : Fin d ↦ -(n : ℤ)) +ᵥ
        Fintype.piFinset fun _ : Fin d ↦ Finset.Ico (0 : ℤ) (2 * n + 1) := by
  ext x
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_vadd_finset, Finset.mem_Ico]
  constructor
  · intro hx
    refine ⟨fun k ↦ x k + n, fun k ↦ ⟨by linarith [(hx k).1], by linarith [(hx k).2]⟩, ?_⟩
    funext k
    simp only [vadd_eq_add, Pi.add_apply]
    ring
  · rintro ⟨y, hy, rfl⟩ k
    simp only [vadd_eq_add, Pi.add_apply]
    constructor <;> linarith [(hy k).1, (hy k).2]

/-- The cubes `[-n, n]^d` are increasing. -/
lemma monotone_piFinset_Icc :
    Monotone fun n : ℕ ↦ (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) :=
  fun _ _ h ↦ piFinset_Icc_subset h

lemma piFinset_Icc_zero_nonempty :
    (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-((0 : ℕ) : ℤ)) (0 : ℕ)).Nonempty :=
  ⟨0, Fintype.mem_piFinset.2 fun _ ↦ by simp⟩

/-- **The cubes `[-n, n]^d` form a Følner sequence** in `ℤ^d`. -/
lemma tendsto_card_vadd_piFinset_Icc_symmDiff_div_card (g : Fin d → ℤ) :
    Tendsto (fun n : ℕ ↦ (((g +ᵥ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) ∆
        (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n)).card : ℝ) /
      (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n).card) atTop (𝓝 0) := by
  simp_rw [piFinset_Icc_eq_vadd_piFinset_Ico]
  exact tendsto_card_vadd_cube_symmDiff_div_card (fun n ↦ fun _ ↦ -(n : ℤ)) (r := fun n ↦ 2 * n + 1)
    (tendsto_atTop_mono (fun n ↦ by change n ≤ 2 * n + 1; omega) tendsto_id) g

/-- **Tempelman regularity of the cubes `[-n, n]^d`** with constant `3 ^ d`. -/
lemma card_sub_add_piFinset_Icc_le (n : ℕ) :
    (((Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) -
      (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) +
      (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n)).card : ℝ≥0∞) ≤
      (3 ^ Fintype.card (Fin d) : ℝ≥0∞) *
        (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n).card := by
  rw [piFinset_Icc_eq_vadd_piFinset_Ico]
  exact_mod_cast card_sub_add_cube_le (fun _ ↦ -(n : ℤ)) (2 * n + 1)

variable [NeZero d] {γ : Specification (Fin d → ℤ) E}

/-- **Georgii, Theorem (14.20)(a) on `ℤ^d`**: for a shift-invariant specification `γ` on `ℤ^d`,
`μ ∈ ex 𝒢_Θ(γ)`, the cubes `Λ_n = [-n, n]^d` and a bounded measurable `f`,
`γ_{Λ_n}(|Λ_n|⁻¹ ∑_{i ∈ Λ_n} f ∘ θ_i) → μ(f)` `μ`-a.s. -/
theorem ae_tendsto_integral_kernel_inv_card_smul_sum_shift_cube {μ : Measure ((Fin d → ℤ) → E)}
    (hμ : μ ∈ (invariantG γ (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞)
    {f : ((Fin d → ℤ) → E) → ℝ} (hf : AEStronglyMeasurable f μ) {M : ℝ}
    (hM : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ M) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦
      ∫ x, ((Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n).card : ℝ)⁻¹ •
        ∑ i ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n, f ((shift E i).toFun x)
        ∂(γ (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) ω))
      atTop (𝓝 (∫ x, f x ∂μ)) :=
  ae_tendsto_integral_kernel_inv_card_smul_sum_shift_of_mem_extremePoints_invariantG hμ
    monotone_piFinset_Icc piFinset_Icc_zero_nonempty
    tendsto_card_vadd_piFinset_Icc_symmDiff_div_card card_sub_add_piFinset_Icc_le
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) monotone_piFinset_Icc hf hM

/-- **Georgii, Theorem (14.20)(b) on `ℤ^d`**: for a shift-invariant specification `γ` on `ℤ^d`
over a compact metrizable state space and `μ ∈ ex 𝒢_Θ(γ)`,
`|Λ_n|⁻¹ ∑_{i ∈ Λ_n} γ_{Λ_n + i}(· | θ_i ω) → μ` weakly for `μ`-almost all `ω`, where
`Λ_n = [-n, n]^d`. -/
theorem ae_tendsto_shiftAverage_weakly_cube [TopologicalSpace E] [CompactSpace E]
    [TopologicalSpace.MetrizableSpace E] [BorelSpace E]
    (hγ : ∀ j : Fin d → ℤ, Specification.IsInvariant (shift E j) γ)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμ : (μ : Measure ((Fin d → ℤ) → E)) ∈
      (invariantG γ (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞) :
    ∀ᵐ ω ∂(μ : Measure ((Fin d → ℤ) → E)), Tendsto (fun n : ℕ ↦ γ.shiftAveragePM
      (piFinset_Icc_zero_nonempty.mono (monotone_piFinset_Icc (Nat.zero_le n)))
      (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) ω) atTop (𝓝 μ) :=
  ae_tendsto_shiftAverage_weakly_of_mem_extremePoints_invariantG hγ hμ monotone_piFinset_Icc
    piFinset_Icc_zero_nonempty tendsto_card_vadd_piFinset_Icc_symmDiff_div_card
    card_sub_add_piFinset_Icc_le (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) monotone_piFinset_Icc

/-- **Georgii, Theorem (14.20)(c) on `ℤ^d`**: for a λ-specification `γ = ρ λ` on `ℤ^d` and
`μ ∈ ex 𝒢_Θ(γ)`, `|Λ_n|⁻¹ ∑_{i ∈ Λ_n} γ_{Λ_n + i}(· | θ_i ω) → μ` in the topology of local
convergence for `μ`-almost all `ω`, where `Λ_n = [-n, n]^d`. -/
theorem ae_tendsto_shiftAverage_withLocalConvergence_cube {ν : Measure E} [IsProbabilityMeasure ν]
    {ρ : Finset (Fin d → ℤ) → ((Fin d → ℤ) → E) → ℝ≥0∞}
    (hmod : (Specification.isssd ν).IsModifier ρ) {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμ : (μ : Measure ((Fin d → ℤ) → E)) ∈
      (invariantG ((Specification.isssd ν).modification ρ hmod)
        (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞) :
    ∀ᵐ ω ∂(μ : Measure ((Fin d → ℤ) → E)), Tendsto (fun n : ℕ ↦ (WithSetwiseTopology.ofMeasure
      (((Specification.isssd ν).modification ρ hmod).shiftAveragePM
        (piFinset_Icc_zero_nonempty.mono (monotone_piFinset_Icc (Nat.zero_le n)))
        (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) ω) :
        WithLocalConvergence (Fin d → ℤ) E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) :=
  Specification.ae_tendsto_shiftAverage_withLocalConvergence_of_mem_extremePoints_invariantG hmod hμ
    monotone_piFinset_Icc piFinset_Icc_zero_nonempty
    tendsto_card_vadd_piFinset_Icc_symmDiff_div_card card_sub_add_piFinset_Icc_le
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) monotone_piFinset_Icc
    tendsto_card_filter_sub_notMem_piFinset_Icc_div

end Lattice

end MeasureTheory.GibbsMeasure

end
