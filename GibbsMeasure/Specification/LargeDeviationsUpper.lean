/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.InformationTheory.KullbackLeibler.Cond
public import GibbsMeasure.Specification.BlockEntropy
public import GibbsMeasure.Specification.InvariantFieldsBarycenter
public import GibbsMeasure.Specification.LargeDeviationsLower

/-!
# The large-deviation upper bound, Georgii Theorem (15.45) / (15.46)

For `Φ ∈ ℬ_Θ` and a set `C ⊆ 𝓟_Θ` of shift-invariant random fields on `ℤ^d`, Georgii's upper
bound (15.46) reads

`limsup_{|Λ| → ∞} |Λ|⁻¹ log sup_ω γ^Φ_Λ(°R_Λ ∈ C | ω) ≤ − inf_{ν ∈ C̄} 𝓀(ν|Φ)`,

with `°R_Λ` the periodic empirical field (15.42) of `Specification/LargeDeviations.lean` and
`𝓀(·|Φ) = P(Φ) + ⟨·, Φ⟩ − 𝓀(·)` the excess free energy (15.32) of
`Specification/VariationalPrinciple.lean`. This file proves it, and the "in particular" clause
that it also holds for every `μ ∈ 𝒢(Φ)`.

## Main statements

* `MeasureTheory.GibbsMeasure.limsup_log_iSup_gibbsSpecification_div_card_le`: **(15.46)**, along
  any sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` of `ℤ^d` whose side lengths tend to infinity,
  with arbitrary torus reductions `π_n`. The logarithm is `ENNReal.log`, so the statement is
  meaningful also when the probability vanishes.
* `MeasureTheory.GibbsMeasure.limsup_log_isGibbsMeasure_div_card_le`: the **"in particular"**
  clause, the same bound for `μ(°R_Λ ∈ C)` with `μ ∈ 𝒢(Φ)` (no shift invariance of `μ`).
* `MeasureTheory.GibbsMeasure.eventually_gibbsSpecification_setOf_periodicEmpiricalFieldL_mem_le`:
  the bound in exponential form, `γ^Φ_Λ(°R_Λ ∈ C|ω) ≤ e^{−c|Λ|}` eventually and uniformly in
  `ω`, for every `c` strictly below the excess free energy on Georgii's `cx̄ C`.

## Georgii's four steps

**Step 1**, `MeasureTheory.GibbsMeasure.neg_log_gibbsSpecification_eq`, is the exponential
Chebyshev identity
`−log γ^Φ_Λ(A|ω) = 𝓗_Λ(γ^C_{Λ|ω}|λ^S) + γ^C_{Λ|ω}(H^Φ_Λ) + log Z^Φ_Λ(ω)` for the conditional
distribution `γ^C_{Λ|ω} = γ^Φ_Λ(·|ω)(·|A)`. It is Georgii (15.34)
(`Potential.relativeEntropyIn_gibbsSpecification_eq`) together with the fact that conditioning on
an event costs exactly `−log` of its probability
(`InformationTheory.klDiv_trim_cond_self`, in `GibbsMeasure/Mathlib/`).

**Step 2** replaces the finite-volume entropy by the specific entropy of the randomly shifted
independent-block field `γ̄^C_{Λ|ω}` of Proposition (15.52)
(`specificEntropy_tileAverage_map_finsetRestrict`), and the average Hamiltonian by the specific
energy of the mean empirical field `γ^C_{Λ|ω} °R_Λ` (`empiricalFieldAverage`) through the estimate
(15.25) (`abs_integral_hamiltonian_juxt_sub_card_mul_specificEnergy_le`). The outcome is the
single-volume inequality `specificRelativeEntropy_tileAverage_cond_le`. Georgii then argues by
contradiction: were the bound to fail, the block fields would have a cluster point `μ` with
`𝓀(μ|Φ) ≤ c` lying in `cx̄ C`. That is
`exists_mem_closedConvexHull_specificRelativeEntropy_le`. Its three ingredients are

* the two auxiliary fields are asymptotically equal on the local events
  (`abs_integral_tileAverage_sub_integral_empiricalFieldAverage_le`,
  `tendsto_measureReal_tileAverage_sub_measureReal_empiricalFieldAverage`), Georgii's remark that
  they are "asymptotically equivalent in the `𝓛`-topology";
* the mean empirical field lies in `cx̄ C`
  (`evalLocalEvents_empiricalFieldAverage_mem_convexHull`), Georgii's "basic observation";
* `𝓀(·|Φ)` is lower semicontinuous and `⟨·, Φ⟩` continuous, while
  `|Λ|⁻¹ log Z^Φ_Λ(ω) → P(Φ)` uniformly in `ω` (Theorem (15.30)(a)) and the boundary term of
  (15.25) is `o(|Λ|)`.

**Step 3** is Georgii (15.54), `inf_{cx̄ C} 𝓀(·|Φ) = inf_{C̄} 𝓀(·|Φ)`, supplied by
`MeasureTheory.GibbsMeasure.iInf_closedConvexHull_eq_iInf_closure_ereal` of
`Specification/InvariantFieldsBarycenter.lean`. It needs `𝓀(·|Φ)` **concave** on `𝓟_Θ`, which is
`smul_specificRelativeEntropy_add_smul_specificRelativeEntropy_le` below: the *convexity* half of
Proposition (15.14) for the specific entropy (`specificEntropy_smul_add_smul_le`, which needs
`d ≥ 1`) together with the affinity of the specific energy.

**Step 4** is the assembly, `limsup_log_iSup_gibbsSpecification_div_card_le`.

## The hypotheses, and where they differ from Georgii's

Georgii states (15.45) over a standard Borel state space. The proof here needs `E` **finite**
(with the discrete σ-algebra), in exactly three places, all in Steps 2 and 3; they are listed in
the docstring of `limsup_log_iSup_gibbsSpecification_div_card_le`. Finiteness buys, in exchange,
two simplifications of Georgii's argument: his approximation of `γ^C_{Λ|ω} °R_Λ` by convex
combinations through a partition of `[0, 1]^k` becomes an exact finite convex combination, and
his appeal to the compactness of the level sets `{𝓀 ≥ a}` becomes the compactness of the whole
space of random fields.

In one respect the statement here is *more* general than Georgii's: he assumes
`C ∈ 𝓔(𝓟_Θ)`, i.e. that `C` belongs to the evaluation σ-algebra of §7.3, which is what makes
`{°R_Λ ∈ C}` an event. Over a finite state space that is automatic for every `C ⊆ 𝓟_Θ`
(`measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem`), so the hypothesis on `C`
here is only `C ⊆ 𝓟_Θ`, which is the other half of Georgii's `C ∈ 𝓔(𝓟_Θ)`.

Steps 1 and 2 are proved for an arbitrary measurable state space: the single-volume inequality
`specificRelativeEntropy_tileAverage_cond_le`, the estimate (15.25) in integrated form
`abs_integral_hamiltonian_juxt_sub_card_mul_specificEnergy_le`, the asymptotic equality of the
two auxiliary fields `abs_integral_tileAverage_sub_integral_empiricalFieldAverage_le`, and the
concavity `smul_specificRelativeEntropy_add_smul_specificRelativeEntropy_le` of `𝓀(·|Φ)` all hold
with no finiteness assumption on `E`. What is missing for Georgii's standard Borel generality is
his change of topology: a countable core `𝒞 ⊆ 𝓕⁰` of `𝓕` (Corollary (4.A13)) and the fact that
the `𝒞`-topology turns `𝓟(Ω, 𝓕)` into a compact metrizable space (Comment (4.A10)(1)) are not
formalised in this library, and without them neither the cluster-point extraction nor Step 3 is
available over an infinite state space.

The lower bound (15.47) is in `Specification/LargeDeviationsLower.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Set Topology
open InformationTheory
open scoped ENNReal NNReal Pointwise Topology symmDiff

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The empirical field of a random field, Georgii's `γ °R_Λ` -/

section EmpiricalFieldAverage

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E]
  {G : AddSubgroup S} {Δ : Finset S} {π : S → S}

variable (E) in
/-- The translate `θ_{-i} σ^∘_Δ` of the periodic continuation of `σ_Δ`, as a function of the
configuration `σ`. The periodic empirical field `°R^σ_Δ` is the uniform average of the Dirac
measures at these points, `i ∈ Δ`. -/
def periodicTranslate (π : S → S) (i : S) (σ : S → E) : S → E :=
  (shift E (-i)).toFun (Potential.periodicExtend π σ)

/-- `(θ_{-i} σ^∘_Δ)_n = σ_{π(n + i)}`. -/
lemma periodicTranslate_apply (π : S → S) (i : S) (σ : S → E) (n : S) :
    periodicTranslate E π i σ n = σ (π (n + i)) := by
  simp [periodicTranslate, Potential.periodicExtend, sub_neg_eq_add]

lemma measurable_periodicTranslate (π : S → S) (i : S) :
    Measurable (periodicTranslate E π i) :=
  measurable_pi_lambda _ fun n ↦ by
    simpa only [periodicTranslate_apply] using measurable_pi_apply (π (n + i))

/-- **Georgii (15.42)** read through `periodicTranslate`: the periodic empirical field is the
uniform average of the Dirac measures at the translates `θ_{-i} σ^∘_Δ`, `i ∈ Δ`. -/
lemma periodicEmpiricalField_eq_uniformAverage_dirac (π : S → S) (Δ : Finset S) (σ : S → E) :
    periodicEmpiricalField E π Δ σ
      = uniformAverage (fun i ↦ Measure.dirac (periodicTranslate E π i σ)) Δ := rfl

variable (E) in
/-- **Georgii's `γ °R_Δ`**, the mean of the periodic empirical field under a random field `κ`:
`(κ °R_Δ)(A) = ∫ °R^σ_Δ(A) κ(dσ)`. It is the uniform average over `i ∈ Δ` of the push-forwards of
`κ` by `σ ↦ θ_{-i} σ^∘_Δ`, so it is again a random field, and a shift-invariant one
(`map_shift_empiricalFieldAverage`) since each `°R^σ_Δ` is. In Step 2 of the proof of the upper
bound (15.46) Georgii applies it to the conditioned Gibbs distribution `γ^C_{Δ|ω}`. -/
def empiricalFieldAverage (π : S → S) (Δ : Finset S) (κ : Measure (S → E)) : Measure (S → E) :=
  uniformAverage (fun i ↦ κ.map (periodicTranslate E π i)) Δ

/-- `(κ °R_Δ)(A) = |Δ|⁻¹ ∑_{i ∈ Δ} κ(θ_{-i} ·^∘_Δ ∈ A)`. -/
lemma empiricalFieldAverage_apply (π : S → S) (Δ : Finset S) (κ : Measure (S → E))
    {A : Set (S → E)} (hA : MeasurableSet A) :
    empiricalFieldAverage E π Δ κ A
      = (#Δ : ℝ≥0∞)⁻¹ * ∑ i ∈ Δ, κ (periodicTranslate E π i ⁻¹' A) := by
  rw [empiricalFieldAverage, uniformAverage_apply]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦
    Measure.map_apply (measurable_periodicTranslate π i) hA)

instance isProbabilityMeasure_empiricalFieldAverage (π : S → S) {Δ : Finset S} [NeZero (#Δ)]
    (κ : Measure (S → E)) [IsProbabilityMeasure κ] :
    IsProbabilityMeasure (empiricalFieldAverage E π Δ κ) :=
  isProbabilityMeasure_uniformAverage _
    (fun i ↦ Measure.isProbabilityMeasure_map (measurable_periodicTranslate π i).aemeasurable)
    (Finset.card_pos.1 (Nat.pos_of_ne_zero (NeZero.ne _)))

/-- `κ °R_Δ` is the `κ`-average of the periodic empirical fields, `(κ °R_Δ)(A) = ∫ °R^σ_Δ(A) κ(dσ)`
— the reading of the definition Georgii uses. -/
theorem empiricalFieldAverage_apply_eq_lintegral (π : S → S) (Δ : Finset S) (κ : Measure (S → E))
    {A : Set (S → E)} (hA : MeasurableSet A) :
    empiricalFieldAverage E π Δ κ A = ∫⁻ σ, periodicEmpiricalField E π Δ σ A ∂κ := by
  have hind : ∀ i, Measurable fun σ : S → E ↦ A.indicator (1 : (S → E) → ℝ≥0∞)
      (periodicTranslate E π i σ) :=
    fun i ↦ (measurable_one.indicator hA).comp (measurable_periodicTranslate π i)
  have hrhs : ∀ σ : S → E, periodicEmpiricalField E π Δ σ A
      = (#Δ : ℝ≥0∞)⁻¹ * ∑ i ∈ Δ, A.indicator 1 (periodicTranslate E π i σ) := fun σ ↦
    periodicEmpiricalField_apply π Δ σ hA
  rw [empiricalFieldAverage_apply π Δ κ hA, lintegral_congr hrhs,
    lintegral_const_mul _ (Finset.measurable_sum _ fun i _ ↦ hind i),
    lintegral_finsetSum _ fun i _ ↦ hind i]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [← lintegral_indicator_one (measurable_periodicTranslate π i hA)]
  exact lintegral_congr fun σ ↦ by
    by_cases h : periodicTranslate E π i σ ∈ A <;> simp [h, Set.mem_preimage]

/-- The integral of a bounded observable against `κ °R_Δ` is the `κ`-average of its periodic
empirical averages. -/
theorem integral_empiricalFieldAverage (π : S → S) (Δ : Finset S) (κ : Measure (S → E))
    [IsFiniteMeasure κ] {f : (S → E) → ℝ} (hfm : StronglyMeasurable f) {c : ℝ}
    (hc : ∀ η, |f η| ≤ c) :
    ∫ η, f η ∂(empiricalFieldAverage E π Δ κ)
      = (#Δ : ℝ)⁻¹ * ∑ i ∈ Δ, ∫ σ, f (periodicTranslate E π i σ) ∂κ := by
  have hint : ∀ i ∈ Δ, Integrable f (κ.map (periodicTranslate E π i)) := fun i _ ↦ by
    have : IsFiniteMeasure (κ.map (periodicTranslate E π i)) :=
      Measure.isFiniteMeasure_map κ (periodicTranslate E π i)
    exact Integrable.of_bound hfm.aestronglyMeasurable c
      (.of_forall fun η ↦ by rw [Real.norm_eq_abs]; exact hc η)
  rw [empiricalFieldAverage, integral_uniformAverage _ _ hint, smul_eq_mul]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦
    integral_map (measurable_periodicTranslate π i).aemeasurable hfm.aestronglyMeasurable)

/-- **`κ °R_Δ ∈ 𝓟_Θ`**: the `κ`-average of the shift-invariant periodic empirical fields is
shift invariant. -/
theorem map_shift_empiricalFieldAverage (hπ : Potential.IsTorusReduction G Δ π)
    (κ : Measure (S → E)) (j : S) :
    (empiricalFieldAverage E π Δ κ).map (shift E j).toFun = empiricalFieldAverage E π Δ κ := by
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.map_apply (shift E j).measurable_toFun hA,
    empiricalFieldAverage_apply_eq_lintegral π Δ κ ((shift E j).measurable_toFun hA),
    empiricalFieldAverage_apply_eq_lintegral π Δ κ hA]
  refine lintegral_congr fun σ ↦ ?_
  rw [← Measure.map_apply (shift E j).measurable_toFun hA,
    map_shift_periodicEmpiricalField hπ σ j]

theorem empiricalFieldAverage_mem_invariantFields (hπ : Potential.IsTorusReduction G Δ π)
    [NeZero (#Δ)] (κ : Measure (S → E)) [IsProbabilityMeasure κ] :
    empiricalFieldAverage E π Δ κ ∈ invariantFields (shiftGroup S E) :=
  mem_invariantFields_shiftGroup.2 ⟨inferInstance, fun j ↦
    ⟨(shift E j).measurable_toFun, map_shift_empiricalFieldAverage hπ κ j⟩⟩

end EmpiricalFieldAverage

/-! ### The independent-block field and the empirical field are asymptotically equal on `𝓛` -/

section BlockVsEmpirical

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E]
  {H : AddSubgroup S} {Λ : Finset S}


/-- The randomly shifted independent-block field `γ̃` of Proposition (15.52) may also be written as
the average over `i ∈ Λ` of the *backward* shifts `θ_{-i} γ̂` of the independent-block field: the
map `i ↦ tileRep(−i)` is an involution of the tile `Λ`, and `θ_{-i} γ̂ = θ_{tileRep(-i)} γ̂`
because `γ̂` is invariant under the shifts of the tiling subgroup. This is the form in which
`γ̃` is compared with the periodic empirical field, whose translates are also backward ones. -/
theorem integral_tileAverage_eq_inv_card_mul_sum
    (hCH : AddSubgroup.IsComplement (Λ : Set S) (H : Set S))
    (γ : Measure (Λ → E)) [IsProbabilityMeasure γ]
    {f : (S → E) → ℝ} (hfm : StronglyMeasurable f) {c : ℝ} (hc : ∀ η, |f η| ≤ c) :
    ∫ η, f η ∂(tileAverage hCH γ)
      = (#Λ : ℝ)⁻¹ * ∑ i ∈ Λ, ∫ ζ, f ((shift E (-i)).toFun ζ) ∂(tileProduct hCH γ) := by
  have hint : ∀ j : S, Integrable f ((tileProduct hCH γ).map (shift E j).toFun) := fun j ↦
    Integrable.of_bound hfm.aestronglyMeasurable c
      (.of_forall fun η ↦ by rw [Real.norm_eq_abs]; exact hc η)
  have hmapint : ∀ j : S, ∫ η, f η ∂((tileProduct hCH γ).map (shift E j).toFun)
      = ∫ ζ, f ((shift E j).toFun ζ) ∂(tileProduct hCH γ) := fun j ↦
    integral_map (shift E j).measurable_toFun.aemeasurable hfm.aestronglyMeasurable
  -- `i ↦ tileRep (−i)` is an involution of the tile
  have hinv : ∀ i ∈ Λ, (tileRep hCH (-(tileRep hCH (-i) : S)) : S) = i := by
    intro i hi
    have h1 : -(tileRep hCH (-i) : S) = i + (tileIdx hCH (-i) : S) := by
      have := coe_tileRep_add_coe_tileIdx hCH (-i)
      have h2 : (tileRep hCH (-i) : S) = -i - (tileIdx hCH (-i) : S) := by
        rw [eq_sub_iff_add_eq]; exact this
      rw [h2]; abel
    rw [h1, tileRep_add_of_mem hCH i (tileIdx hCH (-i)).2, coe_tileRep_of_mem hCH hi]
  rw [tileAverage, integral_uniformAverage _ _ fun j _ ↦ hint j, smul_eq_mul]
  refine congrArg _ (Finset.sum_nbij' (i := fun j ↦ (tileRep hCH (-j) : S))
    (j := fun i ↦ (tileRep hCH (-i) : S)) (fun j _ ↦ (tileRep hCH _).2)
    (fun i _ ↦ (tileRep hCH _).2) hinv hinv fun j hj ↦ ?_)
  rw [hmapint j, ← hmapint (-(tileRep hCH (-j) : S)),
    map_shift_tileProduct_eq_map_shift_tileRep hCH γ (-(tileRep hCH (-j) : S)),
    hinv j hj, hmapint j]

/-- The independent-block field `γ̂` built from the `Λ`-marginal of `κ` agrees with `κ` on the
cylinder σ-algebra `𝓕_Λ` of the tile, so the two integrate every `𝓕_Λ`-measurable observable
alike. -/
theorem integral_tileProduct_map_finsetRestrict
    (hCH : AddSubgroup.IsComplement (Λ : Set S) (H : Set S)) (κ : Measure (S → E))
    [IsProbabilityMeasure κ] {g : (S → E) → ℝ}
    (hg : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] g) :
    ∫ ζ, g ζ ∂(tileProduct hCH (κ.map Λ.restrict)) = ∫ σ, g σ ∂κ := by
  have hle := cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))
  have hgsm : StronglyMeasurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] g :=
    hg.stronglyMeasurable
  have htrim : (tileProduct hCH (κ.map Λ.restrict)).trim hle = κ.trim hle := by
    refine @Measure.ext _ (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)) _ _ fun A hA ↦ ?_
    rw [trim_measurableSet_eq hle hA, trim_measurableSet_eq hle hA]
    exact tileProduct_apply_of_measurableSet_cylinderEvents hCH κ hA
  have h1 : ∫ ζ, g ζ ∂(tileProduct hCH (κ.map Λ.restrict))
      = ∫ x, g x ∂((tileProduct hCH (κ.map Λ.restrict)).trim hle) := integral_trim hle hgsm
  have h2 : ∫ σ, g σ ∂κ = ∫ x, g x ∂(κ.trim hle) := integral_trim hle hgsm
  rw [h1, h2, htrim]

/-- **Georgii, Step 2 of the proof of (15.46): the randomly shifted independent-block field
`γ̄^C_{Λ|ω}` and the mean empirical field `γ^C_{Λ|ω} °R_Λ` are asymptotically equal in the topology
of local convergence.** For a `B`-local observable `f` bounded by `c`,
`|γ̄(f) − (κ °R_Λ)(f)| ≤ 2 c |T| / |Λ|` for any set `T` of sites containing all `i ∈ Λ` with
`B + i ⊄ Λ`; along cubes the right-hand side tends to `0`
(`MeasureTheory.GibbsMeasure.tendsto_card_filter_add_notMem_div_card`). Georgii states this as
"analogous to Remark (15.43)(1)".

The two averages are compared translate by translate. For a good `i` — one with `B + i ⊆ Λ` — the
observable `f ∘ θ_{-i}` is `𝓕_Λ`-measurable, so it does not distinguish `σ` from its periodic
continuation (Georgii Remark (15.43)(1), `apply_shift_periodicExtend_eq`), and it has the same
integral under `κ` and under the independent-block field, whose `𝓕_Λ`-marginal is that of `κ`
(`integral_tileProduct_map_finsetRestrict`). The remaining `|T|` translates contribute at most
`2c` each. -/
theorem abs_integral_tileAverage_sub_integral_empiricalFieldAverage_le
    {G : AddSubgroup S} {π : S → S} (hπ : Potential.IsTorusReduction G Λ π)
    (hCH : AddSubgroup.IsComplement (Λ : Set S) (H : Set S))
    (κ : Measure (S → E)) [IsProbabilityMeasure κ]
    {B : Set S} {f : (S → E) → ℝ} (hf : DependsOn f B) (hfm : StronglyMeasurable f)
    {c : ℝ} (hc : ∀ η, |f η| ≤ c) {T : Finset S} (hT : T ⊆ Λ)
    (hgood : ∀ i ∈ Λ, i ∉ T → ∀ n ∈ B, n + i ∈ Λ) :
    |(∫ η, f η ∂(tileAverage hCH (κ.map Λ.restrict)))
        - ∫ η, f η ∂(empiricalFieldAverage E π Λ κ)| ≤ 2 * c * #T / #Λ := by
  classical
  rcases Λ.eq_empty_or_nonempty with rfl | hΛ
  · simp [Finset.subset_empty.1 hT, tileAverage, empiricalFieldAverage, uniformAverage]
  have hcard : (0 : ℝ) < #Λ := by exact_mod_cast hΛ.card_pos
  -- the good translates contribute equally
  have hequal : ∀ i ∈ Λ, i ∉ T →
      (∫ ζ, f ((shift E (-i)).toFun ζ) ∂(tileProduct hCH (κ.map Λ.restrict)))
        = ∫ σ, f (periodicTranslate E π i σ) ∂κ := by
    intro i hi hiT
    have hgi : ∀ n ∈ B, n + i ∈ Λ := hgood i hi hiT
    have hdep : DependsOn (fun ζ : S → E ↦ f ((shift E (-i)).toFun ζ)) (Λ : Set S) := by
      intro x y hxy
      refine hf fun n hn ↦ ?_
      have hmem : n - -i ∈ (Λ : Set S) := by
        rw [sub_neg_eq_add]; exact_mod_cast hgi n hn
      simpa only [shift_toFun_apply] using hxy _ hmem
    have hmeas : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
        fun ζ : S → E ↦ f ((shift E (-i)).toFun ζ) :=
      (hfm.measurable.comp (shift E (-i)).measurable_toFun).cylinderEvents_of_dependsOn hdep
    rw [integral_tileProduct_map_finsetRestrict hCH κ hmeas]
    exact integral_congr_ae (.of_forall fun σ ↦
      (apply_shift_periodicExtend_eq hπ hf hgi σ).symm)
  -- bound each translate by `c`
  have hbdd : ∀ (ρ : Measure (S → E)) (_ : IsProbabilityMeasure ρ) (g : (S → E) → S → E),
      Measurable g → |∫ ζ, f (g ζ) ∂ρ| ≤ c := by
    intro ρ hρ g hgm
    have := hρ
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ζ, |f (g ζ)| ∂ρ ≤ ∫ _ζ, c ∂ρ :=
          integral_mono_of_nonneg (.of_forall fun _ ↦ abs_nonneg _) (integrable_const c)
            (.of_forall fun ζ ↦ hc _)
      _ = c := by simp
  have hsum : (∑ i ∈ Λ, ∫ ζ, f ((shift E (-i)).toFun ζ) ∂(tileProduct hCH (κ.map Λ.restrict)))
      - ∑ i ∈ Λ, ∫ σ, f (periodicTranslate E π i σ) ∂κ
      = ∑ i ∈ T, ((∫ ζ, f ((shift E (-i)).toFun ζ) ∂(tileProduct hCH (κ.map Λ.restrict)))
        - ∫ σ, f (periodicTranslate E π i σ) ∂κ) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_subset hT fun i hi hiT ↦ ?_).symm
    rw [hequal i hi hiT, sub_self]
  have hbound : |∑ i ∈ T, ((∫ ζ, f ((shift E (-i)).toFun ζ)
        ∂(tileProduct hCH (κ.map Λ.restrict)))
      - ∫ σ, f (periodicTranslate E π i σ) ∂κ)| ≤ 2 * c * #T := by
    calc |∑ i ∈ T, ((∫ ζ, f ((shift E (-i)).toFun ζ) ∂(tileProduct hCH (κ.map Λ.restrict)))
            - ∫ σ, f (periodicTranslate E π i σ) ∂κ)|
        ≤ ∑ i ∈ T, |(∫ ζ, f ((shift E (-i)).toFun ζ) ∂(tileProduct hCH (κ.map Λ.restrict)))
            - ∫ σ, f (periodicTranslate E π i σ) ∂κ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ T, 2 * c := by
          refine Finset.sum_le_sum fun i _ ↦ (abs_sub _ _).trans ?_
          have h1 := hbdd (tileProduct hCH (κ.map Λ.restrict)) inferInstance
            (fun ζ ↦ (shift E (-i)).toFun ζ) (shift E (-i)).measurable_toFun
          have h2 := hbdd κ inferInstance (periodicTranslate E π i)
            (measurable_periodicTranslate π i)
          linarith
      _ = 2 * c * #T := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [integral_tileAverage_eq_inv_card_mul_sum hCH _ hfm hc,
    integral_empiricalFieldAverage π Λ κ hfm hc, ← mul_sub, hsum, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hcard.le), div_eq_inv_mul _ (#Λ : ℝ)]
  exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hcard.le)

end BlockVsEmpirical

/-! ### Step 1: the exponential Chebyshev identity -/

section Step1

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ : Potential S E}
  [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
  (ν : Measure E) [IsProbabilityMeasure ν]

/-- **Step 1 of Georgii's proof of the upper bound (15.46).** For a `𝓕_Λ`-event `A` of positive
probability under the finite-volume Gibbs distribution `γ^Φ_Λ(·|ω)`, the conditional distribution
`γ^C_{Λ|ω} = γ^Φ_Λ(·|ω)(· | A)` satisfies

`−log γ^Φ_Λ(A|ω) = 𝓗_Λ(γ^C_{Λ|ω} | λ^S) + γ^C_{Λ|ω}(H^Φ_Λ) + log Z^Φ_Λ(ω)`,

which in Georgii's sign convention `𝓗_Λ(·) = −𝓗_Λ(· | λ^S)` is
`−|Λ|⁻¹ log γ_{Λ|ω}(A) = |Λ|⁻¹ γ^C_{Λ|ω}(H^Φ_Λ) − |Λ|⁻¹ 𝓗_Λ(γ^C_{Λ|ω}) + |Λ|⁻¹ log Z^Φ_Λ(ω)`.

It is the combination of two facts: conditioning on `A` costs exactly `−log γ_{Λ|ω}(A)` in
relative entropy (`InformationTheory.klDiv_trim_cond_self`, which uses only that `A ∈ 𝓕_Λ`), and
Georgii (15.34), `𝓗_Λ(μ | γ^Φ_Λ(·|ω)) = −𝓗_Λ(μ) + μ(H^Φ_Λ) + log Z^Φ_Λ(ω)`
(`Potential.relativeEntropyIn_gibbsSpecification_eq`). -/
theorem neg_log_gibbsSpecification_eq (Λ : Finset S) (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A)
    (hpos : Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω A ≠ 0) :
    ((ENNReal.ofReal (-Real.log
        ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω).real A)) : ℝ≥0∞)
        : EReal)
      = ((relativeEntropyIn (Λ : Set S)
            ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)[|A])
            (Measure.infinitePi fun _ : S ↦ ν) : ℝ≥0∞) : EReal)
        + (((∫ σ, Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i)
              ∂((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)[|A]))
            + Φ.logZ ν Λ ω : ℝ) : EReal) := by
  set γ := Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω with hγdef
  have hγprob : IsProbabilityMeasure γ := inferInstance
  have hκ : IsProbabilityMeasure (γ[|A]) := cond_isProbabilityMeasure hpos
  have hle := cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))
  have hcond : relativeEntropyIn (Λ : Set S) (γ[|A]) γ
      = ENNReal.ofReal (-Real.log (γ.real A)) := klDiv_trim_cond_self hle hA hpos
  have h1534 := Potential.relativeEntropyIn_gibbsSpecification_eq (Φ := Φ) ν
    (μ := γ[|A]) Λ ω
  rw [hcond] at h1534
  rw [h1534, entropyIn, neg_neg]

end Step1

/-! ### The specific energy and the entropy of the two auxiliary fields -/

section Energy

variable {S E : Type*} [Countable S] [AddCommGroup S] [MeasurableSpace E] {Φ : Potential S E}
  [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
  {G : AddSubgroup S} {Λ : Finset S} {π : S → S}

omit [Countable S] [MeasurableSpace E] in
/-- The periodic continuation of a configuration only sees the sites of the box, so it does not
see the boundary condition: `(σ_Λ ω_{S∖Λ})^∘_Λ = σ^∘_Λ`. -/
theorem periodicExtend_juxt (hπ : Potential.IsTorusReduction G Λ π) (ω σ : S → E) :
    Potential.periodicExtend π (juxt (Λ : Set S) ω fun i ↦ σ i)
      = Potential.periodicExtend π σ := by
  funext n
  simp only [Potential.periodicExtend]
  exact juxt_apply_of_mem (Λ := (Λ : Set S)) (by exact_mod_cast hπ.mapsTo n) _

/-- **The specific energy of `κ °R_Λ` is the `κ`-average of the specific energies of the periodic
empirical fields**, `⟨κ °R_Λ, Φ⟩ = ∫ ⟨°R^σ_Λ, Φ⟩ κ(dσ)`. This is the identity behind Step 1 of
Georgii's proof: it turns the average Hamiltonian into a specific energy. -/
theorem specificEnergy_empiricalFieldAverage (hΦ : Φ.IsShiftInvariant) (π : S → S) (Λ : Finset S)
    (κ : Measure (S → E)) [IsProbabilityMeasure κ] :
    Φ.specificEnergy (empiricalFieldAverage E π Λ κ)
      = ∫ σ, Φ.specificEnergy (periodicEmpiricalField E π Λ σ) ∂κ := by
  have hbdd : ∀ η, |Φ.energyDensity η| ≤ (Φ.normAt 0).toReal := fun η ↦
    Potential.abs_siteEnergy_le 0 η
  have hint : ∀ i : S, Integrable (fun σ : S → E ↦ Φ.energyDensity (periodicTranslate E π i σ))
      κ := fun i ↦
    Integrable.of_bound (((Φ.measurable_siteEnergy 0).comp
      (measurable_periodicTranslate π i)).aestronglyMeasurable) _
      (.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hbdd _)
  rw [Potential.specificEnergy,
    integral_empiricalFieldAverage π Λ κ (Φ.measurable_siteEnergy 0).stronglyMeasurable hbdd]
  have hpt : ∀ σ : S → E, Φ.specificEnergy (periodicEmpiricalField E π Λ σ)
      = (#Λ : ℝ)⁻¹ * ∑ i ∈ Λ, Φ.energyDensity (periodicTranslate E π i σ) := by
    intro σ
    rw [specificEnergy_periodicEmpiricalField hΦ π Λ σ]
    exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ hΦ.siteEnergy_eq i _)
  simp only [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint i]

/-- The specific energy of the periodic empirical field, as a spatial average of the energy
density along the translates of the periodic continuation. -/
theorem specificEnergy_periodicEmpiricalField_eq (hΦ : Φ.IsShiftInvariant) (π : S → S)
    (Λ : Finset S) (σ : S → E) :
    Φ.specificEnergy (periodicEmpiricalField E π Λ σ)
      = (#Λ : ℝ)⁻¹ * ∑ i ∈ Λ, Φ.energyDensity (periodicTranslate E π i σ) := by
  rw [specificEnergy_periodicEmpiricalField hΦ π Λ σ]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ hΦ.siteEnergy_eq i _)

/-- **Georgii's estimate (15.25) integrated against the conditioned Gibbs distribution**, the form
Step 1 of the proof of (15.46) uses: `|κ(H^Φ_Λ) − |Λ| ⟨κ °R_Λ, Φ⟩| ≤ 3 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`
for any random field `κ` and any boundary condition `ω`. Pointwise this is
`abs_hamiltonian_sub_card_mul_specificEnergy_periodicEmpiricalField_le` applied at the
configuration `σ_Λ ω_{S∖Λ}`, whose periodic empirical field is that of `σ`
(`periodicExtend_juxt`). -/
theorem abs_integral_hamiltonian_juxt_sub_card_mul_specificEnergy_le
    (hΦ : Φ.IsShiftInvariant) (hπ : Potential.IsTorusReduction G Λ π) (hΛ : Λ.Nonempty)
    (ω : S → E) (κ : Measure (S → E)) [IsProbabilityMeasure κ] :
    |(∫ σ, Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) ∂κ)
        - (#Λ : ℝ) * Φ.specificEnergy (empiricalFieldAverage E π Λ κ)| ≤ 3 * Φ.tail Λ Λ := by
  have hcard : (0 : ℝ) < #Λ := by exact_mod_cast hΛ.card_pos
  have hbdd : ∀ η, |Φ.energyDensity η| ≤ (Φ.normAt 0).toReal := fun η ↦
    Potential.abs_siteEnergy_le 0 η
  have hmeas : Measurable fun σ : S → E ↦
      (#Λ : ℝ) * Φ.specificEnergy (periodicEmpiricalField E π Λ σ) := by
    simp only [specificEnergy_periodicEmpiricalField_eq hΦ π Λ]
    have hsum : Measurable fun σ : S → E ↦
        ∑ i ∈ Λ, Φ.energyDensity (periodicTranslate E π i σ) :=
      Finset.measurable_sum Λ fun i _ ↦
        (Φ.measurable_siteEnergy 0).comp (measurable_periodicTranslate π i)
    exact (hsum.const_mul _).const_mul _
  have hbdd2 : ∀ σ : S → E,
      |(#Λ : ℝ) * Φ.specificEnergy (periodicEmpiricalField E π Λ σ)|
        ≤ (#Λ : ℝ) * (Φ.normAt 0).toReal := by
    intro σ
    rw [abs_mul, abs_of_nonneg hcard.le]
    refine mul_le_mul_of_nonneg_left ?_ hcard.le
    rw [Potential.specificEnergy]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ η, |Φ.energyDensity η| ∂(periodicEmpiricalField E π Λ σ)
        ≤ ∫ _η, (Φ.normAt 0).toReal ∂(periodicEmpiricalField E π Λ σ) := by
          have : NeZero (#Λ) := ⟨hΛ.card_pos.ne'⟩
          exact integral_mono_of_nonneg (.of_forall fun _ ↦ abs_nonneg _) (integrable_const _)
            (.of_forall fun η ↦ hbdd η)
      _ = (Φ.normAt 0).toReal := by
          have : NeZero (#Λ) := ⟨hΛ.card_pos.ne'⟩
          have hp : IsProbabilityMeasure (periodicEmpiricalField E π Λ σ) := inferInstance
          simp
  have hint2 : Integrable (fun σ : S → E ↦
      (#Λ : ℝ) * Φ.specificEnergy (periodicEmpiricalField E π Λ σ)) κ :=
    Integrable.of_bound hmeas.aestronglyMeasurable _
      (.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hbdd2 σ)
  have hpt : ∀ σ : S → E, |Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i)
      - (#Λ : ℝ) * Φ.specificEnergy (periodicEmpiricalField E π Λ σ)| ≤ 3 * Φ.tail Λ Λ := by
    intro σ
    have h := abs_hamiltonian_sub_card_mul_specificEnergy_periodicEmpiricalField_le hΦ hπ hΛ
      (juxt (Λ : Set S) ω fun i ↦ σ i)
    have hR : periodicEmpiricalField E π Λ (juxt (Λ : Set S) ω fun i ↦ σ i)
        = periodicEmpiricalField E π Λ σ := by
      rw [periodicEmpiricalField, periodicEmpiricalField, periodicExtend_juxt hπ ω σ]
    rwa [hR] at h
  have hcE : (#Λ : ℝ) * Φ.specificEnergy (empiricalFieldAverage E π Λ κ)
      = ∫ σ, (#Λ : ℝ) * Φ.specificEnergy (periodicEmpiricalField E π Λ σ) ∂κ := by
    rw [specificEnergy_empiricalFieldAverage hΦ π Λ κ, integral_const_mul]
  rw [hcE, ← integral_sub (Potential.integrable_hamiltonian_juxt Λ ω κ) hint2]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ σ, |Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i)
          - (#Λ : ℝ) * Φ.specificEnergy (periodicEmpiricalField E π Λ σ)| ∂κ
      ≤ ∫ _σ, 3 * Φ.tail Λ Λ ∂κ :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ abs_nonneg _) (integrable_const _)
          (.of_forall hpt)
    _ = 3 * Φ.tail Λ Λ := by simp

end Energy

/-! ### Georgii's "basic observation": the mean empirical field lies in `cx̄ C` -/

section ConvexHull

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E]
  {G : AddSubgroup S} {Λ : Finset S} {π : S → S}

/-- `°R^σ_Λ` depends on `σ` only through `σ_Λ`: the periodic continuation only reads the sites
of the box. -/
theorem periodicEmpiricalField_congr (hπ : Potential.IsTorusReduction G Λ π) {σ τ : S → E}
    (h : ∀ i ∈ Λ, σ i = τ i) :
    periodicEmpiricalField E π Λ σ = periodicEmpiricalField E π Λ τ := by
  have hext : Potential.periodicExtend π σ = Potential.periodicExtend π τ :=
    funext fun n ↦ h _ (hπ.mapsTo n)
  rw [periodicEmpiricalField, periodicEmpiricalField, hext]

variable [MeasurableSingletonClass E]

omit [AddCommGroup S] in
/-- The fibres of `σ ↦ σ_Λ` are measurable. -/
theorem measurableSet_finsetRestrict_preimage_singleton (Λ : Finset S) (x : Λ → E) :
    MeasurableSet ((Λ.restrict : (S → E) → Λ → E) ⁻¹' {x}) := by
  have hset : (Λ.restrict : (S → E) → Λ → E) ⁻¹' {x}
      = ⋂ i : Λ, {σ : S → E | σ (i : S) = x i} := by
    ext σ
    simp [Set.mem_preimage, funext_iff, Finset.restrict]
  rw [hset]
  exact MeasurableSet.iInter fun i ↦ measurable_pi_apply (i : S) (measurableSet_singleton _)

variable [Finite E]

omit [Finite E] in
/-- **Over a finite state space the mean empirical field is a finite convex combination of
periodic empirical fields.** The fibres of `σ ↦ σ_Λ` are finitely many, `°R^σ_Λ` is constant on
each of them (`periodicEmpiricalField_congr`), and the weights are their `κ`-masses. -/
theorem empiricalFieldAverage_apply_eq_sum (hπ : Potential.IsTorusReduction G Λ π)
    (κ : Measure (S → E)) [IsProbabilityMeasure κ] (ω₀ : S → E) [Fintype (Λ → E)]
    {A : Set (S → E)} (hA : MeasurableSet A) :
    empiricalFieldAverage E π Λ κ A
      = ∑ x : Λ → E, (κ ((Λ.restrict : (S → E) → Λ → E) ⁻¹' {x})) *
          periodicEmpiricalField E π Λ (juxt (Λ : Set S) ω₀ fun i ↦ x i) A := by
  classical
  have hrep : ∀ (x : Λ → E) (i : S) (hi : i ∈ Λ),
      (juxt (Λ : Set S) ω₀ fun j ↦ x j) i = x ⟨i, hi⟩ := fun x i hi ↦
    juxt_apply_of_mem (Λ := (Λ : Set S)) (by exact_mod_cast hi) _
  have hptwise : ∀ σ : S → E, periodicEmpiricalField E π Λ σ A
      = ∑ x : Λ → E, ((Λ.restrict : (S → E) → Λ → E) ⁻¹' {x}).indicator
          (fun _ ↦ periodicEmpiricalField E π Λ (juxt (Λ : Set S) ω₀ fun i ↦ x i) A) σ := by
    intro σ
    rw [Finset.sum_eq_single (Λ.restrict σ)]
    · rw [Set.indicator_of_mem (show σ ∈ (Λ.restrict : (S → E) → Λ → E) ⁻¹' {Λ.restrict σ} from
        rfl)]
      exact congrFun (congrArg _ (periodicEmpiricalField_congr hπ
        fun i hi ↦ (hrep (Λ.restrict σ) i hi).symm)) A
    · intro x _ hx
      have hnot : σ ∉ (Λ.restrict : (S → E) → Λ → E) ⁻¹' {x} :=
        fun hmem ↦ hx (Set.mem_singleton_iff.1 hmem).symm
      exact Set.indicator_of_notMem hnot _
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [empiricalFieldAverage_apply_eq_lintegral π Λ κ hA, lintegral_congr hptwise,
    lintegral_finsetSum _ fun x _ ↦
      ((measurable_const).indicator (measurableSet_finsetRestrict_preimage_singleton Λ x))]
  exact Finset.sum_congr rfl fun x _ ↦ by
    rw [lintegral_indicator_const (measurableSet_finsetRestrict_preimage_singleton Λ x),
      mul_comm]

/-- **Georgii's "basic observation" in Step 2 of the proof of (15.46).** If the random field `κ`
is carried by the event `{°R_Λ ∈ C}` then the mean empirical field `κ °R_Λ` belongs to Georgii's
`cx̄ C`: its evaluation on the local events is a *finite* convex combination of evaluations of
elements of `C`.

Georgii approximates `κ °R_Λ` by convex combinations read off from a partition of `[0, 1]^k` into
small cells. Over a finite state space no approximation is needed: `°R^σ_Λ` depends on `σ` only
through the finitely many values of `σ_Λ`, so decomposing `κ` along the fibres of `σ ↦ σ_Λ`
writes `κ °R_Λ` as an *exact* finite convex combination of periodic empirical fields, each of
which lies in `C` because the fibre it comes from meets `{°R_Λ ∈ C}`. -/
theorem evalLocalEvents_empiricalFieldAverage_mem_convexHull
    (hπ : Potential.IsTorusReduction G Λ π) (hΛ : Λ.Nonempty)
    (κ : Measure (S → E)) [IsProbabilityMeasure κ]
    {C : Set (WithLocalConvergence S E)}
    (hκ : κ {σ | periodicEmpiricalFieldL π hΛ σ ∈ C}ᶜ = 0) :
    haveI : NeZero (#Λ) := ⟨hΛ.card_pos.ne'⟩
    evalLocalEvents S E (WithSetwiseTopology.ofMeasure
        ⟨empiricalFieldAverage E π Λ κ, isProbabilityMeasure_empiricalFieldAverage π κ⟩)
      ∈ convexHull ℝ (evalLocalEvents S E '' C) := by
  classical
  have : NeZero (#Λ) := ⟨hΛ.card_pos.ne'⟩
  have : Fintype (Λ → E) := Fintype.ofFinite _
  obtain ⟨ω₀⟩ : Nonempty (S → E) := Measure.nonempty_of_neZero κ
  set rep : (Λ → E) → (S → E) := fun x ↦ juxt (Λ : Set S) ω₀ fun i ↦ x i with hrepdef
  have hrep : ∀ (x : Λ → E) (i : S) (hi : i ∈ Λ), rep x i = x ⟨i, hi⟩ := fun x i hi ↦
    juxt_apply_of_mem (Λ := (Λ : Set S)) (by exact_mod_cast hi) _
  set w : (Λ → E) → ℝ≥0∞ := fun x ↦ κ ((Λ.restrict : (S → E) → Λ → E) ⁻¹' {x}) with hwdef
  have hwtop : ∀ x, w x ≠ ⊤ := fun x ↦ measure_ne_top κ _
  have hwsum : ∑ x : Λ → E, w x = 1 := by
    have h := sum_measure_preimage_singleton (μ := κ) (f := (Λ.restrict : (S → E) → Λ → E))
      Finset.univ fun x _ ↦ measurableSet_finsetRestrict_preimage_singleton Λ x
    rw [hwdef]
    simpa using h
  set T : Finset (Λ → E) := Finset.univ.filter fun x ↦ w x ≠ 0 with hTdef
  have hTsub : T ⊆ Finset.univ := Finset.filter_subset _ _
  have hTzero : ∀ x ∈ (Finset.univ : Finset (Λ → E)), x ∉ T → w x = 0 := by
    intro x _ hx
    by_contra h
    exact hx (Finset.mem_filter.2 ⟨Finset.mem_univ x, h⟩)
  -- the weights sum to one
  have hTsum : ∑ x ∈ T, (w x).toReal = 1 := by
    rw [Finset.sum_subset hTsub fun x hx hxT ↦ by rw [hTzero x hx hxT, ENNReal.toReal_zero],
      ← ENNReal.toReal_sum fun x _ ↦ hwtop x, hwsum, ENNReal.toReal_one]
  -- the evaluation is the corresponding convex combination
  have heval : evalLocalEvents S E (WithSetwiseTopology.ofMeasure
        ⟨empiricalFieldAverage E π Λ κ, isProbabilityMeasure_empiricalFieldAverage π κ⟩)
      = ∑ x ∈ T, (w x).toReal • evalLocalEvents S E (periodicEmpiricalFieldL π hΛ (rep x)) := by
    funext A
    have hAm : MeasurableSet (A : Set (S → E)) := MeasurableSet.of_mem_measurableCylinders A.2
    have hsum := empiricalFieldAverage_apply_eq_sum hπ κ ω₀ (A := (A : Set (S → E))) hAm
    have hL : evalLocalEvents S E (WithSetwiseTopology.ofMeasure
          ⟨empiricalFieldAverage E π Λ κ, isProbabilityMeasure_empiricalFieldAverage π κ⟩) A
        = ∑ x : Λ → E, (w x).toReal
            * (periodicEmpiricalField E π Λ (rep x)).real (A : Set (S → E)) := by
      change (empiricalFieldAverage E π Λ κ).real (A : Set (S → E)) = _
      rw [measureReal_def, hsum, ENNReal.toReal_sum fun x _ ↦
        ENNReal.mul_ne_top (hwtop x) (measure_ne_top _ _)]
      exact Finset.sum_congr rfl fun x _ ↦ by rw [ENNReal.toReal_mul]; rfl
    have hR : (∑ x ∈ T, (w x).toReal • evalLocalEvents S E
          (periodicEmpiricalFieldL π hΛ (rep x))) A
        = ∑ x ∈ T, (w x).toReal
            * (periodicEmpiricalField E π Λ (rep x)).real (A : Set (S → E)) := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ ↦ rfl
    rw [hL, hR, Finset.sum_subset hTsub fun x hx hxT ↦ by
      rw [hTzero x hx hxT, ENNReal.toReal_zero, zero_mul]]
  -- each surviving periodic empirical field lies in `C`
  have hmem : ∀ x ∈ T,
      evalLocalEvents S E (periodicEmpiricalFieldL π hΛ (rep x))
        ∈ evalLocalEvents S E '' C := by
    intro x hx
    have hw : w x ≠ 0 := (Finset.mem_filter.1 hx).2
    have hne : ((Λ.restrict : (S → E) → Λ → E) ⁻¹' {x}
        ∩ {σ | periodicEmpiricalFieldL π hΛ σ ∈ C}).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hempty
      refine hw (measure_mono_null ?_ hκ)
      intro σ hσ
      exact fun hσC ↦ (Set.eq_empty_iff_forall_notMem.1 hempty σ) ⟨hσ, hσC⟩
    obtain ⟨σ, hσx, hσC⟩ := hne
    have hagree : ∀ i ∈ Λ, rep x i = σ i := fun i hi ↦ by
      rw [hrep x i hi]
      exact congrFun hσx.symm ⟨i, hi⟩
    have heq : periodicEmpiricalFieldL π hΛ (rep x) = periodicEmpiricalFieldL π hΛ σ := by
      unfold periodicEmpiricalFieldL
      congr 1
      exact Subtype.ext (periodicEmpiricalField_congr hπ hagree)
    exact ⟨periodicEmpiricalFieldL π hΛ σ, hσC, by rw [← heq]⟩
  rw [heval]
  exact (convex_convexHull ℝ _).sum_mem (fun x _ ↦ ENNReal.toReal_nonneg) hTsum
    fun x hx ↦ subset_convexHull ℝ _ (hmem x hx)

end ConvexHull

/-! ### The event `{°R_Λ ∈ C}` is a `𝓕_Λ`-event -/

section Event

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E] [Finite E] [Nonempty E]
  [MeasurableSingletonClass E] {G : AddSubgroup S} {Λ : Finset S} {π : S → S}

/-- **Over a finite state space `{°R_Λ ∈ C}` is a cylinder event of the volume `Λ`, for every set
`C` of random fields whatsoever.** The map `σ ↦ °R^σ_Λ` factors through `σ_Λ`
(`periodicEmpiricalField_congr`), whose range is the *finite* set `E^Λ`, all of whose subsets are
measurable. This is what makes `γ^Φ_Λ(°R_Λ ∈ C | ω)` meaningful with no measurability assumption
on `C`, and it is where the finiteness of the state space first enters the upper bound. -/
theorem measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem
    (hπ : Potential.IsTorusReduction G Λ π) (hΛ : Λ.Nonempty)
    (C : Set (WithLocalConvergence S E)) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      {σ | periodicEmpiricalFieldL π hΛ σ ∈ C} := by
  classical
  have : NeZero (#Λ) := ⟨hΛ.card_pos.ne'⟩
  have : Fintype (Λ → E) := Fintype.ofFinite _
  obtain ⟨e₀⟩ := ‹Nonempty E›
  set ω₀ : S → E := fun _ ↦ e₀ with hω₀
  set rep : (Λ → E) → (S → E) := fun x ↦ juxt (Λ : Set S) ω₀ fun i ↦ x i with hrepdef
  have hrep : ∀ (x : Λ → E) (i : S) (hi : i ∈ Λ), rep x i = x ⟨i, hi⟩ := fun x i hi ↦
    juxt_apply_of_mem (Λ := (Λ : Set S)) (by exact_mod_cast hi) _
  have hfactor : ∀ σ : S → E,
      periodicEmpiricalFieldL π hΛ (rep (Λ.restrict σ)) = periodicEmpiricalFieldL π hΛ σ := by
    intro σ
    unfold periodicEmpiricalFieldL
    congr 1
    exact Subtype.ext (periodicEmpiricalField_congr hπ
      fun i hi ↦ hrep (Λ.restrict σ) i hi)
  have hset : {σ : S → E | periodicEmpiricalFieldL π hΛ σ ∈ C}
      = (Λ.restrict : (S → E) → Λ → E) ⁻¹' {x | periodicEmpiricalFieldL π hΛ (rep x) ∈ C} := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hfactor σ]
  rw [hset, cylinderEvents_eq_comap_finsetRestrict]
  exact ⟨_, (Set.toFinite _).measurableSet, rfl⟩

end Event

/-! ### Proposition (15.52) for the block measure of Step 2 -/

section Block1552

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  (ν : Measure E) [IsProbabilityMeasure ν]

/-- **Georgii Proposition (15.52) in the form Step 2 of the proof of (15.46) uses it.** The
randomly shifted independent-block field built from the `Λ`-marginal of a random field `κ`, for
the tiling of `ℤ^d` by the translates of the box `Λ = ∏_k [a_k, a_k + s_k]`, has specific entropy
`𝓀(γ̄) = |Λ|⁻¹ 𝓗_Λ(κ)`, i.e. `−|Λ|⁻¹ 𝓗_Λ(κ | λ^S)` in the sign convention of this library. -/
theorem specificEntropy_tileAverage_map_finsetRestrict (a : ι → ℤ) (s : ι → ℕ)
    (κ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure κ] :
    specificEntropy ν (tileAverage (isComplement_Icc a s)
        (κ.map (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
      = -((relativeEntropyIn ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ)) κ
            (Measure.infinitePi fun _ ↦ ν) : ℝ≥0∞) : EReal)
          / ((#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℕ) : EReal) := by
  rw [specificEntropy_tileAverage_Icc ν a s, card_Icc_add, relativeEntropyIn_coe_finset,
    Measure.infinitePi_map_restrict]

/-- **Georgii's Step 2 in the form the limit argument uses it.** The excess free energy of the
randomly shifted independent-block field built from the `Λ`-marginal of `κ` is
`𝓀(γ̄|Φ) = P(Φ) + ⟨γ̄, Φ⟩ + |Λ|⁻¹ 𝓗_Λ(κ | λ^S)`, whenever that relative entropy is finite. It is
Proposition (15.52) (`specificEntropy_tileAverage_map_finsetRestrict`) read through the definition
`𝓀(μ|Φ) = P(Φ) + ⟨μ, Φ⟩ − 𝓀(μ)`. -/
theorem specificRelativeEntropy_tileAverage_map_finsetRestrict
    {Φ : Potential (ι → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (a : ι → ℤ) (s : ι → ℕ) (κ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure κ]
    (hfin : relativeEntropyIn ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ)) κ
        (Measure.infinitePi fun _ ↦ ν) ≠ ⊤) :
    Φ.specificRelativeEntropy ν (tileAverage (isComplement_Icc a s)
        (κ.map (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
      = ((Φ.pressure ν
          + Φ.specificEnergy (tileAverage (isComplement_Icc a s)
              (κ.map (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
          + (relativeEntropyIn ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ)) κ
              (Measure.infinitePi fun _ ↦ ν)).toReal
            / (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ) : ℝ) : EReal) := by
  have hk : specificEntropy ν (tileAverage (isComplement_Icc a s)
        (κ.map (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
      = ((-((relativeEntropyIn
            ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ)) κ
            (Measure.infinitePi fun _ ↦ ν)).toReal
          / (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ)) : ℝ) : EReal) := by
    rw [specificEntropy_tileAverage_map_finsetRestrict ν a s κ,
      ← EReal.coe_ennreal_toReal hfin, ← EReal.coe_natCast, ← EReal.coe_neg, ← EReal.coe_div,
      neg_div]
  rw [Potential.specificRelativeEntropy, hk, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
  ring

end Block1552

/-! ### Steps 1 and 2 combined in a single volume -/

section Step2

variable {S E : Type*} [Countable S] [AddCommGroup S] [MeasurableSpace E] {Φ : Potential S E}
  [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
  (ν : Measure E) [IsProbabilityMeasure ν]
  {G : AddSubgroup S} {Λ : Finset S} {π : S → S}

/-- **Steps 1 and 2 of Georgii's proof of the upper bound (15.46), before the tiling.** For a
`𝓕_Λ`-event `A` of positive probability under `γ^Φ_Λ(·|ω)` and the conditional distribution
`γ^C_{Λ|ω} = γ^Φ_Λ(·|ω)(· | A)`, the relative entropy `𝓗_Λ(γ^C_{Λ|ω} | λ^S)` is *finite* and

`𝓗_Λ(γ^C_{Λ|ω} | λ^S) + |Λ| ⟨γ^C_{Λ|ω} °R_Λ, Φ⟩ + log Z^Φ_Λ(ω)
    ≤ −log γ^Φ_Λ(A|ω) + 3 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`.

This is Georgii's identity of Step 1 (`neg_log_gibbsSpecification_eq`) together with the estimate
(15.25) of the energy (`abs_integral_hamiltonian_juxt_sub_card_mul_specificEnergy_le`); the
finiteness is forced by the identity, since all the other terms are real. -/
theorem relativeEntropyIn_cond_gibbsSpecification_ne_top_and_le
    (hΦ : Φ.IsShiftInvariant) (hπ : Potential.IsTorusReduction G Λ π) (hΛ : Λ.Nonempty)
    (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A)
    (hpos : Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω A ≠ 0) :
    relativeEntropyIn (Λ : Set S)
        ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)[|A])
        (Measure.infinitePi fun _ : S ↦ ν) ≠ ⊤ ∧
      (relativeEntropyIn (Λ : Set S)
          ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)[|A])
          (Measure.infinitePi fun _ : S ↦ ν)).toReal
        + (#Λ : ℝ) * Φ.specificEnergy (empiricalFieldAverage E π Λ
            ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)[|A]))
        + Φ.logZ ν Λ ω
        ≤ -Real.log ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω).real A)
          + 3 * Φ.tail Λ Λ := by
  have hγprob : IsProbabilityMeasure
      (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω) := inferInstance
  have hκprob : IsProbabilityMeasure
      ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)[|A]) :=
    cond_isProbabilityMeasure hpos
  have hstep1 := neg_log_gibbsSpecification_eq ν Λ ω hA hpos
  have hApos : 0 < (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω).real A := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hpos (measure_ne_top _ _)
  have hq0 : 0 ≤ -Real.log
      ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω).real A) := by
    rw [neg_nonneg]
    exact Real.log_nonpos hApos.le measureReal_le_one
  rw [EReal.coe_ennreal_ofReal, max_eq_left hq0] at hstep1
  have hRtop : relativeEntropyIn (Λ : Set S)
      ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)[|A])
      (Measure.infinitePi fun _ : S ↦ ν) ≠ ⊤ := by
    intro h
    rw [h, EReal.coe_ennreal_top, EReal.top_add_coe] at hstep1
    exact EReal.coe_ne_top _ hstep1
  refine ⟨hRtop, ?_⟩
  rw [← EReal.coe_ennreal_toReal hRtop, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hstep1
  have henergy := abs_integral_hamiltonian_juxt_sub_card_mul_specificEnergy_le hΦ hπ hΛ ω
    ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)[|A])
  have h1 := (abs_le.1 henergy).1
  linarith

end Step2

/-! ### Steps 1 and 2 assembled for a box of `ℤ^d` -/

section Assembled

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  (ν : Measure E) [IsProbabilityMeasure ν]

/-- **Steps 1 and 2 of Georgii's proof of the upper bound (15.46), assembled in one volume.**
For a box `Λ = ∏_k [a_k, a_k + s_k]` of `ℤ^d` with a torus reduction `π`, a boundary condition `ω`
and a `𝓕_Λ`-event `A` of positive probability, the excess free energy of the randomly shifted
independent-block field `γ̄^C_{Λ|ω}` built from the conditional distribution
`γ^C_{Λ|ω} = γ^Φ_Λ(·|ω)(· | A)` obeys

`𝓀(γ̄^C_{Λ|ω}|Φ) ≤ −|Λ|⁻¹ log γ^Φ_Λ(A|ω) + (P(Φ) − |Λ|⁻¹ log Z^Φ_Λ(ω))
                  + (⟨γ̄^C_{Λ|ω}, Φ⟩ − ⟨γ^C_{Λ|ω} °R_Λ, Φ⟩) + 3 |Λ|⁻¹ ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖.`

The three correction terms vanish in the infinite-volume limit: the second by Theorem (15.30)(a)
uniformly in `ω`, the fourth by the estimate (15.25), and the third along any subsequence in which
the two auxiliary fields converge, because they have the same limit points
(`abs_integral_tileAverage_sub_integral_empiricalFieldAverage_le`) and `⟨·, Φ⟩` is continuous. -/
theorem specificRelativeEntropy_tileAverage_cond_le
    {Φ : Potential (ι → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant) (a : ι → ℤ) (s : ι → ℕ)
    {G : AddSubgroup (ι → ℤ)} {π : (ι → ℤ) → (ι → ℤ)}
    (hπ : Potential.IsTorusReduction G (Finset.Icc a fun k ↦ a k + s k) π)
    (ω : (ι → ℤ) → E) {A : Set ((ι → ℤ) → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
      ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ))] A)
    (hpos : Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
      (Finset.Icc a fun k ↦ a k + s k) ω A ≠ 0) :
    Φ.specificRelativeEntropy ν (tileAverage (isComplement_Icc a s)
        (((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
            (Finset.Icc a fun k ↦ a k + s k) ω)[|A]).map
          (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
      ≤ ((-Real.log ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
              (Finset.Icc a fun k ↦ a k + s k) ω).real A)
            / (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ)
          + (Φ.pressure ν - Φ.logZ ν (Finset.Icc a fun k ↦ a k + s k) ω
              / (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ))
          + (Φ.specificEnergy (tileAverage (isComplement_Icc a s)
                (((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
                    (Finset.Icc a fun k ↦ a k + s k) ω)[|A]).map
                  (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
              - Φ.specificEnergy (empiricalFieldAverage E π (Finset.Icc a fun k ↦ a k + s k)
                  ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
                    (Finset.Icc a fun k ↦ a k + s k) ω)[|A])))
          + 3 * Φ.tail (Finset.Icc a fun k ↦ a k + s k) (Finset.Icc a fun k ↦ a k + s k)
              / (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ) : ℝ) : EReal) := by
  have hΛne : (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).Nonempty :=
    Finset.nonempty_Icc.2 fun k ↦ by simp
  have hcard : (0 : ℝ) < #(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) := by
    exact_mod_cast hΛne.card_pos
  have hκprob : IsProbabilityMeasure
      ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
        (Finset.Icc a fun k ↦ a k + s k) ω)[|A]) := cond_isProbabilityMeasure hpos
  obtain ⟨hfin, hM1⟩ := relativeEntropyIn_cond_gibbsSpecification_ne_top_and_le ν hΦ hπ hΛne ω
    hA hpos
  rw [specificRelativeEntropy_tileAverage_map_finsetRestrict ν a s _ hfin, EReal.coe_le_coe_iff]
  set N : ℝ := (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ) with hNdef
  set Rr : ℝ := (relativeEntropyIn
    ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ))
    ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
      (Finset.Icc a fun k ↦ a k + s k) ω)[|A]) (Measure.infinitePi fun _ ↦ ν)).toReal with hRrdef
  set eR : ℝ := Φ.specificEnergy (empiricalFieldAverage E π (Finset.Icc a fun k ↦ a k + s k)
    ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
      (Finset.Icc a fun k ↦ a k + s k) ω)[|A])) with heRdef
  set LZ : ℝ := Φ.logZ ν (Finset.Icc a fun k ↦ a k + s k) ω with hLZdef
  set q : ℝ := -Real.log ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
    (Finset.Icc a fun k ↦ a k + s k) ω).real A) with hqdef
  set tl : ℝ := Φ.tail (Finset.Icc a fun k ↦ a k + s k) (Finset.Icc a fun k ↦ a k + s k)
    with htldef
  have key : Rr / N + eR + LZ / N ≤ q / N + 3 * tl / N := by
    have h2 : (Rr + N * eR + LZ) / N ≤ (q + 3 * tl) / N :=
      div_le_div_of_nonneg_right hM1 hcard.le
    have e1 : (Rr + N * eR + LZ) / N = Rr / N + eR + LZ / N := by field_simp
    have e2 : (q + 3 * tl) / N = q / N + 3 * tl / N := by ring
    rwa [e1, e2] at h2
  linarith

end Assembled


/-! ### The excess free energy is concave on `𝓟_Θ` -/

section Concave

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  (ν : Measure E) [IsProbabilityMeasure ν] {Φ : Potential.BTheta (ι → ℤ) E}

omit [Nonempty ι] in
/-- The excess free energy is `+∞` exactly where the specific entropy is `−∞`. -/
theorem specificRelativeEntropy_eq_top_of_specificEntropy_eq_bot
    {μ : Measure ((ι → ℤ) → E)} (h : specificEntropy ν μ = ⊥) :
    (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ = ⊤ := by
  rw [Potential.specificRelativeEntropy, h, EReal.sub_bot (EReal.coe_ne_bot _)]

/-- **Georgii Proposition (15.14), the concavity of the excess free energy on `𝓟_Θ`.** For
shift-invariant random fields and `a + b = 1` with `a, b ≥ 0`,
`a 𝓀(μ₁|Φ) + b 𝓀(μ₂|Φ) ≤ 𝓀(a μ₁ + b μ₂|Φ)`.

This is the *convexity* half of Proposition (15.14) for the specific entropy
(`specificEntropy_smul_add_smul_le`, which needs `d ≥ 1` and shift invariance) together with the
affinity of the specific energy (`Potential.specificEnergy_smul_add_smul`); the excess free energy
is `𝓀(μ|Φ) = P(Φ) + ⟨μ, Φ⟩ − 𝓀(μ)`. It is what Georgii's Step 3 consumes: the infimum of a
*concave* lower semicontinuous functional does not change when `C` is replaced by its closed
convex hull. -/
theorem smul_specificRelativeEntropy_add_smul_specificRelativeEntropy_le
    {μ₁ μ₂ ρ : Measure ((ι → ℤ) → E)}
    (h₁ : μ₁ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (h₂ : μ₂ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hmix : ρ = ENNReal.ofReal a • μ₁ + ENNReal.ofReal b • μ₂) :
    (a : EReal) * (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ₁
        + (b : EReal) * (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ₂
      ≤ (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν ρ := by
  have hp₁ : IsProbabilityMeasure μ₁ := h₁.1
  have hp₂ : IsProbabilityMeasure μ₂ := h₂.1
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    have hρ : ρ = μ₂ := by rw [hmix]; simp
    rw [hρ]
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1
    have hρ : ρ = μ₁ := by rw [hmix]; simp
    rw [hρ]
    simp
  -- both weights are positive: rewrite the mixture with `ℝ≥0` weights
  set s : ℝ≥0 := a.toNNReal with hsdef
  set t : ℝ≥0 := b.toNNReal with htdef
  have hsa : (s : ℝ) = a := Real.coe_toNNReal a ha
  have htb : (t : ℝ) = b := Real.coe_toNNReal b hb
  have hst : s + t = 1 := by
    rw [hsdef, htdef, ← Real.toNNReal_add ha hb, hab, Real.toNNReal_one]
  have hs0 : 0 < s := Real.toNNReal_pos.2 ha'
  have ht0 : 0 < t := Real.toNNReal_pos.2 hb'
  have hmix' : ρ = s • μ₁ + t • μ₂ := by
    rw [hmix, ENNReal.smul_def, ENNReal.smul_def]; rfl
  have hρinv : ρ ∈ invariantFields (shiftGroup (ι → ℤ) E) := by
    rw [hmix']; exact smul_add_smul_mem_invariantFields h₁ h₂ hst
  have hpρ : IsProbabilityMeasure ρ := hρinv.1
  have hk : specificEntropy ν ρ
      ≤ ((s : ℝ) : EReal) * specificEntropy ν μ₁ + ((t : ℝ) : EReal) * specificEntropy ν μ₂ := by
    rw [hmix']; exact specificEntropy_smul_add_smul_le ν h₁ h₂ hs0 ht0 hst
  have henergy : (Φ : Potential (ι → ℤ) E).specificEnergy ρ
      = (s : ℝ) * (Φ : Potential (ι → ℤ) E).specificEnergy μ₁
        + (t : ℝ) * (Φ : Potential (ι → ℤ) E).specificEnergy μ₂ := by
    rw [hmix']; exact Potential.specificEnergy_smul_add_smul μ₁ μ₂ s t
  by_cases hbot : specificEntropy ν ρ = ⊥
  · rw [specificRelativeEntropy_eq_top_of_specificEntropy_eq_bot ν hbot]
    exact le_top
  -- the specific entropies of `μ₁` and `μ₂` are then finite as well
  have hnonpos₁ : specificEntropy ν μ₁ ≤ 0 := specificEntropy_nonpos ν
  have hnonpos₂ : specificEntropy ν μ₂ ≤ 0 := specificEntropy_nonpos ν
  have hne₁ : specificEntropy ν μ₁ ≠ ⊥ := by
    intro hb₁
    refine hbot (le_bot_iff.1 (hk.trans ?_))
    rw [hb₁, EReal.coe_mul_bot_of_pos (by rw [hsa]; exact ha'), EReal.bot_add]
  have hne₂ : specificEntropy ν μ₂ ≠ ⊥ := by
    intro hb₂
    refine hbot (le_bot_iff.1 (hk.trans ?_))
    rw [hb₂, EReal.coe_mul_bot_of_pos (by rw [htb]; exact hb'), EReal.add_bot]
  -- all three specific entropies are real numbers
  set k₁ : ℝ := (specificEntropy ν μ₁).toReal with hk₁def
  set k₂ : ℝ := (specificEntropy ν μ₂).toReal with hk₂def
  set kρ : ℝ := (specificEntropy ν ρ).toReal with hkρdef
  have e₁ : specificEntropy ν μ₁ = (k₁ : EReal) :=
    (EReal.coe_toReal (specificEntropy_ne_top ν) hne₁).symm
  have e₂ : specificEntropy ν μ₂ = (k₂ : EReal) :=
    (EReal.coe_toReal (specificEntropy_ne_top ν) hne₂).symm
  have eρ : specificEntropy ν ρ = (kρ : EReal) :=
    (EReal.coe_toReal (specificEntropy_ne_top ν) hbot).symm
  have hkR : kρ ≤ a * k₁ + b * k₂ := by
    have h := hk
    rw [e₁, e₂, eρ, hsa, htb, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at h
    exact h
  rw [Potential.specificRelativeEntropy, Potential.specificRelativeEntropy,
    Potential.specificRelativeEntropy, e₁, e₂, eρ, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff,
    henergy, hsa, htb]
  set P : ℝ := (Φ : Potential (ι → ℤ) E).pressure ν with hPdef
  set e₁' : ℝ := (Φ : Potential (ι → ℤ) E).specificEnergy μ₁ with he₁def
  set e₂' : ℝ := (Φ : Potential (ι → ℤ) E).specificEnergy μ₂ with he₂def
  have hPsum : a * P + b * P = P := by rw [← add_mul, hab, one_mul]
  have hexpand : a * (P + e₁' - k₁) + b * (P + e₂' - k₂)
      = (a * P + b * P) + (a * e₁' + b * e₂') - (a * k₁ + b * k₂) := by ring
  rw [hexpand, hPsum]
  linarith

end Concave

/-! ### Georgii Theorem (15.45): the upper bound (15.46) -/

section Main

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  [Finite E] [MeasurableSingletonClass E]
  (ν : Measure E) [IsProbabilityMeasure ν]

omit [Nonempty ι] [Finite E] [MeasurableSingletonClass E] in
open scoped Classical in
/-- **The Følner property of cubes for a finite window.** For a fixed finite set `B` of sites the
boundary layer `{i ∈ Λ_n : B + i ⊄ Λ_n}` of the cube `Λ_n = [m_n, m_n + s_n]^d` has vanishing
relative size. This is `tendsto_card_filter_add_notMem_div_card`, which treats one site, summed
over `B`. -/
theorem tendsto_card_biUnion_filter_add_notMem_div_card {m : ℕ → ι → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop) (B : Finset (ι → ℤ)) :
    Tendsto (fun n ↦ (#(B.biUnion fun b ↦
          {i ∈ Finset.Icc (m n) fun k ↦ m n k + s n |
            b + i ∉ Finset.Icc (m n) fun k ↦ m n k + s n}) : ℝ)
        / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))) atTop (𝓝 0) := by
  have hbound : Tendsto (fun n ↦ ∑ b ∈ B,
      (#{i ∈ Finset.Icc (m n) fun k ↦ m n k + s n |
          b + i ∉ Finset.Icc (m n) fun k ↦ m n k + s n} : ℝ)
        / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum B fun b (_ : b ∈ B) ↦
      tendsto_card_filter_add_notMem_div_card (m := m) hs b
    simpa only [Finset.sum_const_zero] using h
  refine squeeze_zero (fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n ↦ ?_) hbound
  rw [← Finset.sum_div]
  have hpos : (0 : ℝ) < #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) := by
    refine Nat.cast_pos.2 (Finset.card_pos.2 ?_)
    exact Finset.nonempty_Icc.2 fun k ↦ by simp
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_biUnion_le) hpos.le

omit [Nonempty ι] [Finite E] [MeasurableSingletonClass E] in
open scoped Classical in
/-- **The two auxiliary fields of Step 2 agree asymptotically on every local event.** This is
`abs_integral_tileAverage_sub_integral_empiricalFieldAverage_le` at the indicator of the local
event, together with the Følner property of the cubes: it says that the randomly shifted
independent-block field `γ̄` and the mean empirical field `κ °R_Λ` have the same limit points in
the topology of local convergence. -/
theorem tendsto_measureReal_tileAverage_sub_measureReal_empiricalFieldAverage
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (κ : ℕ → Measure ((ι → ℤ) → E)) (hκ : ∀ n, IsProbabilityMeasure (κ n))
    {A : Set ((ι → ℤ) → E)} (hA : A ∈ localEvents (ι → ℤ) E) :
    Tendsto (fun n ↦ (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
          ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict)).real A
        - (empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n) (κ n)).real A)
      atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  have hAmeas : MeasurableSet A := cylinderEvents_le_pi _ hB
  have hdep : DependsOn (Set.indicator A (1 : ((ι → ℤ) → E) → ℝ)) (B : Set (ι → ℤ)) := by
    intro x y hxy
    have h := mem_congr_of_measurableSet_cylinderEvents hB hxy
    by_cases hx : x ∈ A
    · simp [hx, h.1 hx]
    · have hy : y ∉ A := fun hy ↦ hx (h.2 hy)
      simp [hx, hy]
  have hfm : StronglyMeasurable (Set.indicator A (1 : ((ι → ℤ) → E) → ℝ)) :=
    (stronglyMeasurable_const (α := (ι → ℤ) → E) (b := (1 : ℝ))).indicator hAmeas
  have hc : ∀ η, |Set.indicator A (1 : ((ι → ℤ) → E) → ℝ) η| ≤ 1 := by
    intro η; by_cases h : η ∈ A <;> simp [h]
  have hTsub : ∀ n, (B.biUnion fun b ↦
      {i ∈ Finset.Icc (m n) fun k ↦ m n k + s n |
        b + i ∉ Finset.Icc (m n) fun k ↦ m n k + s n})
      ⊆ Finset.Icc (m n) fun k ↦ m n k + s n := fun n ↦
    Finset.biUnion_subset.2 fun b _ ↦ Finset.filter_subset _ _
  have hgood : ∀ n, ∀ i ∈ Finset.Icc (m n) fun k ↦ m n k + s n,
      i ∉ (B.biUnion fun b ↦ {i ∈ Finset.Icc (m n) fun k ↦ m n k + s n |
        b + i ∉ Finset.Icc (m n) fun k ↦ m n k + s n}) →
      ∀ b ∈ (B : Set (ι → ℤ)), b + i ∈ Finset.Icc (m n) fun k ↦ m n k + s n := by
    intro n i hi hiT b hb
    by_contra hbi
    exact hiT (Finset.mem_biUnion.2 ⟨b, hb, Finset.mem_filter.2 ⟨hi, hbi⟩⟩)
  have hsmall := tendsto_card_biUnion_filter_add_notMem_div_card (m := m) hs B
  have hmaj : Tendsto (fun n ↦ 2 * ((#(B.biUnion fun b ↦
        {i ∈ Finset.Icc (m n) fun k ↦ m n k + s n |
          b + i ∉ Finset.Icc (m n) fun k ↦ m n k + s n}) : ℝ)
      / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)))) atTop (𝓝 0) := by
    have h := hsmall.const_mul (2 : ℝ)
    rwa [mul_zero] at h
  refine squeeze_zero_norm' (.of_forall fun n ↦ ?_) hmaj
  have := hκ n
  have hbound := abs_integral_tileAverage_sub_integral_empiricalFieldAverage_le (hπ n)
    (isComplement_Icc (m n) fun _ ↦ s n) (κ n) hdep hfm hc (hTsub n) (hgood n)
  rw [integral_indicator_one hAmeas, integral_indicator_one hAmeas] at hbound
  rw [Real.norm_eq_abs]
  refine hbound.trans (le_of_eq ?_)
  ring

/-- **Steps 2 and 3 of Georgii's proof of the upper bound (15.46): the cluster point.** Suppose
that along a sequence of cubes `Λ_n` with sides tending to infinity there are boundary conditions
`ω_n` for which `γ^Φ_{Λ_n}(°R_{Λ_n} ∈ C | ω_n) > e^{−c|Λ_n|}`. Then there is a shift-invariant
random field `μ` in Georgii's `cx̄ C` with `𝓀(μ|Φ) ≤ c`.

This is Georgii's argument by contradiction in Step 2, with the compactness of the level sets of
the specific entropy replaced by the compactness of the whole space of random fields, which over
a finite state space is automatic (Georgii Example (4.11)(2)). The finite-volume input is
`specificRelativeEntropy_tileAverage_cond_le`; the three correction terms in it vanish along the
convergent subsequence, the first by Theorem (15.30)(a) uniformly in the boundary condition, the
second because the two auxiliary fields have the same limit
(`tendsto_measureReal_tileAverage_sub_measureReal_empiricalFieldAverage`) and `⟨·, Φ⟩` is
continuous, the third by the estimate (15.25). The limit lies in `cx̄ C` because each
`γ^C_{Λ_n|ω_n} °R_{Λ_n}` does
(`evalLocalEvents_empiricalFieldAverage_mem_convexHull`), and `𝓀(·|Φ)` is lower semicontinuous. -/
theorem exists_mem_closedConvexHull_specificRelativeEntropy_le
    (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ} (ω : ℕ → (ι → ℤ) → E)
    (hω : ∀ n, ENNReal.ofReal (Real.exp (-(c *
          #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)))))
        < Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
            (Finset.Icc (m n) fun k ↦ m n k + s n) (ω n)
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}) :
    ∃ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal) := by
  classical
  have : Nonempty E := Measure.nonempty_of_neZero ν
  have hΦ := Potential.BTheta.isShiftInvariant Φ
  have hcardpos : ∀ n, (0 : ℝ) < #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) :=
    fun n ↦ by exact_mod_cast (hne n).card_pos
  have hpos : ∀ n, Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 (Finset.Icc (m n) fun k ↦ m n k + s n) (ω n)
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C} ≠ 0 := fun n ↦
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _)) (hω n).le).ne'
  have hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
      ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C} := fun n ↦
    measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem (hπ n) (hne n) C
  set κ : ℕ → Measure ((ι → ℤ) → E) := fun n ↦
    (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
      (Finset.Icc (m n) fun k ↦ m n k + s n) (ω n))[|
        {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}] with hκdef
  have hκprob : ∀ n, IsProbabilityMeasure (κ n) := fun n ↦ cond_isProbabilityMeasure (hpos n)
  set blk : ℕ → Measure ((ι → ℤ) → E) := fun n ↦
    tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
      ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict) with hblkdef
  have hblkprob : ∀ n, IsProbabilityMeasure (blk n) := fun n ↦ by
    have := hκprob n; exact isProbabilityMeasure_tileAverage _ _
  set emp : ℕ → Measure ((ι → ℤ) → E) := fun n ↦
    empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n) (κ n) with hempdef
  have hempprob : ∀ n, IsProbabilityMeasure (emp n) := fun n ↦ by
    have := hκprob n
    have : NeZero (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))) :=
      ⟨(hne n).card_pos.ne'⟩
    exact isProbabilityMeasure_empiricalFieldAverage _ _
  set blkL : ℕ → WithLocalConvergence (ι → ℤ) E := fun n ↦
    WithSetwiseTopology.ofMeasure ⟨blk n, hblkprob n⟩ with hblkLdef
  set empL : ℕ → WithLocalConvergence (ι → ℤ) E := fun n ↦
    WithSetwiseTopology.ofMeasure ⟨emp n, hempprob n⟩ with hempLdef
  obtain ⟨μ, -, ψ, hψ, hlim⟩ := isCompact_univ.tendsto_subseq (x := blkL) fun n ↦ Set.mem_univ _
  have hs' : Tendsto (fun k ↦ s (ψ k)) atTop atTop := hs.comp hψ.tendsto_atTop
  -- the mean empirical fields have the same limit
  have hempLim : Tendsto (fun k ↦ empL (ψ k)) atTop (𝓝 μ) := by
    rw [tendsto_withLocalConvergence_iff]
    intro A hA
    have h1 : Tendsto (fun k ↦ blk (ψ k) A) atTop (𝓝 ((μ.toMeasure : Measure _) A)) :=
      tendsto_withLocalConvergence_iff.1 hlim A hA
    have h1r : Tendsto (fun k ↦ (blk (ψ k)).real A) atTop
        (𝓝 ((μ.toMeasure : Measure ((ι → ℤ) → E)).real A)) := by
      simpa only [measureReal_def, Function.comp_def] using
        (ENNReal.tendsto_toReal (measure_ne_top (μ.toMeasure : Measure ((ι → ℤ) → E)) A)).comp h1
    have h2 : Tendsto (fun k ↦ (blk (ψ k)).real A - (emp (ψ k)).real A) atTop (𝓝 0) :=
      tendsto_measureReal_tileAverage_sub_measureReal_empiricalFieldAverage
        (m := fun k ↦ m (ψ k)) (s := fun k ↦ s (ψ k)) hs' (fun k ↦ hπ (ψ k))
        (fun k ↦ κ (ψ k)) (fun k ↦ hκprob (ψ k)) hA
    have h3 : Tendsto (fun k ↦ (emp (ψ k)).real A) atTop
        (𝓝 ((μ.toMeasure : Measure ((ι → ℤ) → E)).real A)) := by
      have h := h1r.sub h2
      simpa using h
    have h4 : Tendsto (fun k ↦ ENNReal.ofReal ((emp (ψ k)).real A)) atTop
        (𝓝 (ENNReal.ofReal ((μ.toMeasure : Measure ((ι → ℤ) → E)).real A))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp h3
    have hrwμ : ENNReal.ofReal ((μ.toMeasure : Measure ((ι → ℤ) → E)).real A)
        = (μ.toMeasure : Measure ((ι → ℤ) → E)) A := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hrwμ] at h4
    refine h4.congr fun k ↦ ?_
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  refine ⟨μ, ?_, ?_, ?_⟩
  · -- `μ` is shift invariant
    refine (isClosed_setOf_mem_invariantFields (shiftGroup (ι → ℤ) E)).mem_of_tendsto hlim
      (.of_forall fun k ↦ ?_)
    exact tileAverage_mem_invariantFields_shiftGroup _ _
  · -- `μ` lies in the closed convex hull
    refine isClosed_closedConvexHull.mem_of_tendsto
      (WithSetwiseTopology.continuous_evalReal.continuousAt.tendsto.comp hempLim)
      (.of_forall fun k ↦ ?_)
    refine convexHull_subset_closedConvexHull ?_
    have hcond : κ (ψ k) {σ | periodicEmpiricalFieldL (π (ψ k)) (hne (ψ k)) σ ∈ C}ᶜ = 0 := by
      rw [hκdef]
      have hm := cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E)
        (Δ := ((Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k) : Finset (ι → ℤ)) : Set (ι → ℤ)))
        _ (hAmeas (ψ k))
      rw [cond_apply hm, Set.inter_compl_self, measure_empty, mul_zero]
    have := hκprob (ψ k)
    exact evalLocalEvents_empiricalFieldAverage_mem_convexHull (hπ (ψ k)) (hne (ψ k))
      (κ (ψ k)) hcond
  · -- the excess free energy of the limit is at most `c`
    by_contra hgt
    push Not at hgt
    obtain ⟨c', hcc', hc'⟩ := EReal.exists_between_coe_real hgt
    -- the finite-volume estimate
    have hM : ∀ n, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν (blk n)
        ≤ ((c + (((Φ : Potential (ι → ℤ) E).pressure ν
              - (Φ : Potential (ι → ℤ) E).logZ ν (Finset.Icc (m n) fun k ↦ m n k + s n) (ω n)
                / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)))
            + ((Φ : Potential (ι → ℤ) E).specificEnergy (blk n)
              - (Φ : Potential (ι → ℤ) E).specificEnergy (emp n))
            + 3 * (Φ : Potential (ι → ℤ) E).tail (Finset.Icc (m n) fun k ↦ m n k + s n)
                (Finset.Icc (m n) fun k ↦ m n k + s n)
              / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))) : ℝ) : EReal) := by
      intro n
      have hmain := specificRelativeEntropy_tileAverage_cond_le ν hΦ (m n) (fun _ ↦ s n) (hπ n)
        (ω n) (hAmeas n) (hpos n)
      refine hmain.trans (EReal.coe_le_coe_iff.2 ?_)
      have hq : -Real.log ((Potential.gibbsSpecificationOfAbsolutelySummable
            (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 (Finset.Icc (m n) fun k ↦ m n k + s n)
            (ω n)).real {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
          / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) ≤ c := by
        rw [div_le_iff₀ (hcardpos n)]
        have hlt := (ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos _).le
          (measure_ne_top _ _)).1 (hω n)
        have hlog := Real.log_lt_log (Real.exp_pos _) hlt
        rw [Real.log_exp] at hlog
        rw [measureReal_def]
        linarith
      linarith
    -- the correction terms vanish along the subsequence
    have hZ : Tendsto (fun k ↦ (Φ : Potential (ι → ℤ) E).pressure ν
        - (Φ : Potential (ι → ℤ) E).logZ ν
            (Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k)) (ω (ψ k))
          / #(Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k) : Finset (ι → ℤ)))
        atTop (𝓝 0) := by
      have h := Potential.tendsto_logZ_div_card_pressure (Φ := (Φ : Potential (ι → ℤ) E)) ν hΦ
        (m := fun k ↦ m (ψ k)) (n := fun k ↦ fun j ↦ m (ψ k) j + s (ψ k))
        (fun j ↦ by simpa [Function.comp_def] using
          (tendsto_natCast_atTop_atTop (R := ℤ)).comp hs')
        (fun k ↦ ω (ψ k))
      have h2 : Tendsto (fun k ↦ (Φ : Potential (ι → ℤ) E).pressure ν
          - (Φ : Potential (ι → ℤ) E).logZ ν
              (Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k)) (ω (ψ k))
            / #(Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k) : Finset (ι → ℤ)))
          atTop (𝓝 ((Φ : Potential (ι → ℤ) E).pressure ν
            - (Φ : Potential (ι → ℤ) E).pressure ν)) := tendsto_const_nhds.sub h
      simpa using h2
    have hT : Tendsto (fun k ↦ 3 * (Φ : Potential (ι → ℤ) E).tail
          (Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k))
          (Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k))
        / #(Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k) : Finset (ι → ℤ)))
        atTop (𝓝 0) := by
      have h := Potential.tendsto_tail_div_card (Φ := (Φ : Potential (ι → ℤ) E)) hΦ
        (m := fun k ↦ m (ψ k)) (n := fun k ↦ fun j ↦ m (ψ k) j + s (ψ k))
        (fun j ↦ by simpa [Function.comp_def] using
          (tendsto_natCast_atTop_atTop (R := ℤ)).comp hs')
      simpa [mul_div_assoc] using h.const_mul (3 : ℝ)
    have hEnergy : Tendsto (fun k ↦ (Φ : Potential (ι → ℤ) E).specificEnergy (blk (ψ k))
        - (Φ : Potential (ι → ℤ) E).specificEnergy (emp (ψ k))) atTop (𝓝 0) := by
      have h1 := (Potential.continuous_specificEnergy
        (Φ := (Φ : Potential (ι → ℤ) E))).continuousAt.tendsto.comp hlim
      have h2 := (Potential.continuous_specificEnergy
        (Φ := (Φ : Potential (ι → ℤ) E))).continuousAt.tendsto.comp hempLim
      have h3 : Tendsto (fun k ↦ (Φ : Potential (ι → ℤ) E).specificEnergy (blk (ψ k))
          - (Φ : Potential (ι → ℤ) E).specificEnergy (emp (ψ k))) atTop
          (𝓝 ((Φ : Potential (ι → ℤ) E).specificEnergy (μ.toMeasure : Measure ((ι → ℤ) → E))
            - (Φ : Potential (ι → ℤ) E).specificEnergy
              (μ.toMeasure : Measure ((ι → ℤ) → E)))) := h1.sub h2
      simpa using h3
    have hε : Tendsto (fun k ↦ c + ((((Φ : Potential (ι → ℤ) E).pressure ν
              - (Φ : Potential (ι → ℤ) E).logZ ν
                  (Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k)) (ω (ψ k))
                / #(Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k) : Finset (ι → ℤ)))
            + ((Φ : Potential (ι → ℤ) E).specificEnergy (blk (ψ k))
              - (Φ : Potential (ι → ℤ) E).specificEnergy (emp (ψ k)))
            + 3 * (Φ : Potential (ι → ℤ) E).tail
                (Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k))
                (Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k))
              / #(Finset.Icc (m (ψ k)) fun j ↦ m (ψ k) j + s (ψ k) : Finset (ι → ℤ))))) atTop
        (𝓝 c) := by
      simpa using tendsto_const_nhds.add ((hZ.add hEnergy).add hT)
    -- lower semicontinuity gives a contradiction
    have hlsc := Potential.BTheta.lowerSemicontinuous_specificRelativeEntropy ν Φ μ c' hc'
    have hev1 : ∀ᶠ k in atTop,
        (c' : EReal) < (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν (blk (ψ k)) :=
      hlim.eventually hlsc
    have hev2 : ∀ᶠ k in atTop, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν (blk (ψ k))
        < (c' : EReal) := by
      have hcc'R : c < c' := by exact_mod_cast hcc'
      filter_upwards [hε.eventually (eventually_lt_nhds (by linarith : c < c'))] with k hk
      exact lt_of_le_of_lt (hM (ψ k)) (EReal.coe_lt_coe_iff.2 hk)
    obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
    exact absurd hk1 (not_lt.2 hk2.le)

/-- **The upper bound (15.46) in exponential form, with Georgii's `cx̄ C` on the right.** If `c`
is strictly below the excess free energy of every shift-invariant random field in `cx̄ C`, then
eventually `γ^Φ_Λ(°R_Λ ∈ C | ω) ≤ e^{−c |Λ|}`, *uniformly in the boundary condition* `ω`. This is
the contrapositive of the cluster-point lemma
`exists_mem_closedConvexHull_specificRelativeEntropy_le`; Georgii takes an `ω` at which a fixed
fraction of the supremum in (15.46) is attained, which over a general state space is the way to
get the uniformity, and here amounts to the choice of a boundary condition for each volume in
which the bound fails. -/
theorem eventually_gibbsSpecification_setOf_periodicEmpiricalFieldL_mem_le
    (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hc : ∀ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) →
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) →
      (c : EReal) < (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E))) :
    ∀ᶠ n in atTop, ∀ ω : (ι → ℤ) → E,
      Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
          (Finset.Icc (m n) fun k ↦ m n k + s n) ω
          {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}
        ≤ ENNReal.ofReal (Real.exp
            (-(c * #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))))) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hcon
  have hex : ∀ j : ℕ, ∃ ω : (ι → ℤ) → E,
      ENNReal.ofReal (Real.exp (-(c * #(Finset.Icc (m (φ j)) fun k ↦ m (φ j) k + s (φ j)
          : Finset (ι → ℤ)))))
        < Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
            (Finset.Icc (m (φ j)) fun k ↦ m (φ j) k + s (φ j)) ω
            {σ | periodicEmpiricalFieldL (π (φ j)) (hne (φ j)) σ ∈ C} := by
    intro j
    by_contra h
    push Not at h
    exact hφP j h
  choose ω hω using hex
  obtain ⟨μ, hμinv, hμhull, hμle⟩ := exists_mem_closedConvexHull_specificRelativeEntropy_le ν Φ
    (m := fun j ↦ m (φ j)) (s := fun j ↦ s (φ j)) (hs.comp hφ.tendsto_atTop)
    (G := fun j ↦ G (φ j)) (π := fun j ↦ π (φ j)) (fun j ↦ hπ (φ j)) (fun j ↦ hne (φ j)) ω hω
  exact absurd hμle (not_le.2 (hc μ hμinv hμhull))

/-- **Georgii Theorem (15.45), the upper bound (15.46).** For `Φ ∈ ℬ_Θ` and a set `C ⊆ 𝓟_Θ` of
shift-invariant random fields,

`limsup_{|Λ| → ∞} |Λ|⁻¹ log sup_ω γ^Φ_Λ(°R_Λ ∈ C | ω) ≤ − inf_{ν ∈ C̄} 𝓀(ν|Φ)`,

the limit being taken along any sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` of `ℤ^d` whose side
lengths tend to infinity, with arbitrary torus reductions `π_n` defining the periodic empirical
field `°R_{Λ_n}`.

## Hypotheses

Georgii states (15.45) for a *standard Borel* state space. This proof needs `E` **finite**, in
three places, all of them in Steps 2 and 3:

* the event `{°R_Λ ∈ C}` is a cylinder event for *every* `C` whatsoever
  (`measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem`), so the left-hand side is
  meaningful with no measurability assumption on `C`;
* the mean empirical field `γ^C_{Λ|ω} °R_Λ` is an *exact* finite convex combination of periodic
  empirical fields lying in `C` (`evalLocalEvents_empiricalFieldAverage_mem_convexHull`), which
  is Georgii's "basic observation" of Step 2 without his approximation argument, and the space of
  random fields is compact (Georgii Example (4.11)(2)), which replaces his appeal to the
  compactness of the level sets of the specific entropy;
* Step 3, the passage from `cx̄ C` to `C̄`, rests on the Choquet-theoretic
  `iInf_closedConvexHull_eq_iInf_closure_ereal`, which needs `𝓟_Θ` to be a compact convex subset
  of a locally convex Polish space; over a finite state space the algebra `𝓕⁰` of *all* local
  events is countable, so the topology of local convergence is already the `𝒞`-topology Georgii
  passes to.

`d ≥ 1` (`Nonempty ι`) is Georgii's standing assumption; it is what makes the specific entropy
convex, hence `𝓀(·|Φ)` concave, which Step 3 consumes. -/
theorem limsup_log_iSup_gibbsSpecification_div_card_le
    (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hC : C ⊆ invariantRandomFields (ι → ℤ) E) :
    Filter.limsup (fun n ↦ ENNReal.log (⨆ ω : (ι → ℤ) → E,
          Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
            (Finset.Icc (m n) fun k ↦ m n k + s n) ω
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ ∈ closure C, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  have hΦ := Potential.BTheta.isShiftInvariant Φ
  set P : Set (WithLocalConvergence (ι → ℤ) E) := invariantRandomFields (ι → ℤ) E with hPdef
  set 𝒜 : WithLocalConvergence (ι → ℤ) E → EReal := fun μ ↦
    (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
      (μ.toMeasure : Measure ((ι → ℤ) → E)) with h𝒜def
  have hPmix : ∀ μ ∈ P, ∀ ν' ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ ρ ∈ P, (ρ.toMeasure : Measure ((ι → ℤ) → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure ((ι → ℤ) → E))
          + ENNReal.ofReal b • (ν'.toMeasure : Measure ((ι → ℤ) → E)) := by
    intro μ hμ ν' hν' a b ha hb hab
    have hst : a.toNNReal + b.toNNReal = 1 := by
      rw [← Real.toNNReal_add ha hb, hab, Real.toNNReal_one]
    have hmix := smul_add_smul_mem_invariantFields hμ hν' hst
    refine ⟨⟨⟨_, hmix.1⟩⟩, hmix, ?_⟩
    change (a.toNNReal : ℝ≥0) • (μ.toMeasure : Measure ((ι → ℤ) → E))
        + (b.toNNReal : ℝ≥0) • (ν'.toMeasure : Measure ((ι → ℤ) → E)) = _
    rw [ENNReal.smul_def, ENNReal.smul_def]
    rfl
  have hbdd : ∀ μ ∈ P, ((0 : ℝ) : EReal) ≤ 𝒜 μ := by
    intro μ hμ
    have : IsProbabilityMeasure (μ.toMeasure : Measure ((ι → ℤ) → E)) := hμ.1
    simpa using Potential.specificRelativeEntropy_nonneg (Φ := (Φ : Potential (ι → ℤ) E)) ν hΦ hμ
  have h1554 : (⨅ μ ∈ {μ | μ ∈ P ∧
        evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)}, 𝒜 μ)
      = ⨅ μ ∈ closure C, 𝒜 μ :=
    iInf_closedConvexHull_eq_iInf_closure_ereal
      (isClosed_setOf_mem_invariantFields (shiftGroup (ι → ℤ) E)) hPmix hC hbdd
      ((Potential.BTheta.lowerSemicontinuous_specificRelativeEntropy ν Φ).lowerSemicontinuousOn _)
      (fun μ hμ ν' hν' ρ _ a b ha hb hab hmix ↦
        smul_specificRelativeEntropy_add_smul_specificRelativeEntropy_le ν hμ hν' ha hb hab hmix)
  rw [← h1554]
  set L : EReal := Filter.limsup (fun n ↦ ENNReal.log (⨆ ω : (ι → ℤ) → E,
      Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
        (Finset.Icc (m n) fun k ↦ m n k + s n) ω
        {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
      / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop with hLdef
  -- the bound for every real strictly below the infimum
  have hstep : ∀ c : ℝ, (c : EReal) < (⨅ μ ∈ {μ | μ ∈ P ∧
        evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)}, 𝒜 μ) →
      L ≤ ((-c : ℝ) : EReal) := by
    intro c hcm
    have hc : ∀ μ : WithLocalConvergence (ι → ℤ) E,
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) →
        evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) →
        (c : EReal) < 𝒜 μ := fun μ hμ hμ' ↦
      lt_of_lt_of_le hcm (iInf₂_le μ ⟨hμ, hμ'⟩)
    have hev := eventually_gibbsSpecification_setOf_periodicEmpiricalFieldL_mem_le ν Φ hs hπ hne hc
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hev] with n hn
    have hsup : (⨆ ω : (ι → ℤ) → E,
        Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
          (Finset.Icc (m n) fun k ↦ m n k + s n) ω
          {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        ≤ ENNReal.ofReal (Real.exp
            (-(c * #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))))) :=
      iSup_le hn
    have hlog : ENNReal.log (⨆ ω : (ι → ℤ) → E,
        Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
          (Finset.Icc (m n) fun k ↦ m n k + s n) ω
          {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        ≤ ((-(c * #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))) : ℝ) : EReal) := by
      refine (ENNReal.log_monotone hsup).trans (le_of_eq ?_)
      rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
    have hcard : (0 : ℝ) < #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) := by
      exact_mod_cast (hne n).card_pos
    have hdiv := EReal.div_le_div_right_of_nonneg
      (c := ((#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : ℕ) : EReal))
      (Nat.cast_nonneg' _) hlog
    refine hdiv.trans (le_of_eq ?_)
    rw [← EReal.coe_natCast, ← EReal.coe_div, EReal.coe_eq_coe_iff]
    field_simp
  -- conclude
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real hcon
  have hcm : ((-y : ℝ) : EReal) < ⨅ μ ∈ {μ | μ ∈ P ∧
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)}, 𝒜 μ := by
    rw [EReal.coe_neg]
    exact EReal.neg_lt_comm.1 hy1
  have := hstep (-y) hcm
  rw [neg_neg] at this
  exact absurd hy2 (not_lt.2 this)

/-- **Georgii Theorem (15.45), the "in particular" clause of the upper bound (15.46).** The bound
holds with the finite-volume Gibbs distributions `γ^Φ_Λ(·|ω)` replaced by *any* Gibbs measure
`μ ∈ 𝒢(Φ)` — no shift invariance of `μ` is required:

`limsup_{|Λ| → ∞} |Λ|⁻¹ log μ(°R_Λ ∈ C) ≤ − inf_{ν ∈ C̄} 𝓀(ν|Φ)`.

Georgii obtains it "by integrating over `ω`": the DLR equation writes `μ(°R_Λ ∈ C)` as the
`μ`-average of `γ^Φ_Λ(°R_Λ ∈ C|ω)`, which is at most the supremum over `ω`. -/
theorem limsup_log_isGibbsMeasure_div_card_le
    (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hC : C ⊆ invariantRandomFields (ι → ℤ) E)
    {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : (Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1).IsGibbsMeasure μ) :
    Filter.limsup (fun n ↦
        ENNReal.log (μ {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
          / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ' ∈ closure C, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ'.toMeasure : Measure ((ι → ℤ) → E)) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  refine le_trans (Filter.limsup_le_limsup (.of_forall fun n ↦ ?_))
    (limsup_log_iSup_gibbsSpecification_div_card_le ν Φ hs hπ hne hC)
  refine EReal.div_le_div_right_of_nonneg (Nat.cast_nonneg' _) (ENNReal.log_monotone ?_)
  -- the DLR equation bounds `μ(A)` by the supremum of `γ^Φ_Λ(A|ω)`
  set Λ : Finset (ι → ℤ) := Finset.Icc (m n) fun k ↦ m n k + s n with hΛdef
  set A : Set ((ι → ℤ) → E) := {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C} with hAdef
  have hAm : MeasurableSet A := cylinderEvents_le_pi _
    (measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem (hπ n) (hne n) C)
  have hker : AEMeasurable (fun η : (ι → ℤ) → E ↦
      Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 Λ η)
      μ :=
    (((Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) Λ).measurable.mono cylinderEvents_le_pi
        le_rfl).aemeasurable
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ) Λ
  calc μ A = (μ.bind (Potential.gibbsSpecificationOfAbsolutelySummable
        (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 Λ)) A := by rw [hbind]
    _ = ∫⁻ η, Potential.gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 Λ η A ∂μ := Measure.bind_apply hAm hker
    _ ≤ ∫⁻ _η, (⨆ ω : (ι → ℤ) → E, Potential.gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 Λ ω A) ∂μ :=
        lintegral_mono fun η ↦ le_iSup (fun ω ↦ Potential.gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 Λ ω A) η
    _ = ⨆ ω : (ι → ℤ) → E, Potential.gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 Λ ω A := by
        rw [lintegral_const, measure_univ, mul_one]

end Main

end MeasureTheory.GibbsMeasure

end
