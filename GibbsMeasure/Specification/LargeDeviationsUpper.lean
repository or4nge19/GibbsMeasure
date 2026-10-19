/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Convex.ClosedConvexHullPi
public import GibbsMeasure.Mathlib.InformationTheory.KullbackLeibler.Cond
public import GibbsMeasure.Mathlib.Topology.ClusterPt
public import GibbsMeasure.Specification.BlockEntropy
public import GibbsMeasure.Specification.InvariantFieldsBarycenter
public import GibbsMeasure.Specification.LargeDeviationsLower
public import GibbsMeasure.Topology.LocalMetric

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

* `MeasureTheory.GibbsMeasure.limsup_log_iSup_gibbsSpecification_div_card_le_closedConvexHull`:
  **(15.46) with Georgii's `cx̄ C` on the right, over a standard Borel state space**, under his
  hypothesis `C ∈ 𝓔(𝓟_Θ)` (`MeasureTheory.GibbsMeasure.evalEvents`). This is Georgii's Steps 1, 2
  and 4 in his own generality.
* `MeasureTheory.GibbsMeasure.limsup_log_iSup_gibbsSpecification_div_card_le_of_convex`:
  **(15.46) as Georgii states it, with `C̄` on the right**, over a standard Borel state space and
  for a **convex** `C`, for which `cx̄ C = C̄` and Step 3 is vacuous.
* `MeasureTheory.GibbsMeasure.limsup_log_iSup_gibbsSpecification_div_card_le`: **(15.46)**, along
  any sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` of `ℤ^d` whose side lengths tend to infinity,
  with arbitrary torus reductions `π_n`, over a **finite** state space, where Step 3 is available.
  The logarithm is `ENNReal.log`, so the statement is meaningful also when the probability
  vanishes.
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

**Step 3** — the only step that is not available over an infinite state space, see below — is
Georgii (15.54), `inf_{cx̄ C} 𝓀(·|Φ) = inf_{C̄} 𝓀(·|Φ)`, supplied by
`MeasureTheory.GibbsMeasure.iInf_closedConvexHull_eq_iInf_closure_ereal` of
`Specification/InvariantFieldsBarycenter.lean`. It needs `𝓀(·|Φ)` **concave** on `𝓟_Θ`, which is
`smul_specificRelativeEntropy_add_smul_specificRelativeEntropy_le` below: the *convexity* half of
Proposition (15.14) for the specific entropy (`specificEntropy_smul_add_smul_le`, which needs
`d ≥ 1`) together with the affinity of the specific energy.

**Step 4** is the assembly, `limsup_log_iSup_gibbsSpecification_div_card_le`.

## The state space: Steps 1, 2 and 4 are standard Borel, Step 3 is not

**Steps 1, 2 and 4 hold over a standard Borel state space**, which is Georgii's generality, and
the corresponding statements carry his hypothesis `C ∈ 𝓔(𝓟_Θ)`:

* `evalEvents S E` is Georgii's evaluation σ-algebra of §7.3 on the random fields, and
  `measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem_of_evalEvents` is the statement
  that `C ∈ 𝓔` makes `{°R_Λ ∈ C}` a cylinder event of the volume `Λ`. Over a *finite* state space
  this holds for every `C` whatsoever
  (`measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem`), and Georgii's hypothesis
  carries no information.
* Georgii's "basic observation" of Step 2 is
  `evalLocalEvents_empiricalFieldAverage_mem_closedConvexHull`, over an arbitrary measurable state
  space and for an arbitrary `C`. Georgii builds the approximating convex combination by dividing
  `[0, 1]^k` into cells of diameter `< ε`; that is exactly the statement that a barycentre in
  `ℝ^k` lies in the closed convex hull of the almost sure range
  (`MeasureTheory.Convex.integral_mem`), transported to the product `𝓕⁰ → ℝ` by
  `mem_closedConvexHull_pi_of_forall_finset`.
* The cluster point of Step 2 is
  `exists_mem_closedConvexHull_specificRelativeEntropy_le_of_measurableSet`. The finite-volume
  bound confines all the block fields to one sublevel set `{𝓀(·|Φ) ≤ M}`, which over a standard
  Borel state space is **compact** for the topology of local convergence
  (`Potential.BTheta.isCompact_setOf_specificRelativeEntropy_le`, Georgii's Proposition (15.14));
  this is Georgii's own argument, and it replaces the compactness of the whole space of random
  fields, which is available only over a finite state space. Since the topology of local
  convergence is not first countable over an infinite state space, the cluster point is a limit
  along a finer filter, not along a subsequence (`MapClusterPt.exists_le_tendsto`); every lemma
  feeding Step 2 is therefore stated for a filter `l ≤ atTop`.
* The outcome is `limsup_log_iSup_gibbsSpecification_div_card_le_closedConvexHull`: Georgii's
  (15.46) over a standard Borel state space, **with `cx̄ C` on the right**.

**Step 3, Georgii's (15.54), is what is finite-only.** It replaces `cx̄ C` by `C̄`, and it rests
on a Choquet representation, hence on the compactness of an ambient convex set *in the topology
in which the closure is taken*. Over a finite state space `𝓕⁰` is countable, the space of random
fields is compact metrizable for the topology `𝓛` of local convergence, and
`iInf_closedConvexHull_eq_iInf_closure_ereal` applies; that is
`limsup_log_iSup_gibbsSpecification_div_card_le` below.

Over an infinite standard Borel state space `𝓟_Θ` is **not** `𝓛`-compact, and Georgii's remedy —
passing to the `𝒞`-topology of a countable core `𝒞 ⊆ 𝓕⁰` (Corollary (4.A13), Comment
(4.A10)(1); `GibbsMeasure/Topology/CountableCore.lean` and
`Specification/InvariantFieldsCoreTopology.lean`) — proves *less* than what he states. In the
`𝒞`-topology the Choquet argument produces a measure carried by the **`𝒞`-closure** `C̃` of `C`,
so it yields `inf_{cx̄ C} 𝓀(·|Φ) ≥ inf_{C̃} 𝓀(·|Φ)`, and `C̃` is in general strictly larger than
the `𝓛`-closure `C̄` (a countable core cannot be enlarged by an arbitrary local event: a sequence
of probability measures may converge on the core and not on `𝓕⁰`, and then the `𝒞`-limit lies in
`C̃ ∖ C̄`). The last sentence of Georgii's Step 3, "`C̃` can be replaced by `C̄` here", does not
follow from the coincidence of the two topologies on the sublevel sets of `𝓀(·|Φ)`, which is all
his argument provides. Moreover the resulting `C̃`-bound would be *weaker* than what is proved
here: `cx̄ C ⊆ cx̄_𝒞 C`, so `inf_{cx̄ C} 𝓀 ≥ inf_{C̃} 𝓀` and the bound with `cx̄ C` implies the
bound with `C̃`. Formalising Georgii's change of topology would therefore add nothing to the
statements below, and it is not done.

Two consequences of the `cx̄` form recover Georgii's own right-hand side over a standard Borel
state space in the cases that matter:

* `limsup_log_iSup_gibbsSpecification_div_card_le_of_convex`: for a **convex** `C`, `cx̄ C = C̄`
  and Step 3 is vacuous. This is what Corollary (15.48) needs, since `e_Ψ⁻¹(B) ∩ 𝓟_Θ` is convex
  as soon as `B` is (`Specification/LargeDeviationsCorollaries.lean`).
* For a general `C`, `cx̄ C` is Georgii's own Step-2 conclusion, and `−inf_{cx̄ C} 𝓀(·|Φ)` is a
  smaller — i.e. better — right-hand side than `−inf_{C̃} 𝓀(·|Φ)`.

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
  Measurable.of_eval fun n ↦ by
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
    (fun _ ↦ inferInstance)
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

/-! ### Georgii's `C ∈ 𝓔(𝓟_Θ)`, and the basic observation over an arbitrary state space -/

section EvalEvents

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E]
  {G : AddSubgroup S} {Λ : Finset S} {π : S → S}

variable (S E) in
/-- **Georgii's evaluation σ-algebra `𝓔` of §7.3**, read on the space of random fields with the
topology of local convergence: the σ-algebra generated by the evaluations `μ ↦ μ(A)` over the
measurable sets `A`, pulled back along `μ ↦ μ.toMeasure`.

Georgii's hypothesis on the set `C` of Theorem (15.45) is `C ∈ 𝓔(𝓟_Θ)`, i.e. `C ⊆ 𝓟_Θ` together
with `MeasurableSet[evalEvents S E] C`. It is exactly what makes `{°R_Λ ∈ C}` an event
(`measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem_of_evalEvents`). -/
abbrev evalEvents : MeasurableSpace (WithLocalConvergence S E) :=
  MeasurableSpace.comap (fun μ : WithLocalConvergence S E ↦ (μ.toMeasure : Measure (S → E)))
    inferInstance

/-- **`°R_Λ` is a measurable random field.** The periodic empirical field is a measurable function
of the configuration for the evaluation σ-algebra on `Measure (S → E)`: it is measurable evaluated
at every measurable set, being a finite average of Dirac masses at measurable functions of the
configuration. -/
theorem measurable_periodicEmpiricalField (π : S → S) (Λ : Finset S) :
    Measurable fun σ : S → E ↦ periodicEmpiricalField E π Λ σ := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp_rw [periodicEmpiricalField_apply π Λ _ hA]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
    (measurable_one.indicator hA).comp
      ((shift E (-i)).measurable_toFun.comp (Potential.measurable_periodicExtend π)))

/-- **`°R_Λ` is a `𝓕_Λ`-measurable random field**: the periodic continuation reads the
configuration only inside `Λ` (`measurable_cylinderEvents_periodicExtend`). -/
theorem measurable_cylinderEvents_periodicEmpiricalField
    (hπ : Potential.IsTorusReduction G Λ π) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      fun σ : S → E ↦ periodicEmpiricalField E π Λ σ := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp_rw [periodicEmpiricalField_apply π Λ _ hA]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
    (measurable_one.indicator hA).comp
      ((shift E (-i)).measurable_toFun.comp (measurable_cylinderEvents_periodicExtend hπ)))

/-- **Georgii's hypothesis `C ∈ 𝓔(𝓟_Θ)` makes `{°R_Λ ∈ C}` a cylinder event of the volume `Λ`.**
This is what gives the left-hand side of (15.46) a meaning over an arbitrary — in particular an
infinite standard Borel — state space; over a *finite* state space the hypothesis on `C` can be
dropped altogether
(`measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem`). -/
theorem measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem_of_evalEvents
    (hπ : Potential.IsTorusReduction G Λ π) (hΛ : Λ.Nonempty)
    {C : Set (WithLocalConvergence S E)} (hC : MeasurableSet[evalEvents S E] C) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      {σ | periodicEmpiricalFieldL π hΛ σ ∈ C} := by
  obtain ⟨D, hD, hCD⟩ := hC
  have hset : {σ : S → E | periodicEmpiricalFieldL π hΛ σ ∈ C}
      = (fun σ : S → E ↦ periodicEmpiricalField E π Λ σ) ⁻¹' D := by
    ext σ
    rw [Set.mem_ofPred_eq, ← hCD]
    rfl
  rw [hset]
  exact measurable_cylinderEvents_periodicEmpiricalField hπ hD

/-- **Georgii's "basic observation" in Step 2 of the proof of (15.46), over an arbitrary state
space.** If the random field `κ` is carried by the event `{°R_Λ ∈ C}` then the mean empirical
field `κ °R_Λ` belongs to Georgii's `cx̄ C`.

Georgii produces the approximating convex combination by hand: for cylinder events `A_1, …, A_k`
and `ε > 0` he divides `[0, 1]^k` into finitely many Borel cells of diameter `< ε`, picks a
configuration in each non-empty fibre, and weights it by the `κ`-mass of the fibre. That is
precisely the statement that a barycentre in the *finite-dimensional* space `ℝ^k` lies in the
closed convex hull of the (almost sure) range — `MeasureTheory.Convex.integral_mem` — and the
passage from the finitely many coordinates to the whole product `𝓕⁰ → ℝ` is
`mem_closedConvexHull_pi_of_forall_finset`; the two are packaged as
`integral_mem_closedConvexHull_pi`. Neither finiteness of the state space nor measurability of
`C` is needed: `κ {°R_Λ ∈ C}ᶜ = 0` is an outer-measure statement. -/
theorem evalLocalEvents_empiricalFieldAverage_mem_closedConvexHull (hΛ : Λ.Nonempty)
    (κ : Measure (S → E)) [IsProbabilityMeasure κ]
    {C : Set (WithLocalConvergence S E)}
    (hκ : κ {σ | periodicEmpiricalFieldL π hΛ σ ∈ C}ᶜ = 0) :
    haveI : NeZero (#Λ) := ⟨hΛ.card_pos.ne'⟩
    evalLocalEvents S E (WithSetwiseTopology.ofMeasure
        ⟨empiricalFieldAverage E π Λ κ, isProbabilityMeasure_empiricalFieldAverage π κ⟩)
      ∈ closedConvexHull ℝ (evalLocalEvents S E '' C) := by
  have hNe : NeZero (#Λ) := ⟨hΛ.card_pos.ne'⟩
  set f : (S → E) → (localEvents S E → ℝ) :=
    fun σ ↦ evalLocalEvents S E (periodicEmpiricalFieldL π hΛ σ) with hfdef
  have hmeasA : ∀ A : localEvents S E, MeasurableSet (A : Set (S → E)) :=
    fun A ↦ MeasurableSet.of_mem_measurableCylinders A.2
  have hmeas : ∀ A : localEvents S E, Measurable fun σ ↦ f σ A := fun A ↦
    ((Measure.measurable_coe (hmeasA A)).comp
      (measurable_periodicEmpiricalField π Λ)).ennreal_toReal
  have hbdd : ∀ (A : localEvents S E) (σ : S → E), ‖f σ A‖ ≤ 1 := by
    intro A σ
    have h1 : f σ A = (periodicEmpiricalField E π Λ σ (A : Set (S → E))).toReal := rfl
    rw [h1, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using ENNReal.toReal_mono (by simp) (prob_le_one (μ := periodicEmpiricalField E π Λ σ))
  have hint : ∀ A : localEvents S E, Integrable (fun σ ↦ f σ A) κ := fun A ↦
    (integrable_const (1 : ℝ)).mono' (hmeas A).aestronglyMeasurable
      (.of_forall fun σ ↦ hbdd A σ)
  have hval : evalLocalEvents S E (WithSetwiseTopology.ofMeasure
        ⟨empiricalFieldAverage E π Λ κ, isProbabilityMeasure_empiricalFieldAverage π κ⟩)
      = fun A : localEvents S E ↦ ∫ σ, f σ A ∂κ := by
    funext A
    change (empiricalFieldAverage E π Λ κ).real (A : Set (S → E)) = _
    rw [measureReal_def, empiricalFieldAverage_apply_eq_lintegral π Λ κ (hmeasA A)]
    exact (integral_toReal
      ((Measure.measurable_coe (hmeasA A)).comp
        (measurable_periodicEmpiricalField π Λ)).aemeasurable
      (.of_forall fun σ ↦ measure_lt_top _ _)).symm
  have hae : ∀ᵐ σ ∂κ, f σ ∈ evalLocalEvents S E '' C := by
    refine ae_iff.2 (measure_mono_null (fun σ hσ ↦ ?_) hκ)
    intro hmem
    exact hσ ⟨periodicEmpiricalFieldL π hΛ σ, hmem, rfl⟩
  rw [hval]
  exact integral_mem_closedConvexHull_pi hae hint

end EvalEvents

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

/-- **Steps 1 and 2 of Georgii's proof of the upper bound (15.46), abstracted from the boundary
condition.** For a box `Λ = ∏_k [a_k, a_k + s_k]` of `ℤ^d` with a torus reduction `π` and a random
field `κ` with `𝓗_Λ(κ | λ^S) < ∞`, any real bound
`𝓗_Λ(κ | λ^S) + |Λ| ⟨κ °R_Λ, Φ⟩ + L ≤ q` turns, through Proposition (15.52)
(`specificRelativeEntropy_tileAverage_map_finsetRestrict`), into the bound

`𝓀(γ̄|Φ) ≤ |Λ|⁻¹ q + (P(Φ) − |Λ|⁻¹ L) + (⟨γ̄, Φ⟩ − ⟨κ °R_Λ, Φ⟩)`

for the randomly shifted independent-block field `γ̄` of the `Λ`-marginal of `κ`. With `κ` the
conditioned Gibbs distribution `γ^C_{Λ|ω}`, `q = −log γ^Φ_Λ(A|ω) + 3 r(Λ, Φ)` and
`L = log Z^Φ_Λ(ω)` this is `specificRelativeEntropy_tileAverage_cond_le`; with the periodic Gibbs
distribution, `q = −log °γ^Φ_Λ(A)` and `L = log °Z^Φ_Λ`, it is the corresponding statement of
`GibbsMeasure/Specification/PeriodicBoundaryGibbs.lean`, with no error term at all. -/
theorem specificRelativeEntropy_tileAverage_le_of_relativeEntropyIn_add_le
    {Φ : Potential (ι → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (a : ι → ℤ) (s : ι → ℕ) (π : (ι → ℤ) → (ι → ℤ)) (κ : Measure ((ι → ℤ) → E))
    [IsProbabilityMeasure κ]
    (hfin : relativeEntropyIn ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ)) κ
        (Measure.infinitePi fun _ ↦ ν) ≠ ⊤)
    {q L : ℝ}
    (hle : (relativeEntropyIn ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ)) κ
          (Measure.infinitePi fun _ ↦ ν)).toReal
        + (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ)
          * Φ.specificEnergy (empiricalFieldAverage E π (Finset.Icc a fun k ↦ a k + s k) κ)
        + L ≤ q) :
    Φ.specificRelativeEntropy ν (tileAverage (isComplement_Icc a s)
        (κ.map (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
      ≤ ((q / (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ)
          + (Φ.pressure ν - L / (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ))
          + (Φ.specificEnergy (tileAverage (isComplement_Icc a s)
                (κ.map (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
              - Φ.specificEnergy (empiricalFieldAverage E π (Finset.Icc a fun k ↦ a k + s k) κ))
          : ℝ) : EReal) := by
  have hΛne : (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).Nonempty :=
    Finset.nonempty_Icc.2 fun k ↦ by simp
  have hcard : (0 : ℝ) < #(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) := by
    exact_mod_cast hΛne.card_pos
  rw [specificRelativeEntropy_tileAverage_map_finsetRestrict ν a s _ hfin, EReal.coe_le_coe_iff]
  set N : ℝ := (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ) with hNdef
  set Rr : ℝ := (relativeEntropyIn
    ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ)) κ
    (Measure.infinitePi fun _ ↦ ν)).toReal with hRrdef
  set eR : ℝ := Φ.specificEnergy (empiricalFieldAverage E π (Finset.Icc a fun k ↦ a k + s k) κ)
    with heRdef
  have key : Rr / N + eR + L / N ≤ q / N := by
    have h2 : (Rr + N * eR + L) / N ≤ q / N := div_le_div_of_nonneg_right hle hcard.le
    have e1 : (Rr + N * eR + L) / N = Rr / N + eR + L / N := by field_simp
    rwa [e1] at h2
  linarith

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
  have hκprob : IsProbabilityMeasure
      ((Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
        (Finset.Icc a fun k ↦ a k + s k) ω)[|A]) := cond_isProbabilityMeasure hpos
  obtain ⟨hfin, hM1⟩ := relativeEntropyIn_cond_gibbsSpecification_ne_top_and_le ν hΦ hπ hΛne ω
    hA hpos
  refine (specificRelativeEntropy_tileAverage_le_of_relativeEntropyIn_add_le ν a s π _ hfin
    (L := Φ.logZ ν (Finset.Icc a fun k ↦ a k + s k) ω) hM1).trans (le_of_eq ?_)
  rw [EReal.coe_eq_coe_iff]
  ring

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

/-- Two sequences of random fields whose evaluations on every local event are asymptotically
equal have the same limits in the topology of local convergence. -/
theorem tendsto_withLocalConvergence_iff_of_tendsto_measureReal_sub {S E : Type*}
    [MeasurableSpace E] {ι' : Type*} {l : Filter ι'} {μs νs : ι' → WithLocalConvergence S E}
    (h : ∀ A ∈ localEvents S E, Tendsto (fun n ↦ ((μs n).toMeasure : Measure (S → E)).real A
      - ((νs n).toMeasure : Measure (S → E)).real A) l (𝓝 0))
    (μ : WithLocalConvergence S E) :
    Tendsto μs l (𝓝 μ) ↔ Tendsto νs l (𝓝 μ) := by
  rw [tendsto_withLocalConvergence_iff, tendsto_withLocalConvergence_iff]
  refine forall₂_congr fun A hA ↦ ?_
  rw [tendsto_measure_iff_tendsto_measureReal (μs := fun n ↦ (μs n).toMeasure)
      (μ := μ.toMeasure) A,
    tendsto_measure_iff_tendsto_measureReal (μs := fun n ↦ (νs n).toMeasure)
      (μ := μ.toMeasure) A]
  constructor
  · intro h1
    have := h1.sub (h A hA)
    simpa using this
  · intro h1
    have := h1.add (h A hA)
    simpa using this

/-- Two sequences of random fields that eventually agree on every local event have the same
limits in the topology of local convergence. -/
theorem tendsto_withLocalConvergence_iff_of_eventually_eq {S E : Type*}
    [MeasurableSpace E] {ι' : Type*} {l : Filter ι'} {μs νs : ι' → WithLocalConvergence S E}
    (h : ∀ A ∈ localEvents S E, ∀ᶠ n in l, ((μs n).toMeasure : Measure (S → E)) A
      = ((νs n).toMeasure : Measure (S → E)) A)
    (μ : WithLocalConvergence S E) :
    Tendsto μs l (𝓝 μ) ↔ Tendsto νs l (𝓝 μ) := by
  rw [tendsto_withLocalConvergence_iff, tendsto_withLocalConvergence_iff]
  exact forall₂_congr fun A hA ↦ Filter.tendsto_congr' (h A hA)

omit [Nonempty ι] [Finite E] [MeasurableSingletonClass E] in
/-- **The randomly shifted independent-block field `γ̄` of the `Λ`-marginal of a random field
`κ`**, for the box `Λ = ∏_k [a_k, a_k + s_k]`, read in the space of random fields with the
topology of local convergence. -/
def blockFieldL (a : ι → ℤ) (s : ι → ℕ) (κ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure κ] :
    WithLocalConvergence (ι → ℤ) E :=
  WithSetwiseTopology.ofMeasure ⟨tileAverage (isComplement_Icc a s)
    (κ.map (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict),
    isProbabilityMeasure_tileAverage _ _⟩

omit [Nonempty ι] [Finite E] [MeasurableSingletonClass E] in
@[simp] lemma toMeasure_blockFieldL (a : ι → ℤ) (s : ι → ℕ) (κ : Measure ((ι → ℤ) → E))
    [IsProbabilityMeasure κ] :
    (((blockFieldL a s κ).toMeasure : ProbabilityMeasure ((ι → ℤ) → E)) :
        Measure ((ι → ℤ) → E))
      = tileAverage (isComplement_Icc a s)
          (κ.map (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict) := rfl

/-- **Georgii's `κ °R_Λ`** read in the space of random fields with the topology of local
convergence. -/
def _root_.MeasureTheory.GibbsMeasure.empiricalFieldAverageL {S E : Type*} [AddCommGroup S]
    [MeasurableSpace E] (π : S → S) {Λ : Finset S} (hΛ : Λ.Nonempty) (κ : Measure (S → E))
    [IsProbabilityMeasure κ] : WithLocalConvergence S E :=
  haveI : NeZero (#Λ) := ⟨hΛ.card_pos.ne'⟩
  WithSetwiseTopology.ofMeasure ⟨empiricalFieldAverage E π Λ κ, inferInstance⟩

@[simp] lemma _root_.MeasureTheory.GibbsMeasure.toMeasure_empiricalFieldAverageL {S E : Type*}
    [AddCommGroup S] [MeasurableSpace E] (π : S → S) {Λ : Finset S} (hΛ : Λ.Nonempty)
    (κ : Measure (S → E)) [IsProbabilityMeasure κ] :
    (((empiricalFieldAverageL π hΛ κ).toMeasure : ProbabilityMeasure (S → E)) :
        Measure (S → E)) = empiricalFieldAverage E π Λ κ := rfl

omit [Nonempty ι] [Finite E] [MeasurableSingletonClass E] in
/-- **The two auxiliary fields of Step 2 have the same limits.** Along cubes `Λ_n` with sides
tending to infinity, the randomly shifted independent-block fields `γ̄_n` and the mean empirical
fields `κ_n °R_{Λ_n}` of any random fields `κ_n` converge to the same random fields, since they
agree asymptotically on every local event
(`tendsto_measureReal_tileAverage_sub_measureReal_empiricalFieldAverage`). -/
theorem tendsto_blockFieldL_iff_tendsto_empiricalFieldAverageL
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) {l : Filter ℕ} (hl : l ≤ atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    (κ : ℕ → Measure ((ι → ℤ) → E)) [∀ n, IsProbabilityMeasure (κ n)]
    (μ : WithLocalConvergence (ι → ℤ) E) :
    Tendsto (fun n ↦ blockFieldL (m n) (fun _ ↦ s n) (κ n)) l (𝓝 μ) ↔
      Tendsto (fun n ↦ empiricalFieldAverageL (π n) (hne n) (κ n)) l (𝓝 μ) := by
  refine tendsto_withLocalConvergence_iff_of_tendsto_measureReal_sub (fun A hA ↦ ?_) μ
  have h := tendsto_measureReal_tileAverage_sub_measureReal_empiricalFieldAverage hs hπ κ
    (fun n ↦ inferInstance) hA
  simpa only [toMeasure_blockFieldL, toMeasure_empiricalFieldAverageL] using h.mono_left hl

omit [Nonempty ι] [Finite E] [MeasurableSingletonClass E] in
/-- **Steps 2 and 3 of Georgii's proof of the upper bound (15.46): the limit of the block
fields.** Let `κ_n` be random fields concentrated on `{°R_{Λ_n} ∈ C}` whose randomly shifted
independent-block fields `γ̄_n` obey the finite-volume bound
`𝓀(γ̄_n|Φ) ≤ c + e_n + (⟨γ̄_n, Φ⟩ − ⟨κ_n °R_{Λ_n}, Φ⟩)` with `e_n → 0`, and let `μ` be the limit of
the mean empirical fields `κ_n °R_{Λ_n}` **along a filter `l ≤ atTop`**. Then `μ` is shift
invariant, lies in Georgii's `cx̄ C`, and `𝓀(μ|Φ) ≤ c`.

The block fields converge to the same `μ`
(`tendsto_blockFieldL_iff_tendsto_empiricalFieldAverageL`), so the energy correction vanishes by
the continuity of `⟨·, Φ⟩`; `μ ∈ cx̄ C` because each `κ_n °R_{Λ_n}` lies in Georgii's `cx̄ C`
(`evalLocalEvents_empiricalFieldAverage_mem_closedConvexHull`, Georgii's "basic observation");
and `𝓀(μ|Φ) ≤ c` because `𝓀(·|Φ)` is lower semicontinuous. This is the common core of the upper
bounds (15.46) for the configurational and for the periodic boundary conditions, and of the
cluster-point half of Corollary (15.58).

The filter `l` is `atTop` when the limit is taken along a subsequence; over an infinite state
space the topology of local convergence is not first countable, and the cluster point of Georgii's
Step 2 is only a limit along a finer filter (`MapClusterPt.exists_le_tendsto`). Nothing else
changes: every hypothesis and every step of the proof is filter-wise. -/
theorem mem_closedConvexHull_and_specificRelativeEntropy_le_of_tendsto
    (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {l : Filter ℕ} (hl : l ≤ atTop) (hlne : l.NeBot)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (κ : ℕ → Measure ((ι → ℤ) → E)) [∀ n, IsProbabilityMeasure (κ n)]
    (hcond : ∀ᶠ n in l, κ n {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}ᶜ = 0)
    {e : ℕ → ℝ} (he : Tendsto e l (𝓝 0))
    (hM : ∀ᶠ n in l, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
          ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict))
      ≤ ((c + e n + ((Φ : Potential (ι → ℤ) E).specificEnergy
            (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
              ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict))
          - (Φ : Potential (ι → ℤ) E).specificEnergy
            (empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n) (κ n))) : ℝ)
        : EReal))
    {μ : WithLocalConvergence (ι → ℤ) E}
    (hlim : Tendsto (fun n ↦ empiricalFieldAverageL (π n) (hne n) (κ n)) l (𝓝 μ)) :
    (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal) := by
  have := hlne
  have hblk : Tendsto (fun n ↦ blockFieldL (m n) (fun _ ↦ s n) (κ n)) l (𝓝 μ) :=
    (tendsto_blockFieldL_iff_tendsto_empiricalFieldAverageL hs hl hπ hne κ μ).2 hlim
  refine ⟨?_, ?_, ?_⟩
  · -- `μ` is shift invariant
    refine (isClosed_setOf_mem_invariantFields (shiftGroup (ι → ℤ) E)).mem_of_tendsto hblk
      (.of_forall fun k ↦ ?_)
    exact tileAverage_mem_invariantFields_shiftGroup _ _
  · -- `μ` lies in the closed convex hull
    refine isClosed_closedConvexHull.mem_of_tendsto
      (WithSetwiseTopology.continuous_evalReal.continuousAt.tendsto.comp hlim) ?_
    filter_upwards [hcond] with k hk
    exact evalLocalEvents_empiricalFieldAverage_mem_closedConvexHull (hne k) (κ k) hk
  · -- the excess free energy of the limit is at most `c`
    by_contra hgt
    push Not at hgt
    obtain ⟨c', hcc', hc'⟩ := EReal.exists_between_coe_real hgt
    have hEnergy : Tendsto (fun k ↦ (Φ : Potential (ι → ℤ) E).specificEnergy
        (tileAverage (isComplement_Icc (m k) fun _ ↦ s k)
          ((κ k).map (Finset.Icc (m k) fun j ↦ m k j + s k : Finset (ι → ℤ)).restrict))
        - (Φ : Potential (ι → ℤ) E).specificEnergy
          (empiricalFieldAverage E (π k) (Finset.Icc (m k) fun j ↦ m k j + s k) (κ k)))
        l (𝓝 0) := by
      have h1 := (Potential.continuous_specificEnergy
        (Φ := (Φ : Potential (ι → ℤ) E))).continuousAt.tendsto.comp hblk
      have h2 := (Potential.continuous_specificEnergy
        (Φ := (Φ : Potential (ι → ℤ) E))).continuousAt.tendsto.comp hlim
      have h3 := h1.sub h2
      simpa using h3
    have hε : Tendsto (fun k ↦ c + e k + ((Φ : Potential (ι → ℤ) E).specificEnergy
        (tileAverage (isComplement_Icc (m k) fun _ ↦ s k)
          ((κ k).map (Finset.Icc (m k) fun j ↦ m k j + s k : Finset (ι → ℤ)).restrict))
        - (Φ : Potential (ι → ℤ) E).specificEnergy
          (empiricalFieldAverage E (π k) (Finset.Icc (m k) fun j ↦ m k j + s k) (κ k)))) l
        (𝓝 c) := by
      simpa using (tendsto_const_nhds.add he).add hEnergy
    have hlsc := Potential.BTheta.lowerSemicontinuous_specificRelativeEntropy ν Φ μ c' hc'
    have hev1 : ∀ᶠ k in l, (c' : EReal) < (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (tileAverage (isComplement_Icc (m k) fun _ ↦ s k)
          ((κ k).map (Finset.Icc (m k) fun j ↦ m k j + s k : Finset (ι → ℤ)).restrict)) :=
      hblk.eventually hlsc
    have hev2 : ∀ᶠ k in l, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (tileAverage (isComplement_Icc (m k) fun _ ↦ s k)
          ((κ k).map (Finset.Icc (m k) fun j ↦ m k j + s k : Finset (ι → ℤ)).restrict))
        < (c' : EReal) := by
      have hcc'R : c < c' := by exact_mod_cast hcc'
      filter_upwards [hε.eventually (eventually_lt_nhds hcc'R), hM] with k hk hMk
      exact lt_of_le_of_lt hMk (EReal.coe_lt_coe_iff.2 hk)
    obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
    exact absurd hk1 (not_lt.2 hk2.le)

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Steps 2 and 3 of Georgii's proof of the upper bound (15.46): the cluster point, over a
standard Borel state space.** Suppose that along a sequence of cubes `Λ_n` with sides tending to
infinity there are boundary conditions `ω_n` for which
`γ^Φ_{Λ_n}(°R_{Λ_n} ∈ C | ω_n) > e^{−c|Λ_n|}`. Then there is a shift-invariant random field `μ` in
Georgii's `cx̄ C` with `𝓀(μ|Φ) ≤ c`.

This is Georgii's argument by contradiction in Step 2, verbatim: the finite-volume bound forces
all the block fields `γ̄_n` into one sublevel set `{𝓀(·|Φ) ≤ M}` of the excess free energy, which
is **compact** for the topology of local convergence over a standard Borel state space
(`Potential.BTheta.isCompact_setOf_specificRelativeEntropy_le`, Georgii's Proposition (15.14)
applied as in the remark after (15.45)), so the block fields have a cluster point. The topology of
local convergence is not first countable over an infinite state space, so the cluster point is a
limit along a finer filter rather than along a subsequence (`MapClusterPt.exists_le_tendsto`);
`mem_closedConvexHull_and_specificRelativeEntropy_le_of_tendsto` is stated for a filter for that
reason.

The finite-volume input is `specificRelativeEntropy_tileAverage_cond_le`, whose two correction
terms vanish, the first by Theorem (15.30)(a) uniformly in the boundary condition and the second
by the estimate (15.25).

The hypothesis `hAmeas` is Georgii's `C ∈ 𝓔(𝓟_Θ)`, in the form in which it is used: it is
`measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem_of_evalEvents` for a `C` in the
evaluation σ-algebra, and `measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem` — with
no hypothesis on `C` — over a finite state space. -/
theorem exists_mem_closedConvexHull_specificRelativeEntropy_le_of_measurableSet
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
    (ω : ℕ → (ι → ℤ) → E)
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
  set κ : ℕ → Measure ((ι → ℤ) → E) := fun n ↦
    (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
      (Finset.Icc (m n) fun k ↦ m n k + s n) (ω n))[|
        {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}] with hκdef
  have hκprob : ∀ n, IsProbabilityMeasure (κ n) := fun n ↦ cond_isProbabilityMeasure (hpos n)
  have hcond : ∀ n, κ n {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}ᶜ = 0 := by
    intro n
    rw [hκdef]
    have hm := cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E)
      (Δ := ((Finset.Icc (m n) fun j ↦ m n j + s n : Finset (ι → ℤ)) : Set (ι → ℤ)))
      _ (hAmeas n)
    rw [cond_apply hm, Set.inter_compl_self, measure_empty, mul_zero]
  -- the finite-volume estimate, with the two correction terms
  set e : ℕ → ℝ := fun n ↦ ((Φ : Potential (ι → ℤ) E).pressure ν
      - (Φ : Potential (ι → ℤ) E).logZ ν (Finset.Icc (m n) fun k ↦ m n k + s n) (ω n)
        / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)))
    + 3 * (Φ : Potential (ι → ℤ) E).tail (Finset.Icc (m n) fun k ↦ m n k + s n)
        (Finset.Icc (m n) fun k ↦ m n k + s n)
      / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) with hedef
  have hM : ∀ n, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
      (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
        ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict))
      ≤ ((c + e n + ((Φ : Potential (ι → ℤ) E).specificEnergy
            (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
              ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict))
          - (Φ : Potential (ι → ℤ) E).specificEnergy
            (empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n) (κ n))) : ℝ)
        : EReal) := by
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
    rw [hedef]
    linarith
  -- the correction terms vanish
  have hside : ∀ k, Tendsto (fun n ↦ (fun j ↦ m n j + (s n : ℤ)) k - m n k) atTop atTop := by
    intro k
    have h : Tendsto (fun n ↦ ((s n : ℤ))) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
    simpa using h
  have he : Tendsto e atTop (𝓝 0) := by
    have hZ := Potential.tendsto_logZ_div_card_pressure (Φ := (Φ : Potential (ι → ℤ) E)) ν hΦ
      hside ω
    have hT := Potential.tendsto_tail_div_card (Φ := (Φ : Potential (ι → ℤ) E)) hΦ hside
    have h := ((tendsto_const_nhds (x := (Φ : Potential (ι → ℤ) E).pressure ν)).sub hZ).add
      (hT.const_mul 3)
    simp only [sub_self, mul_zero, add_zero] at h
    refine h.congr fun n ↦ ?_
    rw [hedef]
    ring
  -- the block fields eventually lie in one compact sublevel set of the excess free energy
  set M : ℝ := c + 1 + 2 * ((Φ : Potential (ι → ℤ) E).normAt 0).toReal with hMdef
  set K : Set (WithLocalConvergence (ι → ℤ) E) :=
    {μ' : WithLocalConvergence (ι → ℤ) E | (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
      (μ'.toMeasure : Measure ((ι → ℤ) → E)) ≤ (M : EReal)} with hKdef
  have hKcompact : IsCompact K :=
    Potential.BTheta.isCompact_setOf_specificRelativeEntropy_le ν Φ M
  have hmemK : ∀ᶠ n in atTop, blockFieldL (m n) (fun _ ↦ s n) (κ n) ∈ K := by
    filter_upwards [he.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    change (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
      (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
        ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict))
      ≤ (M : EReal)
    refine (hM n).trans (EReal.coe_le_coe_iff.2 ?_)
    have : NeZero (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))) :=
      ⟨(hne n).card_pos.ne'⟩
    have h1 := abs_le.1 (Potential.abs_specificEnergy_le (Φ := (Φ : Potential (ι → ℤ) E))
      (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
        ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict)))
    have h2 := abs_le.1 (Potential.abs_specificEnergy_le (Φ := (Φ : Potential (ι → ℤ) E))
      (empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n) (κ n)))
    rw [hMdef]
    linarith [h1.2, h2.1, hn.le]
  -- a cluster point of the block fields, by compactness of that sublevel set
  obtain ⟨μ, -, hclus⟩ := hKcompact (f := Filter.map
    (fun n ↦ blockFieldL (m n) (fun _ ↦ s n) (κ n)) atTop) (Filter.le_principal_iff.2 hmemK)
  obtain ⟨l, hl, hlne, hlim⟩ := MapClusterPt.exists_le_tendsto hclus
  have hemp : Tendsto (fun n ↦ empiricalFieldAverageL (π n) (hne n) (κ n)) l (𝓝 μ) :=
    (tendsto_blockFieldL_iff_tendsto_empiricalFieldAverageL hs hl hπ hne κ μ).1 hlim
  exact ⟨μ, mem_closedConvexHull_and_specificRelativeEntropy_le_of_tendsto ν Φ hs hπ hne hl hlne
    κ (.of_forall hcond) (he.mono_left hl) (.of_forall hM) hemp⟩

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii's `C ∈ 𝓔(𝓟_Θ)` in the cluster-point lemma.** Over a standard Borel state space the
event `{°R_Λ ∈ C}` is a cylinder event as soon as `C` lies in the evaluation σ-algebra, which is
Georgii's hypothesis on `C` in Theorem (15.45). -/
theorem exists_mem_closedConvexHull_specificRelativeEntropy_le_of_evalEvents
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hC : MeasurableSet[evalEvents (ι → ℤ) E] C) (ω : ℕ → (ι → ℤ) → E)
    (hω : ∀ n, ENNReal.ofReal (Real.exp (-(c *
          #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)))))
        < Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
            (Finset.Icc (m n) fun k ↦ m n k + s n) (ω n)
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}) :
    ∃ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal) :=
  exists_mem_closedConvexHull_specificRelativeEntropy_le_of_measurableSet ν Φ hs hπ hne
    (fun n ↦ measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem_of_evalEvents
      (hπ n) (hne n) hC) ω hω

/-- **The cluster point over a finite state space**, where `{°R_Λ ∈ C}` is a cylinder event for
*every* `C` whatsoever
(`measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem`), so that Georgii's hypothesis
`C ∈ 𝓔(𝓟_Θ)` carries no information. -/
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
  have : Nonempty E := Measure.nonempty_of_neZero ν
  exact exists_mem_closedConvexHull_specificRelativeEntropy_le_of_measurableSet ν Φ hs hπ hne
    (fun n ↦ measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem (hπ n) (hne n) C) ω hω

omit [Finite E] [MeasurableSingletonClass E] in
/-- **The upper bound (15.46) in exponential form, with Georgii's `cx̄ C` on the right, over a
standard Borel state space.** If `c` is strictly below the excess free energy of every
shift-invariant random field in `cx̄ C`, then eventually `γ^Φ_Λ(°R_Λ ∈ C | ω) ≤ e^{−c |Λ|}`,
*uniformly in the boundary condition* `ω`. This is the contrapositive of the cluster-point lemma
`exists_mem_closedConvexHull_specificRelativeEntropy_le_of_measurableSet`; Georgii takes an `ω` at
which a fixed fraction of the supremum in (15.46) is attained, which over a general state space is
the way to get the uniformity, and here amounts to the choice of a boundary condition for each
volume in which the bound fails. -/
theorem eventually_gibbsSpecification_setOf_periodicEmpiricalFieldL_mem_le_of_measurableSet
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
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
  obtain ⟨μ, hμinv, hμhull, hμle⟩ :=
    exists_mem_closedConvexHull_specificRelativeEntropy_le_of_measurableSet ν Φ
      (m := fun j ↦ m (φ j)) (s := fun j ↦ s (φ j)) (hs.comp hφ.tendsto_atTop)
      (G := fun j ↦ G (φ j)) (π := fun j ↦ π (φ j)) (fun j ↦ hπ (φ j)) (fun j ↦ hne (φ j))
      (fun j ↦ hAmeas (φ j)) ω hω
  exact absurd hμle (not_le.2 (hc μ hμinv hμhull))

omit [Finite E] [MeasurableSingletonClass E] in
/-- **The upper bound (15.46) in exponential form under Georgii's hypothesis `C ∈ 𝓔(𝓟_Θ)`.** -/
theorem eventually_gibbsSpecification_setOf_periodicEmpiricalFieldL_mem_le_of_evalEvents
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hC : MeasurableSet[evalEvents (ι → ℤ) E] C)
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
            (-(c * #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))))) :=
  eventually_gibbsSpecification_setOf_periodicEmpiricalFieldL_mem_le_of_measurableSet ν Φ hs hπ hne
    (fun n ↦ measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem_of_evalEvents
      (hπ n) (hne n) hC) hc

/-- **The upper bound (15.46) in exponential form over a finite state space**, where `{°R_Λ ∈ C}`
is a cylinder event for every `C` whatsoever. -/
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
  exact eventually_gibbsSpecification_setOf_periodicEmpiricalFieldL_mem_le_of_measurableSet ν Φ
    hs hπ hne
    (fun n ↦ measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem (hπ n) (hne n) C) hc

omit [Nonempty ι] [Finite E] [MeasurableSingletonClass E] in
/-- The `EReal` bookkeeping of (15.46): if `x ≤ e^{−c |Λ|}` then `log x / |Λ| ≤ −c`. -/
lemma log_div_natCast_le_neg_of_le_ofReal_exp {x : ℝ≥0∞} {N : ℕ} (hN : N ≠ 0) {c : ℝ}
    (h : x ≤ ENNReal.ofReal (Real.exp (-(c * N)))) :
    ENNReal.log x / ((N : ℕ) : EReal) ≤ ((-c : ℝ) : EReal) := by
  have hlog : ENNReal.log x ≤ ((-(c * N) : ℝ) : EReal) := by
    refine (ENNReal.log_monotone h).trans (le_of_eq ?_)
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hcard : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  refine (EReal.div_le_div_right_of_nonneg (c := ((N : ℕ) : EReal)) (Nat.cast_nonneg' _)
    hlog).trans (le_of_eq ?_)
  rw [← EReal.coe_natCast, ← EReal.coe_div, EReal.coe_eq_coe_iff]
  field_simp

/-- **Georgii's Step 3 assembled**: an extended real `L` bounded by `−c` for every real `c` below
`inf {𝓀(μ|Φ) : μ ∈ 𝓟_Θ ∩ cx̄ C}` is bounded by `−inf_{C̄} 𝓀(·|Φ)`. The passage from `cx̄ C` to
`C̄` is Georgii (15.54), `iInf_closedConvexHull_eq_iInf_closure_ereal`, which needs `𝓀(·|Φ)`
concave on `𝓟_Θ` (`smul_specificRelativeEntropy_add_smul_specificRelativeEntropy_le`, hence
`d ≥ 1`), lower semicontinuous, and bounded below (Corollary (15.35)). -/
theorem le_neg_iInf_closure_specificRelativeEntropy_of_forall_lt
    (Φ : Potential.BTheta (ι → ℤ) E) {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hC : C ⊆ invariantRandomFields (ι → ℤ) E) {L : EReal}
    (hstep : ∀ c : ℝ, (c : EReal) < (⨅ μ ∈ {μ | μ ∈ invariantRandomFields (ι → ℤ) E ∧
        evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)},
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E))) → L ≤ ((-c : ℝ) : EReal)) :
    L ≤ -⨅ μ ∈ closure C, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
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
  change L ≤ -⨅ μ ∈ closure C, 𝒜 μ
  rw [← h1554]
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

omit [Nonempty ι] [Finite E] [MeasurableSingletonClass E] in
/-- The `EReal` bookkeeping of Step 4: an extended real `L` bounded by `−c` for every real `c`
strictly below `T` is bounded by `−T`. -/
lemma le_neg_of_forall_lt {L T : EReal} (h : ∀ c : ℝ, (c : EReal) < T → L ≤ ((-c : ℝ) : EReal)) :
    L ≤ -T := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real hcon
  have hy : ((-y : ℝ) : EReal) < T := by
    rw [EReal.coe_neg]
    exact EReal.neg_lt_comm.1 hy1
  have := h (-y) hy
  rw [neg_neg] at this
  exact absurd hy2 (not_lt.2 this)

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii Theorem (15.45), the upper bound (15.46) with `cx̄ C` on the right, over a standard
Borel state space.** For `Φ ∈ ℬ_Θ` and a set `C` of random fields whose event `{°R_Λ ∈ C}` is a
cylinder event of the volume (`hAmeas`, Georgii's `C ∈ 𝓔(𝓟_Θ)`),

`limsup_{|Λ| → ∞} |Λ|⁻¹ log sup_ω γ^Φ_Λ(°R_Λ ∈ C | ω) ≤ − inf {𝓀(ν|Φ) : ν ∈ 𝓟_Θ ∩ cx̄ C}`,

along any sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` of `ℤ^d` whose side lengths tend to
infinity, with arbitrary torus reductions `π_n`.

This is Georgii's Steps 1 and 2 in full: `cx̄ C` is the closed convex hull *in the topology of
local convergence*, and no assumption beyond `StandardBorelSpace E` is made on `E`. Step 3 —
Georgii's (15.54), replacing `cx̄ C` by `C̄` — is a separate, Choquet-theoretic statement; see
`limsup_log_iSup_gibbsSpecification_div_card_le` for the case in which it is available, and the
module documentation for what it costs. When `C` is *convex* the two right-hand sides agree, since
then `cx̄ C = C̄`. -/
theorem limsup_log_iSup_gibbsSpecification_div_card_le_closedConvexHull_of_measurableSet
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}) :
    Filter.limsup (fun n ↦ ENNReal.log (⨆ ω : (ι → ℤ) → E,
          Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
            (Finset.Icc (m n) fun k ↦ m n k + s n) ω
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ ∈ {μ : WithLocalConvergence (ι → ℤ) E |
          μ ∈ invariantRandomFields (ι → ℤ) E ∧
          evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)},
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  refine le_neg_of_forall_lt fun c hcm ↦ ?_
  have hc : ∀ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) →
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) →
      (c : EReal) < (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) := fun μ hμ hμ' ↦
    lt_of_lt_of_le hcm (iInf₂_le μ ⟨hμ, hμ'⟩)
  have hev := eventually_gibbsSpecification_setOf_periodicEmpiricalFieldL_mem_le_of_measurableSet
    ν Φ hs hπ hne hAmeas hc
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with n hn
  exact log_div_natCast_le_neg_of_le_ofReal_exp (hne n).card_pos.ne' (iSup_le hn)

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii Theorem (15.45), the upper bound (15.46) with `cx̄ C` on the right, under Georgii's
hypothesis `C ∈ 𝓔(𝓟_Θ)`.** -/
theorem limsup_log_iSup_gibbsSpecification_div_card_le_closedConvexHull
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hC : MeasurableSet[evalEvents (ι → ℤ) E] C) :
    Filter.limsup (fun n ↦ ENNReal.log (⨆ ω : (ι → ℤ) → E,
          Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
            (Finset.Icc (m n) fun k ↦ m n k + s n) ω
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ ∈ {μ : WithLocalConvergence (ι → ℤ) E |
          μ ∈ invariantRandomFields (ι → ℤ) E ∧
          evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)},
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) :=
  limsup_log_iSup_gibbsSpecification_div_card_le_closedConvexHull_of_measurableSet ν Φ hs hπ hne
    fun n ↦ measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem_of_evalEvents
      (hπ n) (hne n) hC

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii Theorem (15.45), the upper bound (15.46) for a convex `C`, over a standard Borel
state space.** For a *convex* `C` — Georgii's `cx̄ C` is then its closure — the bound holds in
Georgii's own form,

`limsup_{|Λ| → ∞} |Λ|⁻¹ log sup_ω γ^Φ_Λ(°R_Λ ∈ C | ω) ≤ − inf_{ν ∈ C̄} 𝓀(ν|Φ)`,

with `C̄` the closure in the topology of local convergence, with no finiteness of the state space
and with no appeal to Choquet theory: Step 3 is vacuous. Convexity is expressed through the
evaluation embedding, as Georgii's `cx̄` is. -/
theorem limsup_log_iSup_gibbsSpecification_div_card_le_of_convex
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
    (hCconv : Convex ℝ (evalLocalEvents (ι → ℤ) E '' C)) :
    Filter.limsup (fun n ↦ ENNReal.log (⨆ ω : (ι → ℤ) → E,
          Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential (ι → ℤ) E)) ν 1
            (Finset.Icc (m n) fun k ↦ m n k + s n) ω
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ ∈ closure C, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  refine (limsup_log_iSup_gibbsSpecification_div_card_le_closedConvexHull_of_measurableSet ν Φ hs
    hπ hne hAmeas).trans (EReal.neg_le_neg_iff.2 (le_iInf₂ fun μ hμ ↦ ?_))
  -- for a convex `C` the closed convex hull of its image is the closure of its image, and the
  -- evaluation is a topological embedding, so `μ ∈ C̄`
  have hcl : evalLocalEvents (ι → ℤ) E μ ∈ closure (evalLocalEvents (ι → ℤ) E '' C) := by
    have hhull : closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)
        = closure (evalLocalEvents (ι → ℤ) E '' C) := by
      rw [closedConvexHull_eq_closure_convexHull, hCconv.convexHull_eq]
    exact hhull ▸ hμ.2
  have hμC : μ ∈ closure C := by
    rw [isEmbedding_evalLocalEvents.closure_eq_preimage_closure_image]
    exact hcl
  exact iInf₂_le μ hμC

/-- **Georgii Theorem (15.45), the upper bound (15.46).** For `Φ ∈ ℬ_Θ` and a set `C ⊆ 𝓟_Θ` of
shift-invariant random fields,

`limsup_{|Λ| → ∞} |Λ|⁻¹ log sup_ω γ^Φ_Λ(°R_Λ ∈ C | ω) ≤ − inf_{ν ∈ C̄} 𝓀(ν|Φ)`,

the limit being taken along any sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` of `ℤ^d` whose side
lengths tend to infinity, with arbitrary torus reductions `π_n` defining the periodic empirical
field `°R_{Λ_n}`.

## Hypotheses

Georgii states (15.45) for a *standard Borel* state space. Everything but Step 3 is proved there;
`limsup_log_iSup_gibbsSpecification_div_card_le_closedConvexHull` is the bound with `cx̄ C` on the
right over a standard Borel state space, and
`limsup_log_iSup_gibbsSpecification_div_card_le_of_convex` is this very statement for a convex
`C`. What the present statement adds is **Step 3** for a general `C`, the passage from `cx̄ C` to
`C̄`. It rests on the Choquet-theoretic `iInf_closedConvexHull_eq_iInf_closure_ereal`, which needs
`𝓟_Θ` to be a compact convex subset of a locally convex space *in the topology in which the
closure `C̄` is taken*; over a finite state space the algebra `𝓕⁰` of all local events is
countable and the topology of local convergence is itself compact metrizable, so no change of
topology is needed. Over an infinite state space Georgii's change of topology does not deliver the
`𝓛`-closure; see the module documentation.

Finiteness of `E` also makes `{°R_Λ ∈ C}` a cylinder event for *every* `C` whatsoever
(`measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem`), so Georgii's hypothesis
`C ∈ 𝓔(𝓟_Θ)` carries no information here and only `C ⊆ 𝓟_Θ` is assumed.

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
  refine le_neg_iInf_closure_specificRelativeEntropy_of_forall_lt ν Φ hC fun c hcm ↦ ?_
  have hc : ∀ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) →
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) →
      (c : EReal) < (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) := fun μ hμ hμ' ↦
    lt_of_lt_of_le hcm (iInf₂_le μ ⟨hμ, hμ'⟩)
  have hev := eventually_gibbsSpecification_setOf_periodicEmpiricalFieldL_mem_le ν Φ hs hπ hne hc
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with n hn
  exact log_div_natCast_le_neg_of_le_ofReal_exp (hne n).card_pos.ne' (iSup_le hn)

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii Theorem (15.45), the "in particular" clause, over a standard Borel state space.**
The bound with `cx̄ C` on the right holds with the finite-volume Gibbs distributions
`γ^Φ_Λ(·|ω)` replaced by *any* Gibbs measure `μ ∈ 𝒢(Φ)` — no shift invariance of `μ` is required:

`limsup_{|Λ| → ∞} |Λ|⁻¹ log μ(°R_Λ ∈ C) ≤ − inf {𝓀(ν|Φ) : ν ∈ 𝓟_Θ ∩ cx̄ C}`.

Georgii obtains it "by integrating over `ω`": the DLR equation writes `μ(°R_Λ ∈ C)` as the
`μ`-average of `γ^Φ_Λ(°R_Λ ∈ C|ω)`, which is at most the supremum over `ω`. -/
theorem limsup_log_isGibbsMeasure_div_card_le_closedConvexHull_of_measurableSet
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
    {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : (Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1).IsGibbsMeasure μ) :
    Filter.limsup (fun n ↦
        ENNReal.log (μ {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
          / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ' ∈ {μ' : WithLocalConvergence (ι → ℤ) E |
          μ' ∈ invariantRandomFields (ι → ℤ) E ∧
          evalLocalEvents (ι → ℤ) E μ' ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)},
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ'.toMeasure : Measure ((ι → ℤ) → E)) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  refine le_trans (Filter.limsup_le_limsup (.of_forall fun n ↦ ?_))
    (limsup_log_iSup_gibbsSpecification_div_card_le_closedConvexHull_of_measurableSet ν Φ hs hπ
      hne hAmeas)
  refine EReal.div_le_div_right_of_nonneg (Nat.cast_nonneg' _) (ENNReal.log_monotone ?_)
  -- the DLR equation bounds `μ(A)` by the supremum of `γ^Φ_Λ(A|ω)`
  set Λ : Finset (ι → ℤ) := Finset.Icc (m n) fun k ↦ m n k + s n with hΛdef
  set A : Set ((ι → ℤ) → E) := {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C} with hAdef
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ (hAmeas n)
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
