/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.BoundaryLaw
public import GibbsMeasure.Specification.MarkovInt
public import GibbsMeasure.Specification.CountingKernel
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Acyclic
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Georgii §12.1: Markov chains and boundary laws on trees

Sites `S` are the vertices of a locally finite tree `G : SimpleGraph S` (`G.IsTree`,
`G.LocallyFinite`), the state space `E` is countable with the discrete σ-algebra
(`Countable E`, `MeasurableSingletonClass E`), and the a priori measure is counting measure.
Georgii assumes `E` finite throughout Chapter 12; the two places where countability is not enough
are made explicit hypotheses (`IsTransferFamily.sigmaFiniteLambdaZ_ne_top`,
`IsBoundaryLaw.mass_ne_top`), both automatic for finite `E` (`isTransferFamily_of_finite`,
`IsBoundaryLaw.of_finite`).

## Main declarations

The graph combinatorics (`SimpleGraph.bondsOf`, `SimpleGraph.outerBoundary`,
`SimpleGraph.anchor`, `SimpleGraph.past`, `SimpleGraph.hull`, `SimpleGraph.connected_induction`)
lives in `GibbsMeasure/Mathlib/Combinatorics/SimpleGraph/`, and the counting-measure calculus
(`cyl`, `lintegral_lambdaCount`, …) in `GibbsMeasure/Specification/CountingKernel.lean`.

* `IsMarkovSpecification` — **Definition (12.1)**; `isMarkovSpecification_transferSpecification`.
* `IsMarkovChain` — **Definition (12.2)** (via conditional expectations);
  `IsMarkovChain.measure_preimage_inter_cyl` is its finite-volume content, and
  `IsMarkovChain.measure_cyl_union_eq_mul_prod` the consequence of **(12.4)** used in (12.12)(b).
* `transferWeight`, `IsTransferFamily`, `transferSpecification` — the positive Markov
  specification **(12.8)** of a family of transfer matrices **(12.9)**, as the λ-specification of
  counting measure; `transferSpecification_apply_cyl` is (12.8).
* `IsBoundaryLaw` — **Definition (12.10)**; `IsBoundaryLaw.eq_prod_div_of_normalized` is
  **(12.15)** and `isBoundaryLaw_const_iff` is **(12.16)** on the Cayley tree (the boundary-law
  side of **Corollary (12.17)**).
* `Markov.IsBoundaryLaw.isBoundaryLaw_hasse_int` — **Example (12.11)**: a boundary law of
  Definition (11.8) on `ℤ = SimpleGraph.hasse ℤ` is one of Definition (12.10).
* `boundaryLawWeight`, `volumeLaw`, `normalizedVolumeLaw`, `boundaryLawFDD`,
  `boundaryLawMeasure` — the measure **(12.13)** by Kolmogorov extension; the consistency
  **(12.14)** is `IsBoundaryLaw.exists_lintegral_boundaryLawWeight_insert` /
  `IsBoundaryLaw.normalizedVolumeLaw_map_restrict_eq`; `IsBoundaryLaw.boundaryLawMeasure_cyl` is
  (12.13) and `IsBoundaryLaw.eq_boundaryLawMeasure_of_forall_cyl` its uniqueness.
* **Theorem (12.12)(a)**: `IsBoundaryLaw.isGibbsMeasure_transferSpecification_boundaryLawMeasure`
  (`μ ∈ 𝒢(γ^Q)`) and `IsBoundaryLaw.isMarkovChain_boundaryLawMeasure` (`μ` is a Markov chain,
  with transition matrices `boundaryLawTransition`).
* **Theorem (12.12)(b)**: `IsMarkovChain.isBoundaryLaw_chainBoundaryLaw` and
  `IsMarkovChain.eq_boundaryLawMeasure` — every Markov chain in `𝒢(γ^Q)` is the measure (12.13) of
  the boundary law `chainBoundaryLaw`, `ℓ_{ij}(x) = P_{ji}(a, x) / Q_{ji}(a, x)`.

Not formalised here: Theorem (12.6) (extreme Gibbs measures of Markov specifications are Markov
chains, which needs the backward martingale convergence theorem), the uniqueness up to a factor
in (12.12)(b), Comments (12.3), and Corollary (12.18).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure.Tree

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] [Countable E]
  [MeasurableSingletonClass E]

local notation "λ₀" => Specification.sigmaFiniteLambdaFun (S := S) (E := E) Measure.count

/-! ## Georgii's `γ^Q` on a locally finite graph: transfer matrices along the bonds

A family `Q_{ij}` of matrices on `E` indexed by the oriented bonds `ij` of a locally finite graph
`G`, with `Q_{ij}(x, y) = Q_{ji}(y, x)` (Georgii (12.9)); the bond function `Q_b(σ) = Q_{ij}(σ_i,
    σ_j)`
for `b = {i, j}`, and the weight `∏_{b ∩ Λ ≠ ∅} Q_b(σ)` of (12.8). Nothing in this section uses the
tree property. -/

section TransferFamily

variable (G : SimpleGraph S) [G.LocallyFinite] (Q : S → S → E → E → ℝ≥0∞)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- Georgii (12.9): a family of matrices indexed by oriented bonds with `Q_{ij}(x,y) = Q_{ji}(y,x)`
is a function `Q_b` of the unoriented bond `b = {i, j}` and the two spins on it. -/
def bondWeight (hQ : ∀ i j x y, Q i j x y = Q j i y x) (σ : S → E) : Sym2 S → ℝ≥0∞ :=
  Sym2.lift ⟨fun i j ↦ Q i j (σ i) (σ j), fun i j ↦ hQ i j _ _⟩

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
@[simp] lemma bondWeight_mk (hQ : ∀ i j x y, Q i j x y = Q j i y x) (σ : S → E) (i j : S) :
    bondWeight Q hQ σ s(i, j) = Q i j (σ i) (σ j) := rfl

omit [DecidableEq S] in
lemma measurable_bondWeight (hQ : ∀ i j x y, Q i j x y = Q j i y x) (b : Sym2 S) :
    Measurable fun σ : S → E ↦ bondWeight Q hQ σ b :=
  Sym2.inductionOn b fun i j ↦ measurable_pair (Q i j) i j

/-- **Georgii (12.8) before normalisation.** The weight `∏_{b ∩ Λ ≠ ∅} Q_b(σ)` of the bonds
meeting `Λ`; for `Q_b = e^{-Φ_b}` this is the Boltzmann factor of a nearest-neighbour potential. -/
def transferWeight (hQ : ∀ i j x y, Q i j x y = Q j i y x) (Λ : Finset S) (σ : S → E) : ℝ≥0∞ :=
  ∏ b ∈ G.bondsOf Λ, bondWeight Q hQ σ b

variable {Q} (hQ : ∀ i j x y, Q i j x y = Q j i y x)

lemma measurable_transferWeight (Λ : Finset S) : Measurable (transferWeight G Q hQ Λ) :=
  Finset.measurable_prod _ fun b _ ↦ measurable_bondWeight Q hQ b

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]

lemma transferWeight_pos (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) (Λ : Finset S)
    (σ : S → E) : 0 < transferWeight G Q hQ Λ σ := by
  refine pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b hb ↦ ?_)
  have he := (SimpleGraph.mem_bondsOf.1 hb).1
  revert he
  refine Sym2.inductionOn b fun i j he ↦ ?_
  exact (hpos (G.mem_edgeSet.1 he) _ _).ne'

lemma transferWeight_ne_top (htop : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤) (Λ : Finset S)
    (σ : S → E) : transferWeight G Q hQ Λ σ ≠ ⊤ := by
  refine ENNReal.prod_ne_top fun b hb ↦ ?_
  have he := (SimpleGraph.mem_bondsOf.1 hb).1
  revert he
  refine Sym2.inductionOn b fun i j he ↦ ?_
  exact htop (G.mem_edgeSet.1 he) _ _

omit [DecidableEq S] in
/-- The bond weight of a bond depends only on the spins at its endpoints. -/
lemma bondWeight_congr {σ τ : S → E} {b : Sym2 S} (h : ∀ k ∈ b, σ k = τ k) :
    bondWeight Q hQ σ b = bondWeight Q hQ τ b := by
  revert h
  refine Sym2.inductionOn b fun i j h ↦ ?_
  rw [bondWeight_mk, bondWeight_mk, h i (Sym2.mem_mk_left i j), h j (Sym2.mem_mk_right i j)]

/-- The endpoints of a bond meeting `Λ` lie in `Λ ∪ ∂Λ`. -/
lemma mem_union_outerBoundary_of_mem_bondsOf {Λ : Finset S} {b : Sym2 S} (hb : b ∈ G.bondsOf Λ)
    {k : S} (hk : k ∈ b) : k ∈ Λ ∪ G.outerBoundary Λ := by
  obtain ⟨he, i, hi, hib⟩ := SimpleGraph.mem_bondsOf.1 hb
  by_cases hki : k = i
  · exact hki ▸ Finset.mem_union_left _ hi
  · have : b = s(i, k) := (Sym2.mem_and_mem_iff (Ne.symm hki)).1 ⟨hib, hk⟩
    rw [this, SimpleGraph.mem_edgeSet] at he
    exact G.mem_union_outerBoundary_of_adj hi he

/-- The transfer weight of `Λ` depends only on the spins in `Λ ∪ ∂Λ`. -/
lemma transferWeight_congr {Λ : Finset S} {σ τ : S → E}
    (h : ∀ k ∈ Λ ∪ G.outerBoundary Λ, σ k = τ k) :
    transferWeight G Q hQ Λ σ = transferWeight G Q hQ Λ τ :=
  Finset.prod_congr rfl fun _ hb ↦ bondWeight_congr hQ fun k hk ↦
    h k (mem_union_outerBoundary_of_mem_bondsOf G hb hk)

/-- The transfer weights form a pre-modification (Georgii (1.28)(5)): the weights of the bonds
not meeting `Λ₁` factor out. -/
lemma transferWeight_mul_comm_of_subset {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) {ζ η : S → E}
    (h : ∀ s ∉ Λ₁, ζ s = η s) :
    transferWeight G Q hQ Λ₂ ζ * transferWeight G Q hQ Λ₁ η
      = transferWeight G Q hQ Λ₁ ζ * transferWeight G Q hQ Λ₂ η := by
  have hsplit : ∀ ω : S → E, transferWeight G Q hQ Λ₂ ω
      = (∏ b ∈ G.bondsOf Λ₂ \ G.bondsOf Λ₁, bondWeight Q hQ ω b)
        * transferWeight G Q hQ Λ₁ ω := fun ω ↦
    (Finset.prod_sdiff (SimpleGraph.bondsOf_mono hΛ)).symm
  have hdiff : (∏ b ∈ G.bondsOf Λ₂ \ G.bondsOf Λ₁, bondWeight Q hQ ζ b)
      = ∏ b ∈ G.bondsOf Λ₂ \ G.bondsOf Λ₁, bondWeight Q hQ η b := by
    refine Finset.prod_congr rfl fun b hb ↦ bondWeight_congr hQ fun k hk ↦ h k fun hkΛ ↦ ?_
    have hb' := Finset.mem_sdiff.1 hb
    exact hb'.2 (SimpleGraph.mem_bondsOf.2 ⟨(SimpleGraph.mem_bondsOf.1 hb'.1).1, k, hkΛ, hk⟩)
  rw [hsplit ζ, hsplit η, hdiff]
  ring

/-- The transfer weight of a singleton: the product over the neighbours. -/
lemma transferWeight_singleton (i : S) (σ : S → E) :
    transferWeight G Q hQ {i} σ = ∏ k ∈ G.neighborFinset i, Q i k (σ i) (σ k) := by
  rw [transferWeight, SimpleGraph.bondsOf_singleton, SimpleGraph.incidenceFinset_eq_image,
    Finset.prod_image fun _ _ _ _ h ↦ SimpleGraph.injective_mk_left i h]
  rfl

/-- The bonds at `i ∈ Λ` split off from the bonds meeting `Λ`: the remaining factor does not
depend on the spin at `i`. -/
lemma transferWeight_eq_mul_of_mem {Λ : Finset S} {i : S} (hi : i ∈ Λ) (σ : S → E) :
    transferWeight G Q hQ Λ σ
      = (∏ k ∈ G.neighborFinset i, Q i k (σ i) (σ k))
        * ∏ b ∈ G.bondsOf Λ \ G.incidenceFinset i, bondWeight Q hQ σ b := by
  have hsub : G.incidenceFinset i ⊆ G.bondsOf Λ := by
    rw [← SimpleGraph.bondsOf_singleton (G := G)]
    exact SimpleGraph.bondsOf_mono (Finset.singleton_subset_iff.2 hi)
  rw [transferWeight, ← Finset.prod_sdiff hsub, mul_comm, ← transferWeight_singleton G hQ,
    transferWeight, SimpleGraph.bondsOf_singleton]

lemma prod_bondsOf_sdiff_incidenceFinset_update {Λ : Finset S} (i : S) (σ : S → E) (y : E) :
    ∏ b ∈ G.bondsOf Λ \ G.incidenceFinset i, bondWeight Q hQ (Function.update σ i y) b
      = ∏ b ∈ G.bondsOf Λ \ G.incidenceFinset i, bondWeight Q hQ σ b := by
  refine Finset.prod_congr rfl fun b hb ↦ bondWeight_congr hQ fun k hk ↦
    Function.update_of_ne (fun hki ↦ ?_) _ _
  subst hki
  have hb' := Finset.mem_sdiff.1 hb
  exact hb'.2 ((G.mem_incidenceFinset _ _).2 ⟨(SimpleGraph.mem_bondsOf.1 hb'.1).1, hk⟩)

end TransferFamily

/-! ### Transfer families: positivity, finiteness and admissibility -/

section IsTransferFamily

variable (G : SimpleGraph S) [G.LocallyFinite]

/-- **Georgii's hypotheses on the transfer matrices of §12.1.** A family `Q_{ij}` of matrices on
the countable state space `E` indexed by the ordered pairs of sites which is symmetric in the sense
of (12.9), positive with finite entries along the bonds of `G`, and whose partition functions
`Z_Λ(ω) = ∑_{σ_Λ} ∏_{b ∩ Λ ≠ ∅} Q_b(σ_Λ ω_{Λᶜ})` are finite (λ-admissibility for counting measure).
On a finite state space the last condition is automatic (`isTransferFamily_of_finite`); Georgii
assumes `E` finite throughout Chapter 12. -/
structure IsTransferFamily (Q : S → S → E → E → ℝ≥0∞) : Prop where
  symm : ∀ i j x y, Q i j x y = Q j i y x
  pos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y
  ne_top : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤
  sigmaFiniteLambdaZ_ne_top : ∀ (Λ : Finset S) (ω : S → E),
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count (transferWeight G Q symm)
      Λ ω ≠ ⊤

variable {G} {Q : S → S → E → E → ℝ≥0∞}

lemma isPremodifier_transferWeight (hQ : ∀ i j x y, Q i j x y = Q j i y x) :
    Specification.IsPremodifier (transferWeight G Q hQ) where
  measurable := measurable_transferWeight G hQ
  comm_of_subset _ _ _ _ hΛ h := transferWeight_mul_comm_of_subset G hQ hΛ h

/-- On a finite state space every symmetric family of positive finite matrices is a transfer
family. -/
lemma isTransferFamily_of_finite [Finite E] (symm : ∀ i j x y, Q i j x y = Q j i y x)
    (pos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y)
    (ne_top : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤) : IsTransferFamily G Q where
  symm := symm
  pos := pos
  ne_top := ne_top
  sigmaFiniteLambdaZ_ne_top := sigmaFiniteLambdaZ_count_ne_top_of_finite
    (isPremodifier_transferWeight symm) (transferWeight_ne_top G symm ne_top)

namespace IsTransferFamily

variable (hQ : IsTransferFamily G Q)
include hQ

lemma transferWeight_pos (Λ : Finset S) (σ : S → E) : 0 < transferWeight G Q hQ.symm Λ σ :=
  Tree.transferWeight_pos G hQ.symm hQ.pos Λ σ

lemma transferWeight_ne_top (Λ : Finset S) (σ : S → E) : transferWeight G Q hQ.symm Λ σ ≠ ⊤ :=
  Tree.transferWeight_ne_top G hQ.symm hQ.ne_top Λ σ

/-- A transfer family is admissible for counting measure. -/
theorem isSigmaFiniteLambdaAdmissible :
    Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) Measure.count
      (transferWeight G Q hQ.symm) := fun Λ ω ↦
  ⟨sigmaFiniteLambdaZ_count_ne_zero (isPremodifier_transferWeight hQ.symm)
    (hQ.transferWeight_pos Λ ω).ne', hQ.sigmaFiniteLambdaZ_ne_top Λ ω⟩

end IsTransferFamily

end IsTransferFamily

/-! ### The specification `γ^Q`: Georgii (12.8) -/

section TransferSpecification

variable [Nonempty E] (G : SimpleGraph S) [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q)

/-- **Georgii's positive Markov specification (12.8).** The λ-specification, for counting measure
on the countable state space `E`, of the transfer weights `∏_{b ∩ Λ ≠ ∅} Q_b` of a transfer
family `Q` on the locally finite graph `G`. -/
def transferSpecification : Specification S E :=
  Specification.lambdaSpecification (S := S) (E := E) Measure.count (transferWeight G Q hQ.symm)
    (isPremodifier_transferWeight hQ.symm) hQ.isSigmaFiniteLambdaAdmissible

lemma transferSpecification_apply (Λ : Finset S) (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet A) :
    transferSpecification G hQ Λ ω A
      = (Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
          (transferWeight G Q hQ.symm) Λ ω)⁻¹ * ∫⁻ ζ in A, transferWeight G Q hQ.symm Λ ζ ∂(λ₀ Λ
              ω) := by
  rw [transferSpecification, Specification.lambdaSpecification_apply]
  exact Specification.withDensity_sigmaFinitePremodifierNorm_apply (S := S) (E := E)
    Measure.count (isPremodifier_transferWeight hQ.symm) hA ω

/-- **Georgii (12.8).** `γ_Λ(σ_Λ = ω_Λ | ω) = Z_Λ(ω)⁻¹ ∏_{b ∩ Λ ≠ ∅} Q_b(ω_b)`. -/
lemma transferSpecification_apply_cyl (Λ : Finset S) (ω : S → E) :
    transferSpecification G hQ Λ ω (cyl Λ ω)
      = transferWeight G Q hQ.symm Λ ω / Specification.sigmaFiniteLambdaZ (S := S) (E := E)
          Measure.count (transferWeight G Q hQ.symm) Λ ω := by
  rw [transferSpecification_apply G hQ Λ ω (measurableSet_cyl Λ ω),
    setLIntegral_lambdaCount_cyl Λ ω (measurable_transferWeight G hQ.symm Λ),
        ENNReal.div_eq_inv_mul]

omit [Nonempty E] in
/-- The partition function of a singleton: `Z_{i}(ω) = ∑_x ∏_{k ∈ ∂i} Q_{ik}(x, ω_k)`. -/
lemma sigmaFiniteLambdaZ_transferWeight_singleton (i : S) (ω : S → E) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count (transferWeight G Q hQ.symm)
        {i} ω
      = ∑' x, ∏ k ∈ G.neighborFinset i, Q i k x (ω k) := by
  rw [Specification.sigmaFiniteLambdaZ, lintegral_lambdaCount_singleton i ω
    (measurable_transferWeight G hQ.symm {i})]
  refine tsum_congr fun x ↦ ?_
  rw [transferWeight_singleton]
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [Function.update_self, Function.update_of_ne (G.ne_of_adj ((G.mem_neighborFinset i k).1
      hk)).symm]

omit [Nonempty E] in
/-- The singleton partition function depends only on the spins at the neighbours. -/
lemma sigmaFiniteLambdaZ_transferWeight_singleton_congr (i : S) {ω ζ : S → E}
    (h : ∀ k ∈ G.neighborFinset i, ω k = ζ k) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count (transferWeight G Q hQ.symm)
        {i} ω
      = Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
          (transferWeight G Q hQ.symm) {i} ζ := by
  rw [sigmaFiniteLambdaZ_transferWeight_singleton G hQ,
    sigmaFiniteLambdaZ_transferWeight_singleton G hQ]
  exact tsum_congr fun x ↦ Finset.prod_congr rfl fun k hk ↦ by rw [h k hk]

omit [Nonempty E] in
/-- The partition function `Z_Λ(ω)` depends only on the spins on `∂Λ`. -/
lemma sigmaFiniteLambdaZ_transferWeight_congr (Λ : Finset S) {ω ω' : S → E}
    (h : ∀ k ∈ G.outerBoundary Λ, ω k = ω' k) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count (transferWeight G Q hQ.symm)
        Λ ω
      = Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
          (transferWeight G Q hQ.symm) Λ ω' := by
  rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaZ,
    lintegral_lambdaCount _ _ (measurable_transferWeight G hQ.symm Λ),
    lintegral_lambdaCount _ _ (measurable_transferWeight G hQ.symm Λ)]
  refine tsum_congr fun x ↦ transferWeight_congr G hQ.symm fun k hk ↦ ?_
  rcases Finset.mem_union.1 hk with hkΛ | hkΛ
  · rw [juxt_apply_of_mem (Finset.mem_coe.2 hkΛ), juxt_apply_of_mem (Finset.mem_coe.2 hkΛ)]
  · have hkΛ' : k ∉ (Λ : Set S) := by simpa using G.notMem_of_mem_outerBoundary hkΛ
    rw [juxt_apply_of_not_mem hkΛ', juxt_apply_of_not_mem hkΛ', h k hkΛ]

/-- **Georgii (12.8) on the cylinder `{σ_{Λ ∪ ∂Λ} = ζ}`.** `γ_Λ(σ_{Λ ∪ ∂Λ} = ζ | ω)` is
`∏_{b ∩ Λ ≠ ∅} Q_b(ζ) / Z_Λ(ζ)` if `ω` agrees with `ζ` on `∂Λ` and `0` otherwise. -/
theorem transferSpecification_apply_cyl_union_outerBoundary (Λ : Finset S) (ζ ω : S → E) :
    transferSpecification G hQ Λ ω (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = (cyl (G.outerBoundary Λ) ζ).indicator
          (fun _ ↦ transferWeight G Q hQ.symm Λ ζ
            / Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
                (transferWeight G Q hQ.symm) Λ ζ) ω := by
  rw [transferSpecification_apply G hQ Λ ω (measurableSet_cyl _ _),
    setLIntegral_lambdaCount_cyl_of_subset Finset.subset_union_left ω ζ
      (measurable_transferWeight G hQ.symm Λ),
    Finset.union_sdiff_cancel_left (G.disjoint_outerBoundary Λ)]
  by_cases hω : ω ∈ cyl (G.outerBoundary Λ) ζ
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, ENNReal.div_eq_inv_mul,
      sigmaFiniteLambdaZ_transferWeight_congr G hQ Λ (ω' := ζ) (mem_cyl.1 hω),
      transferWeight_congr G hQ.symm (τ := ζ) fun k hk ↦ ?_]
    rcases Finset.mem_union.1 hk with hkΛ | hkΛ
    · rw [juxt_apply_of_mem (Finset.mem_coe.2 hkΛ)]; rfl
    · rw [juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by
        simpa using G.notMem_of_mem_outerBoundary hkΛ)]
      exact mem_cyl.1 hω k hkΛ
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]

/-- The singleton kernel of `γ^Q` on a cylinder containing the site `i` and its neighbours:
`γ_{i}(σ_H = ζ_H | ω)` is `∏_{k ∈ ∂i} Q_{ik}(ζ_i, ζ_k) / Z_{i}(ζ)` if `ω` agrees with `ζ` on
`H \ {i}` and `0` otherwise. -/
theorem transferSpecification_singleton_apply_cyl {H : Finset S} {i : S} (hi : i ∈ H)
    (hH : G.neighborFinset i ⊆ H) (ζ ω : S → E) :
    transferSpecification G hQ {i} ω (cyl H ζ)
      = (cyl (H.erase i) ζ).indicator
          (fun _ ↦ (∏ k ∈ G.neighborFinset i, Q i k (ζ i) (ζ k))
            / Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
                (transferWeight G Q hQ.symm) {i} ζ) ω := by
  rw [transferSpecification_apply G hQ {i} ω (measurableSet_cyl H ζ),
    ← lintegral_indicator (measurableSet_cyl H ζ),
    lintegral_lambdaCount_singleton i ω
      ((measurable_transferWeight G hQ.symm {i}).indicator (measurableSet_cyl H ζ))]
  by_cases hω : ω ∈ cyl (H.erase i) ζ
  · have hωζ : ∀ k ∈ G.neighborFinset i, ω k = ζ k := fun k hk ↦
      mem_cyl.1 hω k (Finset.mem_erase.2 ⟨G.ne_of_adj ((G.mem_neighborFinset i k).1 hk) |>.symm,
        hH hk⟩)
    rw [Set.indicator_of_mem hω, tsum_eq_single (ζ i) fun y hy ↦ ?_,
      sigmaFiniteLambdaZ_transferWeight_singleton_congr G hQ i hωζ]
    · have hmem : Function.update ω i (ζ i) ∈ cyl H ζ := by
        refine mem_cyl.2 fun k hk ↦ ?_
        by_cases hki : k = i
        · subst hki; exact Function.update_self ..
        · rw [Function.update_of_ne hki]
          exact mem_cyl.1 hω k (Finset.mem_erase.2 ⟨hki, hk⟩)
      rw [Set.indicator_of_mem hmem, transferWeight_singleton, ENNReal.div_eq_inv_mul]
      congr 1
      refine Finset.prod_congr rfl fun k hk ↦ ?_
      rw [Function.update_self,
        Function.update_of_ne (G.ne_of_adj ((G.mem_neighborFinset i k).1 hk)).symm, hωζ k hk]
    · refine Set.indicator_of_notMem (fun h ↦ hy ?_) _
      have := mem_cyl.1 h i hi
      rwa [Function.update_self] at this
  · rw [Set.indicator_of_notMem hω]
    have : ∀ y, (cyl H ζ).indicator (transferWeight G Q hQ.symm {i}) (Function.update ω i y) = 0 :=
      fun y ↦ Set.indicator_of_notMem (fun h ↦ hω (mem_cyl.2 fun k hk ↦ by
        have hki := (Finset.mem_erase.1 hk).1
        have := mem_cyl.1 h k (Finset.mem_erase.1 hk).2
        rwa [Function.update_of_ne hki] at this)) _
    simp [this]

end TransferSpecification


/-! ## Boundary laws: Georgii Definition (12.10) -/

section BoundaryLaw

variable (G : SimpleGraph S) [G.LocallyFinite] (Q : S → S → E → E → ℝ≥0∞)
  (ℓ : S → S → E → ℝ≥0∞)

/-- **Georgii Definition (12.10).** A family `ℓ_{ij}`, indexed by the oriented bonds `ij` of `G`, of
positive finite row vectors on `E` such that for every oriented bond `ij` there is a constant
`c_{ij} > 0` with `ℓ_{ij}(x) = c_{ij} ∏_{k ∈ ∂i \ {j}} (ℓ_{ki} Q_{ki})(x)`, where
`(ℓ_{ki} Q_{ki})(x) = ∑_y ℓ_{ki}(y) Q_{ki}(y, x)` (the row vector `ℓ_{ki}` times the matrix
`Q_{ki}`, i.e. `(ℓ_{ki} · count).bind (ofMatrix Q_{ki})` evaluated at `{x}`).

The last field, finiteness of the total masses `∑_x ∏_{k ∈ ∂i} (ℓ_{ki} Q_{ki})(x)` of the singleton
volumes, is automatic for a finite state space (`IsBoundaryLaw.of_finite`), which is Georgii's
standing assumption in Chapter 12; for a countable `E` it is the normalisability of the measure
(12.13), the tree analogue of `ℓ_i r_i = 1` in Definition (11.8). -/
structure IsBoundaryLaw : Prop where
  pos : ∀ ⦃i j⦄, G.Adj i j → ∀ x, 0 < ℓ i j x
  ne_top : ∀ ⦃i j⦄, G.Adj i j → ∀ x, ℓ i j x ≠ ⊤
  consistent : ∀ ⦃i j⦄, G.Adj i j → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ x,
    ℓ i j x = c * ∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x
  mass_ne_top : ∀ i, ∑' x, ∏ k ∈ G.neighborFinset i, ∑' y, ℓ k i y * Q k i y x ≠ ⊤

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- On a finite state space the mass condition of `IsBoundaryLaw` is automatic. -/
lemma IsBoundaryLaw.of_finite [Finite E] (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤)
    (pos : ∀ ⦃i j⦄, G.Adj i j → ∀ x, 0 < ℓ i j x)
    (ne_top : ∀ ⦃i j⦄, G.Adj i j → ∀ x, ℓ i j x ≠ ⊤)
    (consistent : ∀ ⦃i j⦄, G.Adj i j → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ x,
      ℓ i j x = c * ∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x) :
    IsBoundaryLaw G Q ℓ where
  pos := pos
  ne_top := ne_top
  consistent := consistent
  mass_ne_top i := by
    cases nonempty_fintype E
    simp only [tsum_fintype]
    refine ENNReal.sum_ne_top.2 fun x _ ↦ ENNReal.prod_ne_top fun k hk ↦ ?_
    have hik := (G.mem_neighborFinset i k).1 hk
    exact ENNReal.sum_ne_top.2 fun y _ ↦ ENNReal.mul_ne_top (ne_top hik.symm y) (hQ hik.symm y x)

omit [DecidableEq S] in
/-- `ℓ_{ki} Q_{ki}` as a `Measure.bind`: the row vector `ℓ_{ki}` acting on the kernel of the
matrix `Q_{ki}`. -/
lemma bind_ofMatrix_apply_singleton (k i : S) (x : E) :
    ((Measure.count.withDensity (ℓ k i)).bind (Kernel.ofMatrix (Q k i))) {x}
      = ∑' y, ℓ k i y * Q k i y x := by
  rw [Kernel.bind_ofMatrix_apply_singleton]
  simp_rw [Measure.count_withDensity_apply_singleton]

namespace IsBoundaryLaw

variable {G Q ℓ} (hℓ : IsBoundaryLaw G Q ℓ)
include hℓ

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The row-vector products `ℓ_{ki} Q_{ki}` along a bond are positive. -/
lemma tsum_mul_pos (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) {k i : S} (hki : G.Adj k i)
    (x : E) : 0 < ∑' y, ℓ k i y * Q k i y x :=
  (ENNReal.mul_pos (hℓ.pos hki x).ne' (hQ hki x x).ne').trans_le (ENNReal.le_tsum x)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The row-vector products `ℓ_{ki} Q_{ki}` along a bond are finite: they are factors of the
finite `ℓ_{ij}`, `j` any other neighbour... or, if `i` has no other neighbour, of `ℓ_{ij}` for
`j = k` read through the bond `ki`. -/
lemma tsum_mul_ne_top (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) {k i : S}
    (hki : G.Adj k i) (x : E) : ∑' y, ℓ k i y * Q k i y x ≠ ⊤ := by
  classical
  -- `ℓ_{ki} Q_{ki}` is one of the positive factors in the consistency equation for the
  -- oriented bond `i j` with `j = ` any neighbour of `i` other than `k`; if `k` is the only
  -- neighbour of `i`, use the bond `i k`... whose product is empty. In that case use the mass
  -- condition at `i` instead.
  by_cases hex : ∃ j ∈ G.neighborFinset i, j ≠ k
  · obtain ⟨j, hj, hjk⟩ := hex
    have hij := (G.mem_neighborFinset i j).1 hj
    obtain ⟨c, hc0, -, hc⟩ := hℓ.consistent hij
    have hfin : c * ∏ m ∈ (G.neighborFinset i).erase j, ∑' y, ℓ m i y * Q m i y x ≠ ⊤ :=
      hc x ▸ hℓ.ne_top hij x
    have hprod : ∏ m ∈ (G.neighborFinset i).erase j, ∑' y, ℓ m i y * Q m i y x ≠ ⊤ :=
      fun h ↦ hfin (by rw [h, ENNReal.mul_top hc0])
    have hk : k ∈ (G.neighborFinset i).erase j :=
      Finset.mem_erase.2 ⟨hjk.symm, (G.mem_neighborFinset i k).2 hki.symm⟩
    intro htop
    apply hprod
    rw [← Finset.mul_prod_erase _ _ hk, htop, ENNReal.top_mul]
    exact Finset.prod_ne_zero_iff.2 fun m hm ↦ (hℓ.tsum_mul_pos hQ
      (((G.mem_neighborFinset i m).1
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))).symm) x).ne'
  · push Not at hex
    have hnb : G.neighborFinset i = {k} := by
      ext m
      simp only [Finset.mem_singleton]
      exact ⟨fun hm ↦ hex m hm, fun hm ↦ hm ▸ (G.mem_neighborFinset i k).2 hki.symm⟩
    have := hℓ.mass_ne_top i
    rw [hnb] at this
    simp only [Finset.prod_singleton] at this
    exact ne_top_of_le_ne_top this (ENNReal.le_tsum x)

end IsBoundaryLaw

end BoundaryLaw


/-! ## The weights (12.13) and their consistency (12.14) -/

section BoundaryLawWeight

variable (G : SimpleGraph S) [G.LocallyFinite] (Q : S → S → E → E → ℝ≥0∞)
  (hs : ∀ i j x y, Q i j x y = Q j i y x) (ℓ : S → S → E → ℝ≥0∞)

/-- The right-hand side of Georgii (12.13) before normalisation: the weight
`∏_{k ∈ ∂Λ} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ_b)` of a configuration on `Λ ∪ ∂Λ`. -/
def boundaryLawWeight (Λ : Finset S) (ζ : S → E) : ℝ≥0∞ :=
  (∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ k)) * transferWeight G Q hs Λ ζ

lemma measurable_boundaryLawWeight (Λ : Finset S) : Measurable (boundaryLawWeight G Q hs ℓ Λ) :=
  (Finset.measurable_prod _ fun k _ ↦ measurable_coord (ℓ k (G.anchor Λ k)) k).mul
    (measurable_transferWeight G hs Λ)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The weight of `Λ` depends only on the spins in `Λ ∪ ∂Λ`. -/
lemma boundaryLawWeight_congr {Λ : Finset S} {ζ ζ' : S → E}
    (h : ∀ k ∈ Λ ∪ G.outerBoundary Λ, ζ k = ζ' k) :
    boundaryLawWeight G Q hs ℓ Λ ζ = boundaryLawWeight G Q hs ℓ Λ ζ' := by
  rw [boundaryLawWeight, boundaryLawWeight, transferWeight_congr G hs h]
  congr 1
  exact Finset.prod_congr rfl fun k hk ↦ by rw [h k (Finset.mem_union_right _ hk)]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma boundaryLawWeight_pos (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y)
    (hℓ : ∀ ⦃i j⦄, G.Adj i j → ∀ x, 0 < ℓ i j x) (Λ : Finset S) (ζ : S → E) :
    0 < boundaryLawWeight G Q hs ℓ Λ ζ :=
  ENNReal.mul_pos (Finset.prod_ne_zero_iff.2 fun _ hk ↦ (hℓ (G.adj_anchor hk) _).ne')
    (transferWeight_pos G hs hpos Λ ζ).ne'

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma boundaryLawWeight_ne_top (htop : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤)
    (hℓ : ∀ ⦃i j⦄, G.Adj i j → ∀ x, ℓ i j x ≠ ⊤) (Λ : Finset S) (ζ : S → E) :
    boundaryLawWeight G Q hs ℓ Λ ζ ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ hk ↦ hℓ (G.adj_anchor hk) _)
    (transferWeight_ne_top G hs htop Λ ζ)

variable {G Q ℓ}

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The algebra of Georgii's consistency computation (12.14): for a tree, `Λ` connected,
`i ∈ ∂Λ`, `j = i_Λ` and `V = ∂i \ {j}`, the weight of `Λ ∪ {i}` at a configuration agreeing with
`ζ` off `V` is `∏_{k ∈ ∂Λ \ {i}} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ) ∏_{k ∈ V} ℓ_{ki}(ξ_k)
    Q_{ki}(ξ_k, ζ_i)`. -/
lemma boundaryLawWeight_insert_eq (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {i : S} (hi : i ∈ G.outerBoundary Λ) {ζ ξ : S → E}
    (hξ : ∀ k ∉ (G.neighborFinset i).erase (G.anchor Λ i), ξ k = ζ k) :
    boundaryLawWeight G Q hs ℓ (insert i Λ) ξ
      = ((∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor Λ k) (ζ k))
          * transferWeight G Q hs Λ ζ)
        * ∏ k ∈ (G.neighborFinset i).erase (G.anchor Λ i), ℓ k i (ξ k) * Q k i (ξ k) (ζ i) := by
  set V := (G.neighborFinset i).erase (G.anchor Λ i) with hV
  have hdisj := hG.disjoint_union_outerBoundary_erase hΛ hi
  have hξH : ∀ k ∈ Λ ∪ G.outerBoundary Λ, ξ k = ζ k := fun k hk ↦
    hξ k (Finset.disjoint_left.1 hdisj hk)
  have hξi : ξ i = ζ i := hξH i (Finset.mem_union_right _ hi)
  rw [boundaryLawWeight, hG.outerBoundary_insert_eq hΛ hi,
    Finset.prod_union (hG.disjoint_outerBoundary_erase hΛ hi), transferWeight,
    SimpleGraph.bondsOf_insert_eq_of_mem_outerBoundary hi,
    Finset.prod_union (hG.disjoint_bondsOf_image hΛ hi),
    Finset.prod_image fun _ _ _ _ h ↦ SimpleGraph.injective_mk_left i h]
  have h1 : ∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor (insert i Λ) k) (ξ k)
      = ∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor Λ k) (ζ k) :=
    Finset.prod_congr rfl fun k hk ↦ by
      rw [hG.anchor_insert_of_mem_erase hΛ hi hk,
        hξH k (Finset.mem_union_right _ (Finset.mem_of_mem_erase hk))]
  have h2 : ∏ k ∈ V, ℓ k (G.anchor (insert i Λ) k) (ξ k) = ∏ k ∈ V, ℓ k i (ξ k) :=
    Finset.prod_congr rfl fun k hk ↦ by rw [hG.anchor_insert_of_adj hΛ hi hk]
  have h3 : ∏ b ∈ G.bondsOf Λ, bondWeight Q hs ξ b = transferWeight G Q hs Λ ζ :=
    transferWeight_congr G hs hξH
  have h4 : ∏ k ∈ V, bondWeight Q hs ξ s(i, k) = ∏ k ∈ V, Q k i (ξ k) (ζ i) :=
    Finset.prod_congr rfl fun k _ ↦ by rw [bondWeight_mk, hs, hξi]
  rw [h1, h2, h3, h4, Finset.prod_mul_distrib]
  ring

/-- Integrating the weight of `Λ ∪ {i}` over the spins in `∂i \ {i_Λ}`, before using the
boundary-law equation: the row-vector products `ℓ_{ki} Q_{ki}` appear. -/
lemma lintegral_boundaryLawWeight_insert (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {i : S} (hi : i ∈ G.outerBoundary Λ) (ζ : S → E) :
    ∫⁻ ξ, boundaryLawWeight G Q hs ℓ (insert i Λ) ξ
        ∂(λ₀ ((G.neighborFinset i).erase (G.anchor Λ i)) ζ)
      = ((∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor Λ k) (ζ k))
          * transferWeight G Q hs Λ ζ)
        * ∏ k ∈ (G.neighborFinset i).erase (G.anchor Λ i), ∑' y, ℓ k i y * Q k i y (ζ i) := by
  set V := (G.neighborFinset i).erase (G.anchor Λ i) with hV
  set A := (∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor Λ k) (ζ k))
    * transferWeight G Q hs Λ ζ with hA
  rw [lintegral_lambdaCount_congr V ζ (measurable_boundaryLawWeight G Q hs ℓ _)
    (measurable_const.mul (Finset.measurable_prod _ fun k _ ↦
      measurable_coord (fun y ↦ ℓ k i y * Q k i y (ζ i)) k))
    (G := fun ξ ↦ A * ∏ k ∈ V, ℓ k i (ξ k) * Q k i (ξ k) (ζ i))
    fun ξ hξ ↦ boundaryLawWeight_insert_eq hs hG hΛ hi hξ,
    lintegral_const_mul _ (Finset.measurable_prod _ fun k _ ↦
      measurable_coord (fun y ↦ ℓ k i y * Q k i y (ζ i)) k),
    lintegral_lambdaCount_prod V ζ (fun k y ↦ ℓ k i y * Q k i y (ζ i))]

/-- **Georgii (12.14), one step.** For a tree, `Λ` connected and `i ∈ ∂Λ` with `j = i_Λ`,
integrating the weight of `Λ ∪ {i}` over the spins in `∂i \ {j}` gives `c_{ij}⁻¹` times the
weight of `Λ`. -/
lemma IsBoundaryLaw.exists_lintegral_boundaryLawWeight_insert (hℓ : IsBoundaryLaw G Q ℓ)
    (hG : G.IsAcyclic) {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) {i : S}
    (hi : i ∈ G.outerBoundary Λ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ ζ : S → E,
      ∫⁻ ξ, boundaryLawWeight G Q hs ℓ (insert i Λ) ξ
          ∂(λ₀ ((G.neighborFinset i).erase (G.anchor Λ i)) ζ)
        = c⁻¹ * boundaryLawWeight G Q hs ℓ Λ ζ := by
  obtain ⟨c, hc0, hct, hc⟩ := hℓ.consistent (G.adj_anchor hi)
  refine ⟨c, hc0, hct, fun ζ ↦ ?_⟩
  rw [lintegral_boundaryLawWeight_insert hs hG hΛ hi ζ]
  have hℓi : ∏ k ∈ (G.neighborFinset i).erase (G.anchor Λ i), ∑' y, ℓ k i y * Q k i y (ζ i)
      = c⁻¹ * ℓ i (G.anchor Λ i) (ζ i) := by
    rw [hc (ζ i), ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  rw [hℓi, boundaryLawWeight, ← Finset.mul_prod_erase _ _ hi]
  ring

end BoundaryLawWeight


/-! ## The measure (12.13) of a boundary law -/

section VolumeLaw

variable [Nonempty E] (G : SimpleGraph S) [G.LocallyFinite] (Q : S → S → E → E → ℝ≥0∞)
  (hs : ∀ i j x y, Q i j x y = Q j i y x) (ℓ : S → S → E → ℝ≥0∞)

/-- The measure `ρ_Λ λ_{Λ ∪ ∂Λ}(·|ω₀)` on `S → E` with the density (12.13) on `Λ ∪ ∂Λ` with
respect to counting measure, before normalisation. -/
def volumeLaw (Λ : Finset S) : Measure (S → E) :=
  (λ₀ (Λ ∪ G.outerBoundary Λ) (baseConfig (S := S) (E := E))).withDensity
    (boundaryLawWeight G Q hs ℓ Λ)

/-- The normalised measure `z_Λ ρ_Λ λ_{Λ ∪ ∂Λ}` of (12.13). -/
def normalizedVolumeLaw (Λ : Finset S) : Measure (S → E) :=
  (volumeLaw G Q hs ℓ Λ Set.univ)⁻¹ • volumeLaw G Q hs ℓ Λ

lemma volumeLaw_univ_eq_lintegral (Λ : Finset S) :
    volumeLaw G Q hs ℓ Λ Set.univ
      = ∫⁻ ζ, boundaryLawWeight G Q hs ℓ Λ ζ
          ∂(λ₀ (Λ ∪ G.outerBoundary Λ) (baseConfig (S := S) (E := E))) := by
  rw [volumeLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- The total mass of `volumeLaw Λ` is positive. -/
lemma volumeLaw_univ_ne_zero (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y)
    (hℓ : ∀ ⦃i j⦄, G.Adj i j → ∀ x, 0 < ℓ i j x) (Λ : Finset S) :
    volumeLaw G Q hs ℓ Λ Set.univ ≠ 0 := by
  rw [volumeLaw_univ_eq_lintegral, lintegral_lambdaCount _ _ (measurable_boundaryLawWeight G Q hs
      ℓ Λ)]
  refine ne_of_gt ((boundaryLawWeight_pos G Q hs ℓ hpos hℓ Λ
    (juxt ((Λ ∪ G.outerBoundary Λ : Finset S) : Set S) (baseConfig (S := S) (E := E))
      (fun _ ↦ Classical.arbitrary E))).trans_le (ENNReal.le_tsum _))

/-- The cylinder probabilities of `volumeLaw Λ`: the weight (12.13) before normalisation. -/
lemma volumeLaw_cyl (Λ : Finset S) (ζ : S → E) :
    volumeLaw G Q hs ℓ Λ (cyl (Λ ∪ G.outerBoundary Λ) ζ) = boundaryLawWeight G Q hs ℓ Λ ζ := by
  rw [volumeLaw, withDensity_apply _ (measurableSet_cyl _ _),
    setLIntegral_lambdaCount_cyl' _ _ _ (measurable_boundaryLawWeight G Q hs ℓ Λ)]
  exact boundaryLawWeight_congr G Q hs ℓ fun k hk ↦ juxt_apply_of_mem (Finset.mem_coe.2 hk) _

lemma normalizedVolumeLaw_cyl (Λ : Finset S) (ζ : S → E) :
    normalizedVolumeLaw G Q hs ℓ Λ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = (volumeLaw G Q hs ℓ Λ Set.univ)⁻¹ * boundaryLawWeight G Q hs ℓ Λ ζ := by
  rw [normalizedVolumeLaw, Measure.smul_apply, smul_eq_mul, volumeLaw_cyl]

lemma normalizedVolumeLaw_univ {Λ : Finset S} (h0 : volumeLaw G Q hs ℓ Λ Set.univ ≠ 0)
    (htop : volumeLaw G Q hs ℓ Λ Set.univ ≠ ⊤) :
    normalizedVolumeLaw G Q hs ℓ Λ Set.univ = 1 := by
  rw [normalizedVolumeLaw, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- The mass of a singleton volume, in terms of the row-vector products `ℓ_{ki} Q_{ki}`. -/
lemma volumeLaw_singleton_univ (i : S) :
    volumeLaw G Q hs ℓ {i} Set.univ
      = ∑' x, ∏ k ∈ G.neighborFinset i, ∑' y, ℓ k i y * Q k i y x := by
  have hdisj : Disjoint ({i} : Finset S) (G.outerBoundary {i}) := G.disjoint_outerBoundary _
  rw [volumeLaw_univ_eq_lintegral, lintegral_lambdaCount_union hdisj _
    (measurable_boundaryLawWeight G Q hs ℓ {i}),
    lintegral_lambdaCount_singleton i _ (measurable_lintegral_lambdaCount _
      (measurable_boundaryLawWeight G Q hs ℓ {i}))]
  refine tsum_congr fun x ↦ ?_
  rw [SimpleGraph.outerBoundary_singleton, ← lintegral_lambdaCount_prod (G.neighborFinset i) _
    (fun k y ↦ ℓ k i y * Q k i y x)]
  refine lintegral_lambdaCount_congr _ _ (measurable_boundaryLawWeight G Q hs ℓ {i})
    (Finset.measurable_prod _ fun k _ ↦ measurable_coord (fun y ↦ ℓ k i y * Q k i y x) k)
    fun ξ hξ ↦ ?_
  have hξi : ξ i = x := by
    rw [hξ i (fun h ↦ G.irrefl ((G.mem_neighborFinset i i).1 h)), Function.update_self]
  rw [boundaryLawWeight, transferWeight_singleton, SimpleGraph.outerBoundary_singleton,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [SimpleGraph.anchor_singleton (SimpleGraph.outerBoundary_singleton (G := G) i ▸ hk), hs, hξi]

variable {G Q ℓ}

/-- The mass of a singleton volume is finite for a boundary law. -/
lemma IsBoundaryLaw.volumeLaw_singleton_univ_ne_top (hℓ : IsBoundaryLaw G Q ℓ) (i : S) :
    volumeLaw G Q hs ℓ {i} Set.univ ≠ ⊤ := by
  rw [volumeLaw_singleton_univ]
  exact hℓ.mass_ne_top i

/-- **Georgii (12.14), one step, in measure form.** For a tree, `Λ` connected and `i ∈ ∂Λ`, the
marginal of `volumeLaw (Λ ∪ {i})` on `Λ ∪ ∂Λ` is `c_{ij}⁻¹` times `volumeLaw Λ`. -/
lemma IsBoundaryLaw.exists_volumeLaw_insert_map_restrict (hℓ : IsBoundaryLaw G Q ℓ)
    (hG : G.IsAcyclic) {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) {i : S}
    (hi : i ∈ G.outerBoundary Λ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (volumeLaw G Q hs ℓ (insert i Λ)).map (Λ ∪ G.outerBoundary Λ).restrict
        = c⁻¹ • (volumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict := by
  obtain ⟨c, hc0, hct, hc⟩ := hℓ.exists_lintegral_boundaryLawWeight_insert hs hG hΛ hi
  refine ⟨c, hc0, hct, ?_⟩
  rw [volumeLaw, volumeLaw, hG.insert_union_outerBoundary_eq hΛ hi,
    map_restrict_withDensity_union (hG.disjoint_union_outerBoundary_erase hΛ hi) _
      (measurable_boundaryLawWeight G Q hs ℓ _)]
  simp_rw [hc]
  rw [← Measure.map_smul, ← withDensity_smul _ (measurable_boundaryLawWeight G Q hs ℓ Λ)]
  rfl

lemma IsBoundaryLaw.exists_volumeLaw_insert_univ (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsAcyclic)
    {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) {i : S} (hi : i ∈ G.outerBoundary Λ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      volumeLaw G Q hs ℓ (insert i Λ) Set.univ = c⁻¹ * volumeLaw G Q hs ℓ Λ Set.univ ∧
      (volumeLaw G Q hs ℓ (insert i Λ)).map (Λ ∪ G.outerBoundary Λ).restrict
        = c⁻¹ • (volumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict := by
  obtain ⟨c, hc0, hct, hc⟩ := hℓ.exists_volumeLaw_insert_map_restrict hs hG hΛ hi
  refine ⟨c, hc0, hct, ?_, hc⟩
  have := congrArg (fun μ : Measure ((Λ ∪ G.outerBoundary Λ : Finset S) → E) ↦ μ Set.univ) hc
  simpa only [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) _)
    MeasurableSet.univ, Set.preimage_univ, Measure.smul_apply, smul_eq_mul] using this

/-- The normalised measures (12.13) are consistent under adding a boundary vertex. -/
lemma IsBoundaryLaw.normalizedVolumeLaw_insert_map_restrict (hℓ : IsBoundaryLaw G Q ℓ)
    (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {i : S} (hi : i ∈ G.outerBoundary Λ) :
    (normalizedVolumeLaw G Q hs ℓ (insert i Λ)).map (Λ ∪ G.outerBoundary Λ).restrict
      = (normalizedVolumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict := by
  obtain ⟨c, hc0, hct, hmass, hmap⟩ := hℓ.exists_volumeLaw_insert_univ hs hG hΛ hi
  have h0 := volumeLaw_univ_ne_zero G Q hs ℓ hQ hℓ.pos Λ
  rw [normalizedVolumeLaw, normalizedVolumeLaw, Measure.map_smul, Measure.map_smul, hmap, hmass,
    smul_smul, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hct)) (Or.inl (ENNReal.inv_ne_top.2
        hc0)),
    inv_inv, mul_right_comm, ENNReal.mul_inv_cancel hc0 hct, one_mul]

omit [DecidableEq S] [G.LocallyFinite] [Nonempty E] in
lemma connected_induce_singleton (i : S) : (G.induce (({i} : Finset S) : Set S)).Connected := by
  rw [SimpleGraph.connected_induce_iff_forall_exists_walk]
  refine ⟨⟨i, by simp⟩, fun u hu v hv ↦ ?_⟩
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
  subst hu; subst hv
  exact ⟨SimpleGraph.Walk.nil, fun x hx ↦ by simpa using hx⟩

/-- The mass of a connected volume is finite for a boundary law on a tree. -/
lemma IsBoundaryLaw.volumeLaw_univ_ne_top (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsAcyclic)
    {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) :
    volumeLaw G Q hs ℓ Λ Set.univ ≠ ⊤ := by
  obtain ⟨o, ho⟩ := hΛ.induce_nonempty
  refine SimpleGraph.connected_induction (P := fun Λ ↦ volumeLaw G Q hs ℓ Λ Set.univ ≠ ⊤)
    (connected_induce_singleton o) hΛ (Finset.singleton_subset_iff.2 (Finset.mem_coe.1 ho))
    (hℓ.volumeLaw_singleton_univ_ne_top hs o) fun Λ' hΛ' _ _ i _ hi hP ↦ ?_
  obtain ⟨c, hc0, -, hmass, -⟩ := hℓ.exists_volumeLaw_insert_univ hs hG hΛ' hi
  rw [hmass]
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hP

/-- **Georgii (12.14).** For connected `Λ ⊆ Δ` in a tree, the marginals on `Λ ∪ ∂Λ` of the
normalised measures (12.13) of `Δ` and of `Λ` coincide. -/
theorem IsBoundaryLaw.normalizedVolumeLaw_map_restrict_eq (hℓ : IsBoundaryLaw G Q ℓ)
    (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) (hG : G.IsAcyclic) {Λ Δ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) (hΔ : (G.induce (Δ : Set S)).Connected)
    (hΛΔ : Λ ⊆ Δ) :
    (normalizedVolumeLaw G Q hs ℓ Δ).map (Λ ∪ G.outerBoundary Λ).restrict
      = (normalizedVolumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict := by
  refine SimpleGraph.connected_induction (P := fun Λ' ↦
    (normalizedVolumeLaw G Q hs ℓ Λ').map (Λ ∪ G.outerBoundary Λ).restrict
      = (normalizedVolumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict)
    hΛ hΔ hΛΔ rfl fun Λ' hΛ' hΛΛ' _ i _ hi hP ↦ ?_
  rw [← hP]
  exact map_restrict_eq_of_subset (SimpleGraph.union_outerBoundary_mono hΛΛ')
    (hℓ.normalizedVolumeLaw_insert_map_restrict hs hQ hG hΛ' hi)

end VolumeLaw

/-! ### Kolmogorov extension: the measure of a boundary law -/

section BoundaryLawMeasure

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) {ℓ : S → S → E → ℝ≥0∞} (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsTree)

/-- A root of the tree, used to build connected hulls of finite volumes. -/
def root (hG : G.IsTree) : S := hG.connected.nonempty.some

variable (ℓ) in
/-- The finite-dimensional distributions of a boundary law: the marginal on `Λ` of the normalised
measure (12.13) of the connected hull of `Λ`. -/
def boundaryLawFDD (Λ : Finset S) : Measure (Λ → E) :=
  (normalizedVolumeLaw G Q hQ.symm ℓ (SimpleGraph.hull hG.connected (root hG) Λ)).map Λ.restrict

include hℓ

/-- The marginal on `Λ` of the normalised measure of any connected `Δ` with `Λ ⊆ Δ ∪ ∂Δ` is the
finite-dimensional distribution on `Λ`. -/
lemma IsBoundaryLaw.boundaryLawFDD_eq {Λ Δ : Finset S} (hΔ : (G.induce (Δ : Set S)).Connected)
    (hΛΔ : Λ ⊆ Δ ∪ G.outerBoundary Δ) :
    boundaryLawFDD hQ ℓ hG Λ = (normalizedVolumeLaw G Q hQ.symm ℓ Δ).map Λ.restrict := by
  set H₁ := SimpleGraph.hull hG.connected (root hG) Λ with hH₁
  set H₂ := SimpleGraph.hull hG.connected (root hG) (Λ ∪ Δ) with hH₂
  have h1 := hℓ.normalizedVolumeLaw_map_restrict_eq hQ.symm hQ.pos hG.isAcyclic
    (SimpleGraph.connected_induce_hull hG.connected (root hG) Λ)
    (SimpleGraph.connected_induce_hull hG.connected (root hG) (Λ ∪ Δ))
    (SimpleGraph.hull_mono _ _ Finset.subset_union_left)
  have h2 := hℓ.normalizedVolumeLaw_map_restrict_eq hQ.symm hQ.pos hG.isAcyclic hΔ
    (SimpleGraph.connected_induce_hull hG.connected (root hG) (Λ ∪ Δ))
    (Finset.subset_union_right.trans (SimpleGraph.subset_hull _ _ _))
  rw [boundaryLawFDD, ← map_restrict_eq_of_subset
    ((SimpleGraph.subset_hull hG.connected (root hG) Λ).trans Finset.subset_union_left) h1,
    map_restrict_eq_of_subset hΛΔ h2]

lemma IsBoundaryLaw.isProjectiveMeasureFamily_boundaryLawFDD :
    IsProjectiveMeasureFamily (α := fun _ : S ↦ E) (boundaryLawFDD hQ ℓ hG) := by
  intro I J hJI
  rw [hℓ.boundaryLawFDD_eq hQ hG (SimpleGraph.connected_induce_hull hG.connected (root hG) I)
    ((hJI.trans (SimpleGraph.subset_hull _ _ I)).trans Finset.subset_union_left),
    boundaryLawFDD, Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : S ↦ E) hJI)
      (Finset.measurable_restrict (X := fun _ : S ↦ E) I), Finset.restrict₂_comp_restrict]

lemma IsBoundaryLaw.isProbabilityMeasure_boundaryLawFDD (Λ : Finset S) :
    IsProbabilityMeasure (boundaryLawFDD hQ ℓ hG Λ) := by
  constructor
  rw [boundaryLawFDD, Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ)
    MeasurableSet.univ, Set.preimage_univ]
  exact normalizedVolumeLaw_univ G Q hQ.symm ℓ (volumeLaw_univ_ne_zero G Q hQ.symm ℓ hQ.pos
      hℓ.pos _)
    (hℓ.volumeLaw_univ_ne_top hQ.symm hG.isAcyclic
      (SimpleGraph.connected_induce_hull hG.connected (root hG) Λ))

lemma IsBoundaryLaw.exists_isProjectiveLimit_boundaryLawFDD :
    ∃ μ : Measure (S → E), IsProjectiveLimit μ (boundaryLawFDD hQ ℓ hG) := by
  have : ∀ Λ, IsFiniteMeasure (boundaryLawFDD hQ ℓ hG Λ) := fun Λ ↦ by
    have := hℓ.isProbabilityMeasure_boundaryLawFDD hQ hG Λ
    infer_instance
  exact exists_isProjectiveLimit_of_standardBorel (hℓ.isProjectiveMeasureFamily_boundaryLawFDD hQ
      hG)

/-- **Georgii (12.12)(a), the measure.** The probability measure `μ` on `E^S` with the cylinder
probabilities (12.13), obtained from a boundary law on a tree by Kolmogorov's extension theorem. -/
def boundaryLawMeasure : Measure (S → E) :=
  (hℓ.exists_isProjectiveLimit_boundaryLawFDD hQ hG).choose

lemma IsBoundaryLaw.isProjectiveLimit_boundaryLawMeasure :
    IsProjectiveLimit (boundaryLawMeasure hQ hℓ hG) (boundaryLawFDD hQ ℓ hG) :=
  (hℓ.exists_isProjectiveLimit_boundaryLawFDD hQ hG).choose_spec

instance isProbabilityMeasure_boundaryLawMeasure :
    IsProbabilityMeasure (boundaryLawMeasure hQ hℓ hG) := by
  constructor
  have h := hℓ.isProjectiveLimit_boundaryLawMeasure hQ hG (∅ : Finset S)
  have := hℓ.isProbabilityMeasure_boundaryLawFDD hQ hG (∅ : Finset S)
  calc boundaryLawMeasure hQ hℓ hG Set.univ
      = ((boundaryLawMeasure hQ hℓ hG).map (∅ : Finset S).restrict) Set.univ := by
        rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) _)
          MeasurableSet.univ, Set.preimage_univ]
    _ = boundaryLawFDD hQ ℓ hG ∅ Set.univ := by rw [h]
    _ = 1 := measure_univ

/-- **Georgii (12.13).** For a connected volume `Λ`,
`μ(σ_{Λ ∪ ∂Λ} = ζ) = z_Λ ∏_{k ∈ ∂Λ} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ_b)`, with the normalising
constant `z_Λ = (∑_ζ ∏_{k ∈ ∂Λ} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ_b))⁻¹`. -/
theorem IsBoundaryLaw.boundaryLawMeasure_cyl {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected)
    (ζ : S → E) :
    boundaryLawMeasure hQ hℓ hG (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = (volumeLaw G Q hQ.symm ℓ Λ Set.univ)⁻¹ * boundaryLawWeight G Q hQ.symm ℓ Λ ζ := by
  rw [← restrict_preimage_singleton, ← Measure.map_apply
    (Finset.measurable_restrict (X := fun _ : S ↦ E) _) (measurableSet_singleton _),
    hℓ.isProjectiveLimit_boundaryLawMeasure hQ hG, hℓ.boundaryLawFDD_eq hQ hG hΛ subset_rfl,
    Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) _)
      (measurableSet_singleton _), restrict_preimage_singleton, normalizedVolumeLaw_cyl]

/-- **Georgii (12.12)(a), uniqueness of the measure.** A probability measure with the cylinder
probabilities (12.13) on all connected volumes is `boundaryLawMeasure`. -/
theorem IsBoundaryLaw.eq_boundaryLawMeasure_of_forall_cyl {μ : Measure (S → E)}
    [IsProbabilityMeasure μ]
    (h : ∀ Λ : Finset S, (G.induce (Λ : Set S)).Connected → ∀ ζ : S → E,
      μ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
        = (volumeLaw G Q hQ.symm ℓ Λ Set.univ)⁻¹ * boundaryLawWeight G Q hQ.symm ℓ Λ ζ) :
    μ = boundaryLawMeasure hQ hℓ hG :=
  ext_of_forall_exists_cyl_eq fun Λ ↦
    ⟨SimpleGraph.hull hG.connected (root hG) Λ ∪ G.outerBoundary _,
      (SimpleGraph.subset_hull _ _ Λ).trans Finset.subset_union_left, fun ζ ↦ by
        rw [h _ (SimpleGraph.connected_induce_hull hG.connected (root hG) Λ),
          hℓ.boundaryLawMeasure_cyl hQ hG (SimpleGraph.connected_induce_hull hG.connected (root
              hG) Λ)]⟩

end BoundaryLawMeasure


/-! ## Georgii Theorem (12.12)(a): the measure of a boundary law is a Gibbs measure for `γ^Q` -/

section Gibbs

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) {ℓ : S → S → E → ℝ≥0∞} (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsTree)

omit [Nonempty E] in
/-- The weight (12.13) after resampling the spin at an interior site `i ∈ Λ`: the bonds at `i`
split off, the rest does not depend on the new spin. -/
lemma boundaryLawWeight_update_of_mem {Λ : Finset S} {i : S} (hi : i ∈ Λ) (ζ : S → E) (x : E) :
    boundaryLawWeight G Q hQ.symm ℓ Λ (Function.update ζ i x)
      = (∏ k ∈ G.neighborFinset i, Q i k x (ζ k))
        * ((∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ k))
          * ∏ b ∈ G.bondsOf Λ \ G.incidenceFinset i, bondWeight Q hQ.symm ζ b) := by
  rw [boundaryLawWeight, transferWeight_eq_mul_of_mem G hQ.symm hi,
    prod_bondsOf_sdiff_incidenceFinset_update G hQ.symm, Function.update_self]
  have h1 : ∏ k ∈ G.neighborFinset i, Q i k x (Function.update ζ i x k)
      = ∏ k ∈ G.neighborFinset i, Q i k x (ζ k) :=
    Finset.prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne (G.ne_of_adj ((G.mem_neighborFinset i k).1 hk)).symm]
  have h2 : ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (Function.update ζ i x k)
      = ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ k) :=
    Finset.prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hi (G.notMem_of_mem_outerBoundary hk)).symm]
  rw [h1, h2]
  ring

/-- **Georgii Theorem (12.12)(a).** The probability measure (12.13) of a boundary law for a
transfer family `Q` on a locally finite tree is a Gibbs measure for the Markov specification `γ^Q`
of (12.8). -/
theorem IsBoundaryLaw.isGibbsMeasure_transferSpecification_boundaryLawMeasure :
    (transferSpecification G hQ).IsGibbsMeasure (boundaryLawMeasure hQ hℓ hG) := by
  refine (Specification.lambdaSpecification_isGibbsMeasure_iff_forall_singleton_bind_eq
    (S := S) (E := E) Measure.count (isPremodifier_transferWeight hQ.symm)
    (fun Λ ω ↦ (hQ.transferWeight_pos Λ ω).ne') (fun Λ ω ↦ hQ.transferWeight_ne_top Λ ω)
    hQ.isSigmaFiniteLambdaAdmissible).2 fun i ↦ ?_
  change (boundaryLawMeasure hQ hℓ hG).bind (transferSpecification G hQ {i})
    = boundaryLawMeasure hQ hℓ hG
  have hmeas : Measurable (transferSpecification G hQ {i}) :=
    (transferSpecification G hQ {i}).measurable.mono cylinderEvents_le_pi le_rfl
  have hprob : IsProbabilityMeasure
      ((boundaryLawMeasure hQ hℓ hG).bind (transferSpecification G hQ {i})) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ hmeas.aemeasurable]
    simp
  refine ext_of_forall_exists_cyl_eq fun Λ ↦ ?_
  set Λ' := SimpleGraph.hull hG.connected (root hG) (insert i Λ) with hΛ'def
  have hΛ' : (G.induce (Λ' : Set S)).Connected :=
    SimpleGraph.connected_induce_hull hG.connected (root hG) _
  have hiΛ' : i ∈ Λ' := SimpleGraph.subset_hull _ _ _ (Finset.mem_insert_self i Λ)
  refine ⟨Λ' ∪ G.outerBoundary Λ', ((Finset.subset_insert i Λ).trans
    (SimpleGraph.subset_hull _ _ _)).trans Finset.subset_union_left, fun ζ ↦ ?_⟩
  have hiH : i ∈ Λ' ∪ G.outerBoundary Λ' := Finset.mem_union_left _ hiΛ'
  have hnb : G.neighborFinset i ⊆ Λ' ∪ G.outerBoundary Λ' :=
    G.neighborFinset_subset_union_outerBoundary hiΛ'
  obtain ⟨hZ0, hZt⟩ := hQ.isSigmaFiniteLambdaAdmissible {i} ζ
  rw [Measure.bind_apply (measurableSet_cyl _ ζ) hmeas.aemeasurable]
  simp_rw [transferSpecification_singleton_apply_cyl G hQ hiH hnb ζ]
  rw [lintegral_indicator (measurableSet_cyl _ _), setLIntegral_const,
    measure_cyl_eq_tsum_insert _ (Finset.notMem_erase i _) ζ, Finset.insert_erase hiH]
  simp_rw [hℓ.boundaryLawMeasure_cyl hQ hG hΛ', boundaryLawWeight_update_of_mem hQ hiΛ']
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    ← sigmaFiniteLambdaZ_transferWeight_singleton G hQ i ζ, boundaryLawWeight,
    transferWeight_eq_mul_of_mem G hQ.symm hiΛ', div_eq_mul_inv]
  set Z := Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
    (transferWeight G Q hQ.symm) {i} ζ with hZ
  rw [show ∀ a b c : ℝ≥0∞, a * Z⁻¹ * (b * (Z * c)) = (Z⁻¹ * Z) * (b * (a * c)) from
    fun a b c ↦ by ring, ENNReal.inv_mul_cancel hZ0 hZt, one_mul]
  ring

end Gibbs


/-! ## Markov chains on a tree: Georgii Definition (12.2) -/

section MarkovChain

variable (G : SimpleGraph S)

/-- Georgii's transition matrix `P_{ij}(x, y) = μ(σ_j = y | σ_i = x)` of a probability measure
(the conditional probability given the spin at `i`, as a ratio of cylinder probabilities). -/
def transitionProb (μ : Measure (S → E)) (i j : S) (x y : E) : ℝ≥0∞ :=
  μ ((fun σ ↦ σ i) ⁻¹' {x} ∩ (fun σ ↦ σ j) ⁻¹' {y}) / μ ((fun σ ↦ σ i) ⁻¹' {x})

/-- **Georgii Definition (12.2).** A probability measure `μ` on `E^S` is a *Markov chain* on the
tree `G` if for every oriented bond `ij` and `y ∈ E`,
`μ(σ_j = y | 𝓕_{]-∞, ij[}) = μ(σ_j = y | 𝓕_{i})` `μ`-a.s., where `]-∞, ij[` is the side of `i`. -/
structure IsMarkovChain (μ : Measure (S → E)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  condExp : ∀ ⦃i j⦄, G.Adj i j → ∀ y : E,
    μ[((fun σ : S → E ↦ σ j) ⁻¹' {y}).indicator (1 : (S → E) → ℝ) | cylinderEvents (G.past i j)]
      =ᵐ[μ] μ[((fun σ : S → E ↦ σ j) ⁻¹' {y}).indicator (1 : (S → E) → ℝ)
        | cylinderEvents ({i} : Set S)]

variable {G} {μ : Measure (S → E)}

omit [DecidableEq S] [Countable E] in
/-- The finite-dimensional content of Definition (12.2): for a finite `Δ` on the side of `i` with
`i ∈ Δ`, `μ(σ_j = y, σ_Δ = ω_Δ) = P_{ij}(ω_i, y) μ(σ_Δ = ω_Δ)`. -/
theorem IsMarkovChain.measure_preimage_inter_cyl (hμ : IsMarkovChain G μ) {i j : S}
    (hij : G.Adj i j) {Δ : Finset S} (hΔ : (Δ : Set S) ⊆ G.past i j) (hi : i ∈ Δ) (ω : S → E)
    (y : E) :
    μ ((fun σ ↦ σ j) ⁻¹' {y} ∩ cyl Δ ω) = transitionProb μ i j (ω i) y * μ (cyl Δ ω) := by
  have := hμ.isProbabilityMeasure
  set A := (fun σ : S → E ↦ σ j) ⁻¹' {y} with hA
  have hAm : MeasurableSet A := measurable_pi_apply j (measurableSet_singleton y)
  have hm' : cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S) ≤ cylinderEvents (G.past i j) :=
    cylinderEvents_mono (Set.singleton_subset_iff.2 (hΔ (Finset.mem_coe.2 hi)))
  have hm₀ : cylinderEvents (X := fun _ : S ↦ E) (G.past i j) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have key := (condExp_indicator_ae_eq_iff_forall_setIntegral hm' hm₀ hAm).1 (hμ.condExp hij y)
  set f := μ[A.indicator (1 : (S → E) → ℝ) | cylinderEvents ({i} : Set S)] with hf
  have hfm : Measurable[cylinderEvents ({i} : Set S)] f := stronglyMeasurable_condExp.measurable
  have hdep : DependsOn f {i} := hfm.dependsOn_of_cylinderEvents
  set D₁ := cyl Δ ω with hD₁def
  set D₂ := (fun σ : S → E ↦ σ i) ⁻¹' {ω i} with hD₂def
  have hD₁ : MeasurableSet[cylinderEvents (G.past i j)] D₁ := measurableSet_cylinderEvents_cyl hΔ ω
  have hD₂ : MeasurableSet[cylinderEvents (G.past i j)] D₂ :=
    measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (hΔ (Finset.mem_coe.2 hi))
      (measurableSet_singleton _)
  have hD₁m : MeasurableSet D₁ := measurableSet_cyl Δ ω
  have hD₂m : MeasurableSet D₂ := measurable_pi_apply i (measurableSet_singleton _)
  have hD₁₂ : D₁ ⊆ D₂ := fun σ hσ ↦ mem_cyl.1 hσ i hi
  have h1 : μ.real (A ∩ D₁) = μ.real D₁ * f ω := by
    rw [← key D₁ hD₁, setIntegral_congr_fun hD₁m (g := fun _ ↦ f ω) fun σ hσ ↦ hdep fun k hk ↦ by
      rw [Set.mem_singleton_iff.1 hk]; exact mem_cyl.1 hσ i hi, setIntegral_const, smul_eq_mul]
  have h2 : μ.real (A ∩ D₂) = μ.real D₂ * f ω := by
    rw [← key D₂ hD₂, setIntegral_congr_fun hD₂m (g := fun _ ↦ f ω) fun σ hσ ↦ hdep fun k hk ↦ by
      rw [Set.mem_singleton_iff.1 hk]; exact hσ, setIntegral_const, smul_eq_mul]
  have hE : μ (A ∩ D₁) * μ D₂ = μ (A ∩ D₂) * μ D₁ := by
    have : (μ (A ∩ D₁) * μ D₂).toReal = (μ (A ∩ D₂) * μ D₁).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
        ← measureReal_def, ← measureReal_def, h1, h2]
      ring
    exact (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (measure_ne_top _ _)
      (measure_ne_top _ _)) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 this
  by_cases h0 : μ D₂ = 0
  · have hA₁ : μ (A ∩ D₁) = 0 := measure_mono_null (Set.inter_subset_right.trans hD₁₂) h0
    have hA₂ : μ (D₂ ∩ A) = 0 := measure_mono_null Set.inter_subset_left h0
    rw [hA₁, transitionProb, hA₂, ENNReal.zero_div, zero_mul]
  · rw [transitionProb, div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
      ENNReal.eq_div_iff h0 (measure_ne_top _ _), Set.inter_comm D₂ A, mul_comm]
    exact hE

end MarkovChain


/-! ## Gibbs measures for `γ^Q`: cylinder identities and positivity -/

section GibbsCylinder

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) {μ : Measure (S → E)} [IsProbabilityMeasure μ]

lemma measurable_transferSpecification (Λ : Finset S) :
    Measurable (transferSpecification G hQ Λ) :=
  (transferSpecification G hQ Λ).measurable.mono cylinderEvents_le_pi le_rfl

variable (hμ : (transferSpecification G hQ).IsGibbsMeasure μ)
include hμ

/-- For `μ ∈ 𝒢(γ^Q)`, `μ(σ_{Λ ∪ ∂Λ} = ζ) = γ_Λ(σ_Λ = ζ_Λ | ζ) μ(σ_{∂Λ} = ζ_{∂Λ})` (the Markov
    property
of `γ^Q`). -/
theorem measure_cyl_union_outerBoundary_of_isGibbsMeasure (Λ : Finset S) (ζ : S → E) :
    μ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = transferWeight G Q hQ.symm Λ ζ / Specification.sigmaFiniteLambdaZ (S := S) (E := E)
          Measure.count (transferWeight G Q hQ.symm) Λ ζ * μ (cyl (G.outerBoundary Λ) ζ) := by
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ) Λ
  calc μ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = (μ.bind (transferSpecification G hQ Λ)) (cyl (Λ ∪ G.outerBoundary Λ) ζ) := by rw [hbind]
    _ = _ := by
      rw [Measure.bind_apply (measurableSet_cyl _ _)
        (measurable_transferSpecification hQ Λ).aemeasurable]
      simp_rw [transferSpecification_apply_cyl_union_outerBoundary G hQ Λ ζ]
      rw [lintegral_indicator (measurableSet_cyl _ _), setLIntegral_const, mul_comm]

/-- A Gibbs measure for the positive specification `γ^Q` is positive on cylinder events. -/
theorem measure_cyl_pos_of_isGibbsMeasure (H : Finset S) (ζ : S → E) : 0 < μ (cyl H ζ) := by
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ) H
  have hpos : ∀ ω, 0 < transferSpecification G hQ H ω (cyl H ζ) := fun ω ↦ by
    rw [transferSpecification_apply G hQ H ω (measurableSet_cyl _ _),
      setLIntegral_lambdaCount_cyl' H ω ζ (measurable_transferWeight G hQ.symm H)]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (hQ.sigmaFiniteLambdaZ_ne_top H ω))
      (hQ.transferWeight_pos _ _).ne'
  calc 0 < (μ.bind (transferSpecification G hQ H)) (cyl H ζ) := by
        rw [Measure.bind_apply (measurableSet_cyl _ _)
          (measurable_transferSpecification hQ H).aemeasurable,
          lintegral_pos_iff_support ((Kernel.measurable_coe _ (measurableSet_cyl _ _)).mono
            cylinderEvents_le_pi le_rfl),
          Set.eq_univ_of_forall (s := Function.support fun ω ↦
            transferSpecification G hQ H ω (cyl H ζ)) fun ω ↦ (hpos ω).ne', measure_univ]
        exact one_pos
    _ = μ (cyl H ζ) := by rw [hbind]

end GibbsCylinder

/-! ## Georgii Theorem (12.12)(b): Markov chains in `𝒢(γ^Q)` come from boundary laws -/

section Representation

variable {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}

omit [Countable E] in
/-- The Markov chain property along the whole boundary of a connected set: for `Λ` connected and
`B ⊆ ∂Λ`, `μ(σ_Λ ≡ a, σ_B = ζ_B) = μ(σ_Λ ≡ a) ∏_{k ∈ B} P_{k_Λ k}(a, ζ_k)`. This is Georgii's
`μ(B | A) = ∏_{k ∈ ∂Λ} P_{k_Λ k}(a, ζ_k)` in the proof of (12.12)(b), a consequence of (12.4). -/
theorem IsMarkovChain.measure_cyl_union_eq_mul_prod {μ : Measure (S → E)}
    (hμ : IsMarkovChain G μ) (hG : G.IsAcyclic)
    {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) (a : E) (ζ : S → E) {B : Finset S}
    (hB : B ⊆ G.outerBoundary Λ) :
    μ (cyl (Λ ∪ B) (juxt (Λ : Set S) ζ fun _ ↦ a))
      = μ (cyl Λ fun _ ↦ a) * ∏ k ∈ B, transitionProb μ (G.anchor Λ k) k a (ζ k) := by
  induction B using Finset.induction_on with
  | empty =>
    rw [Finset.union_empty, Finset.prod_empty, mul_one]
    exact congrArg μ (cyl_congr fun k hk ↦ juxt_apply_of_mem (Finset.mem_coe.2 hk) _)
  | insert k B hk ih =>
    have hB' : B ⊆ G.outerBoundary Λ := (Finset.subset_insert k B).trans hB
    have hkΛ : k ∈ G.outerBoundary Λ := hB (Finset.mem_insert_self k B)
    have hkΛ' : k ∉ Λ := G.notMem_of_mem_outerBoundary hkΛ
    have hpast : ((Λ ∪ B : Finset S) : Set S) ⊆ G.past (G.anchor Λ k) k := fun x hx ↦ by
      rw [Finset.mem_coe, Finset.mem_union] at hx
      refine hG.mem_past_anchor hΛ hkΛ ?_ ?_
      · rcases hx with hx | hx
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ (hB' hx)
      · rintro rfl
        rcases hx with hx | hx
        · exact hkΛ' hx
        · exact hk hx
    have key := hμ.measure_preimage_inter_cyl (G.adj_anchor hkΛ).symm hpast
      (Finset.mem_union_left _ (G.anchor_mem hkΛ)) (juxt (Λ : Set S) ζ fun _ ↦ a) (ζ k)
    rw [juxt_apply_of_mem (Finset.mem_coe.2 (G.anchor_mem hkΛ))] at key
    rw [Finset.union_insert, cyl_insert_eq_inter, Finset.prod_insert hk, mul_left_comm, ← ih hB',
      juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by simpa using hkΛ')]
    exact key

variable (G) (Q) (hs : ∀ i j x y, Q i j x y = Q j i y x)

open Classical in
/-- The weight `∏_{b ⊆ Λ} Q_b(a a)` of the bonds inside `Λ` at the constant configuration `a`. -/
def innerWeight (a : E) (Λ : Finset S) : ℝ≥0∞ :=
  ∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ), bondWeight Q hs (fun _ ↦ a) b

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma innerWeight_pos (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) (a : E) (Λ : Finset S) :
    0 < innerWeight G Q hs a Λ := by
  classical
  refine pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b hb ↦ ?_)
  have he := (SimpleGraph.mem_bondsOf.1 (Finset.mem_filter.1 hb).1).1
  revert he
  refine Sym2.inductionOn b fun i j he ↦ ?_
  exact (hpos (G.mem_edgeSet.1 he) _ _).ne'

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma innerWeight_ne_top (htop : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤) (a : E)
    (Λ : Finset S) : innerWeight G Q hs a Λ ≠ ⊤ := by
  classical
  refine ENNReal.prod_ne_top fun b hb ↦ ?_
  have he := (SimpleGraph.mem_bondsOf.1 (Finset.mem_filter.1 hb).1).1
  revert he
  refine Sym2.inductionOn b fun i j he ↦ ?_
  exact htop (G.mem_edgeSet.1 he) _ _

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- On a tree, the transfer weight of a connected `Λ` at the configuration which is `a` on `Λ`
and `ζ` outside factorises as `∏_{b ⊆ Λ} Q_b(aa) ∏_{k ∈ ∂Λ} Q_{k_Λ k}(a, ζ_k)`. -/
lemma transferWeight_juxt_const (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) (ζ : S → E) (a : E) :
    transferWeight G Q hs Λ (juxt (Λ : Set S) ζ fun _ ↦ a)
      = innerWeight G Q hs a Λ * ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) := by
  classical
  rw [transferWeight, hG.bondsOf_eq_filter_union_image hΛ,
    Finset.prod_union (SimpleGraph.disjoint_filter_bondsOf_image Λ),
    Finset.prod_image fun x hx y hy h ↦
      SimpleGraph.injOn_mk_anchor Λ (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) h, innerWeight]
  congr 1
  · exact Finset.prod_congr rfl fun b hb ↦ bondWeight_congr hs fun v hv ↦
      juxt_apply_of_mem (Finset.mem_coe.2 ((Finset.mem_filter.1 hb).2 v hv)) _
  · exact Finset.prod_congr rfl fun k hk ↦ by
      rw [bondWeight_mk, juxt_apply_of_mem (Finset.mem_coe.2 (G.anchor_mem hk)),
        juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by
          simpa using G.notMem_of_mem_outerBoundary hk)]


open Classical in
omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- On a tree, the transfer weight of a connected `Λ` factorises into the bonds inside `Λ` and the
bonds `{k_Λ, k}` to the boundary. -/
lemma transferWeight_eq_filter_mul_prod (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) (σ : S → E) :
    transferWeight G Q hs Λ σ
      = (∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ), bondWeight Q hs σ b)
        * ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k (σ (G.anchor Λ k)) (σ k) := by
  conv_lhs => rw [transferWeight, hG.bondsOf_eq_filter_union_image hΛ]
  rw [Finset.prod_union (SimpleGraph.disjoint_filter_bondsOf_image Λ),
    Finset.prod_image fun x hx y hy h ↦
      SimpleGraph.injOn_mk_anchor Λ (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) h]
  rfl

variable (ℓ : S → S → E → ℝ≥0∞)

open Classical in
omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The weight (12.13) after resampling the spin at a boundary site `k ∈ ∂Λ`: only the factor
`ℓ_{k k_Λ}(y) Q_{k_Λ k}(ζ_{k_Λ}, y)` depends on the new spin `y`. -/
lemma boundaryLawWeight_update_of_mem_outerBoundary (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {k : S} (hk : k ∈ G.outerBoundary Λ) (ζ : S → E)
    (y : E) :
    boundaryLawWeight G Q hs ℓ Λ (Function.update ζ k y)
      = (ℓ k (G.anchor Λ k) y * Q (G.anchor Λ k) k (ζ (G.anchor Λ k)) y)
        * ((∏ k' ∈ (G.outerBoundary Λ).erase k, ℓ k' (G.anchor Λ k') (ζ k'))
          * ((∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ), bondWeight Q hs ζ b)
            * ∏ k' ∈ (G.outerBoundary Λ).erase k,
                Q (G.anchor Λ k') k' (ζ (G.anchor Λ k')) (ζ k'))) := by
  have hkΛ := G.notMem_of_mem_outerBoundary hk
  rw [boundaryLawWeight, transferWeight_eq_filter_mul_prod G Q hs hG hΛ,
    ← Finset.mul_prod_erase _ _ hk,
    ← Finset.mul_prod_erase _ (fun k' ↦ Q (G.anchor Λ k') k' (Function.update ζ k y (G.anchor Λ k'))
      (Function.update ζ k y k')) hk,
    Function.update_self, Function.update_of_ne (ne_of_mem_of_not_mem (G.anchor_mem hk) hkΛ)]
  have h1 : ∏ k' ∈ (G.outerBoundary Λ).erase k, ℓ k' (G.anchor Λ k') (Function.update ζ k y k')
      = ∏ k' ∈ (G.outerBoundary Λ).erase k, ℓ k' (G.anchor Λ k') (ζ k') :=
    Finset.prod_congr rfl fun k' hk' ↦ by rw [Function.update_of_ne (Finset.mem_erase.1 hk').1]
  have h2 : ∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ),
        bondWeight Q hs (Function.update ζ k y) b
      = ∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ), bondWeight Q hs ζ b :=
    Finset.prod_congr rfl fun b hb ↦ bondWeight_congr hs fun v hv ↦
      Function.update_of_ne (ne_of_mem_of_not_mem ((Finset.mem_filter.1 hb).2 v hv) hkΛ) _ _
  have h3 : ∏ k' ∈ (G.outerBoundary Λ).erase k, Q (G.anchor Λ k') k'
        (Function.update ζ k y (G.anchor Λ k')) (Function.update ζ k y k')
      = ∏ k' ∈ (G.outerBoundary Λ).erase k, Q (G.anchor Λ k') k' (ζ (G.anchor Λ k')) (ζ k') :=
    Finset.prod_congr rfl fun k' hk' ↦ by
      rw [Function.update_of_ne (Finset.mem_erase.1 hk').1, Function.update_of_ne
        (ne_of_mem_of_not_mem (G.anchor_mem (Finset.mem_of_mem_erase hk')) hkΛ)]
  rw [h1, h2, h3]
  ring

variable {ℓ}

variable {G Q hs} [Nonempty E] (hQ : IsTransferFamily G Q) {μ : Measure (S → E)}
  [IsProbabilityMeasure μ]

variable (Q) in
/-- Georgii's boundary law of a Markov chain in `𝒢(γ^Q)`, normalised through the reference state
`a`: `ℓ_{ij}(x) = P_{ji}(a, x) / Q_{ji}(a, x)`. -/
def chainBoundaryLaw (μ : Measure (S → E)) (a : E) : S → S → E → ℝ≥0∞ := fun i j x ↦
  transitionProb μ j i a x / Q j i a x

/-- Georgii's normalising constant `z_Λ = μ(σ_Λ ≡ a) / ∏_{b ⊆ Λ} Q_b(aa)` in the proof of
(12.12)(b). -/
def chainNormalizer (μ : Measure (S → E)) (a : E) (Λ : Finset S) : ℝ≥0∞ :=
  μ (cyl Λ fun _ ↦ a) / innerWeight G Q hQ.symm a Λ

variable (hGibbs : (transferSpecification G hQ).IsGibbsMeasure μ)
include hGibbs

lemma transitionProb_pos_of_isGibbsMeasure {i j : S} (hij : i ≠ j) (x y : E) :
    0 < transitionProb μ i j x y :=
  ENNReal.div_pos (by
    rw [preimage_inter_preimage_eq_cyl hij x y (baseConfig (S := S) (E := E))]
    exact (measure_cyl_pos_of_isGibbsMeasure hQ hGibbs _ _).ne') (measure_ne_top _ _)

lemma transitionProb_ne_top_of_isGibbsMeasure (i j : S) (x y : E) :
    transitionProb μ i j x y ≠ ⊤ :=
  ENNReal.div_ne_top (measure_ne_top _ _) (by
    rw [preimage_singleton_eq_cyl i x (baseConfig (S := S) (E := E))]
    exact (measure_cyl_pos_of_isGibbsMeasure hQ hGibbs _ _).ne')

lemma chainBoundaryLaw_pos (a : E) {i j : S} (hij : G.Adj i j) (x : E) :
    0 < chainBoundaryLaw Q μ a i j x :=
  ENNReal.div_pos (transitionProb_pos_of_isGibbsMeasure hQ hGibbs hij.ne.symm a x).ne'
    (hQ.ne_top hij.symm a x)

lemma chainBoundaryLaw_ne_top (a : E) {i j : S} (hij : G.Adj i j) (x : E) :
    chainBoundaryLaw Q μ a i j x ≠ ⊤ :=
  ENNReal.div_ne_top (transitionProb_ne_top_of_isGibbsMeasure hQ hGibbs j i a x)
    (hQ.pos hij.symm a x).ne'

lemma chainNormalizer_ne_zero (a : E) (Λ : Finset S) : chainNormalizer hQ μ a Λ ≠ 0 :=
  ENNReal.div_ne_zero.2 ⟨(measure_cyl_pos_of_isGibbsMeasure hQ hGibbs _ _).ne',
    innerWeight_ne_top G Q hQ.symm hQ.ne_top a Λ⟩

omit [Nonempty E] hGibbs in
lemma chainNormalizer_ne_top (a : E) (Λ : Finset S) : chainNormalizer hQ μ a Λ ≠ ⊤ :=
  ENNReal.div_ne_top (measure_ne_top _ _) (innerWeight_pos G Q hQ.symm hQ.pos a Λ).ne'

variable (hμ : IsMarkovChain G μ) (hG : G.IsTree)
include hμ hG

/-- **Georgii (12.12)(b), the representation (12.13).** A Markov chain `μ ∈ 𝒢(γ^Q)` on a tree
satisfies `μ(σ_{Λ ∪ ∂Λ} = ζ) = z_Λ ∏_{k ∈ ∂Λ} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ)` for every
connected `Λ`, with `ℓ_{ij}(x) = P_{ji}(a, x)/Q_{ji}(a, x)` and `z_Λ = μ(σ_Λ ≡ a)/∏_{b ⊆ Λ}
    Q_b(aa)`. -/
theorem IsMarkovChain.measure_cyl_union_outerBoundary_eq (a : E) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) (ζ : S → E) :
    μ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = chainNormalizer hQ μ a Λ * boundaryLawWeight G Q hQ.symm (chainBoundaryLaw Q μ a) Λ ζ := by
  have hζ'B : ∀ k ∈ G.outerBoundary Λ, (juxt (Λ : Set S) ζ fun _ ↦ a) k = ζ k := fun k hk ↦
    juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by simpa using G.notMem_of_mem_outerBoundary hk) _
  obtain ⟨hZ0, hZt⟩ := hQ.isSigmaFiniteLambdaAdmissible Λ ζ
  have hIa0 := (innerWeight_pos G Q hQ.symm hQ.pos a Λ).ne'
  have hIat := innerWeight_ne_top G Q hQ.symm hQ.ne_top a Λ
  have hQb0 : ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k hk ↦ (hQ.pos (G.adj_anchor hk).symm a (ζ k)).ne'
  have hQbt : ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) ≠ ⊤ :=
    ENNReal.prod_ne_top fun k hk ↦ hQ.ne_top (G.adj_anchor hk).symm a (ζ k)
  have hG1 := measure_cyl_union_outerBoundary_of_isGibbsMeasure hQ hGibbs Λ ζ
  have hG2 := measure_cyl_union_outerBoundary_of_isGibbsMeasure hQ hGibbs Λ
    (juxt (Λ : Set S) ζ fun _ ↦ a)
  have hM := hμ.measure_cyl_union_eq_mul_prod hG.isAcyclic hΛ a ζ subset_rfl
  rw [transferWeight_juxt_const G Q hQ.symm hG.isAcyclic hΛ ζ a,
    sigmaFiniteLambdaZ_transferWeight_congr G hQ Λ hζ'B, cyl_congr hζ'B] at hG2
  have hPb : ∏ k ∈ G.outerBoundary Λ, transitionProb μ (G.anchor Λ k) k a (ζ k)
      = (∏ k ∈ G.outerBoundary Λ, chainBoundaryLaw Q μ a k (G.anchor Λ k) (ζ k))
        * ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk ↦ ?_
    rw [chainBoundaryLaw, ENNReal.div_mul_cancel (hQ.pos (G.adj_anchor hk).symm a (ζ k)).ne'
      (hQ.ne_top (G.adj_anchor hk).symm a (ζ k))]
  rw [hPb] at hM
  have hG2M := hG2.symm.trans hM
  set Y := μ (cyl (G.outerBoundary Λ) ζ) with hY
  set m := μ (cyl Λ fun _ ↦ a) with hm
  set L := ∏ k ∈ G.outerBoundary Λ, chainBoundaryLaw Q μ a k (G.anchor Λ k) (ζ k) with hL
  set Qb := ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) with hQb
  set Z := Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
    (transferWeight G Q hQ.symm) Λ ζ with hZ
  set Ia := innerWeight G Q hQ.symm a Λ with hIa
  have hYeq : Y = m * L * Z * Ia⁻¹ := by
    calc Y = (Ia * Ia⁻¹) * (Qb * Qb⁻¹) * (Z⁻¹ * Z) * Y := by
          rw [ENNReal.mul_inv_cancel hIa0 hIat, ENNReal.mul_inv_cancel hQb0 hQbt,
            ENNReal.inv_mul_cancel hZ0 hZt]
          ring
      _ = (Ia * Qb / Z * Y) * (Ia⁻¹ * Qb⁻¹ * Z) := by rw [div_eq_mul_inv]; ring
      _ = (m * (L * Qb)) * (Ia⁻¹ * Qb⁻¹ * Z) := by rw [hG2M]
      _ = m * L * Z * Ia⁻¹ * (Qb * Qb⁻¹) := by ring
      _ = m * L * Z * Ia⁻¹ := by rw [ENNReal.mul_inv_cancel hQb0 hQbt, mul_one]
  rw [hG1, hYeq, chainNormalizer, boundaryLawWeight, div_eq_mul_inv, div_eq_mul_inv]
  calc transferWeight G Q hQ.symm Λ ζ * Z⁻¹ * (m * L * Z * Ia⁻¹)
      = (Z⁻¹ * Z) * (m * Ia⁻¹ * (L * transferWeight G Q hQ.symm Λ ζ)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hZ0 hZt, one_mul]

/-- The normalising constants of (12.13) are the inverse total masses: `z_Λ ∑_ζ (…) = 1`. -/
theorem IsMarkovChain.chainNormalizer_mul_volumeLaw_univ (a : E) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) :
    chainNormalizer hQ μ a Λ
      * volumeLaw G Q hQ.symm (chainBoundaryLaw Q μ a) Λ Set.univ = 1 := by
  have h := measure_cyl_eq_lintegral_lambdaCount μ (H := ∅) (V := Λ ∪ G.outerBoundary Λ)
    (Finset.disjoint_empty_left _) (baseConfig (S := S) (E := E))
  rw [cyl_empty, measure_univ, Finset.empty_union] at h
  simp_rw [hμ.measure_cyl_union_outerBoundary_eq hQ hGibbs hG a hΛ] at h
  rw [lintegral_const_mul _ (measurable_boundaryLawWeight G Q hQ.symm _ Λ),
    ← volumeLaw_univ_eq_lintegral] at h
  exact h.symm

/-- **Georgii (12.12)(b), the boundary law.** The family `ℓ_{ij}(x) = P_{ji}(a, x)/Q_{ji}(a, x)`
of a Markov chain `μ ∈ 𝒢(γ^Q)` on a tree is a boundary law for `Q`. -/
theorem IsMarkovChain.isBoundaryLaw_chainBoundaryLaw (a : E) :
    IsBoundaryLaw G Q (chainBoundaryLaw Q μ a) where
  pos _ _ hij x := chainBoundaryLaw_pos hQ hGibbs a hij x
  ne_top _ _ hij x := chainBoundaryLaw_ne_top hQ hGibbs a hij x
  consistent i j hij := by
    have hi : i ∈ G.outerBoundary {j} := by
      rw [SimpleGraph.outerBoundary_singleton, SimpleGraph.mem_neighborFinset]
      exact hij.symm
    have hanc : G.anchor {j} i = j := SimpleGraph.anchor_singleton hi
    have hΛ := connected_induce_singleton (G := G) j
    have hzΛ0 := chainNormalizer_ne_zero hQ hGibbs a {j}
    have hzΛt := chainNormalizer_ne_top hQ (μ := μ) a {j}
    have hzΔ0 := chainNormalizer_ne_zero hQ hGibbs a (insert i {j})
    have hzΔt := chainNormalizer_ne_top hQ (μ := μ) a (insert i {j})
    refine ⟨chainNormalizer hQ μ a (insert i {j}) / chainNormalizer hQ μ a {j},
      ENNReal.div_ne_zero.2 ⟨hzΔ0, hzΛt⟩, ENNReal.div_ne_top hzΔt hzΛ0, fun x ↦ ?_⟩
    set ζ : S → E := fun _ ↦ x with hζ
    -- the two representations of `μ(σ_{Λ ∪ ∂Λ} = ζ)`, `Λ = {j}`, through `Λ` and through `Δ`
    have h1 := hμ.measure_cyl_union_outerBoundary_eq hQ hGibbs hG a hΛ ζ
    have h2 := measure_cyl_eq_lintegral_lambdaCount μ
      (hG.isAcyclic.disjoint_union_outerBoundary_erase hΛ hi) ζ
    rw [← hG.isAcyclic.insert_union_outerBoundary_eq hΛ hi] at h2
    simp_rw [hμ.measure_cyl_union_outerBoundary_eq hQ hGibbs hG a
        (SimpleGraph.connected_induce_insert_of_mem_outerBoundary hΛ hi)] at h2
    rw [lintegral_const_mul _ (measurable_boundaryLawWeight G Q hQ.symm _ _),
      lintegral_boundaryLawWeight_insert hQ.symm hG.isAcyclic hΛ hi ζ, h1,
      boundaryLawWeight, ← Finset.mul_prod_erase _ _ hi, hanc,
      mul_assoc (chainBoundaryLaw Q μ a i j (ζ i))] at h2
    have hζi : ζ i = x := rfl
    rw [hζi] at h2
    set A := (∏ k ∈ (G.outerBoundary {j}).erase i,
        chainBoundaryLaw Q μ a k (G.anchor {j} k) (ζ k)) * transferWeight G Q hQ.symm {j} ζ
      with hA
    have hA0 : A ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k hk ↦
      (chainBoundaryLaw_pos hQ hGibbs a (G.adj_anchor (Finset.mem_of_mem_erase hk)) _).ne')
      (hQ.transferWeight_pos _ _).ne'
    have hAt : A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.prod_ne_top fun k hk ↦
      chainBoundaryLaw_ne_top hQ hGibbs a (G.adj_anchor (Finset.mem_of_mem_erase hk)) _)
      (hQ.transferWeight_ne_top _ _)
    calc chainBoundaryLaw Q μ a i j x
        = (chainNormalizer hQ μ a {j})⁻¹ * chainNormalizer hQ μ a {j}
          * (chainBoundaryLaw Q μ a i j x * A) * A⁻¹ := by
          rw [ENNReal.inv_mul_cancel hzΛ0 hzΛt, one_mul, mul_assoc,
            ENNReal.mul_inv_cancel hA0 hAt, mul_one]
      _ = (chainNormalizer hQ μ a {j})⁻¹
          * (chainNormalizer hQ μ a {j} * (chainBoundaryLaw Q μ a i j x * A)) * A⁻¹ := by ring
      _ = (chainNormalizer hQ μ a {j})⁻¹ * (chainNormalizer hQ μ a (insert i {j})
          * (A * ∏ k ∈ (G.neighborFinset i).erase j, ∑' y,
              chainBoundaryLaw Q μ a k i y * Q k i y x)) * A⁻¹ := by rw [h2]
      _ = chainNormalizer hQ μ a (insert i {j}) / chainNormalizer hQ μ a {j}
          * (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, chainBoundaryLaw Q μ a k i y * Q k i y x)
          * (A * A⁻¹) := by rw [div_eq_mul_inv]; ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hA0 hAt, mul_one]
  mass_ne_top i := by
    have h := hμ.chainNormalizer_mul_volumeLaw_univ hQ hGibbs hG a (connected_induce_singleton i)
    rw [volumeLaw_singleton_univ] at h
    intro htop
    rw [htop, ENNReal.mul_top (chainNormalizer_ne_zero hQ hGibbs a {i})] at h
    exact ENNReal.top_ne_one h

/-- **Georgii Theorem (12.12)(b).** Every Markov chain `μ ∈ 𝒢(γ^Q)` on a locally finite tree is
the measure (12.13) of a boundary law for `Q`. -/
theorem IsMarkovChain.eq_boundaryLawMeasure (a : E) :
    μ = boundaryLawMeasure hQ (hμ.isBoundaryLaw_chainBoundaryLaw hQ hGibbs hG a) hG :=
  (hμ.isBoundaryLaw_chainBoundaryLaw hQ hGibbs hG a).eq_boundaryLawMeasure_of_forall_cyl hQ hG
    fun Λ hΛ ζ ↦ by
      rw [hμ.measure_cyl_union_outerBoundary_eq hQ hGibbs hG a hΛ ζ,
        ENNReal.eq_inv_of_mul_eq_one_left (hμ.chainNormalizer_mul_volumeLaw_univ hQ hGibbs hG a hΛ)]

theorem IsMarkovChain.exists_isBoundaryLaw_eq_boundaryLawMeasure :
    ∃ ℓ : S → S → E → ℝ≥0∞, ∃ hℓ : IsBoundaryLaw G Q ℓ, μ = boundaryLawMeasure hQ hℓ hG :=
  ⟨_, _, hμ.eq_boundaryLawMeasure hQ hGibbs hG (Classical.arbitrary E)⟩

end Representation


/-! ## Georgii Definition (12.1): Markov specifications -/

section MarkovSpecification

variable (G : SimpleGraph S) [G.LocallyFinite]

/-- **Georgii Definition (12.1).** A specification `γ` is *Markov* (for the graph `G`) if
`γ_Λ(σ_Λ = ζ | ·)` is `𝓕_{∂Λ}`-measurable for every finite `Λ` and every `ζ`. -/
def IsMarkovSpecification (γ : Specification S E) : Prop :=
  ∀ (Λ : Finset S) (ζ : S → E),
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (G.outerBoundary Λ : Set S)]
      fun ω ↦ γ Λ ω (cyl Λ ζ)

variable {G} [Nonempty E] {Q : S → S → E → E → ℝ≥0∞} (hQ : IsTransferFamily G Q)

/-- `γ^Q` is a Markov specification: `γ_Λ(σ_Λ = ζ_Λ | ω) = ∏_{b ∩ Λ ≠ ∅} Q_b(ζ_Λ ω_{Λᶜ}) / Z_Λ(ω)`
depends on `ω` through `ω_{∂Λ}` only. -/
theorem isMarkovSpecification_transferSpecification :
    IsMarkovSpecification G (transferSpecification G hQ) := by
  intro Λ ζ
  refine (measurable_cylinderEvents_iff_dependsOn (X := fun _ : S ↦ E)).2
    ⟨(Kernel.measurable_coe _ (measurableSet_cyl _ _)).mono cylinderEvents_le_pi le_rfl,
      fun ω ω' h ↦ ?_⟩
  simp only [transferSpecification_apply G hQ Λ _ (measurableSet_cyl Λ ζ),
    setLIntegral_lambdaCount_cyl' Λ _ ζ (measurable_transferWeight G hQ.symm Λ)]
  rw [sigmaFiniteLambdaZ_transferWeight_congr G hQ Λ h,
    transferWeight_congr G hQ.symm (τ := juxt (Λ : Set S) ω' (Λ.restrict ζ)) fun k hk ↦ ?_]
  rcases Finset.mem_union.1 hk with hkΛ | hkΛ
  · rw [juxt_apply_of_mem (Finset.mem_coe.2 hkΛ), juxt_apply_of_mem (Finset.mem_coe.2 hkΛ)]
  · have hkΛ' : k ∉ (Λ : Set S) := by simpa using G.notMem_of_mem_outerBoundary hkΛ
    rw [juxt_apply_of_not_mem hkΛ', juxt_apply_of_not_mem hkΛ', h k hkΛ]

end MarkovSpecification

/-! ## Normalised boundary laws: Georgii (12.15), (12.16) and Corollary (12.17)

A boundary law is determined up to a positive factor on each oriented bond; normalising at a
reference state `a ∈ E` (`ℓ_{ij}(a) = 1`) turns the consistency equation into (12.15). On the
Cayley tree `CT(d)` (every vertex of degree `d + 1`) a *completely homogeneous* family `ℓ_{ij} = ℓ`
for a single symmetric matrix `Q` is a boundary law iff `ℓ` solves (12.16),
`ℓ(x) = (ℓQ(x) / ℓQ(a))^d`. This is the boundary-law side of Corollary (12.17); the
correspondence with completely homogeneous Markov chains is Theorem (12.12). -/

section Normalized

variable {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  {ℓ : S → S → E → ℝ≥0∞}

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- **Georgii (12.15).** For a boundary law normalised at `a` (`ℓ_{ij}(a) = 1`), the constants are
determined: `ℓ_{ij}(x) = ∏_{k ∈ ∂i \ {j}} (ℓ_{ki} Q_{ki})(x) / (ℓ_{ki} Q_{ki})(a)`. -/
theorem IsBoundaryLaw.eq_prod_div_of_normalized (hℓ : IsBoundaryLaw G Q ℓ)
    (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) {a : E}
    (ha : ∀ ⦃i j⦄, G.Adj i j → ℓ i j a = 1) ⦃i j : S⦄ (hij : G.Adj i j) (x : E) :
    ℓ i j x = ∏ k ∈ (G.neighborFinset i).erase j,
      (∑' y, ℓ k i y * Q k i y x) / ∑' y, ℓ k i y * Q k i y a := by
  obtain ⟨c, hc0, hct, hc⟩ := hℓ.consistent hij
  have hprod : ∀ z, ∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y z ≠ 0 := fun z ↦
    Finset.prod_ne_zero_iff.2 fun k hk ↦ (hℓ.tsum_mul_pos hpos
      (((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm) z).ne'
  have hprodt : ∀ z, ∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y z ≠ ⊤ := fun z ↦
    ENNReal.prod_ne_top fun k hk ↦ hℓ.tsum_mul_ne_top hpos
      (((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm) z
  have hca : c = (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y a)⁻¹ := by
    have := hc a
    rw [ha hij] at this
    exact ENNReal.eq_inv_of_mul_eq_one_left this.symm
  rw [hc x, hca, ENNReal.prod_div_distrib, div_eq_mul_inv, mul_comm]
  exact fun k hk _ _ _ ↦ Or.inl (hℓ.tsum_mul_pos hpos
    (((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hk))).symm) a).ne'

variable (G Q)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- **Georgii (12.16) ⇔ (12.10) for completely homogeneous families on the Cayley tree.** On a
graph regular of degree `d + 1`, with a single matrix `Q` along every bond (the transfer family
`Q_{ij} = Q` of a completely homogeneous Markov specification is necessarily symmetric, but the
boundary-law equation does not use this), a constant family `ℓ_{ij} = ℓ` of positive finite
vectors with `ℓ(a) = 1` is a boundary law iff `ℓ` solves `ℓ(x) = (ℓQ(x) / ℓQ(a))^d` (and, for
countable `E`, `∑_x (ℓQ(x))^{d+1} < ∞`). -/
theorem isBoundaryLaw_const_iff {d : ℕ} (hreg : G.IsRegularOfDegree (d + 1))
    {Q₀ : E → E → ℝ≥0∞} (hpos : ∀ x y, 0 < Q₀ x y)
    {ℓ₀ : E → ℝ≥0∞} (hℓpos : ∀ x, 0 < ℓ₀ x) (hℓt : ∀ x, ℓ₀ x ≠ ⊤)
    {a : E} (ha : ℓ₀ a = 1) (hne : ∃ i j : S, G.Adj i j) :
    IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ₀) ↔
      (∀ x, ℓ₀ x = ((∑' y, ℓ₀ y * Q₀ y x) / ∑' y, ℓ₀ y * Q₀ y a) ^ d)
        ∧ ∑' x, (∑' y, ℓ₀ y * Q₀ y x) ^ (d + 1) ≠ ⊤ := by
  have hcard : ∀ ⦃i j : S⦄, G.Adj i j → ((G.neighborFinset i).erase j).card = d := fun i j hij ↦ by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset i j).2 hij),
        G.card_neighborFinset_eq_degree,
      hreg i, Nat.add_sub_cancel]
  constructor
  · intro hℓ
    refine ⟨fun x ↦ ?_, ?_⟩
    · have := hℓ.eq_prod_div_of_normalized (fun _ _ _ x y ↦ hpos x y) (fun _ _ _ ↦ ha)
        hne.choose_spec.choose_spec x
      rwa [Finset.prod_const, hcard hne.choose_spec.choose_spec] at this
    · have := hℓ.mass_ne_top hne.choose
      simp only [Finset.prod_const, G.card_neighborFinset_eq_degree, hreg.degree_eq] at this
      exact this
  · rintro ⟨h16, hm⟩
    refine ⟨fun _ _ _ x ↦ hℓpos x, fun _ _ _ x ↦ hℓt x, fun i j hij ↦ ?_, fun i ↦ ?_⟩
    · have hQa0 : ∑' y, ℓ₀ y * Q₀ y a ≠ 0 :=
        (ENNReal.mul_pos (hℓpos a).ne' (hpos a a).ne').trans_le (ENNReal.le_tsum a) |>.ne'
      have hQat : ∑' y, ℓ₀ y * Q₀ y a ≠ ⊤ := by
        intro h
        apply hm
        refine ENNReal.tsum_eq_top_of_eq_top ⟨a, ?_⟩
        rw [h, ENNReal.top_pow (Nat.succ_ne_zero d)]
      refine ⟨((∑' y, ℓ₀ y * Q₀ y a) ^ d)⁻¹, ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top hQat),
        ENNReal.inv_ne_top.2 (pow_ne_zero d hQa0), fun x ↦ ?_⟩
      rw [Finset.prod_const, hcard hij, h16 x, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow,
        mul_comm]
    · simp only [Finset.prod_const, G.card_neighborFinset_eq_degree, hreg.degree_eq]
      exact hm

end Normalized


/-! ## Georgii Example (12.11): the boundary laws of Chapter 11 on `ℤ`

`ℤ` with its usual graph structure is Mathlib's `SimpleGraph.hasse ℤ` (adjacency `i ⋖ j ∨ j ⋖ i`,
i.e. `|i - j| = 1`). A matrix `Q` on `E` defines the transfer family `Q_{(i,i+1)} = Q`,
`Q_{(i,i-1)} = Qᵀ`, and a boundary law `{ℓ_i, r_i}` for `Q` in the sense of Definition (11.8)
(`GibbsMeasure/Model/BoundaryLaw.lean`) defines the boundary law `ℓ_{(i,i+1)} = ℓ_i`,
`ℓ_{(i,i-1)} = r_iᵀ` in the sense of Definition (12.10). -/

section IntExample

open SimpleGraph

variable (Q : E → E → ℝ≥0∞) (ℓ r : ℤ → E → ℝ≥0∞)

/-- The transfer family on `ℤ` of a matrix `Q`: `Q_{(i,i+1)} = Q`, `Q_{(i,i-1)} = Qᵀ` (and `1` on
non-adjacent pairs, so that the family is symmetric). -/
def intTransferFamily : ℤ → ℤ → E → E → ℝ≥0∞ := fun i j x y ↦
  if j = i + 1 then Q x y else if i = j + 1 then Q y x else 1

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intTransferFamily_of_succ {i j : ℤ} (h : j = i + 1) (x y : E) :
    intTransferFamily Q i j x y = Q x y := by
  rw [intTransferFamily, ite_eq_left h]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intTransferFamily_of_pred {i j : ℤ} (h : i = j + 1) (x y : E) :
    intTransferFamily Q i j x y = Q y x := by
  rw [intTransferFamily, ite_eq_right (by omega), ite_eq_left h]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intTransferFamily_symm (i j : ℤ) (x y : E) :
    intTransferFamily Q i j x y = intTransferFamily Q j i y x := by
  by_cases h1 : j = i + 1
  · rw [intTransferFamily_of_succ Q h1, intTransferFamily_of_pred Q h1]
  · by_cases h2 : i = j + 1
    · rw [intTransferFamily_of_pred Q h2, intTransferFamily_of_succ Q h2]
    · simp [intTransferFamily, h1, h2]

/-- The family `ℓ_{(i,i+1)} = ℓ_i`, `ℓ_{(i,i-1)} = r_i` of Example (12.11). -/
def intBoundaryLaw : ℤ → ℤ → E → ℝ≥0∞ := fun i j x ↦ if j = i + 1 then ℓ i x else r i x

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intBoundaryLaw_of_succ {i j : ℤ} (h : j = i + 1) (x : E) :
    intBoundaryLaw ℓ r i j x = ℓ i x := by
  rw [intBoundaryLaw, ite_eq_left h]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intBoundaryLaw_of_pred {i j : ℤ} (h : i = j + 1) (x : E) :
    intBoundaryLaw ℓ r i j x = r i x := by
  rw [intBoundaryLaw, ite_eq_right (by omega)]

variable {Q ℓ r}

/-- **Georgii Example (12.11).** A boundary law `{ℓ_i, r_i}` for `Q` in the sense of Definition
(11.8) is a boundary law for the transfer family `Q_{(i,i+1)} = Q`, `Q_{(i,i-1)} = Qᵀ` on `ℤ` in the
sense of Definition (12.10), with all constants `c_{ij} = 1`. -/
theorem Markov.IsBoundaryLaw.isBoundaryLaw_hasse_int (h : Markov.IsBoundaryLaw Q ℓ r) :
    IsBoundaryLaw (hasse ℤ) (intTransferFamily Q) (intBoundaryLaw ℓ r) where
  pos i j hij x := by
    rcases (hasse_int_adj i j).1 hij with h1 | h1
    · rw [intBoundaryLaw_of_succ ℓ r h1.symm]; exact h.left_pos i x
    · rw [intBoundaryLaw_of_pred ℓ r h1.symm]; exact h.right_pos i x
  ne_top i j hij x := by
    rcases (hasse_int_adj i j).1 hij with h1 | h1
    · rw [intBoundaryLaw_of_succ ℓ r h1.symm]; exact h.left_ne_top i x
    · rw [intBoundaryLaw_of_pred ℓ r h1.symm]; exact h.right_ne_top i x
  consistent i j hij := by
    refine ⟨1, one_ne_zero, ENNReal.one_ne_top, fun x ↦ ?_⟩
    rw [one_mul]
    rcases (hasse_int_adj i j).1 hij with h1 | h1
    · have e : ((hasse ℤ).neighborFinset i).erase j = {i - 1} := by
        rw [neighborFinset_hasse_int]
        ext k
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [e, Finset.prod_singleton, intBoundaryLaw_of_succ ℓ r h1.symm]
      simp_rw [intBoundaryLaw_of_succ ℓ r (show i = i - 1 + 1 by omega),
        intTransferFamily_of_succ Q (show i = i - 1 + 1 by omega)]
      exact (h.tsum_left_mul_pred i x).symm
    · have e : ((hasse ℤ).neighborFinset i).erase j = {i + 1} := by
        rw [neighborFinset_hasse_int]
        ext k
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [e, Finset.prod_singleton, intBoundaryLaw_of_pred ℓ r h1.symm]
      simp_rw [intBoundaryLaw_of_pred ℓ r (show i + 1 = i + 1 by rfl),
        intTransferFamily_of_pred Q (show i + 1 = i + 1 by rfl), mul_comm]
      exact (h.tsum_mul_right_succ i x).symm
  mass_ne_top i := by
    rw [neighborFinset_hasse_int]
    simp_rw [Finset.prod_pair (show i - 1 ≠ i + 1 by omega),
      intBoundaryLaw_of_succ ℓ r (show i = i - 1 + 1 by omega),
      intTransferFamily_of_succ Q (show i = i - 1 + 1 by omega),
      intBoundaryLaw_of_pred ℓ r (show i + 1 = i + 1 by rfl),
      intTransferFamily_of_pred Q (show i + 1 = i + 1 by rfl), h.tsum_left_mul_pred]
    have : ∀ x, ∑' y, r (i + 1) y * Q x y = r i x := fun x ↦ by
      simp_rw [mul_comm]
      exact h.tsum_mul_right_succ i x
    simp_rw [this]
    rw [h.tsum_left_mul_right i]
    exact ENNReal.one_ne_top

/-! ### The specification `γ^Q` of §11.1 as a transfer-family specification -/

/-- The bonds of `hasse ℤ` meeting `Λ` are the bonds `{j, j + 1}`, `j` ranging over Georgii's
`bondsOf Λ` of §11.1. -/
lemma bondsOf_hasse_int (Λ : Finset ℤ) :
    (hasse ℤ).bondsOf Λ = (Markov.bondsOf Λ).image fun j ↦ s(j, j + 1) := by
  ext e
  rw [mem_bondsOf_hasse_int, Finset.mem_image]
  exact ⟨fun ⟨j, hj, he⟩ ↦ ⟨j, Markov.mem_bondsOf.2 hj, he.symm⟩,
    fun ⟨j, hj, he⟩ ↦ ⟨j, Markov.mem_bondsOf.1 hj, he.symm⟩⟩

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- **Georgii Example (12.11) for the weights.** The transfer weight (12.8) of the family
`Q_{(i,i+1)} = Q` on `ℤ = hasse ℤ` is the transfer weight (11.2)–(11.3) of the matrix `Q`. -/
theorem transferWeight_intTransferFamily (Λ : Finset ℤ) (σ : ℤ → E) :
    transferWeight (hasse ℤ) (intTransferFamily Q) (intTransferFamily_symm Q) Λ σ
      = Markov.transferWeight Q Λ σ := by
  rw [transferWeight, bondsOf_hasse_int, Markov.transferWeight,
    Finset.prod_image fun j _ k _ h ↦ injective_mk_succ_int h]
  exact Finset.prod_congr rfl fun j _ ↦ by
    rw [bondWeight_mk, intTransferFamily_of_succ Q rfl]

/-- A transfer matrix in the sense of **Georgii (11.1)** is a transfer family in the sense of
**Georgii (12.9)** on `ℤ = hasse ℤ`: the partition functions of (12.8) are those of (11.3), which
are entries of the powers of `Q`. -/
theorem Markov.IsTransferMatrix.isTransferFamily_hasse_int (hQ : Markov.IsTransferMatrix Q) :
    IsTransferFamily (hasse ℤ) (intTransferFamily Q) where
  symm := intTransferFamily_symm Q
  pos i j hij x y := by
    rcases (hasse_int_adj i j).1 hij with h | h
    · rw [intTransferFamily_of_succ Q h.symm]; exact hQ.pos x y
    · rw [intTransferFamily_of_pred Q h.symm]; exact hQ.pos y x
  ne_top i j hij x y := by
    rcases (hasse_int_adj i j).1 hij with h | h
    · rw [intTransferFamily_of_succ Q h.symm]; exact hQ.ne_top x y
    · rw [intTransferFamily_of_pred Q h.symm]; exact hQ.ne_top y x
  sigmaFiniteLambdaZ_ne_top Λ ω := by
    rw [show transferWeight (hasse ℤ) (intTransferFamily Q) (intTransferFamily_symm Q)
        = Markov.transferWeight Q from funext fun Λ' ↦ funext fun σ ↦
          transferWeight_intTransferFamily Λ' σ]
    exact (hQ.isSigmaFiniteLambdaAdmissible Λ ω).2

/-- **Georgii Example (12.11) for the specifications.** Georgii's `γ^Q` of §11.1 is the transfer
specification (12.8) of the family `Q_{(i,i+1)} = Q`, `Q_{(i,i-1)} = Qᵀ` on the tree
`ℤ = hasse ℤ`. -/
theorem Markov.transferSpecification_eq_transferSpecification_hasse_int [Nonempty E]
    (hQ : Markov.IsTransferMatrix Q) :
    Markov.transferSpecification Q hQ
      = transferSpecification (hasse ℤ) (Markov.IsTransferMatrix.isTransferFamily_hasse_int hQ) := by
  have key : ∀ ρ₁ ρ₂ : Finset ℤ → (ℤ → E) → ℝ≥0∞, ρ₁ = ρ₂ →
      ∀ (p₁ : Specification.IsPremodifier ρ₁)
        (z₁ : Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ) (E := E) Measure.count ρ₁)
        (p₂ : Specification.IsPremodifier ρ₂)
        (z₂ : Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ) (E := E) Measure.count ρ₂),
      Specification.lambdaSpecification (S := ℤ) (E := E) Measure.count ρ₁ p₁ z₁
        = Specification.lambdaSpecification (S := ℤ) (E := E) Measure.count ρ₂ p₂ z₂ := by
    rintro ρ₁ ρ₂ rfl p₁ z₁ p₂ z₂
    rfl
  exact key _ _
    (funext fun Λ ↦ funext fun σ ↦ (transferWeight_intTransferFamily Λ σ).symm) _ _ _ _

end IntExample


/-! ## Georgii Theorem (12.12)(a): the measure of a boundary law is a Markov chain -/

section MarkovChainOfBoundaryLaw

variable (Q : S → S → E → E → ℝ≥0∞) (ℓ : S → S → E → ℝ≥0∞)

/-- The transition matrix `P_{ij}(x, y) = ℓ_{ji}(y) Q_{ji}(y, x) / (ℓ_{ji} Q_{ji})(x)` of the Markov
chain of a boundary law (Georgii, proof of (12.12)(a)). -/
def boundaryLawTransition (i j : S) (x y : E) : ℝ≥0∞ :=
  ℓ j i y * Q i j x y / ∑' y', ℓ j i y' * Q i j x y'

variable {Q ℓ} [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] (hQ : IsTransferFamily G Q)
  (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsTree)

include hQ hℓ in
omit [Nonempty E] in
lemma tsum_boundaryLawTransition_ne_zero {i j : S} (hij : G.Adj i j) (x : E) :
    ∑' y', ℓ j i y' * Q i j x y' ≠ 0 :=
  ((ENNReal.mul_pos (hℓ.pos hij.symm x).ne' (hQ.pos hij x x).ne').trans_le (ENNReal.le_tsum x)).ne'

include hQ hℓ in
omit [Nonempty E] in
lemma tsum_boundaryLawTransition_ne_top {i j : S} (hij : G.Adj i j) (x : E) :
    ∑' y', ℓ j i y' * Q i j x y' ≠ ⊤ := by
  simp_rw [hQ.symm i j]
  exact hℓ.tsum_mul_ne_top hQ.pos hij.symm x

include hQ hℓ in
omit [Nonempty E] in
lemma boundaryLawTransition_ne_top {i j : S} (hij : G.Adj i j) (x y : E) :
    boundaryLawTransition Q ℓ i j x y ≠ ⊤ :=
  ENNReal.div_ne_top (ENNReal.mul_ne_top (hℓ.ne_top hij.symm y) (hQ.ne_top hij x y))
    (tsum_boundaryLawTransition_ne_zero hQ hℓ hij x)

/-- The one-step Markov property of the measure (12.13) in finite volume: for `Λ` connected and
`j ∈ ∂Λ` with `i = j_Λ`, `μ(σ_j = y, σ_Δ = ξ_Δ) = P_{ij}(ξ_i, y) μ(σ_Δ = ξ_Δ)` for
`Δ = (Λ ∪ ∂Λ) \ {j}`. -/
theorem IsBoundaryLaw.measure_preimage_inter_cyl_erase {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {j : S} (hj : j ∈ G.outerBoundary Λ) (ξ : S → E)
    (y : E) :
    boundaryLawMeasure hQ hℓ hG ((fun σ ↦ σ j) ⁻¹' {y} ∩ cyl ((Λ ∪ G.outerBoundary Λ).erase j) ξ)
      = boundaryLawTransition Q ℓ (G.anchor Λ j) j (ξ (G.anchor Λ j)) y
        * boundaryLawMeasure hQ hℓ hG (cyl ((Λ ∪ G.outerBoundary Λ).erase j) ξ) := by
  classical
  have hjH : j ∈ Λ ∪ G.outerBoundary Λ := Finset.mem_union_right _ hj
  have hjD : j ∉ (Λ ∪ G.outerBoundary Λ).erase j := Finset.notMem_erase j _
  have hinter : (fun σ : S → E ↦ σ j) ⁻¹' {y} ∩ cyl ((Λ ∪ G.outerBoundary Λ).erase j) ξ
      = cyl (Λ ∪ G.outerBoundary Λ) (Function.update ξ j y) := by
    conv_rhs => rw [← Finset.insert_erase hjH]
    rw [cyl_insert_eq_inter, Function.update_self, cyl_update_of_notMem hjD]
    rfl
  rw [hinter, hℓ.boundaryLawMeasure_cyl hQ hG hΛ, measure_cyl_eq_tsum_insert _ hjD ξ,
    Finset.insert_erase hjH]
  simp_rw [hℓ.boundaryLawMeasure_cyl hQ hG hΛ,
    boundaryLawWeight_update_of_mem_outerBoundary G Q hQ.symm ℓ hG.isAcyclic hΛ hj ξ]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, boundaryLawTransition, div_eq_mul_inv]
  set T := ∑' y', ℓ j (G.anchor Λ j) y' * Q (G.anchor Λ j) j (ξ (G.anchor Λ j)) y' with hT
  have hT0 : T ≠ 0 := tsum_boundaryLawTransition_ne_zero hQ hℓ (G.adj_anchor hj).symm _
  have hTt : T ≠ ⊤ := tsum_boundaryLawTransition_ne_top hQ hℓ (G.adj_anchor hj).symm _
  rw [show ∀ a b c : ℝ≥0∞, a * T⁻¹ * (b * (T * c)) = (T⁻¹ * T) * (b * (a * c)) from
    fun a b c ↦ by ring, ENNReal.inv_mul_cancel hT0 hTt, one_mul]

/-- **Georgii Theorem (12.12)(a), the Markov property.** The measure (12.13) of a boundary law on
a tree is a Markov chain in the sense of Definition (12.2), with transition matrices
`P_{ij}(x, y) = ℓ_{ji}(y) Q_{ji}(y, x) / (ℓ_{ji} Q_{ji})(x)`. -/
theorem IsBoundaryLaw.isMarkovChain_boundaryLawMeasure :
    IsMarkovChain G (boundaryLawMeasure hQ hℓ hG) where
  isProbabilityMeasure := inferInstance
  condExp i j hij y := by
    classical
    set B := (fun σ : S → E ↦ σ j) ⁻¹' {y} with hB
    have hBm : MeasurableSet B := measurable_pi_apply j (measurableSet_singleton y)
    let g : E → ℝ≥0∞ := fun x ↦ boundaryLawTransition Q ℓ i j x y
    have hgt : ∀ x, g x ≠ ⊤ := fun x ↦ boundaryLawTransition_ne_top hQ hℓ hij x y
    have hgm : Measurable[cylinderEvents ({i} : Set S)] fun σ : S → E ↦ g (σ i) :=
      (measurable_of_countable g).comp
        (measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (Set.mem_singleton i))
    have hm' : cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S)
        ≤ cylinderEvents (G.past i j) :=
      cylinderEvents_mono (Set.singleton_subset_iff.2 (SimpleGraph.mem_past_self_of_adj hij))
    have hm₀ : cylinderEvents (X := fun _ : S ↦ E) (G.past i j) ≤ MeasurableSpace.pi :=
      cylinderEvents_le_pi
    -- the two set functions agree on the cylinders over finite subsets of the past
    have hcyl : ∀ (W : Finset S) (ω : S → E), (W : Set S) ⊆ G.past i j →
        (boundaryLawMeasure hQ hℓ hG).restrict B (cyl W ω)
          = (boundaryLawMeasure hQ hℓ hG).withDensity (fun σ ↦ g (σ i)) (cyl W ω) := by
      intro W ω hW
      set Λ := SimpleGraph.hull hG.connected i W with hΛdef
      have hΛ : (G.induce (Λ : Set S)).Connected :=
        SimpleGraph.connected_induce_hull hG.connected i W
      have hiΛ : i ∈ Λ := SimpleGraph.mem_hull_self hG.connected i W
      have hΛp : ∀ x ∈ Λ, x ∈ G.past i j :=
        hG.isAcyclic.hull_subset_past hG.connected hij fun k hk ↦ hW (Finset.mem_coe.2 hk)
      have hjΛ : j ∉ Λ := fun h ↦ SimpleGraph.notMem_past_self i j (hΛp j h)
      have hjB : j ∈ G.outerBoundary Λ := (G.mem_outerBoundary).2 ⟨hjΛ, i, hiΛ, hij.symm⟩
      have hanc : G.anchor Λ j = i := hG.isAcyclic.anchor_eq hΛ hjB hiΛ hij.symm
      set Δ := (Λ ∪ G.outerBoundary Λ).erase j with hΔdef
      have hWΔ : W ⊆ Δ := fun k hk ↦ Finset.mem_erase.2
        ⟨fun h ↦ SimpleGraph.notMem_past_self i j (h ▸ hW (Finset.mem_coe.2 hk)),
          Finset.mem_union_left _ (SimpleGraph.subset_hull _ _ _ hk)⟩
      have hiΔ : i ∈ Δ := Finset.mem_erase.2 ⟨hij.ne, Finset.mem_union_left _ hiΛ⟩
      rw [measure_cyl_eq_lintegral_lambdaCount _ (Finset.disjoint_sdiff (s := W) (t := Δ)) ω,
        measure_cyl_eq_lintegral_lambdaCount _ (Finset.disjoint_sdiff (s := W) (t := Δ)) ω,
        Finset.union_sdiff_of_subset hWΔ]
      refine lintegral_congr fun ξ ↦ ?_
      rw [Measure.restrict_apply (measurableSet_cyl _ _), Set.inter_comm,
        withDensity_apply _ (measurableSet_cyl _ _),
        setLIntegral_congr_fun (measurableSet_cyl _ _) (g := fun _ ↦ g (ξ i))
          (fun σ hσ ↦ by simp only [mem_cyl.1 hσ i hiΔ]),
        setLIntegral_const]
      have := hℓ.measure_preimage_inter_cyl_erase hQ hG hΛ hjB ξ y
      rw [hanc] at this
      exact this
    have htrim : ((boundaryLawMeasure hQ hℓ hG).restrict B).trim hm₀
        = ((boundaryLawMeasure hQ hℓ hG).withDensity (fun σ ↦ g (σ i))).trim hm₀ := by
      refine ext_of_generate_finite (cylindersIn (G.past i j))
        (cylinderEvents_eq_generateFrom_cylindersIn _) (isPiSystem_cylindersIn _) ?_ ?_
      · rintro _ ⟨W, ω, hW, rfl⟩
        rw [trim_measurableSet_eq hm₀ (measurableSet_cylinderEvents_cyl hW ω),
          trim_measurableSet_eq hm₀ (measurableSet_cylinderEvents_cyl hW ω)]
        exact hcyl W ω hW
      · have h := hcyl ∅ (fun _ ↦ y) (by simp)
        rw [cyl_empty] at h
        rw [trim_measurableSet_eq hm₀ MeasurableSet.univ,
          trim_measurableSet_eq hm₀ MeasurableSet.univ]
        exact h
    have key : ∀ t, MeasurableSet[cylinderEvents (G.past i j)] t →
        boundaryLawMeasure hQ hℓ hG (B ∩ t) = ∫⁻ σ in t, g (σ i) ∂(boundaryLawMeasure hQ hℓ hG)
            := by
      intro t ht
      have h1 : ((boundaryLawMeasure hQ hℓ hG).restrict B).trim hm₀ t
          = ((boundaryLawMeasure hQ hℓ hG).withDensity (fun σ ↦ g (σ i))).trim hm₀ t := by
        rw [htrim]
      rw [trim_measurableSet_eq hm₀ ht, trim_measurableSet_eq hm₀ ht,
        Measure.restrict_apply (hm₀ _ ht), withDensity_apply _ (hm₀ _ ht), Set.inter_comm] at h1
      exact h1
    have h_past := (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq hm₀ hBm
      (measure_ne_top _ _) (hgm.mono hm' le_rfl).stronglyMeasurable.aestronglyMeasurable
      (ae_of_all _ fun σ ↦ hgt (σ i))).2 key
    have h_i := (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq (hm'.trans hm₀) hBm
      (measure_ne_top _ _) hgm.stronglyMeasurable.aestronglyMeasurable
      (ae_of_all _ fun σ ↦ hgt (σ i))).2 fun t ht ↦ key t (hm' _ ht)
    exact h_past.symm.trans h_i

end MarkovChainOfBoundaryLaw

end MeasureTheory.GibbsMeasure.Tree
