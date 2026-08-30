/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GKSInequalities
public import GibbsMeasure.Model.PlusPhase

/-!
# The Lebowitz–Martin-Löf/Ruelle criterion for a phase transition

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Section 6.2, the paragraph after
Theorem (6.9), states — citing Lebowitz–Martin-Löf (1972) and Ruelle (1972), and without
proof — that for the two-dimensional Ising ferromagnet at zero external field

`|𝒢(βΦ)| > 1  ↔  μ₊^β(σ₀) > 0`.

This file proves that equivalence and deduces from it that non-uniqueness is monotone in `β`.

The `←` direction is the spin-flip symmetry: if `μ₊^β(σ₀) > 0` then `μ₋^β(σ₀) < 0`, so the two
phases differ.  The `→` direction is the contrapositive: if `μ₊^β(σ₀) = 0` then, by the spin flip
and the shift invariance of the two phases, `μ₊` and `μ₋` have the same single-site marginals;
being comparable in the stochastic order they are then equal
(`MeasureTheory.Measure.StochasticallyLE.eq_of_forall_apply_eq`), and every Gibbs measure, being
squeezed between them, coincides with them.  No coupling theorem is used.

Monotonicity of `β ↦ μ₊^β(σ₀)` is Griffiths' inequality passed to the limit: the finite-volume
`+`-boundary magnetisation is a GKS correlation of a ferromagnetic interaction
(`fvMag_eq_corr`), hence nonnegative and nondecreasing in `β`
(`GibbsMeasure.GKS.corr_nonneg`, `GibbsMeasure.GKS.corr_mono_beta`), and it converges to the
magnetisation of the plus phase because `{σ | σ i = true}` is a local event.

## Main declarations

* `fvMag`: the finite-volume magnetisation `⟨σ_i⟩_Λ^+` at inverse temperature `β`.
* `fvMag_eq_corr`: it is the GKS correlation of an explicit ferromagnetic interaction.
* `fvMag_nonneg`, `fvMag_mono`: Griffiths' inequalities at finite volume.
* `plusMag`, `tendsto_fvMag`: the magnetisation of the plus phase, as a local limit.
* `plusMag_nonneg`, `plusMag_mono`: Georgii's "`μ₊^β(σ₀)` is a nonnegative nondecreasing
  function of `β`".
* `spontaneousMagnetisation`: Georgii's `m*(β) = μ₊^β(σ₀)` on `ℤ²` at `J = 1`, `h = 0`.
* `nontrivial_GP_ising2D_iff_spontaneousMagnetisation_pos`: **Lebowitz–Martin-Löf/Ruelle**.
* `nontrivial_GP_ising2D_of_nontrivial_of_le`: non-uniqueness is monotone in `β`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open Filter MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The finite-volume magnetisation as a GKS correlation -/

section FiniteVolume

variable {S : Type*} [Countable S] [DecidableEq S] (G : SimpleGraph S) [G.LocallyFinite]
  (J h β : ℝ)

open Classical in
/-- The ferromagnetic coupling constant carried by an interaction set of the Ising potential:
the external field `h` on singletons, the coupling `J` on bonds, and `0` elsewhere. -/
def isingCoupling (A : Finset S) : ℝ :=
  if A.card = 1 then h else if A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j then J else 0

omit [Countable S] [DecidableEq S] [G.LocallyFinite] in
lemma isingCoupling_nonneg (hJ : 0 ≤ J) (hh : 0 ≤ h) (A : Finset S) :
    0 ≤ isingCoupling G J h A := by
  classical
  rw [isingCoupling]
  split_ifs
  · exact hh
  · exact hJ
  · exact le_rfl

/-- The interaction sets of the Ising potential that meet `Λ`. -/
def isingIdx (Λ : Finset S) : Finset (Finset S) :=
  Potential.interactingSupport (Φ := isingPotential G J h) Λ

/-- The interaction sets of the finite-volume `+`-boundary Ising ferromagnet, seen from
inside `Λ`: a bond leaving `Λ` becomes a singleton, because the outer spin is `+1`. -/
def isingSets (Λ : Finset S) (c : {A // A ∈ isingIdx G J h Λ}) : Finset {x // x ∈ Λ} :=
  (c : Finset S).subtype (· ∈ Λ)

/-- The couplings of the finite-volume `+`-boundary Ising ferromagnet in `Λ`. -/
def isingCouplings (Λ : Finset S) (c : {A // A ∈ isingIdx G J h Λ}) : ℝ :=
  isingCoupling G J h (c : Finset S)

omit [Countable S] [DecidableEq S] in
lemma isingCouplings_nonneg (hJ : 0 ≤ J) (hh : 0 ≤ h) (Λ : Finset S)
    (c : {A // A ∈ isingIdx G J h Λ}) : 0 ≤ isingCouplings G J h Λ c :=
  isingCoupling_nonneg G J h hJ hh _

variable {G J h}

omit [Countable S] in
/-- A spin monomial over `Λ` is the restriction of a spin monomial of the `+`-boundary
configuration: the outer spins are `+1` and drop out of the product. -/
lemma prod_spin_juxt_true (Λ : Finset S) (ζ : {x // x ∈ Λ} → Bool) (A : Finset S) :
    ∏ x ∈ A, spin (juxt (Λ : Set S) (fun _ ↦ true) ζ x)
      = GKS.spinMonomial (A.subtype (· ∈ Λ)) ζ := by
  classical
  have hin : ∀ i : {x // x ∈ Λ}, juxt (Λ : Set S) (fun _ ↦ true) ζ ↑i = ζ i := by
    intro i
    simp [juxt]
  have hstep : GKS.spinMonomial (A.subtype (· ∈ Λ)) ζ
      = ∏ x ∈ A.filter (· ∈ Λ), spin (juxt (Λ : Set S) (fun _ ↦ true) ζ x) := by
    rw [GKS.spinMonomial,
      Finset.prod_congr rfl (fun i (_ : i ∈ A.subtype (· ∈ Λ)) ↦ (congrArg spin (hin i)).symm)]
    exact Finset.prod_subtype_eq_prod_filter
      (fun x ↦ spin (juxt (Λ : Set S) (fun _ ↦ true) ζ x))
  rw [hstep]
  refine (Finset.prod_subset (Finset.filter_subset _ _) ?_).symm
  intro x hxA hxf
  have hx : x ∉ Λ := by
    by_contra hx
    exact hxf (Finset.mem_filter.2 ⟨hxA, hx⟩)
  rw [juxt_apply_of_not_mem (by simpa using hx)]
  simp [spin]

omit [Countable S] [G.LocallyFinite] in
/-- Every interaction term of the `+`-boundary Ising ferromagnet is a ferromagnetic multi-spin
term of the configuration inside `Λ`. -/
lemma isingPotential_juxt_true (Λ : Finset S) (ζ : {x // x ∈ Λ} → Bool) (A : Finset S) :
    isingPotential G J h A (juxt (Λ : Set S) (fun _ ↦ true) ζ)
      = -(isingCoupling G J h A * GKS.spinMonomial (A.subtype (· ∈ Λ)) ζ) := by
  classical
  by_cases h1 : A.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
    rw [isingPotential, Potential.nearestNeighbourPair_apply_card_one h1, isingCoupling,
      ite_eq_left h1, ← prod_spin_juxt_true Λ ζ {a}]
    simp
  · by_cases h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j
    · rw [isingPotential, Potential.nearestNeighbourPair_apply_pair h2, isingCoupling,
        ite_eq_right h1, ite_eq_left h2, ← prod_spin_juxt_true Λ ζ A]
      ring
    · rw [isingPotential, Potential.nearestNeighbourPair_apply_eq_zero h1 h2, isingCoupling,
        ite_eq_right h1, ite_eq_right h2]
      ring

variable (G J h)

omit [Countable S] in
/-- **The `+`-boundary Ising Hamiltonian is a ferromagnetic multi-spin energy.** -/
lemma neg_hamiltonian_juxt_true (Λ : Finset S) (ζ : {x // x ∈ Λ} → Bool) :
    -(isingPotential G J h).hamiltonian Λ (juxt (Λ : Set S) (fun _ ↦ true) ζ)
      = GKS.energy (isingSets G J h Λ) (isingCouplings G J h Λ) ζ := by
  classical
  have hH : (isingPotential G J h).hamiltonian Λ (juxt (Λ : Set S) (fun _ ↦ true) ζ)
      = ∑ A ∈ isingIdx G J h Λ,
          isingPotential G J h A (juxt (Λ : Set S) (fun _ ↦ true) ζ) := by
    rw [Potential.hamiltonian_eq_interactingHamiltonian]
    rfl
  have hE : GKS.energy (isingSets G J h Λ) (isingCouplings G J h Λ) ζ
      = ∑ A ∈ isingIdx G J h Λ,
          isingCoupling G J h A * GKS.spinMonomial (A.subtype (· ∈ Λ)) ζ := by
    rw [GKS.energy_def]
    exact Finset.sum_coe_sort (isingIdx G J h Λ)
      (fun A ↦ isingCoupling G J h A * GKS.spinMonomial (A.subtype (· ∈ Λ)) ζ)
  rw [hH, hE, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun A _ ↦ by rw [isingPotential_juxt_true Λ ζ A]; ring

omit [Countable S] in
/-- The Boltzmann weight of the finite-volume `+`-boundary Ising ferromagnet is the GKS weight
of the interaction `(isingSets, β • isingCouplings)`. -/
lemma isingWeight_true_eq (Λ : Finset S) (ζ : {x // x ∈ Λ} → Bool) :
    isingWeight G J h β Λ (fun _ ↦ true) ζ
      = GKS.weight (isingSets G J h Λ) (fun c ↦ β * isingCouplings G J h Λ c) ζ := by
  have hE : GKS.energy (isingSets G J h Λ) (fun c ↦ β * isingCouplings G J h Λ c) ζ
      = β * GKS.energy (isingSets G J h Λ) (isingCouplings G J h Λ) ζ := by
    rw [GKS.energy_def, GKS.energy_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  rw [GKS.weight_def, hE, ← neg_hamiltonian_juxt_true G J h Λ ζ, isingWeight]
  congr 1
  ring

omit [Countable S] in
lemma sum_isingWeight_true_eq (Λ : Finset S) :
    ∑ ζ : {x // x ∈ Λ} → Bool, isingWeight G J h β Λ (fun _ ↦ true) ζ
      = GKS.partition (isingSets G J h Λ) (fun c ↦ β * isingCouplings G J h Λ c) := by
  rw [GKS.partition_def]
  exact Finset.sum_congr rfl fun ζ _ ↦ isingWeight_true_eq G J h β Λ ζ

omit [Countable S] in
/-- The `+`-boundary expectation of a single spin is the corresponding GKS correlation. -/
lemma sum_isingDensity_mul_spin (Λ : Finset S) (i : {x // x ∈ Λ}) :
    ∑ ζ : {x // x ∈ Λ} → Bool, isingDensity G J h β Λ (fun _ ↦ true) ζ * spin (ζ i)
      = GKS.corr (isingSets G J h Λ) (fun c ↦ β * isingCouplings G J h Λ c)
          (GKS.indicatorIdx {i}) := by
  classical
  have hspin : ∀ ζ : {x // x ∈ Λ} → Bool,
      GKS.spinPow (GKS.indicatorIdx {i}) ζ = spin (ζ i) := by
    intro ζ
    rw [← GKS.spinMonomial_eq_spinPow, GKS.spinMonomial, Finset.prod_singleton]
  rw [GKS.corr_def, GKS.unnorm_def, ← sum_isingWeight_true_eq G J h β Λ, Finset.sum_div]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [hspin ζ, ← isingWeight_true_eq G J h β Λ ζ, isingDensity]
  ring

/-- The finite-volume magnetisation `⟨σ_i⟩_Λ^+` at inverse temperature `β`. -/
def fvMag (Λ : Finset S) (i : S) : ℝ :=
  2 * (isingSpecification G J h β Λ (fun _ ↦ true) {σ | σ i = true}).toReal - 1

/-- **The finite-volume `+`-boundary magnetisation is a GKS correlation** of the ferromagnetic
interaction `(isingSets, β • isingCouplings)`.  This is the identification that turns
Griffiths' inequalities into statements about the Ising specification. -/
theorem fvMag_eq_corr (Λ : Finset S) {i : S} (hi : i ∈ Λ) :
    fvMag G J h β Λ i
      = GKS.corr (isingSets G J h Λ) (fun c ↦ β * isingCouplings G J h Λ c)
          (GKS.indicatorIdx {(⟨i, hi⟩ : {x // x ∈ Λ})}) := by
  classical
  set i₀ : {x // x ∈ Λ} := ⟨i, hi⟩ with hi₀
  have hA : MeasurableSet {σ : S → Bool | σ i = true} :=
    Measure.StochasticallyLE.measurableSet_setOf_eq_true i
  have hind : ∀ ζ : {x // x ∈ Λ} → Bool,
      ({σ : S → Bool | σ i = true}).indicator (1 : (S → Bool) → ℝ)
        (juxt (Λ : Set S) (fun _ ↦ true) ζ) = (spin (ζ i₀) + 1) / 2 := by
    intro ζ
    have hju : juxt (Λ : Set S) (fun _ ↦ true) ζ i = ζ i₀ := by
      simp [juxt, hi, hi₀]
    by_cases hb : ζ i₀ = true
    · have hmem : juxt (Λ : Set S) (fun _ ↦ true) ζ ∈ {σ : S → Bool | σ i = true} := by
        simp only [Set.mem_ofPred_eq, hju]
        exact hb
      rw [Set.indicator_of_mem hmem, hb]
      norm_num [spin]
    · have hmem : juxt (Λ : Set S) (fun _ ↦ true) ζ ∉ {σ : S → Bool | σ i = true} := by
        simp only [Set.mem_ofPred_eq, hju]
        exact hb
      have hbf : ζ i₀ = false := by simpa using hb
      rw [Set.indicator_of_notMem hmem, hbf]
      norm_num [spin]
  have hnn : 0 ≤ ∑ ζ : {x // x ∈ Λ} → Bool, isingDensity G J h β Λ (fun _ ↦ true) ζ *
      ({σ : S → Bool | σ i = true}).indicator (1 : (S → Bool) → ℝ)
        (juxt (Λ : Set S) (fun _ ↦ true) ζ) :=
    Finset.sum_nonneg fun ζ _ ↦ mul_nonneg (isingDensity_nonneg G J h β Λ _ ζ)
      (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  rw [← sum_isingDensity_mul_spin G J h β Λ i₀, fvMag,
    isingSpecification_apply_eq G J h β Λ (fun _ ↦ true) hA, ENNReal.toReal_ofReal hnn,
    Finset.sum_congr rfl (fun ζ (_ : ζ ∈ Finset.univ) ↦ by rw [hind ζ]), Finset.mul_sum,
    Finset.sum_congr rfl (fun ζ (_ : ζ ∈ Finset.univ) ↦
      show 2 * (isingDensity G J h β Λ (fun _ ↦ true) ζ * ((spin (ζ i₀) + 1) / 2))
        = isingDensity G J h β Λ (fun _ ↦ true) ζ * spin (ζ i₀)
          + isingDensity G J h β Λ (fun _ ↦ true) ζ by ring),
    Finset.sum_add_distrib, sum_isingDensity G J h β Λ (fun _ ↦ true)]
  ring

omit [DecidableEq S] in
/-- **GKS-I at finite volume**: the `+`-boundary magnetisation is nonnegative. -/
theorem fvMag_nonneg (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 ≤ β) (Λ : Finset S) {i : S}
    (hi : i ∈ Λ) : 0 ≤ fvMag G J h β Λ i := by
  classical
  rw [fvMag_eq_corr G J h β Λ hi]
  exact GKS.corr_nonneg _ (fun c ↦ mul_nonneg hβ (isingCouplings_nonneg G J h hJ hh Λ c)) _

omit [DecidableEq S] in
/-- **Griffiths' inequality at finite volume**: the `+`-boundary magnetisation is nondecreasing
in the inverse temperature. -/
theorem fvMag_mono (hJ : 0 ≤ J) (hh : 0 ≤ h) (Λ : Finset S) {i : S} (hi : i ∈ Λ)
    {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁) (h12 : β₁ ≤ β₂) :
    fvMag G J h β₁ Λ i ≤ fvMag G J h β₂ Λ i := by
  classical
  rw [fvMag_eq_corr G J h β₁ Λ hi, fvMag_eq_corr G J h β₂ Λ hi]
  exact GKS.corr_mono_beta _ (isingCouplings_nonneg G J h hJ hh Λ) _ h0 h12

end FiniteVolume

/-! ### The magnetisation of the plus phase -/

section Limit

variable {S : Type*} [Countable S] [DecidableEq S] (G : SimpleGraph S) [G.LocallyFinite]
  (J h β : ℝ)

/-- The magnetisation `μ₊^β(σ_i)` of the plus phase at the site `i`. -/
def plusMag (i : S) : ℝ :=
  2 * ((plusState G J h β : Measure (S → Bool)) {σ | σ i = true}).toReal - 1

omit [Countable S] [DecidableEq S] in
lemma upEvent_singleton (i : S) : upEvent ({i} : Finset S) = {σ : S → Bool | σ i = true} := by
  ext σ
  simp [upEvent]

omit [Countable S] [DecidableEq S] in
lemma setOf_eq_true_mem_localEvents (i : S) :
    {σ : S → Bool | σ i = true} ∈ localEvents S Bool := by
  rw [← upEvent_singleton]
  exact upEvent_mem_localEvents _

omit [DecidableEq S] in
/-- **The `+`-boundary magnetisation converges to the magnetisation of the plus phase.** -/
theorem tendsto_fvMag (hJ : 0 ≤ J) (hβ : 0 ≤ β) (i : S) :
    Tendsto (fun Λ : Finset S ↦ fvMag G J h β Λ i) atTop (𝓝 (plusMag G J h β i)) := by
  have h1 := tendsto_measure_plusState G J h β hJ hβ (setOf_eq_true_mem_localEvents (S := S) i)
  have h2 : Tendsto (fun Λ : Finset S ↦
      (isingSpecification G J h β Λ (fun _ ↦ true) {σ : S → Bool | σ i = true}).toReal) atTop
      (𝓝 (((plusState G J h β : Measure (S → Bool)) {σ | σ i = true}).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
  exact (h2.const_mul 2).sub_const 1

omit [DecidableEq S] in
/-- **Georgii's "`μ₊^β(σ₀)` is nonnegative"**, from GKS-I. -/
theorem plusMag_nonneg (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 ≤ β) (i : S) :
    0 ≤ plusMag G J h β i := by
  refine ge_of_tendsto (tendsto_fvMag G J h β hJ hβ i) ?_
  filter_upwards [eventually_ge_atTop ({i} : Finset S)] with Λ hΛ
  exact fvMag_nonneg G J h β hJ hh hβ Λ (Finset.singleton_subset_iff.1 hΛ)

omit [DecidableEq S] in
/-- **Georgii's "`μ₊^β(σ₀)` is a nondecreasing function of `β`"**, from Griffiths' inequality
at finite volume passed to the local limit. -/
theorem plusMag_mono (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁) (h12 : β₁ ≤ β₂)
    (i : S) : plusMag G J h β₁ i ≤ plusMag G J h β₂ i := by
  refine le_of_tendsto_of_tendsto (tendsto_fvMag G J h β₁ hJ h0 i)
    (tendsto_fvMag G J h β₂ hJ (h0.trans h12) i) ?_
  filter_upwards [eventually_ge_atTop ({i} : Finset S)] with Λ hΛ
  exact fvMag_mono G J h hJ hh Λ (Finset.singleton_subset_iff.1 hΛ) h0 h12

end Limit

/-! ### Lebowitz–Martin-Löf/Ruelle on `ℤ²` -/

section LML

open MeasureTheory.GibbsMeasure.Peierls (Site spinFlip)

variable (b : ℝ)

/-- **Georgii's spontaneous magnetisation** `m*(β) = μ₊^β(σ₀)` of the two-dimensional Ising
ferromagnet at zero external field. -/
def spontaneousMagnetisation : ℝ := plusMag (latticeGraph 2) 1 0 b (0 : Site)

theorem spontaneousMagnetisation_nonneg (hb : 0 ≤ b) : 0 ≤ spontaneousMagnetisation b :=
  plusMag_nonneg (latticeGraph 2) 1 0 b zero_le_one le_rfl hb _

/-- **Griffiths' inequality**: the spontaneous magnetisation is nondecreasing in `β`. -/
theorem spontaneousMagnetisation_mono {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁) (h12 : β₁ ≤ β₂) :
    spontaneousMagnetisation β₁ ≤ spontaneousMagnetisation β₂ :=
  plusMag_mono (latticeGraph 2) 1 0 zero_le_one le_rfl h0 h12 _

/-- **Shift invariance of the plus phase**: all sites carry the same magnetisation. -/
theorem plusMag_shift (hb : 0 ≤ b) (i : Site) :
    plusMag (latticeGraph 2) 1 0 b i = spontaneousMagnetisation b := by
  have hmp := measurePreserving_shift_plusState (d := 2) 1 0 b zero_le_one hb i
  have hpre : (shift Bool i).toFun ⁻¹' {σ : Site → Bool | σ i = true}
      = {σ : Site → Bool | σ (0 : Site) = true} := by
    ext ω
    simp
  have hkey : (plusState (latticeGraph 2) 1 0 b : Measure (Site → Bool))
        {σ : Site → Bool | σ i = true}
      = (plusState (latticeGraph 2) 1 0 b : Measure (Site → Bool))
        {σ : Site → Bool | σ (0 : Site) = true} := by
    conv_lhs => rw [← hmp.map_eq]
    rw [Measure.map_apply (shift Bool i).measurable_toFun
      (Measure.StochasticallyLE.measurableSet_setOf_eq_true i), hpre]
  rw [plusMag, spontaneousMagnetisation, plusMag, hkey]

/-- **Spin-flip duality**: the minus phase gives a site the `+` spin exactly as often as the
plus phase gives it the `-` spin. -/
theorem minusState_apply_setOf_eq_true (hb : 0 ≤ b) (i : Site) :
    (minusState (latticeGraph 2) 1 0 b : Measure (Site → Bool)) {σ | σ i = true}
      = 1 - (plusState (latticeGraph 2) 1 0 b : Measure (Site → Bool)) {σ | σ i = true} := by
  have hA : MeasurableSet {σ : Site → Bool | σ i = true} :=
    Measure.StochasticallyLE.measurableSet_setOf_eq_true i
  have hpre : spinFlip.toFun ⁻¹' {σ : Site → Bool | σ i = true}
      = {σ : Site → Bool | σ i = true}ᶜ := by
    ext ω
    simp
  rw [← map_spinFlip_plusState b hb, Measure.map_apply spinFlip.measurable_toFun hA, hpre,
    measure_compl hA (measure_ne_top _ _), measure_univ]

private lemma toReal_plusState (i : Site) :
    ((plusState (latticeGraph 2) 1 0 b : Measure (Site → Bool))
        {σ : Site → Bool | σ i = true}).toReal = (plusMag (latticeGraph 2) 1 0 b i + 1) / 2 := by
  rw [plusMag]
  ring

/-- **Lebowitz–Martin-Löf/Ruelle, `←`.**  A strictly positive spontaneous magnetisation forces
more than one Gibbs measure: the plus and the minus phase differ. -/
theorem nontrivial_GP_ising2D_of_spontaneousMagnetisation_pos (hb : 0 ≤ b)
    (hm : 0 < spontaneousMagnetisation b) :
    (GP (S := Site) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b)).Nontrivial := by
  refine ⟨plusState (latticeGraph 2) 1 0 b,
    plusState_mem_GP (latticeGraph 2) 1 0 b zero_le_one hb,
    minusState (latticeGraph 2) 1 0 b,
    minusState_mem_GP (latticeGraph 2) 1 0 b zero_le_one hb, fun hEq ↦ ?_⟩
  have hmeas : (plusState (latticeGraph 2) 1 0 b : Measure (Site → Bool))
      = (minusState (latticeGraph 2) 1 0 b : Measure (Site → Bool)) := congrArg Subtype.val hEq
  have hle : (plusState (latticeGraph 2) 1 0 b : Measure (Site → Bool))
      {σ : Site → Bool | σ (0 : Site) = true} ≤ 1 := prob_le_one
  have h1 := minusState_apply_setOf_eq_true b hb (0 : Site)
  rw [← hmeas] at h1
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one,
    toReal_plusState b (0 : Site)] at h2
  have h3 : spontaneousMagnetisation b = 0 := by
    rw [spontaneousMagnetisation]
    linarith [h2]
  exact absurd h3 (ne_of_gt hm)

/-- **Lebowitz–Martin-Löf/Ruelle, `→`** (contrapositive form).  A vanishing spontaneous
magnetisation forces uniqueness of the Gibbs measure. -/
theorem subsingleton_GP_ising2D_of_spontaneousMagnetisation_eq_zero (hb : 0 ≤ b)
    (hm : spontaneousMagnetisation b = 0) :
    (GP (S := Site) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b)).Subsingleton := by
  set μp : Measure (Site → Bool) := (plusState (latticeGraph 2) 1 0 b : Measure (Site → Bool))
    with hμp
  set μm : Measure (Site → Bool) := (minusState (latticeGraph 2) 1 0 b : Measure (Site → Bool))
    with hμm
  have hhalf : ∀ i : Site, (μp {σ : Site → Bool | σ i = true}).toReal = 1 / 2 := by
    intro i
    rw [hμp, toReal_plusState b i, plusMag_shift b hb i, hm]
    norm_num
  have hne : ∀ i : Site, μp {σ : Site → Bool | σ i = true} ≠ ⊤ := fun i ↦ measure_ne_top _ _
  have hlep : ∀ i : Site, μp {σ : Site → Bool | σ i = true} ≤ 1 := fun _ ↦ prob_le_one
  have hmhalf : ∀ i : Site, (μm {σ : Site → Bool | σ i = true}).toReal = 1 / 2 := by
    intro i
    rw [hμm, minusState_apply_setOf_eq_true b hb i,
      ENNReal.toReal_sub_of_le (hlep i) ENNReal.one_ne_top, ENNReal.toReal_one, hhalf i]
    norm_num
  have hmarg : ∀ i : Site,
      μm {σ : Site → Bool | σ i = true} = μp {σ : Site → Bool | σ i = true} := by
    intro i
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (hne i)).1
      ((hmhalf i).trans (hhalf i).symm)
  have hmp : μm = μp :=
    Measure.StochasticallyLE.eq_of_forall_apply_eq
      (minusState_stochasticallyLE_plusState (latticeGraph 2) 1 0 b zero_le_one hb) hmarg
  intro x hx y hy
  have key : ∀ ν : ProbabilityMeasure (Site → Bool),
      ν ∈ GP (S := Site) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) →
      ν = plusState (latticeGraph 2) 1 0 b := by
    intro ν hν
    refine Subtype.ext ?_
    change (ν : Measure (Site → Bool))
      = (plusState (latticeGraph 2) 1 0 b : Measure (Site → Bool))
    refine Measure.StochasticallyLE.eq_of_forall_apply_eq
      (stochasticallyLE_plusState (latticeGraph 2) 1 0 b zero_le_one hb hν) fun i ↦ ?_
    have hlo := minusState_stochasticallyLE (latticeGraph 2) 1 0 b zero_le_one hb hν
      (Measure.StochasticallyLE.measurableSet_setOf_eq_true i)
      (Measure.StochasticallyLE.isUpperSet_setOf_eq_true i)
    have hhi := stochasticallyLE_plusState (latticeGraph 2) 1 0 b zero_le_one hb hν
      (Measure.StochasticallyLE.measurableSet_setOf_eq_true i)
      (Measure.StochasticallyLE.isUpperSet_setOf_eq_true i)
    rw [← hμm, hmp] at hlo
    exact le_antisymm hhi hlo
  rw [key x hx, key y hy]

/-- **The Lebowitz–Martin-Löf/Ruelle criterion** (Georgii, Section 6.2, the paragraph after
(6.9), citing Lebowitz–Martin-Löf (1972) and Ruelle (1972)):
`|𝒢(βΦ)| > 1 ↔ μ₊^β(σ₀) > 0`. -/
theorem nontrivial_GP_ising2D_iff_spontaneousMagnetisation_pos (hb : 0 ≤ b) :
    (GP (S := Site) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b)).Nontrivial
      ↔ 0 < spontaneousMagnetisation b := by
  refine ⟨fun hnt ↦ ?_, nontrivial_GP_ising2D_of_spontaneousMagnetisation_pos b hb⟩
  rcases (spontaneousMagnetisation_nonneg b hb).lt_or_eq with hpos | hzero
  · exact hpos
  · exact absurd (subsingleton_GP_ising2D_of_spontaneousMagnetisation_eq_zero b hb hzero.symm)
      (Set.not_subsingleton_iff.2 hnt)

/-- **Non-uniqueness of the Ising Gibbs measure is monotone in `β`.**  This is the consequence
of the Lebowitz–Martin-Löf/Ruelle criterion and Griffiths' inequality that Georgii uses to
define the critical inverse temperature. -/
theorem nontrivial_GP_ising2D_of_nontrivial_of_le {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁) (h12 : β₁ ≤ β₂)
    (hnt : (GP (S := Site) (E := Bool)
      (isingSpecification (latticeGraph 2) 1 0 β₁)).Nontrivial) :
    (GP (S := Site) (E := Bool)
      (isingSpecification (latticeGraph 2) 1 0 β₂)).Nontrivial := by
  have h1 : 0 < spontaneousMagnetisation β₁ :=
    (nontrivial_GP_ising2D_iff_spontaneousMagnetisation_pos β₁ h0).1 hnt
  exact (nontrivial_GP_ising2D_iff_spontaneousMagnetisation_pos β₂ (h0.trans h12)).2
    (lt_of_lt_of_le h1 (spontaneousMagnetisation_mono h0 h12))

end LML

end MeasureTheory.GibbsMeasure

end

end
