/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.Ising
public import GibbsMeasure.Mathlib.MeasureTheory.Order.Holley

/-!
# Holley/FKG monotonicity for the ferromagnetic Ising model

For a ferromagnetic coupling `J ≥ 0`, an arbitrary external field `h` and `β ≥ 0`, the
finite-volume Ising Gibbs distribution `γ_Λ(· | ω)` is stochastically increasing in the boundary
condition `ω`, and, under the all-`+` boundary condition, stochastically decreasing in the volume
`Λ` (dually, increasing in `Λ` under the all-`-` boundary condition).  Spins are ordered by
`false < true`, configurations by the product order.

The route is Holley's inequality in the form `sum_indicator_le_of_holley`.  Writing
`γ_Λ(A | ω) = ∑_ζ f_ω(ζ) 1_A(juxt Λ ω ζ)` for the normalised Boltzmann weights `f_ω` on the finitely
many inner configurations `ζ : Λ → Bool` (`isingSpecification_apply_eq`), the lattice condition
`f_ω(ζ) f_{ω'}(ξ) ≤ f_ω(ζ ⊓ ξ) f_{ω'}(ζ ⊔ ξ)` reduces, since the partition functions cancel and
`β ≥ 0`, to submodularity of the Ising Hamiltonian,
`H_Λ(η ⊓ ζ) + H_Λ(η ⊔ ζ) ≤ H_Λ(η) + H_Λ(ζ)`.  The latter holds interaction term by interaction
term: the field terms are modular (`spin_inf_add_spin_sup`) and the ferromagnetic bond terms are
submodular (`spin_mul_spin_add_le`).  Boundary bonds need no separate treatment because
`juxt Λ ω (ζ ⊓ ξ) = juxt Λ ω ζ ⊓ juxt Λ ω' ξ` already when `ω ≤ ω'` (`juxt_inf_juxt`); the
inequality behind that step is recorded separately as `spin_boundary_nonneg`.

Monotonicity in the volume is then the consistency relation `γ_Λ' = γ_Λ' γ_Λ` for `Λ ⊆ Λ'`
together with `η ≤ (fun _ ↦ true)` for every `η`.

The Ising potential is Georgii (2.16)/(2.17) with the coefficients of formula (3.13), and its
specification is Georgii Definition (2.9); see `GibbsMeasure/Model/Ising.lean`.

## Main declarations

* `spin_inf_add_spin_sup`, `spin_mul_spin_add_le`, `spin_boundary_nonneg`: the pointwise `±1`-spin
  inequalities behind the lattice condition (field terms, interior bonds, boundary bonds).
* `isingPotential_inf_add_sup_le`, `isingHamiltonian_inf_add_sup_le`: submodularity of the
  ferromagnetic Ising interaction terms and of the finite-volume Hamiltonian.
* `isingSpecification_apply_eq`: the finite-volume Gibbs distribution as an explicit finite sum.
* `stochasticallyLE_isingSpecification_of_le`: **(i)** monotonicity in the boundary condition.
* `stochasticallyLE_isingSpecification_plus`, `stochasticallyLE_isingSpecification_minus`:
  **(ii)** monotonicity in the volume under the constant boundary conditions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Pointwise `±1`-spin inequalities -/

/-- `s(a ⊓ b) + s(a ⊔ b) = s a + s b`: the field terms of the Ising Hamiltonian are modular. -/
lemma spin_inf_add_spin_sup (a b : Bool) : spin (a ⊓ b) + spin (a ⊔ b) = spin a + spin b := by
  cases a <;> cases b <;> norm_num [spin]

/-- The **interior-bond inequality**: `s(x ⊔ y) s(u ⊔ v) + s(x ⊓ y) s(u ⊓ v) ≥ s x s u + s y s v`.
This is the lattice condition for a ferromagnetic bond with both endpoints in the volume. -/
lemma spin_mul_spin_add_le (x y u v : Bool) :
    spin x * spin u + spin y * spin v
      ≤ spin (x ⊓ y) * spin (u ⊓ v) + spin (x ⊔ y) * spin (u ⊔ v) := by
  cases x <;> cases y <;> cases u <;> cases v <;> norm_num [spin]

/-- The **boundary-bond inequality**: for `p ≤ q` (the two boundary spins, ordered),
`(s(x ⊓ y) - s x) p + (s(x ⊔ y) - s y) q ≥ 0`.  Both brackets vanish unless `x = true` and
`y = false`, when they are `-2` and `+2`.

This is the content of a bond with one endpoint inside the volume and one outside.  It is not
needed in the proofs below, because `juxt_inf_juxt` and `juxt_sup_juxt` turn boundary bonds into
interior bonds; it is recorded because it is the mathematical core of Holley's argument. -/
lemma spin_boundary_nonneg {p q : ℝ} (hpq : p ≤ q) (x y : Bool) :
    0 ≤ (spin (x ⊓ y) - spin x) * p + (spin (x ⊔ y) - spin y) * q := by
  cases x <;> cases y <;> norm_num [spin]
  linarith

/-! ### Submodularity of the ferromagnetic Ising Hamiltonian -/

section Submodular
variable {S : Type*} (G : SimpleGraph S) (J h : ℝ)

/-- Every interaction term of the ferromagnetic Ising potential is submodular. -/
lemma isingPotential_inf_add_sup_le (hJ : 0 ≤ J) (A : Finset S) (η ζ : S → Bool) :
    isingPotential G J h A (η ⊓ ζ) + isingPotential G J h A (η ⊔ ζ)
      ≤ isingPotential G J h A η + isingPotential G J h A ζ := by
  classical
  simp only [isingPotential]
  by_cases h1 : A.card = 1
  · simp only [Potential.nearestNeighbourPair_apply_card_one h1]
    have key : (∑ i ∈ A, spin ((η ⊓ ζ) i)) + ∑ i ∈ A, spin ((η ⊔ ζ) i)
        = (∑ i ∈ A, spin (η i)) + ∑ i ∈ A, spin (ζ i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ spin_inf_add_spin_sup (η i) (ζ i)
    refine le_of_eq ?_
    calc -h * (∑ i ∈ A, spin ((η ⊓ ζ) i)) + -h * ∑ i ∈ A, spin ((η ⊔ ζ) i)
        = -h * ((∑ i ∈ A, spin ((η ⊓ ζ) i)) + ∑ i ∈ A, spin ((η ⊔ ζ) i)) := by ring
      _ = -h * ((∑ i ∈ A, spin (η i)) + ∑ i ∈ A, spin (ζ i)) := by rw [key]
      _ = -h * (∑ i ∈ A, spin (η i)) + -h * ∑ i ∈ A, spin (ζ i) := by ring
  · by_cases h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h2.1
      simp only [Potential.nearestNeighbourPair_apply_pair h2, Finset.prod_pair hab,
        Pi.inf_apply, Pi.sup_apply]
      have hkey := spin_mul_spin_add_le (η a) (ζ a) (η b) (ζ b)
      nlinarith [hkey, hJ]
    · simp only [Potential.nearestNeighbourPair_apply_eq_zero h1 h2, add_zero, le_refl]

/-- **Submodularity of the ferromagnetic Ising Hamiltonian**: `H_Λ(η ⊓ ζ) + H_Λ(η ⊔ ζ) ≤
H_Λ(η) + H_Λ(ζ)` whenever `J ≥ 0`.  This is the lattice condition behind Holley's inequality. -/
lemma isingHamiltonian_inf_add_sup_le [G.LocallyFinite] (hJ : 0 ≤ J) (Λ : Finset S)
    (η ζ : S → Bool) :
    (isingPotential G J h).hamiltonian Λ (η ⊓ ζ) + (isingPotential G J h).hamiltonian Λ (η ⊔ ζ)
      ≤ (isingPotential G J h).hamiltonian Λ η + (isingPotential G J h).hamiltonian Λ ζ := by
  classical
  simp only [Potential.hamiltonian_eq_interactingHamiltonian, Potential.interactingHamiltonian]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun A _ ↦ isingPotential_inf_add_sup_le G J h hJ A η ζ

end Submodular

/-! ### The finite-volume Ising distribution as an explicit finite sum -/

section Weights
variable {S : Type*} [DecidableEq S] (G : SimpleGraph S) (J h β : ℝ)

/-- The unnormalised Boltzmann weight `exp(-β H_Λ)` of the inner configuration `ζ` under the
boundary condition `ω`. -/
def isingWeight (Λ : Finset S) (ω : S → Bool) (ζ : Λ → Bool) : ℝ :=
  Real.exp (-β * (isingPotential G J h).hamiltonian Λ (juxt (Λ : Set S) ω ζ))

omit [DecidableEq S] in
lemma isingWeight_pos (Λ : Finset S) (ω : S → Bool) (ζ : Λ → Bool) :
    0 < isingWeight G J h β Λ ω ζ := Real.exp_pos _

lemma isingWeight_sum_pos (Λ : Finset S) (ω : S → Bool) :
    0 < ∑ ξ : (Λ → Bool), isingWeight G J h β Λ ω ξ :=
  Finset.sum_pos (fun ξ _ ↦ isingWeight_pos G J h β Λ ω ξ) Finset.univ_nonempty

/-- The normalised finite-volume Ising weights: `γ_Λ(· | ω)` is the law of `juxt Λ ω ζ` when `ζ`
is distributed according to `isingDensity`. -/
def isingDensity (Λ : Finset S) (ω : S → Bool) (ζ : Λ → Bool) : ℝ :=
  isingWeight G J h β Λ ω ζ / ∑ ξ : (Λ → Bool), isingWeight G J h β Λ ω ξ

lemma isingDensity_nonneg (Λ : Finset S) (ω : S → Bool) : 0 ≤ isingDensity G J h β Λ ω :=
  fun ζ ↦ le_of_lt (div_pos (isingWeight_pos G J h β Λ ω ζ) (isingWeight_sum_pos G J h β Λ ω))

lemma sum_isingDensity (Λ : Finset S) (ω : S → Bool) :
    ∑ ζ : (Λ → Bool), isingDensity G J h β Λ ω ζ = 1 := by
  simp only [isingDensity, ← Finset.sum_div]
  exact div_self (isingWeight_sum_pos G J h β Λ ω).ne'

omit [DecidableEq S] in
/-- Under a ferromagnetic coupling the weights satisfy Holley's lattice condition. -/
lemma isingWeight_mul_le [G.LocallyFinite] (hJ : 0 ≤ J) (hβ : 0 ≤ β) (Λ : Finset S)
    {ω ω' : S → Bool} (hω : ω ≤ ω') (ζ ξ : Λ → Bool) :
    isingWeight G J h β Λ ω ζ * isingWeight G J h β Λ ω' ξ
      ≤ isingWeight G J h β Λ ω (ζ ⊓ ξ) * isingWeight G J h β Λ ω' (ζ ⊔ ξ) := by
  simp only [isingWeight, ← Real.exp_add]
  rw [juxt_inf_juxt hω ζ ξ, juxt_sup_juxt hω ζ ξ]
  refine Real.exp_le_exp.2 ?_
  have hsub := isingHamiltonian_inf_add_sup_le G J h hJ Λ
    (juxt (Λ : Set S) ω ζ) (juxt (Λ : Set S) ω' ξ)
  nlinarith [hsub, hβ]

lemma isingDensity_mul_le [G.LocallyFinite] (hJ : 0 ≤ J) (hβ : 0 ≤ β) (Λ : Finset S)
    {ω ω' : S → Bool} (hω : ω ≤ ω') (ζ ξ : Λ → Bool) :
    isingDensity G J h β Λ ω ζ * isingDensity G J h β Λ ω' ξ
      ≤ isingDensity G J h β Λ ω (ζ ⊓ ξ) * isingDensity G J h β Λ ω' (ζ ⊔ ξ) := by
  simp only [isingDensity, div_mul_div_comm]
  have hpos : 0 < (∑ a : (Λ → Bool), isingWeight G J h β Λ ω a) *
      ∑ b : (Λ → Bool), isingWeight G J h β Λ ω' b :=
    mul_pos (isingWeight_sum_pos G J h β Λ ω) (isingWeight_sum_pos G J h β Λ ω')
  have key := isingWeight_mul_le G J h β hJ hβ Λ hω ζ ξ
  calc isingWeight G J h β Λ ω ζ * isingWeight G J h β Λ ω' ξ /
        ((∑ a : (Λ → Bool), isingWeight G J h β Λ ω a) *
          ∑ b : (Λ → Bool), isingWeight G J h β Λ ω' b)
      = isingWeight G J h β Λ ω ζ * isingWeight G J h β Λ ω' ξ *
        ((∑ a : (Λ → Bool), isingWeight G J h β Λ ω a) *
          ∑ b : (Λ → Bool), isingWeight G J h β Λ ω' b)⁻¹ := div_eq_mul_inv _ _
    _ ≤ isingWeight G J h β Λ ω (ζ ⊓ ξ) * isingWeight G J h β Λ ω' (ζ ⊔ ξ) *
        ((∑ a : (Λ → Bool), isingWeight G J h β Λ ω a) *
          ∑ b : (Λ → Bool), isingWeight G J h β Λ ω' b)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.2 hpos.le)
    _ = isingWeight G J h β Λ ω (ζ ⊓ ξ) * isingWeight G J h β Λ ω' (ζ ⊔ ξ) /
        ((∑ a : (Λ → Bool), isingWeight G J h β Λ ω a) *
          ∑ b : (Λ → Bool), isingWeight G J h β Λ ω' b) := (div_eq_mul_inv _ _).symm

end Weights

/-! ### The finite-volume Gibbs distribution in closed form -/

section Spec
variable {S : Type*} [Countable S] [DecidableEq S] (G : SimpleGraph S) [G.LocallyFinite]
  (J h β : ℝ)

private lemma ennreal_div_mul_cancel {a B c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    a / (B * c) * c = a / B := by
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inr hct) (Or.inr hc0),
    div_eq_mul_inv]
  rw [show a * (B⁻¹ * c⁻¹) * c = a * B⁻¹ * (c⁻¹ * c) by ring, ENNReal.inv_mul_cancel hc0 hct,
    mul_one]

omit [Countable S] [DecidableEq S] in
private lemma pi_uniformSpinMeasure_singleton (Λ : Finset S) (ζ : Λ → Bool) :
    (Measure.pi fun _ : Λ ↦ uniformSpinMeasure) {ζ} = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card Λ := by
  have h1 : ∀ b : Bool, uniformSpinMeasure {b} = (2 : ℝ≥0∞)⁻¹ := by
    intro b
    change ((2 : ℝ≥0∞)⁻¹ • Measure.count) {b} = _
    rw [Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
  rw [Measure.pi_singleton]
  simp [h1, Finset.prod_const]

private lemma lintegral_isssd_uniform (Λ : Finset S) (η : S → Bool) {F : (S → Bool) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ x, F x ∂(Specification.isssd (S := S) (E := Bool) uniformSpinMeasure Λ η)
      = (∑ ζ : (Λ → Bool), F (juxt (Λ : Set S) η ζ)) * (2 : ℝ≥0∞)⁻¹ ^ Fintype.card Λ := by
  have hker : (Specification.isssd (S := S) (E := Bool) uniformSpinMeasure Λ η)
      = Measure.map (juxt (Λ : Set S) η) (Measure.pi fun _ : Λ ↦ uniformSpinMeasure) := rfl
  rw [hker, lintegral_map hF Measurable.juxt, lintegral_fintype, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ζ _ ↦ by rw [pi_uniformSpinMeasure_singleton]

private lemma premodifierZ_ising (Λ : Finset S) (ω : S → Bool) (ζ : Λ → Bool) :
    Specification.premodifierZ (S := S) (E := Bool) uniformSpinMeasure
        ((isingPotential G J h).boltzmannFactor β) Λ (juxt (Λ : Set S) ω ζ)
      = (∑ ξ : (Λ → Bool), ENNReal.ofReal (isingWeight G J h β Λ ω ξ)) *
          (2 : ℝ≥0∞)⁻¹ ^ Fintype.card Λ := by
  rw [Specification.premodifierZ,
    lintegral_isssd_uniform Λ _ (Potential.measurable_boltzmannFactor
      (Φ := isingPotential G J h) β Λ)]
  congr 1
  refine Finset.sum_congr rfl fun ξ _ ↦ ?_
  simp only [Potential.boltzmannFactor, isingWeight, juxt_juxt]

/-- **The finite-volume Ising distribution in closed form.** For a measurable `A`,
`γ_Λ(A | ω) = ∑_ζ f_ω(ζ) 1_A(ζ ω)`, where `f_ω` are the normalised Boltzmann weights. -/
theorem isingSpecification_apply_eq (Λ : Finset S) (ω : S → Bool) {A : Set (S → Bool)}
    (hA : MeasurableSet A) :
    isingSpecification G J h β Λ ω A
      = ENNReal.ofReal (∑ ζ : (Λ → Bool), isingDensity G J h β Λ ω ζ *
          A.indicator (1 : (S → Bool) → ℝ) (juxt (Λ : Set S) ω ζ)) := by
  set ρ := Specification.premodifierNorm (S := S) (E := Bool) uniformSpinMeasure
    ((isingPotential G J h).boltzmannFactor β) with hρdef
  have hρmeas : Measurable (ρ Λ) :=
    Specification.premodifierNorm_measurable uniformSpinMeasure
      (Potential.isPremodifier_boltzmannFactor (Φ := isingPotential G J h) β) Λ
  have hmod : isingSpecification G J h β Λ ω
      = (Specification.isssd (S := S) (E := Bool) uniformSpinMeasure Λ ω).withDensity (ρ Λ) := rfl
  set c : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ Fintype.card Λ with hcdef
  have hc0 : c ≠ 0 := by
    simp [hcdef]
  have hct : c ≠ ⊤ := by
    simp [hcdef]
  set W : ℝ := ∑ ξ : (Λ → Bool), isingWeight G J h β Λ ω ξ with hWdef
  have hWpos : 0 < W := isingWeight_sum_pos G J h β Λ ω
  have hB : (∑ ξ : (Λ → Bool), ENNReal.ofReal (isingWeight G J h β Λ ω ξ))
      = ENNReal.ofReal W := by
    rw [hWdef, ENNReal.ofReal_sum_of_nonneg]
    exact fun ξ _ ↦ (isingWeight_pos G J h β Λ ω ξ).le
  have hterm : ∀ ζ : (Λ → Bool), A.indicator (ρ Λ) (juxt (Λ : Set S) ω ζ) * c
      = ENNReal.ofReal (isingDensity G J h β Λ ω ζ *
          A.indicator (1 : (S → Bool) → ℝ) (juxt (Λ : Set S) ω ζ)) := by
    intro ζ
    by_cases hmem : juxt (Λ : Set S) ω ζ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      have hρval : ρ Λ (juxt (Λ : Set S) ω ζ)
          = ENNReal.ofReal (isingWeight G J h β Λ ω ζ) / (ENNReal.ofReal W * c) := by
        rw [hρdef, Specification.premodifierNorm, premodifierZ_ising G J h β Λ ω ζ, hB]
        rfl
      rw [hρval, ennreal_div_mul_cancel hc0 hct, Pi.one_apply, mul_one,
        isingDensity, ← hWdef, ENNReal.ofReal_div_of_pos hWpos]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      simp
  rw [hmod, withDensity_apply _ hA, ← lintegral_indicator hA (ρ Λ),
    lintegral_isssd_uniform Λ ω (hρmeas.indicator hA), Finset.sum_mul, ← hcdef]
  rw [Finset.sum_congr rfl fun ζ _ ↦ hterm ζ, ← ENNReal.ofReal_sum_of_nonneg]
  intro ζ _
  exact mul_nonneg (isingDensity_nonneg G J h β Λ ω ζ)
    (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)

end Spec

/-! ### The main monotonicity theorems -/

section Main
variable {S : Type*} [Countable S] (G : SimpleGraph S) [G.LocallyFinite] (J h β : ℝ)

/-- **(i) Holley's inequality for the Ising model.** For a ferromagnetic coupling `J ≥ 0` and
`β ≥ 0`, the finite-volume Gibbs distribution is stochastically increasing in the boundary
condition. -/
theorem stochasticallyLE_isingSpecification_of_le (hJ : 0 ≤ J) (hβ : 0 ≤ β) (Λ : Finset S)
    {ω ω' : S → Bool} (hω : ω ≤ ω') :
    (isingSpecification G J h β Λ ω).StochasticallyLE (isingSpecification G J h β Λ ω') := by
  classical
  intro A hA hupper
  rw [isingSpecification_apply_eq G J h β Λ ω hA, isingSpecification_apply_eq G J h β Λ ω' hA]
  refine ENNReal.ofReal_le_ofReal ?_
  refine sum_indicator_le_of_holley (f := isingDensity G J h β Λ ω)
    (g := isingDensity G J h β Λ ω') (F := juxt (Λ : Set S) ω) (G := juxt (Λ : Set S) ω')
    (isingDensity_nonneg G J h β Λ ω) (isingDensity_nonneg G J h β Λ ω') ?_
    (fun a b ↦ isingDensity_mul_le G J h β hJ hβ Λ hω a b) (monotone_juxt ω')
    (fun a ↦ juxt_le_juxt hω a) hupper
  rw [sum_isingDensity, sum_isingDensity]

/-- **Under the all-`+` boundary condition the Ising distribution decreases with the volume.** -/
theorem stochasticallyLE_isingSpecification_plus (hJ : 0 ≤ J) (hβ : 0 ≤ β)
    {Λ Λ' : Finset S} (hΛ : Λ ⊆ Λ') :
    (isingSpecification G J h β Λ' (fun _ ↦ true)).StochasticallyLE
      (isingSpecification G J h β Λ (fun _ ↦ true)) := by
  intro A hA hupper
  have hbind : (isingSpecification G J h β Λ' (fun _ ↦ true)).bind
      (isingSpecification G J h β Λ) = isingSpecification G J h β Λ' (fun _ ↦ true) :=
    Specification.bind hΛ _
  have hmeas : Measurable (isingSpecification G J h β Λ : (S → Bool) → Measure (S → Bool)) :=
    (Kernel.measurable (isingSpecification G J h β Λ)).mono cylinderEvents_le_pi le_rfl
  calc isingSpecification G J h β Λ' (fun _ ↦ true) A
      = ((isingSpecification G J h β Λ' (fun _ ↦ true)).bind
          (isingSpecification G J h β Λ)) A := by rw [hbind]
    _ = ∫⁻ η, isingSpecification G J h β Λ η A
          ∂(isingSpecification G J h β Λ' (fun _ ↦ true)) :=
        Measure.bind_apply hA hmeas.aemeasurable
    _ ≤ ∫⁻ _, isingSpecification G J h β Λ (fun _ ↦ true) A
          ∂(isingSpecification G J h β Λ' (fun _ ↦ true)) :=
        lintegral_mono fun η ↦ stochasticallyLE_isingSpecification_of_le G J h β hJ hβ Λ
          (fun x ↦ Bool.le_true (η x)) hA hupper
    _ = isingSpecification G J h β Λ (fun _ ↦ true) A := by
        rw [lintegral_const, measure_univ, mul_one]

/-- **Under the all-`-` boundary condition the Ising distribution increases with the volume.** -/
theorem stochasticallyLE_isingSpecification_minus (hJ : 0 ≤ J) (hβ : 0 ≤ β)
    {Λ Λ' : Finset S} (hΛ : Λ ⊆ Λ') :
    (isingSpecification G J h β Λ (fun _ ↦ false)).StochasticallyLE
      (isingSpecification G J h β Λ' (fun _ ↦ false)) := by
  intro A hA hupper
  have hbind : (isingSpecification G J h β Λ' (fun _ ↦ false)).bind
      (isingSpecification G J h β Λ) = isingSpecification G J h β Λ' (fun _ ↦ false) :=
    Specification.bind hΛ _
  have hmeas : Measurable (isingSpecification G J h β Λ : (S → Bool) → Measure (S → Bool)) :=
    (Kernel.measurable (isingSpecification G J h β Λ)).mono cylinderEvents_le_pi le_rfl
  calc isingSpecification G J h β Λ (fun _ ↦ false) A
      = ∫⁻ _, isingSpecification G J h β Λ (fun _ ↦ false) A
          ∂(isingSpecification G J h β Λ' (fun _ ↦ false)) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ η, isingSpecification G J h β Λ η A
          ∂(isingSpecification G J h β Λ' (fun _ ↦ false)) :=
        lintegral_mono fun η ↦ stochasticallyLE_isingSpecification_of_le G J h β hJ hβ Λ
          (fun x ↦ Bool.false_le (η x)) hA hupper
    _ = ((isingSpecification G J h β Λ' (fun _ ↦ false)).bind
          (isingSpecification G J h β Λ)) A :=
        (Measure.bind_apply hA hmeas.aemeasurable).symm
    _ = isingSpecification G J h β Λ' (fun _ ↦ false) A := by rw [hbind]

end Main

end MeasureTheory.GibbsMeasure

end

