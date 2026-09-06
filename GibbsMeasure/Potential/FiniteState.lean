/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Summable

/-!
# The Gibbs kernels over a finite state space, in closed form

Over a finite single-spin space `E` and a *uniform* a priori measure `λ` (all singletons of the
same mass, Georgii's "equidistribution"), the finite-volume Gibbs kernel of Definition (2.9) is
an elementary ratio of finite sums,

`γ^Φ_Λ(A | ω) = (∑_ζ e^{-β H_Λ(ζω)} 1_A(ζω)) / (∑_ζ e^{-β H_Λ(ζω)})`,

the sums being over the `|E|^{|Λ|}` configurations `ζ` of the volume `Λ`; the mass of a single
configuration cancels between numerator and denominator.

## Main results

* `Specification.lintegral_isssd_of_measure_singleton_eq`: integrating against the independent
  kernel of a uniform finite a priori measure is a finite sum times the constant `c^{|Λ|}`.
* `Specification.sum_measure_singleton_pow_eq_one`: that constant is `|E^Λ|⁻¹`, in the form
  `|E^Λ| · c^{|Λ|} = 1`; in particular it is neither `0` nor `∞`.
* `Potential.gibbsSpecificationOfAbsolutelySummable_apply_of_measure_singleton_eq`:
  **Georgii Definition (2.9) over a finite state space**, the closed form above.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Specification

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] [Fintype E]
  [MeasurableSingletonClass E]

/-- Integrating against the independent kernel of a **uniform** finite a priori measure: a finite
sum over the configurations of the volume, times the common mass `c^{|Λ|}` of a single
configuration.  This is `Specification.lintegral_isssd_fintype` with the weights collected. -/
lemma lintegral_isssd_of_measure_singleton_eq (ν : Measure E) [IsProbabilityMeasure ν]
    {c : ℝ≥0∞} (hc : ∀ x : E, ν {x} = c) (Λ : Finset S) (η : S → E)
    {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(isssd (S := S) (E := E) ν Λ η)
      = (∑ ζ : (Λ → E), F (juxt (Λ : Set S) η ζ)) * c ^ Fintype.card Λ := by
  rw [lintegral_isssd_fintype ν Λ η hF, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  simp only [hc, Finset.prod_const, Finset.card_univ]

/-- The common mass of a single configuration of `Λ` is the reciprocal of the number of
configurations. -/
lemma sum_measure_singleton_pow_eq_one (ν : Measure E) [IsProbabilityMeasure ν]
    {c : ℝ≥0∞} (hc : ∀ x : E, ν {x} = c) (Λ : Finset S) :
    (Fintype.card (Λ → E) : ℝ≥0∞) * c ^ Fintype.card Λ = 1 := by
  classical
  have := MeasureTheory.nonempty_of_isProbabilityMeasure ν
  have h := lintegral_isssd_of_measure_singleton_eq ν hc Λ (Classical.arbitrary (S → E))
    (F := fun _ ↦ 1) measurable_const
  rw [lintegral_const, measure_univ, one_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at h
  exact h.symm

end Specification

namespace Potential

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E] [Fintype E]
  [MeasurableSingletonClass E] {Φ : Potential S E} [IsPotential Φ] [IsAbsolutelySummable Φ]

/-- **Georgii Definition (2.9) over a finite state space with a uniform a priori measure.**
For every measurable `A`,
`γ^Φ_Λ(A | ω) = (∑_ζ e^{-β H_Λ(ζω)} 1_A(ζω)) / (∑_ζ e^{-β H_Λ(ζω)})`,
the sums running over the configurations `ζ : Λ → E` of the volume.  The mass `c` of a single
spin value cancels; the hypothesis `hc` is Georgii's equidistribution. -/
theorem gibbsSpecificationOfAbsolutelySummable_apply_of_measure_singleton_eq
    (ν : Measure E) [IsProbabilityMeasure ν] {c : ℝ≥0∞} (hc : ∀ x : E, ν {x} = c)
    (β : ℝ) (Λ : Finset S) (ω : S → E) {A : Set (S → E)} (hA : MeasurableSet A) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ ω A
      = ENNReal.ofReal
          ((∑ ζ : (Λ → E), Real.exp (-β * Φ.hamiltonian Λ (juxt (Λ : Set S) ω ζ)) *
                A.indicator (1 : (S → E) → ℝ) (juxt (Λ : Set S) ω ζ))
            / ∑ ζ : (Λ → E), Real.exp (-β * Φ.hamiltonian Λ (juxt (Λ : Set S) ω ζ))) := by
  classical
  have := MeasureTheory.nonempty_of_isProbabilityMeasure ν
  set ρ := Specification.premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β) with hρdef
  have hρmeas : Measurable (ρ Λ) :=
    Specification.measurable_relNorm (γ := Specification.isssd ν)
      (isPremodifier_boltzmannFactor (Φ := Φ) β).measurable Λ
  have hmod : gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ ω
      = (Specification.isssd (S := S) (E := E) ν Λ ω).withDensity (ρ Λ) := rfl
  -- the mass of a single configuration of `Λ`
  set cc : ℝ≥0∞ := c ^ Fintype.card Λ with hccdef
  have hcard := Specification.sum_measure_singleton_pow_eq_one (S := S) ν hc Λ
  rw [← hccdef] at hcard
  have hc0 : cc ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcard
    exact zero_ne_one hcard
  have hct : cc ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by exact_mod_cast Fintype.card_ne_zero)] at hcard
    exact ENNReal.top_ne_one hcard
  have hne : Nonempty (Λ → E) := by
    rcases isEmpty_or_nonempty (Λ → E) with hE | hE
    · rw [Fintype.card_eq_zero, Nat.cast_zero, zero_mul] at hcard
      exact absurd hcard zero_ne_one
    · exact hE
  -- the partition function as a real number
  set W : ℝ := ∑ ζ : (Λ → E), Real.exp (-β * Φ.hamiltonian Λ (juxt (Λ : Set S) ω ζ)) with hWdef
  have hWpos : 0 < W :=
    Finset.sum_pos (fun ζ _ ↦ Real.exp_pos _) (Finset.univ_nonempty (α := Λ → E))
  -- the partition function computed at a resampled configuration
  have hZ : ∀ ζ : (Λ → E),
      Specification.relZ (Specification.isssd (S := S) (E := E) ν) (Φ.boltzmannFactor β) Λ
          (juxt (Λ : Set S) ω ζ) = ENNReal.ofReal W * cc := by
    intro ζ
    rw [Specification.relZ, Specification.lintegral_isssd_of_measure_singleton_eq ν hc Λ _
      (measurable_boltzmannFactor (Φ := Φ) β Λ), ← hccdef]
    congr 1
    rw [hWdef, ENNReal.ofReal_sum_of_nonneg (fun ξ _ ↦ (Real.exp_pos _).le)]
    exact Finset.sum_congr rfl fun ξ _ ↦ by rw [juxt_juxt, boltzmannFactor]
  have hterm : ∀ ζ : (Λ → E), A.indicator (ρ Λ) (juxt (Λ : Set S) ω ζ) * cc
      = ENNReal.ofReal (Real.exp (-β * Φ.hamiltonian Λ (juxt (Λ : Set S) ω ζ)) *
          A.indicator (1 : (S → E) → ℝ) (juxt (Λ : Set S) ω ζ) / W) := by
    intro ζ
    by_cases hmem : juxt (Λ : Set S) ω ζ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      rw [hρdef, Specification.premodifierNorm, Specification.relNorm, hZ ζ, boltzmannFactor,
        ENNReal.div_mul _ (Or.inr hc0) (Or.inr hct), ENNReal.mul_div_cancel_right hc0 hct,
        Pi.one_apply, mul_one, ENNReal.ofReal_div_of_pos hWpos]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      simp
  rw [hmod, withDensity_apply _ hA, ← lintegral_indicator hA (ρ Λ),
    Specification.lintegral_isssd_of_measure_singleton_eq ν hc Λ ω (hρmeas.indicator hA),
    Finset.sum_mul, ← hccdef, Finset.sum_congr rfl fun ζ _ ↦ hterm ζ,
    ← ENNReal.ofReal_sum_of_nonneg, ← Finset.sum_div]
  intro ζ _
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le
    (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)) hWpos.le

end Potential

end
