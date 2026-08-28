/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Quasilocal
public import GibbsMeasure.Specification.Quasilocality

/-!
# Quasilocality of the Gibbsian specification of an absolutely summable potential

Georgii Proposition (2.24)(b) and Example (2.25) for `Φ` in the space `ℬ` of (2.11): the partition
function `Z_Λ^Φ` and the density `ρ_Λ^Φ = h_Λ^Φ / Z_Λ^Φ` are quasilocal, hence so is `γ^Φ`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Filter Function GibbsMeasure MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E] {Φ : Potential S E} {Λ : Finset S}

lemma boltzmannLp_le [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    (⇑(Φ.boltzmannLp β Λ)) η ≤ Real.exp (|β| * Φ.hamiltonianBound Λ) := by
  rw [coeFn_boltzmannLp]
  refine Real.exp_le_exp.2 (le_trans (le_abs_self _) ?_)
  rw [abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (abs_hamiltonian_le (Φ := Φ) Λ η) (abs_nonneg _)

lemma le_boltzmannLp [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    Real.exp (-(|β| * Φ.hamiltonianBound Λ)) ≤ (⇑(Φ.boltzmannLp β Λ)) η := by
  rw [coeFn_boltzmannLp]
  refine Real.exp_le_exp.2 (le_trans ?_ (neg_abs_le _))
  rw [abs_mul, abs_neg]
  exact neg_le_neg (mul_le_mul_of_nonneg_left (abs_hamiltonian_le (Φ := Φ) Λ η) (abs_nonneg _))

variable (Φ) in
/-- The partition function `Z_Λ^Φ` as a bounded observable. -/
def partitionLp [IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν]
    (β : ℝ) (Λ : Finset S) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  Specification.action (Specification.isssd ν) Λ (Φ.boltzmannLp β Λ)

variable (ν : Measure E) [IsProbabilityMeasure ν]

lemma le_partitionLp [IsPotential Φ] [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S)
    (η : S → E) :
    Real.exp (-(|β| * Φ.hamiltonianBound Λ)) ≤ (⇑(Φ.partitionLp ν β Λ)) η := by
  have hpm := Specification.isProbabilityMeasure_isssdFun_apply (S := S) (E := E) ν Λ η
  rw [partitionLp, Specification.action_apply]
  calc Real.exp (-(|β| * Φ.hamiltonianBound Λ))
      = ∫ _ : S → E, Real.exp (-(|β| * Φ.hamiltonianBound Λ)) ∂(Specification.isssd ν Λ η) := by
        rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ _ := by
        refine integral_mono (integrable_const _) ?_ fun x ↦ le_boltzmannLp (Φ := Φ) β Λ x
        exact Integrable.mono' (integrable_const ‖Φ.boltzmannLp β Λ‖)
          ((measurable_of_mem_quasilocalFunctions
            (boltzmannLp_mem_quasilocalFunctions (Φ := Φ) β Λ)).aestronglyMeasurable)
          (.of_forall fun x ↦ by simpa using lp.norm_apply_le_norm_top (Φ.boltzmannLp β Λ) x)

lemma partitionLp_pos [IsPotential Φ] [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S)
    (η : S → E) :
    0 < (⇑(Φ.partitionLp ν β Λ)) η :=
  lt_of_lt_of_le (Real.exp_pos _) (le_partitionLp ν β Λ η)

/-- `Z_Λ^Φ` is a quasilocal observable. -/
theorem partitionLp_mem_quasilocalFunctions [DecidableEq S] [Nonempty E] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) :
    Φ.partitionLp ν β Λ ∈ quasilocalFunctions S E :=
  Specification.isQuasilocal_isssd ν Λ _ (boltzmannLp_mem_quasilocalFunctions (Φ := Φ) β Λ)

lemma integrable_boltzmannLp [IsPotential Φ] [IsAbsolutelySummable Φ]
    (β : ℝ) (Λ : Finset S) (η : S → E) :
    Integrable (⇑(Φ.boltzmannLp β Λ)) (Specification.isssd ν Λ η) := by
  have hpm := Specification.isProbabilityMeasure_isssdFun_apply (S := S) (E := E) ν Λ η
  exact Integrable.mono' (integrable_const ‖Φ.boltzmannLp β Λ‖)
    ((measurable_of_mem_quasilocalFunctions
      (boltzmannLp_mem_quasilocalFunctions (Φ := Φ) β Λ)).aestronglyMeasurable)
    (.of_forall fun x ↦ by simpa using lp.norm_apply_le_norm_top (Φ.boltzmannLp β Λ) x)

/-- Bridge between the `ℝ≥0∞`-valued and the `lp`-valued Boltzmann factor. -/
lemma boltzmannFactor_eq_ofReal [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    Φ.boltzmannFactor β Λ η = ENNReal.ofReal ((⇑(Φ.boltzmannLp β Λ)) η) := by
  rw [coeFn_boltzmannLp, boltzmannFactor]

lemma premodifierZ_eq_ofReal [IsPotential Φ] [IsAbsolutelySummable Φ]
    (β : ℝ) (Λ : Finset S) (η : S → E) :
    Specification.premodifierZ ν (Φ.boltzmannFactor β) Λ η
      = ENNReal.ofReal ((⇑(Φ.partitionLp ν β Λ)) η) := by
  rw [partitionLp, Specification.action_apply,
    ofReal_integral_eq_lintegral_ofReal (integrable_boltzmannLp ν β Λ η)
      (.of_forall fun x ↦ le_of_lt (by rw [coeFn_boltzmannLp]; exact Real.exp_pos _))]
  exact lintegral_congr fun x ↦ boltzmannFactor_eq_ofReal β Λ x

variable (Φ) in
/-- The pointwise inverse of the partition function, as a bounded observable. -/
def invPartitionLp [IsPotential Φ] [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) :
    lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨fun η ↦ ((⇑(Φ.partitionLp ν β Λ)) η)⁻¹,
    memℓp_infty ⟨(Real.exp (-(|β| * Φ.hamiltonianBound Λ)))⁻¹, by
      rintro _ ⟨η, rfl⟩
      show ‖((⇑(Φ.partitionLp ν β Λ)) η)⁻¹‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (partitionLp_pos ν β Λ η))]
      exact inv_anti₀ (Real.exp_pos _) (le_partitionLp ν β Λ η)⟩⟩

@[simp] lemma coeFn_invPartitionLp [IsPotential Φ] [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) :
    ⇑(Φ.invPartitionLp ν β Λ) = fun η ↦ ((⇑(Φ.partitionLp ν β Λ)) η)⁻¹ := rfl

theorem invPartitionLp_mem_quasilocalFunctions [DecidableEq S] [Nonempty E] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) :
    Φ.invPartitionLp ν β Λ ∈ quasilocalFunctions S E :=
  Subalgebra.inv_mem_lp (Subalgebra.isClosed_topologicalClosure _)
    (partitionLp_mem_quasilocalFunctions ν β Λ) (Real.exp_pos _)
    (le_partitionLp ν β Λ) fun _ ↦ rfl

lemma premodifierNorm_eq_ofReal [IsPotential Φ] [IsAbsolutelySummable Φ]
    (β : ℝ) (Λ : Finset S) (η : S → E) :
    Specification.premodifierNorm ν (Φ.boltzmannFactor β) Λ η
      = ENNReal.ofReal ((⇑(Φ.boltzmannLp β Λ * Φ.invPartitionLp ν β Λ)) η) := by
  rw [Specification.premodifierNorm, boltzmannFactor_eq_ofReal, premodifierZ_eq_ofReal,
    ← ENNReal.ofReal_div_of_pos (partitionLp_pos ν β Λ η), lp.infty_coeFn_mul]
  rfl

/-- **Georgii (2.24)(b) / Example (2.25).** The Gibbsian specification of an absolutely summable
potential is quasilocal. -/
theorem isQuasilocal_gibbsSpecificationOfAbsolutelySummable [DecidableEq S] [Nonempty E]
    [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ] (β : ℝ) :
    (Φ.gibbsSpecificationOfAbsolutelySummable ν β).IsQuasilocal :=
  Specification.isQuasilocal_modification_isssd ν _
    (r := fun Λ ↦ Φ.boltzmannLp β Λ * Φ.invPartitionLp ν β Λ)
    (fun Λ ↦ Subalgebra.mul_mem _ (boltzmannLp_mem_quasilocalFunctions (Φ := Φ) β Λ)
      (invPartitionLp_mem_quasilocalFunctions ν β Λ))
    (fun Λ η ↦ by
      rw [lp.infty_coeFn_mul]
      exact mul_nonneg (le_of_lt (by rw [coeFn_boltzmannLp]; exact Real.exp_pos _))
        (le_of_lt (inv_pos.2 (partitionLp_pos ν β Λ η))))
    (fun Λ η ↦ premodifierNorm_eq_ofReal ν β Λ η)

end Potential
