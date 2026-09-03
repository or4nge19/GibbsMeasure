/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Summable
public import GibbsMeasure.Specification.Quasilocality

/-!
# Quasilocality of the Hamiltonian of an absolutely summable potential

For `Φ` in the space `ℬ` of Georgii (2.11), the Hamiltonian `H_Λ^Φ` and the Boltzmann factor
`h_Λ^Φ` are bounded quasilocal observables. Quasilocality of `H_Λ^Φ` is the hypothesis of Georgii
Proposition (2.24)(b).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure Set
open scoped Topology ENNReal

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E] {Φ : Potential S E} {Λ : Finset S}

variable (Φ) in
/-- The interaction term of `A` in `H_Λ`, as a bounded observable. -/
def termLp [IsAbsolutelySummable Φ] (Λ A : Finset S) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨fun η ↦ Φ.hamiltonianTerms Λ η A, memℓp_infty ⟨(Φ.termNorm Λ A).toReal, by
    rintro _ ⟨η, rfl⟩
    have h := enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η A
    rw [← ENNReal.toReal_le_toReal (by simp) (termNorm_ne_top (Φ := Φ) Λ A)] at h
    simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h⟩⟩

lemma norm_termLp_le [IsAbsolutelySummable Φ] (Λ A : Finset S) :
    ‖Φ.termLp Λ A‖ ≤ (Φ.termNorm Λ A).toReal := by
  refine lp.norm_le_of_forall_le ENNReal.toReal_nonneg fun η ↦ ?_
  have h := enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η A
  rw [← ENNReal.toReal_le_toReal (by simp) (termNorm_ne_top (Φ := Φ) Λ A)] at h
  simpa [termLp, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h

lemma summable_termLp [IsAbsolutelySummable Φ] (Λ : Finset S) : Summable (Φ.termLp Λ) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun A ↦ norm_nonneg _)
    (fun A ↦ norm_termLp_le (Φ := Φ) Λ A) ?_)
  exact ENNReal.summable_toReal (tsum_termNorm_ne_top (Φ := Φ) Λ)

lemma termLp_mem_localFunctionsOn [IsPotential Φ] [IsAbsolutelySummable Φ] (Λ A : Finset S) :
    Φ.termLp Λ A ∈ localFunctionsOn S E A := by
  change Measurable[cylinderEvents (X := fun _ : S ↦ E) (A : Set S)]
    (fun η ↦ Φ.hamiltonianTerms Λ η A)
  by_cases h : Disjoint A Λ
  · simpa only [hamiltonianTerms_of_disjoint h] using measurable_const (a := (0 : ℝ))
  · simpa only [hamiltonianTerms_of_not_disjoint h] using IsPotential.measurable (Φ := Φ) A

lemma termLp_mem_localFunctions [IsPotential Φ] [IsAbsolutelySummable Φ] (Λ A : Finset S) :
    Φ.termLp Λ A ∈ localFunctions S E :=
  mem_localFunctions.2 ⟨A, termLp_mem_localFunctionsOn (Φ := Φ) Λ A⟩

variable (Φ) in
/-- The Hamiltonian in `Λ` as a bounded observable. -/
def hamiltonianLp [IsAbsolutelySummable Φ] (Λ : Finset S) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨Φ.hamiltonian Λ, memℓp_infty ⟨(∑ i ∈ Λ, Φ.normAt i).toReal, by
    rintro _ ⟨η, rfl⟩
    simpa [Real.norm_eq_abs] using abs_hamiltonian_le (Φ := Φ) Λ η⟩⟩

lemma hasSum_termLp [IsAbsolutelySummable Φ] (Λ : Finset S) :
    HasSum (Φ.termLp Λ) (Φ.hamiltonianLp Λ) := by
  obtain ⟨T, hT⟩ := summable_termLp (Φ := Φ) Λ
  have hpt : ∀ η : S → E, (T : (S → E) → ℝ) η = Φ.hamiltonian Λ η := by
    intro η
    have h1 : HasSum (fun A ↦ (Φ.termLp Λ A : (S → E) → ℝ) η) ((T : (S → E) → ℝ) η) := by
      refine (lp.tendsto_apply_of_tendsto hT η).congr fun s ↦ ?_
      simp
    have h2 : HasSum (Φ.hamiltonianTerms Λ η) (Φ.hamiltonian Λ η) := by
      rw [hamiltonian_eq_tsum (Φ := Φ) Λ η]
      exact (summable_hamiltonianTerms (Φ := Φ) Λ η).hasSum
    exact h1.unique h2
  have : T = Φ.hamiltonianLp Λ := by
    refine lp.ext ?_
    funext η
    exact hpt η
  exact this ▸ hT

/-- The Hamiltonian of an absolutely summable potential is quasilocal: the hypothesis of
Georgii (2.24)(b). -/
theorem hamiltonianLp_mem_quasilocalFunctions [IsPotential Φ] [IsAbsolutelySummable Φ]
    (Λ : Finset S) : Φ.hamiltonianLp Λ ∈ quasilocalFunctions S E := by
  refine (Subalgebra.isClosed_topologicalClosure (localFunctions S E)).mem_of_tendsto
    (hasSum_termLp (Φ := Φ) Λ) (.of_forall fun s ↦ ?_)
  exact Subalgebra.sum_mem _ fun A _ ↦ localFunctions_le_quasilocalFunctions
    (termLp_mem_localFunctions (Φ := Φ) Λ A)

/-! ### The Boltzmann factor -/

variable (Φ) in
/-- The Boltzmann factor `h_Λ^Φ = exp(-β H_Λ^Φ)` as a bounded observable. -/
def boltzmannLp [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  Specification.boltzmann (β • Φ.hamiltonianLp Λ)

@[simp] lemma coeFn_boltzmannLp [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) :
    ⇑(Φ.boltzmannLp β Λ) = fun η ↦ Real.exp (-β * Φ.hamiltonian Λ η) := by
  rw [boltzmannLp, Specification.coeFn_boltzmann]
  funext η
  rw [lp.coeFn_smul]
  norm_num [hamiltonianLp]

/-- The Boltzmann factor of an absolutely summable potential is quasilocal. -/
theorem boltzmannLp_mem_quasilocalFunctions [IsPotential Φ] [IsAbsolutelySummable Φ]
    (β : ℝ) (Λ : Finset S) : Φ.boltzmannLp β Λ ∈ quasilocalFunctions S E :=
  Specification.boltzmann_mem_quasilocalFunctions (Subalgebra.smul_mem _
    (hamiltonianLp_mem_quasilocalFunctions (Φ := Φ) Λ) _)

end Potential
