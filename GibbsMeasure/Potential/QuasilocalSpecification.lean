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

Georgii Example (2.25): the instance of Proposition (2.24)(b)
(`Specification.isQuasilocal_modification_premodifierNorm`) at the bounded quasilocal Hamiltonians
of an absolutely summable potential — the case singled out in (2.25)(ii). Its stronger conclusion
`ρ_Λ^Φ ∈ 𝓛̄` is `Potential.exists_mem_quasilocalFunctions_toReal_premodifierNorm_boltzmannFactor`
in `Potential/FiniteReference.lean`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped Topology ENNReal NNReal

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E] {Φ : Potential S E}
variable (ν : Measure E) [IsProbabilityMeasure ν]

lemma boltzmannFactor_eq_ofReal_boltzmann [IsAbsolutelySummable Φ] (β : ℝ) :
    Φ.boltzmannFactor β
      = fun Λ η ↦ ENNReal.ofReal ((⇑(Specification.boltzmann (β • Φ.hamiltonianLp Λ))) η) := by
  funext Λ η
  rw [boltzmannFactor, Specification.coeFn_boltzmann, lp.coeFn_smul]
  norm_num [hamiltonianLp]

/-- **Georgii Example (2.25).** The Gibbsian specification of an absolutely summable potential is
quasilocal: Proposition (2.24)(b) applied to the bounded quasilocal Hamiltonians of `Φ ∈ ℬ`, the
case singled out in (2.25)(ii); the stronger conclusion `ρ_Λ^Φ ∈ 𝓛̄` is
`exists_mem_quasilocalFunctions_toReal_premodifierNorm_boltzmannFactor`
(`Potential/FiniteReference.lean`). Georgii's a priori measure is finite in this case ((2.11): `Φ
    ∈ ℬ` is `λ`-admissible
iff `λ` is finite); `ν` is its normalization. -/
theorem isQuasilocal_gibbsSpecificationOfAbsolutelySummable
    [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ] (β : ℝ) :
    (Φ.gibbsSpecificationOfAbsolutelySummable ν β).IsQuasilocal := by
  classical
  rw [gibbsSpecificationOfAbsolutelySummable]
  simp only [boltzmannFactor_eq_ofReal_boltzmann (Φ := Φ) β]
  exact Specification.isQuasilocal_modification_premodifierNorm ν
    (H := fun Λ ↦ β • Φ.hamiltonianLp Λ)
    (fun Λ ↦ Subalgebra.smul_mem _ (hamiltonianLp_mem_quasilocalFunctions (Φ := Φ) Λ) β) _

end Potential
