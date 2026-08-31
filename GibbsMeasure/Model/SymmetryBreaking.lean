/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.SharpPhaseTransition
public import GibbsMeasure.Specification.BrokenSymmetry

/-!
# The two-dimensional Ising phase transition as a broken symmetry

Georgii's Definition (5.21) calls a symmetry `τ` of a specification *broken* when some Gibbs
measure is not `τ`-invariant, and observes that a broken symmetry forces `|𝒢(γ)| > 1`. Chapter 6's
phase transition is of exactly this kind: at `β ≥ log 3` the plus and minus phases of the
two-dimensional Ising ferromagnet in zero field are exchanged by the spin flip and are distinct,
so the spin flip — a symmetry of the specification by (5.6)(c)/(5.9)(b), the Ising potential in
zero field being spin-flip invariant — is broken.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure Set

namespace MeasureTheory.GibbsMeasure.PeierlsSharp

/-- **The spin flip is a broken symmetry of the two-dimensional Ising ferromagnet at low
temperature** (Georgii, Definition (5.21) for the model of Theorem (6.9)). -/
theorem isBrokenSymmetry_spinFlip {b : ℝ} (hb : Real.log 9 ≤ 2 * b) :
    (isingSpecification (latticeGraph 2) 1 0 b).IsBrokenSymmetry Peierls.spinFlip := by
  obtain ⟨mp, mm, hne, hp, -, -, -, hflip, -, -, -⟩ := exists_two_shiftInvariant_gibbs_sharp b hb
  refine ⟨mp, hp, fun h ↦ hne (ProbabilityMeasure.toMeasure_injective ?_)⟩
  rw [hflip, ← ProbabilityMeasure.toMeasure_map (hf := Peierls.spinFlip.measurable_toFun.aemeasurable), h]

/-- **Georgii (6.9) as a symmetry breaking.** At `β ≥ log 3` the spin flip is a symmetry of the
two-dimensional Ising specification in zero field, and it is broken. -/
theorem ising_symmetry_breaking {b : ℝ} (hb : Real.log 9 ≤ 2 * b) :
    Specification.IsInvariant Peierls.spinFlip (isingSpecification (latticeGraph 2) 1 0 b) ∧
      (isingSpecification (latticeGraph 2) 1 0 b).IsBrokenSymmetry Peierls.spinFlip :=
  ⟨Peierls.isInvariant_spinFlip b, isBrokenSymmetry_spinFlip hb⟩

/-- Non-uniqueness re-derived from the broken symmetry, through Georgii's remark after (5.21)
rather than through the two explicit phases. -/
theorem nontrivial_GP_of_symmetry_breaking {b : ℝ} (hb : Real.log 9 ≤ 2 * b) :
    (GP (S := Fin 2 → ℤ) (E := Bool)
      (isingSpecification (latticeGraph 2) 1 0 b)).Nontrivial :=
  Specification.nontrivial_GP_of_isBrokenSymmetry (Peierls.isInvariant_spinFlip b)
    (isBrokenSymmetry_spinFlip hb)

end MeasureTheory.GibbsMeasure.PeierlsSharp
