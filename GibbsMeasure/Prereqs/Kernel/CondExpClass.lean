module

public import Mathlib.Probability.Kernel.Defs
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Kernels computing the conditional probabilities of a measure

`ProbabilityTheory.Kernel.IsCondExp π μ`: the kernel `π` from a sub-σ-algebra `𝓑` to `𝓧` is a
version of the conditional probabilities of `μ` given `𝓑`.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {μ : Measure[𝓧] X}

/-- A kernel `π` from `𝓑` to `𝓧` is a **conditional expectation kernel** for `μ` if, for every
`𝓧`-measurable set `A`, the function `x ↦ (π x A).toReal` is a version of `μ[1_A | 𝓑]`; that is,
`π` is a regular version of the conditional probabilities `μ(A | 𝓑)`, as in Georgii,
Remark (1.20). -/
@[mk_iff]
class IsCondExp (π : Kernel[𝓑, 𝓧] X X) (μ : Measure[𝓧] X) : Prop where
  condExp_ae_eq_kernel_apply ⦃A : Set X⦄ : MeasurableSet[𝓧] A →
    μ[A.indicator 1| 𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal

end ProbabilityTheory.Kernel
