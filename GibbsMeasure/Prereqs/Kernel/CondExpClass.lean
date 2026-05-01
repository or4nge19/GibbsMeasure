module

public import Mathlib.Probability.Kernel.Defs
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

public section

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {μ : Measure[𝓧] X}

@[mk_iff]
class IsCondExp (π : Kernel[𝓑, 𝓧] X X) (μ : Measure[𝓧] X) : Prop where
  condExp_ae_eq_kernel_apply ⦃A : Set X⦄ : MeasurableSet[𝓧] A →
    μ[A.indicator 1| 𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal

end ProbabilityTheory.Kernel
