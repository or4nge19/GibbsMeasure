import Comparator.Defs

/-!
# Absolutely summable potentials and their Gibbsian specifications

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Definitions (2.2), (2.3) and (2.9).

Georgii's a priori measure `λ` is finite but not normalized, so the finite-volume a priori measure
`λ_Λ^ω` has mass `λ(E)^{|Λ|}`; that factor occurs in both the numerator and the denominator of the
Gibbs distribution and cancels (`gibbsKernel_smul`, Georgii's Remark (1.28)(3)).

## Main definitions

* `potentialNormAt`: the interaction norm `‖Φ‖ᵢ = ∑_{A ∋ i} sup_ω |Φ_A(ω)|`
* `IsAbsolutelySummablePotential`: Georgii's Definition (2.2)(i) with (2.11)
* `hamiltonian`, `boltzmannFactor`, `partitionFunction`: Georgii (2.3), (2.4), (2.7)
* `freeMeasure`: the a priori measure `λ_Λ^ω` in the volume `Λ`
* `gibbsKernel`: the Gibbsian specification `γ^Φ` of Georgii's Definition (2.9)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

/-! ## Absolutely summable potentials -/

open Classical in
/-- Extend an inner configuration `ζ : Λ → E` to a configuration on all of `S`, using the boundary
condition `ω` outside `Λ`. -/
def extend (Λ : Finset S) (ζ : Λ → E) (ω : Config S E) : Config S E :=
  fun i => if h : i ∈ Λ then ζ ⟨i, h⟩ else ω i

theorem measurable_extend (Λ : Finset S) (ω : Config S E) :
    Measurable fun ζ : Λ → E => extend Λ ζ ω := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i ∈ Λ
  · have h : (fun ζ : Λ → E => extend Λ ζ ω i) = fun ζ => ζ ⟨i, hi⟩ := by
      funext ζ; simp [extend, hi]
    rw [h]
    exact measurable_pi_apply _
  · have h : (fun ζ : Λ → E => extend Λ ζ ω i) = fun _ => ω i := by
      funext ζ; simp [extend, hi]
    rw [h]
    exact measurable_const

/-- **Georgii (2.12)**: the interaction norm `‖Φ‖ᵢ = ∑_{A ∋ i} sup_ω |Φ_A(ω)|` at the site `i`,
computed in `[0, ∞]` so that no finiteness has to be assumed to write it down. -/
def potentialNormAt (Φ : Finset S → Config S E → ℝ) (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S,
    {A : Finset S | i ∈ A}.indicator (fun A => ⨆ ω : Config S E, ENNReal.ofReal |Φ A ω|) A

/-- **Georgii (2.2)(i) with (2.11)**: an absolutely summable potential, i.e. a family `Φ` indexed
by the finite subsets of `S` with each `Φ A` measurable in the coordinates inside `A` and with
finite interaction norm at every site. -/
structure IsAbsolutelySummablePotential (Φ : Finset S → Config S E → ℝ) : Prop where
  /-- Georgii (2.2)(i): `Φ_A` is `𝓕_A`-measurable. -/
  measurable_inside : ∀ A : Finset S, Measurable[inside A] (Φ A)
  /-- Georgii (2.11): `∑_{A ∋ i} sup_ω |Φ_A(ω)| < ∞` for every site `i`. -/
  normAt_ne_top : ∀ i : S, potentialNormAt Φ i ≠ ⊤

/-- **Georgii (2.3)**: the Hamiltonian `H_Λ = ∑_{A : A ∩ Λ ≠ ∅} Φ_A` in the volume `Λ`. -/
def hamiltonian (Φ : Finset S → Config S E → ℝ) (Λ : Finset S) (ω : Config S E) : ℝ :=
  ∑' A : Finset S, {A : Finset S | ∃ i ∈ A, i ∈ Λ}.indicator (fun A => Φ A ω) A

/-- **Georgii (2.4)**: the Boltzmann factor `e^{-β H_Λ}`. -/
def boltzmannFactor (Φ : Finset S → Config S E → ℝ) (β : ℝ) (Λ : Finset S)
    (ω : Config S E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * hamiltonian Φ Λ ω))

/-! ## The Gibbsian specification of an absolutely summable potential -/

/-- **Georgii (1.26)**: the a priori measure `λ_Λ^ω`, resampling the coordinates inside `Λ`
independently from `λ` and keeping the boundary condition `ω` outside.  No normalization of `λ` is
assumed, so its total mass is `λ(E)^{|Λ|}` rather than `1`. -/
def freeMeasure (ν : Measure E) (Λ : Finset S) (ω : Config S E) : Measure (Config S E) :=
  Measure.map (fun ζ : Λ → E => extend Λ ζ ω) (Measure.pi fun _ : Λ => ν)

/-- **Georgii (2.7)**: the partition function `Z_Λ(ω) = ∫ e^{-β H_Λ} dλ_Λ^ω`, computed against the
un-normalized a priori measure itself. -/
def partitionFunction (Φ : Finset S → Config S E → ℝ) (ν : Measure E) (β : ℝ) (Λ : Finset S)
    (ω : Config S E) : ℝ≥0∞ :=
  ∫⁻ σ, boltzmannFactor Φ β Λ σ ∂(freeMeasure ν Λ ω)

/-- **Georgii (2.9)**: the Gibbsian specification `γ_Λ(A | ω) = Z_Λ(ω)⁻¹ ∫ 1_A e^{-β H_Λ} dλ_Λ^ω`
of `Φ`, both integrals being taken against the same un-normalized a priori measure. -/
def gibbsKernel (Φ : Finset S → Config S E → ℝ) (ν : Measure E) (β : ℝ) (Λ : Finset S)
    (ω : Config S E) : Measure (Config S E) :=
  (partitionFunction Φ ν β Λ ω)⁻¹ • (freeMeasure ν Λ ω).withDensity (boltzmannFactor Φ β Λ)

/-- The a-priori measure is a probability measure when `λ` is. -/
instance isProbabilityMeasure_freeMeasure (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S)
    (ω : Config S E) : IsProbabilityMeasure (freeMeasure ν Λ ω) := by
  rw [freeMeasure]
  exact Measure.isProbabilityMeasure_map (measurable_extend Λ ω).aemeasurable

/-! ## The `λ(E)^{|Λ|}` factors and their cancellation -/

/-- The mass of `λ_Λ^ω` is `λ(E)^{|Λ|}`: for a general `λ` the kernel of Georgii's Notation (1.26)
is *not* a probability kernel. -/
theorem freeMeasure_univ (ν : Measure E) [SigmaFinite ν] (Λ : Finset S) (ω : Config S E) :
    freeMeasure ν Λ ω Set.univ = ν Set.univ ^ Λ.card := by
  rw [freeMeasure, Measure.map_apply (measurable_extend Λ ω) MeasurableSet.univ,
    Set.preimage_univ, Measure.pi_univ, Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- For a finite a priori measure the finite-volume a priori measure is finite. -/
instance isFiniteMeasure_freeMeasure (ν : Measure E) [IsFiniteMeasure ν] (Λ : Finset S)
    (ω : Config S E) : IsFiniteMeasure (freeMeasure ν Λ ω) :=
  ⟨by rw [freeMeasure_univ]; exact ENNReal.pow_lt_top (measure_lt_top ν _)⟩

/-- **Georgii (2.9)** as a ratio: `γ_Λ(A|ω)` is a quotient of two integrals of `e^{-β H_Λ}`
against one and the same measure `λ_Λ^ω`. -/
theorem gibbsKernel_apply (Φ : Finset S → Config S E → ℝ) (ν : Measure E) (β : ℝ) (Λ : Finset S)
    (ω : Config S E) {A : Set (Config S E)} (hA : MeasurableSet A) :
    gibbsKernel Φ ν β Λ ω A
      = (∫⁻ σ in A, boltzmannFactor Φ β Λ σ ∂(freeMeasure ν Λ ω))
        / ∫⁻ σ, boltzmannFactor Φ β Λ σ ∂(freeMeasure ν Λ ω) := by
  rw [gibbsKernel, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA, partitionFunction,
    ENNReal.div_eq_inv_mul]

/-- Rescaling the a priori measure rescales `λ_Λ^ω` by `c^{|Λ|}`. -/
theorem freeMeasure_smul (c : ℝ≥0∞) (hc : c ≠ ⊤) (ν : Measure E) [IsFiniteMeasure ν]
    (Λ : Finset S) (ω : Config S E) :
    freeMeasure (c • ν) Λ ω = c ^ Λ.card • freeMeasure ν Λ ω := by
  have : IsFiniteMeasure (c • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) (measure_lt_top ν _)⟩
  have hpi : (Measure.pi fun _ : Λ => c • ν) = c ^ Λ.card • Measure.pi fun _ : Λ => ν := by
    refine Measure.pi_eq (μ := fun _ : Λ => c • ν) fun s _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  simp only [freeMeasure]
  rw [hpi, Measure.map_smul]

/-- **Georgii's Remark (1.28)(3)**: the Gibbs distribution is homogeneous of degree zero in the a
priori measure, which is why (2.9) and (4.23) need `λ` finite but not normalized. -/
theorem gibbsKernel_smul (Φ : Finset S → Config S E → ℝ) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc : c ≠ ⊤)
    (ν : Measure E) [IsFiniteMeasure ν] (β : ℝ) (Λ : Finset S) (ω : Config S E) :
    gibbsKernel Φ (c • ν) β Λ ω = gibbsKernel Φ ν β Λ ω := by
  refine Measure.ext fun A hA => ?_
  rw [gibbsKernel_apply _ _ _ _ _ hA, gibbsKernel_apply _ _ _ _ _ hA,
    freeMeasure_smul c hc ν Λ ω]
  simp only [Measure.restrict_smul, lintegral_smul_measure]
  exact ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ hc0) (ENNReal.pow_ne_top hc)

/-- Normalization is not a hypothesis: replacing a finite non-zero `λ` by the probability measure
`λ(E)⁻¹ λ` leaves the Gibbsian specification unchanged. -/
theorem gibbsKernel_probNormalize (Φ : Finset S → Config S E → ℝ) (ν : Measure E)
    [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) (Λ : Finset S) (ω : Config S E) :
    gibbsKernel Φ ((ν Set.univ)⁻¹ • ν) β Λ ω = gibbsKernel Φ ν β Λ ω :=
  gibbsKernel_smul Φ _ (ENNReal.inv_ne_zero.2 (measure_ne_top ν _))
    (ENNReal.inv_ne_top.2 (NeZero.ne (ν Set.univ))) ν β Λ ω

/-! ## Non-degeneracy: the zero potential -/

/-- The zero potential is absolutely summable. -/
theorem isAbsolutelySummablePotential_zero :
    IsAbsolutelySummablePotential (fun (_ : Finset S) (_ : Config S E) => (0 : ℝ)) where
  measurable_inside _ := measurable_const
  normAt_ne_top i := by
    have h : potentialNormAt (fun (_ : Finset S) (_ : Config S E) => (0 : ℝ)) i = 0 := by
      rw [potentialNormAt]
      refine ENNReal.tsum_eq_zero.2 fun A => ?_
      by_cases hA : i ∈ A <;> simp [hA]
    simp [h]

omit [MeasurableSpace E] in
/-- Its Hamiltonian vanishes. -/
theorem hamiltonian_zero (Λ : Finset S) (ω : Config S E) :
    hamiltonian (fun (_ : Finset S) (_ : Config S E) => (0 : ℝ)) Λ ω = 0 := by
  have h : (fun A : Finset S =>
      {A : Finset S | ∃ i ∈ A, i ∈ Λ}.indicator (fun _ => (0 : ℝ)) A) = fun _ => 0 := by
    funext A
    by_cases hA : A ∈ {A : Finset S | ∃ i ∈ A, i ∈ Λ} <;> simp [hA]
  rw [hamiltonian, h, tsum_zero]

omit [MeasurableSpace E] in
/-- The Boltzmann factor of the zero potential is `1`. -/
theorem boltzmannFactor_zero (β : ℝ) (Λ : Finset S) :
    boltzmannFactor (fun (_ : Finset S) (_ : Config S E) => (0 : ℝ)) β Λ = 1 := by
  funext σ
  simp [boltzmannFactor, hamiltonian_zero]

/-- For the zero potential the partition function is exactly the mass `λ(E)^{|Λ|}` of `λ_Λ^ω`. -/
theorem partitionFunction_zero (ν : Measure E) [SigmaFinite ν] (β : ℝ) (Λ : Finset S)
    (ω : Config S E) :
    partitionFunction (fun (_ : Finset S) (_ : Config S E) => (0 : ℝ)) ν β Λ ω
      = ν Set.univ ^ Λ.card := by
  rw [partitionFunction, boltzmannFactor_zero]
  simp only [Pi.one_apply]
  rw [lintegral_one, freeMeasure_univ]

/-- The Gibbsian specification of the zero potential is the normalized a priori measure: `Z_Λ(ω)`
divides out exactly the factor `λ(E)^{|Λ|}` carried by `λ_Λ^ω`. -/
theorem gibbsKernel_zero (ν : Measure E) [SigmaFinite ν] (β : ℝ) (Λ : Finset S)
    (ω : Config S E) :
    gibbsKernel (fun (_ : Finset S) (_ : Config S E) => (0 : ℝ)) ν β Λ ω
      = (ν Set.univ ^ Λ.card)⁻¹ • freeMeasure ν Λ ω := by
  rw [gibbsKernel, partitionFunction_zero, boltzmannFactor_zero, withDensity_one]

/-- For a normalized a priori measure the zero potential gives the independent specification. -/
theorem gibbsKernel_zero_of_isProbabilityMeasure (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (Λ : Finset S) (ω : Config S E) :
    gibbsKernel (fun (_ : Finset S) (_ : Config S E) => (0 : ℝ)) ν β Λ ω = freeMeasure ν Λ ω := by
  rw [gibbsKernel_zero]
  simp

end GibbsChallenge

end
