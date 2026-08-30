import Comparator.Defs

/-!
# Definitions: potentials, pre-modifications, and Georgii's Theorem (2.30)

This module extends the shared preamble `Comparator.Defs` with the vocabulary needed to state
Georgii's **Gibbs representation theorem (2.30)**.  It holds the definitions used by
`Comparator/Challenge_Representation.lean` and `Comparator/Solution_Representation.lean`.

**It imports `Comparator.Defs` — which imports `Mathlib` and nothing else — and nothing further**,
and every notion is spelled out from first principles.

## Dictionary

| Georgii | here |
| --- | --- |
| `λ^Λ × δ_{ω_{S∖Λ}}`, the a priori kernel (1.26) | `lambdaInt` (in integrated form), `paste` |
| pre-modification, (1.31) | `IsPreModification` |
| positivity of a `λ`-modification, (1.27) | `IsPositive` |
| quasilocal function, (2.21)(1)/(2.22) | `oscOutside`, `IsQuasilocalFun` |
| potential `Φ = (Φ_A)`, (2.2) | `Potential`, `IsPotential` |
| `H^Φ_{Λ,Δ}`, (2.13) | `partialHamiltonian` |
| `H^Φ_Λ`, (2.3) | `HasHamiltonian`, `hamiltonian` |
| `h^Φ_Λ = exp(-H^Φ_Λ)`, (2.4) | `boltzmann` |
| `Z^Φ_Λ = λ_Λ h^Φ_Λ`, (2.7) | `partitionFunction` |
| `λ`-admissible, (2.7) | `IsAdmissible` |
| `ρ^Φ_Λ = h^Φ_Λ / Z^Φ_Λ`, (2.8) | `gibbsModification` |
| gas potential with vacuum state `a`, (2.28)/(2.29)(1) | `IsGasPotential` |

## Design notes

* Georgii's a priori kernels `λ_Λ(·|ω) = λ^Λ × δ_{ω_{S∖Λ}}` of (1.26) are used here only through
  the integrals `λ_Λ f (ω) = ∫ λ^Λ(dζ) f(ζ ω_{S∖Λ})` they define, so instead of building the
  kernels we define `lambdaInt` directly as the lower Lebesgue integral of `f ∘ paste Λ ω` against
  the finite product measure `λ^Λ = Measure.pi (fun _ : Λ => ν)`.  This needs no infinite product
  measure, and `paste Λ ω ζ` is literally Georgii's `ζ ω_{S∖Λ}`.
* Georgii's summation convention (2.1) — the net of the partial sums over `{A : A ⊆ Δ}`, indexed by
  the directed set of finite volumes `Δ` — is rendered as the limit along `atTop : Filter (Finset S)`
  of `partialHamiltonian Φ Λ Δ`, which is exactly `H^Φ_{Λ,Δ} = ∑_{A ⊆ Δ, A ∩ Λ ≠ ∅} Φ_A` of (2.13).
  `IsPotential` therefore says precisely: each `Φ_A` is `𝓕_A`-measurable, and each of these nets
  converges — Georgii (2.2)(i) and (ii).  **No summability, absolute or otherwise, is assumed.**
* `hamiltonian` is the limit of that net, picked out with `Filter.limUnder`; under `IsPotential` it
  is the honest limit (`HasHamiltonian.hamiltonian_eq`).
* Georgii's densities `ρ_Λ : Ω → [0,∞[` of (1.27) are `ℝ≥0∞`-valued here so that they can be
  integrated without side conditions; `IsPositive` is then the conjunction of Georgii's positivity
  `ρ_Λ > 0` with the finiteness `ρ_Λ < ∞` that is built into his `[0,∞[`.
* `IsAdmissible` asks `0 < Z^Φ_Λ < ∞`.  Georgii (2.7) only writes "finite", but `Z^Φ_Λ ≠ 0` is
  implicit in the quotient (2.8) that defines `ρ^Φ`.

## Non-degeneracy

* `isQuasilocalFun_iff` proves that the net formulation (2.22) of quasilocality is equivalent to the
  `ε`-formulation, so the definition is the intended one.
* `isPreModification_one`, `isPositive_one`, `isQuasilocalFun_one`, `lambdaInt_one`: the constant
  family `ρ_Λ ≡ 1` satisfies **all** the hypotheses of Theorem (2.30) for any single-spin
  probability measure, so they are not contradictory.
* `isPotential_zero`, `isGasPotential_zero`, `isAdmissible_zero`, `gibbsModification_zero`: the zero
  potential is a `λ`-admissible gas potential (for every vacuum state) whose modification is that
  `ρ_Λ ≡ 1`, so the conclusion of Theorem (2.30) is realisable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

namespace Representation

/-! ## Quasilocal functions, Georgii (2.21)(1) -/

section Quasilocal

variable {S E : Type*}

/-- The **oscillation of `f` off the finite volume `Δ`**: how much `f` can still change when the
configuration is modified outside `Δ` only.  This is the supremum appearing in Georgii (2.22). -/
def oscOutside (Δ : Finset S) (f : Config S E → ℝ) : ℝ≥0∞ :=
  ⨆ ζ : Config S E, ⨆ η : Config S E, ⨆ _ : ∀ i ∈ Δ, ζ i = η i, ENNReal.ofReal |f ζ - f η|

theorem le_oscOutside {Δ : Finset S} {f : Config S E → ℝ} {ζ η : Config S E}
    (h : ∀ i ∈ Δ, ζ i = η i) : ENNReal.ofReal |f ζ - f η| ≤ oscOutside Δ f :=
  le_iSup_of_le ζ (le_iSup_of_le η (le_iSup (fun _ : ∀ i ∈ Δ, ζ i = η i =>
    ENNReal.ofReal |f ζ - f η|) h))

/-- **Quasilocal function**, Georgii (2.21)(1) / (2.22):

`lim_{Δ ∈ 𝒮} sup {|f(ζ) - f(η)| : ζ_Δ = η_Δ} = 0`,

the limit being taken along the directed set of finite volumes. -/
def IsQuasilocalFun (f : Config S E → ℝ) : Prop :=
  Tendsto (fun Δ : Finset S => oscOutside Δ f) atTop (nhds 0)

/-- The `ε`-form of Georgii (2.22). -/
theorem isQuasilocalFun_iff (f : Config S E → ℝ) :
    IsQuasilocalFun f ↔ ∀ ε : ℝ, 0 < ε → ∃ Δ : Finset S,
      ∀ ζ η : Config S E, (∀ i ∈ Δ, ζ i = η i) → |f ζ - f η| ≤ ε := by
  constructor
  · intro h ε hε
    have hmem : Set.Iio (ENNReal.ofReal ε) ∈ nhds (0 : ℝ≥0∞) :=
      Iio_mem_nhds (by simpa using hε)
    have hev : ∀ᶠ Δ : Finset S in atTop, oscOutside Δ f < ENNReal.ofReal ε := h hmem
    obtain ⟨Δ, hΔ⟩ := hev.exists
    refine ⟨Δ, fun ζ η hζη => ?_⟩
    have := (le_oscOutside (f := f) hζη).trans_lt hΔ
    rw [ENNReal.ofReal_lt_ofReal_iff hε] at this
    exact this.le
  · intro h
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
    rcases eq_or_ne ε ⊤ with rfl | htop
    · exact .of_forall fun _ => le_top
    · have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
      obtain ⟨Δ₀, hΔ₀⟩ := h ε.toReal hεpos
      filter_upwards [eventually_ge_atTop Δ₀] with Δ hΔ
      refine (iSup₂_le fun ζ η => iSup_le fun hζη => ?_).trans_eq (ENNReal.ofReal_toReal htop)
      exact ENNReal.ofReal_le_ofReal (hΔ₀ ζ η fun i hi => hζη i (hΔ hi))

/-- A function depending on finitely many coordinates only is quasilocal, so the notion is not
vacuous. -/
theorem isQuasilocalFun_of_local {f : Config S E → ℝ} {Δ₀ : Finset S}
    (hf : ∀ ζ η : Config S E, (∀ i ∈ Δ₀, ζ i = η i) → f ζ = f η) : IsQuasilocalFun f := by
  rw [isQuasilocalFun_iff]
  exact fun ε hε => ⟨Δ₀, fun ζ η hζη => by rw [hf ζ η hζη]; simpa using hε.le⟩

end Quasilocal

/-! ## The a priori kernels `λ_Λ`, Georgii (1.26) -/

section Lambda

variable {S E : Type*} [MeasurableSpace E]

open Classical in
/-- `paste Λ η ζ` is Georgii's configuration `ζ η_{S∖Λ}`: it follows `ζ` inside `Λ` and the
boundary condition `η` outside `Λ`. -/
def paste (Λ : Finset S) (η : Config S E) (ζ : Λ → E) : Config S E :=
  fun i => if h : i ∈ Λ then ζ ⟨i, h⟩ else η i

omit [MeasurableSpace E] in
theorem paste_of_mem {Λ : Finset S} {i : S} (hi : i ∈ Λ) (η : Config S E) (ζ : Λ → E) :
    paste Λ η ζ i = ζ ⟨i, hi⟩ := by simp [paste, hi]

omit [MeasurableSpace E] in
theorem paste_of_notMem {Λ : Finset S} {i : S} (hi : i ∉ Λ) (η : Config S E) (ζ : Λ → E) :
    paste Λ η ζ i = η i := by simp [paste, hi]

theorem measurable_paste (Λ : Finset S) (η : Config S E) : Measurable (paste Λ η) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i ∈ Λ
  · have : (fun ζ : Λ → E => paste Λ η ζ i) = fun ζ : Λ → E => ζ ⟨i, hi⟩ :=
      funext fun ζ => paste_of_mem hi η ζ
    rw [this]
    exact measurable_pi_apply (⟨i, hi⟩ : Λ)
  · have : (fun ζ : Λ → E => paste Λ η ζ i) = fun _ : Λ → E => η i :=
      funext fun ζ => paste_of_notMem hi η ζ
    rw [this]
    exact measurable_const

/-- **Georgii (1.26)**, in integrated form: `λ_Λ f (η) = ∫ λ^Λ(dζ) f(ζ η_{S∖Λ})`, the integral of
`f` against the a priori kernel `λ_Λ(·|η) = λ^Λ × δ_{η_{S∖Λ}}`. -/
def lambdaInt (ν : Measure E) (Λ : Finset S) (f : Config S E → ℝ≥0∞) (η : Config S E) : ℝ≥0∞ :=
  ∫⁻ ζ : Λ → E, f (paste Λ η ζ) ∂(Measure.pi fun _ : Λ => ν)

/-! ## Pre-modifications, Georgii (1.31) -/

/-- **Pre-modification**, Georgii (1.31): a family `(ρ_Λ)` of measurable densities with

`ρ_Δ(ζ) ρ_Λ(η) = ρ_Λ(ζ) ρ_Δ(η)` for `Λ ⊆ Δ` and `ζ_{S∖Λ} = η_{S∖Λ}`. -/
structure IsPreModification (ρ : Finset S → Config S E → ℝ≥0∞) : Prop where
  measurable : ∀ Λ : Finset S, Measurable (ρ Λ)
  mul_comm_of_subset : ∀ ⦃Λ Δ : Finset S⦄, Λ ⊆ Δ → ∀ ⦃ζ η : Config S E⦄,
    (∀ i ∉ Λ, ζ i = η i) → ρ Δ ζ * ρ Λ η = ρ Λ ζ * ρ Δ η

/-- **Positivity**, Georgii (1.27): every `ρ_Λ` takes values in `]0,∞[`.  (Georgii's densities are
`[0,∞[`-valued by definition, and *positive* means `ρ_Λ > 0`.) -/
def IsPositive (ρ : Finset S → Config S E → ℝ≥0∞) : Prop :=
  ∀ (Λ : Finset S) (η : Config S E), ρ Λ η ≠ 0 ∧ ρ Λ η ≠ ⊤

end Lambda

/-! ## Potentials, Georgii (2.2) -/

section Potentials

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S]

/-- **Interaction potential**, Georgii (2.2): a family `Φ = (Φ_A)` of real functions on `Ω`
indexed by the finite subsets of `S`. -/
abbrev Potential (S E : Type*) := Finset S → Config S E → ℝ

/-- **Georgii (2.13)**: the partial Hamiltonian `H^Φ_{Λ,Δ} = ∑_{A ⊆ Δ, A ∩ Λ ≠ ∅} Φ_A`. -/
def partialHamiltonian (Φ : Potential S E) (Λ Δ : Finset S) (η : Config S E) : ℝ :=
  ∑ A ∈ Δ.powerset.filter (fun A => (A ∩ Λ).Nonempty), Φ A η

/-- **Georgii (2.2)(ii), (2.3)**: `H` is the energy of `η` in `Λ` for `Φ`, i.e. the sum
`∑_{A ∩ Λ ≠ ∅} Φ_A(η)` in the sense of Georgii's convention (2.1): the net of the partial sums
`H^Φ_{Λ,Δ}` over the directed set of finite volumes `Δ` converges to `H`. -/
def HasHamiltonian (Φ : Potential S E) (Λ : Finset S) (η : Config S E) (H : ℝ) : Prop :=
  Tendsto (fun Δ : Finset S => partialHamiltonian Φ Λ Δ η) atTop (nhds H)

/-- **Georgii (2.2)**: `Φ` is an interaction potential, i.e. (i) each `Φ_A` is `𝓕_A`-measurable and
(ii) all the energies `H^Φ_Λ(η)` of (2.3) exist. -/
structure IsPotential (Φ : Potential S E) : Prop where
  measurable : ∀ A : Finset S, Measurable[inside A] (Φ A)
  exists_hamiltonian : ∀ (Λ : Finset S) (η : Config S E), ∃ H : ℝ, HasHamiltonian Φ Λ η H

/-- **Georgii (2.3)**: the Hamiltonian `H^Φ_Λ`.  Under `IsPotential` this is the honest limit of
the partial Hamiltonians (`HasHamiltonian.hamiltonian_eq`). -/
def hamiltonian (Φ : Potential S E) (Λ : Finset S) (η : Config S E) : ℝ :=
  limUnder atTop fun Δ : Finset S => partialHamiltonian Φ Λ Δ η

omit [MeasurableSpace E] in
theorem HasHamiltonian.hamiltonian_eq {Φ : Potential S E} {Λ : Finset S} {η : Config S E} {H : ℝ}
    (h : HasHamiltonian Φ Λ η H) : hamiltonian Φ Λ η = H :=
  h.limUnder_eq

/-- **Georgii (2.4)**: the Boltzmann factor `h^Φ_Λ = exp(-H^Φ_Λ)`. -/
def boltzmann (Φ : Potential S E) (Λ : Finset S) (η : Config S E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-hamiltonian Φ Λ η))

/-- **Georgii (2.7)**: the partition function `Z^Φ_Λ(η) = λ_Λ h^Φ_Λ(η)`. -/
def partitionFunction (ν : Measure E) (Φ : Potential S E) (Λ : Finset S) (η : Config S E) : ℝ≥0∞ :=
  lambdaInt ν Λ (boltzmann Φ Λ) η

/-- **Georgii (2.7)**: `Φ` is `λ`-admissible, i.e. all its partition functions are finite (and
nonzero, as is implicit in the quotient (2.8)). -/
def IsAdmissible (ν : Measure E) (Φ : Potential S E) : Prop :=
  ∀ (Λ : Finset S) (η : Config S E),
    partitionFunction ν Φ Λ η ≠ 0 ∧ partitionFunction ν Φ Λ η ≠ ⊤

/-- **Georgii (2.8)**: the `λ`-modification `ρ^Φ_Λ = h^Φ_Λ / Z^Φ_Λ` of a `λ`-admissible
potential. -/
def gibbsModification (ν : Measure E) (Φ : Potential S E) (Λ : Finset S) (η : Config S E) : ℝ≥0∞ :=
  boltzmann Φ Λ η / partitionFunction ν Φ Λ η

/-- **Gas potential with vacuum state `a`**, Georgii (2.28) and (2.29)(1): `Φ` is normalized by the
Dirac measure `δ_a`, which by (2.29)(1) means exactly that `Φ_A(ω) = 0` whenever `ω_i = a` for
some `i ∈ A`. -/
def IsGasPotential (a : E) (Φ : Potential S E) : Prop :=
  ∀ (A : Finset S) (η : Config S E), (∃ i ∈ A, η i = a) → Φ A η = 0

end Potentials

/-! ## Non-degeneracy -/

section Examples

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S]

omit [DecidableEq S] in
/-- The constant family `ρ_Λ ≡ 1` is a pre-modification. -/
theorem isPreModification_one :
    IsPreModification fun (_ : Finset S) (_ : Config S E) => (1 : ℝ≥0∞) where
  measurable _ := measurable_const
  mul_comm_of_subset _ _ _ _ _ _ := rfl

omit [MeasurableSpace E] [DecidableEq S] in
/-- The constant family `ρ_Λ ≡ 1` is positive. -/
theorem isPositive_one : IsPositive fun (_ : Finset S) (_ : Config S E) => (1 : ℝ≥0∞) :=
  fun _ _ => ⟨one_ne_zero, ENNReal.one_ne_top⟩

omit [MeasurableSpace E] [DecidableEq S] in
/-- The constant family `ρ_Λ ≡ 1` is quasilocal. -/
theorem isQuasilocalFun_one (Λ : Finset S) :
    IsQuasilocalFun fun η : Config S E =>
      ((fun (_ : Finset S) (_ : Config S E) => (1 : ℝ≥0∞)) Λ η).toReal :=
  isQuasilocalFun_of_local (Δ₀ := (∅ : Finset S)) fun _ _ _ => rfl

omit [DecidableEq S] in
/-- The constant family `ρ_Λ ≡ 1` is normalized: `λ_Λ ρ_Λ = 1`. -/
theorem lambdaInt_one (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) (η : Config S E) :
    lambdaInt ν Λ (fun _ => (1 : ℝ≥0∞)) η = 1 := by
  simp [lambdaInt]

omit [MeasurableSpace E] in
/-- The zero potential has vanishing Hamiltonians. -/
theorem hamiltonian_zero (Λ : Finset S) (η : Config S E) :
    hamiltonian (fun _ _ => (0 : ℝ)) Λ η = 0 :=
  HasHamiltonian.hamiltonian_eq (Φ := fun _ _ => (0 : ℝ)) (by simp [HasHamiltonian,
    partialHamiltonian])

/-- The zero potential is a potential. -/
theorem isPotential_zero : IsPotential fun (_ : Finset S) (_ : Config S E) => (0 : ℝ) where
  measurable _ := measurable_const
  exists_hamiltonian _ _ := ⟨0, by simp [HasHamiltonian, partialHamiltonian]⟩

omit [MeasurableSpace E] [DecidableEq S] in
/-- The zero potential is a gas potential, whatever the vacuum state. -/
theorem isGasPotential_zero (a : E) :
    IsGasPotential a fun (_ : Finset S) (_ : Config S E) => (0 : ℝ) := fun _ _ _ => rfl

omit [MeasurableSpace E] in
/-- The Boltzmann factor of the zero potential is `1`. -/
theorem boltzmann_zero (Λ : Finset S) (η : Config S E) :
    boltzmann (fun _ _ => (0 : ℝ)) Λ η = (1 : ℝ≥0∞) := by
  simp [boltzmann, hamiltonian_zero]

/-- The partition functions of the zero potential are `1`. -/
theorem partitionFunction_zero (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S)
    (η : Config S E) : partitionFunction ν (fun _ _ => (0 : ℝ)) Λ η = 1 := by
  have h : boltzmann (fun (_ : Finset S) (_ : Config S E) => (0 : ℝ)) Λ
      = fun _ : Config S E => (1 : ℝ≥0∞) := funext fun ξ => boltzmann_zero Λ ξ
  rw [partitionFunction, h, lambdaInt_one]

/-- The zero potential is `λ`-admissible for any single-spin probability measure. -/
theorem isAdmissible_zero (ν : Measure E) [IsProbabilityMeasure ν] :
    IsAdmissible ν fun (_ : Finset S) (_ : Config S E) => (0 : ℝ) := fun Λ η => by
  rw [partitionFunction_zero]
  exact ⟨one_ne_zero, ENNReal.one_ne_top⟩

/-- The `λ`-modification of the zero potential is the constant family `ρ_Λ ≡ 1`: the conclusion of
Theorem (2.30) is realisable. -/
theorem gibbsModification_zero (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S)
    (η : Config S E) :
    gibbsModification ν (fun _ _ => (0 : ℝ)) Λ η = 1 := by
  rw [gibbsModification, boltzmann_zero, partitionFunction_zero, one_div_one]

end Examples

end Representation

end GibbsChallenge

end
