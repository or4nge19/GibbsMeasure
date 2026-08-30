import Mathlib

/-!
# Comparator challenge: the two-dimensional Ising phase transition (Georgii, Theorem (6.9))

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).

**It imports `Mathlib` and nothing else.** In particular it does *not* import the `GibbsMeasure`
library whose theorem is being certified: every notion appearing in the final statements — the
lattice `ℤ²`, the spin variables, the nearest-neighbour bonds, the Hamiltonian, the finite-volume
Gibbs distribution, the DLR equation, the lattice shifts — is spelled out here from first
principles using only `Mathlib`. A skeptical reader can check each definition by eye against the
physics without having to trust anything else.

## Dictionary

* `Site := Fin 2 → ℤ` is the lattice `ℤ²`, and `Config := Site → Bool` is the configuration space
  `{-1, +1} ^ (ℤ²)`, carrying the product σ-algebra (`Bool` is discrete).
* `spin b = if b then 1 else -1` turns a `Bool` into a `±1` spin.
* `e k` is the `k`-th unit vector of `ℤ²`. The nearest-neighbour bonds are the pairs
  `{i, i + e k}` for `i : Site` and `k : Fin 2`, encoded as ordered pairs `(i, k)` so that every
  bond has exactly one encoding.
* `bonds Λ` is the (finite) set of bonds *meeting* the finite volume `Λ`, i.e. those `(i, k)` with
  `i ∈ Λ ∨ i + e k ∈ Λ`; `mem_bonds` is the membership characterisation.
* `hamiltonian Λ σ = -∑ bonds meeting Λ, spin (σ i) * spin (σ (i + e k))` is the ferromagnetic
  Ising energy with coupling constant `1` and zero external field.
* `gibbsMeasure β Λ ω` is the finite-volume Gibbs distribution in `Λ` at inverse temperature `β`
  with boundary condition `ω`, written out as an explicit normalised finite sum of Dirac measures.
* `IsGibbs β μ` is the Dobrushin–Lanford–Ruelle condition: `μ` is a probability measure and, for
  every finite volume `Λ` and every measurable set `A`, `μ A = ∫⁻ ω, gibbsMeasure β Λ ω A ∂μ`.
* `shift j` translates a configuration by the lattice vector `j`.

## Main statements

* `ising_phase_transition`: **Georgii, Theorem (6.9), the "in particular" half.** At all
  sufficiently low temperatures the two-dimensional Ising ferromagnet has two distinct
  shift-invariant Gibbs measures, exchanged by the global spin flip, with strictly negative
  respectively strictly positive spontaneous magnetisation.
* `ising_uniqueness_at_high_temperature`: the Dobrushin half, stated only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

noncomputable section

namespace IsingChallenge

/-! ### The lattice and the configuration space -/

/-- The sites of the two-dimensional lattice `ℤ²`. -/
abbrev Site : Type := Fin 2 → ℤ

/-- A spin configuration: a `Bool`, i.e. a sign, attached to every site of `ℤ²`. Being a product
of copies of the discrete space `Bool`, this carries the product σ-algebra. -/
abbrev Config : Type := Site → Bool

/-- The `±1`-valued spin attached to a `Bool`: `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- The `k`-th unit vector of the lattice `ℤ²`. -/
def e (k : Fin 2) : Site := fun l ↦ if l = k then 1 else 0

/-! ### The nearest-neighbour bonds meeting a finite volume

A nearest-neighbour bond of `ℤ²` is an unordered pair `{i, i + e k}` with `k : Fin 2`; we encode
it by the ordered pair `(i, k)`, so that each bond has exactly one encoding. -/

/-- An auxiliary finite set of sites containing every left endpoint of a bond meeting `Λ`: the
volume `Λ` itself together with all of its translates by `-e k`. -/
def bondBase (Λ : Finset Site) : Finset Site :=
  Λ ∪ (Finset.univ : Finset (Fin 2)).biUnion fun k ↦ Λ.image fun i ↦ i - e k

/-- The set of nearest-neighbour bonds `{i, i + e k}` of `ℤ²` that *meet* the finite volume `Λ`,
encoded as ordered pairs `(i, k)`. It is finite because the left endpoint `i` of such a bond lies
either in `Λ` or in one of the two translates `Λ - e k`. -/
def bonds (Λ : Finset Site) : Finset (Site × Fin 2) :=
  (bondBase Λ ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p ↦ p.1 ∈ Λ ∨ p.1 + e p.2 ∈ Λ

/-- The promised characterisation: `(i, k)` belongs to `bonds Λ` exactly when the nearest-neighbour
bond `{i, i + e k}` meets `Λ`. -/
theorem mem_bonds (Λ : Finset Site) (i : Site) (k : Fin 2) :
    (i, k) ∈ bonds Λ ↔ (i ∈ Λ ∨ i + e k ∈ Λ) := by
  refine ⟨fun h ↦ (Finset.mem_filter.mp h).2, fun h ↦ Finset.mem_filter.mpr ⟨?_, h⟩⟩
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
  rcases h with h | h
  · exact Finset.mem_union_left _ h
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, ?_⟩)
    exact Finset.mem_image.mpr ⟨i + e k, h, by simp⟩

/-! ### The Ising Hamiltonian -/

/-- The energy of the configuration `σ` in the finite volume `Λ`: minus the sum of the products of
neighbouring spins, over all nearest-neighbour bonds meeting `Λ`. This is the ferromagnetic Ising
Hamiltonian with coupling constant `1` and zero external field. -/
def hamiltonian (Λ : Finset Site) (σ : Config) : ℝ :=
  -∑ p ∈ bonds Λ, spin (σ p.1) * spin (σ (p.1 + e p.2))

/-! ### The finite-volume Gibbs distribution -/

/-- `glue Λ ζ ω` follows `ζ` inside `Λ` and the boundary condition `ω` outside `Λ`. -/
def glue (Λ : Finset Site) (ζ ω : Config) : Config := fun i ↦ if i ∈ Λ then ζ i else ω i

/-- Extend an inner configuration `ζ : Λ → Bool` to all of `ℤ²`, using `ω` outside `Λ`. -/
def extend (Λ : Finset Site) (ζ : Λ → Bool) (ω : Config) : Config :=
  fun i ↦ if h : i ∈ Λ then ζ ⟨i, h⟩ else ω i

/-- The unnormalised Boltzmann weight `exp (-β * H)` of the inner configuration `ζ` in the volume
`Λ` with boundary condition `ω`. -/
def weight (β : ℝ) (Λ : Finset Site) (ω : Config) (ζ : Λ → Bool) : ℝ :=
  Real.exp (-β * hamiltonian Λ (glue Λ (extend Λ ζ ω) ω))

/-- The partition function in the volume `Λ` with boundary condition `ω`: the sum of the Boltzmann
weights over the `2 ^ #Λ` inner configurations. -/
def partitionFunction (β : ℝ) (Λ : Finset Site) (ω : Config) : ℝ :=
  ∑ ζ : Λ → Bool, weight β Λ ω ζ

/-- The finite-volume Gibbs distribution in `Λ` at inverse temperature `β` with boundary condition
`ω`, written out explicitly as a normalised finite sum of Dirac measures: the configuration that
agrees with `ζ` on `Λ` and with `ω` off `Λ` gets probability `exp (-β * H) / Z`. -/
def gibbsMeasure (β : ℝ) (Λ : Finset Site) (ω : Config) : Measure Config :=
  (ENNReal.ofReal (partitionFunction β Λ ω))⁻¹ •
    ∑ ζ : Λ → Bool,
      ENNReal.ofReal (weight β Λ ω ζ) • Measure.dirac (glue Λ (extend Λ ζ ω) ω)

/-! ### Gibbs measures (the DLR equation) -/

/-- `μ` is a Gibbs measure for the two-dimensional Ising model at inverse temperature `β`: it is a
probability measure on `Config` whose conditional distribution in every finite volume `Λ`, given
the configuration outside `Λ`, is the finite-volume Gibbs distribution. This is the
Dobrushin–Lanford–Ruelle equation, written in the elementary integrated form
`μ A = ∫⁻ ω, gibbsMeasure β Λ ω A ∂μ` for measurable `A`. -/
def IsGibbs (β : ℝ) (μ : Measure Config) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ Λ : Finset Site, ∀ A : Set Config, MeasurableSet A →
      μ A = ∫⁻ ω, gibbsMeasure β Λ ω A ∂μ

/-- Translation of a configuration by the lattice vector `j`. -/
def shift (j : Site) (σ : Config) : Config := fun i ↦ σ (i - j)

/-! ### The theorems -/

/-- **Georgii, Theorem (6.9), the "in particular" half: the two-dimensional Ising phase
transition.** There is an inverse temperature `β₀` such that for every `β ≥ β₀` the two-dimensional
Ising ferromagnet admits two *distinct* Gibbs measures `μ₊` and `μ₋`, both invariant under all
lattice translations, exchanged by the global spin flip, and exhibiting spontaneous magnetisation:
the expected spin at the origin is strictly negative under `μ₋` and strictly positive under `μ₊`. -/
theorem ising_phase_transition :
    ∃ β₀ : ℝ, ∀ β ≥ β₀, ∃ μp μm : Measure Config,
      IsGibbs β μp ∧
      IsGibbs β μm ∧
      μp ≠ μm ∧
      (∀ j : Site, μp.map (shift j) = μp) ∧
      (∀ j : Site, μm.map (shift j) = μm) ∧
      μm = μp.map (fun σ i ↦ !σ i) ∧
      ∫ σ, spin (σ 0) ∂μm < 0 ∧
      0 < ∫ σ, spin (σ 0) ∂μp :=
  sorry

/-- **The Dobrushin half: uniqueness at high temperature.** When the inverse temperature is small
enough — Dobrushin's condition holds for the two-dimensional Ising model as soon as `β < 1 / 4`,
since every site has four neighbours — the Gibbs measure is unique. -/
theorem ising_uniqueness_at_high_temperature :
    ∀ β : ℝ, 0 ≤ β → β < 1 / 4 → ∀ μ ν : Measure Config, IsGibbs β μ → IsGibbs β ν → μ = ν :=
  sorry

end IsingChallenge

end
