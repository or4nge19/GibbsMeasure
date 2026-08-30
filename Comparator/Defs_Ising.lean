import Mathlib

/-!
# The two-dimensional Ising model, spelled out from first principles

This module holds the Mathlib-only definition of the two-dimensional Ising ferromagnet shared by
the `comparator` challenge files `Comparator/Challenge.lean` (Georgii, Theorem (6.9), the "in
particular" half) and `Comparator/Challenge_LowTemperature.lean` (Theorem (6.9), first assertion).

**It imports `Mathlib` and nothing else.** In particular it does *not* import the `GibbsMeasure`
library whose theorems are being certified: every notion appearing in the final statements — the
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
* `IsLocalEvent A` says that `A` depends on the spins in a finite volume only — Georgii's
  algebra `𝓕⁰` of local events.
* `nonUniqueness` is the set of `β ≥ 0` carrying two distinct Gibbs measures, and
  `betaC = sInf nonUniqueness` is the critical inverse temperature.
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

/-! ### Local events

An event is *local* — Georgii's algebra `𝓕⁰` — when it depends on the spins in a finite volume
only: there is a finite `Λ` such that any two configurations agreeing on `Λ` are either both in
the event or both outside it. -/

/-- `A` depends on the spins in a finite volume only. -/
def IsLocalEvent (A : Set Config) : Prop :=
  ∃ Λ : Finset Site, ∀ σ τ : Config, (∀ i ∈ Λ, σ i = τ i) → (σ ∈ A ↔ τ ∈ A)

/-! ### The critical inverse temperature -/

/-- The set of nonnegative inverse temperatures at which the Gibbs measure is *not* unique. -/
def nonUniqueness : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ ∃ μ ν : Measure Config, IsGibbs β μ ∧ IsGibbs β ν ∧ μ ≠ ν}

/-- The **critical inverse temperature** of the two-dimensional Ising ferromagnet: the infimum of
the inverse temperatures at which the Gibbs measure fails to be unique. -/
def betaC : ℝ := sInf nonUniqueness

end IsingChallenge

end
