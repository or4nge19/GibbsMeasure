import Comparator.Defs

/-!
# Definitions: uniqueness in one dimension (Georgii, Section 8.3)

This module extends the shared preamble `Comparator.Defs` with the vocabulary of Georgii's
Section 8.3: the oscillation `δ(f)` of (8.2), potentials in the sense of Definition (2.2), the
Hamiltonian of (2.3) as a *limit of partial sums over increasing volumes*, the Boltzmann factor
(2.4), the finite-volume Gibbs distribution (2.9) against an arbitrary σ-finite a priori measure,
the uniform domination hypothesis of Proposition (8.38), the spanning sum of condition (8.40) and
the chain structure that condition exploits.

**It imports `Comparator.Defs` — which imports `Mathlib` and nothing else — and nothing further.**
Every notion is spelled out from first principles, so a skeptical reader can check the statements
by eye against the book.

## Dictionary

| Georgii | here |
| --- | --- |
| `δ(f) = sup f − inf f`, (8.2) | `osc` |
| `Φ_A`, the interaction terms of `H_Λ`, (2.3) | `hamiltonianTerm` |
| Convention (2.1): `∑_A` is `lim_{Δ↑S} ∑_{A ⊆ Δ}` | `HasHamiltonian` |
| potential, Definition (2.2)(i) + (ii) | `IsPotential` |
| `H_Λ^Φ`, (2.3) | `hamiltonian` |
| `h_Λ^Φ = e^{−β H_Λ^Φ}`, (2.4) | `boltzmannFactor` |
| `λ_Λ(·\|ω) = λ^Λ × δ_{ω_{S∖Λ}}`, Notation (1.26) | `freeMeasure` |
| `Z_Λ^Φ(ω) = λ_Λ(h_Λ^Φ\|ω)`, (2.7) | `partitionFunction` |
| `λ`-admissibility, Definition (2.8) | `IsAdmissible` |
| `γ_Λ^Φ(A\|ω)`, Definition (2.9)/(1.27) | `gibbsKernel` |
| `‖Φ‖_i = ∑_{A ∋ i} sup\|Φ_A\|`, (2.12); `Φ ∈ ℬ`, (2.11) | `potentialNormAt`, `IsAbsolutelySummable` |
| the hypothesis of Proposition (8.38) | `IsUniformlyDominated` |
| `min A ≤ i < max A` | `Spans` |
| `∑_{A : min A ≤ i < max A} δ(Φ_A)`, the sum in (8.40) | `oscSpan` |
| the chain structure of `ℤ` and `ℕ` exploited in (8.39) | `HasBoundedBoundary` |
| the translate `A + n` used in Comments (8.41) | `shiftFinset` |

## The Hamiltonian is a limit of partial sums, not a `tsum`

Georgii's Definition (2.2)(ii) asks that the net of partial sums `∑_{A ⊆ Δ} Φ_A`, indexed by the
finite volumes `Δ` ordered by inclusion, converge — Convention (2.1).  This is *strictly weaker*
than unconditional (absolute) summability, and Theorem (8.39) is stated at exactly this
generality.  Accordingly `HasHamiltonian` is the convergence of that net and `hamiltonian` is its
limit; nothing below assumes absolute convergence.  `IsAbsolutelySummable` — Georgii's space `ℬ`
of (2.11) — is introduced separately, and used only where Georgii uses it, namely for the
*existence* half of (8.39), which rests on Theorem (4.23)(a).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace OneDimChallenge

open GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

/-! ## Georgii (8.2): the oscillation -/

/-- **Georgii (8.2)**: the oscillation `δ(f) = sup f − inf f = sup_{ζ,η} |f(ζ) − f(η)|` of a
function on the configuration space, recorded in `[0, ∞]` so that no boundedness has to be
assumed in order to write it down. -/
def osc (f : Config S E → ℝ) : ℝ≥0∞ :=
  ⨆ (ζ : Config S E) (η : Config S E), ENNReal.ofReal |f ζ - f η|

omit [MeasurableSpace E] in
theorem le_osc (f : Config S E → ℝ) (ζ η : Config S E) :
    ENNReal.ofReal |f ζ - f η| ≤ osc f :=
  le_iSup_of_le ζ (le_iSup_of_le η le_rfl)

omit [MeasurableSpace E] in
theorem osc_le {f : Config S E → ℝ} {c : ℝ≥0∞}
    (h : ∀ ζ η : Config S E, ENNReal.ofReal |f ζ - f η| ≤ c) : osc f ≤ c :=
  iSup₂_le h

omit [MeasurableSpace E] in
@[simp] theorem osc_const (r : ℝ) : osc (fun _ : Config S E ↦ r) = 0 := by
  simp [osc]

/-! ## Georgii (2.1)–(2.4): potentials, Hamiltonians, Boltzmann factors -/

/-- The interaction terms entering the Hamiltonian in the volume `Λ` (Georgii (2.3)), extended by
zero: `Φ_A` for those supports `A` that meet `Λ`, and `0` otherwise. -/
def hamiltonianTerm (Φ : Finset S → Config S E → ℝ) (Λ : Finset S) (ω : Config S E)
    (A : Finset S) : ℝ :=
  {B : Finset S | ∃ i ∈ B, i ∈ Λ}.indicator (fun B ↦ Φ B ω) A

/-- **Georgii, Convention (2.1)**: the sum `∑_{A ∩ Λ ≠ ∅} Φ_A` is the limit of the partial sums
`∑_{A ⊆ Δ} Φ_A` over the finite volumes `Δ` ordered by inclusion.  `HasHamiltonian Φ Λ ω h` says
that this net converges to `h`. -/
def HasHamiltonian (Φ : Finset S → Config S E → ℝ) (Λ : Finset S) (ω : Config S E) (h : ℝ) :
    Prop :=
  Tendsto (fun Δ : Finset S ↦ ∑ A ∈ Δ.powerset, hamiltonianTerm Φ Λ ω A) atTop (𝓝 h)

/-- **A potential**, Georgii Definition (2.2): a family `Φ` of interaction terms indexed by the
finite subsets `A` of the parameter set `S` such that

* (i) `Φ_A` is `𝓕_A`-measurable, i.e. depends only on the coordinates inside `A`;
* (ii) for every finite volume `Λ` the Hamiltonian series `∑_{A ∩ Λ ≠ ∅} Φ_A` converges in the
  sense of Convention (2.1).

No *absolute* convergence is assumed; that is Georgii's separate class `ℬ` of (2.11), see
`IsAbsolutelySummable` below. -/
structure IsPotential (Φ : Finset S → Config S E → ℝ) : Prop where
  /-- Georgii (2.2)(i): `Φ_A` is `𝓕_A`-measurable. -/
  measurable_inside : ∀ A : Finset S, Measurable[inside A] (Φ A)
  /-- Georgii (2.2)(ii): the Hamiltonian series converges in the sense of Convention (2.1). -/
  exists_hasHamiltonian : ∀ (Λ : Finset S) (ω : Config S E), ∃ h : ℝ, HasHamiltonian Φ Λ ω h

/-- **The Hamiltonian**, Georgii (2.3): `H_Λ^Φ = ∑_{A ∩ Λ ≠ ∅} Φ_A`, the limit of the partial sums
of `hamiltonianTerm` over increasing volumes. -/
def hamiltonian (Φ : Finset S → Config S E → ℝ) (Λ : Finset S) (ω : Config S E) : ℝ :=
  limUnder atTop (fun Δ : Finset S ↦ ∑ A ∈ Δ.powerset, hamiltonianTerm Φ Λ ω A)

/-- The limit in Georgii (2.3) is attained by `hamiltonian`. -/
theorem hasHamiltonian_hamiltonian {Φ : Finset S → Config S E → ℝ} (hΦ : IsPotential Φ)
    (Λ : Finset S) (ω : Config S E) : HasHamiltonian Φ Λ ω (hamiltonian Φ Λ ω) := by
  obtain ⟨h, hh⟩ := hΦ.exists_hasHamiltonian Λ ω
  rwa [hamiltonian, hh.limUnder_eq]

omit [MeasurableSpace E] in
theorem hamiltonian_eq_of_hasHamiltonian {Φ : Finset S → Config S E → ℝ} {Λ : Finset S}
    {ω : Config S E} {h : ℝ} (hh : HasHamiltonian Φ Λ ω h) : hamiltonian Φ Λ ω = h :=
  hh.limUnder_eq

/-- **The Boltzmann factor** `h_Λ^Φ = e^{−β H_Λ^Φ}`, Georgii (2.4). -/
def boltzmannFactor (Φ : Finset S → Config S E → ℝ) (β : ℝ) (Λ : Finset S) (ω : Config S E) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * hamiltonian Φ Λ ω))

/-! ## Georgii (1.26), (2.7)–(2.9): the finite-volume Gibbs distribution -/

open Classical in
/-- Extend an inner configuration `ζ : Λ → E` to a configuration on all of `S`, keeping the
boundary condition `ω` outside `Λ`. -/
def extend (Λ : Finset S) (ζ : Λ → E) (ω : Config S E) : Config S E :=
  fun i ↦ if h : i ∈ Λ then ζ ⟨i, h⟩ else ω i

theorem measurable_extend (Λ : Finset S) (ω : Config S E) :
    Measurable fun ζ : Λ → E ↦ extend Λ ζ ω := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  by_cases hi : i ∈ Λ
  · have h : (fun ζ : Λ → E ↦ extend Λ ζ ω i) = fun ζ ↦ ζ ⟨i, hi⟩ := by
      funext ζ; simp [extend, hi]
    rw [h]; exact measurable_pi_apply _
  · have h : (fun ζ : Λ → E ↦ extend Λ ζ ω i) = fun _ ↦ ω i := by
      funext ζ; simp [extend, hi]
    rw [h]; exact measurable_const

/-- **Georgii, Notation (1.26)**: the finite-volume a priori measure
`λ_Λ(·|ω) = λ^Λ × δ_{ω_{S∖Λ}}` — the coordinates inside `Λ` are resampled independently from the
single-spin measure `λ`, while the boundary condition `ω` is kept outside `Λ`.  No normalization
of `λ` is assumed. -/
def freeMeasure (lam : Measure E) (Λ : Finset S) (ω : Config S E) : Measure (Config S E) :=
  Measure.map (fun ζ : Λ → E ↦ extend Λ ζ ω) (Measure.pi fun _ : Λ ↦ lam)

/-- **The partition function** `Z_Λ^Φ(ω) = λ_Λ(h_Λ^Φ|ω)`, Georgii (2.7). -/
def partitionFunction (Φ : Finset S → Config S E → ℝ) (lam : Measure E) (β : ℝ) (Λ : Finset S)
    (ω : Config S E) : ℝ≥0∞ :=
  ∫⁻ σ, boltzmannFactor Φ β Λ σ ∂(freeMeasure lam Λ ω)

/-- **`λ`-admissibility**, Georgii Definition (2.8): every finite-volume partition function is
non-zero and finite. -/
def IsAdmissible (Φ : Finset S → Config S E → ℝ) (lam : Measure E) (β : ℝ) : Prop :=
  ∀ (Λ : Finset S) (ω : Config S E),
    partitionFunction Φ lam β Λ ω ≠ 0 ∧ partitionFunction Φ lam β Λ ω ≠ ⊤

/-- **The finite-volume Gibbs distribution**, Georgii Definition (2.9):
`γ_Λ^Φ(A | ω) = Z_Λ^Φ(ω)⁻¹ ∫ 1_A(σ) e^{−β H_Λ^Φ(σ)} λ_Λ(dσ|ω)`.  Both the measure integrated
against and the normalizing partition function are built from the same, un-normalized, a priori
measure `λ`, so the total mass `λ(E)^{|Λ|}` of `λ_Λ(·|ω)` cancels. -/
def gibbsKernel (Φ : Finset S → Config S E → ℝ) (lam : Measure E) (β : ℝ) (Λ : Finset S)
    (ω : Config S E) : Measure (Config S E) :=
  (partitionFunction Φ lam β Λ ω)⁻¹ • (freeMeasure lam Λ ω).withDensity (boltzmannFactor Φ β Λ)

theorem gibbsKernel_apply (Φ : Finset S → Config S E → ℝ) (lam : Measure E) (β : ℝ)
    (Λ : Finset S) (ω : Config S E) {A : Set (Config S E)} (hA : MeasurableSet A) :
    gibbsKernel Φ lam β Λ ω A
      = (∫⁻ σ in A, boltzmannFactor Φ β Λ σ ∂(freeMeasure lam Λ ω))
        / ∫⁻ σ, boltzmannFactor Φ β Λ σ ∂(freeMeasure lam Λ ω) := by
  rw [gibbsKernel, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA, partitionFunction,
    ENNReal.div_eq_inv_mul]

/-! ## Georgii (2.11), (2.12): absolutely summable potentials -/

/-- **Georgii (2.12)**: the interaction norm `‖Φ‖_i = ∑_{A ∋ i} sup_ω |Φ_A(ω)|`. -/
def potentialNormAt (Φ : Finset S → Config S E → ℝ) (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S,
    {B : Finset S | i ∈ B}.indicator (fun B ↦ ⨆ ω : Config S E, ENNReal.ofReal |Φ B ω|) A

/-- **Georgii (2.11)**: `Φ ∈ ℬ`, i.e. `‖Φ‖_i < ∞` at every site. -/
def IsAbsolutelySummable (Φ : Finset S → Config S E → ℝ) : Prop :=
  ∀ i : S, potentialNormAt Φ i ≠ ⊤

/-! ## Georgii (8.38): uniform domination -/

/-- **The hypothesis of Georgii, Proposition (8.38)**: every cylinder event `A` admits a volume
`Λ` with `γ_Λ(A|ζ) ≥ c γ_Λ(A|η)` for all boundary conditions `ζ, η`. -/
def IsUniformlyDominated (γ : Finset S → Config S E → Measure (Config S E)) (c : ℝ≥0∞) : Prop :=
  ∀ A : Set (Config S E), IsLocalEvent A →
    ∃ Λ : Finset S, ∀ ζ η : Config S E, c * γ Λ η A ≤ γ Λ ζ A

/-! ## Georgii (8.40): the spanning sum -/

section Order

variable [Preorder S]

/-- `A` **spans** the site `i`, i.e. `min A ≤ i < max A`: `A` has an element `≤ i` and an element
`> i`.  (For `A = ∅` this is false, matching `min ∅ = ∞`.) -/
def Spans (A : Finset S) (i : S) : Prop := (∃ a ∈ A, a ≤ i) ∧ ∃ b ∈ A, i < b

/-- **The sum appearing in Georgii (8.40)**: `∑_{A ∈ 𝓢, min A ≤ i < max A} δ(Φ_A)`. -/
def oscSpan (Φ : Finset S → Config S E → ℝ) (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S, {B : Finset S | Spans B i}.indicator (fun B ↦ osc (Φ B)) A

variable (S) in
/-- **Georgii's one-dimensional input** (the paragraph opening Section 8.3): `S` is exhausted by
intervals with at most `m` boundary sites.  Formally: every finite `Λ₀` is contained in a volume
`Λ` admitting a set `D` of at most `m` sites such that every interaction support meeting `Λ` and
leaving `Λ` spans a site of `D`.

Georgii's two cases are `S = ℤ` with `Λ = ]−n, n]` and `D = {−n, n}` (`m = 2`) and `S = ℕ` with
`Λ = [0, n]` and `D = {n}` (`m = 1`). -/
def HasBoundedBoundary (m : ℕ) : Prop :=
  ∀ Λ₀ : Finset S, ∃ Λ : Finset S, Λ₀ ⊆ Λ ∧ ∃ D : Finset S, D.card ≤ m ∧
    ∀ A : Finset S, ¬ Disjoint A Λ → ¬ A ⊆ Λ → ∃ k ∈ D, Spans A k

end Order

/-! ## Georgii (8.41): translates on `ℤ` -/

/-- The translate `A + n` of a finite set of integers, used in Comments (8.41). -/
def shiftFinset (n : ℤ) (A : Finset ℤ) : Finset ℤ := A.map (Equiv.addRight n).toEmbedding

@[simp] theorem mem_shiftFinset {n x : ℤ} {A : Finset ℤ} : x ∈ shiftFinset n A ↔ x - n ∈ A := by
  simp only [shiftFinset, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.coe_addRight]
  exact ⟨by rintro ⟨a, ha, rfl⟩; simpa using ha, fun h ↦ ⟨x - n, h, by ring⟩⟩

/-! ## Non-vacuity: the zero potential

The zero potential is a potential in the sense of Definition (2.2), is absolutely summable, is
`λ`-admissible over any probability a priori measure, satisfies (8.40) with the value `0`, and its
Gibbsian specification is the independent one — so none of the hypotheses assembled above is
empty. -/

section Zero

omit [MeasurableSpace E] in
@[simp] theorem hamiltonianTerm_zero (Λ : Finset S) (ω : Config S E) (A : Finset S) :
    hamiltonianTerm (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) Λ ω A = 0 := by
  rw [hamiltonianTerm]
  by_cases h : A ∈ {B : Finset S | ∃ i ∈ B, i ∈ Λ} <;> simp [h]

omit [MeasurableSpace E] in
@[simp] theorem hamiltonian_zero (Λ : Finset S) (ω : Config S E) :
    hamiltonian (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) Λ ω = 0 :=
  hamiltonian_eq_of_hasHamiltonian (by simp [HasHamiltonian])

theorem isPotential_zero : IsPotential (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) where
  measurable_inside _ := measurable_const
  exists_hasHamiltonian Λ ω := ⟨0, by simp [HasHamiltonian]⟩

omit [MeasurableSpace E] in
theorem isAbsolutelySummable_zero :
    IsAbsolutelySummable (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) := by
  intro i
  have h : potentialNormAt (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) i = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun A ↦ ?_
    by_cases hA : A ∈ {B : Finset S | i ∈ B} <;> simp [hA]
  simp [h]

omit [MeasurableSpace E] in
@[simp] theorem boltzmannFactor_zero (β : ℝ) (Λ : Finset S) :
    boltzmannFactor (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) β Λ = 1 := by
  funext σ; simp [boltzmannFactor]

instance isProbabilityMeasure_freeMeasure (lam : Measure E) [IsProbabilityMeasure lam]
    (Λ : Finset S) (ω : Config S E) : IsProbabilityMeasure (freeMeasure lam Λ ω) := by
  rw [freeMeasure]
  exact Measure.isProbabilityMeasure_map (measurable_extend Λ ω).aemeasurable

theorem partitionFunction_zero (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (Λ : Finset S) (ω : Config S E) :
    partitionFunction (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) lam β Λ ω = 1 := by
  rw [partitionFunction, boltzmannFactor_zero]
  simp

theorem isAdmissible_zero (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ) :
    IsAdmissible (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) lam β := fun Λ ω ↦ by
  rw [partitionFunction_zero]
  exact ⟨one_ne_zero, ENNReal.one_ne_top⟩

/-- **The Gibbsian specification of the zero potential is the independent one.** -/
theorem gibbsKernel_zero (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ) (Λ : Finset S)
    (ω : Config S E) :
    gibbsKernel (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) lam β Λ ω
      = freeMeasure lam Λ ω := by
  rw [gibbsKernel, partitionFunction_zero, boltzmannFactor_zero, withDensity_one, inv_one,
    one_smul]

variable [Preorder S]

omit [MeasurableSpace E] in
theorem oscSpan_zero (i : S) :
    oscSpan (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) i = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun A ↦ ?_
  by_cases hA : A ∈ {B : Finset S | Spans B i} <;> simp [hA]

omit [MeasurableSpace E] in
theorem iSup_oscSpan_zero_ne_top :
    (⨆ i : S, oscSpan (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) i) ≠ ⊤ := by
  simp [oscSpan_zero]

end Zero

end OneDimChallenge

end
