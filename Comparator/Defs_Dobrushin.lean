import Comparator.Defs

/-!
# Definitions: Dobrushin's uniqueness theorem (Georgii, Section 8.1)

This module extends the shared preamble `Comparator.Defs` with Georgii's Section 8.1: the uniform
distance (8.1), Dobrushin's interdependence matrix (8.5), Dobrushin's condition of weak dependence
(8.6), the single-site oscillation (8.14) and the series (8.19).  It holds the definitions used by
`Comparator/Challenge_Dobrushin.lean` and `Comparator/Solution_Dobrushin.lean`.

**It imports `Comparator.Defs` — which imports `Mathlib` and nothing else — and nothing further.**
Every notion is spelled out from first principles, so a skeptical reader can check the statements
by eye against the book.

## Dictionary

| Georgii | here |
| --- | --- |
| `‖α₁ − α₂‖ = sup_A \|α₁(A) − α₂(A)\|`, (8.1) | `unifDist` |
| `γ_i^0(·\|ζ)`, the law of `σ_i` under `γ_{i}(·\|ζ)`, (8.4) | `proj` |
| `C_ij(γ)`, Dobrushin's interdependence matrix, (8.5) | `interdep` |
| `𝓛_Λ`, `𝓛`: bounded local observables, (2.20)(a) | `IsLocalFn` |
| `𝓛̄`: quasilocal observables, (2.20)(b) | `IsQuasilocalFn` |
| quasilocal specification, (2.23): `f ∈ 𝓛` implies `γ_Λ f ∈ 𝓛̄` | `IsQuasilocalSpec` |
| Dobrushin's condition `c(γ) = sup_i ∑_j C_ij(γ) < 1`, (8.6) | `IsDobrushin` |
| `δ_j(f)`, the single-site oscillation, (8.14) | `oscAt` |
| `C(γ)^n b` | `interdepIter` |
| `D(γ) b = ∑_{n ≥ 0} C(γ)^n b`, (8.19) | `interdepSeries` |
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace DobrushinChallenge

open GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

/-! ## Georgii (8.1): the uniform distance -/

/-- **Georgii (8.1)**: the uniform distance `‖α₁ − α₂‖ = sup_A |α₁(A) − α₂(A)|` between two
probability measures on `E`, the supremum ranging over all measurable `A ⊆ E`. The values
`α_k A` of a probability measure are finite, so `(α_k A).toReal` loses no information, and the
result is recorded in `ℝ≥0∞` purely so that the suprema and series below need no boundedness
side conditions. -/
def unifDist (α₁ α₂ : Measure E) : ℝ≥0∞ :=
  ⨆ (A : Set E) (_ : MeasurableSet A), ENNReal.ofReal |(α₁ A).toReal - (α₂ A).toReal|

theorem le_unifDist {α₁ α₂ : Measure E} {A : Set E} (hA : MeasurableSet A) :
    ENNReal.ofReal |(α₁ A).toReal - (α₂ A).toReal| ≤ unifDist α₁ α₂ :=
  le_iSup₂ (f := fun (A : Set E) (_ : MeasurableSet A) ↦
    ENNReal.ofReal |(α₁ A).toReal - (α₂ A).toReal|) A hA

theorem unifDist_le {α₁ α₂ : Measure E} {c : ℝ≥0∞}
    (h : ∀ A : Set E, MeasurableSet A → ENNReal.ofReal |(α₁ A).toReal - (α₂ A).toReal| ≤ c) :
    unifDist α₁ α₂ ≤ c := iSup₂_le h

/-- The uniform distance is symmetric. -/
theorem unifDist_comm (α₁ α₂ : Measure E) : unifDist α₁ α₂ = unifDist α₂ α₁ := by
  simp only [unifDist, abs_sub_comm]

@[simp] theorem unifDist_self (α : Measure E) : unifDist α α = 0 := by
  simp [unifDist]

/-- Sanity check: the uniform distance of two probability measures is at most `1`. -/
theorem unifDist_le_one (α₁ α₂ : Measure E) [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂] :
    unifDist α₁ α₂ ≤ 1 := by
  have key : ∀ (α : Measure E) (_ : IsProbabilityMeasure α) (A : Set E),
      0 ≤ (α A).toReal ∧ (α A).toReal ≤ 1 := by
    intro α hα A
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  refine unifDist_le fun A _ ↦ ENNReal.ofReal_le_one.2 ?_
  obtain ⟨h1, h2⟩ := key α₁ ‹_› A
  obtain ⟨h3, h4⟩ := key α₂ ‹_› A
  rw [abs_le]
  constructor <;> linarith

/-! ## Georgii (8.4), (8.5): the single-site distributions and Dobrushin's matrix -/

/-- **Georgii (8.4)**: `γ_i^0(·|ζ)`, the law of the single spin `σ_i` under the single-site
kernel `γ_{i}(·|ζ)`. -/
def proj (γ : Finset S → Config S E → Measure (Config S E)) (i : S) (ζ : Config S E) :
    Measure E := (γ {i} ζ).map fun ω ↦ ω i

/-- **Georgii (8.5)**: Dobrushin's interdependence matrix
`C_ij(γ) = sup { ‖γ_i^0(·|ζ) − γ_i^0(·|η)‖ : ζ, η agree off the single site j }`. -/
def interdep (γ : Finset S → Config S E → Measure (Config S E)) (i j : S) : ℝ≥0∞ :=
  ⨆ (ζ : Config S E) (η : Config S E) (_ : ∀ k, k ≠ j → ζ k = η k),
    unifDist (proj γ i ζ) (proj γ i η)

theorem le_interdep {γ : Finset S → Config S E → Measure (Config S E)} {i j : S}
    {ζ η : Config S E} (h : ∀ k, k ≠ j → ζ k = η k) :
    unifDist (proj γ i ζ) (proj γ i η) ≤ interdep γ i j :=
  le_iSup_of_le ζ (le_iSup_of_le η (le_iSup_of_le h le_rfl))

theorem interdep_le {γ : Finset S → Config S E → Measure (Config S E)} {i j : S} {c : ℝ≥0∞}
    (h : ∀ ζ η : Config S E, (∀ k, k ≠ j → ζ k = η k) →
      unifDist (proj γ i ζ) (proj γ i η) ≤ c) :
    interdep γ i j ≤ c := iSup₂_le fun ζ η ↦ iSup_le (h ζ η)

/-! ## Georgii (2.20), (2.23): local and quasilocal observables -/

/-- A bounded function on the configuration space. -/
def IsBddFn (f : Config S E → ℝ) : Prop := ∃ C : ℝ, ∀ ω, |f ω| ≤ C

/-- **Georgii (2.20)(a)**: a *local* observable, i.e. an element of `𝓛 = ⋃_Λ 𝓛_Λ`: a bounded
function of the configuration which is `𝓕_Λ`-measurable for some finite volume `Λ`, i.e. which
depends on finitely many coordinates only. -/
def IsLocalFn (f : Config S E → ℝ) : Prop :=
  IsBddFn f ∧ ∃ Λ : Finset S, Measurable[inside Λ] f

/-- Sanity check: local observables are measurable. -/
theorem IsLocalFn.measurable {f : Config S E → ℝ} (hf : IsLocalFn f) : Measurable f := by
  obtain ⟨Λ, hΛ⟩ := hf.2
  exact hΛ.mono (inside_le Λ) le_rfl

/-- **Georgii (2.20)(b)**: a *quasilocal* observable, i.e. an element of `𝓛̄`: a bounded function
which is a **uniform** limit of local observables. -/
def IsQuasilocalFn (f : Config S E → ℝ) : Prop :=
  IsBddFn f ∧ ∀ ε : ℝ, 0 < ε → ∃ g : Config S E → ℝ, IsLocalFn g ∧ ∀ ω, |f ω - g ω| ≤ ε

theorem IsLocalFn.isQuasilocalFn {f : Config S E → ℝ} (hf : IsLocalFn f) : IsQuasilocalFn f :=
  ⟨hf.1, fun ε hε ↦ ⟨f, hf, fun ω ↦ by simp [le_of_lt hε]⟩⟩

/-- Sanity check: quasilocal observables are measurable, being uniform limits of measurable
functions; so the conclusion of `IsQuasilocalSpec` below is a statement about a genuine
observable. -/
theorem IsQuasilocalFn.measurable {f : Config S E → ℝ} (hf : IsQuasilocalFn f) : Measurable f := by
  have hex : ∀ n : ℕ, ∃ g : Config S E → ℝ, IsLocalFn g ∧ ∀ ω, |f ω - g ω| ≤ 1 / (n + 1) :=
    fun n ↦ hf.2 (1 / (n + 1)) (by positivity)
  choose g hg1 hg2 using hex
  refine measurable_of_tendsto_metrizable (fun n ↦ (hg1 n).measurable) ?_
  rw [tendsto_pi_nhds]
  intro ω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hmono : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
    have : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact one_div_le_one_div_of_le (by positivity) this
  rw [Real.dist_eq, abs_sub_comm]
  calc |f ω - g n ω| ≤ 1 / (n + 1) := hg2 n ω
    _ ≤ 1 / (N + 1) := hmono
    _ < ε := hN

/-- **Georgii, Definition (2.23)**: the specification `γ` is *quasilocal* if for each `Λ ∈ 𝓢`,
`f ∈ 𝓛` implies `γ_Λ f ∈ 𝓛̄`, where `(γ_Λ f)(ω) = ∫ f dγ_Λ(·|ω)`.

Note that the premise is that `f` be **local**, not merely quasilocal — this is Georgii's own
formulation: "to verify that a given specification `γ` is quasilocal we only need to check that
`γ_Λ f ∈ 𝓛̄` when `Λ ∈ 𝓢` and `f ∈ 𝓛`" (the remark immediately following (2.23)). The extension
from local to quasilocal `f` is automatic, because `γ_Λ` is a contraction for the sup-norm and
`𝓛̄` is the uniform closure of `𝓛`; but it is a genuine analytic step, and it is *not* assumed
here. Since `IsLocalFn.isQuasilocalFn` says every local observable is quasilocal, requiring the
conclusion only for local `f` is the **weaker** demand on `γ`. Hence `IsDobrushin` below is a
weaker hypothesis, and the uniqueness theorem that consumes it is correspondingly stronger. -/
def IsQuasilocalSpec (γ : Finset S → Config S E → Measure (Config S E)) : Prop :=
  ∀ (Λ : Finset S) (f : Config S E → ℝ), IsLocalFn f →
    IsQuasilocalFn fun ω ↦ ∫ x, f x ∂(γ Λ ω)

/-- Sanity check that `IsQuasilocalSpec` is indeed the weaker of the two readings of (2.23):
demanding `γ_Λ f ∈ 𝓛̄` for every *quasilocal* `f` implies demanding it for every *local* `f`,
because local observables are quasilocal. Consequently `IsDobrushin` below is implied by (and is
not equivalent to) the condition one gets by substituting the quasilocal-premise reading, so any
theorem taking `IsDobrushin` as a hypothesis is at least as strong as its counterpart under that
reading. -/
theorem isQuasilocalSpec_of_forall_isQuasilocalFn
    {γ : Finset S → Config S E → Measure (Config S E)}
    (h : ∀ (Λ : Finset S) (f : Config S E → ℝ), IsQuasilocalFn f →
      IsQuasilocalFn fun ω ↦ ∫ x, f x ∂(γ Λ ω)) :
    IsQuasilocalSpec γ :=
  fun Λ f hf ↦ h Λ f hf.isQuasilocalFn

/-! ## Georgii (8.6): Dobrushin's condition of weak dependence -/

/-- **Georgii (8.6)**: Dobrushin's condition of weak dependence. It has *two* conjuncts: `γ` is
quasilocal, and `c(γ) = sup_i ∑_j C_ij(γ) < 1`. The quasilocality conjunct carries real content:
the row sums say nothing about the dependence of `γ_i^0(·|ω)` on the behaviour of `ω` at
infinity, and Georgii's Example (2.27) has `C_ij(γ) = 0` for all `i, j` while `𝓖(γ)` is
uncountable. -/
def IsDobrushin (γ : Finset S → Config S E → Measure (Config S E)) : Prop :=
  IsQuasilocalSpec γ ∧ ⨆ i, ∑' j, interdep γ i j < 1

/-! ## Georgii (8.14), (8.19): the single-site oscillation and the series `D(γ)` -/

/-- **Georgii (8.14)**: the single-site oscillation
`δ_j(f) = sup { |f(ζ) − f(η)| : ζ, η agree off the single site j }`. -/
def oscAt (f : Config S E → ℝ) (j : S) : ℝ≥0∞ :=
  ⨆ (ζ : Config S E) (η : Config S E) (_ : ∀ k, k ≠ j → ζ k = η k),
    ENNReal.ofReal |f ζ - f η|

omit [MeasurableSpace E] in
@[simp] theorem oscAt_const (r : ℝ) (j : S) : oscAt (fun _ : Config S E ↦ r) j = 0 := by
  simp [oscAt]

/-- `C(γ)^n b`, the `n`-fold action of Dobrushin's interdependence matrix on a vector. -/
def interdepIter (γ : Finset S → Config S E → Measure (Config S E)) :
    ℕ → (S → ℝ≥0∞) → S → ℝ≥0∞
  | 0, b => b
  | (n + 1), b => fun i ↦ ∑' j, interdep γ i j * interdepIter γ n b j

/-- **Georgii (8.19)**: `D(γ) b = ∑_{n ≥ 0} C(γ)^n b`. -/
def interdepSeries (γ : Finset S → Config S E → Measure (Config S E)) (b : S → ℝ≥0∞) (i : S) :
    ℝ≥0∞ := ∑' n : ℕ, interdepIter γ n b i

end DobrushinChallenge

end
