import Comparator.Defs

/-!
# Definitions: quasilocality, and Georgii Example (4.16) — a single particle at a random site

This module extends the shared preamble `Comparator.Defs` with quasilocality (Georgii (2.23) /
(4.15)) and with the single-particle kernels of Georgii Example (4.16).  It holds the definitions
used by `Comparator/Challenge_NoGibbs.lean` and `Comparator/Solution_NoGibbs.lean`.

**It imports `Comparator.Defs` — which imports `Mathlib` and nothing else — and nothing further**,
and every notion is spelled out from first principles.

A **single particle at a uniformly random site**.

The site set `S` is countably infinite, the single-site state space is `Bool` (`false` = "empty",
`true` = "occupied"), and for a finite volume `Λ` the kernel `γ_Λ(· | ω)` is:

* if `ω` vanishes off `Λ` (there is no particle outside `Λ`), the **uniform distribution on the
  `|Λ|` configurations carrying exactly one particle inside `Λ`**;
* otherwise the **Dirac mass at `0_Λ ω`**, the configuration `ω` emptied inside `Λ`.

This is a genuine specification — proper, consistent, and each `γ_Λ` is a probability kernel from
the external σ-algebra `𝓣_Λ` — yet it has **no** Gibbs measure at all
(`not_isGibbs_gamma`): the single particle "escapes to infinity". So the existence theorems
(4.17) / (4.22) really do need a hypothesis beyond "specification": this `γ` is **not quasilocal**
(`not_isQuasilocal_gamma`), witnessed explicitly by `one_le_oscOutside_gamma`.

The infinitude of `S` is essential: for a finite `S` the very same formulas define a specification
whose uniform distribution on the `|S|` one-particle configurations *is* a Gibbs measure
(`isGibbs_spikeMeasure_of_finite`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

/-! ## Quasilocality, from first principles -/

section Quasilocal

variable {S E : Type*} [MeasurableSpace E]

/-- The **oscillation of `f` off the finite volume `Δ`**: how much `f` can still change when the
configuration is modified outside `Δ` only. Georgii (2.23) / (4.15). -/
def oscOutside (Δ : Finset S) (f : Config S E → ℝ) : ℝ≥0∞ :=
  ⨆ ω : Config S E, ⨆ ω' : Config S E, ⨆ _ : ∀ i ∈ Δ, ω i = ω' i, ENNReal.ofReal |f ω - f ω'|

omit [MeasurableSpace E] in
theorem le_oscOutside {Δ : Finset S} {f : Config S E → ℝ} {ω ω' : Config S E}
    (h : ∀ i ∈ Δ, ω i = ω' i) : ENNReal.ofReal |f ω - f ω'| ≤ oscOutside Δ f :=
  le_iSup_of_le ω (le_iSup_of_le ω' (le_iSup (fun _ : ∀ i ∈ Δ, ω i = ω' i =>
    ENNReal.ofReal |f ω - f ω'|) h))

/-- `f` is **local**: it depends on finitely many coordinates only. -/
def IsLocalFun (f : Config S E → ℝ) : Prop :=
  ∃ Δ : Finset S, ∀ ω ω' : Config S E, (∀ i ∈ Δ, ω i = ω' i) → f ω = f ω'

/-- `f` is **quasilocal**, Georgii (2.23): it is a uniform limit of local functions, equivalently
its oscillation off `Δ` tends to `0` along the net of finite volumes `Δ ↑ S`. -/
def IsQuasilocalFun (f : Config S E → ℝ) : Prop :=
  Filter.Tendsto (fun Δ : Finset S => oscOutside Δ f) Filter.atTop (nhds 0)

omit [MeasurableSpace E] in
/-- A local function is quasilocal, so the notion is not vacuous. -/
theorem IsLocalFun.isQuasilocalFun {f : Config S E → ℝ} (hf : IsLocalFun f) :
    IsQuasilocalFun f := by
  obtain ⟨Δ₀, hΔ₀⟩ := hf
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop Δ₀] with Δ hΔ
  refine le_antisymm (iSup₂_le fun ω ω' => iSup_le fun h => ?_) bot_le
  rw [hΔ₀ ω ω' fun i hi => h i (hΔ hi)]
  simp

/-- **Quasilocality of a family of kernels**, Georgii (2.23): `γ_Λ f` is a quasilocal function for
every finite volume `Λ` and every bounded measurable local function `f`. -/
def IsQuasilocal (γ : Finset S → Config S E → Measure (Config S E)) : Prop :=
  ∀ (Λ : Finset S) (f : Config S E → ℝ), Measurable f → IsLocalFun f → (∀ ω, |f ω| ≤ 1) →
    IsQuasilocalFun fun ω => ∫ σ, f σ ∂(γ Λ ω)

/-- **`IsQuasilocal` is not vacuous**: on an arbitrary site set the identity family
`γ_Λ(·|ω) = δ_ω` is quasilocal, because `γ_Λ f = f` is already local. -/
theorem isQuasilocal_dirac :
    IsQuasilocal fun (_ : Finset S) (ω : Config S E) => Measure.dirac ω := by
  intro Λ f hf hloc _
  have h : (fun ω : Config S E => ∫ σ, f σ ∂(Measure.dirac ω)) = f :=
    funext fun ω => integral_dirac' f ω hf.stronglyMeasurable
  rw [h]
  exact hloc.isQuasilocalFun

end Quasilocal

/-! ## The single-particle specification of Georgii (4.16) -/

namespace SingleParticle

variable {S : Type*} [Countable S] [DecidableEq S]

/-- Georgii's `ω^a`: the configuration with a single particle at the site `a`. -/
def spike (a : S) : Config S Bool := fun i => decide (i = a)

/-- Georgii's `0_Λ ω`: the configuration `ω` emptied inside `Λ`. -/
def zeroOn (Λ : Finset S) (ω : Config S Bool) : Config S Bool :=
  fun i => if i ∈ Λ then false else ω i

/-- The event `{ω = 0 off Λ}`: there is no particle outside `Λ`. -/
def vanishOff (Λ : Finset S) : Set (Config S Bool) := {ω | ∀ i ∉ Λ, ω i = false}

/-- The uniform distribution on the `|Λ|` one-particle configurations `ω^a`, `a ∈ Λ`. -/
def spikeMeasure (Λ : Finset S) : Measure (Config S Bool) :=
  (Λ.card : ℝ≥0∞)⁻¹ • ∑ a ∈ Λ, Measure.dirac (spike a)

open Classical in
/-- **Georgii Example (4.16)**: the single-particle kernels. On `{ω = 0 off Λ}` the particle is
placed uniformly at random inside `Λ`; otherwise the volume `Λ` is emptied. (For `Λ = ∅` this is
the identity kernel `γ_∅(·|ω) = δ_ω`, as it must be.) -/
def gamma (Λ : Finset S) (ω : Config S Bool) : Measure (Config S Bool) :=
  if Λ.Nonempty ∧ ω ∈ vanishOff Λ then spikeMeasure Λ else Measure.dirac (zeroOn Λ ω)

end SingleParticle

end GibbsChallenge

end
