import Comparator.Defs

/-!
# Definitions: quasilocality, and Georgii Example (4.16)

Quasilocality (Georgii (2.20)–(2.23)) and the single-particle kernels of Georgii Example (4.16):
a single particle at a uniformly random site of a countably infinite `S`, with single-site state
space `Bool`.  For a finite volume `Λ` the kernel `γ_Λ(· | ω)` is the uniform distribution on the
`|Λ|` one-particle configurations inside `Λ` when `ω` carries no particle outside `Λ`, and the
Dirac mass at `0_Λ ω` otherwise.

## Main definitions

* `oscOutside`, `IsLocalFun`, `IsQuasilocalFun`: Georgii (2.20), (2.21)(1)/(2.22); `IsQuasilocal`:
  Georgii (2.23)
* `spike`, `zeroOn`, `vanishOff`, `spikeMeasure`, `gamma`: Georgii Example (4.16)

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], (2.23) and Example (4.16)
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

/-- **Georgii (2.22)**: the oscillation of `f` off the finite volume `Δ`, i.e. how much `f` can
still change when the configuration is modified outside `Δ` only. -/
def oscOutside (Δ : Finset S) (f : Config S E → ℝ) : ℝ≥0∞ :=
  ⨆ ω : Config S E, ⨆ ω' : Config S E, ⨆ _ : ∀ i ∈ Δ, ω i = ω' i, ENNReal.ofReal |f ω - f ω'|

omit [MeasurableSpace E] in
theorem le_oscOutside {Δ : Finset S} {f : Config S E → ℝ} {ω ω' : Config S E}
    (h : ∀ i ∈ Δ, ω i = ω' i) : ENNReal.ofReal |f ω - f ω'| ≤ oscOutside Δ f :=
  le_iSup_of_le ω (le_iSup_of_le ω' (le_iSup (fun _ : ∀ i ∈ Δ, ω i = ω' i =>
    ENNReal.ofReal |f ω - f ω'|) h))

/-- `f` depends on finitely many coordinates only. -/
def IsLocalFun (f : Config S E → ℝ) : Prop :=
  ∃ Δ : Finset S, ∀ ω ω' : Config S E, (∀ i ∈ Δ, ω i = ω' i) → f ω = f ω'

/-- **Georgii (2.20)(b) with Remark (2.21)(1)**: `f` is a uniform limit of local functions,
equivalently its oscillation off `Δ` tends to `0` along the net of finite volumes `Δ ↑ S`. -/
def IsQuasilocalFun (f : Config S E → ℝ) : Prop :=
  Filter.Tendsto (fun Δ : Finset S => oscOutside Δ f) Filter.atTop (nhds 0)

omit [MeasurableSpace E] in
theorem IsLocalFun.isQuasilocalFun {f : Config S E → ℝ} (hf : IsLocalFun f) :
    IsQuasilocalFun f := by
  obtain ⟨Δ₀, hΔ₀⟩ := hf
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop Δ₀] with Δ hΔ
  refine le_antisymm (iSup₂_le fun ω ω' => iSup_le fun h => ?_) bot_le
  rw [hΔ₀ ω ω' fun i hi => h i (hΔ hi)]
  simp

/-- **Georgii (2.23)** for a family of kernels: `γ_Λ f` is quasilocal for every finite volume `Λ`
and every bounded measurable local `f`. -/
def IsQuasilocal (γ : Finset S → Config S E → Measure (Config S E)) : Prop :=
  ∀ (Λ : Finset S) (f : Config S E → ℝ), Measurable f → IsLocalFun f → (∀ ω, |f ω| ≤ 1) →
    IsQuasilocalFun fun ω => ∫ σ, f σ ∂(γ Λ ω)

/-- Non-vacuity of `IsQuasilocal`: the identity family `γ_Λ(·|ω) = δ_ω` is quasilocal. -/
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
/-- **Georgii, Example (4.16)**: the single-particle kernels.  On `{ω = 0 off Λ}` the particle is
placed uniformly at random inside `Λ`; otherwise `Λ` is emptied.  For `Λ = ∅` this is the identity
kernel `γ_∅(·|ω) = δ_ω`, as it must be. -/
def gamma (Λ : Finset S) (ω : Config S Bool) : Measure (Config S Bool) :=
  if Λ.Nonempty ∧ ω ∈ vanishOff Λ then spikeMeasure Λ else Measure.dirac (zeroOn Λ ω)

end SingleParticle

end GibbsChallenge

end
