/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Function.BoundedMeasurable
public import GibbsMeasure.Mathlib.Logic.Function.DependsOn
public import GibbsMeasure.Prereqs.CylinderEvents
public import Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# Local and quasilocal observables

Georgii's Definition (2.20): a bounded function on `E^S` is *local* if it is `𝓕_Λ`-measurable for
some finite `Λ`, and *quasilocal* if it is a uniform limit of local functions.

Both are subalgebras of the Banach algebra `lp (fun _ : (S → E) ↦ ℝ) ∞` of bounded functions, the
second being the topological closure of the first. No topology on `E` is involved.

## Main declarations

* `GibbsMeasure.localFunctionsOn`, `GibbsMeasure.localFunctions`,
  `GibbsMeasure.quasilocalFunctions`: Georgii's `𝓛_Λ`, `𝓛`, `𝓛̄`.
* `GibbsMeasure.oscOutside`: the oscillation of Georgii's eq. (2.22).
* `GibbsMeasure.mem_quasilocalFunctions_iff`: Georgii Remark (2.21)(1).
-/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace GibbsMeasure

variable (S E : Type*) [MeasurableSpace E]

/-- Georgii (2.20)(a): `𝓛_Λ`, the bounded `𝓕_Λ`-measurable observables. -/
def localFunctionsOn (Λ : Finset S) : Subalgebra ℝ (lp (fun _ : S → E ↦ ℝ) ∞) :=
  boundedMeasurable (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S))

variable {S E}

lemma mem_localFunctionsOn {Λ : Finset S} {f : lp (fun _ : S → E ↦ ℝ) ∞} :
    f ∈ localFunctionsOn S E Λ ↔
      Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] (⇑f) := Iff.rfl

lemma localFunctionsOn_mono {Λ₁ Λ₂ : Finset S} (h : Λ₁ ⊆ Λ₂) :
    localFunctionsOn S E Λ₁ ≤ localFunctionsOn S E Λ₂ :=
  boundedMeasurable_mono (cylinderEvents_mono (by exact_mod_cast h))

variable (S E)

/-- Georgii (2.20)(a): `𝓛 = ⋃_Λ 𝓛_Λ`, the bounded local observables. -/
def localFunctions : Subalgebra ℝ (lp (fun _ : S → E ↦ ℝ) ∞) :=
  ⨆ Λ : Finset S, localFunctionsOn S E Λ

/-- Georgii (2.20)(b): `𝓛̄`, the uniform closure of `𝓛`. -/
def quasilocalFunctions : Subalgebra ℝ (lp (fun _ : S → E ↦ ℝ) ∞) :=
  (localFunctions S E).topologicalClosure

variable {S E}

lemma directed_localFunctionsOn :
    Directed (· ≤ ·) (localFunctionsOn S E) := by
  classical
  exact fun Λ₁ Λ₂ ↦ ⟨Λ₁ ∪ Λ₂, localFunctionsOn_mono Finset.subset_union_left,
    localFunctionsOn_mono Finset.subset_union_right⟩

/-- The family `𝓛_Λ` is directed, so `𝓛` is their union. -/
lemma mem_localFunctions {f : lp (fun _ : S → E ↦ ℝ) ∞} :
    f ∈ localFunctions S E ↔ ∃ Λ : Finset S, f ∈ localFunctionsOn S E Λ := by
  rw [localFunctions, ← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed directed_localFunctionsOn]
  simp [SetLike.mem_coe]

lemma localFunctions_le_quasilocalFunctions :
    localFunctions S E ≤ quasilocalFunctions S E :=
  Subalgebra.le_topologicalClosure _

/-- Quasilocal observables are measurable. -/
lemma quasilocalFunctions_le_boundedMeasurable :
    quasilocalFunctions S E ≤ boundedMeasurable (MeasurableSpace.pi (X := fun _ : S ↦ E)) := by
  refine topologicalClosure_le_boundedMeasurable ?_
  rw [localFunctions, iSup_le_iff]
  exact fun Λ ↦ boundedMeasurable_mono cylinderEvents_le_pi

lemma measurable_of_mem_quasilocalFunctions {f : lp (fun _ : S → E ↦ ℝ) ∞}
    (hf : f ∈ quasilocalFunctions S E) : Measurable (⇑f) :=
  quasilocalFunctions_le_boundedMeasurable hf


/-! ### Georgii's oscillation criterion (2.21)(1) -/

section Oscillation

/-- Georgii (2.22): the oscillation of `f` under variation of the coordinates outside `Λ`. -/
noncomputable def oscOutside (Λ : Finset S) (f : (S → E) → ℝ) : ℝ≥0∞ :=
  ⨆ ζ : S → E, ⨆ η : S → E, ⨆ _ : ∀ i ∈ Λ, ζ i = η i, ENNReal.ofReal |f ζ - f η|

lemma le_oscOutside {Λ : Finset S} {f : (S → E) → ℝ} {ζ η : S → E}
    (h : ∀ i ∈ Λ, ζ i = η i) : ENNReal.ofReal |f ζ - f η| ≤ oscOutside Λ f := by
  exact le_iSup_of_le ζ (le_iSup_of_le η (le_iSup_of_le h le_rfl))

lemma oscOutside_le {Λ : Finset S} {f : (S → E) → ℝ} {c : ℝ≥0∞}
    (h : ∀ ζ η : S → E, (∀ i ∈ Λ, ζ i = η i) → ENNReal.ofReal |f ζ - f η| ≤ c) :
    oscOutside Λ f ≤ c :=
  iSup_le fun ζ ↦ iSup_le fun η ↦ iSup_le fun hζη ↦ h ζ η hζη

lemma oscOutside_antitone {f : (S → E) → ℝ} : Antitone fun Λ : Finset S ↦ oscOutside Λ f := by
  intro Λ₁ Λ₂ h
  exact oscOutside_le fun ζ η hζη ↦ le_oscOutside (fun i hi ↦ hζη i (h hi))

/-- A function depending only on `Λ` has zero oscillation outside `Λ`. -/
lemma oscOutside_eq_zero_of_dependsOn {Λ : Finset S} {f : (S → E) → ℝ}
    (hf : DependsOn f (Λ : Set S)) : oscOutside Λ f = 0 := by
  refine le_antisymm (oscOutside_le fun ζ η hζη ↦ ?_) bot_le
  simp [hf (fun i hi ↦ hζη i (by exact_mod_cast hi))]


end Oscillation

section Criterion

variable {S E : Type*} [MeasurableSpace E]

/-- Values of an `ℓ^∞` element are bounded by its norm. -/
lemma apply_le_norm {S E : Type*} (g : lp (fun _ : S → E ↦ ℝ) ∞) (x : S → E) :
    |(g : (S → E) → ℝ) x| ≤ ‖g‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero g x

/-- Georgii (2.21)(1), forward direction. -/
theorem tendsto_oscOutside_of_mem_quasilocalFunctions {f : lp (fun _ : S → E ↦ ℝ) ∞}
    (hf : f ∈ quasilocalFunctions S E) :
    Tendsto (fun Λ : Finset S ↦ oscOutside Λ (⇑f)) atTop (𝓝 0) := by
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ Λ : Finset S in atTop,
      oscOutside Λ (⇑f) ≤ ENNReal.ofReal (2 * δ) := by
    intro δ hδ
    obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hf δ hδ
    obtain ⟨Λ₀, hΛ₀⟩ := mem_localFunctions.1 hg
    have hdep : DependsOn (⇑g) (Λ₀ : Set S) :=
      (mem_localFunctionsOn.1 hΛ₀).dependsOn_of_cylinderEvents
    filter_upwards [eventually_ge_atTop Λ₀] with Λ hΛ
    refine oscOutside_le fun ζ η hζη ↦ ?_
    have hζη₀ : ∀ i ∈ (Λ₀ : Set S), ζ i = η i := fun i hi ↦ hζη i (hΛ (by exact_mod_cast hi))
    have hgeq : (g : (S → E) → ℝ) ζ = (g : (S → E) → ℝ) η := hdep hζη₀
    have hbound : ∀ x : S → E, |(f : (S → E) → ℝ) x - (g : (S → E) → ℝ) x| ≤ δ := by
      intro x
      have h1 : |(f : (S → E) → ℝ) x - (g : (S → E) → ℝ) x| ≤ ‖f - g‖ := by
        have := apply_le_norm (f - g) x
        rwa [lp.coeFn_sub, Pi.sub_apply] at this
      have h2 : ‖f - g‖ < δ := by rwa [← dist_eq_norm]
      exact h1.trans h2.le
    have : |(f : (S → E) → ℝ) ζ - (f : (S → E) → ℝ) η| ≤ 2 * δ := by
      calc |(f : (S → E) → ℝ) ζ - (f : (S → E) → ℝ) η|
          = |((f : (S → E) → ℝ) ζ - (g : (S → E) → ℝ) ζ)
              + (((g : (S → E) → ℝ) η) - (f : (S → E) → ℝ) η)| := by rw [hgeq]; ring_nf
        _ ≤ |(f : (S → E) → ℝ) ζ - (g : (S → E) → ℝ) ζ|
              + |((g : (S → E) → ℝ) η) - (f : (S → E) → ℝ) η| := abs_add_le _ _
        _ ≤ δ + δ := by
            gcongr
            · exact hbound ζ
            · rw [abs_sub_comm]; exact hbound η
        _ = 2 * δ := by ring
    exact ENNReal.ofReal_le_ofReal this
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact (key 1 one_pos).mono fun Λ h ↦ le_top
  · have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    refine (key (ε.toReal / 2) (by positivity)).mono fun Λ h ↦ ?_
    rwa [show 2 * (ε.toReal / 2) = ε.toReal by ring, ENNReal.ofReal_toReal hεtop] at h


/-- Georgii (2.21)(1), reverse direction. -/
theorem mem_quasilocalFunctions_of_tendsto_oscOutside [Nonempty E]
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hmeas : Measurable (⇑f))
    (hosc : Tendsto (fun Λ : Finset S ↦ oscOutside Λ (⇑f)) atTop (𝓝 0)) :
    f ∈ quasilocalFunctions S E := by
  classical
  set η₀ : S → E := fun _ ↦ Classical.arbitrary E with hη₀
  set T : Finset S → (S → E) → (S → E) := fun Λ ω i ↦ if i ∈ Λ then ω i else η₀ i with hT
  have hTagree : ∀ (Λ : Finset S) (ω : S → E), ∀ i ∈ Λ, T Λ ω i = ω i := by
    intro Λ ω i hi; simp [hT, hi]
  have hTdep : ∀ Λ : Finset S, DependsOn (T Λ) (Λ : Set S) := by
    intro Λ ω ω' h
    funext i
    by_cases hi : i ∈ Λ
    · simp [hT, hi, h i (by exact_mod_cast hi)]
    · simp [hT, hi]
  have hTmeas : ∀ Λ : Finset S, Measurable (T Λ) := by
    intro Λ
    refine measurable_pi_lambda _ fun i ↦ ?_
    by_cases hi : i ∈ Λ
    · simpa [hT, hi] using measurable_pi_apply (X := fun _ : S ↦ E) i
    · simp only [hT, hi, if_false]
      exact measurable_const
  have hgmem : ∀ Λ : Finset S, ((⇑f) ∘ T Λ) ∈ lp (fun _ : S → E ↦ ℝ) ∞ := by
    intro Λ
    refine memℓp_infty ⟨‖f‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact apply_le_norm f (T Λ x)
  set G : Finset S → lp (fun _ : S → E ↦ ℝ) ∞ := fun Λ ↦ ⟨(⇑f) ∘ T Λ, hgmem Λ⟩ with hG
  have hGmem : ∀ Λ : Finset S, G Λ ∈ localFunctions S E := by
    intro Λ
    refine mem_localFunctions.2 ⟨Λ, ?_⟩
    exact Measurable.cylinderEvents_of_dependsOn (hmeas.comp (hTmeas Λ))
      (DependsOn.comp (⇑f) (hTdep Λ))
  have hbound : ∀ (Λ : Finset S) (δ : ℝ), 0 ≤ δ →
      oscOutside Λ (⇑f) ≤ ENNReal.ofReal δ → ‖f - G Λ‖ ≤ δ := by
    intro Λ δ hδ hle
    refine lp.norm_le_of_forall_le hδ fun x ↦ ?_
    rw [lp.coeFn_sub, Pi.sub_apply]
    have h1 : ENNReal.ofReal |(f : (S → E) → ℝ) x - (f : (S → E) → ℝ) (T Λ x)|
        ≤ ENNReal.ofReal δ :=
      le_trans (le_oscOutside (f := (⇑f)) fun i hi ↦ (hTagree Λ x i hi).symm) hle
    have := (ENNReal.ofReal_le_ofReal_iff hδ).1 h1
    simpa [hG, Real.norm_eq_abs] using this
  have htend : Tendsto G atTop (𝓝 f) := by
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    have hεpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := by
      simpa using ENNReal.ofReal_pos.2 (by positivity)
    filter_upwards [(ENNReal.tendsto_nhds_zero.1 hosc) _ hεpos] with Λ hΛ
    have := hbound Λ (ε / 2) (by positivity) hΛ
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    exact lt_of_le_of_lt this (by linarith)
  exact mem_closure_of_tendsto htend (.of_forall fun Λ ↦ hGmem Λ)

/-- **Georgii, Remark (2.21)(1).** -/
theorem mem_quasilocalFunctions_iff [Nonempty E] {f : lp (fun _ : S → E ↦ ℝ) ∞} :
    f ∈ quasilocalFunctions S E ↔
      Measurable (⇑f) ∧ Tendsto (fun Λ : Finset S ↦ oscOutside Λ (⇑f)) atTop (𝓝 0) :=
  ⟨fun h ↦ ⟨measurable_of_mem_quasilocalFunctions h,
      tendsto_oscOutside_of_mem_quasilocalFunctions h⟩,
    fun h ↦ mem_quasilocalFunctions_of_tendsto_oscOutside h.1 h.2⟩


end Criterion

end GibbsMeasure
