import Comparator.Defs

/-!
# Mathlib-only vocabulary for the de Finetti comparator challenge

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Examples (7.16), (7.17) and (7.31),
spelled out from first principles.

## Main definitions

* `finitaryPerm`: the group of permutations of `ℕ` moving finitely many indices.
* `permute σ ω = ω ∘ σ`: the action on configurations.
* `IsExchangeable μ`: invariance of `μ` under every finitary permutation, Georgii (7.16).
* `IsSymmetric A`: the symmetric events, Georgii's σ-algebra `𝓘`.
* `iidMix m`: the mixture `∫ λ^ℕ m(dλ)` of i.i.d. product measures, as `Measure.bind`.

## Main statements

* `isExchangeable_infinitePi`, `measurableSet_isSymmetric`, `iidMix_dirac`: the definitions are
  non-vacuous — product measures are exchangeable, the symmetric events are events, and the
  mixture of a Dirac weight is the corresponding product measure.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge
namespace DeFinetti

variable {E : Type*} [MeasurableSpace E]

/-- The permutations of `ℕ` moving only finitely many indices. -/
def finitaryPerm : Set (Equiv.Perm ℕ) := {σ | ∃ n, ∀ i, n ≤ i → σ i = i}

/-- The action of a permutation on a configuration: `permute σ ω = ω ∘ σ`. -/
def permute (σ : Equiv.Perm ℕ) (ω : Config ℕ E) : Config ℕ E := fun i ↦ ω (σ i)

lemma measurable_permute (σ : Equiv.Perm ℕ) : Measurable (permute (E := E) σ) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

/-- **Georgii, Example (7.16)**: a measure on `E^ℕ` is *exchangeable* if it is invariant under
every finitary permutation of the coordinates. -/
def IsExchangeable (μ : Measure (Config ℕ E)) : Prop :=
  ∀ σ ∈ finitaryPerm, μ.map (permute σ) = μ

/-- A *symmetric* event: measurable and invariant under every finitary permutation.  These form
Georgii's σ-algebra `𝓘` of Example (7.16). -/
def IsSymmetric (A : Set (Config ℕ E)) : Prop :=
  MeasurableSet A ∧ ∀ σ ∈ finitaryPerm, permute σ ⁻¹' A = A

/-- The mixture `∫ λ^ℕ m(dλ)` of i.i.d. product measures under a weight `m` on measures. -/
def iidMix (m : Measure (Measure E)) : Measure (Config ℕ E) :=
  m.bind fun lam ↦ Measure.infinitePi fun _ : ℕ ↦ lam

/-! ### Non-vacuity -/

lemma prodAtom_mem_finitaryPerm {n : ℕ} {σ : Equiv.Perm ℕ} (h : ∀ i, n ≤ i → σ i = i) :
    σ ∈ finitaryPerm := ⟨n, h⟩

/-- Product measures are exchangeable. -/
lemma isExchangeable_infinitePi (ν : Measure E) [IsProbabilityMeasure ν] :
    IsExchangeable (Measure.infinitePi fun _ : ℕ ↦ ν) := by
  intro σ hσ
  refine (Measure.eq_infinitePi _ fun s t ht ↦ ?_).trans rfl
  classical
  rw [Measure.map_apply (measurable_permute σ)
    (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i)]
  have hpre : permute σ ⁻¹' (s : Set ℕ).pi t
      = (s.image σ : Set ℕ).pi fun j ↦ t (σ.symm j) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, permute, Finset.coe_image, Set.mem_image,
      Finset.mem_coe]
    constructor
    · rintro h j ⟨i, hi, rfl⟩
      simpa using h i hi
    · intro h i hi
      simpa using h (σ i) ⟨i, hi, rfl⟩
  rw [hpre, Measure.infinitePi_pi _ fun j _ ↦ ht (σ.symm j),
    Finset.prod_image fun a _ b _ hab ↦ σ.injective hab]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [Equiv.symm_apply_apply]

/-- The whole space is symmetric, so `IsSymmetric` is non-vacuous. -/
lemma isSymmetric_univ : IsSymmetric (Set.univ : Set (Config ℕ E)) :=
  ⟨MeasurableSet.univ, fun _ _ ↦ Set.preimage_univ⟩

/-- The i.i.d. map `λ ↦ λ^ℕ` is measurable for the Giry σ-algebra, by induction over the square
cylinders. -/
lemma measurable_iid :
    Measurable fun lam : Measure E ↦ Measure.infinitePi fun _ : ℕ ↦ lam := by
  refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
  have hProb : MeasurableSet {lam : Measure E | IsProbabilityMeasure lam} := by
    have h : {lam : Measure E | IsProbabilityMeasure lam}
        = (fun lam : Measure E ↦ lam Set.univ) ⁻¹' {1} := by
      ext lam
      simp [isProbabilityMeasure_iff]
    rw [h]
    exact (measurableSet_singleton 1).preimage (Measure.measurable_coe .univ)
  have hzero : ∀ lam : Measure E, ¬ IsProbabilityMeasure lam →
      Measure.infinitePi (fun _ : ℕ ↦ lam) = 0 := by
    intro lam hlam
    rw [Measure.infinitePi]
    exact dif_neg fun h ↦ hlam (h 0)
  have hbox : ∀ (s : Finset ℕ) (t : ℕ → Set E), (∀ i, MeasurableSet (t i)) →
      Measurable fun lam : Measure E ↦ Measure.infinitePi (fun _ : ℕ ↦ lam) ((s : Set ℕ).pi t) :=
    by
    intro s t ht
    have hval : (fun lam : Measure E ↦ Measure.infinitePi (fun _ : ℕ ↦ lam) ((s : Set ℕ).pi t))
        = {lam : Measure E | IsProbabilityMeasure lam}.indicator
            fun lam ↦ ∏ i ∈ s, lam (t i) := by
      funext lam
      by_cases hlam : IsProbabilityMeasure lam
      · rw [Set.indicator_of_mem (show lam ∈ {lam : Measure E | IsProbabilityMeasure lam}
          from hlam)]
        exact Measure.infinitePi_pi _ fun i _ ↦ ht i
      · rw [Set.indicator_of_notMem (show lam ∉ {lam : Measure E | IsProbabilityMeasure lam}
          from hlam), hzero lam hlam]
        rfl
    rw [hval]
    exact Measurable.indicator
      (Finset.measurable_prod _ fun i _ ↦ Measure.measurable_coe (ht i)) hProb
  induction B, hB using MeasurableSpace.induction_on_inter
    (m := MeasurableSpace.pi)
    (s := squareCylinders fun _ : ℕ ↦ {s : Set E | MeasurableSet s})
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ ↦ fun _ h₁ _ h₂ _ ↦ h₁.inter h₂) fun _ ↦ .univ) with
  | empty => simp only [measure_empty]; exact measurable_const
  | basic B hBmem =>
      obtain ⟨s, t, ht, rfl⟩ := hBmem
      exact hbox s t fun i ↦ ht i trivial
  | compl B hBm hB =>
      have hval : (fun lam : Measure E ↦ Measure.infinitePi (fun _ : ℕ ↦ lam) Bᶜ)
          = fun lam ↦ Measure.infinitePi (fun _ : ℕ ↦ lam) Set.univ
              - Measure.infinitePi (fun _ : ℕ ↦ lam) B := by
        funext lam
        by_cases hlam : IsProbabilityMeasure lam
        · have : IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ ↦ lam) := inferInstance
          rw [measure_compl hBm (measure_ne_top _ _)]
        · rw [hzero lam hlam]
          simp
      have huniv : Measurable fun lam : Measure E ↦
          Measure.infinitePi (fun _ : ℕ ↦ lam) Set.univ := by
        have h : (Set.univ : Set (Config ℕ E))
            = (↑(∅ : Finset ℕ) : Set ℕ).pi fun _ ↦ Set.univ := by simp
        rw [h]
        exact hbox ∅ (fun _ ↦ Set.univ) fun _ ↦ .univ
      rw [hval]
      exact huniv.sub hB
  | iUnion f hdisj hfm hf =>
      have hval : (fun lam : Measure E ↦ Measure.infinitePi (fun _ : ℕ ↦ lam) (⋃ n, f n))
          = fun lam ↦ ∑' n, Measure.infinitePi (fun _ : ℕ ↦ lam) (f n) := by
        funext lam
        exact measure_iUnion hdisj hfm
      rw [hval]
      exact Measurable.tsum hf

/-- The mixture of a Dirac weight is the corresponding i.i.d. product measure. -/
lemma iidMix_dirac (ν : Measure E) :
    iidMix (Measure.dirac ν) = Measure.infinitePi fun _ : ℕ ↦ ν := by
  rw [iidMix, Measure.dirac_bind measurable_iid]

end DeFinetti
end GibbsChallenge

end
