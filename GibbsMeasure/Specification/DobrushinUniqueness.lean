/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Dobrushin

/-!
# Dobrushin's condition of weak dependence and the comparison theorem

Georgii, *Gibbs Measures and Phase Transitions*, Sections 8.1–8.2.

## Main declarations

* `MeasureTheory.GibbsMeasure.Dobrushin.proj`: Georgii (8.4), the single-site distribution
  `γ_i^0(·|ω)`; `act`: the single-site action `γ_i f` on bounded observables.
* `MeasureTheory.GibbsMeasure.Dobrushin.oscAt_act_le`: the single-site estimate
  `δ_j(γ_i f) ≤ δ_j(f) + C_{ij}(γ) δ_i(f)` from the proof of (8.18).
* `MeasureTheory.GibbsMeasure.Dobrushin.IsEstimate`: Georgii (8.16).
* `MeasureTheory.GibbsMeasure.Dobrushin.IsEstimate.step`: Georgii's key Lemma (8.18).
* `MeasureTheory.GibbsMeasure.Dobrushin.comparison`: Georgii's comparison Theorem (8.20).
* `MeasureTheory.GibbsMeasure.Dobrushin.eq_of_isDobrushin`,
  `subsingleton_GP_of_isDobrushin`, `existsUnique_mem_GP_of_isDobrushin`: Georgii's uniqueness
  Theorem (8.7).
* `MeasureTheory.GibbsMeasure.Dobrushin.condSpec`: Georgii's Lemma (8.22), the specification
  `γ^{(V,ω)}` obtained by conditioning on `ω` outside `V`.
* `MeasureTheory.GibbsMeasure.Dobrushin.measure_le_add_interdepTail`,
  `tendsto_interdepTail`: the Cauchy estimate of Georgii (8.23), step 1.
* `MeasureTheory.GibbsMeasure.Dobrushin.GP_nonempty_of_isDobrushin`,
  `existsUnique_mem_GP_of_isDobrushin_of_standardBorel`: the existence half of Theorem (8.7),
  proved as Georgii (8.23).

The underlying notions — `unifDist` (8.1), `interdep` (8.5), `IsDobrushin` (8.6), `osc`,
`oscAt` (8.14) and the potential criterion (8.8) — live in
`GibbsMeasure.Specification.Dobrushin`.
-/

@[expose] public section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal NNReal Topology

noncomputable section



open Filter Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.GibbsMeasure.Dobrushin

variable {S E : Type*} [MeasurableSpace E]

/-! ### The uniform distance (Georgii (8.1)) -/

section UnifDist

variable {α₁ α₂ : Measure E}

/-- `α₁ A ≤ α₂ A + ‖α₁ - α₂‖` for measurable `A`. -/
lemma measure_le_add_unifDist {A : Set E} (hA : MeasurableSet A) :
    α₁ A ≤ α₂ A + unifDist α₁ α₂ := tsub_le_iff_left.1 (le_unifDist hA)

private lemma ennreal_sub_aux {a c : ℝ≥0∞} (ha : a ≤ 1) :
    a - c = (1 - c) - (1 - a) := by
  rcases le_total a c with h | h
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (tsub_le_tsub_left h 1)]
  · have h1 : (1 : ℝ≥0∞) - c = (1 - a) + (a - c) := (tsub_add_tsub_cancel ha h).symm
    rw [h1, ENNReal.add_sub_cancel_left (by finiteness)]

end UnifDist


/-! ### Oscillations (Georgii (8.2), (8.14), (8.15)) -/

section Osc

omit [MeasurableSpace E]

variable {f g : (S → E) → ℝ} {j : S} {c : ℝ≥0∞}


lemma osc_le_ofReal_two_mul {C : ℝ} (hC : ∀ ζ, |f ζ| ≤ C) : osc f ≤ ENNReal.ofReal (2 * C) :=
  osc_le fun ζ η ↦ ENNReal.ofReal_le_ofReal <| by
    calc |f ζ - f η| ≤ |f ζ| + |f η| := abs_sub _ _
      _ ≤ C + C := add_le_add (hC ζ) (hC η)
      _ = 2 * C := by ring

lemma osc_ne_top_of_bounded {C : ℝ} (hC : ∀ ζ, |f ζ| ≤ C) : osc f ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (osc_le_ofReal_two_mul hC)

lemma oscAt_ne_top_of_bounded {C : ℝ} (hC : ∀ ζ, |f ζ| ≤ C) : oscAt f j ≠ ⊤ :=
  ne_top_of_le_ne_top (osc_ne_top_of_bounded hC) oscAt_le_osc

lemma osc_add_le : osc (f + g) ≤ osc f + osc g := by
  refine osc_le fun ζ η ↦ ?_
  calc ENNReal.ofReal |(f + g) ζ - (f + g) η|
      ≤ ENNReal.ofReal (|f ζ - f η| + |g ζ - g η|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simpa [Pi.add_apply, add_sub_add_comm] using abs_add_le (f ζ - f η) (g ζ - g η)
    _ = ENNReal.ofReal |f ζ - f η| + ENNReal.ofReal |g ζ - g η| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ osc f + osc g := add_le_add (le_osc _ _ _) (le_osc _ _ _)

lemma oscAt_add_le : oscAt (f + g) j ≤ oscAt f j + oscAt g j := by
  refine oscAt_le fun ζ η h ↦ ?_
  calc ENNReal.ofReal |(f + g) ζ - (f + g) η|
      ≤ ENNReal.ofReal (|f ζ - f η| + |g ζ - g η|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simpa [Pi.add_apply, add_sub_add_comm] using abs_add_le (f ζ - f η) (g ζ - g η)
    _ = ENNReal.ofReal |f ζ - f η| + ENNReal.ofReal |g ζ - g η| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ oscAt f j + oscAt g j := add_le_add (le_oscAt h) (le_oscAt h)

/-- The combinatorial heart: two configurations differing only on a finite set `D` are compared by
telescoping over `D`. Georgii (8.15). -/
lemma ofReal_abs_sub_le_sum_oscAt (f : (S → E) → ℝ) (D : Finset S) :
    ∀ ζ η : S → E, (∀ k, k ∉ D → ζ k = η k) →
      ENNReal.ofReal |f ζ - f η| ≤ ∑ j ∈ D, oscAt f j := by
  classical
  induction D using Finset.induction_on with
  | empty => intro ζ η h; rw [funext fun k ↦ h k (by simp)]; simp
  | insert a D ha ih =>
      intro ζ η h
      set ξ : S → E := Function.update ζ a (η a) with hξ
      have h1 : ENNReal.ofReal |f ζ - f ξ| ≤ oscAt f a := by
        refine le_oscAt fun k hk ↦ ?_
        simp [hξ, Function.update_of_ne hk]
      have h2 : ENNReal.ofReal |f ξ - f η| ≤ ∑ j ∈ D, oscAt f j := by
        refine ih ξ η fun k hk ↦ ?_
        by_cases hka : k = a
        · subst hka; simp [hξ]
        · rw [hξ, Function.update_of_ne hka]
          exact h k (by simp [hka, hk])
      have htri : ENNReal.ofReal |f ζ - f η|
          ≤ ENNReal.ofReal |f ζ - f ξ| + ENNReal.ofReal |f ξ - f η| := by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
      calc ENNReal.ofReal |f ζ - f η| ≤ oscAt f a + ∑ j ∈ D, oscAt f j :=
            htri.trans (add_le_add h1 h2)
        _ = ∑ j ∈ insert a D, oscAt f j := (Finset.sum_insert ha).symm

/-- Georgii (8.15) for local functions: the global oscillation is dominated by the sum of the
single-site oscillations. -/
lemma osc_le_sum_oscAt_of_dependsOn {Λ : Finset S} (hf : DependsOn f (Λ : Set S)) :
    osc f ≤ ∑ j ∈ Λ, oscAt f j := by
  classical
  refine osc_le fun ζ η ↦ ?_
  set ξ : S → E := fun k ↦ if k ∈ Λ then ζ k else η k with hξ
  have hfζ : f ζ = f ξ := hf fun k hk ↦ by simp [hξ, Finset.mem_coe.1 hk]
  rw [hfζ]
  exact ofReal_abs_sub_le_sum_oscAt f Λ ξ η fun k hk ↦ by simp [hξ, hk]

lemma osc_le_tsum_oscAt_of_dependsOn {Λ : Finset S} (hf : DependsOn f (Λ : Set S)) :
    osc f ≤ ∑' j, oscAt f j :=
  (osc_le_sum_oscAt_of_dependsOn hf).trans (ENNReal.sum_le_tsum Λ)

end Osc


/-! ### Georgii (8.1): the uniform distance controls differences of integrals -/

section Comparison

variable {α₁ α₂ : Measure E} {f : E → ℝ}

private lemma ofReal_integral_sub_le_aux [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂]
    (hf : Measurable f) {C D : ℝ} (hC : ∀ x, |f x| ≤ C) (hD : ∀ x y, f x - f y ≤ D) :
    ENNReal.ofReal (∫ x, f x ∂α₁ - ∫ x, f x ∂α₂) ≤ unifDist α₁ α₂ * ENNReal.ofReal D := by
  set u := unifDist α₁ α₂ with hu
  have hne : Nonempty E := by
    rcases isEmpty_or_nonempty E with h | h
    · exact absurd (measure_univ (μ := α₁)) (by simp [Set.univ_eq_empty_iff.2 h])
    · exact h
  have hD0 : 0 ≤ D := by simpa using hD hne.some hne.some
  have hbdd : BddBelow (Set.range f) := ⟨-C, by
    rintro _ ⟨x, rfl⟩; linarith [(abs_le.1 (hC x)).1]⟩
  set m : ℝ := ⨅ x, f x with hm
  have hmle : ∀ x, m ≤ f x := fun x ↦ ciInf_le hbdd x
  set g : E → ℝ := fun x ↦ f x - m with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦ sub_nonneg.2 (hmle x)
  have hgD : ∀ x, g x ≤ D := fun x ↦ by
    have h : f x - D ≤ m := le_ciInf fun y ↦ by linarith [hD x y]
    simp only [hg]; linarith
  have hgmeas : Measurable g := hf.sub measurable_const
  have hgint : ∀ (α : Measure E), IsFiniteMeasure α → Integrable g α := by
    intro α _
    exact ⟨hgmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := D)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgD x)⟩
  have hfint : ∀ (α : Measure E), IsFiniteMeasure α → Integrable f α := by
    intro α _
    exact ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C)
      (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)⟩
  have hgf : ∀ (α : Measure E), IsProbabilityMeasure α → ∫ x, g x ∂α = ∫ x, f x ∂α - m := by
    intro α hα
    simp only [hg]
    have := hα
    rw [integral_sub (hfint α inferInstance) (integrable_const m), integral_const]
    simp
  -- Layer cake
  have hmeasA : ∀ t : ℝ, MeasurableSet {x | t < g x} := fun t ↦
    measurableSet_lt measurable_const hgmeas
  have hlayer : ∀ (α : Measure E), ∫⁻ x, ENNReal.ofReal (g x) ∂α
      = ∫⁻ t in Set.Ioi (0 : ℝ), α {x | t < g x} := fun α ↦
    lintegral_eq_lintegral_meas_lt α (Filter.Eventually.of_forall hg0) hgmeas.aemeasurable
  have hzero : ∀ (α : Measure E), ∫⁻ t in Set.Ioi D, α {x | t < g x} = 0 := by
    intro α
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ (0 : ℝ≥0∞)) ?_]
    · simp
    · intro t ht
      have hemp : {x | t < g x} = (∅ : Set E) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact (hgD x).trans ht.le
      simp [hemp]
  have hsplit : ∀ (α : Measure E), ∫⁻ t in Set.Ioi (0 : ℝ), α {x | t < g x}
      = ∫⁻ t in Set.Ioc (0 : ℝ) D, α {x | t < g x} := by
    intro α
    rw [← Set.Ioc_union_Ioi_eq_Ioi hD0,
      lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl), hzero α, add_zero]
  have hcmp : ∫⁻ t in Set.Ioc (0 : ℝ) D, α₁ {x | t < g x}
      ≤ (∫⁻ t in Set.Ioc (0 : ℝ) D, α₂ {x | t < g x}) + u * ENNReal.ofReal D := by
    calc ∫⁻ t in Set.Ioc (0 : ℝ) D, α₁ {x | t < g x}
        ≤ ∫⁻ t in Set.Ioc (0 : ℝ) D, (α₂ {x | t < g x} + u) :=
          lintegral_mono fun t ↦ measure_le_add_unifDist (hmeasA t)
      _ = (∫⁻ t in Set.Ioc (0 : ℝ) D, α₂ {x | t < g x}) + u * ENNReal.ofReal D := by
          rw [lintegral_add_right _ measurable_const, lintegral_const,
            Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_comm]
  have hmain : ∫⁻ x, ENNReal.ofReal (g x) ∂α₁
      ≤ (∫⁻ x, ENNReal.ofReal (g x) ∂α₂) + u * ENNReal.ofReal D := by
    rw [hlayer α₁, hlayer α₂, hsplit α₁, hsplit α₂]; exact hcmp
  have h1 : ENNReal.ofReal (∫ x, g x ∂α₁) = ∫⁻ x, ENNReal.ofReal (g x) ∂α₁ :=
    ofReal_integral_eq_lintegral_ofReal (hgint α₁ inferInstance)
      (Filter.Eventually.of_forall hg0)
  have h2 : ENNReal.ofReal (∫ x, g x ∂α₂) = ∫⁻ x, ENNReal.ofReal (g x) ∂α₂ :=
    ofReal_integral_eq_lintegral_ofReal (hgint α₂ inferInstance)
      (Filter.Eventually.of_forall hg0)
  have hge : (0 : ℝ) ≤ ∫ x, g x ∂α₂ := integral_nonneg hg0
  have hfg : ∫ x, f x ∂α₁ - ∫ x, f x ∂α₂ = ∫ x, g x ∂α₁ - ∫ x, g x ∂α₂ := by
    rw [hgf α₁ inferInstance, hgf α₂ inferInstance]; ring
  rw [hfg, ENNReal.ofReal_sub _ hge, tsub_le_iff_left, h1, h2]
  exact hmain

/-- Georgii (8.1): `|α₁(f) - α₂(f)| ≤ ‖α₁ - α₂‖ δ(f)` for bounded measurable `f`. -/
lemma ofReal_abs_integral_sub_leD [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂]
    (hf : Measurable f) {C D : ℝ} (hC : ∀ x, |f x| ≤ C) (hD : ∀ x y, |f x - f y| ≤ D) :
    ENNReal.ofReal |∫ x, f x ∂α₁ - ∫ x, f x ∂α₂| ≤ unifDist α₁ α₂ * ENNReal.ofReal D := by
  rcases abs_cases (∫ x, f x ∂α₁ - ∫ x, f x ∂α₂) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]
    exact ofReal_integral_sub_le_aux hf hC fun x y ↦ (le_abs_self _).trans (hD x y)
  · rw [he, neg_sub]
    rw [unifDist_comm]
    exact ofReal_integral_sub_le_aux hf hC fun x y ↦ (le_abs_self _).trans (hD x y)

end Comparison


/-! ### Georgii (8.4): the single-site kernel and its `σ_i`-projection -/

section Proj

/-- Georgii (8.4): `γ_i^0(·|ω)`, the `σ_i`-projection of the single-site kernel `γ_i(·|ω)`. -/
noncomputable def proj (γ : Specification S E) (i : S) (ω : S → E) : Measure E :=
  (γ {i} ω).map (fun σ ↦ σ i)

instance instIsProbabilityMeasureProj (γ : Specification S E) (i : S) (ω : S → E) :
    IsProbabilityMeasure (proj γ i ω) :=
  Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable

lemma interdep_eq (γ : Specification S E) (i j : S) :
    interdep γ i j =
      ⨆ (ζ : S → E) (η : S → E) (_ : ∀ k, k ≠ j → ζ k = η k),
        unifDist (proj γ i ζ) (proj γ i η) := rfl

lemma unifDist_proj_le_interdep (γ : Specification S E) (i j : S) {ζ η : S → E}
    (h : ∀ k, k ≠ j → ζ k = η k) : unifDist (proj γ i ζ) (proj γ i η) ≤ interdep γ i j :=
  le_iSup_of_le ζ (le_iSup_of_le η (le_iSup_of_le h le_rfl))

variable [DecidableEq S]

lemma measurable_updateAt (i : S) (ω : S → E) :
    Measurable (fun σ : S → E ↦ Function.update ω i (σ i)) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  by_cases hk : k = i
  · subst hk; simpa using measurable_pi_apply k
  · simp [Function.update_of_ne hk]

lemma measurable_updateOf (i : S) (ω : S → E) :
    Measurable (fun x : E ↦ Function.update ω i x) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  by_cases hk : k = i
  · subst hk; simpa using measurable_id'
  · simp [Function.update_of_ne hk]

/-- Properness of `γ_{\{i\}}` says that resetting every site but `i` to the boundary condition
leaves `γ_i(·|ω)` unchanged; this is the measure-theoretic content of Georgii's statement, before
(8.4), that `γ_i` is determined by its `σ_i`-projection `γ_i^0`. -/
lemma map_updateAt_eq (γ : Specification S E) (i : S) (ω : S → E) :
    (γ {i} ω).map (fun σ ↦ Function.update ω i (σ i)) = γ {i} ω := by
  classical
  have hT : Measurable (fun σ : S → E ↦ Function.update ω i (σ i)) := measurable_updateAt i ω
  have : IsProbabilityMeasure ((γ {i} ω).map (fun σ ↦ Function.update ω i (σ i))) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have hprop : Specification.IsProper γ := γ.isProper
  refine ext_of_generate_finite (squareCylindersMeas S E)
      (generateFrom_squareCylindersMeas S E) (isPiSystem_squareCylindersMeas S E) ?_ ?_
  · rintro C ⟨J, t, ht, rfl⟩
    have htm : ∀ j, MeasurableSet (t j) := fun j ↦ Set.mem_univ_pi.1 ht j
    set B : Set (S → E) := ((J.erase i : Finset S) : Set S).pi t with hBdef
    set A' : Set (S → E) := if i ∈ J then (fun σ : S → E ↦ σ i) ⁻¹' (t i) else Set.univ with hA'def
    have hmemB : ∀ σ : S → E, σ ∈ B ↔ ∀ j ∈ J, j ≠ i → σ j ∈ t j := by
      intro σ
      simp only [hBdef, Set.mem_pi, Finset.mem_coe, Finset.mem_erase]
      exact ⟨fun h j hj hji ↦ h j ⟨hji, hj⟩, fun h j hj ↦ h j hj.2 hj.1⟩
    have hmemJ : ∀ σ : S → E, σ ∈ (J : Set S).pi t ↔ ∀ j ∈ J, σ j ∈ t j := by
      intro σ; simp only [Set.mem_pi, Finset.mem_coe]
    have hBmeas :
        MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((({i} : Finset S) : Set S)ᶜ)] B := by
      have hBeq : B = ⋂ j ∈ (J.erase i), (fun σ : S → E ↦ σ j) ⁻¹' (t j) := by
        ext σ
        rw [hmemB σ]
        simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_erase]
        exact ⟨fun h j hj ↦ h j hj.2 hj.1, fun h j hj hji ↦ h j ⟨hji, hj⟩⟩
      rw [hBeq]
      refine Finset.measurableSet_biInter _ fun j hj ↦ ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      exact (htm j).preimage
        (measurable_cylinderEvent_apply (i := j) (X := fun _ : S ↦ E) (by simp [hji]))
    have hA'meas : MeasurableSet A' := by
      by_cases hiJ : i ∈ J
      · simp only [hA'def, hiJ, ite_true]
        exact (htm i).preimage (measurable_pi_apply i)
      · simp [hA'def, hiJ]
    have hsplit : ((J : Set S).pi t) = A' ∩ B := by
      ext σ
      rw [Set.mem_inter_iff, hmemJ, hmemB]
      by_cases hiJ : i ∈ J
      · simp only [hA'def, hiJ, ite_true, Set.mem_preimage]
        refine ⟨fun h ↦ ⟨h i hiJ, fun j hj _ ↦ h j hj⟩, fun h j hj ↦ ?_⟩
        by_cases hji : j = i
        · subst hji; exact h.1
        · exact h.2 j hj hji
      · simp only [hA'def, hiJ, ite_false, Set.mem_univ, true_and]
        exact ⟨fun h j hj _ ↦ h j hj,
          fun h j hj ↦ h j hj (by rintro rfl; exact hiJ hj)⟩
    have hmemT : ∀ σ : S → E,
        (Function.update ω i (σ i)) ∈ (J : Set S).pi t ↔ (σ ∈ A' ∧ ω ∈ B) := by
      intro σ
      rw [hmemJ, hmemB]
      by_cases hiJ : i ∈ J
      · simp only [hA'def, hiJ, ite_true, Set.mem_preimage]
        constructor
        · intro h
          exact ⟨by simpa using h i hiJ,
            fun j hj hji ↦ by simpa [Function.update_of_ne hji] using h j hj⟩
        · rintro ⟨h1, h2⟩ j hj
          by_cases hji : j = i
          · subst hji; simpa using h1
          · rw [Function.update_of_ne hji]; exact h2 j hj hji
      · simp only [hA'def, hiJ, ite_false, Set.mem_univ, true_and]
        constructor
        · intro h j hj hji
          simpa [Function.update_of_ne hji] using h j hj
        · intro h j hj
          have hji : j ≠ i := by rintro rfl; exact hiJ hj
          rw [Function.update_of_ne hji]; exact h j hj hji
    have hpre : (fun σ : S → E ↦ Function.update ω i (σ i)) ⁻¹' ((J : Set S).pi t)
        = if ω ∈ B then A' else (∅ : Set (S → E)) := by
      ext σ
      by_cases hωB : ω ∈ B <;> simp [Set.mem_preimage, hmemT σ, hωB]
    rw [Measure.map_apply hT (measurableSet_finset_pi J t htm), hpre, hsplit,
      hprop.inter_eq_indicator_mul ({i} : Finset S) hA'meas hBmeas ω]
    by_cases hωB : ω ∈ B
    · simp [hωB, Set.indicator_of_mem]
    · simp [hωB, Set.indicator_of_notMem]
  · rw [Measure.map_apply hT MeasurableSet.univ]
    simp

/-- Georgii's identity `γ_i f(ω) = γ_i^0(f_{i,ω}|ω)`. -/
lemma integral_eq_integral_proj (γ : Specification S E) (i : S) (ω : S → E)
    {f : (S → E) → ℝ} (hf : Measurable f) :
    ∫ σ, f σ ∂(γ {i} ω) = ∫ x, f (Function.update ω i x) ∂(proj γ i ω) := by
  classical
  have hT : Measurable (fun σ : S → E ↦ Function.update ω i (σ i)) := measurable_updateAt i ω
  have hU : Measurable (fun x : E ↦ Function.update ω i x) := measurable_updateOf i ω
  conv_lhs => rw [← map_updateAt_eq γ i ω]
  rw [integral_map hT.aemeasurable hf.aestronglyMeasurable, proj,
    integral_map (measurable_pi_apply i).aemeasurable (hf.comp hU).aestronglyMeasurable]

end Proj


/-! ### The single-site estimates feeding Georgii (8.18) -/

section SingleSite

variable {γ γ' : Specification S E}

/-- `γ_i f`, Georgii's single-site action on bounded measurable observables. -/
noncomputable def act (γ : Specification S E) (i : S) (f : (S → E) → ℝ) : (S → E) → ℝ :=
  fun ω ↦ ∫ σ, f σ ∂(γ {i} ω)

lemma measurable_act_cylinderEvents {f : (S → E) → ℝ} (hf : Measurable f) (i : S) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) ((({i} : Finset S) : Set S)ᶜ)] (act γ i f) :=
  (StronglyMeasurable.integral_kernel (κ := γ {i}) hf.stronglyMeasurable).measurable

lemma measurable_act {f : (S → E) → ℝ} (hf : Measurable f) (i : S) : Measurable (act γ i f) :=
  (measurable_act_cylinderEvents (γ := γ) hf i).mono cylinderEvents_le_pi le_rfl

lemma abs_act_le {f : (S → E) → ℝ} {C : ℝ} (hC : ∀ σ, |f σ| ≤ C) (i : S) (ω : S → E) :
    |act γ i f ω| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := γ {i} ω) (C := C)
    (Filter.Eventually.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hC σ)
  simpa [act, Real.norm_eq_abs] using h

/-- Georgii, proof of (8.18): `δ_i(γ_i f) = 0`. -/
lemma oscAt_act_self {f : (S → E) → ℝ} (hf : Measurable f) (i : S) :
    oscAt (act γ i f) i = 0 :=
  oscAt_eq_zero_of_dependsOn
    ((measurable_act_cylinderEvents (γ := γ) hf i).dependsOn_of_cylinderEvents) (by simp)

private lemma integrable_section [DecidableEq S] {f : (S → E) → ℝ} {C : ℝ} (hf : Measurable f)
    (hC : ∀ σ, |f σ| ≤ C) (i : S) (ξ : S → E) (α : Measure E) [IsProbabilityMeasure α] :
    Integrable (fun x ↦ f (Function.update ξ i x)) α :=
  ⟨(hf.comp (measurable_updateOf i ξ)).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := C)
      (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hC _)⟩

/-- Georgii, proof of (8.18): `δ_j(γ_i f) ≤ δ_j(f) + C_{ij}(γ) δ_i(f)`. -/
theorem oscAt_act_le {f : (S → E) → ℝ} {C : ℝ} (hf : Measurable f) (hC : ∀ σ, |f σ| ≤ C)
    (i j : S) :
    oscAt (act γ i f) j ≤ oscAt f j + interdep γ i j * oscAt f i := by
  classical
  refine oscAt_le fun ζ η hζη ↦ ?_
  set di := (oscAt f i).toReal with hdidef
  set dj := (oscAt f j).toReal with hdjdef
  have hdi : ENNReal.ofReal di = oscAt f i := ENNReal.ofReal_toReal (oscAt_ne_top_of_bounded hC)
  have hdj : ENNReal.ofReal dj = oscAt f j := ENNReal.ofReal_toReal (oscAt_ne_top_of_bounded hC)
  have hsecζη : ∀ x : E, |f (Function.update ζ i x) - f (Function.update η i x)| ≤ dj := by
    intro x
    have h : ENNReal.ofReal |f (Function.update ζ i x) - f (Function.update η i x)| ≤ oscAt f j :=
      le_oscAt fun k hk ↦ by
        by_cases hki : k = i
        · subst hki; simp
        · rw [Function.update_of_ne hki, Function.update_of_ne hki]; exact hζη k hk
    rw [← hdj] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have hsecη : ∀ x y : E, |f (Function.update η i x) - f (Function.update η i y)| ≤ di := by
    intro x y
    have h : ENNReal.ofReal |f (Function.update η i x) - f (Function.update η i y)| ≤ oscAt f i :=
      le_oscAt fun k hk ↦ by rw [Function.update_of_ne hk, Function.update_of_ne hk]
    rw [← hdi] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  rw [act, act, integral_eq_integral_proj γ i ζ hf, integral_eq_integral_proj γ i η hf]
  set A := ∫ x, f (Function.update ζ i x) ∂(proj γ i ζ) with hA
  set B := ∫ x, f (Function.update η i x) ∂(proj γ i ζ) with hB
  set D := ∫ x, f (Function.update η i x) ∂(proj γ i η) with hD
  have step1 : ENNReal.ofReal |A - B| ≤ oscAt f j := by
    have hsub : A - B = ∫ x, (f (Function.update ζ i x) - f (Function.update η i x))
        ∂(proj γ i ζ) := by
      rw [hA, hB, ← integral_sub (integrable_section hf hC i ζ _)
        (integrable_section hf hC i η _)]
    have hbnd : |A - B| ≤ dj := by
      rw [hsub]
      have h := norm_integral_le_of_norm_le_const (μ := proj γ i ζ) (C := dj)
        (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hsecζη x)
      simpa [Real.norm_eq_abs] using h
    rw [← hdj]
    exact ENNReal.ofReal_le_ofReal hbnd
  have step2 : ENNReal.ofReal |B - D| ≤ interdep γ i j * oscAt f i := by
    have h := ofReal_abs_integral_sub_leD (α₁ := proj γ i ζ) (α₂ := proj γ i η)
      (f := fun x ↦ f (Function.update η i x)) (hf.comp (measurable_updateOf i η))
      (C := C) (D := di) (fun x ↦ hC _) hsecη
    rw [hdi] at h
    refine h.trans ?_
    gcongr
    exact unifDist_proj_le_interdep γ i j hζη
  calc ENNReal.ofReal |A - D| ≤ ENNReal.ofReal |A - B| + ENNReal.ofReal |B - D| := by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ ≤ oscAt f j + interdep γ i j * oscAt f i := add_le_add step1 step2

/-- Georgii, proof of (8.18): `|γ_i f(ω) - γ̃_i f(ω)| ≤ ‖γ_i^0(·|ω) - γ̃_i^0(·|ω)‖ δ_i(f)`. -/
theorem ofReal_abs_act_sub_act_le {f : (S → E) → ℝ} {C : ℝ} (hf : Measurable f)
    (hC : ∀ σ, |f σ| ≤ C) (i : S) (ω : S → E) :
    ENNReal.ofReal |act γ i f ω - act γ' i f ω|
      ≤ unifDist (proj γ i ω) (proj γ' i ω) * oscAt f i := by
  classical
  set di := (oscAt f i).toReal with hdidef
  have hdi : ENNReal.ofReal di = oscAt f i := ENNReal.ofReal_toReal (oscAt_ne_top_of_bounded hC)
  have hsecω : ∀ x y : E, |f (Function.update ω i x) - f (Function.update ω i y)| ≤ di := by
    intro x y
    have h : ENNReal.ofReal |f (Function.update ω i x) - f (Function.update ω i y)| ≤ oscAt f i :=
      le_oscAt fun k hk ↦ by rw [Function.update_of_ne hk, Function.update_of_ne hk]
    rw [← hdi] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  rw [act, act, integral_eq_integral_proj γ i ω hf, integral_eq_integral_proj γ' i ω hf, ← hdi]
  exact ofReal_abs_integral_sub_leD (hf.comp (measurable_updateOf i ω)) (C := C)
    (fun x ↦ hC _) hsecω

end SingleSite


/-! ### Localization of quasilocal observables (Georgii, Remark (8.17)(2)) -/

section Localize

variable [DecidableEq S]

/-- `σ ↦ σ_Λ ω_{S∖Λ}`: the configuration agreeing with `σ` on `Λ` and with `ω` off `Λ`. -/
def loc (Λ : Finset S) (ω σ : S → E) : S → E := fun k ↦ if k ∈ Λ then σ k else ω k

omit [MeasurableSpace E] in
@[simp] lemma loc_apply_of_mem {Λ : Finset S} {ω σ : S → E} {k : S} (hk : k ∈ Λ) :
    loc Λ ω σ k = σ k := by simp [loc, hk]

omit [MeasurableSpace E] in
@[simp] lemma loc_apply_of_notMem {Λ : Finset S} {ω σ : S → E} {k : S} (hk : k ∉ Λ) :
    loc Λ ω σ k = ω k := by simp [loc, hk]

lemma measurable_loc (Λ : Finset S) (ω : S → E) : Measurable (loc Λ ω) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  by_cases hk : k ∈ Λ
  · simpa [loc, hk] using measurable_pi_apply (X := fun _ : S ↦ E) k
  · simp [loc, hk]

omit [MeasurableSpace E] in
lemma dependsOn_loc (Λ : Finset S) (ω : S → E) : DependsOn (loc Λ ω) (Λ : Set S) := by
  intro σ σ' h
  funext k
  by_cases hk : k ∈ Λ
  · simp [loc, hk, h k (by exact_mod_cast hk)]
  · simp [loc, hk]

/-- Georgii's `f_Λ` from Remark (8.17)(2), as an element of `ℓ^∞`. -/
noncomputable def locLp (Λ : Finset S) (ω : S → E) (f : lp (fun _ : S → E ↦ ℝ) ∞) :
    lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨(⇑f) ∘ loc Λ ω, memℓp_infty ⟨‖f‖, by
    rintro _ ⟨x, rfl⟩; exact lp.norm_apply_le_norm ENNReal.top_ne_zero f _⟩⟩

omit [MeasurableSpace E] in
@[simp] lemma locLp_apply (Λ : Finset S) (ω : S → E) (f : lp (fun _ : S → E ↦ ℝ) ∞) (σ : S → E) :
    (locLp Λ ω f : (S → E) → ℝ) σ = (f : (S → E) → ℝ) (loc Λ ω σ) := rfl

lemma locLp_mem_localFunctions {Λ : Finset S} {ω : S → E} {f : lp (fun _ : S → E ↦ ℝ) ∞}
    (hf : Measurable (⇑f)) : locLp Λ ω f ∈ localFunctions S E :=
  mem_localFunctions.2 ⟨Λ, Measurable.cylinderEvents_of_dependsOn
    (hf.comp (measurable_loc Λ ω)) (DependsOn.comp (⇑f) (dependsOn_loc Λ ω))⟩

omit [MeasurableSpace E] in
lemma oscAt_locLp_le (Λ : Finset S) (ω : S → E) (f : lp (fun _ : S → E ↦ ℝ) ∞) (j : S) :
    oscAt (⇑(locLp Λ ω f)) j ≤ oscAt (⇑f) j := by
  refine oscAt_le fun ζ η h ↦ ?_
  refine le_oscAt (ζ := loc Λ ω ζ) (η := loc Λ ω η) fun k hk ↦ ?_
  by_cases hkΛ : k ∈ Λ
  · simp [hkΛ, h k hk]
  · simp [hkΛ]

lemma ofReal_abs_sub_locLp_le (Λ : Finset S) (ω : S → E) (f : lp (fun _ : S → E ↦ ℝ) ∞)
    (σ : S → E) :
    ENNReal.ofReal |(f : (S → E) → ℝ) σ - (locLp Λ ω f : (S → E) → ℝ) σ|
      ≤ oscOutside Λ (⇑f) :=
  le_oscOutside fun _ hk ↦ (loc_apply_of_mem hk).symm

/-- Georgii (8.15): for a quasilocal `f`, `δ(f) ≤ ∑_j δ_j(f)`. -/
theorem osc_le_tsum_oscAt {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E) :
    osc (⇑f) ≤ ∑' j, oscAt (⇑f) j := by
  classical
  have hosc : Tendsto (fun Λ : Finset S ↦ oscOutside Λ (⇑f)) atTop (𝓝 0) :=
    tendsto_oscOutside_of_mem_quasilocalFunctions hf
  have htend : Tendsto (fun Λ : Finset S ↦ oscOutside Λ (⇑f) + ∑' j, oscAt (⇑f) j) atTop
      (𝓝 (∑' j, oscAt (⇑f) j)) := by
    have hconst : Tendsto (fun _ : Finset S ↦ (∑' j, oscAt (⇑f) j)) atTop
        (𝓝 (∑' j, oscAt (⇑f) j)) := tendsto_const_nhds
    simpa using hosc.add hconst
  refine ge_of_tendsto htend (Filter.Eventually.of_forall fun Λ ↦ ?_)
  refine osc_le fun ζ η ↦ ?_
  have h1 : ENNReal.ofReal |(f : (S → E) → ℝ) ζ - (f : (S → E) → ℝ) (loc Λ η ζ)|
      ≤ oscOutside Λ (⇑f) := le_oscOutside fun k hk ↦ (loc_apply_of_mem hk).symm
  have h2 : ENNReal.ofReal |(f : (S → E) → ℝ) (loc Λ η ζ) - (f : (S → E) → ℝ) η|
      ≤ ∑ j ∈ Λ, oscAt (⇑f) j :=
    ofReal_abs_sub_le_sum_oscAt (⇑f) Λ (loc Λ η ζ) η fun k hk ↦ loc_apply_of_notMem hk
  calc ENNReal.ofReal |(f : (S → E) → ℝ) ζ - (f : (S → E) → ℝ) η|
      ≤ ENNReal.ofReal |(f : (S → E) → ℝ) ζ - (f : (S → E) → ℝ) (loc Λ η ζ)|
        + ENNReal.ofReal |(f : (S → E) → ℝ) (loc Λ η ζ) - (f : (S → E) → ℝ) η| := by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ ≤ oscOutside Λ (⇑f) + ∑' j, oscAt (⇑f) j :=
        add_le_add h1 (h2.trans (ENNReal.sum_le_tsum Λ))

end Localize


/-! ### Georgii (8.16), (8.17): estimates for a pair of measures -/

section Estimates

variable {μ ν : Measure (S → E)} {a b : S → ℝ≥0∞}

/-- Georgii (8.16): `a` is an *estimate* for `μ` and `μ̃` if
`|μ(f) - μ̃(f)| ≤ ∑_j a_j δ_j(f)` for every quasilocal `f`. -/
def IsEstimate (μ ν : Measure (S → E)) (a : S → ℝ≥0∞) : Prop :=
  ∀ f : lp (fun _ : S → E ↦ ℝ) ∞, f ∈ quasilocalFunctions S E →
    ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂μ - ∫ σ, (f : (S → E) → ℝ) σ ∂ν|
      ≤ ∑' j, a j * oscAt (⇑f) j

/-- Georgii (8.16) tested on local observables only; by Remark (8.17)(2) this is equivalent. -/
def IsEstimateOn (μ ν : Measure (S → E)) (a : S → ℝ≥0∞) : Prop :=
  ∀ f : lp (fun _ : S → E ↦ ℝ) ∞, f ∈ localFunctions S E →
    ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂μ - ∫ σ, (f : (S → E) → ℝ) σ ∂ν|
      ≤ ∑' j, a j * oscAt (⇑f) j

lemma IsEstimate.isEstimateOn (h : IsEstimate μ ν a) : IsEstimateOn μ ν a :=
  fun f hf ↦ h f (localFunctions_le_quasilocalFunctions hf)

lemma IsEstimate.mono (h : IsEstimate μ ν a) (hab : ∀ j, a j ≤ b j) : IsEstimate μ ν b :=
  fun f hf ↦ (h f hf).trans (ENNReal.tsum_le_tsum fun j ↦ by gcongr; exact hab j)

lemma oscOutside_le_osc {Λ : Finset S} {f : (S → E) → ℝ} : oscOutside Λ f ≤ osc f :=
  oscOutside_le fun ζ η _ ↦ le_osc _ ζ η

/-- Georgii, Remark (8.17)(3): an estimate obtained by improving finitely many coordinates at a
time is an estimate. -/
lemma isEstimateOn_of_forall_finset [DecidableEq S]
    (h : ∀ Λ : Finset S, IsEstimateOn μ ν (fun j ↦ if j ∈ Λ then b j else a j)) :
    IsEstimateOn μ ν b := by
  classical
  intro f hf
  obtain ⟨Λ, hΛ⟩ := mem_localFunctions.1 hf
  have hdep : DependsOn (⇑f) (Λ : Set S) :=
    (mem_localFunctionsOn.1 hΛ).dependsOn_of_cylinderEvents
  refine (h Λ f hf).trans_eq (tsum_congr fun j ↦ ?_)
  by_cases hj : j ∈ Λ
  · simp [hj]
  · simp [hj, oscAt_eq_zero_of_dependsOn hdep (by simpa using hj)]

/-- Georgii, Remark (8.17)(2): it suffices to test (8.16) on local observables. -/
theorem IsEstimateOn.isEstimate [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : IsEstimateOn μ ν a) : IsEstimate μ ν a := by
  classical
  intro f hf
  have hfmeas : Measurable (⇑f) := measurable_of_mem_quasilocalFunctions hf
  rcases isEmpty_or_nonempty (S → E) with hemp | hne'
  · exact absurd (measure_univ (μ := μ)) (by simp [Set.univ_eq_empty_iff.2 hemp])
  obtain ⟨ω⟩ := hne'
  set T := ∑' j, a j * oscAt (⇑f) j with hT
  have hosc : Tendsto (fun Λ : Finset S ↦ oscOutside Λ (⇑f)) atTop (𝓝 0) :=
    tendsto_oscOutside_of_mem_quasilocalFunctions hf
  have htend : Tendsto (fun Λ : Finset S ↦ oscOutside Λ (⇑f) + oscOutside Λ (⇑f) + T)
      atTop (𝓝 T) := by
    have hconst : Tendsto (fun _ : Finset S ↦ T) atTop (𝓝 T) := tendsto_const_nhds
    simpa using (hosc.add hosc).add hconst
  refine ge_of_tendsto htend (Filter.Eventually.of_forall fun Λ ↦ ?_)
  set g := locLp Λ ω f with hg
  have hgmeas : Measurable (⇑g) := hfmeas.comp (measurable_loc Λ ω)
  have hne : oscOutside Λ (⇑f) ≠ ⊤ :=
    ne_top_of_le_ne_top (osc_ne_top_of_bounded (C := ‖f‖)
      (fun σ ↦ by simpa [Real.norm_eq_abs] using
        lp.norm_apply_le_norm ENNReal.top_ne_zero f σ)) oscOutside_le_osc
  set d := (oscOutside Λ (⇑f)).toReal with hd
  have hdeq : ENNReal.ofReal d = oscOutside Λ (⇑f) := ENNReal.ofReal_toReal hne
  have hpt : ∀ σ : S → E, |(f : (S → E) → ℝ) σ - (g : (S → E) → ℝ) σ| ≤ d := by
    intro σ
    have := ofReal_abs_sub_locLp_le Λ ω f σ
    rw [← hdeq] at this
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  have hcmp : ∀ ρ : Measure (S → E), IsProbabilityMeasure ρ →
      ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂ρ - ∫ σ, (g : (S → E) → ℝ) σ ∂ρ|
        ≤ oscOutside Λ (⇑f) := by
    intro ρ hρ
    have := hρ
    have hsub : ∫ σ, (f : (S → E) → ℝ) σ ∂ρ - ∫ σ, (g : (S → E) → ℝ) σ ∂ρ
        = ∫ σ, ((f : (S → E) → ℝ) σ - (g : (S → E) → ℝ) σ) ∂ρ :=
      (integral_sub (lp.integrable_of_measurable hfmeas ρ)
        (lp.integrable_of_measurable hgmeas ρ)).symm
    rw [hsub, ← hdeq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := norm_integral_le_of_norm_le_const (μ := ρ) (C := d)
      (Filter.Eventually.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hpt σ)
    simpa [Real.norm_eq_abs] using hb
  have hmid : ENNReal.ofReal |∫ σ, (g : (S → E) → ℝ) σ ∂μ - ∫ σ, (g : (S → E) → ℝ) σ ∂ν| ≤ T := by
    refine (h g (locLp_mem_localFunctions hfmeas)).trans ?_
    exact ENNReal.tsum_le_tsum fun j ↦ by gcongr; exact oscAt_locLp_le Λ ω f j
  calc ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂μ - ∫ σ, (f : (S → E) → ℝ) σ ∂ν|
      ≤ ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂μ - ∫ σ, (g : (S → E) → ℝ) σ ∂μ|
        + (ENNReal.ofReal |∫ σ, (g : (S → E) → ℝ) σ ∂μ - ∫ σ, (g : (S → E) → ℝ) σ ∂ν|
          + ENNReal.ofReal |∫ σ, (g : (S → E) → ℝ) σ ∂ν - ∫ σ, (f : (S → E) → ℝ) σ ∂ν|) := by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
          ← ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := abs_sub_le (∫ σ, (f : (S → E) → ℝ) σ ∂μ) (∫ σ, (g : (S → E) → ℝ) σ ∂μ)
          (∫ σ, (f : (S → E) → ℝ) σ ∂ν)
        have h2 := abs_sub_le (∫ σ, (g : (S → E) → ℝ) σ ∂μ) (∫ σ, (g : (S → E) → ℝ) σ ∂ν)
          (∫ σ, (f : (S → E) → ℝ) σ ∂ν)
        linarith
    _ ≤ oscOutside Λ (⇑f) + (T + oscOutside Λ (⇑f)) := by
        refine add_le_add (hcmp μ inferInstance) (add_le_add hmid ?_)
        rw [abs_sub_comm]
        exact hcmp ν inferInstance
    _ = oscOutside Λ (⇑f) + oscOutside Λ (⇑f) + T := by ring

/-- Georgii, Remark (8.17)(1): the constant vector `a ≡ 1` is always an estimate. -/
theorem isEstimate_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsEstimate μ ν 1 := by
  classical
  intro f hf
  have hfmeas : Measurable (⇑f) := measurable_of_mem_quasilocalFunctions hf
  have hCb : ∀ σ : S → E, |(f : (S → E) → ℝ) σ| ≤ ‖f‖ := fun σ ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f σ
  have hoscne : osc (⇑f) ≠ ⊤ := osc_ne_top_of_bounded hCb
  set D := (osc (⇑f)).toReal with hD
  have hDeq : ENNReal.ofReal D = osc (⇑f) := ENNReal.ofReal_toReal hoscne
  have hDb : ∀ x y : S → E, |(f : (S → E) → ℝ) x - (f : (S → E) → ℝ) y| ≤ D := by
    intro x y
    have h := le_osc (⇑f) x y
    rw [← hDeq] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have hkey := ofReal_abs_integral_sub_leD (α₁ := μ) (α₂ := ν) (f := (⇑f)) hfmeas hCb hDb
  rw [hDeq] at hkey
  refine hkey.trans ?_
  have h1 : unifDist μ ν * osc (⇑f) ≤ 1 * osc (⇑f) := mul_le_mul' unifDist_le_one le_rfl
  refine h1.trans ?_
  rw [one_mul]
  refine (osc_le_tsum_oscAt hf).trans_eq (tsum_congr fun j ↦ ?_)
  simp

end Estimates


/-! ### Prerequisites for Georgii's Lemma (8.18) -/

section Prereq818

variable {γ : Specification S E}

/-- `γ_i^0(·|ω)` does not depend on `ω_i`. -/
lemma proj_eq_of_agree (γ : Specification S E) (i : S) {ζ η : S → E}
    (h : ∀ k, k ≠ i → ζ k = η k) : proj γ i ζ = proj γ i η := by
  have hker : γ {i} ζ = γ {i} η := by
    refine Measure.ext fun A hA ↦ ?_
    have hmeas : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((({i} : Finset S) : Set S)ᶜ)]
        (fun ω ↦ γ {i} ω A) := Kernel.measurable_coe _ hA
    exact hmeas.dependsOn_of_cylinderEvents fun k hk ↦ h k (by simpa using hk)
  rw [proj, proj, hker]

/-- Georgii, used in the proof of (8.18): `C_{ii}(γ) = 0`. -/
@[simp] lemma interdep_self_eq_zero (γ : Specification S E) (i : S) : interdep γ i i = 0 :=
  le_antisymm (iSup₂_le fun ζ η ↦ iSup_le fun h ↦ by
    show unifDist (proj γ i ζ) (proj γ i η) ≤ 0
    rw [proj_eq_of_agree γ i h]; simp) bot_le

lemma coe_action_eq_act (γ : Specification S E) (i : S) (f : lp (fun _ : S → E ↦ ℝ) ∞) :
    ⇑(Specification.action γ {i} f) = act γ i (⇑f) := rfl

/-- `∫ f d(μ γ_i) = ∫ γ_i f dμ`. -/
lemma integral_bind_singleton (γ : Specification S E) (i : S) (μ : Measure (S → E))
    [IsProbabilityMeasure μ] {f : (S → E) → ℝ} {C : ℝ} (hf : Measurable f)
    (hC : ∀ σ, |f σ| ≤ C) :
    ∫ σ, f σ ∂(μ.bind (γ {i})) = ∫ ω, act γ i f ω ∂μ := by
  classical
  set κ : Kernel (S → E) (S → E) :=
    (γ {i}).comap id (cylinderEvents_le_pi (X := fun _ : S ↦ E)
      (Δ := ((({i} : Finset S) : Set S)ᶜ))) with hκdef
  have hκ : ⇑κ = ⇑(γ {i}) := by simp [hκdef, Kernel.coe_comap]
  have : IsProbabilityMeasure (μ.bind (γ {i})) := γ.isProbabilityMeasure_bind {i} μ
  have hint : Integrable f (μ.bind ⇑(γ {i})) :=
    ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C)
      (Filter.Eventually.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hC σ)⟩
  rw [← hκ] at hint ⊢
  exact Measure.integral_bind hint

end Prereq818


/-! ### Georgii's key Lemma (8.18) -/

section Lemma818

variable {γ γ' : Specification S E} {μ ν : Measure (S → E)}

/-- **Georgii, Lemma (8.18).** If `a` is an estimate for `μ ∈ 𝒢(γ)` and `μ̃ ∈ 𝒢(γ̃)`, then so is
`C(γ) a + μ̃(b)`, where `b_i` dominates `‖γ_i^0(·|ω) - γ̃_i^0(·|ω)‖`. -/
theorem IsEstimate.step [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hγq : γ.IsQuasilocal)
    (hμ : ∀ i : S, μ.bind (γ {i}) = μ) (hν : ∀ i : S, ν.bind (γ' {i}) = ν)
    {a : S → ℝ≥0∞} (ha : IsEstimate μ ν a)
    {b : S → (S → E) → ℝ≥0∞} (hbm : ∀ i, Measurable (b i))
    (hb : ∀ i ω, unifDist (proj γ i ω) (proj γ' i ω) ≤ b i ω) :
    IsEstimate μ ν (fun i ↦ (∑' j, interdep γ i j * a j) + ∫⁻ ω, b i ω ∂ν) := by
  classical
  set bar : S → ℝ≥0∞ := fun i ↦ (∑' j, interdep γ i j * a j) + ∫⁻ ω, b i ω ∂ν with hbar
  set aa : Finset S → S → ℝ≥0∞ := fun Λ j ↦ if j ∈ Λ then min (bar j) (a j) else a j with haa
  have key : ∀ Λ : Finset S, IsEstimate μ ν (aa Λ) := by
    intro Λ
    induction Λ using Finset.induction_on with
    | empty => simpa [haa] using ha
    | insert i Λ hi ih =>
        refine IsEstimateOn.isEstimate ?_
        intro f hfloc
        have hfq : f ∈ quasilocalFunctions S E := localFunctions_le_quasilocalFunctions hfloc
        have hfm : Measurable (⇑f) := measurable_of_mem_quasilocalFunctions hfq
        have hfb : ∀ σ : S → E, |(f : (S → E) → ℝ) σ| ≤ ‖f‖ := fun σ ↦ by
          simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f σ
        set d : S → ℝ≥0∞ := fun j ↦ oscAt (⇑f) j with hd
        have hgq : Specification.action γ {i} f ∈ quasilocalFunctions S E := hγq {i} f hfq
        have hgm : Measurable (act γ i (⇑f)) := measurable_act hfm i
        have hg'm : Measurable (act γ' i (⇑f)) := measurable_act hfm i
        have hgb : ∀ ω, |act γ i (⇑f) ω| ≤ ‖f‖ := abs_act_le hfb i
        have hg'b : ∀ ω, |act γ' i (⇑f) ω| ≤ ‖f‖ := abs_act_le hfb i
        have hintg : ∀ (ρ : Measure (S → E)) (_ : IsProbabilityMeasure ρ),
            Integrable (act γ i (⇑f)) ρ := by
          intro ρ hρ
          have := hρ
          exact ⟨hgm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := ‖f‖)
            (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hgb ω)⟩
        have hintg' : ∀ (ρ : Measure (S → E)) (_ : IsProbabilityMeasure ρ),
            Integrable (act γ' i (⇑f)) ρ := by
          intro ρ hρ
          have := hρ
          exact ⟨hg'm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := ‖f‖)
            (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hg'b ω)⟩
        have hμf : ∫ σ, (f : (S → E) → ℝ) σ ∂μ = ∫ ω, act γ i (⇑f) ω ∂μ := by
          conv_lhs => rw [← hμ i]
          exact integral_bind_singleton γ i μ hfm hfb
        have hνf : ∫ σ, (f : (S → E) → ℝ) σ ∂ν = ∫ ω, act γ' i (⇑f) ω ∂ν := by
          conv_lhs => rw [← hν i]
          exact integral_bind_singleton γ' i ν hfm hfb
        set A := ∫ ω, act γ i (⇑f) ω ∂μ with hA
        set B := ∫ ω, act γ i (⇑f) ω ∂ν with hB
        set D := ∫ ω, act γ' i (⇑f) ω ∂ν with hD
        set X := ∑' j, (if j = i then 0 else aa Λ j * d j) with hX
        -- Term 1: the induction hypothesis applied to `γ_i f`
        have hT1 : ENNReal.ofReal |A - B| ≤ ∑' j, aa Λ j * oscAt (act γ i (⇑f)) j := by
          have h := ih (Specification.action γ {i} f) hgq
          rwa [coe_action_eq_act] at h
        have hsum1 : (∑' j, aa Λ j * oscAt (act γ i (⇑f)) j)
            ≤ X + (∑' j, interdep γ i j * a j) * d i := by
          have hterm : ∀ j, aa Λ j * oscAt (act γ i (⇑f)) j
              ≤ (if j = i then 0 else aa Λ j * d j) + (interdep γ i j * a j) * d i := by
            intro j
            by_cases hj : j = i
            · subst hj; simp [oscAt_act_self hfm]
            · rw [ite_eq_right hj]
              have h1 : oscAt (act γ i (⇑f)) j ≤ d j + interdep γ i j * d i :=
                oscAt_act_le hfm hfb i j
              have h2 : aa Λ j ≤ a j := by
                by_cases hjΛ : j ∈ Λ
                · simp [haa, hjΛ]
                · simp [haa, hjΛ]
              calc aa Λ j * oscAt (act γ i (⇑f)) j
                  ≤ aa Λ j * (d j + interdep γ i j * d i) := by gcongr
                _ = aa Λ j * d j + interdep γ i j * aa Λ j * d i := by ring
                _ ≤ aa Λ j * d j + interdep γ i j * a j * d i := by gcongr
          calc (∑' j, aa Λ j * oscAt (act γ i (⇑f)) j)
              ≤ ∑' j, ((if j = i then 0 else aa Λ j * d j) + (interdep γ i j * a j) * d i) :=
                ENNReal.tsum_le_tsum hterm
            _ = X + ∑' j, (interdep γ i j * a j) * d i := ENNReal.tsum_add
            _ = X + (∑' j, interdep γ i j * a j) * d i := by rw [ENNReal.tsum_mul_right]
        -- Term 2: the two specifications differ by at most `b_i`
        have hT2 : ENNReal.ofReal |B - D| ≤ (∫⁻ ω, b i ω ∂ν) * d i := by
          have hsub : B - D = ∫ ω, (act γ i (⇑f) ω - act γ' i (⇑f) ω) ∂ν :=
            (integral_sub (hintg ν inferInstance) (hintg' ν inferInstance)).symm
          have habs : |B - D| ≤ ∫ ω, |act γ i (⇑f) ω - act γ' i (⇑f) ω| ∂ν := by
            rw [hsub]
            simpa [Real.norm_eq_abs] using
              norm_integral_le_integral_norm (μ := ν)
                (f := fun ω ↦ act γ i (⇑f) ω - act γ' i (⇑f) ω)
          have hintabs : Integrable (fun ω ↦ |act γ i (⇑f) ω - act γ' i (⇑f) ω|) ν :=
            ((hintg ν inferInstance).sub (hintg' ν inferInstance)).abs
          calc ENNReal.ofReal |B - D|
              ≤ ENNReal.ofReal (∫ ω, |act γ i (⇑f) ω - act γ' i (⇑f) ω| ∂ν) :=
                ENNReal.ofReal_le_ofReal habs
            _ = ∫⁻ ω, ENNReal.ofReal |act γ i (⇑f) ω - act γ' i (⇑f) ω| ∂ν :=
                ofReal_integral_eq_lintegral_ofReal hintabs
                  (Filter.Eventually.of_forall fun ω ↦ abs_nonneg _)
            _ ≤ ∫⁻ ω, b i ω * d i ∂ν := by
                refine lintegral_mono fun ω ↦ ?_
                refine (ofReal_abs_act_sub_act_le hfm hfb i ω).trans ?_
                gcongr
                exact hb i ω
            _ = (∫⁻ ω, b i ω ∂ν) * d i := lintegral_mul_const _ (hbm i)
        -- Combine
        have hbound1 : ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂μ
            - ∫ σ, (f : (S → E) → ℝ) σ ∂ν| ≤ X + bar i * d i := by
          rw [hμf, hνf]
          calc ENNReal.ofReal |A - D|
              ≤ ENNReal.ofReal |A - B| + ENNReal.ofReal |B - D| := by
                rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
                exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
            _ ≤ (X + (∑' j, interdep γ i j * a j) * d i) + (∫⁻ ω, b i ω ∂ν) * d i :=
                add_le_add (hT1.trans hsum1) hT2
            _ = X + bar i * d i := by rw [hbar]; ring
        have hbound2 : ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂μ
            - ∫ σ, (f : (S → E) → ℝ) σ ∂ν| ≤ X + a i * d i := by
          refine (ih f hfq).trans ?_
          have hsplit : (∑' j, aa Λ j * d j) = aa Λ i * d i + X :=
            ENNReal.tsum_eq_add_tsum_ite i
          rw [hsplit]
          have : aa Λ i = a i := by simp [haa, hi]
          rw [this, add_comm]
        -- conclude
        have hgoal : (∑' j, aa (insert i Λ) j * d j) = min (bar i) (a i) * d i + X := by
          have hsplit : (∑' j, aa (insert i Λ) j * d j)
              = aa (insert i Λ) i * d i + ∑' j, (if j = i then 0 else aa (insert i Λ) j * d j) :=
            ENNReal.tsum_eq_add_tsum_ite i
          have hXeq : (∑' j, (if j = i then 0 else aa (insert i Λ) j * d j)) = X := by
            refine tsum_congr fun j ↦ ?_
            by_cases hj : j = i
            · simp [hj]
            · simp [hj, haa, Finset.mem_insert]
          have hai : aa (insert i Λ) i = min (bar i) (a i) := by simp [haa]
          rw [hsplit, hXeq, hai]
        rw [hgoal]
        rcases le_total (bar i) (a i) with hle | hle
        · rw [min_eq_left hle, add_comm]; exact hbound1
        · rw [min_eq_right hle, add_comm]; exact hbound2
  have hfin : IsEstimateOn μ ν (fun j ↦ min (bar j) (a j)) :=
    isEstimateOn_of_forall_finset (a := a) (b := fun j ↦ min (bar j) (a j))
      fun Λ ↦ (key Λ).isEstimateOn
  exact (hfin.isEstimate).mono fun j ↦ min_le_left _ _

end Lemma818


/-! ### Iterating the interdependence matrix -/

section Iterate

variable {γ γ' : Specification S E} {μ ν : Measure (S → E)}

/-- `C(γ)^n a`, the `n`-fold action of Dobrushin's interdependence matrix on a vector. -/
noncomputable def interdepIter (γ : Specification S E) : ℕ → (S → ℝ≥0∞) → S → ℝ≥0∞
  | 0, a => a
  | (n + 1), a => fun i ↦ ∑' j, interdep γ i j * interdepIter γ n a j

@[simp] lemma interdepIter_zero (γ : Specification S E) (a : S → ℝ≥0∞) :
    interdepIter γ 0 a = a := rfl

lemma interdepIter_succ (γ : Specification S E) (n : ℕ) (a : S → ℝ≥0∞) (i : S) :
    interdepIter γ (n + 1) a i = ∑' j, interdep γ i j * interdepIter γ n a j := rfl

/-- Georgii, proof of (8.20): `∑_j C^n_{ij} ≤ c(γ)^n`. -/
lemma interdepIter_le (γ : Specification S E) {c : ℝ≥0∞} (hc : ∀ i, ∑' j, interdep γ i j ≤ c)
    {a : S → ℝ≥0∞} {M : ℝ≥0∞} (ha : ∀ j, a j ≤ M) (n : ℕ) (i : S) :
    interdepIter γ n a i ≤ M * c ^ n := by
  induction n generalizing i with
  | zero => simpa using ha i
  | succ n ih =>
      calc interdepIter γ (n + 1) a i = ∑' j, interdep γ i j * interdepIter γ n a j := rfl
        _ ≤ ∑' j, interdep γ i j * (M * c ^ n) :=
            ENNReal.tsum_le_tsum fun j ↦ by gcongr; exact ih j
        _ = (∑' j, interdep γ i j) * (M * c ^ n) := ENNReal.tsum_mul_right
        _ ≤ c * (M * c ^ n) := by gcongr; exact hc i
        _ = M * c ^ (n + 1) := by ring

/-- Iterating Georgii's Lemma (8.18) with `γ̃ = γ` and `b = 0`. -/
theorem isEstimate_interdepIter [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hγq : γ.IsQuasilocal) (hμ : ∀ i : S, μ.bind (γ {i}) = μ) (hν : ∀ i : S, ν.bind (γ {i}) = ν)
    {a : S → ℝ≥0∞} (ha : IsEstimate μ ν a) (n : ℕ) : IsEstimate μ ν (interdepIter γ n a) := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
      have h := IsEstimate.step (γ := γ) (γ' := γ) hγq hμ hν ih (b := fun _ _ ↦ 0)
        (fun _ ↦ measurable_const) (fun i ω ↦ by simp)
      exact h.mono fun i ↦ by simp [interdepIter_succ]

end Iterate

/-! ### Local observables separate probability measures -/

section Separate

variable {μ ν : Measure (S → E)}

/-- Two probability measures on the configuration space agreeing on all bounded local observables
are equal. -/
theorem eq_of_forall_localFunctions_integral_eq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ f : lp (fun _ : S → E ↦ ℝ) ∞, f ∈ localFunctions S E →
      ∫ σ, (f : (S → E) → ℝ) σ ∂μ = ∫ σ, (f : (S → E) → ℝ) σ ∂ν) : μ = ν := by
  classical
  refine ext_of_generate_finite (squareCylindersMeas S E)
      (generateFrom_squareCylindersMeas S E) (isPiSystem_squareCylindersMeas S E) ?_ (by simp)
  rintro C ⟨J, t, ht, rfl⟩
  set A : Set (S → E) := (J : Set S).pi t with hAdef
  have htm : ∀ j, MeasurableSet (t j) := fun j ↦ Set.mem_univ_pi.1 ht j
  have hAmeas : MeasurableSet A := measurableSet_finset_pi J t htm
  have hdep : DependsOn (A.indicator (1 : (S → E) → ℝ)) (J : Set S) := by
    intro σ σ' hσ
    have : σ ∈ A ↔ σ' ∈ A := by
      simp only [hAdef, Set.mem_pi, Finset.mem_coe]
      exact ⟨fun hh j hj ↦ (hσ j (by exact_mod_cast hj)) ▸ hh j hj,
        fun hh j hj ↦ (hσ j (by exact_mod_cast hj)).symm ▸ hh j hj⟩
    by_cases hσA : σ ∈ A
    · rw [Set.indicator_of_mem hσA, Set.indicator_of_mem (this.1 hσA)]; rfl
    · have hσ'A : σ' ∉ A := fun hc ↦ hσA (this.2 hc)
      rw [Set.indicator_of_notMem hσA, Set.indicator_of_notMem hσ'A]
  have hmeas : Measurable (A.indicator (1 : (S → E) → ℝ)) :=
    (measurable_const : Measurable (1 : (S → E) → ℝ)).indicator hAmeas
  set g : lp (fun _ : S → E ↦ ℝ) ∞ :=
    ⟨A.indicator (1 : (S → E) → ℝ), memℓp_infty ⟨1, by
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]; simp
      · simp only [Set.indicator_of_notMem hx]; simp⟩⟩ with hgdef
  have hgloc : g ∈ localFunctions S E :=
    mem_localFunctions.2 ⟨J, Measurable.cylinderEvents_of_dependsOn hmeas hdep⟩
  have hint := h g hgloc
  have hμA : ∫ σ, (g : (S → E) → ℝ) σ ∂μ = μ.real A := integral_indicator_one hAmeas
  have hνA : ∫ σ, (g : (S → E) → ℝ) σ ∂ν = ν.real A := integral_indicator_one hAmeas
  rw [hμA, hνA] at hint
  have h1 : (μ A).toReal = (ν A).toReal := hint
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).1 h1

end Separate


/-! ### Georgii's Theorem (8.7): Dobrushin's uniqueness theorem -/

section Uniqueness

variable {γ : Specification S E} {μ ν : Measure (S → E)}

/-- The sum of the single-site oscillations of a local observable is finite. -/
lemma tsum_oscAt_ne_top {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctions S E) :
    (∑' j, oscAt (⇑f) j) ≠ ⊤ := by
  classical
  obtain ⟨Λ, hΛ⟩ := mem_localFunctions.1 hf
  have hdep : DependsOn (⇑f) (Λ : Set S) :=
    (mem_localFunctionsOn.1 hΛ).dependsOn_of_cylinderEvents
  have hfb : ∀ σ : S → E, |(f : (S → E) → ℝ) σ| ≤ ‖f‖ := fun σ ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f σ
  have hsum : (∑' j, oscAt (⇑f) j) = ∑ j ∈ Λ, oscAt (⇑f) j :=
    tsum_eq_sum fun j hj ↦ oscAt_eq_zero_of_dependsOn hdep (by simpa using hj)
  rw [hsum]
  exact (ENNReal.sum_lt_top.2 fun j _ ↦ (oscAt_ne_top_of_bounded hfb).lt_top).ne

/-- **Georgii, Theorem (8.7)** (uniqueness part): a quasilocal specification satisfying
Dobrushin's condition of weak dependence has at most one Gibbs measure. -/
theorem eq_of_isDobrushin [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ)
    (hμ : ∀ i : S, μ.bind (γ {i}) = μ) (hν : ∀ i : S, ν.bind (γ {i}) = ν) : μ = ν := by
  classical
  obtain ⟨-, c, hc1, hc⟩ := hd
  refine eq_of_forall_localFunctions_integral_eq fun f hfloc ↦ ?_
  have hfq : f ∈ quasilocalFunctions S E := localFunctions_le_quasilocalFunctions hfloc
  set T : ℝ≥0∞ := ∑' j, oscAt (⇑f) j with hT
  have hTfin : T ≠ ⊤ := tsum_oscAt_ne_top hfloc
  have hbound : ∀ n : ℕ,
      ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂μ - ∫ σ, (f : (S → E) → ℝ) σ ∂ν| ≤ c ^ n * T := by
    intro n
    refine (isEstimate_interdepIter hγq hμ hν isEstimate_one n f hfq).trans ?_
    calc (∑' j, interdepIter γ n 1 j * oscAt (⇑f) j)
        ≤ ∑' j, (c ^ n) * oscAt (⇑f) j := by
          refine ENNReal.tsum_le_tsum fun j ↦ ?_
          gcongr
          simpa using interdepIter_le γ hc (a := (1 : S → ℝ≥0∞)) (M := 1) (fun _ ↦ le_rfl) n j
      _ = c ^ n * T := ENNReal.tsum_mul_left
  have htend : Tendsto (fun n : ℕ ↦ c ^ n * T) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ ↦ c ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc1
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hTfin)
  have hzero : ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂μ
      - ∫ σ, (f : (S → E) → ℝ) σ ∂ν| ≤ 0 :=
    ge_of_tendsto htend (Filter.Eventually.of_forall hbound)
  have habs : |∫ σ, (f : (S → E) → ℝ) σ ∂μ - ∫ σ, (f : (S → E) → ℝ) σ ∂ν| ≤ 0 :=
    ENNReal.ofReal_eq_zero.1 (le_antisymm hzero bot_le)
  have := abs_nonpos_iff.1 habs
  linarith [this]

/-- **Georgii, Theorem (8.7)**: `|𝒢(γ)| ≤ 1` for a quasilocal specification satisfying
Dobrushin's condition. -/
theorem subsingleton_GP_of_isDobrushin (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ) :
    (GP (S := S) (E := E) γ).Subsingleton := by
  intro μ hμ ν hν
  have hμ' : ∀ i : S, (μ : Measure (S → E)).bind (γ {i}) = (μ : Measure (S → E)) := fun i ↦
    (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)
      (μ := (μ : Measure (S → E)))).1 hμ {i}
  have hν' : ∀ i : S, (ν : Measure (S → E)).bind (γ {i}) = (ν : Measure (S → E)) := fun i ↦
    (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)
      (μ := (ν : Measure (S → E)))).1 hν {i}
  exact ProbabilityMeasure.toMeasure_injective (eq_of_isDobrushin hγq hd hμ' hν')

end Uniqueness


/-! ### Existence and uniqueness: `|𝒢(γ)| = 1` -/

section ExistenceUniqueness

variable {γ : Specification S E}

/-- **Georgii, Theorem (8.7)**: under Dobrushin's condition, `𝒢(γ)` is a singleton as soon as it
is non-empty. -/
theorem existsUnique_mem_GP_of_isDobrushin (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ)
    (hne : (GP (S := S) (E := E) γ).Nonempty) :
    ∃! μ : ProbabilityMeasure (S → E), μ ∈ GP (S := S) (E := E) γ := by
  obtain ⟨μ, hμ⟩ := hne
  exact ⟨μ, hμ, fun _ hσ ↦ subsingleton_GP_of_isDobrushin hγq hd hσ hμ⟩

/-- **Georgii, Theorem (8.7)**, second assertion: over a standard Borel state space the Gibbsian
specification of an absolutely summable potential satisfying Dobrushin's condition has exactly one
Gibbs measure. -/
theorem existsUnique_mem_GP_gibbsSpecification [Countable S] [StandardBorelSpace E]
    {Φ : Potential S E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (hd : IsDobrushin (Φ.gibbsSpecificationOfAbsolutelySummable ν β)) :
    ∃! μ : ProbabilityMeasure (S → E),
      μ ∈ GP (S := S) (E := E) (Φ.gibbsSpecificationOfAbsolutelySummable ν β) :=
  existsUnique_mem_GP_of_isDobrushin
    (Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable ν β) hd
    (Potential.GP_gibbsSpecification_nonempty ν β)

end ExistenceUniqueness


/-! ### Georgii's comparison theorem (8.20) -/

section Comparison820

variable {γ γ' : Specification S E} {μ ν : Measure (S → E)}

/-- Georgii (8.19): the vector `D(γ) b̃ = ∑_{n ≥ 0} C(γ)^n b̃`, whose `i`-th coordinate is
`∑_j D_{ij}(γ) b̃_j`. -/
noncomputable def interdepSeries (γ : Specification S E) (bt : S → ℝ≥0∞) (i : S) : ℝ≥0∞ :=
  ∑' n : ℕ, interdepIter γ n bt i

/-- Georgii, proof of (8.20): the vectors `a^{(n)} = C^n 1 + ∑_{k<n} C^k b̃`. -/
noncomputable def comparisonVec (γ : Specification S E) (bt : S → ℝ≥0∞) (n : ℕ) (i : S) : ℝ≥0∞ :=
  interdepIter γ n 1 i + ∑ k ∈ Finset.range n, interdepIter γ k bt i

lemma comparisonVec_succ (γ : Specification S E) (bt : S → ℝ≥0∞) (n : ℕ) (i : S) :
    (∑' j, interdep γ i j * comparisonVec γ bt n j) + bt i = comparisonVec γ bt (n + 1) i := by
  have hmul : ∀ j, interdep γ i j * comparisonVec γ bt n j
      = interdep γ i j * interdepIter γ n 1 j
        + ∑ k ∈ Finset.range n, interdep γ i j * interdepIter γ k bt j := by
    intro j; rw [comparisonVec, mul_add, Finset.mul_sum]
  have hswap : (∑' j, ∑ k ∈ Finset.range n, interdep γ i j * interdepIter γ k bt j)
      = ∑ k ∈ Finset.range n, interdepIter γ (k + 1) bt i := by
    rw [Summable.tsum_finsetSum fun k _ ↦ ENNReal.summable]
    exact Finset.sum_congr rfl fun k _ ↦ (interdepIter_succ γ k bt i).symm
  calc (∑' j, interdep γ i j * comparisonVec γ bt n j) + bt i
      = ((∑' j, interdep γ i j * interdepIter γ n 1 j)
          + ∑' j, ∑ k ∈ Finset.range n, interdep γ i j * interdepIter γ k bt j) + bt i := by
        rw [tsum_congr hmul, ENNReal.tsum_add]
    _ = (interdepIter γ (n + 1) 1 i + ∑ k ∈ Finset.range n, interdepIter γ (k + 1) bt i)
          + bt i := by
        rw [hswap, ← interdepIter_succ]
    _ = comparisonVec γ bt (n + 1) i := by
        rw [comparisonVec, Finset.sum_range_succ' (fun k ↦ interdepIter γ k bt i) n]
        simp [add_assoc]

/-- Georgii, proof of (8.20): each `a^{(n)}` is an estimate. -/
theorem isEstimate_comparisonVec [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hγq : γ.IsQuasilocal) (hμ : ∀ i : S, μ.bind (γ {i}) = μ)
    (hν : ∀ i : S, ν.bind (γ' {i}) = ν)
    {b : S → (S → E) → ℝ≥0∞} (hbm : ∀ i, Measurable (b i))
    (hb : ∀ i ω, unifDist (proj γ i ω) (proj γ' i ω) ≤ b i ω) (n : ℕ) :
    IsEstimate μ ν (comparisonVec γ (fun j ↦ ∫⁻ ω, b j ω ∂ν) n) := by
  induction n with
  | zero =>
      have h0 : comparisonVec γ (fun j ↦ ∫⁻ ω, b j ω ∂ν) 0 = 1 := by
        funext i; simp [comparisonVec]
      rw [h0]; exact isEstimate_one
  | succ n ih =>
      exact (IsEstimate.step hγq hμ hν ih hbm hb).mono fun i ↦
        le_of_eq (comparisonVec_succ γ _ n i)

/-- **Georgii, Theorem (8.20)** (the Dobrushin comparison theorem). If `γ` is quasilocal and
satisfies Dobrushin's condition, `μ` is Gibbs for `γ`, `μ̃` is Gibbs for `γ̃`, and `b_i` dominates
`‖γ_i^0(·|ω) - γ̃_i^0(·|ω)‖`, then
`|μ(f) - μ̃(f)| ≤ ∑_{i,j} δ_i(f) D_{ij}(γ) μ̃(b_j)` for every local `f`. -/
theorem comparison [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ)
    (hμ : ∀ i : S, μ.bind (γ {i}) = μ) (hν : ∀ i : S, ν.bind (γ' {i}) = ν)
    {b : S → (S → E) → ℝ≥0∞} (hbm : ∀ i, Measurable (b i))
    (hb : ∀ i ω, unifDist (proj γ i ω) (proj γ' i ω) ≤ b i ω) :
    IsEstimateOn μ ν (interdepSeries γ fun j ↦ ∫⁻ ω, b j ω ∂ν) := by
  classical
  obtain ⟨-, c, hc1, hc⟩ := hd
  intro f hfloc
  have hfq : f ∈ quasilocalFunctions S E := localFunctions_le_quasilocalFunctions hfloc
  set bt : S → ℝ≥0∞ := fun j ↦ ∫⁻ ω, b j ω ∂ν with hbt
  set T : ℝ≥0∞ := ∑' j, oscAt (⇑f) j with hT
  have hTfin : T ≠ ⊤ := tsum_oscAt_ne_top hfloc
  set Q : ℝ≥0∞ := ∑' i, interdepSeries γ bt i * oscAt (⇑f) i with hQ
  have hbound : ∀ n : ℕ,
      ENNReal.ofReal |∫ σ, (f : (S → E) → ℝ) σ ∂μ - ∫ σ, (f : (S → E) → ℝ) σ ∂ν|
        ≤ c ^ n * T + Q := by
    intro n
    refine (isEstimate_comparisonVec hγq hμ hν hbm hb n f hfq).trans ?_
    have hle : ∀ i, comparisonVec γ bt n i ≤ c ^ n + interdepSeries γ bt i := by
      intro i
      refine add_le_add ?_ ?_
      · simpa using interdepIter_le γ hc (a := (1 : S → ℝ≥0∞)) (M := 1) (fun _ ↦ le_rfl) n i
      · exact ENNReal.sum_le_tsum (Finset.range n)
    calc (∑' i, comparisonVec γ bt n i * oscAt (⇑f) i)
        ≤ ∑' i, (c ^ n + interdepSeries γ bt i) * oscAt (⇑f) i :=
          ENNReal.tsum_le_tsum fun i ↦ by gcongr; exact hle i
      _ = ∑' i, (c ^ n * oscAt (⇑f) i + interdepSeries γ bt i * oscAt (⇑f) i) := by
          exact tsum_congr fun i ↦ by rw [add_mul]
      _ = c ^ n * T + Q := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
  have htend : Tendsto (fun n : ℕ ↦ c ^ n * T + Q) atTop (𝓝 Q) := by
    have h0 : Tendsto (fun n : ℕ ↦ c ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc1
    have h1 : Tendsto (fun n : ℕ ↦ c ^ n * T) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hTfin)
    have hconst : Tendsto (fun _ : ℕ ↦ Q) atTop (𝓝 Q) := tendsto_const_nhds
    simpa using h1.add hconst
  exact ge_of_tendsto htend (Filter.Eventually.of_forall hbound)

end Comparison820

/-! ### Georgii (8.22): conditioning a specification on part of the volume -/

section CondSpec

variable [DecidableEq S]

open scoped Classical in
/-- Georgii (8.22): the configuration `ω_V ζ_{S∖V}` which agrees with `ω` on `V` and with `ζ`
off `V`. -/
noncomputable def condCfg (V : Finset S) (ω ζ : S → E) : S → E :=
  fun k ↦ if k ∈ V then ω k else ζ k

variable {V W Δ Λ : Finset S} {ω ζ : S → E} {k : S}

omit [MeasurableSpace E] in
@[simp] lemma condCfg_apply_of_mem {k : S} (hk : k ∈ V) : condCfg V ω ζ k = ω k := by
  simp [condCfg, hk]

omit [MeasurableSpace E] in
@[simp] lemma condCfg_apply_of_notMem {k : S} (hk : k ∉ V) : condCfg V ω ζ k = ζ k := by
  simp [condCfg, hk]

omit [MeasurableSpace E] in
@[simp] lemma condCfg_empty (ω ζ : S → E) : condCfg (∅ : Finset S) ω ζ = ζ := by
  funext k; simp

omit [MeasurableSpace E] in
lemma condCfg_congr_left {ω ω' : S → E} (h : ∀ k ∈ V, ω k = ω' k) :
    condCfg V ω = condCfg V ω' := by
  funext ζ k
  by_cases hk : k ∈ V
  · simp [hk, h k hk]
  · simp [hk]

lemma measurable_condCfg (V : Finset S) (ω : S → E) : Measurable (condCfg V ω) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  by_cases hk : k ∈ V
  · simp [hk]
  · simpa [hk] using measurable_pi_apply (X := fun _ : S ↦ E) k

/-- The conditioning map is measurable from the `Λ`-boundary σ-algebra to the `Δ`-boundary
σ-algebra as soon as every site of `Λ` outside `Δ` is frozen. -/
lemma measurable_condCfg_cylinderEvents (h : ∀ k ∈ Λ, k ∉ Δ → k ∈ W) (ω : S → E) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S))ᶜ,
      cylinderEvents (X := fun _ : S ↦ E) ((Δ : Set S))ᶜ] (condCfg W ω) := by
  refine measurable_cylinderEvents_iff.2 fun k hk ↦ ?_
  simp only [Set.mem_compl_iff, Finset.mem_coe] at hk
  by_cases hkW : k ∈ W
  · simp [hkW]
  · have hkΛ : k ∉ Λ := fun hkΛ ↦ hkW (h k hkΛ hk)
    simpa [hkW] using
      measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (Δ := ((Λ : Set S))ᶜ) (i := k) hkΛ

/-! #### Properness: a specification kernel does not move the sites outside its volume -/

/-- Georgii's properness, in the form used in the proof of (8.22): `γ_Δ(·|ξ)` is carried by the
configurations agreeing with `ξ` off `Δ`, so freezing any set of sites disjoint from `Δ` back to
`ξ` does not change the measure. -/
theorem map_condCfg_eq_self (γ : Specification S E) (hWΔ : Disjoint W Δ) (ξ : S → E) :
    (γ Δ ξ).map (condCfg W ξ) = γ Δ ξ := by
  classical
  have hT : Measurable (condCfg W ξ) := measurable_condCfg W ξ
  have : IsProbabilityMeasure ((γ Δ ξ).map (condCfg W ξ)) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have hprop : Specification.IsProper γ := γ.isProper
  have hWΔ' : ∀ k, k ∈ W → k ∉ Δ := fun k hk hk' ↦
    (Finset.disjoint_left.1 hWΔ hk) hk'
  refine ext_of_generate_finite (squareCylindersMeas S E)
      (generateFrom_squareCylindersMeas S E) (isPiSystem_squareCylindersMeas S E) ?_ ?_
  · rintro C ⟨J, t, ht, rfl⟩
    have htm : ∀ j, MeasurableSet (t j) := fun j ↦ Set.mem_univ_pi.1 ht j
    set A' : Set (S → E) := (((J \ W : Finset S) : Finset S) : Set S).pi t with hA'def
    set B : Set (S → E) := (((J ∩ W : Finset S) : Finset S) : Set S).pi t with hBdef
    have hmemA' : ∀ σ : S → E, σ ∈ A' ↔ ∀ j ∈ J, j ∉ W → σ j ∈ t j := by
      intro σ
      simp only [hA'def, Set.mem_pi, Finset.mem_coe, Finset.mem_sdiff]
      exact ⟨fun h j hj hjW ↦ h j ⟨hj, hjW⟩, fun h j hj ↦ h j hj.1 hj.2⟩
    have hmemB : ∀ σ : S → E, σ ∈ B ↔ ∀ j ∈ J, j ∈ W → σ j ∈ t j := by
      intro σ
      simp only [hBdef, Set.mem_pi, Finset.mem_coe, Finset.mem_inter]
      exact ⟨fun h j hj hjW ↦ h j ⟨hj, hjW⟩, fun h j hj ↦ h j hj.1 hj.2⟩
    have hmemJ : ∀ σ : S → E, σ ∈ (J : Set S).pi t ↔ ∀ j ∈ J, σ j ∈ t j := by
      intro σ; simp only [Set.mem_pi, Finset.mem_coe]
    have hsplit : ((J : Set S).pi t) = A' ∩ B := by
      ext σ
      rw [Set.mem_inter_iff, hmemJ, hmemA', hmemB]
      refine ⟨fun h ↦ ⟨fun j hj _ ↦ h j hj, fun j hj _ ↦ h j hj⟩, fun h j hj ↦ ?_⟩
      by_cases hjW : j ∈ W
      · exact h.2 j hj hjW
      · exact h.1 j hj hjW
    have hBmeas :
        MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Set S)ᶜ)] B := by
      have hBeq : B = ⋂ j ∈ (J ∩ W : Finset S), (fun σ : S → E ↦ σ j) ⁻¹' (t j) := by
        ext σ
        simp only [hBdef, Set.mem_pi, Finset.mem_coe, Set.mem_iInter, Set.mem_preimage]
      rw [hBeq]
      refine Finset.measurableSet_biInter _ fun j hj ↦ ?_
      have hjW : j ∈ W := (Finset.mem_inter.1 hj).2
      exact (htm j).preimage
        (measurable_cylinderEvent_apply (i := j) (X := fun _ : S ↦ E)
          (by simpa using hWΔ' j hjW))
    have hA'meas : MeasurableSet A' := measurableSet_finset_pi _ t htm
    have hmemT : ∀ σ : S → E,
        (condCfg W ξ σ) ∈ (J : Set S).pi t ↔ (σ ∈ A' ∧ ξ ∈ B) := by
      intro σ
      rw [hmemJ, hmemA', hmemB]
      constructor
      · intro h
        refine ⟨fun j hj hjW ↦ ?_, fun j hj hjW ↦ ?_⟩
        · simpa [condCfg_apply_of_notMem hjW] using h j hj
        · simpa [condCfg_apply_of_mem hjW] using h j hj
      · rintro ⟨h1, h2⟩ j hj
        by_cases hjW : j ∈ W
        · simpa [condCfg_apply_of_mem hjW] using h2 j hj hjW
        · simpa [condCfg_apply_of_notMem hjW] using h1 j hj hjW
    have hpre : (condCfg W ξ) ⁻¹' ((J : Set S).pi t)
        = if ξ ∈ B then A' else (∅ : Set (S → E)) := by
      ext σ
      by_cases hξB : ξ ∈ B <;> simp [Set.mem_preimage, hmemT σ, hξB]
    rw [Measure.map_apply hT (measurableSet_finset_pi J t htm), hpre, hsplit,
      hprop.inter_eq_indicator_mul Δ hA'meas hBmeas ξ]
    by_cases hξB : ξ ∈ B
    · simp [hξB, Set.indicator_of_mem]
    · simp [hξB, Set.indicator_of_notMem]
  · rw [Measure.map_apply hT MeasurableSet.univ]
    simp

/-- Set form of `map_condCfg_eq_self`. -/
theorem measure_preimage_condCfg (γ : Specification S E) (hWΔ : Disjoint W Δ) (ξ : S → E)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    γ Δ ξ (condCfg W ξ ⁻¹' A) = γ Δ ξ A := by
  conv_rhs => rw [← map_condCfg_eq_self γ hWΔ ξ]
  rw [Measure.map_apply (measurable_condCfg W ξ) hA]

omit [DecidableEq S] in
/-- Georgii (8.21): the empty-volume kernel of a specification is the Dirac kernel. -/
lemma apply_empty_eq_dirac (γ : Specification S E) (ξ : S → E) :
    γ ∅ ξ = Measure.dirac ξ := by
  ext A hA
  have hcyl : cylinderEvents (X := fun _ : S ↦ E) (((∅ : Finset S) : Set S))ᶜ
      = MeasurableSpace.pi := by
    rw [Finset.coe_empty, compl_empty, cylinderEvents_univ]
  have hA' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (((∅ : Finset S) : Set S))ᶜ] A := by
    rw [hcyl]; exact hA
  have h := (γ.isProper ∅).inter_eq_indicator_mul cylinderEvents_le_pi MeasurableSet.univ hA' ξ
  rw [Set.univ_inter] at h
  rw [h, measure_univ, mul_one, Measure.dirac_apply' _ hA]

/-! #### The conditioned specification `γ^{(V,ω)}` -/

/-- The measurability of the conditioning map used to define `γ^{(V,ω)}_Λ`. -/
lemma measurable_condCfg_condSpec (V Λ : Finset S) (ω : S → E) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S))ᶜ,
      cylinderEvents (X := fun _ : S ↦ E) (((Λ ∩ V : Finset S) : Set S))ᶜ]
      (condCfg (Λ \ V) ω) :=
  measurable_condCfg_cylinderEvents (by
    intro k hk hk'
    simp only [Finset.mem_inter, not_and] at hk'
    simp [Finset.mem_sdiff, hk, hk' hk]) ω

/-- Properness of the conditioned kernels. -/
lemma isProper_comap_condCfg (γ : Specification S E) {Δ Λ W : Finset S} (ω : S → E)
    (hΔΛ : Δ ⊆ Λ) (hWΛ : W ⊆ Λ)
    (hmeas : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S))ᶜ,
      cylinderEvents (X := fun _ : S ↦ E) ((Δ : Set S))ᶜ] (condCfg W ω)) :
    Kernel.IsProper ((γ Δ).comap (condCfg W ω) hmeas) := by
  rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
  intro A hA B hB ζ
  have hBle : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Set S))ᶜ] B :=
    cylinderEvents_mono (Set.compl_subset_compl.2 (by exact_mod_cast hΔΛ)) _ hB
  have hind : B.indicator (1 : (S → E) → ℝ≥0∞) (condCfg W ω ζ) = B.indicator 1 ζ :=
    (measurable_const.indicator hB).dependsOn_of_cylinderEvents fun k hk ↦
      condCfg_apply_of_notMem fun h ↦ hk (by simpa using hWΛ h)
  simp only [Kernel.comap_apply]
  rw [(γ.isProper Δ).inter_eq_indicator_mul cylinderEvents_le_pi hA hBle (condCfg W ω ζ), hind]

/-- The key computation behind Georgii's Lemma (8.22): since `γ_{Δ₂}(·|ξ)` does not move the sites
outside `Δ₂`, freezing the sites of `W` back to `ξ` before applying `γ_{Δ₁}` changes nothing. -/
lemma bind_comap_condCfg (γ : Specification S E) {Δ₁ Δ₂ W : Finset S} (hΔ : Δ₁ ⊆ Δ₂)
    (hdisj : Disjoint W Δ₂) (ξ : S → E) :
    (γ Δ₂ ξ).bind (fun η ↦ γ Δ₁ (condCfg W ξ η)) = γ Δ₂ ξ := by
  have h1 : (fun η ↦ γ Δ₁ (condCfg W ξ η)) = (⇑(γ Δ₁)) ∘ (condCfg W ξ) := rfl
  rw [h1, ← Measure.bind_map (measurable_condCfg W ξ) (γ.measurable_kernel_toMeasure Δ₁),
    map_condCfg_eq_self γ hdisj ξ]
  exact Specification.bind (γ := γ) hΔ ξ

/-- **Georgii, Lemma (8.22).** The conditioned kernels are consistent. -/
lemma isConsistent_comap_condCfg (γ : Specification S E) (V : Finset S) (ω : S → E) :
    IsConsistent (fun Λ ↦ (γ (Λ ∩ V)).comap (condCfg (Λ \ V) ω)
      (measurable_condCfg_condSpec V Λ ω)) := by
  intro Λ₁ Λ₂ hΛ
  refine Kernel.ext fun ζ ↦ ?_
  set ξ : S → E := condCfg (Λ₂ \ V) ω ζ with hξ
  have hω : condCfg (Λ₁ \ V) ω = condCfg (Λ₁ \ V) ξ := by
    refine condCfg_congr_left fun k hk ↦ ?_
    have hk' : k ∈ Λ₂ \ V := by
      simp only [Finset.mem_sdiff] at hk ⊢
      exact ⟨hΛ hk.1, hk.2⟩
    rw [hξ, condCfg_apply_of_mem hk']
  have hdisj : Disjoint (Λ₁ \ V) (Λ₂ ∩ V) :=
    Finset.disjoint_left.2 fun a ha ha' ↦ (Finset.mem_sdiff.1 ha).2 (Finset.mem_inter.1 ha').2
  have key : (γ (Λ₂ ∩ V) ξ).bind (fun η ↦ γ (Λ₁ ∩ V) (condCfg (Λ₁ \ V) ω η))
      = γ (Λ₂ ∩ V) ξ := by
    rw [hω]
    exact bind_comap_condCfg γ (Finset.inter_subset_inter hΛ (Finset.Subset.refl V)) hdisj ξ
  rw [Kernel.comp_apply]
  exact key

/-- **Georgii, Lemma (8.22).** The specification `γ^{(V,ω)}` obtained from `γ` by conditioning on
the configuration `ω` outside `V`: `γ^{(V,ω)}_Λ(A|ζ) = γ_{Λ∩V}(A | ω_Λ ζ_{S∖Λ})`.

Since `γ_{Λ∩V}(A|·)` does not depend on the sites of `Λ ∩ V`, only the sites of `Λ \ V` need to be
frozen, which is the form used here. -/
noncomputable def condSpec (γ : Specification S E) (V : Finset S) (ω : S → E) :
    Specification S E where
  toFun Λ := (γ (Λ ∩ V)).comap (condCfg (Λ \ V) ω) (measurable_condCfg_condSpec V Λ ω)
  isConsistent' := isConsistent_comap_condCfg γ V ω
  isMarkovKernel' Λ := Kernel.IsMarkovKernel.comap _ (measurable_condCfg_condSpec V Λ ω)
  isProper' Λ :=
    isProper_comap_condCfg γ ω Finset.inter_subset_left Finset.sdiff_subset
      (measurable_condCfg_condSpec V Λ ω)

@[simp] lemma condSpec_apply (γ : Specification S E) (V : Finset S) (ω : S → E) (Λ : Finset S)
    (ζ : S → E) : condSpec γ V ω Λ ζ = γ (Λ ∩ V) (condCfg (Λ \ V) ω ζ) :=
  Kernel.comap_apply (γ (Λ ∩ V)) (measurable_condCfg_condSpec V Λ ω) ζ

/-- `γ^{(V,ω)}_Λ = γ_Λ` for every finite volume `Λ ⊆ V`; Georgii (8.22)(i), `γ^{(S,ω)} = γ`, is
the case `V = S`. -/
lemma condSpec_apply_of_subset (γ : Specification S E) {V Λ : Finset S} (h : Λ ⊆ V) (ω ζ : S → E) :
    condSpec γ V ω Λ ζ = γ Λ ζ := by
  rw [condSpec_apply, Finset.inter_eq_left.2 h, Finset.sdiff_eq_empty_iff_subset.2 h, condCfg_empty]

/-- Georgii (8.22), the frozen sites: if `i ∉ V` then `γ^{(V,ω)}_i(·|ζ) = δ_{ω_i ζ_{S∖i}}`. -/
lemma condSpec_singleton_of_notMem (γ : Specification S E) {V : Finset S} {i : S} (hi : i ∉ V)
    (ω ζ : S → E) :
    condSpec γ V ω {i} ζ = Measure.dirac (condCfg {i} ω ζ) := by
  rw [condSpec_apply, Finset.singleton_inter_of_notMem hi,
    Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_left.2 hi), apply_empty_eq_dirac]

/-! #### Precomposition of observables with a configuration map -/

/-- Precomposition of a bounded observable with a map of configurations. -/
noncomputable def precompLp (T : (S → E) → (S → E)) (f : lp (fun _ : S → E ↦ ℝ) ∞) :
    lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨(⇑f) ∘ T, memℓp_infty ⟨‖f‖, by
    rintro _ ⟨x, rfl⟩; exact lp.norm_apply_le_norm ENNReal.top_ne_zero f _⟩⟩

omit [MeasurableSpace E] [DecidableEq S] in
@[simp] lemma precompLp_apply (T : (S → E) → (S → E)) (f : lp (fun _ : S → E ↦ ℝ) ∞)
    (σ : S → E) : (precompLp T f : (S → E) → ℝ) σ = (f : (S → E) → ℝ) (T σ) := rfl

omit [MeasurableSpace E] [DecidableEq S] in
lemma dist_precompLp_le (T : (S → E) → (S → E)) (f g : lp (fun _ : S → E ↦ ℝ) ∞) :
    dist (precompLp T f) (precompLp T g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (norm_nonneg _) fun σ ↦ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, precompLp_apply, precompLp_apply]
  have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (f - g) (T σ)
  rwa [lp.coeFn_sub, Pi.sub_apply] at h

omit [DecidableEq S] in
lemma precompLp_mem_localFunctions {T : (S → E) → (S → E)} (hT : Measurable T)
    (hTdep : ∀ (Δ : Set S) (x y : S → E), (∀ k ∈ Δ, x k = y k) → ∀ k ∈ Δ, T x k = T y k)
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctions S E) :
    precompLp T f ∈ localFunctions S E := by
  obtain ⟨Λ₀, hΛ₀⟩ := mem_localFunctions.1 hf
  have hmeas : Measurable (⇑f) := (mem_localFunctionsOn.1 hΛ₀).mono cylinderEvents_le_pi le_rfl
  have hdep : DependsOn (⇑f) (Λ₀ : Set S) :=
    (mem_localFunctionsOn.1 hΛ₀).dependsOn_of_cylinderEvents
  refine mem_localFunctions.2 ⟨Λ₀, Measurable.cylinderEvents_of_dependsOn (hmeas.comp hT) ?_⟩
  intro x y hxy
  exact hdep (hTdep _ x y hxy)

omit [DecidableEq S] in
lemma precompLp_mem_quasilocalFunctions {T : (S → E) → (S → E)} (hT : Measurable T)
    (hTdep : ∀ (Δ : Set S) (x y : S → E), (∀ k ∈ Δ, x k = y k) → ∀ k ∈ Δ, T x k = T y k)
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E) :
    precompLp T f ∈ quasilocalFunctions S E := by
  rw [mem_quasilocalFunctions_iff_mem_closure, Metric.mem_closure_iff] at hf ⊢
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := hf ε hε
  exact ⟨precompLp T g, precompLp_mem_localFunctions hT hTdep hg,
    lt_of_le_of_lt (dist_precompLp_le T f g) hfg⟩

/-- **Georgii (8.22)(iv).** `C_{ij}(γ^{(V,ω)}) = 1_V(i) C_{ij}(γ)`. -/
theorem interdep_condSpec (γ : Specification S E) (V : Finset S) (ω : S → E) (i j : S) :
    interdep (condSpec γ V ω) i j = if i ∈ V then interdep γ i j else 0 := by
  split_ifs with hi
  · have hker : ∀ ζ : S → E, proj (condSpec γ V ω) i ζ = proj γ i ζ := fun ζ ↦ by
      rw [proj, proj, condSpec_apply_of_subset γ (Finset.singleton_subset_iff.2 hi) ω ζ]
    simp only [interdep_eq, hker]
  · have hmi : Measurable (fun σ : S → E ↦ σ i) := measurable_pi_apply i
    have hker : ∀ ζ : S → E, proj (condSpec γ V ω) i ζ = Measure.dirac (ω i) := fun ζ ↦ by
      rw [proj, condSpec_singleton_of_notMem γ hi ω ζ, Measure.map_dirac' hmi,
        condCfg_apply_of_mem (Finset.mem_singleton_self i)]
    simp only [interdep_eq, hker, unifDist_self]
    exact le_antisymm (iSup₂_le fun _ _ ↦ iSup_le fun _ ↦ le_rfl) bot_le

lemma interdep_condSpec_le (γ : Specification S E) (V : Finset S) (ω : S → E) (i j : S) :
    interdep (condSpec γ V ω) i j ≤ interdep γ i j := by
  rw [interdep_condSpec]; split <;> simp

/-- **Georgii (8.22)(iii).** `γ^{(V,ω)}` inherits quasilocality. -/
theorem isQuasilocal_condSpec {γ : Specification S E} (hγq : γ.IsQuasilocal) (V : Finset S)
    (ω : S → E) :
    (condSpec γ V ω).IsQuasilocal := by
  intro Λ f hf
  have heq : Specification.action (condSpec γ V ω) Λ f
      = precompLp (condCfg (Λ \ V) ω) (Specification.action γ (Λ ∩ V) f) := by
    refine Subtype.ext (funext fun η ↦ ?_)
    have : (Specification.action (condSpec γ V ω) Λ f : (S → E) → ℝ) η
        = ∫ x, (f : (S → E) → ℝ) x ∂(condSpec γ V ω Λ η) := rfl
    rw [this, condSpec_apply]
    rfl
  rw [heq]
  refine precompLp_mem_quasilocalFunctions (measurable_condCfg _ _) ?_ (hγq (Λ ∩ V) f hf)
  intro Δ x y hxy k hk
  by_cases hkW : k ∈ Λ \ V
  · simp [hkW]
  · simp [hkW, hxy k hk]

/-- **Georgii (8.22)(iv).** `γ^{(V,ω)}` inherits Dobrushin's condition. -/
theorem isDobrushin_condSpec {γ : Specification S E} (hd : IsDobrushin γ) (V : Finset S)
    (ω : S → E) :
    IsDobrushin (condSpec γ V ω) := by
  obtain ⟨hq, c, hc, hle⟩ := hd
  exact ⟨isQuasilocal_condSpec hq V ω, c, hc, fun i ↦ (ENNReal.tsum_le_tsum fun j ↦ interdep_condSpec_le γ V ω i j).trans (hle i)⟩

/-- **Georgii (8.22)(ii).** For finite `V`, `γ_V(·|ω)` is a Gibbs measure for `γ^{(V,ω)}`. -/
theorem bind_condSpec_eq (γ : Specification S E) (V : Finset S) (ω : S → E) (Λ : Finset S) :
    (γ V ω).bind (condSpec γ V ω Λ) = γ V ω := by
  have h : ⇑(condSpec γ V ω Λ) = fun η ↦ γ (Λ ∩ V) (condCfg (Λ \ V) ω η) :=
    funext fun η ↦ condSpec_apply γ V ω Λ η
  rw [h]
  exact bind_comap_condCfg γ Finset.inter_subset_right
    (Finset.disjoint_left.2 fun a ha ha' ↦ (Finset.mem_sdiff.1 ha).2 ha') ω

end CondSpec

/-! ### Georgii (8.23): the Cauchy estimate for the finite-volume Gibbs distributions -/

section Cauchy

variable [DecidableEq S] {γ : Specification S E}

omit [DecidableEq S] in
/-- `C(γ)^n` is monotone in the interdependence matrix. -/
lemma interdepIter_mono_matrix {γ' : Specification S E}
    (h : ∀ i j, interdep γ' i j ≤ interdep γ i j) (n : ℕ) (a : S → ℝ≥0∞) (i : S) :
    interdepIter γ' n a i ≤ interdepIter γ n a i := by
  induction n generalizing i with
  | zero => exact le_rfl
  | succ n ih => exact ENNReal.tsum_le_tsum fun j ↦ mul_le_mul' (h i j) (ih j)

omit [DecidableEq S] in
lemma interdepSeries_mono_matrix {γ' : Specification S E}
    (h : ∀ i j, interdep γ' i j ≤ interdep γ i j) (a : S → ℝ≥0∞) (i : S) :
    interdepSeries γ' a i ≤ interdepSeries γ a i :=
  ENNReal.tsum_le_tsum fun n ↦ interdepIter_mono_matrix h n a i

omit [DecidableEq S] in
lemma interdepIter_mono_vec (γ : Specification S E) {a b : S → ℝ≥0∞} (hab : ∀ j, a j ≤ b j)
    (n : ℕ) (i : S) : interdepIter γ n a i ≤ interdepIter γ n b i := by
  induction n generalizing i with
  | zero => exact hab i
  | succ n ih => exact ENNReal.tsum_le_tsum fun j ↦ mul_le_mul' le_rfl (ih j)

omit [DecidableEq S] in
lemma interdepSeries_mono_vec (γ : Specification S E) {a b : S → ℝ≥0∞} (hab : ∀ j, a j ≤ b j)
    (i : S) : interdepSeries γ a i ≤ interdepSeries γ b i :=
  ENNReal.tsum_le_tsum fun n ↦ interdepIter_mono_vec γ hab n i

omit [DecidableEq S] in
lemma interdepIter_add (γ : Specification S E) (a b : S → ℝ≥0∞) (n : ℕ) (i : S) :
    interdepIter γ n (a + b) i = interdepIter γ n a i + interdepIter γ n b i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp only [interdepIter_succ]
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun j ↦ by rw [ih j, mul_add]

variable (γ) in
/-- Georgii's `∑_{j ∈ V∖Δ} D_{ij}(γ)`, for `V = S`: the total weight `D(γ)` puts on the sites
outside the finite volume `Δ`. -/
noncomputable def interdepTail (Δ : Finset S) (i : S) : ℝ≥0∞ :=
  interdepSeries γ (fun j ↦ if j ∈ Δ then 0 else 1) i

lemma interdepTail_antitone (γ : Specification S E) {Δ Δ' : Finset S} (h : Δ ⊆ Δ') (i : S) :
    interdepTail γ Δ' i ≤ interdepTail γ Δ i :=
  interdepSeries_mono_vec γ (fun j ↦ by
    by_cases hj : j ∈ Δ
    · simp [hj, h hj]
    · by_cases hj' : j ∈ Δ' <;> simp [hj, hj']) i

/-! #### Tail estimates for `D(γ) = ∑_n C(γ)^n` -/

omit [DecidableEq S] in
/-- Splitting a `tsum` at a finite set: the terms indexed by `J` are bounded by `δ`, the others
by `h`. -/
lemma tsum_le_card_mul_add {ι : Type*} [DecidableEq ι] (g h : ι → ℝ≥0∞) (J : Finset ι)
    (δ : ℝ≥0∞)
    (h1 : ∀ j ∈ J, g j ≤ δ) (h2 : ∀ j, j ∉ J → g j ≤ h j) :
    ∑' j, g j ≤ J.card * δ + ∑' j, (if j ∈ J then 0 else h j) := by
  classical
  have hstep : ∀ j, g j ≤ (if j ∈ J then δ else 0) + (if j ∈ J then 0 else h j) := by
    intro j
    by_cases hj : j ∈ J
    · simpa [hj] using h1 j hj
    · simpa [hj] using h2 j hj
  have hsum : ∑ j ∈ J, (if j ∈ J then δ else 0) = ∑ _j ∈ J, δ :=
    Finset.sum_congr rfl fun j hj ↦ by simp [hj]
  calc ∑' j, g j ≤ ∑' j, ((if j ∈ J then δ else 0) + (if j ∈ J then 0 else h j)) :=
        ENNReal.tsum_le_tsum hstep
    _ = (∑' j, if j ∈ J then δ else 0) + ∑' j, (if j ∈ J then 0 else h j) := ENNReal.tsum_add
    _ = J.card * δ + ∑' j, (if j ∈ J then 0 else h j) := by
        congr 1
        rw [tsum_eq_sum (s := J) fun b hb ↦ by simp [hb], hsum, Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq S] in
lemma tsum_ite_compl_eq {ι : Type*} [DecidableEq ι] (f : ι → ℝ≥0∞) (J : Finset ι) :
    ∑' j, (if j ∈ J then 0 else f j) = ∑' j : {x : ι // x ∉ J}, f j := by
  have hsub : ∑' j : {x : ι // x ∉ J}, f j = ∑' j, Set.indicator {x : ι | x ∉ J} f j :=
    tsum_subtype {x : ι | x ∉ J} f
  rw [hsub]
  exact tsum_congr fun j ↦ by by_cases hj : j ∈ J <;> simp [hj]

omit [DecidableEq S] in
/-- The tail of a finite `ℝ≥0∞`-valued sum can be made arbitrarily small. -/
lemma exists_tsum_ite_compl_le {ι : Type*} [DecidableEq ι] {f : ι → ℝ≥0∞}
    (hf : ∑' j, f j ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ J : Finset ι, ∑' j, (if j ∈ J then 0 else f j) ≤ ε := by
  have h := ENNReal.tendsto_tsum_compl_atTop_zero hf
  rw [ENNReal.tendsto_nhds_zero] at h
  obtain ⟨J, hJ⟩ := (h ε hε).exists
  exact ⟨J, by rw [tsum_ite_compl_eq]; exact hJ⟩

/-- For each fixed number of steps, `C(γ)^n 1_{S∖Δ}` can be made arbitrarily small by taking `Δ`
large. -/
theorem exists_interdepIter_compl_le (hd : IsDobrushin γ) (n : ℕ) (i : S) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ Δ : Finset S, interdepIter γ n (fun j ↦ if j ∈ Δ then 0 else 1) i ≤ ε := by
  classical
  obtain ⟨-, c, hc1, hc⟩ := hd
  have hcne : c ≠ ⊤ := ne_top_of_lt hc1
  have hbdd : ∀ (Δ : Finset S) (m : ℕ) (j : S),
      interdepIter γ m (fun k ↦ if k ∈ Δ then 0 else 1) j ≤ 1 := by
    intro Δ m j
    refine (interdepIter_le γ hc (M := 1) (fun k ↦ by split <;> simp) m j).trans ?_
    simpa using pow_le_one₀ (by simp : (0 : ℝ≥0∞) ≤ c) hc1.le
  have hfin : ∀ i : S, ∑' j, interdep γ i j ≠ ⊤ := fun i ↦ ne_top_of_le_ne_top hcne (hc i)
  suffices H : ∀ (n : ℕ) (i : S) (ε : ℝ≥0∞), 0 < ε →
      ∃ Δ : Finset S, interdepIter γ n (fun j ↦ if j ∈ Δ then 0 else 1) i ≤ ε from H n i ε hε
  intro n
  induction n with
  | zero => exact fun i ε _ ↦ ⟨{i}, by simp⟩
  | succ n ih =>
    intro i ε hε
    obtain ⟨J, hJ⟩ := exists_tsum_ite_compl_le (hfin i) (ENNReal.half_pos hε.ne')
    set δ : ℝ≥0∞ := (ε / 2) / (J.card + 1) with hδ
    have hδpos : 0 < δ := ENNReal.div_pos (ENNReal.half_pos hε.ne').ne' (by simp)
    choose Δf hΔf using fun j : S ↦ ih j δ hδpos
    refine ⟨J.sup Δf, ?_⟩
    have hsub : ∀ j ∈ J, Δf j ⊆ J.sup Δf := fun j hj ↦ Finset.le_sup hj
    have hmono : ∀ j ∈ J,
        interdepIter γ n (fun k ↦ if k ∈ J.sup Δf then 0 else 1) j ≤ δ := by
      intro j hj
      refine le_trans (interdepIter_mono_vec γ (fun k ↦ ?_) n j) (hΔf j)
      by_cases hk : k ∈ Δf j
      · simp [hk, hsub j hj hk]
      · by_cases hk' : k ∈ J.sup Δf <;> simp [hk, hk']
    have hstep := tsum_le_card_mul_add
      (g := fun j ↦ interdep γ i j * interdepIter γ n (fun k ↦ if k ∈ J.sup Δf then 0 else 1) j)
      (h := fun j ↦ interdep γ i j) J δ
      (fun j hj ↦ le_trans (mul_le_mul' (interdep_le_one γ i j) (hmono j hj)) (by simp))
      (fun j _ ↦ by
        refine le_trans (mul_le_mul' le_rfl (hbdd _ n j)) (by simp))
    have hcard : (J.card : ℝ≥0∞) * δ ≤ ε / 2 := by
      calc (J.card : ℝ≥0∞) * δ ≤ ((J.card : ℝ≥0∞) + 1) * δ := by gcongr; exact le_self_add
        _ = ε / 2 := ENNReal.mul_div_cancel' (by simp) (by simp)
    calc interdepIter γ (n + 1) (fun k ↦ if k ∈ J.sup Δf then 0 else 1) i
        = ∑' j, interdep γ i j
            * interdepIter γ n (fun k ↦ if k ∈ J.sup Δf then 0 else 1) j := rfl
      _ ≤ (J.card : ℝ≥0∞) * δ + ∑' j, (if j ∈ J then 0 else interdep γ i j) := hstep
      _ ≤ ε / 2 + ε / 2 := add_le_add hcard hJ
      _ = ε := ENNReal.add_halves ε

/-- **Georgii (8.23), step 1.** `∑_{j ∉ Δ} D_{ij}(γ) → 0` as `Δ ↑ S`; this is the finiteness
`∑_{j ∈ S} D_{ij}(γ) < ∞` used by Georgii to make the net `(γ_Δ)` Cauchy. -/
theorem tendsto_interdepTail (hd : IsDobrushin γ) (i : S) :
    Tendsto (fun Δ : Finset S ↦ interdepTail γ Δ i) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨hq, c, hc1, hc⟩ := hd
  have hgeom : ∑' n : ℕ, c ^ n ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hc1).ne'
  obtain ⟨J, hJ⟩ := exists_tsum_ite_compl_le (f := fun n : ℕ ↦ c ^ n) hgeom
    (ENNReal.half_pos hε.ne')
  set δ : ℝ≥0∞ := (ε / 2) / (J.card + 1) with hδ
  have hδpos : 0 < δ := ENNReal.div_pos (ENNReal.half_pos hε.ne').ne' (by simp)
  choose Δf hΔf using fun n : ℕ ↦ exists_interdepIter_compl_le ⟨hq, c, hc1, hc⟩ n i hδpos
  set Δ₀ : Finset S := J.sup Δf with hΔ₀
  have hsub : ∀ n ∈ J, Δf n ⊆ Δ₀ := fun n hn ↦ Finset.le_sup hn
  have hmono : ∀ n ∈ J, interdepIter γ n (fun k ↦ if k ∈ Δ₀ then 0 else 1) i ≤ δ := by
    intro n hn
    refine le_trans (interdepIter_mono_vec γ (fun k ↦ ?_) n i) (hΔf n)
    by_cases hk : k ∈ Δf n
    · simp [hk, hsub n hn hk]
    · by_cases hk' : k ∈ Δ₀ <;> simp [hk, hk']
  have hbound : interdepTail γ Δ₀ i ≤ ε := by
    have hstep := tsum_le_card_mul_add
      (g := fun n : ℕ ↦ interdepIter γ n (fun k ↦ if k ∈ Δ₀ then 0 else 1) i)
      (h := fun n : ℕ ↦ c ^ n) J δ hmono
      (fun n _ ↦ by
        simpa using interdepIter_le γ hc (M := 1) (fun k ↦ by split <;> simp) n i)
    have hcard : (J.card : ℝ≥0∞) * δ ≤ ε / 2 := by
      calc (J.card : ℝ≥0∞) * δ ≤ ((J.card : ℝ≥0∞) + 1) * δ := by gcongr; exact le_self_add
        _ = ε / 2 := ENNReal.mul_div_cancel' (by simp) (by simp)
    calc interdepTail γ Δ₀ i
        = ∑' n : ℕ, interdepIter γ n (fun k ↦ if k ∈ Δ₀ then 0 else 1) i := rfl
      _ ≤ (J.card : ℝ≥0∞) * δ + ∑' n : ℕ, (if n ∈ J then 0 else c ^ n) := hstep
      _ ≤ ε / 2 + ε / 2 := add_le_add hcard hJ
      _ = ε := ENNReal.add_halves ε
  filter_upwards [Filter.eventually_ge_atTop Δ₀] with Δ hΔ
  exact (interdepTail_antitone γ hΔ i).trans hbound

/-- From `|x.toReal - y.toReal| ≤ c` for finite `x`, `y`, the one-sided `ℝ≥0∞` bound
`y ≤ x + c`. -/
private lemma le_add_of_ofReal_abs_toReal_sub_le {x y c : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤)
    (h : ENNReal.ofReal |x.toReal - y.toReal| ≤ c) : y ≤ x + c := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  have h1 : ENNReal.ofReal (y.toReal - x.toReal) ≤ c :=
    le_trans (ENNReal.ofReal_le_ofReal (by
      rw [abs_sub_comm]; exact le_abs_self _)) h
  have h2 : y.toReal - x.toReal ≤ c.toReal := (ENNReal.ofReal_le_iff_le_toReal hc).1 h1
  have h3 : y.toReal ≤ x.toReal + c.toReal := by linarith
  calc y = ENNReal.ofReal y.toReal := (ENNReal.ofReal_toReal hy).symm
    _ ≤ ENNReal.ofReal (x.toReal + c.toReal) := ENNReal.ofReal_le_ofReal h3
    _ = ENNReal.ofReal x.toReal + ENNReal.ofReal c.toReal :=
        ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = x + c := by rw [ENNReal.ofReal_toReal hx, ENNReal.ofReal_toReal hc]

/-- **Georgii (8.23), step 1**, the Cauchy estimate. For a `Λ`-local event `A` and `Δ ⊆ Δ'`,
`γ_{Δ'}(A|ω) ≤ γ_Δ(A|ω) + ∑_{i ∈ Λ} ∑_{j ∉ Δ} D_{ij}(γ)`, by the comparison Theorem (8.20)
applied to the conditioned specifications `γ^{(Δ,ω)}` and `γ^{(Δ',ω)}` of Lemma (8.22). Georgii's
sharper `∑_{j ∈ Δ'∖Δ}` form is not needed here: the proof compares with `b_j = 1` off `Δ`. -/
theorem measure_le_add_interdepTail (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ)
    {Λ Δ Δ' : Finset S} (hΔ : Δ ⊆ Δ') (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    γ Δ' ω A ≤ γ Δ ω A + ∑ i ∈ Λ, interdepTail γ Δ i := by
  classical
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  set bt : S → ℝ≥0∞ := fun j ↦ if j ∈ Δ then 0 else 1 with hbt
  set b : S → (S → E) → ℝ≥0∞ := fun j _ ↦ bt j with hbdef
  have hbm : ∀ i, Measurable (b i) := fun _ ↦ measurable_const
  have hbb : ∀ i ζ, unifDist (proj (condSpec γ Δ ω) i ζ) (proj (condSpec γ Δ' ω) i ζ)
      ≤ b i ζ := by
    intro i ζ
    by_cases hi : i ∈ Δ
    · have h1 : condSpec γ Δ ω {i} ζ = γ {i} ζ :=
        condSpec_apply_of_subset γ (Finset.singleton_subset_iff.2 hi) ω ζ
      have h2 : condSpec γ Δ' ω {i} ζ = γ {i} ζ :=
        condSpec_apply_of_subset γ (Finset.singleton_subset_iff.2 (hΔ hi)) ω ζ
      simp [proj, h1, h2]
    · simpa [hbdef, hbt, hi] using
        unifDist_le_one (α₁ := proj (condSpec γ Δ ω) i ζ)
          (α₂ := proj (condSpec γ Δ' ω) i ζ)
  have hvec : (fun j ↦ ∫⁻ ζ, b j ζ ∂(γ Δ' ω)) = bt := by
    funext j; simp [hbdef]
  have hcomp := comparison (γ := condSpec γ Δ ω) (γ' := condSpec γ Δ' ω)
      (μ := γ Δ ω) (ν := γ Δ' ω)
      (isQuasilocal_condSpec hγq Δ ω) (isDobrushin_condSpec hd Δ ω)
      (fun i ↦ bind_condSpec_eq γ Δ ω {i}) (fun i ↦ bind_condSpec_eq γ Δ' ω {i}) hbm hbb
  rw [hvec] at hcomp
  have hloc : (indicatorLp A : lp (fun _ : S → E ↦ ℝ) ∞) ∈ localFunctions S E :=
    indicatorLp_mem_localFunctions (mem_localEvents_of_cylinderEvents Λ hA)
  have hest := hcomp (indicatorLp A) hloc
  have hint : ∀ (μ : Measure (S → E)), IsProbabilityMeasure μ →
      ∫ σ, (indicatorLp (S := S) (E := E) A : (S → E) → ℝ) σ ∂μ = (μ A).toReal := by
    intro μ _
    rw [show ⇑(indicatorLp (S := S) (E := E) A) = A.indicator (fun _ ↦ (1 : ℝ)) from rfl,
      integral_indicator_const (1 : ℝ) hAm]
    simp [measureReal_def]
  rw [hint _ inferInstance, hint _ inferInstance] at hest
  have hoscz : ∀ i, i ∉ Λ → oscAt (⇑(indicatorLp (S := S) (E := E) A)) i = 0 := by
    intro i hi
    refine oscAt_eq_zero_of_dependsOn ?_ (fun hmem ↦ hi (Finset.mem_coe.1 hmem))
    exact (measurable_const.indicator hA).dependsOn_of_cylinderEvents
  have hosc1 : ∀ i, oscAt (⇑(indicatorLp (S := S) (E := E) A)) i ≤ 1 := by
    intro i
    refine oscAt_le fun ζ η _ ↦ ENNReal.ofReal_le_one.2 ?_
    rw [show ⇑(indicatorLp (S := S) (E := E) A) = A.indicator (fun _ ↦ (1 : ℝ)) from rfl]
    by_cases h1 : ζ ∈ A <;> by_cases h2 : η ∈ A <;> simp [h1, h2]
  have hRHS : (∑' i, interdepSeries (condSpec γ Δ ω) bt i
        * oscAt (⇑(indicatorLp (S := S) (E := E) A)) i)
      ≤ ∑ i ∈ Λ, interdepTail γ Δ i := by
    rw [tsum_eq_sum (s := Λ) fun i hi ↦ by rw [hoscz i hi, mul_zero]]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    calc interdepSeries (condSpec γ Δ ω) bt i
            * oscAt (⇑(indicatorLp (S := S) (E := E) A)) i
        ≤ interdepSeries (condSpec γ Δ ω) bt i * 1 := by gcongr; exact hosc1 i
      _ = interdepSeries (condSpec γ Δ ω) bt i := mul_one _
      _ ≤ interdepSeries γ bt i :=
          interdepSeries_mono_matrix (interdep_condSpec_le γ Δ ω) bt i
      _ = interdepTail γ Δ i := rfl
  exact le_add_of_ofReal_abs_toReal_sub_le (measure_ne_top _ _) (measure_ne_top _ _)
    (hest.trans hRHS)

end Cauchy

/-! ### Georgii (8.7), (8.23): existence of the Gibbs measure -/

section Existence

variable {γ : Specification S E}

/-- **Georgii (8.23), step 1.** Under Dobrushin's condition the net of finite-volume Gibbs
distributions with a fixed boundary condition is locally equicontinuous: this is the
Cauchy property of Georgii's proof, in the form of Georgii (4.6). -/
theorem locallyEquicontinuous_finiteVolumeDistributions_of_isDobrushin
    (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ) (η : S → E) :
    LocallyEquicontinuous atTop (finiteVolumeDistributions γ η) := by
  classical
  intro Λ A hAm hanti hempty
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have htail : Tendsto (fun Δ : Finset S ↦ ∑ i ∈ Λ, interdepTail γ Δ i) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (f := fun (i : S) (Δ : Finset S) ↦ interdepTail γ Δ i)
      (a := fun _ : S ↦ (0 : ℝ≥0∞)) Λ fun i _ ↦ tendsto_interdepTail hd i
    simpa using h
  obtain ⟨Δ₀, hΔ₀⟩ := ((ENNReal.tendsto_nhds_zero.1 htail) (ε / 2)
    (ENNReal.half_pos hε.ne')).exists
  have hlim : ∀ m, limsup (fun Δ : Finset S ↦
      ((finiteVolumeDistributions γ η Δ : ProbabilityMeasure (S → E)) :
        Measure (S → E)) (A m)) atTop ≤ γ Δ₀ η (A m) + ε / 2 := by
    intro m
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [Filter.eventually_ge_atTop Δ₀] with Δ hΔ
    exact le_trans (measure_le_add_interdepTail hγq hd hΔ η (hAm m))
      (add_le_add (le_refl _) hΔ₀)
  have hmeas : Tendsto (fun m ↦ γ Δ₀ η (A m)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := γ Δ₀ η)
      (fun m ↦ ((cylinderEvents_le_pi _ (hAm m)).nullMeasurableSet)) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hempty] at h
    simpa [Function.comp_def] using h
  have hev : ∀ᶠ m in atTop, γ Δ₀ η (A m) ≤ ε / 2 :=
    (ENNReal.tendsto_nhds_zero.1 hmeas) (ε / 2) (ENNReal.half_pos hε.ne')
  filter_upwards [hev] with m hm
  calc limsup (fun Δ : Finset S ↦
        ((finiteVolumeDistributions γ η Δ : ProbabilityMeasure (S → E)) :
          Measure (S → E)) (A m)) atTop
      ≤ γ Δ₀ η (A m) + ε / 2 := hlim m
    _ ≤ ε / 2 + ε / 2 := add_le_add hm (le_refl _)
    _ = ε := ENNReal.add_halves ε

/-- **Georgii, Theorem (8.7)**, existence part (restated and proved as Georgii (8.23)): over a
standard Borel state space a quasilocal specification satisfying Dobrushin's condition has at
least one Gibbs measure. -/
theorem GP_nonempty_of_isDobrushin [Nonempty E] [StandardBorelSpace E]
    (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ) :
    (GP (S := S) (E := E) γ).Nonempty := by
  obtain ⟨μ, hμ, -⟩ := exists_isLocalThermodynamicLimit_mem_GP hγq (fun _ ↦ Classical.arbitrary E)
    (locallyEquicontinuous_finiteVolumeDistributions_of_isDobrushin hγq hd _)
  exact ⟨μ, hμ⟩

/-- **Georgii, Theorem (8.7).** If `γ` is a quasilocal specification satisfying Dobrushin's
condition and `(E, ℰ)` is a standard Borel space, then `|𝒢(γ)| = 1`. -/
theorem existsUnique_mem_GP_of_isDobrushin_of_standardBorel [Nonempty E] [StandardBorelSpace E]
    (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ) :
    ∃! μ : ProbabilityMeasure (S → E), μ ∈ GP (S := S) (E := E) γ :=
  existsUnique_mem_GP_of_isDobrushin hγq hd (GP_nonempty_of_isDobrushin hγq hd)

end Existence

end MeasureTheory.GibbsMeasure.Dobrushin

end
