/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.MarkovInt
public import GibbsMeasure.Model.MarkovChain

/-!
# Chapter 3 as an instance of Chapter 10

The Markov specification `γ_P` of a positive stochastic matrix on a finite state space (Georgii
(3.5)) is Markov in the sense of Definition (10.2), and the stationary chain `μ_P` of (3.3) is a
Markov chain in the sense of Definition (10.4).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

/-! ## Chapter 3 as an instance: finite state space -/

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]

omit [DecidableEq E] [Nonempty E] in
omit [Fintype E] in
/-- The Boltzmann factor of Georgii's Chapter 3 Markov potential is a Markovian density family
in the sense of (10.2). -/
theorem isMarkovianInt_boltzmannFactor_markovPotential [Finite E] (P : Matrix E E ℝ) :
    Specification.IsMarkovianInt ((markovPotential P).boltzmannFactor 1) := by
  have := Fintype.ofFinite E
  intro i k hik
  have hrw : (markovPotential P).boltzmannFactor 1 (Finset.Ioo i k) = fun σ ↦
      ENNReal.ofReal (Real.exp (-1 * ∑ j ∈ bondsOf (Finset.Ioo i k),
        -Real.log (P (σ j) (σ (j + 1))))) := by
    funext σ
    rw [Potential.boltzmannFactor, hamiltonian_eq_sum_bondsOf]
  rw [hrw]
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
    (Finset.measurable_sum _ fun j hj ↦ ?_)))
  rw [mem_bondsOf] at hj
  simp only [Finset.mem_Ioo] at hj
  have hj1 : j ∈ Set.Icc i k := by simp only [Set.mem_Icc]; omega
  have hj2 : j + 1 ∈ Set.Icc i k := by simp only [Set.mem_Icc]; omega
  exact (measurable_of_countable fun q : E × E ↦ -Real.log (P q.1 q.2)).comp
    ((measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) hj1).prodMk
      (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) hj2))

omit [DecidableEq E] in
/-- **Chapter 3 as an instance of (10.2).** The Markov specification `γ_P` of a stochastic matrix
`P` (Georgii (3.6)) is a Markov specification in the sense of Definition (10.2). -/
theorem isMarkovInt_markovSpecification (P : Matrix E E ℝ) :
    Specification.IsMarkovInt (markovSpecification P) :=
  Specification.isMarkovInt_of_forall_apply_eq _ (uniformOn (Set.univ : Set E))
    (fun Λ ↦ Potential.measurable_boltzmannFactor 1 Λ)
    (isMarkovianInt_boltzmannFactor_markovPotential P) markovSpecification_eq_withDensity

/-! ### The stationary chain of Chapter 3 is a Markov chain in the sense of (10.4) -/

open Classical in
omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Over a finite state space, a rectangle is the disjoint union of the point cylinders of the
configurations it contains. -/
lemma rect_eq_iUnion_cyl (W : Finset ℤ) (B : ℤ → Set E) :
    rect W B = ⋃ ξ : W → E, if ∀ j : W, ξ j ∈ B j then
      cyl W (juxt (W : Set ℤ) (fun _ ↦ Classical.arbitrary E) ξ) else ∅ := by
  ext σ
  simp only [mem_rect, Set.mem_iUnion]
  constructor
  · intro h
    refine ⟨fun j ↦ σ j.1, ?_⟩
    have hc : ∀ j : W, (fun j : W ↦ σ j.1) j ∈ B j.1 := fun j ↦ h j.1 j.2
    rw [ite_eq_left hc]
    intro k hk
    rw [juxt_apply_of_mem (Finset.mem_coe.2 hk)]
  · rintro ⟨ξ, hξ⟩ k hk
    split_ifs at hξ with hB
    · have := hξ k hk
      rw [juxt_apply_of_mem (Finset.mem_coe.2 hk)] at this
      rw [this]
      exact hB ⟨k, hk⟩
    · exact absurd hξ (Set.notMem_empty σ)

open Classical in
omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma pairwise_disjoint_ite_cyl (W : Finset ℤ) (B : ℤ → Set E) :
    Pairwise (Function.onFun Disjoint fun ξ : W → E ↦ if ∀ j : W, ξ j ∈ B j then
      cyl W (juxt (W : Set ℤ) (fun _ ↦ Classical.arbitrary E) ξ) else ∅) := by
  intro ξ ξ' hne
  simp only [Function.onFun]
  split_ifs with h₁ h₂
  · refine Set.disjoint_left.2 fun σ hσ hσ' ↦ hne (funext fun j ↦ ?_)
    have h1 := hσ j.1 j.2
    have h2 := hσ' j.1 j.2
    rw [juxt_apply_of_mem (Finset.mem_coe.2 j.2)] at h1 h2
    exact h1.symm.trans h2
  all_goals simp

/-- **Chapter 3 as an instance of (10.4).** The stationary Markov chain `μ_P` of Georgii (3.3),
built from a positive stochastic matrix `P` on a finite state space, is a Markov chain in the
sense of Definition (10.4) for any (hence the) kernel `K` with `K(x, {y}) = P(x, y)`. -/
theorem isMarkovChain_stationaryChain (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) (K : Kernel E E) [IsMarkovKernel K]
    (hK : ∀ (x : E) (S : Set E), K x S = ∑ y, S.indicator (fun y ↦ ENNReal.ofReal (P x y)) y) :
    IsMarkovChain (fun _ ↦ K) (stationaryChain P hP hpos) := by
  classical
  have := isProbabilityMeasure_stationaryChain P hP hpos
  set μ := stationaryChain P hP hpos with hμ
  rw [isMarkovChain_iff_forall_measure_inter]
  intro i A hA t ht
  have hg : Measurable fun σ : ℤ → E ↦ K (σ (i - 1)) A :=
    (Kernel.measurable_coe K hA).comp (measurable_pi_apply _)
  -- the identity on point cylinders over `[i - n - 1, i - 1]`
  have core : ∀ (n : ℕ) (η : ℤ → E),
      μ ((fun σ ↦ σ i) ⁻¹' A ∩ cyl (Finset.Icc (i - n - 1) (i - 1)) η)
        = ∫⁻ σ in cyl (Finset.Icc (i - n - 1) (i - 1)) η, K (σ (i - 1)) A ∂μ := by
    intro n η
    set W := Finset.Icc (i - n - 1) (i - 1) with hW
    have hiW : i ∉ W := by simp [hW]
    have hi1W : i - 1 ∈ W := by simp [hW]
    have hins : insert i W = Finset.Icc (i - n - 1) i := by
      ext j; simp only [hW, Finset.mem_insert, Finset.mem_Icc]; omega
    -- left-hand side: sum over the value at `i`
    have hdecomp : (fun σ ↦ σ i) ⁻¹' A ∩ cyl W η
        = ⋃ y : E, if y ∈ A then cyl (insert i W) (Function.update η i y) else ∅ := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, mem_cyl]
      constructor
      · rintro ⟨hσA, hσ⟩
        refine ⟨σ i, ?_⟩
        rw [ite_eq_left hσA]
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · simp
        · rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hiW), hσ k hk]
      · rintro ⟨y, hy⟩
        split_ifs at hy with hyA
        · have hi := hy i (Finset.mem_insert_self _ _)
          rw [Function.update_self] at hi
          refine ⟨hi ▸ hyA, fun k hk ↦ ?_⟩
          rw [hy k (Finset.mem_insert_of_mem hk),
            Function.update_of_ne (ne_of_mem_of_not_mem hk hiW)]
        · exact absurd hy (Set.notMem_empty σ)
    have hdisj : Pairwise (Function.onFun Disjoint fun y : E ↦
        if y ∈ A then cyl (insert i W) (Function.update η i y) else ∅) := by
      intro y y' hne
      simp only [Function.onFun]
      split_ifs
      · refine Set.disjoint_left.2 fun σ hσ hσ' ↦ hne ?_
        have h1 := hσ i (Finset.mem_insert_self _ _)
        have h2 := hσ' i (Finset.mem_insert_self _ _)
        simp only [Function.update_self] at h1 h2
        exact h1.symm.trans h2
      all_goals simp
    have hle : i - n - 1 ≤ i - 1 := by omega
    have hcylW : μ (cyl W η) = ENNReal.ofReal (stationaryDist P hP hpos (η (i - n - 1))
        * ∏ k ∈ Finset.Ico (i - n - 1) (i - 1), P (η k) (η (k + 1))) :=
      markovChain_cylinder P hP hpos hle η
    have hcyl : ∀ y, μ (cyl (insert i W) (Function.update η i y))
        = ENNReal.ofReal (stationaryDist P hP hpos (η (i - n - 1))
          * ∏ k ∈ Finset.Ico (i - n - 1) (i - 1), P (η k) (η (k + 1)))
          * ENNReal.ofReal (P (η (i - 1)) y) := by
      intro y
      have h1 : μ (cyl (Finset.Icc (i - n - 1) i) (Function.update η i y))
          = ENNReal.ofReal (stationaryDist P hP hpos (Function.update η i y (i - n - 1))
            * ∏ k ∈ Finset.Ico (i - n - 1) i,
              P (Function.update η i y k) (Function.update η i y (k + 1))) :=
        markovChain_cylinder P hP hpos (by omega) _
      have hIco : Finset.Ico (i - n - 1) i = insert (i - 1) (Finset.Ico (i - n - 1) (i - 1)) := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hnot : i - 1 ∉ Finset.Ico (i - n - 1) (i - 1) := by simp
      have hprod : ∏ k ∈ Finset.Ico (i - n - 1) (i - 1),
          P (Function.update η i y k) (Function.update η i y (k + 1))
          = ∏ k ∈ Finset.Ico (i - n - 1) (i - 1), P (η k) (η (k + 1)) :=
        Finset.prod_congr rfl fun k hk ↦ by
          simp only [Finset.mem_Ico] at hk
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rw [hins, h1, hIco, Finset.prod_insert hnot, hprod, show i - 1 + 1 = i by ring,
        Function.update_of_ne (by omega : i - n - 1 ≠ i), Function.update_self,
        Function.update_of_ne (by omega : i - 1 ≠ i)]
      rw [show stationaryDist P hP hpos (η (i - n - 1))
          * (P (η (i - 1)) y * ∏ k ∈ Finset.Ico (i - n - 1) (i - 1), P (η k) (η (k + 1)))
          = (stationaryDist P hP hpos (η (i - n - 1))
            * ∏ k ∈ Finset.Ico (i - n - 1) (i - 1), P (η k) (η (k + 1))) * P (η (i - 1)) y by ring]
      exact ENNReal.ofReal_mul (mul_nonneg (stationaryDist_pos P hP hpos _).le
        (Finset.prod_nonneg fun k _ ↦ (hpos _ _).le))
    rw [hdecomp, measure_iUnion hdisj (fun y ↦ by
      split_ifs
      · exact measurableSet_cyl _ _
      · exact MeasurableSet.empty), tsum_fintype]
    -- right-hand side: the integrand is constant on the cylinder
    rw [setLIntegral_congr_fun (measurableSet_cyl W η) (g := fun _ ↦ K (η (i - 1)) A)
      (fun σ hσ ↦ by rw [hσ (i - 1) hi1W]), setLIntegral_const, hcylW, hK, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    by_cases hy : y ∈ A
    · rw [ite_eq_left hy, Set.indicator_of_mem hy, hcyl, mul_comm]
    · rw [ite_eq_right hy, Set.indicator_of_notMem hy, measure_empty, zero_mul]
  -- rectangles are disjoint unions of point cylinders
  have hrect : ∀ (n : ℕ) (B : ℤ → Set E), (∀ k, MeasurableSet (B k)) →
      μ ((fun σ ↦ σ i) ⁻¹' A ∩ rect (Finset.Icc (i - n - 1) (i - 1)) B)
        = ∫⁻ σ in rect (Finset.Icc (i - n - 1) (i - 1)) B, K (σ (i - 1)) A ∂μ := by
    intro n B _
    rw [rect_eq_iUnion_cyl, Set.inter_iUnion, measure_iUnion (fun ξ ξ' hne ↦
        (pairwise_disjoint_ite_cyl _ B hne).mono Set.inter_subset_right Set.inter_subset_right)
      (fun ξ ↦ (measurable_pi_apply i hA).inter (by
        split_ifs
        · exact measurableSet_cyl _ _
        · exact MeasurableSet.empty)),
      lintegral_iUnion (fun ξ ↦ by
        split_ifs
        · exact measurableSet_cyl _ _
        · exact MeasurableSet.empty) (pairwise_disjoint_ite_cyl _ B)]
    refine tsum_congr fun ξ ↦ ?_
    split_ifs
    · exact core n _
    · simp
  -- the π-λ argument over the rectangles generating `𝓕_{]-∞,i[}`
  have := ext_on_measurableSpace_of_generate_finite (MeasurableSpace.pi)
    (μ := μ.restrict ((fun σ : ℤ → E ↦ σ i) ⁻¹' A))
    (ν := μ.withDensity fun σ : ℤ → E ↦ K (σ (i - 1)) A)
    (rectangles E fun n ↦ Finset.Icc (i - n - 1) (i - 1)) ?_ cylinderEvents_le_pi
    (cylinderEvents_Iio_eq_generateFrom i) (isPiSystem_rectangles (monotone_Icc_left' i)) ?_ ht
  · rw [Measure.restrict_apply' (measurable_pi_apply i hA), withDensity_apply _
      (cylinderEvents_le_pi _ ht), Set.inter_comm] at this
    exact this
  · rintro _ ⟨m, B', hB', rfl⟩
    rw [Measure.restrict_apply' (measurable_pi_apply i hA),
      withDensity_apply _ (measurableSet_rect hB'), Set.inter_comm]
    exact hrect m B' hB'
  · rw [Measure.restrict_apply' (measurable_pi_apply i hA), withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, Set.univ_inter]
    have := hrect 0 (fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ)
    have huniv : rect (Finset.Icc (i - (0 : ℕ) - 1) (i - 1)) (fun _ : ℤ ↦ (Set.univ : Set E))
        = Set.univ := by ext; simp [rect]
    rw [huniv, Set.inter_univ, Measure.restrict_univ] at this
    exact this

end MeasureTheory.GibbsMeasure.Markov

end
