/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.MarkovInt
public import GibbsMeasure.Specification.MarkovIntUniqueness
public import GibbsMeasure.Model.MarkovChain
public import GibbsMeasure.Potential.NearestNeighbour
public import GibbsMeasure.Potential.Transformation
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Chapter 3 as an instance of Chapter 10, and Georgii's Example (10.24)(1)

The Markov specification `γ_P` of a positive stochastic matrix on a finite state space (Georgii
(3.5)) is Markov in the sense of Definition (10.2), and the stationary chain `μ_P` of (3.3) is a
Markov chain in the sense of Definition (10.4).

**Georgii, Example (10.24)(1)** — nearest-neighbour potentials on `ℤ` over an arbitrary state
space: `isIrreducibleInt_premodifierNorm_boltzmannFactor_of_isNearestNeighbour` (and its literal
form `…_of_isNearestNeighbour'` with `Φ_{\{0\}} = 0`, and the `Potential.gibbsModifier` form
`isIrreducibleInt_gibbsModifier_of_isNearestNeighbour`). For a shift-invariant nearest-neighbour
`Φ` with `sup_ω Z^Φ_{\{0\}}(ω) ≤ c < ∞` and `sup_{ω_0, ω_1 ∈ C_N} Φ_{\{0,1\}} ≤ c_N` for some
`C_N ↑ E`, the Gibbsian modification `ρ^Φ` is irreducible in the sense of Definition (10.23) with
`n(N) = 1` and `h_N = 1_{C_N} e^{-2c_N}/c`. The Chapter 3 Markov potential is an instance
(`isIrreducibleInt_premodifierNorm_boltzmannFactor_markovPotential`, with `C_N = E`, `c = 1`,
`c_N = logBound P`).

The general inputs live with their objects: `Potential.IsNearestNeighbour.isFiniteRange` and
`Potential.hamiltonian_singleton_of_isNearestNeighbour_hasse_int` in
`Potential/NearestNeighbour.lean`, `Specification.marginalDensity_singleton` in
`Specification/MarkovIntChains.lean`; the Chapter 3 facts `isNearestNeighbour_markovPotential`,
`isShiftInvariant_markovPotential` are here.
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
    exact mem_cyl.2 fun k hk ↦ by rw [juxt_apply_of_mem (Finset.mem_coe.2 hk)]
  · rintro ⟨ξ, hξ⟩ k hk
    split_ifs at hξ with hB
    · have := mem_cyl.1 hξ k hk
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
    have h1 := mem_cyl.1 hσ j.1 j.2
    have h2 := mem_cyl.1 hσ' j.1 j.2
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
        refine mem_cyl.2 fun k hk ↦ ?_
        rcases Finset.mem_insert.1 hk with rfl | hk
        · simp
        · rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hiW), hσ k hk]
      · rintro ⟨y, hy⟩
        split_ifs at hy with hyA
        · have hi := mem_cyl.1 hy i (Finset.mem_insert_self _ _)
          rw [Function.update_self] at hi
          refine ⟨hi ▸ hyA, fun k hk ↦ ?_⟩
          rw [mem_cyl.1 hy k (Finset.mem_insert_of_mem hk),
            Function.update_of_ne (ne_of_mem_of_not_mem hk hiW)]
        · exact absurd hy (Set.notMem_empty σ)
    have hdisj : Pairwise (Function.onFun Disjoint fun y : E ↦
        if y ∈ A then cyl (insert i W) (Function.update η i y) else ∅) := by
      intro y y' hne
      simp only [Function.onFun]
      split_ifs
      · refine Set.disjoint_left.2 fun σ hσ hσ' ↦ hne ?_
        have h1 := mem_cyl.1 hσ i (Finset.mem_insert_self _ _)
        have h2 := mem_cyl.1 hσ' i (Finset.mem_insert_self _ _)
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
      (fun σ hσ ↦ by rw [mem_cyl.1 hσ (i - 1) hi1W]), setLIntegral_const, hcylW, hK, Finset.sum_mul]
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

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [MeasurableSpace E]

/-- **Georgii, Example (10.24)(1).** Let `λ` be a probability a priori measure (Georgii's
standing reduction before (10.13)) and `Φ` a shift-invariant nearest-neighbour potential on `ℤ`
(`Φ_A = 0` unless `A` is a clique of `hasse ℤ`, i.e. a site or a bond). Suppose
`c = sup_ω Z^Φ_{\{0\}}(ω) < ∞` and, for some `C_N ↑ E`, `sup_{ω_0, ω_1 ∈ C_N} Φ_{\{0,1\}}(ω) ≤ c_N`.
Then the Gibbsian modification `ρ^Φ = h^Φ / Z^Φ` is irreducible in the sense of Definition
(10.23), with `n(N) = 1` and `h_N = 1_{C_N} e^{-2 c_N} / c`.

Georgii's "without loss `Φ_{\{0\}} = 0`" (by passing to an equivalent potential) is replaced by
the weaker hypothesis of a bound `sup_{ω_0 ∈ C_N} Φ_{\{0\}}(ω) ≤ c₀(N)` on the self-energy, so
that `h_N = 1_{C_N} e^{-(c₀(N) + 2 c_N)} / c`; the literal statement is
`isIrreducibleInt_premodifierNorm_boltzmannFactor_of_isNearestNeighbour'`. The bond `\{-1, 0\}` is
controlled through the bond `\{0, 1\}` by shift-invariance. -/
theorem isIrreducibleInt_premodifierNorm_boltzmannFactor_of_isNearestNeighbour
    (ν : Measure E) [IsProbabilityMeasure ν] {Φ : Potential ℤ E} [Potential.IsPotential Φ]
    (hnn : Potential.IsNearestNeighbour (SimpleGraph.hasse ℤ) Φ) (hshift : Φ.IsShiftInvariant)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hZ : ∀ ω, Specification.premodifierZ ν (Φ.boltzmannFactor 1) {0} ω ≤ c)
    {C : ℕ → Set E} (hCmeas : ∀ N, MeasurableSet (C N)) (hCmono : Monotone C)
    (hCunion : ⋃ N, C N = univ) {c₀ c₁ : ℕ → ℝ}
    (hsingle : ∀ N (ω : ℤ → E), ω 0 ∈ C N → Φ {0} ω ≤ c₀ N)
    (hpair : ∀ N (ω : ℤ → E), ω 0 ∈ C N → ω 1 ∈ C N → Φ {0, 1} ω ≤ c₁ N) :
    Specification.IsIrreducibleInt ν (Specification.premodifierNorm ν (Φ.boltzmannFactor 1)) := by
  have := hnn.isFiniteRange
  refine ⟨C, fun _ ↦ 1, fun N ↦ (C N).indicator fun _ ↦
      ENNReal.ofReal (Real.exp (-(c₀ N + 2 * c₁ N))) / c,
    hCmeas, hCmono, hCunion, fun N ↦ measurable_const.indicator (hCmeas N), fun _ ↦ le_rfl,
    ?_, ?_⟩
  · have htend : Filter.Tendsto (fun N ↦ ν (C N)) Filter.atTop (nhds 1) := by
      have := tendsto_measure_iUnion_atTop (μ := ν) hCmono
      rwa [hCunion, measure_univ] at this
    filter_upwards [htend.eventually_const_lt zero_lt_one] with N hN
    rw [lintegral_indicator_const (hCmeas N)]
    exact ENNReal.mul_pos (ENNReal.div_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hc).ne'
      hN.ne'
  · intro N ω h1 h2
    dsimp only at h1 h2 ⊢
    have hΛ : Finset.Ioo (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = ({0} : Finset ℤ) := by
      ext k
      simp only [Nat.cast_one, Finset.mem_Ioo, Finset.mem_singleton]
      omega
    rw [hΛ, Specification.marginalDensity_singleton ν
      (Specification.measurable_relNorm (γ := Specification.isssd ν)
        (Potential.isPremodifier_boltzmannFactor 1).measurable {0}) ω]
    by_cases h0 : ω 0 ∈ C N
    · rw [Set.indicator_of_mem h0]
      change _ ≤ Φ.boltzmannFactor 1 {0} ω
        / Specification.premodifierZ ν (Φ.boltzmannFactor 1) {0} ω
      refine ENNReal.div_le_div ?_ (hZ ω)
      rw [Potential.boltzmannFactor]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      rw [Potential.hamiltonian_singleton_of_isNearestNeighbour_hasse_int hnn 0 ω, zero_sub,
        zero_add]
      have hm : Φ {-1, 0} ω ≤ c₁ N := by
        have h := (Potential.isShiftInvariant_iff Φ).1 hshift 1 {-1, 0} ω
        have hmap : ({-1, 0} : Finset ℤ).map (Equiv.addRight (1 : ℤ)).toEmbedding = {0, 1} := by
          ext k
          simp only [Finset.mem_map_equiv, Equiv.addRight_symm, Equiv.coe_addRight,
            Finset.mem_insert, Finset.mem_singleton]
          omega
        rw [hmap] at h
        rw [← h]
        refine hpair N _ ?_ ?_
        · simpa using h1
        · simpa using h0
      have hp := hpair N ω h0 (by simpa using h2)
      have hs := hsingle N ω h0
      linarith
    · rw [Set.indicator_of_notMem h0]
      exact zero_le


/-- **Georgii, Example (10.24)(1), literally.** With `Φ_{\{0\}} = 0` (Georgii's "without loss"
normalisation), `sup_ω Z^Φ_{\{0\}}(ω) ≤ c < ∞` and `sup_{ω_0, ω_1 ∈ C_N} Φ_{\{0,1\}}(ω) ≤ c_N` for
some `C_N ↑ E`, the Gibbsian modification `ρ^Φ` is irreducible with `n(N) = 1` and
`h_N = 1_{C_N} e^{-2 c_N} / c`. -/
theorem isIrreducibleInt_premodifierNorm_boltzmannFactor_of_isNearestNeighbour'
    (ν : Measure E) [IsProbabilityMeasure ν] {Φ : Potential ℤ E} [Potential.IsPotential Φ]
    (hnn : Potential.IsNearestNeighbour (SimpleGraph.hasse ℤ) Φ) (hshift : Φ.IsShiftInvariant)
    (h0 : Φ {0} = 0) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hZ : ∀ ω, Specification.premodifierZ ν (Φ.boltzmannFactor 1) {0} ω ≤ c)
    {C : ℕ → Set E} (hCmeas : ∀ N, MeasurableSet (C N)) (hCmono : Monotone C)
    (hCunion : ⋃ N, C N = univ) {c₁ : ℕ → ℝ}
    (hpair : ∀ N (ω : ℤ → E), ω 0 ∈ C N → ω 1 ∈ C N → Φ {0, 1} ω ≤ c₁ N) :
    Specification.IsIrreducibleInt ν (Specification.premodifierNorm ν (Φ.boltzmannFactor 1)) :=
  isIrreducibleInt_premodifierNorm_boltzmannFactor_of_isNearestNeighbour ν hnn hshift hc hZ
    hCmeas hCmono hCunion (c₀ := fun _ ↦ 0) (fun _ ω _ ↦ by rw [h0]; exact le_rfl) hpair

/-- Example (10.24)(1) for the Gibbs modifier `Potential.gibbsModifier Φ 1 ν` (Georgii's
`ρ^Φ` of (2.8)). -/
theorem isIrreducibleInt_gibbsModifier_of_isNearestNeighbour
    (ν : Measure E) [IsProbabilityMeasure ν] {Φ : Potential ℤ E} [Potential.IsPotential Φ]
    [Potential.IsFiniteRange Φ]
    (hnn : Potential.IsNearestNeighbour (SimpleGraph.hasse ℤ) Φ) (hshift : Φ.IsShiftInvariant)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hZ : ∀ ω, Potential.partitionFunction Φ 1 ν {0} ω ≤ c)
    {C : ℕ → Set E} (hCmeas : ∀ N, MeasurableSet (C N)) (hCmono : Monotone C)
    (hCunion : ⋃ N, C N = univ) {c₀ c₁ : ℕ → ℝ}
    (hsingle : ∀ N (ω : ℤ → E), ω 0 ∈ C N → Φ {0} ω ≤ c₀ N)
    (hpair : ∀ N (ω : ℤ → E), ω 0 ∈ C N → ω 1 ∈ C N → Φ {0, 1} ω ≤ c₁ N) :
    Specification.IsIrreducibleInt ν (Potential.gibbsModifier Φ 1 ν) := by
  have hbw : Potential.boltzmannWeight (Φ := Φ) 1 = Φ.boltzmannFactor 1 := by
    funext Λ η
    exact (Potential.boltzmannFactor_eq_boltzmannWeight 1 Λ η).symm
  rw [Potential.gibbsModifier_eq_premodifierNorm, hbw]
  refine isIrreducibleInt_premodifierNorm_boltzmannFactor_of_isNearestNeighbour ν hnn hshift hc
    (fun ω ↦ ?_) hCmeas hCmono hCunion hsingle hpair
  have := hZ ω
  rwa [Potential.partitionFunction, hbw] at this


/-! ### Chapter 3 as an instance of Example (10.24)(1) -/

section ChapterThree

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Markov potential of Chapter 3 is a nearest-neighbour potential for `hasse ℤ`. -/
lemma isNearestNeighbour_markovPotential (P : Matrix E E ℝ) :
    Potential.IsNearestNeighbour (SimpleGraph.hasse ℤ) (markovPotential P) := by
  intro A hA
  refine funext fun σ ↦ markovPotential_of_not_pair P (fun ⟨i, hi⟩ ↦ hA ?_) σ
  subst hi
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rw [SimpleGraph.hasse_int_adj]
  omega

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Markov potential of Chapter 3 is shift-invariant (Georgii (5.8)). -/
lemma isShiftInvariant_markovPotential (P : Matrix E E ℝ) :
    (markovPotential P).IsShiftInvariant := by
  rw [Potential.isShiftInvariant_iff]
  intro j A η
  by_cases hA : ∃ i : ℤ, A = {i, i + 1}
  · obtain ⟨i, rfl⟩ := hA
    have hmap : ({i, i + 1} : Finset ℤ).map (Equiv.addRight j).toEmbedding
        = {i + j, i + j + 1} := by
      ext k
      simp only [Finset.mem_map_equiv, Equiv.addRight_symm, Equiv.coe_addRight, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    rw [hmap, markovPotential_pair, markovPotential_pair]
    simp only [shift_toFun_apply, add_sub_cancel_right]
    rw [show i + j + 1 - j = i + 1 by ring]
  · have hA' : ¬ ∃ i : ℤ, A.map (Equiv.addRight j).toEmbedding = {i, i + 1} := by
      rintro ⟨i, hi⟩
      refine hA ⟨i - j, Finset.ext fun a ↦ ?_⟩
      have := Finset.ext_iff.1 hi (a + j)
      simp only [Finset.mem_map_equiv, Equiv.addRight_symm, Equiv.coe_addRight,
        add_neg_cancel_right, Finset.mem_insert, Finset.mem_singleton] at this
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [this]
      constructor
      · rintro (h | h)
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      · rintro (h | h)
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    rw [markovPotential_of_not_pair P hA', markovPotential_of_not_pair P hA]

omit [MeasurableSingletonClass E] in
/-- The single-site partition function of `markovSpecification P` is at most `1`: the Boltzmann
factor `P(ω_{-1}, ω_0) P(ω_0, ω_1)` of a stochastic matrix is at most `1`. -/
lemma premodifierZ_boltzmannFactor_markovPotential_singleton_le_one (P : Matrix E E ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) (i : ℤ) (ω : ℤ → E) :
    Specification.premodifierZ (uniformOn (Set.univ : Set E))
      ((markovPotential P).boltzmannFactor 1) {i} ω ≤ 1 := by
  have := Specification.isMarkovKernel_isssdFun (ν := uniformOn (Set.univ : Set E)) (S := ℤ) {i}
  calc Specification.premodifierZ (uniformOn (Set.univ : Set E))
        ((markovPotential P).boltzmannFactor 1) {i} ω
      = ∫⁻ σ, (markovPotential P).boltzmannFactor 1 {i} σ
          ∂(Specification.isssd (uniformOn (Set.univ : Set E)) {i} ω) := rfl
    _ ≤ ∫⁻ _, 1 ∂(Specification.isssd (uniformOn (Set.univ : Set E)) {i} ω) := by
        refine lintegral_mono fun σ ↦ ?_
        rw [boltzmannFactor_eq_prod_bondsOf hpos]
        exact ENNReal.ofReal_le_one.2 (Finset.prod_le_one
          (fun _ _ ↦ Matrix.nonneg_of_mem_rowStochastic hP)
          (fun _ _ ↦ Matrix.le_one_of_mem_rowStochastic hP))
    _ = 1 := by rw [lintegral_one, measure_univ]

/-- **Chapter 3 as an instance of Example (10.24)(1).** The Gibbsian modification of the Markov
potential of a positive stochastic matrix on a finite state space is irreducible in the sense of
Definition (10.23): `C_N = E`, `c = 1`, `c_N = logBound P`. -/
theorem isIrreducibleInt_premodifierNorm_boltzmannFactor_markovPotential (P : Matrix E E ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) :
    Specification.IsIrreducibleInt (uniformOn (Set.univ : Set E))
      (Specification.premodifierNorm (uniformOn (Set.univ : Set E))
        ((markovPotential P).boltzmannFactor 1)) :=
  isIrreducibleInt_premodifierNorm_boltzmannFactor_of_isNearestNeighbour' _
    (isNearestNeighbour_markovPotential P) (isShiftInvariant_markovPotential P)
    (funext fun σ ↦ markovPotential_of_not_pair P (not_exists_pair_singleton 0) σ)
    ENNReal.one_ne_top
    (fun ω ↦ premodifierZ_boltzmannFactor_markovPotential_singleton_le_one P hP hpos 0 ω)
    (C := fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ) (fun _ _ _ ↦ le_rfl)
    (Set.iUnion_const Set.univ)
    (c₁ := fun _ ↦ logBound P)
    (fun _ ω _ _ ↦ (le_abs_self _).trans (abs_markovPotential_le P _ ω))

end ChapterThree

end MeasureTheory.GibbsMeasure.Markov

end
