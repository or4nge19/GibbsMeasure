/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.ProductMeasure
public import GibbsMeasure.Specification.Average
public import GibbsMeasure.Specification.DobrushinUniqueness
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.GluedFamily
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Analysis.Real.Cardinality

/-!
# Georgii, Example (2.27): a specification with vanishing interdependence and many Gibbs measures

`E = {0,1}`, `S = ℕ`. For a parameter `y` let `λ^y = y δ_1 + (1-y) δ_0` (`bern`, totalised to all
of `ℝ≥0∞` by truncating `y` at `1`) and `μ^y = (λ^y)^ℕ` (`bernoulliField`). The supports of the
`μ^x` are separated by the tail function

`ξ = liminf_n n⁻¹ ∑_{i < n} σ_i`

(`xi`, valued in `ℝ≥0∞`): by the strong law of large numbers `ξ = x` holds `μ^x`-a.s.
(`measure_xi_eq_one`). Georgii's Remark (1.25) (`Specification.isGibbsMeasure_isssd_iff`) gives
`μ^y ∈ 𝒢(λ^y_·)`, and the gluing construction of Remark (2.26)
(`Specification.glued`, `GibbsMeasure/Specification/GluedFamily.lean`) turns the family
`(λ^y_·)_y` into a single specification `γ = gammaEx` with `γ_Λ(· | ω) = λ^{ξ ω}_Λ(· | ω)`.

The point of the example is that `γ` has *vanishing interdependence*: modifying `ω` at a single
site changes neither `ξ ω` (a liminf of Cesàro averages ignores finitely many coordinates,
`dependsOn_xi`) nor the resulting single-spin law, so `C_ij(γ) = 0` for all `i, j` and Dobrushin's
constant is `c(γ) = 0 < 1`. Yet `𝒢(γ)` is uncountable. So the quasilocality conjunct of Georgii's
Definition (8.6) (`MeasureTheory.GibbsMeasure.Dobrushin.IsDobrushin`) is not decorative: without
it Theorem (8.7) would be false.

## Main results

* `measure_xi_eq_one`: `μ^x(ξ = x) = 1` for `x ∈ [0,1]`, by the strong law of large numbers.
* `isGibbsMeasure_bernoulliField`: every `μ^x`, `x ∈ [0,1]`, is a Gibbs measure for `γ`.
* `interdep_gammaEx`, `tsum_interdep_gammaEx`: `C_ij(γ) = 0` and `c(γ) = 0`.
* `not_countable_gibbsMeasures`: `𝒢(γ)` is uncountable.
* `not_isQuasilocal_gammaEx`: `γ` is not quasilocal.
* `exists_not_countable_gibbsMeasures_of_tsum_interdep_lt_one`: the two previous items packaged as
  the justification for the quasilocality conjunct of Definition (8.6).
* `G_gammaEx_eq`: Georgii's full identification `𝒢(γ) = {∫ w(dx) μ^x : w ∈ 𝓟([0,1])}`, and
  `existsUnique_weight_of_mem_G`: the mixing weight `w` is unique, being the law of `ξ`.

The identification needs nothing beyond `μ γ_Λ = μ`: on an event `A ∈ 𝓕_Λ` the glued kernel is
`γ_Λ(A | ω) = μ^{ξ ω}(A)` (`gammaEx_apply_of_mem_cylinderEvents`, from
`Specification.isssd_apply_of_mem_cylinderEvents`), so the DLR equation reads
`μ(A) = ∫ μ(dω) μ^{ξ ω}(A) = ∫ ξ(μ)(dx) μ^x(A)` and the local events determine `μ`. The reverse
inclusion is the general fact that a measurable mixture of Gibbs measures is Gibbs
(`Specification.isGibbsMeasure_bind`).

De Finetti's theorem, Georgii's Example (7.31), is *not* needed for this; it is what further
identifies the above set with the set of all exchangeable random fields, and is formalised in
`GibbsMeasure/Specification/DeFinetti.lean` (`existsUnique_mixing_of_isExchangeable`).
-/

@[expose] public section

-- Lean 4.34's module system does not unfold non-exposed mathlib defs during `isDefEq`.
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.GibbsMeasure.Exchangeable

/-! ### The single-spin distributions `λ^x` -/

/-- Georgii (2.27): the single spin distribution `λ^y = y δ_1 + (1 - y) δ_0` on `E = {0, 1}`,
totalised to all of `ℝ≥0∞` by truncating the parameter at `1`. -/
noncomputable def bern (y : ℝ≥0∞) : Measure Bool :=
  min y 1 • Measure.dirac true + (1 - min y 1) • Measure.dirac false

lemma bern_apply (y : ℝ≥0∞) (B : Set Bool) :
    bern y B = min y 1 * B.indicator 1 true + (1 - min y 1) * B.indicator 1 false := by
  simp [bern, Measure.add_apply, Measure.smul_apply, smul_eq_mul]

@[simp] lemma bern_apply_true (y : ℝ≥0∞) : bern y {true} = min y 1 := by
  simp [bern_apply]

@[simp] lemma bern_apply_false (y : ℝ≥0∞) : bern y {false} = 1 - min y 1 := by
  simp [bern_apply]

instance instIsProbabilityMeasureBern (y : ℝ≥0∞) : IsProbabilityMeasure (bern y) where
  measure_univ := by
    rw [bern_apply]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
    exact add_tsub_cancel_of_le (min_le_right y 1)

lemma measurable_bern_apply (B : Set Bool) : Measurable fun y : ℝ≥0∞ ↦ bern y B := by
  simp only [bern_apply]
  fun_prop

/-- The single-spin distributions depend measurably on the parameter. -/
lemma measurable_bern : Measurable bern :=
  Measure.measurable_of_measurable_coe _ fun B _ ↦ measurable_bern_apply B

/-- `bern` sees the parameter only through its truncation at `1`. -/
lemma bern_min_one (y : ℝ≥0∞) : bern (min y 1) = bern y := by simp [bern]

/-- Every `bern y` is a `bern` of a genuine `[0,1]` parameter. -/
lemma bern_ofReal_toReal (y : ℝ≥0∞) : bern (ENNReal.ofReal (min y 1).toReal) = bern y := by
  rw [ENNReal.ofReal_toReal (by simp), bern_min_one]

/-! ### The tail function `ξ` -/

/-- The `{0,1}`-valued spin variable of Georgii (2.27). -/
def spin (b : Bool) : ℝ := if b then 1 else 0

lemma spin_nonneg (b : Bool) : 0 ≤ spin b := by cases b <;> simp [spin]

lemma spin_le_one (b : Bool) : spin b ≤ 1 := by cases b <;> simp [spin]

lemma measurable_spin : Measurable spin := by fun_prop

/-- The Cesàro averages `n⁻¹ ∑_{i < n} σ_i`. -/
noncomputable def avg (ω : ℕ → Bool) (n : ℕ) : ℝ := (∑ i ∈ Finset.range n, spin (ω i)) / n

lemma avg_nonneg (ω : ℕ → Bool) (n : ℕ) : 0 ≤ avg ω n :=
  div_nonneg (Finset.sum_nonneg fun _ _ ↦ spin_nonneg _) (Nat.cast_nonneg n)

lemma avg_le_one (ω : ℕ → Bool) (n : ℕ) : avg ω n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [avg]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [avg, div_le_one hnpos]
  calc ∑ i ∈ Finset.range n, spin (ω i) ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦ spin_le_one _
    _ = n := by simp

/-- **Georgii (2.27)**: the tail function `ξ = liminf_n n⁻¹ ∑_{i < n} σ_i`, valued in `ℝ≥0∞`. -/
noncomputable def xi (ω : ℕ → Bool) : ℝ≥0∞ :=
  liminf (fun n ↦ ENNReal.ofReal (avg ω n)) atTop

lemma measurable_avg (n : ℕ) : Measurable fun ω : ℕ → Bool ↦ avg ω n := by
  unfold avg
  exact (Finset.measurable_sum _ fun i _ ↦ measurable_spin.comp (measurable_pi_apply i)).div
    measurable_const

lemma measurable_xi : Measurable xi :=
  Measurable.liminf fun n ↦ (measurable_avg n).ennreal_ofReal

/-- **Georgii (2.27)**: `ξ` takes its values in `[0,1]`, being a liminf of averages of
`{0,1}`-valued spins. -/
lemma xi_le_one (ω : ℕ → Bool) : xi ω ≤ 1 :=
  calc xi ω ≤ liminf (fun _ : ℕ ↦ (1 : ℝ≥0∞)) atTop :=
        liminf_le_liminf (.of_forall fun n ↦ ENNReal.ofReal_le_one.2 (avg_le_one ω n))
    _ = 1 := liminf_const 1

/-! ### `ξ` is insensitive to finitely many coordinates -/

/-- Modifying `ω` inside a finite volume `Λ` shifts the Cesàro averages by at most `|Λ|/n`. -/
lemma avg_le_avg_add {Λ : Finset ℕ} {ζ η : ℕ → Bool} (h : ∀ i ∉ Λ, ζ i = η i) (n : ℕ) :
    avg ζ n ≤ avg η n + (Λ.card : ℝ) / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [avg]
  have key : ∑ i ∈ Finset.range n, (spin (ζ i) - spin (η i)) ≤ (Λ.card : ℝ) := by
    have h1 : ∀ i ∈ Finset.range n, spin (ζ i) - spin (η i) ≤ if i ∈ Λ then (1 : ℝ) else 0 := by
      intro i _
      by_cases hi : i ∈ Λ
      · simp only [hi, ite_true]
        have h2 := spin_le_one (ζ i)
        have h3 := spin_nonneg (η i)
        linarith
      · simp [hi, h i hi]
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_ite_mem]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  rw [Finset.sum_sub_distrib] at key
  have hsum : ∑ i ∈ Finset.range n, spin (ζ i)
      ≤ (∑ i ∈ Finset.range n, spin (η i)) + (Λ.card : ℝ) := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold avg
  rw [← add_div]
  gcongr

lemma tendsto_ofReal_card_div (c : ℕ) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((c : ℝ) / n)) atTop (𝓝 0) := by
  simpa using ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))

lemma xi_le_xi_of_agree {Λ : Finset ℕ} {ζ η : ℕ → Bool} (h : ∀ i ∉ Λ, ζ i = η i) :
    xi ζ ≤ xi η := by
  have hstep : ∀ n : ℕ, ENNReal.ofReal (avg ζ n)
      ≤ ENNReal.ofReal (avg η n) + ENNReal.ofReal ((Λ.card : ℝ) / n) := by
    intro n
    rw [← ENNReal.ofReal_add (avg_nonneg η n) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (avg_le_avg_add h n)
  calc xi ζ ≤ liminf (fun n ↦ ENNReal.ofReal (avg η n) + ENNReal.ofReal ((Λ.card : ℝ) / n))
        atTop := liminf_le_liminf (.of_forall hstep)
    _ = liminf (fun n ↦ ENNReal.ofReal (avg η n)) atTop :=
        ENNReal.liminf_add_of_right_tendsto_zero (tendsto_ofReal_card_div Λ.card) _
    _ = xi η := rfl

/-- **Georgii (2.27)**: a liminf of Cesàro averages is insensitive to any finite set of
coordinates. -/
lemma dependsOn_xi (Λ : Finset ℕ) : DependsOn xi ((Λ : Set ℕ)ᶜ) := by
  intro ζ η hagree
  have h : ∀ i ∉ Λ, ζ i = η i := fun i hi ↦ hagree i (by simpa using hi)
  have h' : ∀ i ∉ Λ, η i = ζ i := fun i hi ↦ (h i hi).symm
  exact le_antisymm (xi_le_xi_of_agree h) (xi_le_xi_of_agree h')

/-- **Georgii (2.27)**: `ξ` is measurable for the tail σ-algebra. -/
lemma measurable_tail_xi : Measurable[tailSigmaAlgebra ℕ Bool] xi := by
  intro s hs
  rw [tailSigmaAlgebra, MeasurableSpace.measurableSet_iInf]
  exact fun Λ ↦ measurable_xi.cylinderEvents_of_dependsOn (dependsOn_xi Λ) hs

/-! ### The independent specifications `γ^y` and their joint measurability -/

lemma isssd_apply_eq (ν : Measure Bool) [IsProbabilityMeasure ν] (Λ : Finset ℕ) (ω : ℕ → Bool) :
    Specification.isssd ν Λ ω = Measure.map (juxt (Λ : Set ℕ) ω) (Measure.pi fun _ : Λ ↦ ν) := rfl

lemma pi_singleton (ν : Measure Bool) [IsProbabilityMeasure ν] (Λ : Finset ℕ)
    (σ : {i // i ∈ Λ} → Bool) :
    (Measure.pi fun _ : Λ ↦ ν) {σ} = ∏ i, ν {σ i} := by
  rw [← Set.univ_pi_singleton σ, Measure.pi_pi]

/-- On a two-point spin space the independent kernel is a finite sum over the finite-volume
configurations. -/
lemma isssd_apply_eq_sum (ν : Measure Bool) [IsProbabilityMeasure ν] (Λ : Finset ℕ)
    (ω : ℕ → Bool) {A : Set (ℕ → Bool)} (hA : MeasurableSet A) :
    Specification.isssd ν Λ ω A =
      ∑ σ : {i // i ∈ Λ} → Bool,
        (juxt (Λ : Set ℕ) ω ⁻¹' A).indicator (fun τ ↦ ∏ i, ν {τ i}) σ := by
  rw [isssd_apply_eq, Measure.map_apply Measurable.juxt hA]
  have hB : MeasurableSet (juxt (Λ : Set ℕ) ω ⁻¹' A) := Measurable.juxt hA
  have hfun : (fun τ : {i // i ∈ Λ} → Bool ↦ (Measure.pi fun _ : Λ ↦ ν) {τ})
      = fun τ ↦ ∏ i, ν {τ i} := funext fun τ ↦ pi_singleton ν Λ τ
  refine Eq.trans
    (Measure.tsum_indicator_apply_singleton (Measure.pi fun _ : Λ ↦ ν) _ hB).symm ?_
  rw [tsum_fintype, hfun]
  rfl

/-- **Georgii (2.27)**: the independent specifications `γ^y = λ^y` depend measurably on `y`. -/
lemma isMeasurableFamily_isssd_bern :
    Specification.IsMeasurableFamily (S := ℕ) fun y : ℝ≥0∞ ↦ Specification.isssd (S := ℕ)
      (bern y) := by
  intro Λ A hA
  have hrw : (fun p : ℝ≥0∞ × (ℕ → Bool) ↦ Specification.isssd (bern p.1) Λ p.2 A) =
      fun p ↦ ∑ σ : {i // i ∈ Λ} → Bool,
        (juxt (Λ : Set ℕ) p.2 ⁻¹' A).indicator (fun τ ↦ ∏ i, bern p.1 {τ i}) σ := by
    funext p
    exact isssd_apply_eq_sum _ Λ p.2 hA
  rw [hrw]
  refine Finset.measurable_sum _ fun σ _ ↦ ?_
  have hsnd : @Measurable (ℝ≥0∞ × (ℕ → Bool)) (ℕ → Bool)
      (@Prod.instMeasurableSpace ℝ≥0∞ (ℕ → Bool) _ (cylinderEvents ((Λ : Set ℕ)ᶜ)))
      (cylinderEvents ((Λ : Set ℕ)ᶜ)) Prod.snd := measurable_snd
  have hfst : @Measurable (ℝ≥0∞ × (ℕ → Bool)) ℝ≥0∞
      (@Prod.instMeasurableSpace ℝ≥0∞ (ℕ → Bool) _ (cylinderEvents ((Λ : Set ℕ)ᶜ)))
      _ Prod.fst := measurable_fst
  have hset : @MeasurableSet (ℝ≥0∞ × (ℕ → Bool))
      (@Prod.instMeasurableSpace ℝ≥0∞ (ℕ → Bool) _ (cylinderEvents ((Λ : Set ℕ)ᶜ)))
      {p : ℝ≥0∞ × (ℕ → Bool) | juxt (Λ : Set ℕ) p.2 σ ∈ A} :=
    ((measurable_cylinderEvents_juxt_boundary σ).comp hsnd) hA
  have hind : (fun p : ℝ≥0∞ × (ℕ → Bool) ↦
        (juxt (Λ : Set ℕ) p.2 ⁻¹' A).indicator (fun τ ↦ ∏ i, bern p.1 {τ i}) σ) =
      {p : ℝ≥0∞ × (ℕ → Bool) | juxt (Λ : Set ℕ) p.2 σ ∈ A}.indicator
        fun p ↦ ∏ i, bern p.1 {σ i} := by
    funext p
    by_cases h : juxt (Λ : Set ℕ) p.2 σ ∈ A
    · rw [Set.indicator_of_mem (show σ ∈ juxt (Λ : Set ℕ) p.2 ⁻¹' A from h),
        Set.indicator_of_mem
          (show p ∈ {q : ℝ≥0∞ × (ℕ → Bool) | juxt (Λ : Set ℕ) q.2 σ ∈ A} from h)]
      rfl
    · rw [Set.indicator_of_notMem (show σ ∉ juxt (Λ : Set ℕ) p.2 ⁻¹' A from h),
        Set.indicator_of_notMem
          (show p ∉ {q : ℝ≥0∞ × (ℕ → Bool) | juxt (Λ : Set ℕ) q.2 σ ∈ A} from h)]
  rw [hind]
  exact Measurable.indicator
    ((Finset.measurable_prod _ fun i _ ↦ measurable_bern_apply {σ i}).comp hfst) hset

/-! ### The Bernoulli random fields and the strong law of large numbers -/

variable (y : ℝ≥0∞)

/-- Georgii (2.27): the Bernoulli random field `μ^y = (λ^y)^ℕ`. -/
noncomputable def bernoulliField : Measure (ℕ → Bool) := Measure.infinitePi fun _ : ℕ ↦ bern y

instance instIsProbabilityMeasureBernoulliField : IsProbabilityMeasure (bernoulliField y) := by
  rw [bernoulliField]; infer_instance

variable {y}

lemma spin_eq_indicator : spin = Set.indicator ({true} : Set Bool) 1 := by
  funext b; cases b <;> simp [spin]

lemma integral_spin_bern (y : ℝ≥0∞) : ∫ b, spin b ∂(bern y) = (min y 1).toReal := by
  rw [spin_eq_indicator]
  have h := integral_indicator_const (μ := bern y) (1 : ℝ) (measurableSet_singleton true)
  simpa [MeasureTheory.measureReal_def] using h

lemma min_ofReal_one {x : ℝ} (hx1 : x ≤ 1) : min (ENNReal.ofReal x) 1 = ENNReal.ofReal x :=
  min_eq_left (ENNReal.ofReal_le_one.2 hx1)

lemma bernoulliField_map_eval (y : ℝ≥0∞) (i : ℕ) :
    (bernoulliField y).map (fun ω : ℕ → Bool ↦ ω i) = bern y :=
  Measure.infinitePi_map_eval _ i

/-- **Georgii (2.27)**: the family `y ↦ μ^y` of Bernoulli fields is measurable for the Giry
σ-algebra. -/
lemma measurable_bernoulliField : Measurable (bernoulliField : ℝ≥0∞ → Measure (ℕ → Bool)) :=
  Measure.measurable_infinitePi_const.comp measurable_bern

/-- Every Bernoulli field is the Bernoulli field of a genuine `[0,1]` parameter. -/
lemma bernoulliField_ofReal_toReal (y : ℝ≥0∞) :
    bernoulliField (ENNReal.ofReal (min y 1).toReal) = bernoulliField y := by
  rw [bernoulliField, bernoulliField, bern_ofReal_toReal]

/-- **Georgii (2.27)**: by the strong law of large numbers, `ξ = x` almost surely under `μ^x`. -/
theorem xi_ae_eq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ᵐ ω ∂(bernoulliField (ENNReal.ofReal x)), xi ω = ENNReal.ofReal x := by
  set μ : Measure (ℕ → Bool) := bernoulliField (ENNReal.ofReal x) with hμ
  set X : ℕ → (ℕ → Bool) → ℝ := fun i ω ↦ spin (ω i) with hX
  have hXmeas : ∀ i, Measurable (X i) := fun i ↦ measurable_spin.comp (measurable_pi_apply i)
  have hindep : iIndepFun X μ := by
    rw [hμ, bernoulliField]
    exact iIndepFun_infinitePi fun _ ↦ measurable_spin
  have hmapi : ∀ i, μ.map (X i) = (bern (ENNReal.ofReal x)).map spin := by
    intro i
    have hcomp : X i = spin ∘ fun ω : ℕ → Bool ↦ ω i := rfl
    rw [hcomp, ← Measure.map_map measurable_spin (measurable_pi_apply i), hμ,
      bernoulliField_map_eval]
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i ↦
    ⟨(hXmeas i).aemeasurable, (hXmeas 0).aemeasurable, by rw [hmapi i, hmapi 0]⟩
  have hint : Integrable (X 0) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (hXmeas 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    have h1 := spin_nonneg (ω 0)
    have h2 := spin_le_one (ω 0)
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2
  have hmean : ∫ ω, X 0 ω ∂μ = x := by
    change ∫ ω, spin (ω 0) ∂μ = x
    have h1 : ∫ b, spin b ∂(μ.map fun ω : ℕ → Bool ↦ ω 0) = ∫ ω, spin (ω 0) ∂μ :=
      integral_map (measurable_pi_apply 0).aemeasurable measurable_spin.aestronglyMeasurable
    rw [← h1, hμ, bernoulliField_map_eval, integral_spin_bern, min_ofReal_one hx1,
      ENNReal.toReal_ofReal hx0]
  have hslln := ProbabilityTheory.strong_law_ae_real X hint
    (fun _ _ hij ↦ hindep.indepFun hij) hident
  rw [hmean] at hslln
  filter_upwards [hslln] with ω hω
  have h1 : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (avg ω n)) atTop (𝓝 (ENNReal.ofReal x)) :=
    ENNReal.tendsto_ofReal hω
  exact h1.liminf_eq

/-- **Georgii (2.27)**: the supports of the `μ^x` are separated by `ξ`. -/
theorem measure_xi_eq_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    bernoulliField (ENNReal.ofReal x) {ω | xi ω = ENNReal.ofReal x} = 1 := by
  have hmeas : MeasurableSet {ω : ℕ → Bool | xi ω = ENNReal.ofReal x} :=
    measurable_xi (measurableSet_singleton _)
  rw [← prob_compl_eq_zero_iff hmeas]
  have := (MeasureTheory.ae_iff).1 (xi_ae_eq hx0 hx1)
  simpa [Set.compl_ofPred] using this

/-- **Georgii (2.27)**, `ℝ≥0∞`-parameter form of `xi_ae_eq`: `ξ = y` almost surely under `μ^y`,
for every parameter `y ≤ 1`. -/
theorem xi_ae_eq' {y : ℝ≥0∞} (hy : y ≤ 1) : ∀ᵐ ω ∂(bernoulliField y), xi ω = y := by
  have hy' : ENNReal.ofReal y.toReal = y :=
    ENNReal.ofReal_toReal (hy.trans_lt ENNReal.one_lt_top).ne
  rw [← hy']
  exact xi_ae_eq ENNReal.toReal_nonneg (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hy)

/-- **Georgii (2.27)**: the law of the tail function `ξ` under `μ^y` is the Dirac measure at `y`;
this is what makes the mixing weight of a mixture of Bernoulli fields recoverable. -/
lemma map_xi_bernoulliField {y : ℝ≥0∞} (hy : y ≤ 1) :
    (bernoulliField y).map xi = Measure.dirac y := by
  rw [Measure.map_congr (xi_ae_eq' hy), Measure.map_const, measure_univ, one_smul]

/-! ### The glued specification of Example (2.27) -/

/-- **Georgii, Example (2.27)**: the specification obtained by gluing the independent
specifications `γ^y = λ^y` along the tail function `ξ`. -/
noncomputable def gammaEx : Specification ℕ Bool :=
  Specification.glued (fun y : ℝ≥0∞ ↦ Specification.isssd (bern y)) xi
    isMeasurableFamily_isssd_bern measurable_tail_xi

@[simp] lemma gammaEx_apply (Λ : Finset ℕ) (ω : ℕ → Bool) :
    gammaEx Λ ω = Specification.isssd (bern (xi ω)) Λ ω := rfl

/-- **Georgii, Example (2.27)**: every Bernoulli field `μ^x`, `x ∈ [0,1]`, is a Gibbs measure
for `γ`. -/
theorem isGibbsMeasure_bernoulliField {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    gammaEx.IsGibbsMeasure (bernoulliField (ENNReal.ofReal x)) := by
  have h : (Specification.isssd (bern (ENNReal.ofReal x))).IsGibbsMeasure
      (bernoulliField (ENNReal.ofReal x)) := by
    rw [Specification.isGibbsMeasure_isssd_iff]
    rfl
  exact Specification.isGibbsMeasure_glued _ _ (measure_xi_eq_one hx0 hx1) h

/-- **Georgii, Example (2.27)**: every Bernoulli field `μ^y`, for an arbitrary parameter
`y : ℝ≥0∞`, is a Gibbs measure for `γ`; `bern` truncates the parameter at `1`, so this is no more
than `isGibbsMeasure_bernoulliField`. -/
theorem isGibbsMeasure_bernoulliField' (y : ℝ≥0∞) :
    gammaEx.IsGibbsMeasure (bernoulliField y) := by
  rw [← bernoulliField_ofReal_toReal y]
  exact isGibbsMeasure_bernoulliField ENNReal.toReal_nonneg
    (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (min_le_right y 1))

/-- **Georgii, Example (2.27)**: on an event inside the finite volume `Λ` the glued kernel is the
Bernoulli field of parameter `ξ ω`, with no dependence left on the boundary condition:
`γ_Λ(A | ω) = μ^{ξ ω}(A)` for `A ∈ 𝓕_Λ`. -/
lemma gammaEx_apply_of_mem_cylinderEvents (Λ : Finset ℕ) (ω : ℕ → Bool) {A : Set (ℕ → Bool)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ Bool) (Λ : Set ℕ)] A) :
    gammaEx Λ ω A = bernoulliField (xi ω) A := by
  rw [gammaEx_apply, Specification.isssd_apply_of_mem_cylinderEvents _ Λ ω hA, bernoulliField]

/-! ### `C(γ) ≡ 0`: Georgii's interdependence matrix vanishes -/

lemma map_eval_isssd (ν : Measure Bool) [IsProbabilityMeasure ν] (i : ℕ) (ζ : ℕ → Bool) :
    (Specification.isssd ν ({i} : Finset ℕ) ζ).map (fun ω : ℕ → Bool ↦ ω i) = ν := by
  rw [isssd_apply_eq, Measure.map_map (measurable_pi_apply i) Measurable.juxt]
  have hi : i ∈ ((({i} : Finset ℕ) : Set ℕ)) := by simp
  have hcomp : ((fun ω : ℕ → Bool ↦ ω i) ∘ juxt (({i} : Finset ℕ) : Set ℕ) ζ)
      = fun σ : {j // j ∈ ({i} : Finset ℕ)} → Bool ↦ σ ⟨i, by simp⟩ := by
    funext σ
    simp [juxt]
  rw [hcomp]
  exact (measurePreserving_eval (fun _ : ({i} : Finset ℕ) ↦ ν) ⟨i, by simp⟩).map_eq

lemma map_eval_gammaEx (i : ℕ) (ζ : ℕ → Bool) :
    (gammaEx ({i} : Finset ℕ) ζ).map (fun ω : ℕ → Bool ↦ ω i) = bern (xi ζ) := by
  rw [gammaEx_apply]
  exact map_eval_isssd _ i ζ

/-- **Georgii, Example (2.27)**: Dobrushin's interdependence matrix of `γ` vanishes identically,
because a single-site modification of the boundary condition changes neither `ξ` nor the resulting
single-spin law. -/
theorem interdep_gammaEx (i j : ℕ) : Dobrushin.interdep gammaEx i j = 0 := by
  refine le_antisymm ?_ zero_le
  refine iSup_le fun ζ ↦ iSup_le fun η ↦ iSup_le fun h ↦ ?_
  have hxi : xi ζ = xi η :=
    dependsOn_xi ({j} : Finset ℕ) fun k hk ↦ h k (by simpa using hk)
  rw [map_eval_gammaEx, map_eval_gammaEx, hxi]
  simp [Dobrushin.unifDist]

/-- **Georgii, Example (2.27)**: Dobrushin's constant `c(γ)` is `0`. -/
theorem tsum_interdep_gammaEx (i : ℕ) : ∑' j, Dobrushin.interdep gammaEx i j = 0 := by
  simp [interdep_gammaEx]

/-! ### `𝒢(γ)` is uncountable -/

/-- **Georgii, Example (2.27)**: distinct parameters give distinct Bernoulli fields, because `ξ`
separates their supports. -/
theorem bernoulliField_injOn :
    Set.InjOn (fun x : ℝ ↦ bernoulliField (ENNReal.ofReal x)) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have hab' : bernoulliField (ENNReal.ofReal a) = bernoulliField (ENNReal.ofReal b) := hab
  by_contra hne
  have hne' : ENNReal.ofReal a ≠ ENNReal.ofReal b := by
    rw [Ne, ENNReal.ofReal_eq_ofReal_iff ha.1 hb.1]
    exact hne
  have h1 : bernoulliField (ENNReal.ofReal b) {ω | xi ω = ENNReal.ofReal a} = 1 := by
    rw [← hab']
    exact measure_xi_eq_one ha.1 ha.2
  have h2 : bernoulliField (ENNReal.ofReal b) {ω | xi ω = ENNReal.ofReal b} = 1 :=
    measure_xi_eq_one hb.1 hb.2
  have hdisj : Disjoint {ω : ℕ → Bool | xi ω = ENNReal.ofReal a}
      {ω : ℕ → Bool | xi ω = ENNReal.ofReal b} := by
    rw [Set.disjoint_left]
    intro ω hωa hωb
    exact hne' (hωa.symm.trans hωb)
  have hmeasb : MeasurableSet {ω : ℕ → Bool | xi ω = ENNReal.ofReal b} :=
    measurable_xi (measurableSet_singleton _)
  have hle : bernoulliField (ENNReal.ofReal b)
      ({ω : ℕ → Bool | xi ω = ENNReal.ofReal a} ∪ {ω | xi ω = ENNReal.ofReal b}) ≤ 1 := by
    simpa using measure_mono (μ := bernoulliField (ENNReal.ofReal b)) (Set.subset_univ
      ({ω : ℕ → Bool | xi ω = ENNReal.ofReal a} ∪ {ω | xi ω = ENNReal.ofReal b}))
  rw [measure_union hdisj hmeasb, h1, h2] at hle
  exact absurd hle (by norm_num)

/-- **Georgii, Example (2.27)**: `𝒢(γ)` is uncountable. -/
theorem not_countable_gibbsMeasures :
    ¬ {μ : Measure (ℕ → Bool) | gammaEx.IsGibbsMeasure μ}.Countable := by
  intro hG
  have hmaps : Set.MapsTo (fun x : ℝ ↦ bernoulliField (ENNReal.ofReal x)) (Set.Icc 0 1)
      {μ : Measure (ℕ → Bool) | gammaEx.IsGibbsMeasure μ} :=
    fun x hx ↦ isGibbsMeasure_bernoulliField hx.1 hx.2
  have hIcc : (Set.Icc (0 : ℝ) 1).Countable := hmaps.countable_of_injOn bernoulliField_injOn hG
  simp only [Cardinal.Real.Icc_countable_iff] at hIcc
  norm_num at hIcc

/-- **Georgii, Example (2.27)**: `γ` is not quasilocal. If it were, Dobrushin's uniqueness
theorem (8.7) would apply — `c(γ) = 0 < 1` — and `𝒢(γ)` would be a singleton, contradicting
`not_countable_gibbsMeasures`. This is exactly why Georgii's Definition (8.6) carries the
quasilocality conjunct next to `c(γ) < 1`. -/
theorem not_isQuasilocal_gammaEx : ¬ gammaEx.IsQuasilocal := by
  intro hq
  have hd : Dobrushin.IsDobrushin gammaEx :=
    ⟨hq, 0, zero_lt_one, fun i ↦ le_of_eq (tsum_interdep_gammaEx i)⟩
  obtain ⟨μ, -, huniq⟩ :=
    Dobrushin.existsUnique_mem_GP_of_isDobrushin_of_standardBorel hq hd
  have h0 : (⟨bernoulliField (ENNReal.ofReal 0), inferInstance⟩ :
      ProbabilityMeasure (ℕ → Bool)) ∈ GP gammaEx :=
    isGibbsMeasure_bernoulliField le_rfl zero_le_one
  have h1 : (⟨bernoulliField (ENNReal.ofReal 1), inferInstance⟩ :
      ProbabilityMeasure (ℕ → Bool)) ∈ GP gammaEx :=
    isGibbsMeasure_bernoulliField zero_le_one le_rfl
  have heq := (huniq _ h0).trans (huniq _ h1).symm
  have heq' : bernoulliField (ENNReal.ofReal 0) = bernoulliField (ENNReal.ofReal 1) :=
    congrArg (fun p : ProbabilityMeasure (ℕ → Bool) ↦ (p : Measure (ℕ → Bool))) heq
  have := bernoulliField_injOn (by norm_num) (by norm_num) heq'
  norm_num at this

/-- **Georgii, Example (2.27)**, packaged as the justification for the quasilocality conjunct of
Definition (8.6): there is a specification satisfying the second conjunct `c(γ) < 1` of
`MeasureTheory.GibbsMeasure.Dobrushin.IsDobrushin` — with `c(γ) = 0`, in fact — whose set of Gibbs
measures is uncountable. So the second conjunct alone cannot imply uniqueness, and the
quasilocality conjunct is not decorative. -/
theorem exists_not_countable_gibbsMeasures_of_tsum_interdep_lt_one :
    ∃ γ : Specification ℕ Bool,
      (∃ c : ℝ≥0∞, c < 1 ∧ ∀ i, ∑' j, Dobrushin.interdep γ i j ≤ c) ∧
        ¬ {μ : Measure (ℕ → Bool) | γ.IsGibbsMeasure μ}.Countable :=
  ⟨gammaEx, ⟨0, zero_lt_one, fun i ↦ le_of_eq (tsum_interdep_gammaEx i)⟩,
    not_countable_gibbsMeasures⟩

/-! ### `𝒢(γ) = {∫ w(dx) μ^x : w ∈ 𝓟([0,1])}`: Georgii's identification -/

instance instIsProbabilityMeasureBindBernoulliField (w : Measure ℝ≥0∞)
    [IsProbabilityMeasure w] : IsProbabilityMeasure (w.bind bernoulliField) :=
  MeasureTheory.isProbabilityMeasure_bind measurable_bernoulliField.aemeasurable
    (.of_forall fun _ ↦ inferInstance)

/-- **Georgii, Example (2.27)**, the inclusion `⊇`: every mixture `∫ w(dx) μ^x` of Bernoulli
fields is a Gibbs measure for `γ`. -/
theorem isGibbsMeasure_bind_bernoulliField (w : Measure ℝ≥0∞) [IsProbabilityMeasure w] :
    gammaEx.IsGibbsMeasure (w.bind bernoulliField) :=
  gammaEx.isGibbsMeasure_bind measurable_bernoulliField.aemeasurable
    (.of_forall fun _ ↦ inferInstance) (.of_forall isGibbsMeasure_bernoulliField')

/-- The law of `ξ` under a probability measure is carried by `[0,1]`, so it is a weight in
Georgii's `𝓟(X)` with `X = [0,1]`. -/
lemma map_xi_apply_Icc (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] :
    μ.map xi (Set.Icc 0 1) = 1 := by
  have hpre : xi ⁻¹' (Set.Icc 0 1) = Set.univ := by
    ext ω
    simp [xi_le_one ω]
  rw [Measure.map_apply measurable_xi measurableSet_Icc, hpre, measure_univ]

/-- **Georgii, Example (2.27)**, the inclusion `⊆`: a Gibbs measure for `γ` is the mixture of the
Bernoulli fields along the law of its own tail function `ξ`. Only the DLR equation `μ γ_Λ = μ` is
used: on a local event `A ∈ 𝓕_Λ` it reads `μ(A) = ∫ μ(dω) μ^{ξ ω}(A)`, and the local events
generate `𝓕`. -/
theorem eq_bind_map_xi {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]
    (hμ : gammaEx.IsGibbsMeasure μ) : μ = (μ.map xi).bind bernoulliField := by
  have hw : IsProbabilityMeasure (μ.map xi) :=
    Measure.isProbabilityMeasure_map measurable_xi.aemeasurable
  have hbind : ∀ Λ : Finset ℕ, μ.bind (gammaEx Λ) = μ :=
    Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ
  refine MeasureTheory.ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun A hA ↦ ?_) (by rw [measure_univ, measure_univ])
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hΛ
  have hker : AEMeasurable (gammaEx Λ : (ℕ → Bool) → Measure (ℕ → Bool)) μ :=
    ((gammaEx Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
  calc μ A = (μ.bind (gammaEx Λ)) A := by rw [hbind]
    _ = ∫⁻ ω, gammaEx Λ ω A ∂μ := Measure.bind_apply hAm hker
    _ = ∫⁻ ω, bernoulliField (xi ω) A ∂μ :=
        lintegral_congr fun ω ↦ gammaEx_apply_of_mem_cylinderEvents Λ ω hΛ
    _ = ∫⁻ x, bernoulliField x A ∂(μ.map xi) :=
        (lintegral_map ((Measure.measurable_coe hAm).comp measurable_bernoulliField)
          measurable_xi).symm
    _ = ((μ.map xi).bind bernoulliField) A :=
        (Measure.bind_apply hAm measurable_bernoulliField.aemeasurable).symm

/-- **Georgii, Example (2.27)**, the full identification:
`𝒢(γ) = {∫ w(dx) μ^x : w ∈ 𝓟([0,1])}`, the weights being the probability measures on `ℝ≥0∞`
carried by `[0,1]`. -/
theorem G_gammaEx_eq :
    G gammaEx = {μ : Measure (ℕ → Bool) | ∃ w : Measure ℝ≥0∞, IsProbabilityMeasure w ∧
      w (Set.Icc 0 1) = 1 ∧ μ = w.bind bernoulliField} := by
  ext μ
  constructor
  · rintro ⟨hprob, hgibbs⟩
    exact ⟨μ.map xi, Measure.isProbabilityMeasure_map measurable_xi.aemeasurable,
      map_xi_apply_Icc μ, eq_bind_map_xi hgibbs⟩
  · rintro ⟨w, hw, -, rfl⟩
    exact ⟨inferInstance, isGibbsMeasure_bind_bernoulliField w⟩

/-- **Georgii, Example (2.27)**: the mixing weight is recovered from the mixture as the law of the
tail function `ξ`, because `ξ = x` holds `μ^x`-almost surely. -/
theorem map_xi_bind_bernoulliField (w : Measure ℝ≥0∞) [IsProbabilityMeasure w]
    (hw : w (Set.Icc 0 1) = 1) : (w.bind bernoulliField).map xi = w := by
  rw [Measure.map_bind measurable_bernoulliField measurable_xi]
  have hIcc : ∀ᵐ x ∂w, x ∈ Set.Icc (0 : ℝ≥0∞) 1 :=
    mem_ae_iff.2 ((prob_compl_eq_zero_iff measurableSet_Icc).2 hw)
  have hae : ∀ᵐ x ∂w, (bernoulliField x).map xi = Measure.dirac x := by
    filter_upwards [hIcc] with x hx
    exact map_xi_bernoulliField hx.2
  rw [Measure.bind_congr_right hae]
  exact Measure.bind_dirac

/-- **Georgii, Example (2.27)**: the weight in the representation `μ = ∫ w(dx) μ^x` is unique. -/
theorem eq_of_bind_bernoulliField_eq {w w' : Measure ℝ≥0∞} [IsProbabilityMeasure w]
    [IsProbabilityMeasure w'] (hw : w (Set.Icc 0 1) = 1) (hw' : w' (Set.Icc 0 1) = 1)
    (h : w.bind bernoulliField = w'.bind bernoulliField) : w = w' := by
  rw [← map_xi_bind_bernoulliField w hw, ← map_xi_bind_bernoulliField w' hw', h]

/-- **Georgii, Example (2.27)**, sharp form of the identification: every Gibbs measure for `γ` is
`∫ w(dx) μ^x` for a *unique* probability weight `w` on `[0,1]`, namely the law of `ξ`. So `𝒢(γ)`
is affinely isomorphic to `𝓟([0,1])`. -/
theorem existsUnique_weight_of_mem_G {μ : Measure (ℕ → Bool)} (hμ : μ ∈ G gammaEx) :
    ∃! w : Measure ℝ≥0∞, IsProbabilityMeasure w ∧ w (Set.Icc 0 1) = 1 ∧
      μ = w.bind bernoulliField := by
  obtain ⟨w, hwprob, hwsupp, hwμ⟩ := G_gammaEx_eq.subset hμ
  refine ⟨w, ⟨hwprob, hwsupp, hwμ⟩, ?_⟩
  rintro w' ⟨hw'prob, hw'supp, hw'μ⟩
  exact eq_of_bind_bernoulliField_eq hw'supp hwsupp (hw'μ.symm.trans hwμ)

end MeasureTheory.GibbsMeasure.Exchangeable

