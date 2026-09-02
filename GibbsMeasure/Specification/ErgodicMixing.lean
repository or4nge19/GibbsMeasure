/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Dynamics.Ergodic.MeanErgodic
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.SetwiseConvergence
public import GibbsMeasure.Specification.Ergodicity
public import GibbsMeasure.Topology.LocalConvergence
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Group.Pointwise

/-!
# Ergodicity as mixing on average (Georgii §14.1, Proposition (14.7))

For `μ ∈ 𝓟_Θ` and a sequence of cubes `Λ_n ⊆ ℤ^d` with `|Λ_n| → ∞`, Georgii's Proposition (14.7)
says that the following are equivalent:

* (i) `μ` is ergodic;
* (ii) for every event `A`,
  `sup_B | |Λ_n|⁻¹ ∑_{i ∈ Λ_n} μ(A ∩ θ_i B) − μ(A) μ(B) | → 0`;
* (iii) for all cylinder events `A`, `B`,
  `|Λ_n|⁻¹ ∑_{i ∈ Λ_n} μ(A ∩ θ_i B) → μ(A) μ(B)`.

Nothing in the proof uses the cubes beyond the Følner property, nor `ℤ^d` beyond its acting by
measure-preserving maps, so the statements are proved first for a countable group `G` acting
measurably on a probability space along a Følner net of finite sets `F : κ → Finset G`
(the setting of the mean ergodic theorem in `GibbsMeasure.Mathlib.Dynamics.Ergodic.MeanErgodic`):

* `MeasureTheory.tendstoUniformlyOn_inv_card_mul_sum_measureReal_inter_smul` — (i) ⟹ (ii):
  the "sup over `B`" of Georgii is uniform convergence on the measurable sets
  (`TendstoUniformlyOn`). The proof is Georgii's: the difference is `∫_B (R_n 1_A − μ(A)) dμ`,
  bounded by `‖R_n 1_A − μ(A)‖₁`, which tends to `0` by the mean ergodic theorem (14.A5) since
  `μ[1_A | 𝓘] = μ(A)` a.e. for ergodic `μ`.
* `MeasureTheory.ergodicSMul_of_forall_mem_tendsto_inv_card_mul_sum_measureReal_inter_smul` —
  (iii) ⟹ (i), from a π-system generating the σ-algebra. Georgii's Dynkin-system argument is
  `MeasureTheory.tendsto_measureReal_of_isPiSystem_of_le`: setwise convergence of measures
  dominated by a finite measure extends from a generating π-system to the whole σ-algebra. This
  direction uses neither the Følner property nor the ergodic theorem: for `A ∈ 𝓘` the averages
  are constantly `μ(A)`, so `μ(A) = μ(A)²`.
* `MeasureTheory.ergodicSMul_iff_tendstoUniformlyOn_inv_card_mul_sum_measureReal_inter_smul`,
  `MeasureTheory.ergodicSMul_iff_forall_mem_tendsto_inv_card_mul_sum_measureReal_inter_smul` —
  the equivalences (i) ⟺ (ii) and (i) ⟺ (iii).
* `MeasureTheory.GibbsMeasure.ergodicSMul_shiftGroup_tfae` — **Proposition (14.7)** as stated:
  for the shift group `Θ` on configuration space `S → E`, `μ ∈ 𝓟_Θ`, and a Følner sequence of
  finite volumes `Λ_n ⊆ S` (any sequence of cubes with `|Λ_n| → ∞` on `ℤ^d`), with the cylinder
  events `localEvents S E`.

## Conventions

Georgii writes `μ(A ∩ θ_i B)` with `θ_i B` the *image* of `B` under the shift `θ_i`. Here the
group acts on the left, `i • ω`, and `i • B` is the pointwise image `(i • ·) '' B`, which is the
preimage under the inverse, `(i⁻¹ • ·) ⁻¹' B` (`Set.preimage_smul_inv`). Thus
`μ (A ∩ i • B) = μ ((i • ·) ⁻¹' A ∩ B) = ∫_B 1_A (i • ω) dμ(ω)`
(`MeasureTheory.measure_inter_inv_smul`), so that the ergodic average of `1_A` over `F` is what
appears, exactly as in Georgii's proof. Had one used the preimage `(i • ·) ⁻¹' B` instead, the
averages would run over `F⁻¹`; for `ℤ^d` and cubes both families are Følner, and on an abelian
group they coincide up to reflection.

## Hypotheses

* `Countable G` and `IsProbabilityMeasure μ` throughout, as in Georgii (`μ ∈ 𝓟_Θ`); countability
  is what identifies `ErgodicSMul` with triviality on the strictly invariant σ-algebra
  (`ergodicSMul_iff_forall_measurableSet_invariants`, Remark (14.3)(2)).
* The Følner hypothesis `hF` and eventual non-emptiness `hne` are used only in (i) ⟹ (ii), through
  the mean ergodic theorem. (iii) ⟹ (i) needs only `hne` and a non-trivial filter.
-/

@[expose] public section

open Filter Finset Set MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped Topology Pointwise symmDiff ENNReal

namespace MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

section Group

variable {G : Type*} [Group G] [MulAction G Ω] [MeasurableConstSMul G Ω] {μ : Measure Ω}
  {κ : Type*} {l : Filter κ} {F : κ → Finset G}

omit [MeasurableConstSMul G Ω] in
/-- `μ(A ∩ i • B) = μ(B ∩ i⁻¹ • A)` for an invariant measure. -/
lemma measureReal_inter_smul_comm [SMulInvariantMeasure G Ω μ] (i : G) (A B : Set Ω) :
    μ.real (A ∩ i • B) = μ.real (B ∩ i⁻¹ • A) := by
  rw [measureReal_def, measureReal_def, measure_inter_inv_smul, inter_comm]

/-- Georgii's identity `μ(A ∩ θ_i B) = ∫_B 1_A ∘ θ_i dμ`, in the left-action convention. -/
lemma measureReal_inter_smul_eq_setIntegral [SMulInvariantMeasure G Ω μ] {A : Set Ω}
    (hA : MeasurableSet A) (B : Set Ω) (i : G) :
    μ.real (A ∩ i • B) = ∫ ω in B, A.indicator (1 : Ω → ℝ) (i • ω) ∂μ := by
  have : (fun ω ↦ A.indicator (1 : Ω → ℝ) (i • ω)) = ((i • ·) ⁻¹' A).indicator 1 := rfl
  rw [this, setIntegral_indicator (hA.preimage (measurable_const_smul i))]
  simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
  rw [Set.preimage_smul, measureReal_inter_smul_comm]

/-- Georgii's identity behind (14.7): the deviation of the averaged correlation from
`μ(A) μ(B)` is `∫_B (R_F 1_A − μ(A)) dμ`, where `R_F 1_A = |F|⁻¹ ∑_{i ∈ F} 1_A ∘ (i • ·)`. -/
lemma inv_card_mul_sum_measureReal_inter_smul_sub_eq_setIntegral [SMulInvariantMeasure G Ω μ]
    [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet A) (B : Set Ω) (F : Finset G) :
    (F.card : ℝ)⁻¹ * ∑ i ∈ F, μ.real (A ∩ i • B) - μ.real A * μ.real B =
      ∫ ω in B, (((F.card : ℝ)⁻¹ • ∑ i ∈ F, A.indicator (1 : Ω → ℝ) (i • ω)) - μ.real A) ∂μ := by
  have hint : ∀ i : G, Integrable (fun ω ↦ A.indicator (1 : Ω → ℝ) (i • ω)) (μ.restrict B) :=
    fun i ↦ ((measurePreserving_smul i μ).integrable_comp_of_integrable
      ((integrable_const (1 : ℝ)).indicator hA)).integrableOn
  have h1 : Integrable (fun ω ↦ (F.card : ℝ)⁻¹ • ∑ i ∈ F, A.indicator (1 : Ω → ℝ) (i • ω))
      (μ.restrict B) :=
    (integrable_finsetSum F fun i _ ↦ hint i).smul (F.card : ℝ)⁻¹
  rw [integral_sub h1 (integrable_const (μ.real A)), integral_smul,
    integral_finsetSum F fun i _ ↦ hint i, setIntegral_const, smul_eq_mul, smul_eq_mul,
    mul_comm (μ.real B)]
  congr 2
  exact Finset.sum_congr rfl fun i _ ↦ measureReal_inter_smul_eq_setIntegral hA B i

/-- **Georgii (14.7), (i) ⟹ (ii).** For an ergodic `μ` and a Følner net of finite sets, the
averaged correlations `|F k|⁻¹ ∑_{i ∈ F k} μ(A ∩ i • B)` converge to `μ(A) μ(B)` *uniformly in
the measurable set `B`*: this is Georgii's `sup_B |⋯| → 0`. The proof is the mean ergodic
theorem (14.A5) applied to `1_A`, whose conditional expectation on the invariant σ-algebra is the
constant `μ(A)` by ergodicity. -/
theorem tendstoUniformlyOn_inv_card_mul_sum_measureReal_inter_smul [Countable G] [DecidableEq G]
    [SMulInvariantMeasure G Ω μ] [IsProbabilityMeasure μ] (hμ : ErgodicSMul G Ω μ)
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    {A : Set Ω} (hA : MeasurableSet A) :
    TendstoUniformlyOn (fun k B ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, μ.real (A ∩ i • B))
      (fun B ↦ μ.real A * μ.real B) l {B | MeasurableSet B} := by
  set f : Ω → ℝ := A.indicator 1 with hf_def
  have hf : Integrable f μ := (integrable_const (1 : ℝ)).indicator hA
  have htriv := (ergodicSMul_iff_forall_measurableSet_invariants ‹_›).1 hμ
  have hcond : μ[f | MeasurableSpace.smulInvariants G Ω] =ᵐ[μ] fun _ ↦ μ.real A := by
    have := condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one
      (MeasurableSpace.smulInvariants_le (M := G)) htriv f
    rwa [hf_def, integral_indicator_one hA] at this
  have hmet : Tendsto (fun k ↦ ∫ ω, ‖((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω) - μ.real A‖ ∂μ) l
      (𝓝 0) := by
    refine (tendsto_integral_norm_inv_card_smul_sum_sub_condExp hne hF hf).congr fun k ↦
      integral_congr_ae ?_
    filter_upwards [hcond] with ω hω
    rw [hω]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hmet.eventually (gt_mem_nhds hε)] with k hk B hB
  have hint : Integrable (fun ω ↦ ((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω) - μ.real A) μ := by
    have h1 : Integrable (fun ω ↦ ((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω)) μ :=
      (integrable_finsetSum (F k) fun i _ ↦
        (measurePreserving_smul i μ).integrable_comp_of_integrable hf).smul ((F k).card : ℝ)⁻¹
    exact h1.sub (integrable_const (μ.real A))
  rw [Real.dist_eq, abs_sub_comm,
    inv_card_mul_sum_measureReal_inter_smul_sub_eq_setIntegral hA B]
  calc |∫ ω in B, (((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω) - μ.real A) ∂μ|
      ≤ ∫ ω in B, ‖((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω) - μ.real A‖ ∂μ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω) - μ.real A‖ ∂μ :=
        setIntegral_le_integral hint.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
    _ < ε := hk

/-- **Georgii (14.7), (iii) ⟹ (i).** If the averaged correlations
`|F k|⁻¹ ∑_{i ∈ F k} μ(A ∩ i • B)` converge to `μ(A) μ(B)` for all `A`, `B` in a π-system
generating the σ-algebra, then `μ` is ergodic. Georgii's Dynkin-system argument
(`tendsto_measureReal_of_isPiSystem_of_le`, once in each variable) extends the convergence to
all measurable `A`, `B`; for an invariant `A` the averages are constantly `μ(A)`, whence
`μ(A) = μ(A)²`. Neither the Følner property nor the ergodic theorem is used. -/
theorem ergodicSMul_of_forall_mem_tendsto_inv_card_mul_sum_measureReal_inter_smul [Countable G]
    [SMulInvariantMeasure G Ω μ] [IsProbabilityMeasure μ] [l.NeBot]
    (hne : ∀ᶠ k in l, (F k).Nonempty) {C : Set (Set Ω)}
    (hgen : m = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (h : ∀ A ∈ C, ∀ B ∈ C, Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, μ.real (A ∩ i • B)) l
      (𝓝 (μ.real A * μ.real B))) :
    ErgodicSMul G Ω μ := by
  have hall : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, μ.real (A ∩ i • B)) l
        (𝓝 (μ.real A * μ.real B)) := by
    intro A hA B hB
    -- first in `B`, for `A ∈ C`
    have h1 : ∀ A ∈ C, Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, μ.real (A ∩ i • B)) l
        (𝓝 (μ.real A * μ.real B)) := by
      intro A hA
      simp only [measureReal_inter_smul_comm _ A]
      refine tendsto_inv_card_mul_sum_measureReal_inter_of_isPiSystem hne hgen hpi
        (T := fun i ↦ i⁻¹ • A) (fun i ↦ by rw [measureReal_def, measure_smul]; rfl) ?_ hB
      intro B hB
      simpa only [measureReal_inter_smul_comm _ A] using h A hA B hB
    -- then in `A`, for measurable `B`
    simp only [mul_comm (μ.real _) (μ.real B)]
    exact tendsto_inv_card_mul_sum_measureReal_inter_of_isPiSystem hne hgen hpi
      (T := fun i ↦ i • B) (fun i ↦ by rw [measureReal_def, measure_smul]; rfl)
      (fun A hA ↦ by simpa only [mul_comm (μ.real B)] using h1 A hA) hA
  refine (ergodicSMul_iff_forall_measurableSet_invariants ‹_›).2 fun A hA ↦ ?_
  have hAi : ∀ i : G, i • A = A := fun i ↦ by rw [← preimage_smul_inv]; exact hA.2 i⁻¹
  have hlim := hall A hA.1 A hA.1
  have hconst : Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, μ.real (A ∩ i • A)) l
      (𝓝 (μ.real A)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hne] with k hk
    simp only [hAi, inter_self, Finset.sum_const, nsmul_eq_mul]
    rw [inv_mul_cancel_left₀ (by exact_mod_cast hk.card_pos.ne')]
  have heq : μ.real A = μ.real A * μ.real A := tendsto_nhds_unique hconst hlim
  have hprod : μ.real A * (μ.real A - 1) = 0 := by rw [mul_sub, mul_one]; linarith
  rcases mul_eq_zero.1 hprod with h0 | h1
  · left
    rwa [measureReal_eq_zero_iff] at h0
  · right
    rw [measureReal_def] at h1
    exact (ENNReal.toReal_eq_one_iff _).1 (by linarith)

/-- **Georgii (14.7), (i) ⟺ (ii)** for a countable group acting along a Følner net: `μ` is ergodic
iff for every event `A` the averaged correlations `|F k|⁻¹ ∑_{i ∈ F k} μ(A ∩ i • B)` converge to
`μ(A) μ(B)` uniformly in the event `B`. -/
theorem ergodicSMul_iff_tendstoUniformlyOn_inv_card_mul_sum_measureReal_inter_smul [Countable G]
    [DecidableEq G] [SMulInvariantMeasure G Ω μ] [IsProbabilityMeasure μ] [l.NeBot]
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0)) :
    ErgodicSMul G Ω μ ↔ ∀ A, MeasurableSet A →
      TendstoUniformlyOn (fun k B ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, μ.real (A ∩ i • B))
        (fun B ↦ μ.real A * μ.real B) l {B | MeasurableSet B} := by
  refine ⟨fun hμ A hA ↦ tendstoUniformlyOn_inv_card_mul_sum_measureReal_inter_smul hμ hne hF hA,
    fun h ↦ ergodicSMul_of_forall_mem_tendsto_inv_card_mul_sum_measureReal_inter_smul hne
      MeasurableSpace.generateFrom_measurableSet.symm MeasurableSpace.isPiSystem_measurableSet
      fun A hA B hB ↦ (h A hA).tendsto_at hB⟩

/-- **Georgii (14.7), (i) ⟺ (iii)** for a countable group acting along a Følner net: `μ` is
ergodic iff `|F k|⁻¹ ∑_{i ∈ F k} μ(A ∩ i • B) → μ(A) μ(B)` for all `A`, `B` in a π-system
generating the σ-algebra. -/
theorem ergodicSMul_iff_forall_mem_tendsto_inv_card_mul_sum_measureReal_inter_smul [Countable G]
    [DecidableEq G] [SMulInvariantMeasure G Ω μ] [IsProbabilityMeasure μ] [l.NeBot]
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    {C : Set (Set Ω)} (hgen : m = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C) :
    ErgodicSMul G Ω μ ↔ ∀ A ∈ C, ∀ B ∈ C,
      Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, μ.real (A ∩ i • B)) l
        (𝓝 (μ.real A * μ.real B)) := by
  have hmeasC : ∀ t ∈ C, MeasurableSet t := fun t ht ↦
    hgen ▸ MeasurableSpace.measurableSet_generateFrom ht
  exact ⟨fun hμ A hA B hB ↦ (tendstoUniformlyOn_inv_card_mul_sum_measureReal_inter_smul hμ hne hF
      (hmeasC A hA)).tendsto_at (hmeasC B hB),
    ergodicSMul_of_forall_mem_tendsto_inv_card_mul_sum_measureReal_inter_smul hne hgen hpi⟩

end Group

/-! ### Georgii's shift group -/

namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S]

/-- The shifts `θ_j`, `j ∈ S`, as elements of the shift group `Θ` (Georgii (5.2)(1)); the map
`j ↦ θ_j` is injective (it is read off the site part `τ_* = (· + j)`). -/
def shiftEmbedding (E : Type*) [MeasurableSpace E] : S ↪ shiftGroup S E where
  toFun j := ⟨shift E j, shift_mem_shiftGroup j⟩
  inj' j j' h := by
    have h' := congrArg (fun τ : shiftGroup S E ↦ (τ : Transformation S E).sites 0) h
    simpa [shift] using h'

@[simp] lemma coe_shiftEmbedding (j : S) :
    ((shiftEmbedding E j : shiftGroup S E) : Transformation S E) = shift E j :=
  rfl

/-- `θ_i ∘ θ_j = θ_{i + j}` (Georgii (5.2)(1)), in the transformation group. -/
lemma shift_mul_shift (i j : S) : shift E i * shift E j = shift E (i + j) := by
  refine Transformation.ext (Equiv.ext fun k ↦ ?_) rfl
  show k + j + i = k + (i + j)
  rw [add_assoc, add_comm j i]

lemma shiftEmbedding_mul (i j : S) :
    shiftEmbedding E i * shiftEmbedding E j = shiftEmbedding E (i + j) :=
  Subtype.ext (shift_mul_shift i j)

lemma shiftEmbedding_smul_set (j : S) (B : Set (S → E)) :
    shiftEmbedding E j • B = shift E j • B :=
  rfl

variable [DecidableEq S]

/-- The Følner ratios of a finite volume `Λ ⊆ S` and of its image in the shift group agree:
`(θ_g • θ(Λ)) ∆ θ(Λ)` is the image of `(g +ᵥ Λ) ∆ Λ`. -/
lemma card_smul_map_shiftEmbedding_symmDiff [DecidableEq (shiftGroup S E)] (g : S)
    (Λ : Finset S) :
    ((shiftEmbedding E g • Λ.map (shiftEmbedding E)) ∆ Λ.map (shiftEmbedding E)).card =
      ((g +ᵥ Λ) ∆ Λ).card := by
  have h : shiftEmbedding E g • Λ.map (shiftEmbedding E) = (g +ᵥ Λ).map (shiftEmbedding E) := by
    ext x
    simp only [Finset.mem_smul_finset, Finset.mem_map, Finset.mem_vadd_finset, vadd_eq_add,
      smul_eq_mul]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨g + a, ⟨a, ha, rfl⟩, (shiftEmbedding_mul g a).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨shiftEmbedding E a, ⟨a, ha, rfl⟩, shiftEmbedding_mul g a⟩
  rw [h, Finset.map_eq_image, Finset.map_eq_image,
    ← Finset.image_symmDiff _ _ (shiftEmbedding E).injective,
    Finset.card_image_of_injective _ (shiftEmbedding E).injective]

/-- **Georgii, Proposition (14.7).** For a `Θ`-invariant random field `μ ∈ 𝓟_Θ` on `S → E` and a
Følner sequence of finite volumes `Λ_n ⊆ S` — on `ℤ^d`, any sequence of cubes with `|Λ_n| → ∞` —
the following are equivalent:

1. `μ` is ergodic;
2. for every event `A`,
   `sup_B | |Λ_n|⁻¹ ∑_{i ∈ Λ_n} μ(A ∩ θ_i B) − μ(A) μ(B) | → 0`
   (uniform convergence in the measurable set `B`);
3. for all cylinder events `A`, `B`, `|Λ_n|⁻¹ ∑_{i ∈ Λ_n} μ(A ∩ θ_i B) → μ(A) μ(B)`.

Here `θ_i B = shift E i • B` is the image of `B` under the shift `θ_i`, as in Georgii. -/
theorem ergodicSMul_shiftGroup_tfae [Countable S] {μ : Measure (S → E)}
    (hμ : μ ∈ invariantFields (shiftGroup S E)) {κ : Type*} {l : Filter κ} [l.NeBot]
    {Λ : κ → Finset S} (hne : ∀ᶠ n in l, (Λ n).Nonempty)
    (hΛ : ∀ j : S, Tendsto (fun n ↦ (((j +ᵥ Λ n) ∆ Λ n).card : ℝ) / (Λ n).card) l (𝓝 0)) :
    [ErgodicSMul (shiftGroup S E) (S → E) μ,
      ∀ A, MeasurableSet A →
        TendstoUniformlyOn
          (fun n B ↦ ((Λ n).card : ℝ)⁻¹ * ∑ j ∈ Λ n, μ.real (A ∩ shift E j • B))
          (fun B ↦ μ.real A * μ.real B) l {B | MeasurableSet B},
      ∀ A ∈ localEvents S E, ∀ B ∈ localEvents S E,
        Tendsto (fun n ↦ ((Λ n).card : ℝ)⁻¹ * ∑ j ∈ Λ n, μ.real (A ∩ shift E j • B)) l
          (𝓝 (μ.real A * μ.real B))].TFAE := by
  classical
  have := hμ.1
  have := hμ.2
  set F : κ → Finset (shiftGroup S E) := fun n ↦ (Λ n).map (shiftEmbedding E) with hF_def
  have hne' : ∀ᶠ n in l, (F n).Nonempty := hne.mono fun n hn ↦ Finset.map_nonempty.2 hn
  have hF : ∀ g : shiftGroup S E,
      Tendsto (fun n ↦ (((g • F n) ∆ F n).card : ℝ) / (F n).card) l (𝓝 0) := by
    intro g
    obtain ⟨j, hj⟩ := g.2
    have hg : g = shiftEmbedding E j := Subtype.ext hj.symm
    subst hg
    simpa only [hF_def, card_smul_map_shiftEmbedding_symmDiff, Finset.card_map] using hΛ j
  have hsum : ∀ n (A B : Set (S → E)),
      ((F n).card : ℝ)⁻¹ * ∑ i ∈ F n, μ.real (A ∩ i • B) =
        ((Λ n).card : ℝ)⁻¹ * ∑ j ∈ Λ n, μ.real (A ∩ shift E j • B) := by
    intro n A B
    rw [hF_def, Finset.card_map, Finset.sum_map]
    rfl
  have h12 := ergodicSMul_iff_tendstoUniformlyOn_inv_card_mul_sum_measureReal_inter_smul
    (μ := μ) hne' hF
  have h13 := ergodicSMul_iff_forall_mem_tendsto_inv_card_mul_sum_measureReal_inter_smul
    (μ := μ) hne' hF (C := localEvents S E) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders
  simp only [hsum] at h12 h13
  tfae_have 1 ↔ 2 := h12
  tfae_have 1 ↔ 3 := h13
  tfae_finish

end GibbsMeasure

end MeasureTheory
