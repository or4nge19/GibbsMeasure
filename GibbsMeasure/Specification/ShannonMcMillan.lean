/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Dynamics.Ergodic.ShannonMcMillanCube
public import GibbsMeasure.Specification.SpecificEntropy

/-!
# The theorem of McMillan for a shift-invariant random field (Georgii, §15.2 and §15.5)

Let `E` be a finite state space, `λ = |E|⁻¹ ∑_x δ_x` the uniform a priori measure and
`μ ∈ 𝓟_Θ` a shift-invariant random field on `Ω = E^{ℤ^d}`. Georgii's specific entropy
`𝓀(μ) = lim |Λ|⁻¹ 𝓗_Λ(μ)` (`MeasureTheory.GibbsMeasure.specificEntropy`,
`GibbsMeasure/Specification/SpecificEntropy.lean`) and the entropy rate
`h = inf_W ∫ g_W dμ` of the stationary finite-state random field `i ↦ σ_i`
(`MeasureTheory.entropyRate`, `GibbsMeasure/Mathlib/Dynamics/Ergodic/ShannonMcMillanBreiman.lean`)
are two names for the same number, up to the normalisation constant `log |E|` that Georgii's
counting-measure convention hides.

## Main results

* `MeasureTheory.GibbsMeasure.specificEntropy_uniformOn_eq_entropyRate_sub_log_card`, **the
  bridge**: for `μ ∈ 𝓟_Θ`,
  `𝓀(μ) = h − log |E|`, `h = entropyRate (Lex (ℤ^d)) μ (σ ↦ σ_0)`,
  the entropy rate relative to the lexicographic order of `ℤ^d`. No ergodicity is needed. Both
  sides are limits along the cubes `Λ_n = [−n, 0]^d`: on the left by Georgii's Theorem (15.12)
  (`tendsto_entropyIn_div_card`), on the right by
  `MeasureTheory.tendsto_inv_card_mul_integral_neg_log_blockProb`, the chain-rule computation of
  the block entropy density. The finite-volume identity that matches the two is Shannon's formula
  `entropyIn_uniformOn_eq_neg_integral_log_measureReal` together with
  `blockMap_preimage_singleton_eq_restrict_preimage`, which identifies the block
  `(σ_{−i})_{i ∈ Λ}` of the stationary random field with the restriction `σ_{−Λ}`.
* `tendsto_integral_abs_neg_inv_card_mul_log_measureReal_sub_entropyRate` (in
  `MeasureTheory.GibbsMeasure`), the **Shannon–McMillan theorem** in the vocabulary of this
  library: for an *ergodic* `μ ∈ 𝓟_Θ` and cubes `Λ_n = [a_n, a_n + p_n]` with `p_n → ∞`,
  `∫ | −|Λ_n|⁻¹ log μ(σ_{Λ_n} = σ_{Λ_n}(ω)) − (𝓀(μ) + log |E|) | dμ(ω) → 0`.
* `MeasureTheory.GibbsMeasure.tendsto_integral_abs_inv_card_mul_log_density_add_specificEntropy`,
  **the theorem of McMillan as Georgii uses it** in the proof of the large deviation lower bound
  (15.47): with `f_Λ = dμ|𝓕_Λ / dλ^Λ = |E|^{|Λ|} μ(σ_Λ = σ_Λ(·))` the density of `μ` on `𝓕_Λ`
  with respect to the a priori product measure,
  `μ(| |Λ_n|⁻¹ log f_{Λ_n} + 𝓀(μ)|) → 0`.

Georgii cites Krengel, *Ergodic Theorems*, Theorem 9.2.4 for the last statement.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Real Topology
open scoped ENNReal NNReal Pointwise Topology symmDiff

namespace MeasureTheory.GibbsMeasure

attribute [local instance] shiftAddAction measurableConstVAdd_shift

/-! ### Blocks of the stationary random field are finite-volume cylinders -/

section Block

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E] {μ : Measure (S → E)}

/-- Under the shift action `j +ᵥ ω = θ_j ω`, the spin at the origin of `i +ᵥ ω` is the spin of
`ω` at `−i`. -/
lemma spin_zero_vadd (i : S) (ω : S → E) : (i +ᵥ ω) 0 = ω (-i) := by
  rw [shift_vadd, shift_toFun_apply, zero_sub]

/-- **The block of the stationary random field `i ↦ σ_i` on a finite set of sites `Λ` is the
restriction of the configuration to the reflected volume `−Λ`.** Consequently the block
probabilities of the field `ω ↦ ω 0` are the measures of the finite-volume cylinders of `μ`. -/
lemma blockMap_preimage_singleton_eq_restrict_preimage {Λ Δ : Finset S}
    (hΔ : ∀ i : S, i ∈ Δ ↔ -i ∈ Λ) (ω : S → E) :
    blockMap (fun ω : S → E ↦ ω 0) Λ ⁻¹' {blockMap (fun ω : S → E ↦ ω 0) Λ ω}
      = (Δ.restrict ⁻¹' {Δ.restrict ω} : Set (S → E)) := by
  ext η
  rw [mem_blockMap_preimage_singleton]
  simp only [spin_zero_vadd, Set.mem_preimage, Set.mem_singleton_iff, funext_iff,
    Subtype.forall, Finset.restrict]
  constructor
  · intro h j hj
    have h' := h (-j) ((hΔ j).1 hj)
    rwa [neg_neg] at h'
  · intro h i hi
    exact h (-i) ((hΔ (-i)).2 (by rwa [neg_neg]))

variable (μ) in
/-- The block probability of the stationary field `i ↦ σ_i` on `Λ` is the `μ`-measure of the
cylinder that fixes the configuration on the reflected volume `−Λ`. -/
lemma blockProb_eq_measureReal_restrict_preimage {Λ Δ : Finset S}
    (hΔ : ∀ i : S, i ∈ Δ ↔ -i ∈ Λ) (ω : S → E) :
    blockProb μ (fun ω : S → E ↦ ω 0) Λ ω
      = μ.real (Δ.restrict ⁻¹' {Δ.restrict ω} : Set (S → E)) := by
  rw [blockProb, blockMap_preimage_singleton_eq_restrict_preimage hΔ]

end Block

/-! ### The cubes used for both limits -/

section Cubes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `−[0, n+1)^d = [−n, 0]^d`: the reflection of the cube along which the Følner property is
available is the box along which the entropy density converges. -/
lemma mem_Icc_iff_neg_mem_piFinset_Ico (n : ℕ) (i : ι → ℤ) :
    i ∈ Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)
      ↔ -i ∈ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ) := by
  simp only [Finset.mem_Icc, Fintype.mem_piFinset, Finset.mem_Ico, Pi.le_def, Pi.neg_apply,
    Pi.zero_apply, Nat.cast_add, Nat.cast_one]
  constructor
  · rintro ⟨h1, h2⟩ k
    have := h1 k
    have := h2 k
    omega
  · intro h
    exact ⟨fun k ↦ by have := h k; omega, fun k ↦ by have := h k; omega⟩

/-- The cube `[0, n+1)^d` and the box `[−n, 0]^d` have the same cardinality. -/
lemma card_piFinset_Ico_eq_card_Icc (n : ℕ) :
    #(Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ))
      = #(Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)) :=
  Finset.card_bij' (fun a _ ↦ -a) (fun a _ ↦ -a)
    (fun a ha ↦ (mem_Icc_iff_neg_mem_piFinset_Ico n (-a)).2 (by rwa [neg_neg]))
    (fun a ha ↦ (mem_Icc_iff_neg_mem_piFinset_Ico n a).1 ha)
    (fun a _ ↦ neg_neg a) (fun a _ ↦ neg_neg a)

end Cubes

/-! ### The bridge between the specific entropy and the entropy rate -/

section Bridge

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι] [MeasurableSpace E] [Fintype E]
  [Nonempty E] [MeasurableSingletonClass E] {μ : Measure ((ι → ℤ) → E)}

/-- **The specific entropy is the entropy rate, up to the normalisation `log |E|`.** For a finite
state space `E`, the uniform a priori measure `λ = |E|⁻¹ ∑_x δ_x` and a shift-invariant random
field `μ ∈ 𝓟_Θ` on `E^{ℤ^d}`,
`𝓀(μ) = h − log |E|`,
where `h = entropyRate (Lex (ℤ^d)) μ (σ ↦ σ_0)` is the mean conditional information of the spin at
the origin given the lexicographic past. Georgii normalises by counting measure, for which the
constant `log |E| = −log λ(E)` is absent, so that `𝓀(μ)` *is* the entropy rate.

Both sides are limits along the cubes `Λ_n = [−n, 0]^d`: the left-hand side by Theorem (15.12),
the right-hand side by the chain rule for block probabilities. No ergodicity is required. -/
theorem specificEntropy_uniformOn_eq_entropyRate_sub_log_card
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy (uniformOn Set.univ) μ
      = ((entropyRate (Lex (ι → ℤ)) μ (fun ω : (ι → ℤ) → E ↦ ω 0)
          - log (Fintype.card E) : ℝ) : EReal) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  have hvadd := vaddInvariantMeasure_of_forall_measurePreserving_shift hpres
  have hXm : Measurable (fun ω : (ι → ℤ) → E ↦ ω 0) := measurable_pi_apply 0
  have hcardQ := card_piFinset_Ico_eq_card_Icc (ι := ι)
  -- Georgii Theorem (15.12) along the boxes `[-n, 0]^d`
  have hleft : Tendsto (fun n : ℕ ↦
      entropyIn (uniformOn (Set.univ : Set E))
          (Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ) : Set (ι → ℤ)) μ
        / (#(Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)) : EReal))
      atTop (𝓝 (specificEntropy (uniformOn Set.univ) μ)) :=
    tendsto_entropyIn_div_card (m := fun n : ℕ ↦ fun _ : ι ↦ -(n : ℤ))
      (n := fun _ : ℕ ↦ (0 : ι → ℤ)) _ hμ fun k ↦ by
        simpa using tendsto_natCast_atTop_atTop (R := ℤ)
  -- the block-entropy density along the cubes `[0, n+1)^d`
  have hright : Tendsto (fun n : ℕ ↦
      -((#(Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ)) : ℝ)⁻¹
        * ∫ ω, log (blockProb μ (fun ω : (ι → ℤ) → E ↦ ω 0)
            (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ)) ω) ∂μ))
      atTop (𝓝 (entropyRate (Lex (ι → ℤ)) μ (fun ω : (ι → ℤ) → E ↦ ω 0))) := by
    refine tendsto_inv_card_mul_integral_neg_log_blockProb (G := Lex (ι → ℤ))
      (F := fun n : ℕ ↦ (Fintype.piFinset fun _ : ι ↦
        Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ) : Finset (ι → ℤ)))
      (fun ω : (ι → ℤ) → E ↦ ω 0) hXm ?_ fun g ↦ ?_
    · filter_upwards with n
      refine ⟨0, Fintype.mem_piFinset.2 fun i ↦ ?_⟩
      simp only [Finset.mem_Ico]
      exact ⟨le_rfl, by positivity⟩
    · have hzero : ∀ s : Finset (ι → ℤ), (0 : ι → ℤ) +ᵥ s = s := fun s ↦ by
        ext i
        simp
      have h := tendsto_card_vadd_cube_symmDiff_div_card (fun _ : ℕ ↦ (0 : ι → ℤ))
        (r := fun n : ℕ ↦ n + 1) (tendsto_add_atTop_nat 1) (ofLex g)
      simp only [hzero] at h
      exact h
  -- the finite-volume identity matching the two
  have hstep : ∀ n : ℕ,
      entropyIn (uniformOn (Set.univ : Set E))
          (Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ) : Set (ι → ℤ)) μ
        / (#(Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)) : EReal)
      = ((-((#(Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ)) : ℝ)⁻¹
            * ∫ ω, log (blockProb μ (fun ω : (ι → ℤ) → E ↦ ω 0)
                (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ)) ω) ∂μ)
          - log (Fintype.card E) : ℝ) : EReal) := by
    intro n
    have hpos : (0 : ℝ) < #(Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)) := by
      have hne : (Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)).Nonempty :=
        ⟨0, Finset.mem_Icc.2 ⟨fun k ↦ by simp, le_rfl⟩⟩
      exact_mod_cast Finset.card_pos.2 hne
    have hint : ∫ ω, log (μ.real
          ((Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)).restrict ⁻¹'
            {(Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)).restrict ω}
              : Set ((ι → ℤ) → E))) ∂μ
        = ∫ ω, log (blockProb μ (fun ω : (ι → ℤ) → E ↦ ω 0)
            (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ)) ω) ∂μ := by
      refine integral_congr_ae (.of_forall fun ω ↦ ?_)
      simp only [blockProb_eq_measureReal_restrict_preimage μ
        (mem_Icc_iff_neg_mem_piFinset_Ico n)]
    have hc : (#(Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)) : ℝ) ≠ 0 := hpos.ne'
    rw [entropyIn_uniformOn_eq_neg_integral_log_measureReal, hint, hcardQ n,
      show ((#(Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)) : EReal))
        = ((#(Finset.Icc (fun _ : ι ↦ -(n : ℤ)) (0 : ι → ℤ)) : ℝ) : EReal)
          from by norm_cast, ← EReal.coe_div]
    congr 1
    field_simp
  simp only [hstep] at hleft
  exact tendsto_nhds_unique hleft
    ((continuous_coe_real_ereal.tendsto _).comp (hright.sub_const _))

end Bridge


/-! ### Reflected boxes -/

section Reflection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The translate by `x` of the cube `[0, r+1)^d` is the box `[x, x + r]`. -/
lemma vadd_piFinset_Ico_eq_Icc (x : ι → ℤ) (r : ℕ) :
    x +ᵥ (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((r + 1 : ℕ) : ℤ))
      = Finset.Icc x (fun k ↦ x k + r) := by
  ext i
  simp only [Finset.mem_vadd_finset, Fintype.mem_piFinset, Finset.mem_Ico, Finset.mem_Icc,
    Pi.le_def, vadd_eq_add, Nat.cast_add, Nat.cast_one]
  have hxy : ∀ y : ι → ℤ, ∀ k, (x + y) k = x k + y k := fun _ _ ↦ rfl
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun k ↦ by have := hy k; rw [hxy y k]; omega,
      fun k ↦ by have := hy k; rw [hxy y k]; omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨i - x, fun k ↦ ?_, by ext k; simp⟩
    have hk1 := h1 k
    have hk2 := h2 k
    simp only [Pi.sub_apply]
    omega

end Reflection

/-! ### The theorem of McMillan -/

section McMillan

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι] [MeasurableSpace E]
  [MeasurableSingletonClass E] {μ : Measure ((ι → ℤ) → E)}

/-- The specific entropy of a shift-invariant random field over a finite state space is the real
number `h − log |E|`, `h` its entropy rate. -/
lemma toReal_specificEntropy_uniformOn [Fintype E] [Nonempty E]
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    (specificEntropy (uniformOn Set.univ) μ).toReal
      = entropyRate (Lex (ι → ℤ)) μ (fun ω : (ι → ℤ) → E ↦ ω 0) - log (Fintype.card E) := by
  rw [specificEntropy_uniformOn_eq_entropyRate_sub_log_card hμ, EReal.toReal_coe]

/-- **The Shannon–McMillan theorem for an ergodic shift-invariant random field over a finite
state space.** Along any sequence of cubes `Λ_n = [a_n, a_n + p_n]` whose side lengths tend to
infinity,
`∫ | −|Λ_n|⁻¹ log μ(σ_{Λ_n} = σ_{Λ_n}(ω)) − h | dμ(ω) → 0`,
where `h = entropyRate (Lex (ℤ^d)) μ (σ ↦ σ_0)` is the entropy rate; by
`specificEntropy_uniformOn_eq_entropyRate_sub_log_card`, `h = 𝓀(μ) + log |E|`. Ergodicity is
triviality of `μ` on the invariant σ-algebra `𝓘` of the shift group, Georgii (14.5). -/
theorem tendsto_integral_abs_neg_inv_card_mul_log_measureReal_sub_entropyRate [Finite E]
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (herg : ∀ A, MeasurableSet[invariantEvents (shiftGroup (ι → ℤ) E)] A → μ A = 0 ∨ μ A = 1)
    (a : ℕ → ι → ℤ) {p : ℕ → ℕ} (hp : Tendsto p atTop atTop) :
    Tendsto (fun n ↦ ∫ ω,
      |(-((#(Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ)) : ℝ)⁻¹
            * log (μ.real ((Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ)).restrict ⁻¹'
                {(Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ)).restrict ω}
                  : Set ((ι → ℤ) → E)))))
        - entropyRate (Lex (ι → ℤ)) μ (fun ω : (ι → ℤ) → E ↦ ω 0)| ∂μ) atTop (𝓝 0) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  have hvadd := vaddInvariantMeasure_of_forall_measurePreserving_shift hpres
  have hXm : Measurable (fun ω : (ι → ℤ) → E ↦ ω 0) := measurable_pi_apply 0
  have herg' : ∀ A, MeasurableSet[MeasurableSpace.smulInvariants (Multiplicative (ι → ℤ))
      ((ι → ℤ) → E)] A → μ A = 0 ∨ μ A = 1 := by
    rw [smulInvariants_multiplicative_eq_invariantEvents_shiftGroup]
    exact herg
  -- the reflected cubes, in which the block probabilities live
  have hmem : ∀ (n : ℕ) (i : ι → ℤ),
      i ∈ Finset.Icc (a n) (fun k ↦ a n k + (p n : ℤ))
        ↔ -i ∈ Finset.Icc (fun k ↦ -(a n k) - (p n : ℤ))
              (fun k ↦ (fun k ↦ -(a n k) - (p n : ℤ)) k + (p n : ℤ)) := by
    intro n i
    simp only [Finset.mem_Icc, Pi.le_def, Pi.neg_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun k ↦ by have := h2 k; omega, fun k ↦ by have := h1 k; omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun k ↦ by have := h2 k; omega, fun k ↦ by have := h1 k; omega⟩
  have hcard : ∀ n : ℕ,
      #(Finset.Icc (fun k ↦ -(a n k) - (p n : ℤ))
          (fun k ↦ (fun k ↦ -(a n k) - (p n : ℤ)) k + (p n : ℤ)))
        = #(Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ)) := fun n ↦
    Finset.card_bij' (fun c _ ↦ -c) (fun c _ ↦ -c)
      (fun c hc ↦ (hmem n (-c)).2 (by rwa [neg_neg]))
      (fun c hc ↦ (hmem n c).1 hc) (fun c _ ↦ neg_neg c) (fun c _ ↦ neg_neg c)
  have h := tendsto_integral_abs_neg_inv_card_mul_log_blockProb_sub_entropyRate_cube
    (μ := μ) (fun ω : (ι → ℤ) → E ↦ ω 0) hXm herg'
    (fun n ↦ fun k ↦ -(a n k) - (p n : ℤ)) (r := fun n ↦ p n + 1)
    (tendsto_atTop_mono (fun n ↦ Nat.le_succ (p n)) hp)
  simp only [vadd_piFinset_Ico_eq_Icc] at h
  refine h.congr fun n ↦ integral_congr_ae (.of_forall fun ω ↦ ?_)
  rw [blockProb_eq_measureReal_restrict_preimage μ (hmem n), hcard n]

/-- **The theorem of McMillan in Georgii's form**, the input to the large deviation lower bound
(15.47). Let `f_Λ = dμ|𝓕_Λ / dλ^Λ = |E|^{|Λ|} μ(σ_Λ = σ_Λ(·))` be the density of `μ` on the
finite-volume σ-algebra `𝓕_Λ` with respect to the uniform a priori product measure. Then for an
ergodic `μ ∈ 𝓟_Θ` and cubes `Λ_n` whose side lengths tend to infinity,
`μ(| |Λ_n|⁻¹ log f_{Λ_n} + 𝓀(μ) |) → 0`. -/
theorem tendsto_integral_abs_inv_card_mul_log_density_add_specificEntropy
    [Fintype E] [Nonempty E] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (herg : ∀ A, MeasurableSet[invariantEvents (shiftGroup (ι → ℤ) E)] A → μ A = 0 ∨ μ A = 1)
    (a : ℕ → ι → ℤ) {p : ℕ → ℕ} (hp : Tendsto p atTop atTop) :
    Tendsto (fun n ↦ ∫ ω,
      |(#(Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ)) : ℝ)⁻¹
          * log ((Fintype.card E : ℝ) ^ #(Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ))
            * μ.real ((Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ)).restrict ⁻¹'
                {(Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ)).restrict ω}
                  : Set ((ι → ℤ) → E)))
        + (specificEntropy (uniformOn Set.univ) μ).toReal| ∂μ) atTop (𝓝 0) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  have hvadd := vaddInvariantMeasure_of_forall_measurePreserving_shift hpres
  have hXm : Measurable (fun ω : (ι → ℤ) → E ↦ ω 0) := measurable_pi_apply 0
  have hmem : ∀ (n : ℕ) (i : ι → ℤ),
      i ∈ Finset.Icc (a n) (fun k ↦ a n k + (p n : ℤ))
        ↔ -i ∈ Finset.Icc (fun k ↦ -(a n k) - (p n : ℤ))
              (fun k ↦ (fun k ↦ -(a n k) - (p n : ℤ)) k + (p n : ℤ)) := by
    intro n i
    simp only [Finset.mem_Icc, Pi.le_def, Pi.neg_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun k ↦ by have := h2 k; omega, fun k ↦ by have := h1 k; omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun k ↦ by have := h2 k; omega, fun k ↦ by have := h1 k; omega⟩
  have hcE : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  refine (tendsto_integral_abs_neg_inv_card_mul_log_measureReal_sub_entropyRate
    hμ herg a hp).congr fun n ↦ ?_
  have hne : (#(Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ)) : ℝ) ≠ 0 := by
    have hnn : (Finset.Icc (a n) fun k ↦ a n k + (p n : ℤ)).Nonempty :=
      ⟨a n, Finset.mem_Icc.2 ⟨le_rfl, fun k ↦ by simp⟩⟩
    exact_mod_cast (Finset.card_pos.2 hnn).ne'
  refine integral_congr_ae ?_
  filter_upwards [ae_blockProb_pos (μ := μ) (fun ω : (ι → ℤ) → E ↦ ω 0)
    (Finset.Icc (fun k ↦ -(a n k) - (p n : ℤ))
      (fun k ↦ (fun k ↦ -(a n k) - (p n : ℤ)) k + (p n : ℤ)))] with ω hω
  rw [blockProb_eq_measureReal_restrict_preimage μ (hmem n)] at hω
  rw [toReal_specificEntropy_uniformOn hμ, log_mul (by positivity) hω.ne', log_pow]
  refine abs_eq_abs.2 (Or.inr ?_)
  field_simp
  ring

end McMillan

end MeasureTheory.GibbsMeasure
