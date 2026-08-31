/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.InvariantExistence
public import GibbsMeasure.Model.Ising

/-!
# Shift-invariant Gibbs measures on `ℤ^d` from averaged Gibbs distributions

Georgii Example (5.20)(1) and (5.17)(1): cluster points of the cube-averaged finite-volume Gibbs
distributions `|Λ_N|⁻¹ ∑_{i ∈ Λ_N} γ_{Λ_N + i}(· | ω)` with a constant boundary condition are
shift-invariant Gibbs measures; for finite `E` they exist, in particular for the Ising model.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology symmDiff

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] {d : ℕ}

/-- Georgii (5.20)(1): the cube `Λ_N = ℤ^d ∩ [-N, N]^d`. -/
def cube (d N : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ ↦ Finset.Icc (-(N : ℤ)) N

lemma mem_cube {N : ℕ} {i : Fin d → ℤ} : i ∈ cube d N ↔ ∀ k, (i k).natAbs ≤ N := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  exact forall_congr' fun k ↦ by omega

lemma card_cube (d N : ℕ) : (cube d N).card = (2 * N + 1) ^ d := by
  rw [cube, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc]
  congr 1
  omega

lemma cube_nonempty (d N : ℕ) : (cube d N).Nonempty :=
  Fintype.piFinset_nonempty.2 fun _ ↦ Finset.nonempty_Icc.2 (by omega)

lemma cube_mono : Monotone (cube d) := fun _ _ h _ hi ↦
  mem_cube.2 fun k ↦ (mem_cube.1 hi k).trans h

/-- The cubes `Λ_N` exhaust `ℤ^d`: `Λ_N ↑ S`. -/
lemma tendsto_cube_atTop : Tendsto (cube d) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun Λ ↦
    ⟨Λ.sup fun i ↦ Finset.univ.sup fun k ↦ (i k).natAbs, fun N hN i hi ↦ mem_cube.2 fun k ↦ ?_⟩
  exact ((Finset.le_sup (f := fun k ↦ (i k).natAbs) (Finset.mem_univ k)).trans
    (Finset.le_sup (f := fun i ↦ Finset.univ.sup fun k ↦ (i k).natAbs) hi)).trans hN

/-- Membership in the translate `Λ + j = {i + j : i ∈ Λ}` of a finite volume of `ℤ^d`. -/
lemma mem_map_addRight_iff {Λ : Finset (Fin d → ℤ)} {j x : Fin d → ℤ} :
    x ∈ Λ.map (Equiv.addRight j).toEmbedding ↔ x - j ∈ Λ := by
  simp [Finset.mem_map_equiv, sub_eq_add_neg]

/-- Georgii (5.20)(1): `|(Λ_N + j) ∆ Λ_N| + 2 |Λ_{N - m}| ≤ 2 |Λ_N|` for `m = ‖j‖₁ ≤ N`, since
`Λ_{N - m} + j ⊆ Λ_N ∩ (Λ_N + j)`. -/
lemma card_symmDiff_map_addRight_cube_le (j : Fin d → ℤ) {N : ℕ} (hN : ∑ k, (j k).natAbs ≤ N) :
    ((cube d N).map (Equiv.addRight j).toEmbedding ∆ cube d N).card +
      2 * (cube d (N - ∑ k, (j k).natAbs)).card ≤ 2 * (cube d N).card := by
  set m := ∑ k, (j k).natAbs with hm
  set C := cube d N with hC
  set D := (cube d (N - m)).map (Equiv.addRight j).toEmbedding with hD
  have hDC : D ⊆ C := fun x hx ↦ by
    rw [hD, mem_map_addRight_iff, mem_cube] at hx
    refine mem_cube.2 fun k ↦ ?_
    have hjk : (j k).natAbs ≤ m :=
      Finset.single_le_sum (fun k _ ↦ Nat.zero_le ((j k).natAbs)) (Finset.mem_univ k)
    have hxk := hx k
    simp only [Pi.sub_apply] at hxk
    omega
  have hDCj : D ⊆ C.map (Equiv.addRight j).toEmbedding :=
    Finset.map_subset_map.2 (cube_mono (Nat.sub_le N m))
  have h1 : (C.map (Equiv.addRight j).toEmbedding \ C).card ≤ C.card - D.card :=
    calc (C.map (Equiv.addRight j).toEmbedding \ C).card
        ≤ (C.map (Equiv.addRight j).toEmbedding \ D).card :=
          Finset.card_le_card (Finset.sdiff_subset_sdiff (subset_refl _) hDC)
      _ = C.card - D.card := by rw [Finset.card_sdiff_of_subset hDCj, Finset.card_map]
  have h2 : (C \ C.map (Equiv.addRight j).toEmbedding).card ≤ C.card - D.card :=
    calc (C \ C.map (Equiv.addRight j).toEmbedding).card ≤ (C \ D).card :=
          Finset.card_le_card (Finset.sdiff_subset_sdiff (subset_refl _) hDCj)
      _ = C.card - D.card := Finset.card_sdiff_of_subset hDC
  have hDcard : D.card = (cube d (N - m)).card := Finset.card_map _
  have hDle : D.card ≤ C.card := Finset.card_le_card hDC
  have h3 := Finset.card_union_le (C.map (Equiv.addRight j).toEmbedding \ C)
    (C \ C.map (Equiv.addRight j).toEmbedding)
  rw [← Finset.symmDiff_def] at h3
  omega

/-- Georgii (5.20)(1): `|Λ_{N - r(N)}| / |Λ_N| → 1` whenever `r(N) / N → 0`. -/
lemma tendsto_card_cube_sub_div {r : ℕ → ℕ} (hr : Tendsto (fun N ↦ (r N : ℝ) / N) atTop (𝓝 0))
    (hr' : ∀ᶠ N in atTop, r N ≤ N) :
    Tendsto (fun N ↦ ((cube d (N - r N)).card : ℝ) / (cube d N).card) atTop (𝓝 1) := by
  have h0 : Tendsto (fun N : ℕ ↦ (2 * r N : ℝ) / (2 * N + 1)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr
      (Eventually.of_forall fun N ↦ by positivity) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_div_iff₀ (by positivity) hN']
    nlinarith [(r N).cast_nonneg (α := ℝ)]
  have h1 : Tendsto (fun N : ℕ ↦ (1 - (2 * r N : ℝ) / (2 * N + 1)) ^ d) atTop (𝓝 1) := by
    simpa using (h0.const_sub 1).pow d
  refine h1.congr' ?_
  filter_upwards [hr'] with N hN
  rw [card_cube, card_cube, Nat.cast_pow, Nat.cast_pow, ← div_pow]
  congr 1
  have h2 : (2 * N + 1 : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub hN]
  field_simp
  ring

/-- Georgii (5.20)(1): the translation ratio `|(Λ_N + j) ∆ Λ_N| / |Λ_N| → 0` as `N → ∞`. -/
lemma tendsto_card_symmDiff_map_addRight_cube_div (j : Fin d → ℤ) :
    Tendsto (fun N ↦ (((cube d N).map (Equiv.addRight j).toEmbedding ∆ cube d N).card : ℝ) /
      (cube d N).card) atTop (𝓝 0) := by
  set m := ∑ k, (j k).natAbs with hm
  have hq : Tendsto (fun N ↦ ((cube d (N - m)).card : ℝ) / (cube d N).card) atTop (𝓝 1) :=
    tendsto_card_cube_sub_div (r := fun _ ↦ m)
      (by simpa using tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)) (eventually_ge_atTop m)
  have h2 : Tendsto (fun N ↦ 2 * (1 - ((cube d (N - m)).card : ℝ) / (cube d N).card)) atTop
      (𝓝 0) := by
    simpa using (hq.const_sub 1).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall fun N ↦ by positivity) ?_
  filter_upwards [eventually_ge_atTop m] with N hN
  have hC : (0 : ℝ) < (cube d N).card := by exact_mod_cast (cube_nonempty d N).card_pos
  have hle : ((((cube d N).map (Equiv.addRight j).toEmbedding ∆ cube d N).card : ℕ) : ℝ) +
      2 * (cube d (N - m)).card ≤ 2 * (cube d N).card := by
    exact_mod_cast card_symmDiff_map_addRight_cube_le j hN
  rw [div_le_iff₀ hC]
  have h3 : 2 * (1 - ((cube d (N - m)).card : ℝ) / (cube d N).card) * (cube d N).card =
      2 * (cube d N).card - 2 * (cube d (N - m)).card := by
    field_simp
  linarith

/-- `Nat.sqrt` tends to infinity. -/
lemma tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  Filter.tendsto_atTop_atTop.2 fun b ↦ ⟨b * b, fun n hn ↦ by
    simpa [Nat.sqrt_eq] using Nat.sqrt_le_sqrt hn⟩

/-- `√N / N → 0`, for the choice `k(N) = N - √N` in Georgii (5.20)(1). -/
lemma tendsto_nat_sqrt_div_self : Tendsto (fun N : ℕ ↦ (Nat.sqrt N : ℝ) / N) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ ↦ ((Nat.sqrt N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_nat_sqrt_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun N ↦ by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hs : 1 ≤ Nat.sqrt N := Nat.le_sqrt.2 (by simpa using hN)
  have hs' : (0 : ℝ) < Nat.sqrt N := by exact_mod_cast hs
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hN', inv_mul_eq_div, le_div_iff₀ hs']
  exact_mod_cast Nat.sqrt_le N

/-- `N - √N → ∞`, for the choice `k(N) = N - √N` in Georgii (5.20)(1). -/
lemma tendsto_sub_nat_sqrt_atTop : Tendsto (fun N ↦ N - Nat.sqrt N) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b ↦ ⟨(b + 2) ^ 2, fun N hN ↦ ?_⟩
  have hs : b + 2 ≤ Nat.sqrt N := by
    have h := Nat.sqrt_le_sqrt hN
    rwa [Nat.sqrt_eq'] at h
  have h1 : Nat.sqrt N * (b + 2) ≤ Nat.sqrt N * Nat.sqrt N :=
    Nat.mul_le_mul_left _ hs
  have h2 : Nat.sqrt N * Nat.sqrt N ≤ N := by
    have h := Nat.sqrt_le' N
    rwa [pow_two] at h
  have hb : b ≤ Nat.sqrt N * b := Nat.le_mul_of_pos_left b (by omega)
  have h3 : Nat.sqrt N + b ≤ Nat.sqrt N * (b + 2) := by rw [Nat.mul_add]; omega
  omega


/-- Georgii (5.20)(1): the translates `{Λ_N + i : i ∈ Λ_k}` of the cube `Λ_N`. -/
def cubeTranslates (d N k : ℕ) : Finset (Finset (Fin d → ℤ)) :=
  (cube d k).image fun i ↦ (cube d N).map (Equiv.addRight i).toEmbedding

/-- Distinct translates of a cube are distinct. -/
lemma map_addRight_cube_injective (N : ℕ) :
    Function.Injective fun i : Fin d → ℤ ↦ (cube d N).map (Equiv.addRight i).toEmbedding := by
  have key : ∀ a b : Fin d → ℤ, (cube d N).map (Equiv.addRight a).toEmbedding =
      (cube d N).map (Equiv.addRight b).toEmbedding → ∀ k, b k ≤ a k := by
    intro a b hab k
    have hmem : (fun _ ↦ -(N : ℤ)) + a ∈ (cube d N).map (Equiv.addRight a).toEmbedding := by
      rw [mem_map_addRight_iff, add_sub_cancel_right]
      exact mem_cube.2 fun k ↦ by simp
    rw [hab, mem_map_addRight_iff, mem_cube] at hmem
    have := hmem k
    simp only [Pi.add_apply, Pi.sub_apply] at this
    omega
  intro i i' h
  funext k
  exact le_antisymm (key i' i h.symm k) (key i i' h k)

lemma card_cubeTranslates (d N k : ℕ) : (cubeTranslates d N k).card = (cube d k).card :=
  Finset.card_image_of_injective _ (map_addRight_cube_injective N)

lemma cubeTranslates_nonempty (d N k : ℕ) : (cubeTranslates d N k).Nonempty :=
  (cube_nonempty d k).image _

lemma cubeTranslates_mono (d N : ℕ) {k k' : ℕ} (h : k ≤ k') :
    cubeTranslates d N k ⊆ cubeTranslates d N k' :=
  Finset.image_subset_image (cube_mono h)

/-- `Λ_{N - k} ⊆ Λ_N + i` for every `i ∈ Λ_k` (`k ≤ N`): the intersection of the translates
contains `Λ_{N - k}` (Georgii (5.20)(1)). -/
lemma cube_sub_subset_of_mem_cubeTranslates {N k : ℕ} (hk : k ≤ N) {Λ : Finset (Fin d → ℤ)}
    (hΛ : Λ ∈ cubeTranslates d N k) : cube d (N - k) ⊆ Λ := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hΛ
  intro x hx
  rw [mem_map_addRight_iff]
  rw [mem_cube] at hx hi ⊢
  intro l
  have h1 := hx l
  have h2 := hi l
  simp only [Pi.sub_apply]
  omega

/-- The shift `θ_j` maps the family of translates by `Λ_k` to the translates by `Λ_k + j`
(Georgii (5.20)(1): `{τ_* Λ : Λ ∈ R_N} = {Λ_N + i : i ∈ Λ_N + j}`). -/
lemma map_cubeTranslates_shift (j : Fin d → ℤ) (N k : ℕ) :
    (cubeTranslates d N k).map
        (Finset.mapEmbedding (shift E j).sites.toEmbedding).toEmbedding =
      ((cube d k).map (Equiv.addRight j).toEmbedding).image
        fun i ↦ (cube d N).map (Equiv.addRight i).toEmbedding := by
  rw [Finset.map_eq_image, cubeTranslates, Finset.image_image, Finset.map_eq_image,
    Finset.image_image]
  refine Finset.image_congr fun i _ ↦ ?_
  simp only [Function.comp_apply, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply,
    Equiv.coe_toEmbedding, Equiv.coe_addRight]
  rw [Finset.map_map]
  congr 1
  ext x
  simp [shift, add_assoc]

/-- Georgii (5.20)(1): `|{θ_{j*} Λ : Λ ∈ R_N} ∆ R_N| = |(Λ_k + j) ∆ Λ_k|`. -/
lemma card_symmDiff_map_cubeTranslates_shift (j : Fin d → ℤ) (N k : ℕ) :
    ((cubeTranslates d N k).map
        (Finset.mapEmbedding (shift E j).sites.toEmbedding).toEmbedding ∆
      cubeTranslates d N k).card =
      ((cube d k).map (Equiv.addRight j).toEmbedding ∆ cube d k).card := by
  rw [map_cubeTranslates_shift, cubeTranslates,
    ← Finset.image_symmDiff _ _ (map_addRight_cube_injective N),
    Finset.card_image_of_injective _ (map_addRight_cube_injective N)]

/-! ### Georgii Example (5.20)(1): configurational boundary conditions on `ℤ^d` -/

variable {γ : Specification (Fin d → ℤ) E} {ν : Measure ((Fin d → ℤ) → E)}

/-- **Georgii (5.20)(1), invariance part.** For shift-invariant `γ` and `ν` on `ℤ^d`, every cluster
point of `μ_N = |Λ_N|⁻¹ ∑_{i ∈ Λ_N} ν γ_{Λ_N + i}` is shift-invariant, by Proposition (5.18). -/
theorem measurePreserving_shift_of_mapClusterPt_average_cubeTranslates [IsProbabilityMeasure ν]
    (hγ : ∀ j, Specification.IsInvariant (shift E j) γ)
    (hν : ∀ j, MeasurePreserving (shift E j).toFun ν ν)
    {μs : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμs : ∀ N, (μs N : Measure ((Fin d → ℤ) → E)) = γ.average ν (cubeTranslates d N N))
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμ : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence (Fin d → ℤ) E)
      atTop fun N ↦ WithSetwiseTopology.ofMeasure (μs N)) (j : Fin d → ℤ) :
    MeasurePreserving (shift E j).toFun μ μ := by
  refine measurePreserving_of_mapClusterPt_average (hγ j) (hν j)
    (fun N ↦ cubeTranslates_nonempty d N N) ?_ hμs hμ
  simp only [card_symmDiff_map_cubeTranslates_shift, card_cubeTranslates]
  exact tendsto_card_symmDiff_map_addRight_cube_div j

/-- **Georgii (5.20)(1), Gibbs part.** For quasilocal `γ` on `ℤ^d`, every cluster point of
`μ_N = |Λ_N|⁻¹ ∑_{i ∈ Λ_N} ν γ_{Λ_N + i}` is Gibbs (modified sequence `k(N) = N - √N`, (4.18)). -/
theorem mem_GP_of_mapClusterPt_average_cubeTranslates [IsProbabilityMeasure ν]
    (hγq : γ.IsQuasilocal)
    {μs : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμs : ∀ N, (μs N : Measure ((Fin d → ℤ) → E)) = γ.average ν (cubeTranslates d N N))
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμ : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence (Fin d → ℤ) E)
      atTop fun N ↦ WithSetwiseTopology.ofMeasure (μs N)) :
    μ ∈ GP (S := Fin d → ℤ) (E := E) γ := by
  -- the modified sequence `μ'_N`, averaging over `i ∈ Λ_{k(N)}` with `k(N) = N - √N`
  set μs' : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E) := fun N ↦
    ⟨γ.average ν (cubeTranslates d N (N - Nat.sqrt N)),
      γ.isProbabilityMeasure_average ν (cubeTranslates_nonempty d N (N - Nat.sqrt N))⟩ with hμs'
  -- `|Λ_{k(N)}| / |Λ_N| → 1`
  have hq : Tendsto (fun N ↦ ((cube d (N - Nat.sqrt N)).card : ℝ) / (cube d N).card) atTop
      (𝓝 1) :=
    tendsto_card_cube_sub_div tendsto_nat_sqrt_div_self
      (Eventually.of_forall fun N ↦ Nat.sqrt_le_self N)
  have h2 : Tendsto (fun N ↦ 2 * (1 - ((cube d (N - Nat.sqrt N)).card : ℝ) / (cube d N).card))
      atTop (𝓝 0) := by
    simpa using (hq.const_sub 1).const_mul 2
  -- `μ` is a cluster point of the modified sequence
  have hμ' : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence (Fin d → ℤ) E)
      atTop fun N ↦ WithSetwiseTopology.ofMeasure (μs' N) := by
    refine mapClusterPt_of_tendsto_real_sub hμ fun A _ ↦ ?_
    refine squeeze_zero_norm (fun N ↦ ?_) h2
    rw [Real.norm_eq_abs, hμs N]
    have h := Specification.abs_average_real_sub_le_of_subset (γ := γ) (ν := ν)
      (cubeTranslates_nonempty d N (N - Nat.sqrt N))
      (cubeTranslates_mono d N (Nat.sub_le N (Nat.sqrt N))) A
    rwa [card_cubeTranslates, card_cubeTranslates] at h
  -- the modified sequence is fixed by `γ_{Λ_{√N}}`
  have hfix : ∀ N, γ.bindPM (cube d (Nat.sqrt N)) (μs' N) = μs' N := by
    intro N
    refine ProbabilityMeasure.toMeasure_injective ?_
    rw [Specification.coe_bindPM]
    refine Specification.bind_average_of_subset fun Λ hΛ ↦ ?_
    have := cube_sub_subset_of_mem_cubeTranslates (Nat.sub_le N (Nat.sqrt N)) hΛ
    rwa [Nat.sub_sub_self (Nat.sqrt_le_self N)] at this
  refine mem_GP_of_mapClusterPt hγq (γs := fun _ ↦ γ) (Λs := fun N ↦ cube d (Nat.sqrt N))
    (νs := μs') (tendsto_cube_atTop.comp tendsto_nat_sqrt_atTop)
    (fun Λ f _ ↦ by simp) ?_
  simpa only [hfix] using hμ'

/-- **Georgii Example (5.20)(1)** for the shift group on `ℤ^d` (random boundary condition `ν`):
every cluster point of `μ_N = |Λ_N|⁻¹ ∑_{i ∈ Λ_N} ν γ_{Λ_N + i}` is shift-invariant and Gibbs. -/
theorem mem_GP_and_measurePreserving_shift_of_mapClusterPt_average_cubeTranslates
    [IsProbabilityMeasure ν] (hγq : γ.IsQuasilocal)
    (hγ : ∀ j, Specification.IsInvariant (shift E j) γ)
    (hν : ∀ j, MeasurePreserving (shift E j).toFun ν ν)
    {μs : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμs : ∀ N, (μs N : Measure ((Fin d → ℤ) → E)) = γ.average ν (cubeTranslates d N N))
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμ : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence (Fin d → ℤ) E)
      atTop fun N ↦ WithSetwiseTopology.ofMeasure (μs N)) :
    μ ∈ GP (S := Fin d → ℤ) (E := E) γ ∧
      ∀ j, MeasurePreserving (shift E j).toFun (μ : Measure ((Fin d → ℤ) → E)) μ :=
  ⟨mem_GP_of_mapClusterPt_average_cubeTranslates hγq hμs hμ,
    measurePreserving_shift_of_mapClusterPt_average_cubeTranslates hγ hν hμs hμ⟩

/-- A constant configuration `ω = (e)_{i ∈ S}` is fixed by every shift (Georgii (5.20)(1):
`τ ω = ω` for `τ ∈ Θ`). -/
lemma measurePreserving_shift_dirac_const (e : E) (j : Fin d → ℤ) :
    MeasurePreserving (shift E j).toFun (Measure.dirac fun _ ↦ e)
      (Measure.dirac fun _ ↦ e) := by
  refine ⟨(shift E j).measurable_toFun, ?_⟩
  rw [Measure.map_dirac' (shift E j).measurable_toFun]
  refine congrArg Measure.dirac (funext fun i ↦ ?_)
  rw [shift_toFun_apply]

/-- **Georgii Example (5.20)(1)** with the constant boundary condition `ω = (e)_{i ∈ S}`: every
cluster point of `|Λ_N|⁻¹ ∑_{i ∈ Λ_N} γ_{Λ_N + i}(· | ω)` is a shift-invariant Gibbs measure. -/
theorem mem_GP_and_measurePreserving_shift_of_mapClusterPt_average_cubeTranslates_dirac
    (hγq : γ.IsQuasilocal) (hγ : ∀ j, Specification.IsInvariant (shift E j) γ) (e : E)
    {μs : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμs : ∀ N, (μs N : Measure ((Fin d → ℤ) → E)) =
      γ.average (Measure.dirac fun _ ↦ e) (cubeTranslates d N N))
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμ : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence (Fin d → ℤ) E)
      atTop fun N ↦ WithSetwiseTopology.ofMeasure (μs N)) :
    μ ∈ GP (S := Fin d → ℤ) (E := E) γ ∧
      ∀ j, MeasurePreserving (shift E j).toFun (μ : Measure ((Fin d → ℤ) → E)) μ :=
  mem_GP_and_measurePreserving_shift_of_mapClusterPt_average_cubeTranslates hγq hγ
    (measurePreserving_shift_dirac_const e) hμs hμ

/-- **Existence of shift-invariant Gibbs measures** (Georgii (5.17)(1)/(5.20)(1)): over a finite
state space, a quasilocal shift-invariant specification on `ℤ^d` has a shift-invariant one. -/
theorem exists_mem_GP_forall_measurePreserving_shift [Finite E] [MeasurableSingletonClass E]
    [Nonempty E] (hγq : γ.IsQuasilocal) (hγ : ∀ j, Specification.IsInvariant (shift E j) γ) :
    ∃ μ ∈ GP (S := Fin d → ℤ) (E := E) γ,
      ∀ j, MeasurePreserving (shift E j).toFun (μ : Measure ((Fin d → ℤ) → E)) μ := by
  classical
  obtain ⟨e⟩ := ‹Nonempty E›
  -- Georgii (5.20)(1): `𝓡_N = {Λ_N + i : i ∈ Λ_{k(N)}}` with `k(N) = N - √N`, so that
  -- `Λ_{√N} ⊆ ⋂ 𝓡_N ↑ S`; the boundary condition is the shift-invariant `δ_ω`, `ω ≡ e`.
  have hRne : ∀ N : ℕ, (cubeTranslates d N (N - Nat.sqrt N)).Nonempty := fun N ↦
    cubeTranslates_nonempty d N (N - Nat.sqrt N)
  have hΛ : Tendsto (fun N ↦ (cubeTranslates d N (N - Nat.sqrt N)).inf' (hRne N) id)
      atTop atTop := by
    refine tendsto_atTop_mono (fun N ↦ ?_) (tendsto_cube_atTop.comp tendsto_nat_sqrt_atTop)
    refine Finset.le_inf' _ _ fun Λ hΛ ↦ ?_
    have h := cube_sub_subset_of_mem_cubeTranslates (Nat.sub_le N (Nat.sqrt N)) hΛ
    rwa [Nat.sub_sub_self (Nat.sqrt_le_self N)] at h
  have hsymm : ∀ τ ∈ Set.range (shift (S := Fin d → ℤ) E), Tendsto (fun N ↦
      (((cubeTranslates d N (N - Nat.sqrt N)).map
          (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding ∆
        cubeTranslates d N (N - Nat.sqrt N)).card : ℝ) /
          (cubeTranslates d N (N - Nat.sqrt N)).card) atTop (𝓝 0) := by
    rintro τ ⟨j, rfl⟩
    simp only [card_symmDiff_map_cubeTranslates_shift, card_cubeTranslates]
    exact (tendsto_card_symmDiff_map_addRight_cube_div j).comp tendsto_sub_nat_sqrt_atTop
  obtain ⟨μ, hμGP, hμinv, -⟩ := exists_mem_GP_and_forall_measurePreserving
    (I := Set.range (shift (S := Fin d → ℤ) E)) (γs := fun _ : ℕ ↦ γ)
    (νs := fun _ : ℕ ↦ (⟨Measure.dirac fun _ ↦ e, inferInstance⟩ :
      ProbabilityMeasure ((Fin d → ℤ) → E)))
    (μs := fun N ↦ ⟨γ.average (Measure.dirac fun _ ↦ e)
      (cubeTranslates d N (N - Nat.sqrt N)), γ.isProbabilityMeasure_average _ (hRne N)⟩)
    hγq (by rintro τ ⟨j, rfl⟩ N; exact hγ j) (fun Λ f _ ↦ by simp) hRne hΛ hsymm
    (by rintro τ ⟨j, rfl⟩ N; exact measurePreserving_shift_dirac_const e j) (fun N ↦ rfl)
    (locallyEquicontinuous_of_finite _ _)
  exact ⟨μ, hμGP, fun j ↦ hμinv _ ⟨j, rfl⟩⟩

/-- **Shift-invariant Gibbs measures for the Ising model on `ℤ^d`** (Georgii (5.20)(1)). -/
theorem exists_latticeIsing_mem_GP_forall_measurePreserving_shift (d : ℕ) (J h β : ℝ) :
    ∃ μ ∈ GP (S := Fin d → ℤ) (E := Bool) (isingSpecification (latticeGraph d) J h β),
      ∀ j, MeasurePreserving (shift Bool j).toFun
        (μ : Measure ((Fin d → ℤ) → Bool)) μ :=
  exists_mem_GP_forall_measurePreserving_shift
    (Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable uniformSpinMeasure β)
    (isInvariant_shift_isingSpecification d J h β)


end MeasureTheory.GibbsMeasure

end
