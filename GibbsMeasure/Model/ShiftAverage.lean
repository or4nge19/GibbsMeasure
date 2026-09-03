/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.InvariantExistence
public import GibbsMeasure.Specification.InvariantExistenceGroup
public import GibbsMeasure.Potential.FreeBoundary
public import GibbsMeasure.Model.Ising

/-!
# Shift-invariant Gibbs measures on `ℤ^d` from averaged Gibbs distributions

Georgii (5.17)(1): a shift-invariant specification with `𝒢(γ)` non-empty and compact has a
shift-invariant Gibbs measure, by Corollary (5.16) since the shift group `Θ` is abelian
(`exists_mem_GP_forall_measurePreserving_shift_of_isCompact`, no hypothesis on the state space);
in particular for the Gibbsian specification of a shift-invariant absolutely summable potential
over a standard Borel state space (Theorem (4.23)(a)).

Georgii Example (5.20)(1): cluster points of the cube-averaged finite-volume Gibbs
distributions `|Λ_N|⁻¹ ∑_{i ∈ Λ_N} γ_{Λ_N + i}(· | ω)` with a constant boundary condition are
shift-invariant Gibbs measures; for finite `E` they exist, in particular for the Ising model.

Georgii Theorem (5.15) with `I₀ = Θ` and Example (5.17)(2): a further symmetrisation over an
abelian group of symmetries commuting with the shift group — or over a single involution, the
shape of the `F`-steps in Examples (5.17)(2)–(4) — preserves the shift-invariance
(`exists_mem_GP_forall_measurePreserving_shift_and_measurePreserving_of_isCompact`). The
concrete instance is the spin flip `pureSpin S boolNot` of the zero-field Ising model:
`𝒢_{F∘Θ} ≠ ∅` for `F = {id, flip}`
(`exists_latticeIsing_mem_GP_forall_measurePreserving_shift_and_spinFlip`).
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

/-- Georgii (5.20)(1): `|(Λ_N + j) ∆ Λ_N| + 2 |Λ_{N - m}| ≤ 2 |Λ_N|` for `m = ‖j‖₁ ≤ N`, since
`Λ_{N - m} + j ⊆ Λ_N ∩ (Λ_N + j)`. -/
lemma card_symmDiff_map_addRight_cube_le (j : Fin d → ℤ) {N : ℕ} (hN : ∑ k, (j k).natAbs ≤ N) :
    ((cube d N).map (Equiv.addRight j).toEmbedding ∆ cube d N).card +
      2 * (cube d (N - ∑ k, (j k).natAbs)).card ≤ 2 * (cube d N).card := by
  set m := ∑ k, (j k).natAbs with hm
  set C := cube d N with hC
  set D := (cube d (N - m)).map (Equiv.addRight j).toEmbedding with hD
  have hDC : D ⊆ C := fun x hx ↦ by
    rw [hD, Potential.mem_translate, mem_cube] at hx
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
      rw [Potential.mem_translate, add_sub_cancel_right]
      exact mem_cube.2 fun k ↦ by simp
    rw [hab, Potential.mem_translate, mem_cube] at hmem
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
  rw [Potential.mem_translate]
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

/-! ### Georgii (5.17)(1): existence of shift-invariant Gibbs measures -/

section ShiftGroup
variable [AddCommGroup S]

/-- On an abelian group of sites, `j ↦ θ_j` is a homomorphism into the transformation group:
`θ_{j + j'} = θ_j ∘ θ_{j'}` (Georgii (5.2)(1): the shift group `Θ`). -/
lemma shift_add (j j' : S) : shift E (j + j') = shift E j * shift E j' := by
  refine Transformation.ext (Equiv.ext fun x ↦ ?_) rfl
  show x + (j + j') = x + j' + j
  rw [add_comm j j', ← add_assoc]

/-- **Georgii (5.17)(1).** A shift-invariant specification on an abelian group of sites whose
set of Gibbs measures is non-empty and compact in the topology of local convergence admits a
shift-invariant Gibbs measure, by Corollary (5.16) since the shift group `Θ` is abelian. No
hypothesis on the state space is needed. -/
theorem exists_mem_GP_forall_measurePreserving_shift_of_isCompact {γ : Specification S E}
    (hγ : ∀ j, Specification.IsInvariant (shift E j) γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ})
    (hne : (GP (S := S) (E := E) γ).Nonempty) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      ∀ j : S, MeasurePreserving (shift E j).toFun (μ : Measure (S → E)) μ :=
  exists_mem_GP_and_forall_measurePreserving_of_isCompact (Φ := shift E)
    (fun j j' ↦ shift_add j j') hγ hcpt hne

/-- **Georgii Theorem (5.15)(ii) with the shift group as inner subgroup `I₀ = Θ`.** Let `γ` be
invariant under the shifts and under an abelian group `A` of symmetries `Φ`, each commuting with
the shift group in Georgii's sense `Φ x ∘ Θ = Θ ∘ Φ x` (i.e. `θ_j ∘ Φ x = Φ x ∘ θ_{j'}` for some
`j'`). If `𝒢(γ)` is non-empty and compact in the topology of local convergence, then `𝒢(γ)`
contains a measure invariant under all shifts and all `Φ x` simultaneously:
`𝒢_{⟨Φ⟩∘Θ}(γ) ≠ ∅`. Example (5.17)(1) supplies the shift-invariant starting measure, and
Theorem (5.15)(ii) preserves its shift-invariance while averaging over `A`. -/
theorem exists_mem_GP_forall_measurePreserving_shift_and_measurePreserving_of_isCompact
    {A : Type*} [AddCommGroup A] {γ : Specification S E} {Φ : A → Transformation S E}
    (hΦ : ∀ x y, Φ (x + y) = Φ x * Φ y)
    (hcomm : ∀ (j : S) (x : A), ∃ j',
      (shift E j).toFun ∘ (Φ x).toFun = (Φ x).toFun ∘ (shift E j').toFun)
    (hγs : ∀ j, Specification.IsInvariant (shift E j) γ)
    (hγΦ : ∀ x, Specification.IsInvariant (Φ x) γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ})
    (hne : (GP (S := S) (E := E) γ).Nonempty) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ j : S, MeasurePreserving (shift E j).toFun (μ : Measure (S → E)) μ) ∧
        ∀ x : A, MeasurePreserving (Φ x).toFun (μ : Measure (S → E)) μ := by
  obtain ⟨ν, hν, hνs⟩ :=
    exists_mem_GP_forall_measurePreserving_shift_of_isCompact hγs hcpt hne
  exact exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_measurePreserving
    (T₀ := shift E) hΦ hcomm hγΦ hcpt hν hνs

/-- **Georgii Theorem (5.15)(ii) with `I₀ = Θ` and an involution generating `I₁`** — the shape
of the `F`-steps in Georgii's Examples (5.17)(2)–(4): a specification invariant under the shifts
and under an involution `τ` commuting with the shift group has, when `𝒢(γ)` is non-empty and
compact in the topology of local convergence, a Gibbs measure invariant under `τ` and all shifts
simultaneously: `𝒢_{{id,τ}∘Θ}(γ) ≠ ∅`. -/
theorem exists_mem_GP_forall_measurePreserving_shift_and_involution_of_isCompact
    {γ : Specification S E} {τ : Transformation S E} (hτ : τ * τ = 1)
    (hcomm : ∀ j : S, ∃ j', (shift E j).toFun ∘ τ.toFun = τ.toFun ∘ (shift E j').toFun)
    (hγs : ∀ j, Specification.IsInvariant (shift E j) γ)
    (hγτ : Specification.IsInvariant τ γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ})
    (hne : (GP (S := S) (E := E) γ).Nonempty) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ j : S, MeasurePreserving (shift E j).toFun (μ : Measure (S → E)) μ) ∧
        MeasurePreserving τ.toFun (μ : Measure (S → E)) μ := by
  have key : ∀ n : ℤ, τ ^ n = 1 ∨ τ ^ n = τ := by
    intro n
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Int.even_or_odd n
    · left
      rw [hk, ← two_mul, zpow_mul, zpow_two, hτ, one_zpow]
    · right
      rw [hk, zpow_add, zpow_one, zpow_mul, zpow_two, hτ, one_zpow, one_mul]
  have hγΦ : ∀ n : ℤ, Specification.IsInvariant (τ ^ n) γ := by
    intro n
    obtain h | h := key n
    · rw [h]
      exact Specification.isInvariant_id γ
    · rw [h]
      exact hγτ
  have hcomm' : ∀ (j : S) (n : ℤ), ∃ j',
      (shift E j).toFun ∘ (τ ^ n).toFun = (τ ^ n).toFun ∘ (shift E j').toFun := by
    intro j n
    obtain h | h := key n
    · refine ⟨j, ?_⟩
      rw [h]
      funext ω
      simp only [Function.comp_apply, Transformation.one_def, Transformation.id_toFun]
    · rw [h]
      exact hcomm j
  obtain ⟨μ, hμ, hs, hall⟩ :=
    exists_mem_GP_forall_measurePreserving_shift_and_measurePreserving_of_isCompact
      (Φ := fun n : ℤ ↦ τ ^ n) (fun x y ↦ zpow_add τ x y) hcomm' hγs hγΦ hcpt hne
  refine ⟨μ, hμ, hs, ?_⟩
  have h1 := hall 1
  rwa [zpow_one] at h1

end ShiftGroup

/-- **Georgii (5.17)(1) for Gibbsian specifications.** Over a standard Borel state space, the
Gibbsian specification of a shift-invariant absolutely summable potential on `ℤ^d` admits a
shift-invariant Gibbs measure: `𝒢(βΦ)` is non-empty and compact by Theorem (4.23)(a). -/
theorem exists_mem_GP_gibbsSpecification_forall_measurePreserving_shift [StandardBorelSpace E]
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant) (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) :
    ∃ μ ∈ GP (S := Fin d → ℤ) (E := E)
        (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β),
      ∀ j, MeasurePreserving (shift E j).toFun (μ : Measure ((Fin d → ℤ) → E)) μ :=
  exists_mem_GP_forall_measurePreserving_shift_of_isCompact
    (isInvariant_shift_gibbsSpecification hΦ ν β)
    (Potential.isCompact_setOf_mem_GP_gibbsSpecification ν β)
    (Potential.GP_gibbsSpecification_nonempty ν β)

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

/-- **Existence of shift-invariant Gibbs measures** (Georgii (5.20)(1), existence part): over a
finite state space, a quasilocal shift-invariant specification on `ℤ^d` has a shift-invariant
Gibbs measure. A corollary of the general (5.17)(1): `𝒢(γ)` is closed by quasilocality and the
whole space of random fields is compact over a finite state space (Example (4.11)(2)). -/
theorem exists_mem_GP_forall_measurePreserving_shift [Finite E] [MeasurableSingletonClass E]
    [Nonempty E] (hγq : γ.IsQuasilocal) (hγ : ∀ j, Specification.IsInvariant (shift E j) γ) :
    ∃ μ ∈ GP (S := Fin d → ℤ) (E := E) γ,
      ∀ j, MeasurePreserving (shift E j).toFun (μ : Measure ((Fin d → ℤ) → E)) μ := by
  refine exists_mem_GP_forall_measurePreserving_shift_of_isCompact hγ
    (isClosed_setOf_mem_GP hγq).isCompact ?_
  obtain ⟨μ, hμ, -⟩ := exists_isLocalThermodynamicLimit_mem_GP hγq
    (fun _ ↦ Classical.arbitrary E) (locallyEquicontinuous_of_finite _ _)
  exact ⟨μ, hμ⟩

/-- **Shift-invariant Gibbs measures for the Ising model on `ℤ^d`** (Georgii (5.20)(1)). -/
theorem exists_latticeIsing_mem_GP_forall_measurePreserving_shift (d : ℕ) (J h β : ℝ) :
    ∃ μ ∈ GP (S := Fin d → ℤ) (E := Bool) (isingSpecification (latticeGraph d) J h β),
      ∀ j, MeasurePreserving (shift Bool j).toFun
        (μ : Measure ((Fin d → ℤ) → Bool)) μ :=
  exists_mem_GP_forall_measurePreserving_shift
    (Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable uniformSpinMeasure β)
    (isInvariant_shift_isingSpecification d J h β)


/-! ### Georgii Example (5.17)(2): pure spin symmetries composed with the shifts -/

variable (S) in
/-- Georgii (5.2)(2)/(5.20): the **pure spin transformation** applying the same measurable
bijection `e` of the state space at every site; its spatial part is the identity. The spin flip
of the Ising model is `pureSpin S boolNot`. -/
def pureSpin (e : E ≃ᵐ E) : Transformation S E where
  sites := Equiv.refl S
  spin _ := e

@[simp] lemma pureSpin_toFun_apply (e : E ≃ᵐ E) (ω : S → E) (i : S) :
    (pureSpin S e).toFun ω i = e (ω i) := rfl

@[simp] lemma pureSpin_inv_toFun_apply (e : E ≃ᵐ E) (ω : S → E) (i : S) :
    (pureSpin S e).inv.toFun ω i = e.symm (ω i) := rfl

lemma pureSpin_mul (e f : E ≃ᵐ E) :
    pureSpin S e * pureSpin S f = pureSpin S (f.trans e) := rfl

lemma pureSpin_refl : pureSpin S (MeasurableEquiv.refl E) = 1 := rfl

/-- Pure spin transformations commute with the shifts (Georgii (5.20): elements of `T⁰` commute
elementwise with the spatial transformations). -/
lemma shift_toFun_comp_pureSpin_toFun [AddGroup S] (e : E ≃ᵐ E) (j : S) :
    (shift E j).toFun ∘ (pureSpin S e).toFun = (pureSpin S e).toFun ∘ (shift E j).toFun := by
  funext ω i
  simp only [Function.comp_apply, shift_toFun_apply, pureSpin_toFun_apply]

/-- The spin flip is an involution of configuration space. -/
lemma pureSpin_boolNot_mul_self :
    pureSpin S boolNot * pureSpin S boolNot = (1 : Transformation S Bool) := by
  rw [pureSpin_mul, boolNot_trans_boolNot, pureSpin_refl]

/-- The zero-field Ising potential on any graph is invariant under the spin flip: the pair terms
are even in the spins, and the odd single-site terms carry the factor `h = 0`. This generalises
`Peierls.map_spinFlip_isingPotential` (the case `G = latticeGraph 2`, `J = 1`). -/
lemma map_pureSpin_boolNot_isingPotential (G : SimpleGraph S) (J : ℝ) :
    Potential.map (pureSpin S boolNot) (isingPotential G J 0) = isingPotential G J 0 := by
  classical
  funext A η
  rw [Potential.map_apply]
  have hA : A.map (pureSpin S boolNot).sites.symm.toEmbedding = A := by
    ext x
    simp [pureSpin]
  rw [hA]
  simp only [isingPotential, Potential.nearestNeighbourPair]
  have hspin : ∀ c : Bool, spin (!c) = -spin c := fun c ↦ by cases c <;> simp [spin]
  by_cases h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j
  · have h1 : ¬A.card = 1 := by
      have := h2.1
      omega
    rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 h2.1
    rw [Finset.prod_pair huv, Finset.prod_pair huv]
    simp only [pureSpin_inv_toFun_apply, boolNot_symm_apply, hspin]
    ring
  · by_cases h1 : A.card = 1
    · rw [ite_eq_left h1, ite_eq_left h1]
      simp
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h2]

/-- The spin flip preserves the uniform a-priori spin measure. This generalises
`Peierls.measurePreserving_boolNot`. -/
lemma measurePreserving_boolNot_uniformSpinMeasure :
    MeasurePreserving ⇑boolNot uniformSpinMeasure uniformSpinMeasure := by
  refine ⟨boolNot.measurable, ?_⟩
  have hsingle : ∀ c : Bool, uniformSpinMeasure {c} = 2⁻¹ := by
    intro c
    rw [uniformSpinMeasure, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
  refine Measure.ext_of_singleton fun c ↦ ?_
  rw [Measure.map_apply boolNot.measurable (measurableSet_singleton c)]
  have hpre : (⇑boolNot ⁻¹' {c}) = {!c} := by
    ext d
    cases c <;> cases d <;> simp
  rw [hpre, hsingle, hsingle]

/-- **Georgii (5.9)(b) for the spin flip.** At zero external field, the Ising specification on
any countable locally finite graph is invariant under the spin flip. This generalises
`Peierls.isInvariant_spinFlip` (the case `G = latticeGraph 2`, `J = 1`). -/
lemma isInvariant_pureSpin_boolNot_isingSpecification [Countable S] (G : SimpleGraph S)
    [G.LocallyFinite] (J β : ℝ) :
    Specification.IsInvariant (pureSpin S boolNot) (isingSpecification G J 0 β) :=
  Potential.isInvariant_gibbsSpecification (pureSpin S boolNot) (isingPotential G J 0)
    uniformSpinMeasure β (fun _ ↦ measurePreserving_boolNot_uniformSpinMeasure)
    (map_pureSpin_boolNot_isingPotential G J)

/-- **Georgii Example (5.17)(2)-shaped result for the Ising model**, with the spin flip as the
outer symmetry group: at zero external field, the Ising specification on `ℤ^d` has a Gibbs
measure that is simultaneously shift-invariant and spin-flip-invariant — in Georgii's notation
`𝒢_{F∘Θ}(γ) ≠ ∅` for the two-element group `F = {id, flip}`. This is Theorem (5.15)(ii) applied
with `I₀ = Θ` (whose invariant Gibbs measure Example (5.17)(1) supplies) and `I₁ = F`, using
that the flip commutes with every shift. -/
theorem exists_latticeIsing_mem_GP_forall_measurePreserving_shift_and_spinFlip
    (d : ℕ) (J β : ℝ) :
    ∃ μ ∈ GP (S := Fin d → ℤ) (E := Bool) (isingSpecification (latticeGraph d) J 0 β),
      (∀ j, MeasurePreserving (shift Bool j).toFun (μ : Measure ((Fin d → ℤ) → Bool)) μ) ∧
        MeasurePreserving (pureSpin (Fin d → ℤ) boolNot).toFun
          (μ : Measure ((Fin d → ℤ) → Bool)) μ :=
  exists_mem_GP_forall_measurePreserving_shift_and_involution_of_isCompact
    pureSpin_boolNot_mul_self
    (fun j ↦ ⟨j, shift_toFun_comp_pureSpin_toFun boolNot j⟩)
    (isInvariant_shift_isingSpecification d J 0 β)
    (isInvariant_pureSpin_boolNot_isingSpecification (latticeGraph d) J β)
    (isCompact_setOf_latticeIsingGibbsMeasure d J 0 β)
    (latticeIsingGibbsMeasure_nonempty d J 0 β)

/-! ### Georgii Example (5.20)(2): free boundary conditions -/

section FreeBoundarySymmetry

open Potential

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ : Potential S E}
  {ν : Measure E} [IsProbabilityMeasure ν] {β : ℝ}

/-- **Georgii Example (5.20)(2): free boundary conditions produce symmetric Gibbs measures.**

Let `Φ ∈ ℬ` be invariant under a set `I` of `λ`-preserving transformations whose spatial parts
preserve each volume `Δ_n` of an exhausting sequence — Georgii's `I ⊆ T_λ⁰ ∘ R` and the cubes
`Λ_N`, which every reflection maps onto themselves.  Then each truncation `Φ^{Δ_n}` inherits the
`I`-invariance, so every cluster point of the free-boundary net `ν_n γ^{Φ^{Δ_n}}_{Δ_n}` is an
`I`-invariant Gibbs measure for `Φ`.

The boundary fields `ν_n` need only be `I`-invariant; by Georgii's remark they may be taken to be
anything at all as far as the Gibbs half is concerned, since `γ^{Φ^{Δ}}_{Δ}(·|ω)` restricted to
`𝓕_Δ` does not depend on `ω`. -/
theorem mem_GP_and_measurePreserving_of_mapClusterPt_truncation
    [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    {I : Set (Transformation S E)}
    (hIspin : ∀ τ ∈ I, ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hIΦ : ∀ τ ∈ I, Potential.map τ Φ = Φ)
    {Δs : ℕ → Finset S} (hΔ : Tendsto Δs atTop atTop)
    (hΔinv : ∀ τ ∈ I, ∀ n, (Δs n).map τ.sites.toEmbedding = Δs n)
    (νs : ℕ → ProbabilityMeasure (S → E))
    (hνs : ∀ τ ∈ I, ∀ n, MeasurePreserving τ.toFun (νs n : Measure (S → E)) (νs n))
    {μ : ProbabilityMeasure (S → E)}
    (hcp : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) atTop
      fun n ↦ WithSetwiseTopology.ofMeasure
        ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation (Δs n)) ν β).bindPM
          (Δs n) (νs n))) :
    μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ := by
  classical
  refine ⟨?_, fun τ hτ ↦ ?_⟩
  · exact mem_GP_of_mapClusterPt
      (isQuasilocal_gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) hΔ
      (fun Λ f hf ↦ (tendsto_dist_action_truncation ν β Λ hf).comp hΔ) hcp
  · -- the truncations are `τ`-invariant, and `{Δ_n}` is a one-element Følner family for `τ`
    have hinv : ∀ n, Specification.IsInvariant τ
        (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation (Δs n)) ν β) := fun n ↦
      Potential.isInvariant_gibbsSpecification τ _ ν β (hIspin τ hτ)
        (map_truncation_eq_of_map_eq (hIΦ τ hτ) (hΔinv τ hτ n))
    refine measurePreserving_of_mapClusterPt_average_of_eventually_preimage_eq
      (τs := fun _ ↦ τ) (γs := fun n ↦ gibbsSpecificationOfAbsolutelySummable
        (Φ := Φ.truncation (Δs n)) ν β) (νs := νs) (R := fun n ↦ {Δs n})
      hinv (fun n ↦ hνs τ hτ n) (fun n ↦ Finset.singleton_nonempty _) ?_
      (fun _ _ ↦ Eventually.of_forall fun _ ↦ rfl) ?_ hcp
    · refine tendsto_const_nhds.congr fun n ↦ ?_
      have hmap : ({Δs n} : Finset (Finset S)).map
          (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding = {Δs n} := by
        rw [Finset.map_singleton]
        congr 1
        change (Finset.mapEmbedding τ.sites.toEmbedding) (Δs n) = Δs n
        rw [Finset.mapEmbedding_apply, hΔinv τ hτ n]
      rw [hmap, symmDiff_self]
      simp
    · intro n
      rw [Specification.average_singleton]
      rfl

end FreeBoundarySymmetry

end MeasureTheory.GibbsMeasure

end
