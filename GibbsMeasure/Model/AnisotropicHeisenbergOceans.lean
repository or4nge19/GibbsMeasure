/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.HaarToSphere
public import GibbsMeasure.Model.DiscreteSymmetryBreakingExamples
public import GibbsMeasure.Model.HeisenbergOceans

/-!
# Georgii 18.3.6: the anisotropic Heisenberg ferromagnet

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.6.  The state space is the unit sphere
`E` of a finite-dimensional real inner product space `V` (Georgii: `ℝⁿ`, `n ≥ 2`), the a priori
measure is the normalised surface measure `sphereProb V` of
`GibbsMeasure/Model/HeisenbergOceans.lean`, and the `C`-potential is **(18.33)**

`Φ_C = -∑_{{i,j} ⊆ C, |i-j|=1} [σ_{i,1}σ_{j,1} + α ∑_{ℓ ≥ 2} σ_{i,ℓ}σ_{j,ℓ}]`,  `0 ≤ α < 1`.

Georgii's `1`-direction is here a unit vector `u ∈ E`, and the term in square brackets is the
deformation of the inner product

`⟪x, u⟫⟪y, u⟫ + α (⟪x, y⟫ - ⟪x, u⟫⟪y, u⟫) = (1 - α) ⟪x, u⟫⟪y, u⟫ + α ⟪x, y⟫`

(`anisoBond`), which is what `anisoHeisenbergCube` sums over the edges of `C`.  At `α = 1` this
is the isotropic Heisenberg interaction `heisenbergCube` of
`GibbsMeasure/Model/HeisenbergOceans.lean`.

## Main results

* `anisoBond_le_one` and `anisoBond_eq_one_iff` — the bond interaction is at most `1` and equals
  `1` exactly when the two spins are the same polar vector `±u`; hence
  `localGroundEnergy_anisoHeisenbergCube`, **Georgii's `m_Φ = -4`** in the plane, and
  `anisoHeisenbergCube_eq_neg_four_iff`, the local ground states are the two constant
  configurations `±u`.
* `anisoPolarCap`, `anisoG` — Georgii's polar caps `U_± = {x : ±x₁ ≥ 1 - δ}` and the sets
  `G_± = U_±^C`; `localGroundStates_subset_anisoG` is **his "straightforward computation"**
  `G_ε(Φ) ⊆ G_+ ∪ G_-` for `0 < ε < (1 - α)δ`, and `isPStablePartition_anisoG` the stability
  (18.23)(a)(ii), which for `δ < 1` is the disjointness of the two caps.
* `isPhiSymmetric_anisoG` — **"the reflection of the first coordinate of all spins is a symmetry
  of `Φ` which maps `G_+` onto `G_-`, and vice versa"**: the reflection in the hyperplane `u^⊥`
  is a linear isometry, so it preserves the surface measure
  (`LinearIsometryEquiv.measurePreserving_sphere_toSphere_volume`), and it reverses `⟪·, u⟫` while
  preserving `⟪·, ·⟫`.
* `eventually_two_le_encard_extremePoints_anisoHeisenberg` — **Georgii's conclusion**,
  `|ex 𝒢_Θ(βΦ)| ≥ 2` for `β` large enough, and
  `eventually_exists_anisoHeisenberg_gibbsMeasure_pair` for the two measures themselves.
-/

@[expose] public section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The anisotropic bond interaction -/

/-- **The bracket of Georgii (18.33)**, the deformation of the inner product in the direction of
the unit vector `u`: `(1 - α) ⟪x, u⟫⟪y, u⟫ + α ⟪x, y⟫`. -/
def anisoBond (α : ℝ) (u x y : V) : ℝ := (1 - α) * (⟪x, u⟫ * ⟪y, u⟫) + α * ⟪x, y⟫

lemma anisoBond_comm (α : ℝ) (u x y : V) : anisoBond α u x y = anisoBond α u y x := by
  rw [anisoBond, anisoBond, real_inner_comm x y, mul_comm ⟪x, u⟫ ⟪y, u⟫]

lemma continuous_anisoBond (α : ℝ) (u : V) :
    Continuous (Function.uncurry (anisoBond α u)) := by
  unfold Function.uncurry anisoBond
  fun_prop

variable {α : ℝ} {u x y : V}

lemma abs_real_inner_le_one (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) : |⟪x, u⟫| ≤ 1 := by
  have := abs_real_inner_le_norm x u
  rwa [hx, hu, one_mul] at this

/-- **The bond interaction of (18.33) is at most `1`** on the unit sphere. -/
lemma anisoBond_le_one (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hu : ‖u‖ = 1) (hx : ‖x‖ = 1)
    (hy : ‖y‖ = 1) : anisoBond α u x y ≤ 1 := by
  have h1 : ⟪x, u⟫ * ⟪y, u⟫ ≤ 1 := by
    have hx' := abs_real_inner_le_one hx hu
    have hy' := abs_real_inner_le_one hy hu
    calc ⟪x, u⟫ * ⟪y, u⟫ ≤ |⟪x, u⟫ * ⟪y, u⟫| := le_abs_self _
      _ = |⟪x, u⟫| * |⟪y, u⟫| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul hx' hy' (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h2 : ⟪x, y⟫ ≤ 1 := by
    have := abs_real_inner_le_norm x y
    rw [hx, hy, one_mul] at this
    exact (le_abs_self _).trans this
  rw [anisoBond]
  nlinarith

/-- **`-1` is a lower bound for `-anisoBond`.** -/
lemma neg_one_le_neg_anisoBond (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hu : ‖u‖ = 1) (hx : ‖x‖ = 1)
    (hy : ‖y‖ = 1) : (-1 : ℝ) ≤ -anisoBond α u x y :=
  neg_le_neg (anisoBond_le_one hα0 hα1 hu hx hy)

lemma neg_anisoBond_le_one (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hu : ‖u‖ = 1) (hx : ‖x‖ = 1)
    (hy : ‖y‖ = 1) : -anisoBond α u x y ≤ 1 := by
  have h := anisoBond_le_one (α := α) (u := u) (x := -x) (y := y) hα0 hα1 hu (by simpa using hx) hy
  simp only [anisoBond, inner_neg_left] at h ⊢
  linarith

/-- **Georgii's "the term in square brackets is a deformation of the inner product"**: on the
unit sphere the bond interaction attains its maximum `1` exactly when both spins are the same
polar vector `±u`.  For `α < 1` the anisotropy is what forces the spins to the poles; for
`α = 1` the statement below is still true only because the pair `(x, y)` with `⟪x,y⟫ = 1` is
`x = y`, which is the isotropic case and is *not* what is claimed here — the hypothesis `α < 1`
is therefore genuinely used. -/
lemma anisoBond_eq_one_iff (hα0 : 0 ≤ α) (hα1 : α < 1) (hu : ‖u‖ = 1) (hx : ‖x‖ = 1)
    (hy : ‖y‖ = 1) : anisoBond α u x y = 1 ↔ (x = u ∧ y = u) ∨ (x = -u ∧ y = -u) := by
  constructor
  · intro heq
    have hxu := abs_real_inner_le_one hx hu
    have hyu := abs_real_inner_le_one hy hu
    have hxy : ⟪x, y⟫ ≤ 1 := by
      have := abs_real_inner_le_norm x y
      rw [hx, hy, one_mul] at this
      exact (le_abs_self _).trans this
    have hprod : ⟪x, u⟫ * ⟪y, u⟫ ≤ 1 := by
      calc ⟪x, u⟫ * ⟪y, u⟫ ≤ |⟪x, u⟫| * |⟪y, u⟫| := (le_abs_self _).trans (abs_mul _ _).le
        _ ≤ 1 * 1 := mul_le_mul hxu hyu (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hone : ⟪x, u⟫ * ⟪y, u⟫ = 1 := by
      rw [anisoBond] at heq
      nlinarith
    have hx1 : ⟪x, u⟫ = 1 ∨ ⟪x, u⟫ = -1 := by
      rcases le_or_gt ⟪x, u⟫ 0 with h | h
      · right
        nlinarith [abs_le.1 hxu, abs_le.1 hyu]
      · left
        nlinarith [abs_le.1 hxu, abs_le.1 hyu]
    have hkey : ∀ z : V, ‖z‖ = 1 → ⟪z, u⟫ = 1 → z = u := fun z hz hzu ↦
      (inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) hz hu).1 hzu
    have hkey' : ∀ z : V, ‖z‖ = 1 → ⟪z, u⟫ = -1 → z = -u := fun z hz hzu ↦
      (inner_eq_neg_one_iff_of_norm_eq_one (𝕜 := ℝ) hz hu).1 hzu
    rcases hx1 with hx1 | hx1
    · have hy1 : ⟪y, u⟫ = 1 := by rw [hx1, one_mul] at hone; exact hone
      exact Or.inl ⟨hkey x hx hx1, hkey y hy hy1⟩
    · have hy1 : ⟪y, u⟫ = -1 := by rw [hx1] at hone; linarith
      exact Or.inr ⟨hkey' x hx hx1, hkey' y hy hy1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp only [anisoBond, real_inner_self_eq_norm_sq, inner_neg_left, inner_neg_right, hu] <;>
      ring


/-! ### Georgii (18.33): the anisotropic Heisenberg cube interaction -/

variable (α u) in
/-- **Georgii (18.33)**: the `C`-potential of the anisotropic Heisenberg ferromagnet with
anisotropy `α` in the direction of the unit vector `u`. -/
abbrev anisoHeisenbergCube (d : ℕ) (u : sphere (0 : V) 1) :
    ((Fin d → Fin 2) → sphere (0 : V) 1) → ℝ :=
  cubeBondSum d fun x y ↦ -anisoBond α (u : V) (x : V) (y : V)

variable {d : ℕ} {u : sphere (0 : V) 1}

lemma norm_sphere_eq_one (x : sphere (0 : V) 1) : ‖(x : V)‖ = 1 :=
  mem_sphere_zero_iff_norm.1 x.2

lemma continuous_anisoHeisenbergCube : Continuous (anisoHeisenbergCube α d u) := by
  refine continuous_cubeBondSum ?_
  have h : Continuous fun p : sphere (0 : V) 1 × sphere (0 : V) 1 ↦ ((p.1 : V), (p.2 : V)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_anisoBond α (u : V)).comp h).neg

lemma measurable_anisoHeisenbergCube : Measurable (anisoHeisenbergCube α d u) :=
  continuous_anisoHeisenbergCube.measurable

/-- **Condition (iii) of Georgii (17.18)** for (18.33). -/
lemma anisoHeisenbergCube_cubeRefl (k : Fin d) (ζ : (Fin d → Fin 2) → sphere (0 : V) 1) :
    anisoHeisenbergCube α d u (cubeRefl (sphere (0 : V) 1) k ζ) = anisoHeisenbergCube α d u ζ :=
  cubeBondSum_cubeRefl _ k ζ

section Anisotropy

variable (hα0 : 0 ≤ α) (hα1 : α < 1)

include hα0 hα1

/-- **Georgii's `Φ_C ≥ -4`** in the plane. -/
lemma neg_four_le_anisoHeisenbergCube (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    -4 ≤ anisoHeisenbergCube α 2 u ζ := by
  have h := cubeBondSum_ge (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ -anisoBond α (u : V) (x : V) (y : V)) (m := -1) (ζ := ζ)
    fun c c' ↦ neg_one_le_neg_anisoBond hα0 hα1.le (norm_sphere_eq_one u) (norm_sphere_eq_one _)
      (norm_sphere_eq_one _)
  norm_num at h
  linarith

/-- **`|Φ_C| ≤ 4`** in the plane, the first alternative of condition (iv) of (17.18). -/
lemma abs_anisoHeisenbergCube_le_four (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    |anisoHeisenbergCube α 2 u ζ| ≤ 4 := by
  have h := cubeBondSum_le (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ -anisoBond α (u : V) (x : V) (y : V)) (M := 1) (ζ := ζ)
    fun c c' ↦ neg_anisoBond_le_one hα0 hα1.le (norm_sphere_eq_one u) (norm_sphere_eq_one _)
      (norm_sphere_eq_one _)
  norm_num at h
  rw [abs_le]
  exact ⟨neg_four_le_anisoHeisenbergCube hα0 hα1 ζ, h⟩

lemma anisoHeisenbergCube_const_eq_neg_four (x : sphere (0 : V) 1)
    (hx : (x : V) = (u : V) ∨ (x : V) = -(u : V)) :
    anisoHeisenbergCube α 2 u (fun _ ↦ x) = -4 := by
  have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * (-1 : ℝ))) = -4 := by norm_num
  rw [← hval]
  refine (cubeBondSum_eq_iff_forall_adj (fun a b ↦
    neg_one_le_neg_anisoBond hα0 hα1.le (norm_sphere_eq_one u) (norm_sphere_eq_one _)
      (norm_sphere_eq_one _)) _).2 fun c c' _ ↦ ?_
  have hone : anisoBond α (u : V) (x : V) (x : V) = 1 := by
    refine (anisoBond_eq_one_iff hα0 hα1 (norm_sphere_eq_one u) (norm_sphere_eq_one x)
      (norm_sphere_eq_one x)).2 ?_
    rcases hx with h | h
    · exact Or.inl ⟨h, h⟩
    · exact Or.inr ⟨h, h⟩
  rw [hone]

/-- **Georgii's `m_Φ = -4`** for (18.33) in the plane. -/
theorem localGroundEnergy_anisoHeisenbergCube [Nontrivial V] :
    localGroundEnergy (anisoHeisenbergCube α 2 u) (sphereProb V) = -4 :=
  localGroundEnergy_eq_of_isOpenPosMeasure continuous_anisoHeisenbergCube
    (neg_four_le_anisoHeisenbergCube hα0 hα1) (ζ₀ := fun _ ↦ u)
    (anisoHeisenbergCube_const_eq_neg_four hα0 hα1 u (Or.inl rfl))


end Anisotropy

/-! ### Georgii's polar caps and the partition `{G_+, G_-}` -/

/-- The two signs of Georgii's polar caps `U_±`. -/
def anisoSign (n : Fin 2) : ℝ := ![1, -1] n

@[simp] lemma anisoSign_zero : anisoSign 0 = 1 := rfl

@[simp] lemma anisoSign_one : anisoSign 1 = -1 := rfl

lemma anisoSign_eq_neg_of_ne {m n : Fin 2} (h : m ≠ n) : anisoSign m = -anisoSign n := by
  fin_cases m <;> fin_cases n <;> first | exact absurd rfl h | simp [anisoSign]

/-- **Georgii's `G_± = U_±^C`** for (18.33): the cube configurations all of whose spins lie in
the polar cap `U_± = {x ∈ E : ±⟪x, u⟫ ≥ 1 - δ}`. -/
def anisoG (δ : ℝ) (u : sphere (0 : V) 1) (n : Fin 2) :
    Set ((Fin 2 → Fin 2) → sphere (0 : V) 1) :=
  {ζ | ∀ c, 1 - δ ≤ anisoSign n * ⟪(ζ c : V), (u : V)⟫}

variable {δ : ℝ}

lemma mem_anisoG {n : Fin 2} {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1} :
    ζ ∈ anisoG δ u n ↔ ∀ c, 1 - δ ≤ anisoSign n * ⟪(ζ c : V), (u : V)⟫ := Iff.rfl

lemma continuous_inner_apply (c : Fin 2 → Fin 2) :
    Continuous fun ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 ↦ ⟪(ζ c : V), (u : V)⟫ :=
  (continuous_subtype_val.comp (continuous_apply c)).inner continuous_const

lemma measurableSet_anisoG (n : Fin 2) : MeasurableSet (anisoG δ u n) := by
  have h : anisoG δ u n
      = ⋂ c, {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 |
        1 - δ ≤ anisoSign n * ⟪(ζ c : V), (u : V)⟫} := by
    ext ζ
    simp [anisoG, Set.mem_iInter]
  rw [h]
  refine MeasurableSet.iInter fun c ↦ measurableSet_le measurable_const ?_
  exact (continuous_const.mul (continuous_inner_apply c)).measurable

lemma isRSymmetric_anisoG (n : Fin 2) :
    IsRSymmetric (sphere (0 : V) 1) (anisoG δ u n) := by
  intro k
  ext ζ
  simp only [Set.mem_preimage, mem_anisoG, cubeRefl_apply]
  exact ⟨fun h c ↦ by simpa [cubeSiteRefl_cubeSiteRefl] using h (cubeSiteRefl k c),
    fun h c ↦ h _⟩

/-- **Georgii's stability of `{G_+, G_-}`**: the two polar caps are disjoint when `δ < 1`, so
already a single corner of a face separates `G_+` from `G_-`. -/
theorem pairwise_disjoint_faceRestrict_anisoG (hδ1 : δ < 1) (k : Fin 2) (a : Fin 2) :
    Pairwise fun m n ↦ Disjoint (faceRestrict (sphere (0 : V) 1) k a '' anisoG δ u m)
      (faceRestrict (sphere (0 : V) 1) k a '' anisoG δ u n) := by
  intro m n hmn
  rw [Set.disjoint_left]
  rintro f ⟨ζ, hζ, rfl⟩ ⟨ξ, hξ, hfe⟩
  have hcorner : ζ (fun _ ↦ a) = ξ (fun _ ↦ a) :=
    (congrFun hfe (⟨fun _ ↦ a, rfl⟩ : {c : Fin 2 → Fin 2 // c k = a})).symm
  have h1 := hζ (fun _ ↦ a)
  have h2 := hξ (fun _ ↦ a)
  rw [← hcorner] at h2
  rw [anisoSign_eq_neg_of_ne hmn] at h1
  fin_cases n <;> simp only [anisoSign_zero, anisoSign_one] at h1 h2 <;> linarith


/-! ### Georgii's `G_ε(Φ) ⊆ G_+ ∪ G_-` for `0 < ε < (1 - α)δ` -/

section Estimate

variable (hα0 : 0 ≤ α) (hα1 : α < 1)

include hα0 hα1

/-- **The key step of Georgii's "straightforward computation"**: a bond of energy within `ε` of
the minimum has `⟪x, u⟫⟪y, u⟫ > 1 - δ`, because the anisotropy `1 - α` converts the energy gap
into a gap for the polar components. -/
lemma one_sub_lt_inner_mul {ε : ℝ} (hε : ε < (1 - α) * δ) {x y : V}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (h : 1 - ε ≤ anisoBond α (u : V) x y) :
    1 - δ < ⟪x, (u : V)⟫ * ⟪y, (u : V)⟫ := by
  have hxy : ⟪x, y⟫ ≤ 1 := real_inner_le_one_of_norm_eq_one hx hy
  have h1a : (0 : ℝ) < 1 - α := by linarith
  rw [anisoBond] at h
  nlinarith [mul_le_mul_of_nonneg_left hxy hα0]

omit hα0 hα1 in
lemma one_sub_lt_abs_of_mul {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hδ : δ ≤ 1)
    (h : 1 - δ < a * b) : 1 - δ < |a| ∧ 0 < a * b := by
  refine ⟨?_, by linarith⟩
  calc 1 - δ < a * b := h
    _ ≤ |a * b| := le_abs_self _
    _ = |a| * |b| := abs_mul _ _
    _ ≤ |a| * 1 := by gcongr
    _ = |a| := mul_one _

omit hα0 hα1 in
/-- The sign bookkeeping in Georgii's computation: if the four polar components of the corners of
the square have pairwise products `> 1 - δ` along the four edges, then they all have the same
sign and all have modulus `> 1 - δ`. -/
lemma sign_of_four (hδ1 : δ ≤ 1) {A B C D : ℝ} (hA : |A| ≤ 1) (hB : |B| ≤ 1) (hC : |C| ≤ 1)
    (hD : |D| ≤ 1) (hAB : 1 - δ < A * B) (hCD : 1 - δ < C * D) (hAC : 1 - δ < A * C)
    (hBD : 1 - δ < B * D) :
    (1 - δ ≤ A ∧ 1 - δ ≤ B ∧ 1 - δ ≤ C ∧ 1 - δ ≤ D) ∨
      (1 - δ ≤ -A ∧ 1 - δ ≤ -B ∧ 1 - δ ≤ -C ∧ 1 - δ ≤ -D) := by
  obtain ⟨hA', hABpos⟩ := one_sub_lt_abs_of_mul hA hB hδ1 hAB
  obtain ⟨hB', -⟩ := one_sub_lt_abs_of_mul hB hA hδ1 (by rw [mul_comm] at hAB; exact hAB)
  obtain ⟨hC', -⟩ := one_sub_lt_abs_of_mul hC hA hδ1 (by rw [mul_comm] at hAC; exact hAC)
  obtain ⟨hD', -⟩ := one_sub_lt_abs_of_mul hD hC hδ1 (by rw [mul_comm] at hCD; exact hCD)
  obtain ⟨-, hACpos⟩ := one_sub_lt_abs_of_mul hA hC hδ1 hAC
  obtain ⟨-, hBDpos⟩ := one_sub_lt_abs_of_mul hB hD hδ1 hBD
  have hAne : A ≠ 0 := fun h0 ↦ by rw [h0, zero_mul] at hABpos; exact absurd hABpos (lt_irrefl 0)
  rcases lt_or_gt_of_ne hAne with hAneg | hApos
  · refine Or.inr ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_of_neg hAneg] at hA'; linarith
    · have hBneg : B < 0 := by nlinarith
      rw [abs_of_neg hBneg] at hB'; linarith
    · have hCneg : C < 0 := by nlinarith
      rw [abs_of_neg hCneg] at hC'; linarith
    · have hCneg : C < 0 := by nlinarith
      have hDneg : D < 0 := by nlinarith
      rw [abs_of_neg hDneg] at hD'; linarith
  · refine Or.inl ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_of_pos hApos] at hA'; linarith
    · have hBpos : 0 < B := by nlinarith
      rw [abs_of_pos hBpos] at hB'; linarith
    · have hCpos : 0 < C := by nlinarith
      rw [abs_of_pos hCpos] at hC'; linarith
    · have hBpos : 0 < B := by nlinarith
      have hDpos : 0 < D := by nlinarith
      rw [abs_of_pos hDpos] at hD'; linarith

/-- **Georgii's `G_ε(Φ) ⊆ G_+ ∪ G_-` whenever `0 < ε < (1 - α)δ`.** -/
theorem localGroundStates_subset_anisoG [Nontrivial V] (hδ1 : δ ≤ 1) {ε : ℝ}
    (hε : ε < (1 - α) * δ) :
    localGroundStates (anisoHeisenbergCube α 2 u) (sphereProb V) ε
      ⊆ anisoG δ u 0 ∪ anisoG δ u 1 := by
  intro ζ hζ
  rw [mem_localGroundStates, localGroundEnergy_anisoHeisenbergCube hα0 hα1] at hζ
  have hζ' : cubeBondSum 2
      (fun x y : sphere (0 : V) 1 ↦ -anisoBond α (u : V) (x : V) (y : V)) ζ ≤ -4 + ε := hζ
  rw [cubeBondSum_two (fun x y ↦ by rw [anisoBond_comm])] at hζ'
  have hb : ∀ x y : sphere (0 : V) 1, (-1 : ℝ) ≤ -anisoBond α (u : V) (x : V) (y : V) :=
    fun x y ↦ neg_one_le_neg_anisoBond hα0 hα1.le (norm_sphere_eq_one u) (norm_sphere_eq_one x)
      (norm_sphere_eq_one y)
  have h1 := hb (ζ (sqCorner 0 0)) (ζ (sqCorner 1 0))
  have h2 := hb (ζ (sqCorner 0 1)) (ζ (sqCorner 1 1))
  have h3 := hb (ζ (sqCorner 0 0)) (ζ (sqCorner 0 1))
  have h4 := hb (ζ (sqCorner 1 0)) (ζ (sqCorner 1 1))
  have habs : ∀ c : Fin 2 → Fin 2, |⟪(ζ c : V), (u : V)⟫| ≤ 1 := fun c ↦
    abs_real_inner_le_one (norm_sphere_eq_one _) (norm_sphere_eq_one u)
  have key := sign_of_four hδ1 (habs (sqCorner 0 0)) (habs (sqCorner 1 0))
    (habs (sqCorner 0 1)) (habs (sqCorner 1 1))
    (one_sub_lt_inner_mul hα0 hα1 hε (norm_sphere_eq_one _) (norm_sphere_eq_one _) (by linarith))
    (one_sub_lt_inner_mul hα0 hα1 hε (norm_sphere_eq_one _) (norm_sphere_eq_one _) (by linarith))
    (one_sub_lt_inner_mul hα0 hα1 hε (norm_sphere_eq_one _) (norm_sphere_eq_one _) (by linarith))
    (one_sub_lt_inner_mul hα0 hα1 hε (norm_sphere_eq_one _) (norm_sphere_eq_one _) (by linarith))
  rcases key with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
  · refine Or.inl fun c ↦ ?_
    rw [anisoSign_zero, one_mul]
    rcases sqCorner_surjective c with rfl | rfl | rfl | rfl <;> assumption
  · refine Or.inr fun c ↦ ?_
    rw [anisoSign_one]
    rcases sqCorner_surjective c with rfl | rfl | rfl | rfl <;> linarith

end Estimate


/-! ### Georgii's reflection of the first coordinate -/

variable (u) in
/-- **Georgii's "reflection of the first coordinate of all spins"**: the reflection of `V` in the
hyperplane `u^⊥` orthogonal to the anisotropy direction.  It is a linear isometry, so it
preserves the surface measure of the sphere. -/
def anisoRefl : V ≃ₗᵢ[ℝ] V := Submodule.reflection ((ℝ ∙ (u : V))ᗮ)

lemma anisoRefl_apply (v : V) : anisoRefl u v = v - (2 * ⟪(u : V), v⟫) • (u : V) := by
  rw [anisoRefl, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
    norm_sphere_eq_one u]
  push_cast
  module

lemma inner_anisoRefl_left (v : V) : ⟪anisoRefl u v, (u : V)⟫ = -⟪v, (u : V)⟫ := by
  rw [anisoRefl_apply, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    norm_sphere_eq_one u, real_inner_comm (u : V) v]
  ring

lemma anisoRefl_anisoRefl (v : V) : anisoRefl u (anisoRefl u v) = v :=
  Submodule.reflection_reflection _ v

lemma anisoBond_anisoRefl (v w : V) :
    anisoBond α (u : V) (anisoRefl u v) (anisoRefl u w) = anisoBond α (u : V) v w := by
  rw [anisoBond, anisoBond, inner_anisoRefl_left, inner_anisoRefl_left,
    (anisoRefl u).inner_map_map]
  ring

variable (u) in
/-- Georgii's reflection as an element of the transformation group `T_{C,λ}`: a pure spin
transformation (18.21). -/
def anisoReflTransform : CubeTransformation (sphere (0 : V) 1) 2 :=
  CubeTransformation.pureSpin fun _ ↦ (anisoRefl u).sphereMeasurableEquiv

@[simp] lemma coe_onCube_anisoReflTransform (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1)
    (c : Fin 2 → Fin 2) :
    (((anisoReflTransform u).onCube.toFun ζ c : sphere (0 : V) 1) : V)
      = anisoRefl u (ζ c : V) := by
  rw [anisoReflTransform, CubeTransformation.pureSpin_onCube_toFun_apply]
  rfl

lemma measurePreserving_anisoRefl_sphereProb :
    MeasurePreserving (anisoRefl u).sphereMeasurableEquiv (sphereProb V) (sphereProb V) :=
  MeasurePreserving.probNormalize
    ((anisoRefl u).measurePreserving_sphere_toSphere_volume)

lemma onCube_anisoReflTransform_involutive (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    (anisoReflTransform u).onCube.toFun ((anisoReflTransform u).onCube.toFun ζ) = ζ := by
  funext c
  refine Subtype.ext ?_
  rw [coe_onCube_anisoReflTransform, coe_onCube_anisoReflTransform, anisoRefl_anisoRefl]

/-- **Georgii's "the reflection … maps `G_+` onto `G_-`, and vice versa".** -/
lemma image_onCube_anisoReflTransform {m n : Fin 2} (hmn : m ≠ n) :
    (anisoReflTransform u).onCube.toFun '' anisoG δ u m = anisoG δ u n := by
  have key : ∀ (p q : Fin 2), p ≠ q → ∀ ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1,
      ζ ∈ anisoG δ u p → (anisoReflTransform u).onCube.toFun ζ ∈ anisoG δ u q := by
    intro p q hpq ζ hζ c
    have h := hζ c
    rw [coe_onCube_anisoReflTransform, inner_anisoRefl_left, anisoSign_eq_neg_of_ne hpq] at *
    linarith [h]
  refine Set.Subset.antisymm ?_ fun ξ hξ ↦ ⟨(anisoReflTransform u).onCube.toFun ξ,
    key n m (Ne.symm hmn) ξ hξ, onCube_anisoReflTransform_involutive ξ⟩
  rintro _ ⟨ζ, hζ, rfl⟩
  exact key m n hmn ζ hζ

section Symmetry

variable [Nontrivial V] (hα0 : 0 ≤ α) (hα1 : α < 1)

include hα0 hα1

theorem isSymmetry_anisoReflTransform :
    (anisoReflTransform u).IsSymmetry (anisoHeisenbergCube α 2 u) (sphereProb V) :=
  CubeTransformation.IsSymmetry.of_apply_onCube anisoHeisenbergCube_cubeRefl
    (fun _ ↦ measurePreserving_anisoRefl_sphereProb)
    fun ζ ↦ cubeBondSum_onCube _ (fun c c' _ x y ↦ by
      change -anisoBond α (u : V) (anisoRefl u (x : V)) (anisoRefl u (y : V))
        = -anisoBond α (u : V) (x : V) (y : V)
      rw [anisoBond_anisoRefl]) ζ

theorem isPhiSymmetric_anisoG :
    IsPhiSymmetric (anisoHeisenbergCube α 2 u) (sphereProb V) (anisoG δ u) :=
  isPhiSymmetric_of_ne anisoHeisenbergCube_cubeRefl fun m n hmn ↦
    ⟨anisoReflTransform u, isSymmetry_anisoReflTransform hα0 hα1,
      image_onCube_anisoReflTransform hmn⟩

end Symmetry


/-! ### Georgii 18.3.6: the conclusion -/

section Conclusion

variable [Nontrivial V] (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)

include hα0 hα1 hδ0 hδ1

/-- Georgii's admissible range for (18.33) is `0 < ε < (1 - α)δ`; we fix the midpoint. -/
lemma anisoEps_pos : 0 < (1 - α) * δ / 2 := by
  have : 0 < 1 - α := by linarith
  positivity

lemma anisoEps_lt : (1 - α) * δ / 2 < (1 - α) * δ := by
  have : 0 < (1 - α) * δ := by
    have : 0 < 1 - α := by linarith
    positivity
  linarith

lemma localGroundStates_subset_iUnion_anisoG :
    localGroundStates (anisoHeisenbergCube α 2 u) (sphereProb V) ((1 - α) * δ / 2)
      ⊆ ⋃ n, anisoG δ u n :=
  (localGroundStates_subset_anisoG hα0 hα1 hδ1.le (anisoEps_lt hα0 hα1 hδ0 hδ1)).trans
    (Set.union_subset (Set.subset_iUnion _ 0) (Set.subset_iUnion _ 1))

/-- **Georgii's "`{G_+, G_-}` is a stable partition of the local ground states"** for (18.33). -/
theorem isPStablePartition_anisoG :
    IsPStablePartition (anisoHeisenbergCube α 2 u) (sphereProb V) Set.univ (anisoG δ u) where
  exists_localGroundStates_subset :=
    ⟨(1 - α) * δ / 2, anisoEps_pos hα0 hα1 hδ0 hδ1,
      localGroundStates_subset_iUnion_anisoG hα0 hα1 hδ0 hδ1⟩
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_anisoG hδ1 k a

/-- **Georgii 18.3.6, the anisotropic Heisenberg ferromagnet (18.33).**  *Theorem (18.25) shows
that `|ex 𝒢_Θ(βΦ)| ≥ 2` when `β` is large enough.*

The local ground states are the two constant configurations `±u`
(`localGroundEnergy_anisoHeisenbergCube`), and for `0 < ε < (1 - α)δ` the local `ε`-ground states
lie in `G_+ ∪ G_-` (`localGroundStates_subset_anisoG`).  Both members are `r`-symmetric, so
Georgii's shift group `Θ̃` is all of `Θ`. -/
theorem eventually_two_le_encard_extremePoints_anisoHeisenberg :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * anisoHeisenbergCube α 2 u ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * anisoHeisenbergCube α 2 u ζ),
      (2 : ℕ∞) ≤ ((invariantG (cubeGibbsSpec (sphere (0 : V) 1)
        (fun ζ ↦ β * anisoHeisenbergCube α 2 u ζ) (sphereProb V) hφβ hMβ)
        (shiftGroup (Fin 2 → ℤ) (sphere (0 : V) 1))).extremePoints ℝ≥0∞).encard :=
  eventually_le_encard_extremePoints (E := sphere (0 : V) 1)
    (φ := anisoHeisenbergCube α 2 u) (ν := sphereProb V) (G := anisoG δ u)
    measurable_anisoHeisenbergCube (neg_four_le_anisoHeisenbergCube hα0 hα1)
    anisoHeisenbergCube_cubeRefl
    (isCubeConfining_univ ⟨4, abs_anisoHeisenbergCube_le_four hα0 hα1⟩)
    (isPStablePartition_anisoG hα0 hα1 hδ0 hδ1) (isPhiSymmetric_anisoG hα0 hα1)
    measurableSet_anisoG isRSymmetric_anisoG (anisoEps_pos hα0 hα1 hδ0 hδ1)
    (localGroundStates_subset_iUnion_anisoG hα0 hα1 hδ0 hδ1)

open Peierls in
/-- **Georgii 18.3.6**, the two Gibbs measures themselves: for `β` large enough there are two
mutually singular shift-invariant Gibbs measures for `βΦ`, `μ_±` carried by the configurations
whose `G_±`-cubes percolate in an ocean, and the reflection of the first coordinate of all spins
exchanges them. -/
theorem eventually_exists_anisoHeisenberg_gibbsMeasure_pair :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * anisoHeisenbergCube α 2 u ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * anisoHeisenbergCube α 2 u ζ),
      ∃ μ : Fin 2 → Measure ((Fin 2 → ℤ) → sphere (0 : V) 1),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec (sphere (0 : V) 1)
          (fun ζ ↦ β * anisoHeisenbergCube α 2 u ζ) (sphereProb V) hφβ hMβ) (μ n)) ∧
        (μ 0).MutuallySingular (μ 1) ∧
        (∀ n, μ n {ω | (latticeOceanPart (sphere (0 : V) 1) (anisoG δ u n) ω).Nonempty} = 1) ∧
        (∀ (n : Fin 2) (a : Fin 2 → ℤ),
          MeasurePreserving (shift (sphere (0 : V) 1) a).toFun (μ n) (μ n)) ∧
        (μ 0).map ((anisoReflTransform u).onLattice (sphere (0 : V) 1)).toFun = μ 1 ∧
        (μ 1).map ((anisoReflTransform u).onLattice (sphere (0 : V) 1)).toFun = μ 0 := by
  filter_upwards [eventually_exists_gibbsMeasure_family_shift (E := sphere (0 : V) 1)
    (φ := anisoHeisenbergCube α 2 u) (ν := sphereProb V) (G := anisoG δ u)
    measurable_anisoHeisenbergCube (neg_four_le_anisoHeisenbergCube hα0 hα1)
    anisoHeisenbergCube_cubeRefl
    (isCubeConfining_univ ⟨4, abs_anisoHeisenbergCube_le_four hα0 hα1⟩)
    (isPStablePartition_anisoG hα0 hα1 hδ0 hδ1) (isPhiSymmetric_anisoG hα0 hα1)
    measurableSet_anisoG (anisoEps_pos hα0 hα1 hδ0 hδ1)
    (localGroundStates_subset_iUnion_anisoG hα0 hα1 hδ0 hδ1)] with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, h4, -, h6, -, h8, -⟩ := hβ hφβ hMβ
  have hrefl : (anisoReflTransform u).IsSymmetry
      (fun ζ ↦ β * anisoHeisenbergCube α 2 u ζ) (sphereProb V) :=
    (isSymmetry_anisoReflTransform hα0 hα1).const_mul anisoHeisenbergCube_cubeRefl β
  exact ⟨ρ, h1, h2, h3 (by decide), h4,
    fun n a ↦ h6 n a ((isRSymmetric_anisoG n).preimage_tauPow _),
    h8 0 1 _ hrefl (image_onCube_anisoReflTransform (by decide)),
    h8 1 0 _ hrefl (image_onCube_anisoReflTransform (by decide))⟩

end Conclusion

end MeasureTheory.GibbsMeasure

end

end
