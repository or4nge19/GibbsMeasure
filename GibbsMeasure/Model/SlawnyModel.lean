/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.AnisotropicAntiferroOceans

/-!
# Georgii 18.3.10: Slawny's `□`-model

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.10.  This is the one example of §18.3
which needs **three** dimensions: `S = ℤ³`, `E = {-1, 1}` with counting measure, and the
`C`-potential is **(18.39)**

`Φ_C = -∑_{F ⊆ C} ∏_{i ∈ F} σ_i`,

the sum extending over the six faces `F` of the unit cube `C = {0,1}³`.

## What is and is not formalised

Everything in Georgii's paragraph up to the invocation of Theorem (18.25) is proved here:

* `slawnyCube` is (18.39), `slawnyCube_eq_neg_six_iff` is his "`Φ_C(ω)` is minimal if and only if
  on each face `F` of `C` there exists an even number of sites `i ∈ F` with `ω_i = 1`", and
  `localGroundEnergy_slawnyCube` is `m_Φ = -6`;
* `slawnyG` are his `G_1 = {ω : ω_{(u,v,0)} = ω_{(u,v,1)} for all u, v}` and
  `G_2 = {ω : ω_{(u,v,0)} ≠ ω_{(u,v,1)} for all u, v}`, and
  `slawnyCube_eq_neg_six_subset` is his "the latter property implies that if
  `ω_{(u,v,0)} = ω_{(u,v,1)} for some choice of u, v then the same identity holds for all
  u, v`", that is `G_0(Φ) ⊆ G_1 ∪ G_2`;
* `isPStablePartition_slawnyG` is his "**the partition `{G_1, G_2}` is `P`-stable**, despite the
  fact that `σ_F(G_1) = σ_F(G_2)` when `F` is the top face or bottom face of `C`" — the point of
  Comment (18.26)(2), that in `d > 2` only the four `P`-faces enter (18.23)(a)(ii); and
* `slawnyLayerFlip`, `isPhiSymmetric_slawnyG` are his "`G_1` and `G_2` are related to each other
  by the mapping `ω ↦ ((-1)^{i_3} ω_i)` which belongs to `I_{C,λ}(Φ)`".

**The conclusion is not formalised.**  Theorem (18.25) and the low energy ocean machinery of
§18.1 on which it rests — `latticeOceanPart` of `GibbsMeasure/Model/LowEnergyOceans.lean`, the
crossing bound of `GibbsMeasure/Model/PlanarCrossing.lean`, `GZero_nonempty` and
`exists_gibbsMeasure_family` — are formalised in the tree **only for `d = 2`**, where the plane
`P` of (18.5) is the whole lattice: `latticeOceanPart` takes `ω : (Fin 2 → ℤ) → E`, and
`exists_gibbsMeasure_family` takes a cube interaction on `(Fin 2 → Fin 2) → E`.  Georgii's §18.1
is written for a general `d` with the plane `P`, and the `P`-stability of (18.23) is precisely
what is needed to run the argument in the plane `P ⊂ ℤ³`; the missing input is therefore the
`d`-dimensional version of §18.1, not anything about this model.  Everything in this file is
stated for the cube of `ℤ³` and for `P = {0, 1}`, so that it plugs into that version unchanged.
Propositions (18.40) and (18.41) — the continuum of extremal Gibbs measures obtained from the
uncountable symmetry group `τ_η`, `η ∈ {-1,1}^ℤ` — depend on that conclusion and are likewise
not formalised.

## Main results

* `cubeFace`, `faceProd`, `slawnyCube` — the six faces of `C`, their spin products and (18.39).
* `faceProd_eq_one_iff_*` — each face product is `±1`, and `Φ_C ≥ -6` with equality exactly when
  all six are `+1`.
* `slawnyVert`, `mem_slawnyG_iff` — the four vertical pairs of `C` and the description of
  `G_1, G_2` by them.
* `isPStablePartition_slawnyG`, `isPhiSymmetric_slawnyG`, `isCubeConfining_slawnyCube` — the
  hypotheses of Theorem (18.25) for `P = {0, 1} ⊆ Fin 3`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The faces of the unit cube -/

variable {d : ℕ}

variable (d) in
/-- **The face `F = {i ∈ C : i_k = a}` of the unit cube.**  In `d = 3` these are Georgii's six
faces of `C`; the `P`-faces of (18.23) are those with `k ∈ P`. -/
def cubeFace (k : Fin d) (a : Fin 2) : Finset (Fin d → Fin 2) :=
  Finset.univ.filter fun c ↦ c k = a

/-- **Georgii's `∏_{i ∈ F} σ_i`** over the face `F = {i : i_k = a}`. -/
def faceProd (k : Fin d) (a : Fin 2) (ζ : (Fin d → Fin 2) → Bool) : ℝ :=
  ∏ c ∈ cubeFace d k a, spin (ζ c)

variable (d) in
/-- **Georgii (18.39)**: the `C`-potential of Slawny's `□`-model, `Φ_C = -∑_{F ⊆ C} ∏_{i∈F} σ_i`,
the sum extending over the `2d` faces of `C` (the six faces of the cube when `d = 3`). -/
def slawnyCube : ((Fin d → Fin 2) → Bool) → ℝ := fun ζ ↦ -∑ k, ∑ a, faceProd k a ζ

lemma measurable_slawnyCube : Measurable (slawnyCube d) := Measurable.of_discrete

/-- A face product is `±1`. -/
lemma faceProd_eq_one_or (k : Fin d) (a : Fin 2) (ζ : (Fin d → Fin 2) → Bool) :
    faceProd k a ζ = 1 ∨ faceProd k a ζ = -1 := by
  refine Finset.prod_induction _ (fun x ↦ x = 1 ∨ x = -1) (fun x y hx hy ↦ ?_) (Or.inl rfl)
    fun c _ ↦ ?_
  · rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> norm_num
  · cases ζ c <;> simp [spin]

lemma faceProd_le_one (k : Fin d) (a : Fin 2) (ζ : (Fin d → Fin 2) → Bool) :
    faceProd k a ζ ≤ 1 := by
  rcases faceProd_eq_one_or k a ζ with h | h <;> rw [h] <;> norm_num

lemma fin_three_cases (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide

/-- A reflection of the cube maps the face `{c : c_l = a}` onto itself when `l ≠ k`, and onto the
opposite face when `l = k`. -/
lemma faceProd_cubeRefl (k l : Fin d) (a : Fin 2) (ζ : (Fin d → Fin 2) → Bool) :
    faceProd l a (cubeRefl Bool k ζ) = faceProd l (if l = k then a + 1 else a) ζ := by
  refine Finset.prod_equiv (cubeSiteRefl k) (fun c ↦ ?_) (fun c _ ↦ by rw [cubeRefl_apply])
  simp only [cubeFace, Finset.mem_filter, Finset.mem_univ, true_and, cubeSiteRefl_apply,
    Function.update_apply]
  by_cases hlk : l = k
  · subst hlk
    simp only [fin_two_rev_eq_add_one]
    constructor
    · rintro rfl; rfl
    · intro h
      have := congrArg (· + (1 : Fin 2)) h
      simpa [add_assoc, fin_two_add_self] using this
  · simp [hlk]

/-- **Condition (iii) of Georgii (17.18)** for (18.39): a reflection of the cube permutes its
faces. -/
lemma slawnyCube_cubeRefl (k : Fin d) (ζ : (Fin d → Fin 2) → Bool) :
    slawnyCube d (cubeRefl Bool k ζ) = slawnyCube d ζ := by
  simp only [slawnyCube, faceProd_cubeRefl]
  congr 1
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  by_cases hlk : l = k
  · subst hlk
    simp only [if_pos rfl]
    exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 2)) _ _ fun a ↦ rfl
  · simp only [if_neg hlk]

/-- **Georgii's `Φ_C ≥ -2d`**: the cube has `2d` faces and each face product is at most `1`. -/
lemma le_slawnyCube (ζ : (Fin d → Fin 2) → Bool) : -(2 * d : ℝ) ≤ slawnyCube d ζ := by
  have h : ∑ k : Fin d, ∑ a : Fin 2, faceProd k a ζ ≤ ∑ _k : Fin d, ∑ _a : Fin 2, (1 : ℝ) :=
    Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun a _ ↦ faceProd_le_one k a ζ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  rw [slawnyCube]
  push_cast at h ⊢
  linarith

/-- **Georgii's "`Φ_C(ω)` is minimal if and only if on each face `F` of `C` there exists an even
number of sites `i ∈ F` with `ω_i = 1`"**: the minimum `-2d` is attained exactly when every face
product is `+1`. -/
theorem slawnyCube_eq_neg_iff (ζ : (Fin d → Fin 2) → Bool) :
    slawnyCube d ζ = -(2 * d : ℝ) ↔ ∀ k a, faceProd k a ζ = 1 := by
  have hle : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      ∑ a : Fin 2, faceProd k a ζ ≤ ∑ _a : Fin 2, (1 : ℝ) :=
    fun k _ ↦ Finset.sum_le_sum fun a _ ↦ faceProd_le_one k a ζ
  constructor
  · intro heq k a
    have hsum : ∑ k : Fin d, ∑ a : Fin 2, faceProd k a ζ
        = ∑ _k : Fin d, ∑ _a : Fin 2, (1 : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [slawnyCube] at heq
      push_cast
      linarith
    have h1 := (Finset.sum_eq_sum_iff_of_le hle).1 hsum k (Finset.mem_univ k)
    exact (Finset.sum_eq_sum_iff_of_le fun a _ ↦ faceProd_le_one k a ζ).1 h1 a
      (Finset.mem_univ a)
  · intro h
    rw [slawnyCube]
    have hsum : ∑ k : Fin d, ∑ a : Fin 2, faceProd k a ζ = (2 * d : ℝ) := by
      simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast
      ring
    rw [hsum]

/-! ### The unit cube of `ℤ³` -/

/-- The corner `(x, y, z)` of the unit cube of `ℤ³`. -/
abbrev cb (x y z : Fin 2) : Fin 3 → Fin 2 := ![x, y, z]

lemma cb_eq (c : Fin 3 → Fin 2) : c = cb (c 0) (c 1) (c 2) := by
  funext l; fin_cases l <;> rfl

@[simp] lemma cubeSiteRefl_two_cb (x y z : Fin 2) :
    cubeSiteRefl 2 (cb x y z) = cb x y (z + 1) := by
  funext l; fin_cases l <;> simp [cubeSiteRefl_apply, fin_two_rev_eq_add_one]

/-- The product of four spins is `+1` exactly when the four Booleans have even parity. -/
lemma spin_four_eq_one_iff (p q r s : Bool) :
    spin p * spin q * spin r * spin s = 1 ↔ xor (xor p q) (xor r s) = false := by
  cases p <;> cases q <;> cases r <;> cases s <;> norm_num [spin]

/-- The product over a face, computed from an explicit description of its four corners. -/
lemma faceProd_eq_of_face {k : Fin 3} {a : Fin 2} {c1 c2 c3 c4 : Fin 3 → Fin 2}
    (h : cubeFace 3 k a = {c1, c2, c3, c4}) (h1 : c1 ∉ ({c2, c3, c4} : Finset (Fin 3 → Fin 2)))
    (h2 : c2 ∉ ({c3, c4} : Finset (Fin 3 → Fin 2)))
    (h3 : c3 ∉ ({c4} : Finset (Fin 3 → Fin 2))) (ζ : (Fin 3 → Fin 2) → Bool) :
    faceProd k a ζ = spin (ζ c1) * spin (ζ c2) * spin (ζ c3) * spin (ζ c4) := by
  rw [faceProd, h, Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_insert h3,
    Finset.prod_singleton]
  ring

lemma faceProd_zero (a : Fin 2) (ζ : (Fin 3 → Fin 2) → Bool) :
    faceProd 0 a ζ
      = spin (ζ (cb a 0 0)) * spin (ζ (cb a 0 1)) * spin (ζ (cb a 1 0)) * spin (ζ (cb a 1 1)) := by
  rcases fin_two_eq_zero_or_one a with rfl | rfl
  · exact faceProd_eq_of_face (by decide) (by decide) (by decide) (by decide) ζ
  · exact faceProd_eq_of_face (by decide) (by decide) (by decide) (by decide) ζ

lemma faceProd_one (a : Fin 2) (ζ : (Fin 3 → Fin 2) → Bool) :
    faceProd 1 a ζ
      = spin (ζ (cb 0 a 0)) * spin (ζ (cb 0 a 1)) * spin (ζ (cb 1 a 0)) * spin (ζ (cb 1 a 1)) := by
  rcases fin_two_eq_zero_or_one a with rfl | rfl
  · exact faceProd_eq_of_face (by decide) (by decide) (by decide) (by decide) ζ
  · exact faceProd_eq_of_face (by decide) (by decide) (by decide) (by decide) ζ

lemma faceProd_two (a : Fin 2) (ζ : (Fin 3 → Fin 2) → Bool) :
    faceProd 2 a ζ
      = spin (ζ (cb 0 0 a)) * spin (ζ (cb 0 1 a)) * spin (ζ (cb 1 0 a)) * spin (ζ (cb 1 1 a)) := by
  rcases fin_two_eq_zero_or_one a with rfl | rfl
  · exact faceProd_eq_of_face (by decide) (by decide) (by decide) (by decide) ζ
  · exact faceProd_eq_of_face (by decide) (by decide) (by decide) (by decide) ζ

/-! ### Georgii's two classes `G_1` and `G_2` -/

/-- The parity of the vertical pair of `C` over `(x, y)`: `false` when
`ω_{(x,y,0)} = ω_{(x,y,1)}`. -/
def slawnyVert (ζ : (Fin 3 → Fin 2) → Bool) (x y : Fin 2) : Bool :=
  xor (ζ (cb x y 0)) (ζ (cb x y 1))

/-- **Georgii's `G_1` and `G_2`**: `G_1 = {ω : ω_{(u,v,0)} = ω_{(u,v,1)}` for all `u, v}` and
`G_2 = {ω : ω_{(u,v,0)} ≠ ω_{(u,v,1)}` for all `u, v}`. -/
def slawnyG (n : Fin 2) : Set ((Fin 3 → Fin 2) → Bool) :=
  {ζ | ∀ c, xor (ζ c) (ζ (cubeSiteRefl 2 c)) = ![false, true] n}

lemma measurableSet_slawnyG (n : Fin 2) : MeasurableSet (slawnyG n) :=
  MeasurableSet.of_discrete

/-- `G_1` and `G_2` are described by the four vertical pairs. -/
lemma mem_slawnyG_iff {n : Fin 2} {ζ : (Fin 3 → Fin 2) → Bool} :
    ζ ∈ slawnyG n ↔ ∀ x y, slawnyVert ζ x y = ![false, true] n := by
  constructor
  · intro h x y
    have hc := h (cb x y 0)
    rwa [cubeSiteRefl_two_cb, show (0 : Fin 2) + 1 = 1 from rfl] at hc
  · intro h c
    rw [cb_eq c, cubeSiteRefl_two_cb]
    rcases fin_two_eq_zero_or_one (c 2) with hz | hz <;> rw [hz]
    · exact h (c 0) (c 1)
    · rw [show (1 : Fin 2) + 1 = 0 from rfl, Bool.xor_comm]
      exact h (c 0) (c 1)


/-! ### `G_0(Φ) ⊆ G_1 ∪ G_2` -/

lemma xor_eq_false_iff (a b : Bool) : xor a b = false ↔ a = b := by revert a b; decide

/-- **Georgii's "if `ω_{(u,v,0)} = ω_{(u,v,1)}` for some choice of `u, v` then the same identity
holds for all `u, v`"**: the four side faces of `C` say that the parities of the four vertical
pairs agree in pairs, hence all agree. -/
theorem slawnyCube_eq_neg_six_subset {ζ : (Fin 3 → Fin 2) → Bool}
    (h : slawnyCube 3 ζ = -6) : ζ ∈ slawnyG 0 ∪ slawnyG 1 := by
  have h6 : (-(2 * (3 : ℕ) : ℝ)) = -6 := by norm_num
  have hall := (slawnyCube_eq_neg_iff ζ).1 (by rw [h6]; exact h)
  have hside0 : ∀ a : Fin 2, slawnyVert ζ a 0 = slawnyVert ζ a 1 := by
    intro a
    have hfa := hall 0 a
    rw [faceProd_zero, spin_four_eq_one_iff] at hfa
    exact (xor_eq_false_iff _ _).1 hfa
  have hside1 : ∀ b : Fin 2, slawnyVert ζ 0 b = slawnyVert ζ 1 b := by
    intro b
    have hfb := hall 1 b
    rw [faceProd_one, spin_four_eq_one_iff] at hfb
    exact (xor_eq_false_iff _ _).1 hfb
  have hconst : ∀ x y, slawnyVert ζ x y = slawnyVert ζ 0 0 := by
    intro x y
    rcases fin_two_eq_zero_or_one x with rfl | rfl <;>
      rcases fin_two_eq_zero_or_one y with rfl | rfl
    · rfl
    · exact (hside0 0).symm
    · exact (hside1 0).symm
    · rw [← hside0 1, ← hside1 0]
  by_cases hw : slawnyVert ζ 0 0 = true
  · exact Or.inr (mem_slawnyG_iff.2 fun x y ↦ by rw [hconst x y, hw]; rfl)
  · rw [Bool.not_eq_true] at hw
    exact Or.inl (mem_slawnyG_iff.2 fun x y ↦ by rw [hconst x y, hw]; rfl)

/-! ### `m_Φ = -6` and the local `ε`-ground states -/

/-- A ground state of (18.39): the constant configuration. -/
lemma slawnyCube_const (b : Bool) : slawnyCube 3 (fun _ ↦ b) = -6 := by
  have h6 : (-(2 * (3 : ℕ) : ℝ)) = -6 := by norm_num
  rw [← h6]
  refine (slawnyCube_eq_neg_iff _).2 fun k a ↦ ?_
  have hsq : spin b * spin b = 1 := by cases b <;> norm_num [spin]
  rcases fin_three_cases k with rfl | rfl | rfl
  · rw [faceProd_zero]; nlinarith [hsq]
  · rw [faceProd_one]; nlinarith [hsq]
  · rw [faceProd_two]; nlinarith [hsq]

/-- **Georgii's `m_Φ = -6`** for (18.39). -/
theorem localGroundEnergy_slawnyCube :
    localGroundEnergy (slawnyCube 3) uniformSpinMeasure = -6 := by
  have h6 : (-(2 * (3 : ℕ) : ℝ)) = -6 := by norm_num
  exact localGroundEnergy_eq uniformSpinMeasure_singleton_ne_zero
    (fun ζ ↦ by rw [← h6]; exact le_slawnyCube ζ) (ζ₀ := fun _ ↦ true) (slawnyCube_const true)

/-- **Georgii's (18.23)(a)(i) for (18.39)**: for `ε` small the local `ε`-ground states lie in
`G_1 ∪ G_2`. -/
theorem exists_localGroundStates_subset_slawnyG :
    ∃ ε > 0, localGroundStates (slawnyCube 3) uniformSpinMeasure ε ⊆ ⋃ n, slawnyG n := by
  have h6 : (-(2 * (3 : ℕ) : ℝ)) = -6 := by norm_num
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset
    (ν := uniformSpinMeasure) uniformSpinMeasure_singleton_ne_zero
    (m := -6) (fun ζ ↦ by rw [← h6]; exact le_slawnyCube ζ) (ζ₀ := fun _ ↦ true)
    (slawnyCube_const true)
  refine ⟨ε, hε, fun ζ hζ ↦ ?_⟩
  rcases slawnyCube_eq_neg_six_subset (hsub hζ) with h | h
  · exact Set.mem_iUnion.2 ⟨0, h⟩
  · exact Set.mem_iUnion.2 ⟨1, h⟩

/-! ### Georgii's `P`-stability of `{G_1, G_2}` -/

/-- **Georgii's "the partition `{G_1, G_2}` is `P`-stable, despite the fact that
`σ_F(G_1) = σ_F(G_2)` when `F` is the top face or bottom face of `C`"**: a `P`-face, `k ∈ {0,1}`,
contains a whole vertical pair, whose parity distinguishes `G_1` from `G_2`. -/
theorem pairwise_disjoint_faceRestrict_slawnyG {k : Fin 3} (hk : k ∈ ({0, 1} : Set (Fin 3)))
    (a : Fin 2) :
    Pairwise fun m n ↦ Disjoint (faceRestrict Bool k a '' slawnyG m)
      (faceRestrict Bool k a '' slawnyG n) := by
  intro m n hmn
  rw [Set.disjoint_left]
  rintro g ⟨ζ, hζ, rfl⟩ ⟨ξ, hξ, hfe⟩
  obtain ⟨c0, c1, hc0, hc1, hpair⟩ :
      ∃ c0 c1 : Fin 3 → Fin 2, c0 k = a ∧ c1 k = a ∧
        (∀ ω : (Fin 3 → Fin 2) → Bool, xor (ω c0) (ω c1) = slawnyVert ω (c0 0) (c0 1)) := by
    rcases hk with hk | hk
    · subst hk
      exact ⟨cb a 0 0, cb a 0 1, rfl, rfl, fun ω ↦ rfl⟩
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      exact ⟨cb 0 a 0, cb 0 a 1, rfl, rfl, fun ω ↦ rfl⟩
  have h0 : ζ c0 = ξ c0 := (congrFun hfe (⟨c0, hc0⟩ : {c : Fin 3 → Fin 2 // c k = a})).symm
  have h1 : ζ c1 = ξ c1 := (congrFun hfe (⟨c1, hc1⟩ : {c : Fin 3 → Fin 2 // c k = a})).symm
  have hz := mem_slawnyG_iff.1 hζ (c0 0) (c0 1)
  have hx := mem_slawnyG_iff.1 hξ (c0 0) (c0 1)
  rw [← hpair ζ] at hz
  rw [← hpair ξ, ← h0, ← h1] at hx
  refine hmn ?_
  have : (![false, true] m : Bool) = ![false, true] n := by rw [← hz, hx]
  revert this
  fin_cases m <;> fin_cases n <;> decide

/-! ### Georgii's symmetry `ω ↦ ((-1)^{i_3} ω_i)` -/

/-- **Georgii's `τ : ω ↦ ((-1)^{i_3} ω_i)`**, the spin flip on the odd layers: a pure spin
transformation (18.21). -/
def slawnyLayerFlip : CubeTransformation Bool 3 :=
  CubeTransformation.pureSpin fun c ↦ if c 2 = 1 then boolNot else MeasurableEquiv.refl Bool

lemma slawnyLayerFlip_spin (c : Fin 3 → Fin 2) :
    slawnyLayerFlip.spin c = if c 2 = 1 then boolNot else MeasurableEquiv.refl Bool := rfl

@[simp] lemma onCube_slawnyLayerFlip (ζ : (Fin 3 → Fin 2) → Bool) (c : Fin 3 → Fin 2) :
    slawnyLayerFlip.onCube.toFun ζ c = if c 2 = 1 then !(ζ c) else ζ c := by
  rw [slawnyLayerFlip, CubeTransformation.pureSpin_onCube_toFun_apply]
  split_ifs with h <;> rfl

/-- Georgii's `τ` belongs to `I_{C,λ}(Φ)` for (18.39): every face of `C` contains an even number
of sites of each layer. -/
theorem isSymmetry_slawnyLayerFlip :
    slawnyLayerFlip.IsSymmetry (slawnyCube 3) uniformSpinMeasure := by
  refine CubeTransformation.IsSymmetry.of_apply_onCube slawnyCube_cubeRefl
    (fun c ↦ by
      rw [slawnyLayerFlip_spin]
      split_ifs with h
      · exact measurePreserving_boolNot_uniformSpinMeasure
      · exact MeasurePreserving.id _)
    fun ζ ↦ ?_
  have hface : ∀ (l : Fin 3) (a : Fin 2), faceProd l a (slawnyLayerFlip.onCube.toFun ζ)
      = faceProd l a ζ := by
    intro l a
    rcases fin_three_cases l with rfl | rfl | rfl
    · rw [faceProd_zero, faceProd_zero]
      simp only [onCube_slawnyLayerFlip, show ((cb a 0 0) 2 : Fin 2) = 0 from rfl,
        show ((cb a 0 1) 2 : Fin 2) = 1 from rfl, show ((cb a 1 0) 2 : Fin 2) = 0 from rfl,
        show ((cb a 1 1) 2 : Fin 2) = 1 from rfl]
      norm_num [spin_not]
    · rw [faceProd_one, faceProd_one]
      simp only [onCube_slawnyLayerFlip, show ((cb 0 a 0) 2 : Fin 2) = 0 from rfl,
        show ((cb 0 a 1) 2 : Fin 2) = 1 from rfl, show ((cb 1 a 0) 2 : Fin 2) = 0 from rfl,
        show ((cb 1 a 1) 2 : Fin 2) = 1 from rfl]
      norm_num [spin_not]
    · rw [faceProd_two, faceProd_two]
      rcases fin_two_eq_zero_or_one a with rfl | rfl
      · simp only [onCube_slawnyLayerFlip, show ((cb 0 0 (0 : Fin 2)) 2 : Fin 2) = 0 from rfl,
          show ((cb 0 1 (0 : Fin 2)) 2 : Fin 2) = 0 from rfl,
          show ((cb 1 0 (0 : Fin 2)) 2 : Fin 2) = 0 from rfl,
          show ((cb 1 1 (0 : Fin 2)) 2 : Fin 2) = 0 from rfl]
        norm_num
      · simp only [onCube_slawnyLayerFlip, show ((cb 0 0 (1 : Fin 2)) 2 : Fin 2) = 1 from rfl,
          show ((cb 0 1 (1 : Fin 2)) 2 : Fin 2) = 1 from rfl,
          show ((cb 1 0 (1 : Fin 2)) 2 : Fin 2) = 1 from rfl,
          show ((cb 1 1 (1 : Fin 2)) 2 : Fin 2) = 1 from rfl]
        norm_num [spin_not]
  simp only [slawnyCube]
  congr 1
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun a _ ↦ hface l a

/-- **Georgii's "`G_1` and `G_2` are related to each other by `ω ↦ ((-1)^{i_3} ω_i)`".** -/
lemma image_onCube_slawnyLayerFlip_slawnyG {m n : Fin 2} (hmn : m ≠ n) :
    slawnyLayerFlip.onCube.toFun '' slawnyG m = slawnyG n := by
  have hvert : ∀ (ω : (Fin 3 → Fin 2) → Bool) (x y : Fin 2),
      slawnyVert (slawnyLayerFlip.onCube.toFun ω) x y = !(slawnyVert ω x y) := by
    intro ω x y
    simp only [slawnyVert, onCube_slawnyLayerFlip, show ((cb x y 0) 2 : Fin 2) = 0 from rfl,
      show ((cb x y 1) 2 : Fin 2) = 1 from rfl, if_neg (by decide : ¬((0 : Fin 2) = 1))]
    generalize ω (cb x y 0) = p
    generalize ω (cb x y 1) = q
    revert p q
    decide
  have hstep : ∀ p q : Fin 2, p ≠ q → ∀ ω : (Fin 3 → Fin 2) → Bool, ω ∈ slawnyG p →
      slawnyLayerFlip.onCube.toFun ω ∈ slawnyG q := by
    intro p q hpq ω hω
    refine mem_slawnyG_iff.2 fun x y ↦ ?_
    rw [hvert, mem_slawnyG_iff.1 hω x y]
    revert hpq
    fin_cases p <;> fin_cases q <;> decide
  refine Set.Subset.antisymm ?_ fun ξ hξ ↦ ⟨slawnyLayerFlip.onCube.toFun ξ,
    hstep n m (Ne.symm hmn) ξ hξ, ?_⟩
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact hstep m n hmn ζ hζ
  · funext c
    simp only [onCube_slawnyLayerFlip]
    split_ifs with h <;> simp

theorem isPhiSymmetric_slawnyG :
    IsPhiSymmetric (slawnyCube 3) uniformSpinMeasure slawnyG :=
  isPhiSymmetric_of_ne slawnyCube_cubeRefl
    fun m n hmn ↦ ⟨slawnyLayerFlip, isSymmetry_slawnyLayerFlip,
      image_onCube_slawnyLayerFlip_slawnyG hmn⟩


/-! ### The hypotheses of Theorem (18.25) for `P = {0, 1}` -/

/-- **Georgii's `P`-stable, `Φ`-symmetric partition of the local ground states of (18.39)**, with
`P = {0, 1} ⊆ Fin 3` the plane (18.5).  Together with `isPhiSymmetric_slawnyG` and
`isCubeConfining_slawnyCube` these are all the hypotheses of Theorem (18.25); only its
`d`-dimensional proof is missing from the tree (see the module doc). -/
theorem isPStablePartition_slawnyG :
    IsPStablePartition (slawnyCube 3) uniformSpinMeasure ({0, 1} : Set (Fin 3)) slawnyG where
  exists_localGroundStates_subset := exists_localGroundStates_subset_slawnyG
  pairwise_disjoint_faceRestrict k hk a := pairwise_disjoint_faceRestrict_slawnyG hk a

/-- **Condition (iv) of Georgii (17.18)** for (18.39): the state space is finite, so `Φ_C` is
bounded and `K_ℓ = E` will do. -/
theorem isCubeConfining_slawnyCube :
    IsCubeConfining (slawnyCube 3) uniformSpinMeasure fun _ : ℕ ↦ (Set.univ : Set Bool) :=
  isCubeConfining_univ_of_finite _ _

end MeasureTheory.GibbsMeasure

end

end
