/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.GroupTheory.SignedPerm.Affine
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.Sort

/-!
# The alcoves of the cubic lattice

For a finite linear order `ι`, the *fundamental chamber* (alcove)

  `fundamentalChamber ι = {x | 1/2 > x_{i₁} > x_{i₂} > ⋯ > x_{i_d} > 0}`, `i₁ < ⋯ < i_d`,

i.e. `x` strictly antitone with values in `(0, 1/2)`, is a fundamental domain of the affine signed
permutations `AffineSignedPerm ι = ℤ^ι ⋊ SignedPerm ι` on the complement of the mirrors: it meets
no mirror (`notMem_sUnion_mirrors_of_mem_fundamentalChamber`), and every point on no mirror is
`g • z` for a unique `g` and `z ∈ fundamentalChamber ι` (`exists_smul_eq_of_notMem_sUnion_mirrors`,
`eq_of_smul_eq_smul`). The proof is the standard one: subtract the nearest lattice point
(`round`), then the coordinates are nonzero, of distinct absolute values in `(0, 1/2)`, and
exactly one signed permutation makes them positive and decreasing.

The *chambers* are the connected components of the complement of the mirrors. Since the
translates `g • fundamentalChamber ι` are open, convex, pairwise disjoint and cover that
complement, they are exactly the chambers (`chambers_eq_range`), and the group acts on the
chambers simply transitively (`smul_fundamentalChamber_injective`,
`existsUnique_smul_fundamentalChamber_eq`).
-/

@[expose] public section

open Equiv Finset Function Matrix SemidirectProduct
open scoped Pointwise

/-- Every injective family on a finite linear order can be sorted decreasingly. -/
theorem Finite.exists_perm_strictAnti_comp {ι β : Type*} [Finite ι] [LinearOrder ι]
    [LinearOrder β] {a : ι → β} (ha : Injective a) : ∃ σ : Perm ι, StrictAnti (a ∘ σ) := by
  have := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  let b : Fin (Fintype.card ι) → βᵒᵈ := fun k ↦ OrderDual.toDual (a (e k))
  have hb : Antitone (a ∘ e ∘ Tuple.sort b) := Tuple.monotone_sort b
  have hinj : Injective (a ∘ e ∘ Tuple.sort b) :=
    ha.comp (e.injective.comp (Tuple.sort b).injective)
  refine ⟨(e.symm.toEquiv.trans (Tuple.sort b)).trans e.toEquiv, ?_⟩
  exact (hb.strictAnti_of_injective hinj).comp_strictMono e.symm.strictMono

/-- A permutation reordering a strictly antitone family into a strictly antitone family is the
identity. -/
theorem Equiv.Perm.eq_one_of_strictAnti_comp {ι β : Type*} [Finite ι] [LinearOrder ι]
    [Preorder β] {f : ι → β} (hf : StrictAnti f) {σ : Perm ι} (hσ : StrictAnti (f ∘ σ)) :
    σ = 1 := by
  have hmono : StrictMono σ := fun a b hab ↦ (StrictAnti.lt_iff_gt hf).1 (hσ hab)
  have h := Subsingleton.elim (hmono.orderIsoOfSurjective σ σ.surjective) (OrderIso.refl ι)
  exact Equiv.ext fun i ↦ congrArg (fun e : ι ≃o ι ↦ e i) h

namespace AffineSignedPerm

variable {ι : Type*} [LinearOrder ι]

variable (ι) in
/-- The **fundamental chamber** `{x | 1/2 > x_{i₁} > ⋯ > x_{i_d} > 0}` (for `ι = Fin 3`:
`{0 < x₂ < x₁ < x₀ < 1/2}`): the strictly antitone `x` with values in `(0, 1/2)`. -/
def fundamentalChamber : Set (ι → ℝ) :=
  {x | StrictAnti x ∧ ∀ i, 0 < x i ∧ x i < 1 / 2}

theorem nonempty_fundamentalChamber [Finite ι] : (fundamentalChamber ι).Nonempty := by
  have := Fintype.ofFinite ι
  refine ⟨fun i ↦ ((#{j | i < j} : ℕ) + 1 : ℝ) / (2 * (Fintype.card ι + 1)),
    fun i j hij ↦ ?_, fun i ↦ ⟨by positivity, ?_⟩⟩
  · have hlt : #{k | j < k} < #{k | i < k} := Finset.card_lt_card
      ⟨fun k hk ↦ by simp only [mem_filter, mem_univ, true_and] at hk ⊢; exact hij.trans hk,
        fun h ↦ by have := h (by simpa using hij); simp at this⟩
    dsimp only
    gcongr
  · have hlt : #{j | i < j} < Fintype.card ι :=
      Finset.card_lt_univ_of_notMem (x := i) (by simp)
    rw [div_lt_iff₀ (by positivity)]
    have : ((#{j | i < j} : ℕ) : ℝ) + 1 ≤ Fintype.card ι := by exact_mod_cast hlt
    linarith

theorem isOpen_fundamentalChamber [Finite ι] : IsOpen (fundamentalChamber ι) := by
  have h : fundamentalChamber ι = (⋂ i, ⋂ j, ⋂ (_ : i < j), {x : ι → ℝ | x j < x i}) ∩
      ⋂ i, ({x | 0 < x i} ∩ {x | x i < 1 / 2}) := by
    ext x
    simp [fundamentalChamber, StrictAnti]
  rw [h]
  exact (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
    isOpen_iInter_of_finite fun _ ↦ isOpen_lt (continuous_apply j) (continuous_apply i)).inter
    (isOpen_iInter_of_finite fun i ↦ (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const))

theorem convex_fundamentalChamber : Convex ℝ (fundamentalChamber ι) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hx.1 hij
    have h2 := hy.1 hij
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      linarith
    · nlinarith [mul_lt_mul_of_pos_left h1 ha', mul_le_mul_of_nonneg_left h2.le hb]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := (hx.2 i).1
    have h2 := (hy.2 i).1
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      linarith
    · nlinarith [mul_pos ha' h1, mul_nonneg hb h2.le]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := (hx.2 i).2
    have h2 := (hy.2 i).2
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      linarith
    · nlinarith [mul_lt_mul_of_pos_left h1 ha', mul_le_mul_of_nonneg_left h2.le hb]

omit [LinearOrder ι] in
theorem smul_apply_eq {g : AffineSignedPerm ι} (z : ι → ℝ) (i : ι) :
    (g • z) i = translationPart g i + ((g.right.left i : ℤ) : ℝ) * z (g.right.right⁻¹ i) := by
  simp [smul_apply, SignedPerm.smul_apply, Units.smul_def]

theorem abs_units_mul {u : ℤˣ} {a : ℝ} (ha : 0 ≤ a) : |((u : ℤ) : ℝ) * a| = a := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp [abs_of_nonneg ha]

/-- `translationPart g` is the nearest lattice point of every point of `g • fundamentalChamber ι`.
-/
theorem round_smul_apply {g : AffineSignedPerm ι} {z : ι → ℝ} (hz : z ∈ fundamentalChamber ι)
    (i : ι) : round ((g • z) i) = translationPart g i := by
  have h := abs_units_mul (u := g.right.left i) (hz.2 (g.right.right⁻¹ i)).1.le
  have hlt := (hz.2 (g.right.right⁻¹ i)).2
  rw [smul_apply_eq, round_intCast_add, round_eq_zero_iff.2, add_zero]
  constructor <;> [skip; rw [← h] at hlt] <;> linarith [neg_abs_le (((g.right.left i : ℤ) : ℝ) *
    z (g.right.right⁻¹ i)), le_abs_self (((g.right.left i : ℤ) : ℝ) * z (g.right.right⁻¹ i))]

/-- **Uniqueness**: if `g • z = g' • z'` with `z, z'` in the fundamental chamber, then `g = g'`
(and `z = z'`). -/
theorem eq_of_smul_eq_smul [Finite ι] {g g' : AffineSignedPerm ι} {z z' : ι → ℝ}
    (hz : z ∈ fundamentalChamber ι) (hz' : z' ∈ fundamentalChamber ι) (h : g • z = g' • z') :
    g = g' := by
  have hk : translationPart g = translationPart g' := funext fun i ↦ by
    rw [← round_smul_apply hz i, ← round_smul_apply hz' i, h]
  have hrz : ∀ i, ((g.right.left i : ℤ) : ℝ) * z (g.right.right⁻¹ i) =
      ((g'.right.left i : ℤ) : ℝ) * z' (g'.right.right⁻¹ i) := fun i ↦ by
    have := congrFun h i
    rw [smul_apply_eq, smul_apply_eq, hk] at this
    linarith
  have habs : ∀ i, z (g.right.right⁻¹ i) = z' (g'.right.right⁻¹ i) := fun i ↦ by
    have := congrArg abs (hrz i)
    rwa [abs_units_mul (hz.2 _).1.le, abs_units_mul (hz'.2 _).1.le] at this
  have hzτ : z = z' ∘ (g'.right.right⁻¹ * g.right.right) := funext fun j ↦ by
    simpa using habs (g.right.right j)
  have hτ : g'.right.right⁻¹ * g.right.right = 1 :=
    Perm.eq_one_of_strictAnti_comp hz'.1 (hzτ ▸ hz.1)
  have hσ : g.right.right = g'.right.right := (inv_mul_eq_one.1 hτ).symm
  have hzz : z = z' := by rw [hzτ, hτ]; rfl
  have ht : g.right.left = g'.right.left := funext fun i ↦ by
    have := hrz i
    rw [hσ, hzz] at this
    have := mul_right_cancel₀ (hz'.2 _).1.ne' this
    exact Units.ext (by exact_mod_cast this)
  exact SemidirectProduct.ext hk (SemidirectProduct.ext ht hσ)

/-- **The action on the chambers is free**: `g • fundamentalChamber ι` determines `g`. -/
theorem smul_fundamentalChamber_injective [Finite ι] :
    Injective fun g : AffineSignedPerm ι ↦ g • fundamentalChamber ι := by
  intro g g' h
  obtain ⟨z, hz⟩ := nonempty_fundamentalChamber (ι := ι)
  have h' : g • fundamentalChamber ι = g' • fundamentalChamber ι := h
  obtain ⟨z', hz', hzz'⟩ : g • z ∈ g' • fundamentalChamber ι := h' ▸ Set.smul_mem_smul_set hz
  exact (eq_of_smul_eq_smul hz' hz hzz').symm

/-- The stabilizer of the fundamental chamber is trivial. -/
theorem eq_one_of_smul_fundamentalChamber [Finite ι] {g : AffineSignedPerm ι}
    (h : g • fundamentalChamber ι = fundamentalChamber ι) : g = 1 :=
  smul_fundamentalChamber_injective (h.trans (one_smul _ _).symm)

variable [Fintype ι]

/-- **The fundamental chamber meets no mirror.** -/
theorem notMem_sUnion_mirrors_of_mem_fundamentalChamber {z : ι → ℝ}
    (hz : z ∈ fundamentalChamber ι) : z ∉ ⋃₀ mirrors ι := by
  have hnot : ∀ m : ℤ, ¬ ((0 : ℝ) < m ∧ (m : ℝ) < 1) := fun m ⟨h0, h1⟩ ↦ by
    have h0' : 0 < m := by exact_mod_cast h0
    have h1' : m < 1 := by exact_mod_cast h1
    omega
  rw [mem_sUnion_mirrors_iff]
  rintro (⟨i, m, h⟩ | ⟨i, j, hij, m, h | h⟩)
  · exact hnot m ⟨by linarith [(hz.2 i).1], by linarith [(hz.2 i).2]⟩
  · exact hnot m ⟨by linarith [(hz.2 i).1, (hz.2 j).1], by linarith [(hz.2 i).2, (hz.2 j).2]⟩
  · have hm1 : (m : ℝ) < 1 := by linarith [(hz.2 i).2, (hz.2 j).1]
    have hm2 : (-1 : ℝ) < m := by linarith [(hz.2 i).1, (hz.2 j).2]
    have hm : m = 0 := by
      have : m < 1 := by exact_mod_cast hm1
      have : -1 < m := by exact_mod_cast hm2
      omega
    subst hm
    exact hij (hz.1.injective (by simpa [sub_eq_zero] using h))

/-- **Every point on no mirror lies in a translate `g • fundamentalChamber ι`.** -/
theorem exists_smul_eq_of_notMem_sUnion_mirrors {x : ι → ℝ} (hx : x ∉ ⋃₀ mirrors ι) :
    ∃ g : AffineSignedPerm ι, ∃ z ∈ fundamentalChamber ι, g • z = x := by
  rw [mem_sUnion_mirrors_iff] at hx
  push Not at hx
  obtain ⟨hcoord, hdiag⟩ := hx
  have hy0 : ∀ i, x i - round (x i) ≠ 0 := fun i h ↦ hcoord i (2 * round (x i)) (by
    rw [sub_eq_zero] at h; push_cast; rw [← h])
  have hy_lt : ∀ i, |x i - round (x i)| < 1 / 2 := fun i ↦ by
    refine (abs_sub_round (x i)).lt_of_ne fun h ↦ ?_
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.1 h with h' | h'
    · exact hcoord i (2 * round (x i) + 1) (by push_cast; linarith)
    · exact hcoord i (2 * round (x i) - 1) (by push_cast; linarith)
  have hinj : Injective fun i ↦ |x i - round (x i)| := fun i j h ↦ by
    by_contra hij
    rcases abs_eq_abs.1 h with h' | h'
    · exact (hdiag i j hij (round (x i) - round (x j))).2 (by push_cast; linarith)
    · exact (hdiag i j hij (round (x i) + round (x j))).1 (by push_cast; linarith)
  obtain ⟨σ, hσ⟩ := Finite.exists_perm_strictAnti_comp hinj
  refine ⟨⟨Multiplicative.ofAdd fun i ↦ round (x i),
    ⟨fun i ↦ if 0 < x i - round (x i) then 1 else -1, σ⟩⟩,
    fun j ↦ |x (σ j) - round (x (σ j))|, ⟨hσ, fun j ↦ ⟨abs_pos.2 (hy0 _), hy_lt _⟩⟩,
    funext fun i ↦ ?_⟩
  rw [smul_apply, SignedPerm.smul_apply]
  simp only [translationPart, toAdd_ofAdd, Units.smul_def, zsmul_eq_mul]
  rw [show σ (σ⁻¹ i) = i from σ.apply_symm_apply i]
  by_cases hpos : 0 < x i - round (x i)
  · simp only [hpos, ↓reduceIte, abs_of_pos hpos]
    simp
  · have hneg : x i - round (x i) < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hy0 i)
    simp only [hpos, ↓reduceIte, abs_of_neg hneg]
    simp

theorem existsUnique_mem_smul_fundamentalChamber {x : ι → ℝ} (hx : x ∉ ⋃₀ mirrors ι) :
    ∃! g : AffineSignedPerm ι, x ∈ g • fundamentalChamber ι := by
  obtain ⟨g, z, hz, rfl⟩ := exists_smul_eq_of_notMem_sUnion_mirrors hx
  refine ⟨g, Set.smul_mem_smul_set hz, fun g' ⟨z', hz', h⟩ ↦ eq_of_smul_eq_smul hz' hz h⟩

/-! ### Chambers -/

variable (ι) in
/-- The **chambers**: the connected components of the complement of the mirrors. -/
def chambers : Set (Set (ι → ℝ)) :=
  {C | ∃ x ∉ ⋃₀ mirrors ι, connectedComponentIn (⋃₀ mirrors ι)ᶜ x = C}

theorem smul_fundamentalChamber_subset_compl (g : AffineSignedPerm ι) :
    g • fundamentalChamber ι ⊆ (⋃₀ mirrors ι)ᶜ := by
  rintro _ ⟨w, hw, rfl⟩ hm
  exact notMem_sUnion_mirrors_of_mem_fundamentalChamber hw ((smul_mem_sUnion_mirrors_iff g w).1 hm)

/-- **The chamber of `g • z`**, `z` in the fundamental chamber, is `g • fundamentalChamber ι`. -/
theorem connectedComponentIn_smul_eq (g : AffineSignedPerm ι) {z : ι → ℝ}
    (hz : z ∈ fundamentalChamber ι) :
    connectedComponentIn (⋃₀ mirrors ι)ᶜ (g • z) = g • fundamentalChamber ι := by
  have hopen : ∀ h : AffineSignedPerm ι, IsOpen (h • fundamentalChamber ι) := fun h ↦
    isOpen_fundamentalChamber.smul h
  have hgz : g • z ∈ g • fundamentalChamber ι := Set.smul_mem_smul_set hz
  refine Set.Subset.antisymm ?_ ?_
  · have hV : IsOpen (⋃ (h : AffineSignedPerm ι) (_ : h ≠ g), h • fundamentalChamber ι) :=
      isOpen_iUnion fun h ↦ isOpen_iUnion fun _ ↦ hopen h
    have hUV : Disjoint (g • fundamentalChamber ι)
        (⋃ (h : AffineSignedPerm ι) (_ : h ≠ g), h • fundamentalChamber ι) := by
      simp only [Set.disjoint_iUnion_right]
      intro h hne
      rw [Set.disjoint_left]
      rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hww'⟩
      exact hne (eq_of_smul_eq_smul hw' hw hww')
    have hcover : (⋃₀ mirrors ι)ᶜ ⊆ g • fundamentalChamber ι ∪
        ⋃ (h : AffineSignedPerm ι) (_ : h ≠ g), h • fundamentalChamber ι := by
      intro x hx
      obtain ⟨h, w, hw, rfl⟩ := exists_smul_eq_of_notMem_sUnion_mirrors hx
      by_cases hh : h = g
      · exact .inl (hh ▸ Set.smul_mem_smul_set hw)
      · exact .inr (Set.mem_iUnion₂.2 ⟨h, hh, Set.smul_mem_smul_set hw⟩)
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union (hopen g) hV hUV
      ((connectedComponentIn_subset _ _).trans hcover)
      ⟨g • z, mem_connectedComponentIn (smul_fundamentalChamber_subset_compl g hgz), hgz⟩
  · have hpre : IsPreconnected (g • fundamentalChamber ι) := by
      rw [← Set.image_smul]
      exact convex_fundamentalChamber.isPreconnected.image _
        (continuous_const_smul g).continuousOn
    exact hpre.subset_connectedComponentIn hgz (smul_fundamentalChamber_subset_compl g)

/-- **The chambers are exactly the translates of the fundamental chamber.** -/
theorem chambers_eq_range :
    chambers ι = Set.range fun g : AffineSignedPerm ι ↦ g • fundamentalChamber ι := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, z, hz, rfl⟩ := exists_smul_eq_of_notMem_sUnion_mirrors hx
    exact ⟨g, (connectedComponentIn_smul_eq g hz).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨z, hz⟩ := nonempty_fundamentalChamber (ι := ι)
    exact ⟨g • z, smul_fundamentalChamber_subset_compl g (Set.smul_mem_smul_set hz),
      connectedComponentIn_smul_eq g hz⟩

/-- **The group acts simply transitively on the chambers.** -/
theorem existsUnique_smul_fundamentalChamber_eq {C : Set (ι → ℝ)} (hC : C ∈ chambers ι) :
    ∃! g : AffineSignedPerm ι, g • fundamentalChamber ι = C := by
  rw [chambers_eq_range] at hC
  obtain ⟨g, rfl⟩ := hC
  exact ⟨g, rfl, fun g' h ↦ smul_fundamentalChamber_injective h⟩

theorem smul_mem_chambers (g : AffineSignedPerm ι) {C : Set (ι → ℝ)} (hC : C ∈ chambers ι) :
    g • C ∈ chambers ι := by
  rw [chambers_eq_range] at hC ⊢
  obtain ⟨h, rfl⟩ := hC
  exact ⟨g * h, mul_smul g h _⟩

end AffineSignedPerm
