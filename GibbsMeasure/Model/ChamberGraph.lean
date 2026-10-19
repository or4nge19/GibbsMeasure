/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Cayley
public import GibbsMeasure.Mathlib.GroupTheory.SignedPerm.Alcove
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The chamber graph of the cubic lattice

In `d = n + 1` dimensions (coordinates `Fin (n + 1)`), the fundamental chamber
`C₀ = {1/2 > x₀ > x₁ > ⋯ > x_n > 0}` has `d + 1` walls, numbered as in the lattice QED₃
construction (for `d = 3`, `C₀ = {0 < x₃ < x₂ < x₁ < 1/2}` in 1-based coordinates):

* wall `0`: `x_n = 0`, reflection `s₀ : x_n ↦ -x_n`;
* wall `c + 1` (`c : Fin n`): `x_{n-1-c} = x_{n-c}`, reflection the transposition of these
  coordinates;
* wall `n + 1`: `x₀ = 1/2`, reflection `s_{n+1} : x₀ ↦ 1 - x₀`.

`wallReflection i` is the reflection in wall `i` (`wallReflection_eq_mirrorReflection`), with
inward normal `wallNormal i` and height `wallHeight i` (`wall i = mirror (wallNormal i)
(wallHeight i)`). The **chamber graph** is the Cayley graph of `AffineSignedPerm (Fin (n + 1))`
for the wall reflections: `g` and `g * wallReflection i` are joined by a bond of type `i`. Since
the group acts simply transitively on the chambers, its vertices are the chambers `g • C₀`; for a
base point `v₀ ∈ C₀` they are the fermion sites `g • v₀`, and `translationPart g` is the nearest
lattice point of `g • v₀` (`round_smul_apply`), the photon site of the site.

## Main results ([Q] Proposition 2.1)

* `chamberGraph_connected`: the wall reflections generate the group, so the graph is connected.
* `chamberGraph_isBipartite`: each wall reflection has sign `-1`; the parts are the signs of the
  linear parts.
* `neighborSet_chamberGraph`, `mul_wallReflection_injective`: each site has exactly one neighbour
  of each type, `n + 2` in all.
* `translationPart_mul_wallReflection`: bonds of type `≠ n + 1` keep the photon site; a bond of
  type `n + 1` moves it by `g.right • e₀`, a unit vector (`translationPart_mul_eq_smul`: the
  photon site is equivariant).
* `card_lowerEnd`: exactly `2 ^ n * n !` bonds of type `n + 1` have lower end at `k` over the
  link `k → k + e μ` (`8` for `d = 3`).
-/

@[expose] public section

open Equiv Finset Function Matrix SemidirectProduct
open scoped Pointwise

namespace AffineSignedPerm

variable {n : ℕ}

/-! ### The walls of the fundamental chamber -/

/-- The inward normals of the walls of the fundamental chamber: `e_n`, `e_{n-1-c} - e_{n-c}`,
`-e₀`. -/
def wallNormal : Fin (n + 2) → Fin (n + 1) → ℤ :=
  Fin.cases (Pi.single (Fin.last n) 1)
    (Fin.lastCases (Pi.single 0 (-1)) fun c ↦
      Pi.single c.rev.castSucc 1 + Pi.single c.rev.succ (-1))

/-- The heights of the walls: `wall i = mirror (wallNormal i) (wallHeight i)`. -/
def wallHeight : Fin (n + 2) → ℤ :=
  Fin.cases 0 (Fin.lastCases (-1) fun _ ↦ 0)

/-- The reflections in the walls of the fundamental chamber: `x_n ↦ -x_n`, the transposition of
`x_{n-1-c}` and `x_{n-c}`, and `x₀ ↦ 1 - x₀`. -/
def wallReflection : Fin (n + 2) → AffineSignedPerm (Fin (n + 1)) :=
  Fin.cases (inr (inl (Pi.mulSingle (Fin.last n) (-1))))
    (Fin.lastCases ⟨Multiplicative.ofAdd (Pi.single 0 1), inl (Pi.mulSingle 0 (-1))⟩
      fun c ↦ inr (inr (Equiv.swap c.rev.castSucc c.rev.succ)))

/-- The walls of the fundamental chamber. -/
def wall (i : Fin (n + 2)) : Set (Fin (n + 1) → ℝ) :=
  mirror (wallNormal i) (wallHeight i)

@[simp] theorem wallNormal_zero : wallNormal (0 : Fin (n + 2)) = Pi.single (Fin.last n) 1 := rfl

@[simp] theorem wallNormal_last : wallNormal (Fin.last (n + 1)) = Pi.single 0 (-1) := by
  rw [← Fin.succ_last, wallNormal, Fin.cases_succ, Fin.lastCases_last]

@[simp] theorem wallNormal_succ_castSucc (c : Fin n) :
    wallNormal c.castSucc.succ = Pi.single c.rev.castSucc 1 + Pi.single c.rev.succ (-1) := by
  rw [wallNormal, Fin.cases_succ, Fin.lastCases_castSucc]

@[simp] theorem wallHeight_zero : wallHeight (0 : Fin (n + 2)) = 0 := rfl

@[simp] theorem wallHeight_last : wallHeight (Fin.last (n + 1)) = -1 := by
  rw [← Fin.succ_last, wallHeight, Fin.cases_succ, Fin.lastCases_last]

@[simp] theorem wallHeight_succ_castSucc (c : Fin n) : wallHeight c.castSucc.succ = 0 := by
  rw [wallHeight, Fin.cases_succ, Fin.lastCases_castSucc]

@[simp] theorem wallReflection_zero :
    wallReflection (0 : Fin (n + 2)) = inr (inl (Pi.mulSingle (Fin.last n) (-1))) := rfl

@[simp] theorem wallReflection_last : wallReflection (Fin.last (n + 1)) =
    ⟨Multiplicative.ofAdd (Pi.single 0 1), inl (Pi.mulSingle 0 (-1))⟩ := by
  rw [← Fin.succ_last, wallReflection, Fin.cases_succ, Fin.lastCases_last]

@[simp] theorem wallReflection_succ_castSucc (c : Fin n) :
    wallReflection c.castSucc.succ = inr (inr (Equiv.swap c.rev.castSucc c.rev.succ)) := by
  rw [wallReflection, Fin.cases_succ, Fin.lastCases_castSucc]

/-- Induction on the walls: wall `0`, the walls `c + 1`, wall `n + 1`. -/
@[elab_as_elim]
theorem wall_induction {motive : Fin (n + 2) → Prop} (zero : motive 0)
    (mid : ∀ c : Fin n, motive c.castSucc.succ) (last : motive (Fin.last (n + 1)))
    (i : Fin (n + 2)) : motive i := by
  induction i using Fin.cases with
  | zero => exact zero
  | succ j =>
    induction j using Fin.lastCases with
    | last => rw [Fin.succ_last]; exact last
    | cast c => exact mid c

theorem castSucc_rev_ne_succ_rev (c : Fin n) : c.rev.castSucc ≠ c.rev.succ :=
  Fin.castSucc_lt_succ.ne

theorem wallNormal_dotProduct_self (i : Fin (n + 2)) :
    wallNormal i ⬝ᵥ wallNormal i = if i = 0 ∨ i = Fin.last (n + 1) then 1 else 2 := by
  induction i using wall_induction with
  | zero => simp
  | mid c =>
    have h : ¬(c.castSucc.succ = 0 ∨ c.castSucc.succ = Fin.last (n + 1)) := by
      simp [Fin.ext_iff]; omega
    simp only [h, ↓reduceIte, wallNormal_succ_castSucc]
    simp [dotProduct_add, castSucc_rev_ne_succ_rev, (castSucc_rev_ne_succ_rev c).symm]
  | last => simp

theorem wallNormal_dotProduct_self_dvd (i : Fin (n + 2)) :
    wallNormal i ⬝ᵥ wallNormal i ∣ 2 := by
  rw [wallNormal_dotProduct_self]
  split_ifs <;> norm_num

/-- **The wall reflections are the reflections in the walls.** -/
theorem wallReflection_eq_mirrorReflection (i : Fin (n + 2)) :
    wallReflection i =
      mirrorReflection (wallNormal i) (wallNormal_dotProduct_self_dvd i) (wallHeight i) := by
  induction i using wall_induction with
  | zero =>
    rw [wallReflection_zero]
    simp only [wallHeight_zero, wallNormal_zero]
    rw [mirrorReflection_zero, SignedPerm.reflection_single]
  | mid c =>
    rw [wallReflection_succ_castSucc]
    simp only [wallHeight_succ_castSucc, wallNormal_succ_castSucc]
    rw [mirrorReflection_zero,
      SignedPerm.reflection_single_add_single_neg_one (castSucc_rev_ne_succ_rev c)]
  | last =>
    refine ext_smul (R := ℝ) fun x ↦ funext fun k ↦ ?_
    rw [wallReflection_last, mirrorReflection_smul]
    simp only [wallHeight_last, wallNormal_last]
    have h1 : (Pi.single 0 (-1) : Fin (n + 1) → ℤ) ⬝ᵥ Pi.single 0 (-1) = 1 := by simp
    rw [intCast_single_dotProduct, h1]
    rcases eq_or_ne k 0 with rfl | hk
    · simp [smul_apply, SignedPerm.smul_apply, translationPart]
      ring
    · simp [smul_apply, SignedPerm.smul_apply, translationPart, hk]

theorem wallReflection_mul_self (i : Fin (n + 2)) : wallReflection i * wallReflection i = 1 := by
  rw [wallReflection_eq_mirrorReflection, mirrorReflection_mul_self]

theorem wallReflection_ne_one (i : Fin (n + 2)) : wallReflection i ≠ 1 := by
  intro h
  have := congrArg (fun g ↦ SignedPerm.sign g.right) h
  induction i using wall_induction with
  | zero => simp at this
  | mid c => simp [Perm.sign_swap (castSucc_rev_ne_succ_rev c)] at this
  | last => simp at this

/-- The wall reflections are odd. -/
theorem sign_wallReflection_right (i : Fin (n + 2)) :
    SignedPerm.sign (wallReflection i).right = -1 := by
  induction i using wall_induction with
  | zero => simp
  | mid c => simp [Perm.sign_swap (castSucc_rev_ne_succ_rev c)]
  | last => simp

/-- Only the reflection in the wall `x₀ = 1/2` translates: by `e₀`. -/
theorem translationPart_wallReflection (i : Fin (n + 2)) :
    translationPart (wallReflection i) = if i = Fin.last (n + 1) then Pi.single 0 1 else 0 := by
  induction i using wall_induction with
  | zero => simp [Fin.ext_iff]
  | mid c =>
    have h : c.castSucc.succ ≠ Fin.last (n + 1) := by simp [Fin.ext_iff]; omega
    simp [h]
  | last => simp [translationPart]

theorem wallReflection_injective : Injective (wallReflection (n := n)) := by
  intro i j h
  have ht := congrArg translationPart h
  have hr := congrArg (fun g ↦ g.right.right) h
  have hl := congrArg (fun g ↦ g.right.left) h
  rw [translationPart_wallReflection, translationPart_wallReflection] at ht
  induction i using wall_induction with
  | zero =>
    induction j using wall_induction with
    | zero => rfl
    | mid c =>
      simp only [wallReflection_zero, wallReflection_succ_castSucc, right_inr, right_inl] at hr
      exact absurd (swap_eq_one_iff.1 hr.symm) (castSucc_rev_ne_succ_rev c)
    | last =>
      have h0 : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by simp [Fin.ext_iff]
      simp only [h0, ↓reduceIte] at ht
      simpa using congrFun ht 0
  | mid c =>
    have hc : c.castSucc.succ ≠ Fin.last (n + 1) := by simp [Fin.ext_iff]; omega
    induction j using wall_induction with
    | zero =>
      simp only [wallReflection_zero, wallReflection_succ_castSucc, right_inr, right_inl] at hr
      exact absurd (swap_eq_one_iff.1 hr) (castSucc_rev_ne_succ_rev c)
    | mid c' =>
      simp only [wallReflection_succ_castSucc, right_inr] at hr
      have h1 := congrArg (fun σ : Perm (Fin (n + 1)) ↦ σ c.rev.castSucc) hr
      simp only [swap_apply_left] at h1
      have hcc : c = c' := by
        rcases eq_or_ne c.rev.castSucc c'.rev.castSucc with h2 | h2
        · exact Fin.rev_injective (Fin.castSucc_injective _ h2)
        rcases eq_or_ne c.rev.castSucc c'.rev.succ with h3 | h3
        · rw [h3, swap_apply_right] at h1
          rw [Fin.ext_iff] at h1 h3
          simp only [Fin.val_castSucc, Fin.val_succ] at h1 h3
          omega
        · rw [swap_apply_of_ne_of_ne h2 h3] at h1
          exact absurd h1.symm (castSucc_rev_ne_succ_rev c)
      rw [hcc]
    | last =>
      simp only [hc, ↓reduceIte] at ht
      simpa using congrFun ht 0
  | last =>
    induction j using wall_induction with
    | zero =>
      have h0 : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by simp [Fin.ext_iff]
      simp only [h0, ↓reduceIte] at ht
      simpa using congrFun ht 0
    | mid c =>
      have hc : c.castSucc.succ ≠ Fin.last (n + 1) := by simp [Fin.ext_iff]; omega
      simp only [hc, ↓reduceIte] at ht
      simpa using congrFun ht 0
    | last => rfl

/-- **The wall reflections generate the group.** -/
theorem closure_range_wallReflection :
    Subgroup.closure (Set.range (wallReflection (n := n))) = ⊤ := by
  set H := Subgroup.closure (Set.range (wallReflection (n := n)))
  have hmem : ∀ i, wallReflection i ∈ H := fun i ↦ Subgroup.subset_closure ⟨i, rfl⟩
  have hr : ∀ r, (inr r : AffineSignedPerm (Fin (n + 1))) ∈ H := fun r ↦ by
    have hle : Subgroup.closure (insert (inl (Pi.mulSingle (Fin.last n) (-1)))
        (Set.range fun c : Fin n ↦ inr (Equiv.swap c.castSucc c.succ)) :
          Set (SignedPerm (Fin (n + 1)))) ≤ H.comap inr := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | ⟨c, rfl⟩)
      · exact hmem 0
      · have := hmem c.rev.castSucc.succ
        rwa [wallReflection_succ_castSucc, Fin.rev_rev] at this
    rw [SignedPerm.closure_inl_mulSingle_inr_swap_castSucc_succ] at hle
    exact hle (Subgroup.mem_top r)
  refine eq_top_of_inr_mem_of_inl_single_mem hr (i₀ := 0) ?_
  have h := H.mul_mem (hmem (Fin.last (n + 1))) (hr (inl (Pi.mulSingle 0 (-1))))
  convert h using 1
  rw [wallReflection_last]
  refine SemidirectProduct.ext ?_ ?_
  · simp [mul_left]
  · rw [mul_right, right_inl, right_inr, ← map_mul, ← Pi.mulSingle_mul, Int.units_mul_self,
      Pi.mulSingle_one, map_one]

/-! ### The chamber graph -/

variable (n) in
/-- The **chamber graph**: the Cayley graph of `AffineSignedPerm (Fin (n + 1))` for the wall
reflections. Its vertices are the chambers `g • C₀`, or the fermion sites `g • v₀`; the bond of
type `i` joins `g` and `g * wallReflection i`. -/
abbrev chamberGraph : SimpleGraph (AffineSignedPerm (Fin (n + 1))) :=
  SimpleGraph.mulCayley (Set.range wallReflection)

theorem chamberGraph_adj {g h : AffineSignedPerm (Fin (n + 1))} :
    (chamberGraph n).Adj g h ↔ ∃ i, g * wallReflection i = h := by
  rw [SimpleGraph.mulCayley_adj']
  constructor
  · rintro ⟨-, _, ⟨i, rfl⟩, hgh | hgh⟩
    · exact ⟨i, hgh⟩
    · exact ⟨i, by rw [hgh, mul_assoc, wallReflection_mul_self, mul_one]⟩
  · rintro ⟨i, rfl⟩
    refine ⟨fun h ↦ wallReflection_ne_one i ?_, _, ⟨i, rfl⟩, .inl rfl⟩
    simpa using h.symm

theorem mul_wallReflection_injective (g : AffineSignedPerm (Fin (n + 1))) :
    Injective fun i ↦ g * wallReflection i :=
  fun _ _ h ↦ wallReflection_injective (mul_left_cancel h)

/-- **Each site has exactly one neighbour of each type.** -/
theorem neighborSet_chamberGraph (g : AffineSignedPerm (Fin (n + 1))) :
    (chamberGraph n).neighborSet g = Set.range fun i ↦ g * wallReflection i := by
  ext h
  simp [SimpleGraph.mem_neighborSet, chamberGraph_adj]

theorem card_neighborSet_chamberGraph (g : AffineSignedPerm (Fin (n + 1))) :
    Nat.card ((chamberGraph n).neighborSet g) = n + 2 := by
  rw [neighborSet_chamberGraph, Nat.card_range_of_injective (mul_wallReflection_injective g),
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The chamber graph is connected.** -/
theorem chamberGraph_connected : (chamberGraph n).Connected :=
  SimpleGraph.mulCayley_connected closure_range_wallReflection

/-- **The chamber graph is bipartite**, with parts the sites `g` of sign `±1`. -/
theorem chamberGraph_isBipartite : (chamberGraph n).IsBipartite :=
  SimpleGraph.mulCayley_isBipartite (χ := SignedPerm.sign.comp rightHom) <| by
    rintro _ ⟨i, rfl⟩
    exact sign_wallReflection_right i

/-! ### Photon sites -/

/-- **Bonds and photon sites**: a bond of type `i ≠ n + 1` keeps the photon site
`translationPart g`; a bond of type `n + 1` moves it by the unit vector `g.right • e₀`. -/
theorem translationPart_mul_wallReflection (g : AffineSignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) : translationPart (g * wallReflection i) =
      if i = Fin.last (n + 1) then translationPart g + g.right • (Pi.single 0 1 : Fin (n + 1) → ℤ)
      else translationPart g := by
  rw [translationPart_mul, translationPart_wallReflection]
  split_ifs <;> simp

/-- Along a bond of type `n + 1` the direction `g.right • e₀` is reversed. -/
theorem right_mul_wallReflection_last_smul (g : AffineSignedPerm (Fin (n + 1))) :
    (g * wallReflection (Fin.last (n + 1))).right • (Pi.single 0 1 : Fin (n + 1) → ℤ) =
      -(g.right • Pi.single 0 1) := by
  rw [mul_right, mul_smul, wallReflection_last, SignedPerm.inl_smul, ← smul_neg]
  congr 1
  ext j
  rcases eq_or_ne j 0 with rfl | hj <;> simp [*]

/-- The lower ends of the bonds of type `n + 1` over the link `k → k + e μ` are the sites `g` with
`translationPart g = k` and `g.right • e₀ = e μ`. -/
theorem translationPart_mul_wallReflection_last_of_smul {g : AffineSignedPerm (Fin (n + 1))}
    {μ : Fin (n + 1)} (h : g.right • (Pi.single 0 1 : Fin (n + 1) → ℤ) = Pi.single μ 1) :
    translationPart (g * wallReflection (Fin.last (n + 1))) =
      translationPart g + Pi.single μ 1 := by
  simp only [translationPart_mul_wallReflection, ↓reduceIte, h]

theorem card_perm_apply_zero_eq (μ : Fin (n + 1)) :
    Nat.card {σ : Perm (Fin (n + 1)) // σ 0 = μ} = n.factorial := by
  have e : {σ : Perm (Fin (n + 1)) // σ 0 = μ} ≃ Perm (Fin n) := {
    toFun σ := (Perm.decomposeFin σ.1).2
    invFun e := ⟨Perm.decomposeFin.symm (μ, e), Perm.decomposeFin_symm_apply_zero μ e⟩
    left_inv σ := by
      obtain ⟨σ, rfl⟩ := σ
      ext1
      have h1 : (Perm.decomposeFin σ).1 = σ 0 := by
        have := Perm.decomposeFin_symm_apply_zero (Perm.decomposeFin σ).1 (Perm.decomposeFin σ).2
        rw [Prod.mk.eta, Equiv.symm_apply_apply] at this
        exact this.symm
      simp only
      rw [← h1, Prod.mk.eta, Equiv.symm_apply_apply]
    right_inv e := by simp }
  rw [Nat.card_congr e, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_units_fun_eq_one (μ : Fin (n + 1)) :
    Nat.card {t : Fin (n + 1) → ℤˣ // t μ = 1} = 2 ^ n := by
  have e : {t : Fin (n + 1) → ℤˣ // t μ = 1} ≃ ({j // j ≠ μ} → ℤˣ) := {
    toFun t j := t.1 j
    invFun s := ⟨fun j ↦ if h : j = μ then 1 else s ⟨j, h⟩, by simp⟩
    left_inv t := by
      ext1
      funext j
      by_cases h : j = μ
      · subst h; simp [t.2]
      · simp [h]
    right_inv s := by
      funext j
      simp [j.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := ℤˣ),
    Fintype.card_units_int, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Fintype.card_fin, Nat.add_sub_cancel]

/-- **Bonds over a link**: exactly `2 ^ n * n !` sites `g` with photon site `k` have their bond of
type `n + 1` over the link `k → k + e μ` (`8` in three dimensions): the signed permutations with
`r • e₀ = e μ`. -/
theorem card_lowerEnd (k : Fin (n + 1) → ℤ) (μ : Fin (n + 1)) :
    Nat.card {g : AffineSignedPerm (Fin (n + 1)) //
      translationPart g = k ∧ g.right • (Pi.single 0 1 : Fin (n + 1) → ℤ) = Pi.single μ 1} =
      2 ^ n * n.factorial := by
  have e : {g : AffineSignedPerm (Fin (n + 1)) //
      translationPart g = k ∧ g.right • (Pi.single 0 1 : Fin (n + 1) → ℤ) = Pi.single μ 1} ≃
      {t : Fin (n + 1) → ℤˣ // t μ = 1} × {σ : Perm (Fin (n + 1)) // σ 0 = μ} := {
    toFun g := (⟨g.1.right.left, by
        have := g.2.2
        rw [SignedPerm.smul_single] at this
        have hσ : g.1.right.right 0 = μ := by
          by_contra hne
          simpa [Pi.single_apply, hne] using congrFun this μ
        have := congrFun this μ
        rw [hσ, Pi.single_eq_same, Pi.single_eq_same, Units.smul_def, smul_eq_mul,
          mul_one] at this
        exact Units.ext this⟩,
      ⟨g.1.right.right, by
        have := g.2.2
        rw [SignedPerm.smul_single] at this
        by_contra hne
        simpa [Pi.single_apply, hne] using congrFun this μ⟩)
    invFun x := ⟨⟨Multiplicative.ofAdd k, ⟨x.1.1, x.2.1⟩⟩, rfl, by
      rw [SignedPerm.smul_single]
      simp [x.1.2, x.2.2]⟩
    left_inv g := by
      obtain ⟨⟨k', r⟩, hk, -⟩ := g
      subst hk
      rfl
    right_inv x := rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_units_fun_eq_one, card_perm_apply_zero_eq]

/-! ### The wall functionals -/

/-- The affine function of wall `i`, `(2 / ‖n_i‖²) ⟪n_i, z⟫ - m_i`: `2 z_n`, `z_{n-1-c} - z_{n-c}`,
`1 - 2 z₀` (`wallFunctional_zero`, `wallFunctional_succ_castSucc`, `wallFunctional_last`). It
vanishes exactly on the wall (`mem_wall_iff`), and the fundamental chamber is the set where all of
them are positive (`mem_fundamentalChamber_iff`). -/
def wallFunctional (i : Fin (n + 2)) (z : Fin (n + 1) → ℝ) : ℝ :=
  ((2 / (wallNormal i ⬝ᵥ wallNormal i) : ℤ) : ℝ) * ((fun k ↦ (wallNormal i k : ℝ)) ⬝ᵥ z) -
    wallHeight i

theorem mem_wall_iff {i : Fin (n + 2)} {z : Fin (n + 1) → ℝ} :
    z ∈ wall i ↔ wallFunctional i z = 0 := by
  rw [wall, mem_mirror, wallFunctional, sub_eq_zero]

@[simp] theorem wallFunctional_zero (z : Fin (n + 1) → ℝ) :
    wallFunctional 0 z = 2 * z (Fin.last n) := by
  have h : (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℤ) ⬝ᵥ Pi.single (Fin.last n) 1 = 1 := by simp
  rw [wallFunctional, wallNormal_zero, wallHeight_zero, h, intCast_single_dotProduct]
  norm_num

@[simp] theorem wallFunctional_succ_castSucc (c : Fin n) (z : Fin (n + 1) → ℝ) :
    wallFunctional c.castSucc.succ z = z c.rev.castSucc - z c.rev.succ := by
  have h := dotProduct_single_one_add_single_self (castSucc_rev_ne_succ_rev c) (-1)
  simp only [Units.val_neg, Units.val_one] at h
  rw [wallFunctional, wallNormal_succ_castSucc, wallHeight_succ_castSucc, h,
    intCast_single_add_single_dotProduct]
  norm_num
  ring

@[simp] theorem wallFunctional_last (z : Fin (n + 1) → ℝ) :
    wallFunctional (Fin.last (n + 1)) z = 1 - 2 * z 0 := by
  have h : (Pi.single 0 (-1) : Fin (n + 1) → ℤ) ⬝ᵥ Pi.single 0 (-1) = 1 := by simp
  rw [wallFunctional, wallNormal_last, wallHeight_last, h, intCast_single_dotProduct]
  norm_num
  ring

/-- `wallFunctional (c + 1)` in terms of a coordinate `q = rev c`: `z_q - z_{q+1}`. -/
theorem wallFunctional_rev (q : Fin n) (z : Fin (n + 1) → ℝ) :
    wallFunctional q.rev.castSucc.succ z = z q.castSucc - z q.succ := by
  rw [wallFunctional_succ_castSucc, Fin.rev_rev]

/-- **The fundamental chamber is the intersection of the positive sides of its walls.** -/
theorem mem_fundamentalChamber_iff {z : Fin (n + 1) → ℝ} :
    z ∈ fundamentalChamber (Fin (n + 1)) ↔ ∀ i, 0 < wallFunctional i z := by
  constructor
  · rintro ⟨hz, hb⟩ i
    induction i using wall_induction with
    | zero => simpa using (hb _).1
    | mid c => simpa using hz (Fin.castSucc_lt_succ (i := c.rev))
    | last => rw [wallFunctional_last]; linarith [(hb 0).2]
  · intro h
    have hanti : StrictAnti z := Fin.strictAnti_iff_succ_lt.2 fun q ↦ by
      simpa [wallFunctional_rev] using h q.rev.castSucc.succ
    refine ⟨hanti, fun k ↦ ⟨?_, ?_⟩⟩
    · have := h 0
      rw [wallFunctional_zero] at this
      exact (by linarith : 0 < z (Fin.last n)).trans_le (hanti.antitone (Fin.le_last k))
    · have := h (Fin.last (n + 1))
      rw [wallFunctional_last] at this
      exact (hanti.antitone (Fin.zero_le k)).trans_lt (by linarith)

theorem wallFunctional_sub_smul (j i : Fin (n + 2)) (z : Fin (n + 1) → ℝ) (t : ℝ) :
    wallFunctional j (z - t • fun k ↦ (wallNormal i k : ℝ)) = wallFunctional j z -
      t * (((2 / (wallNormal j ⬝ᵥ wallNormal j)) * (wallNormal j ⬝ᵥ wallNormal i) : ℤ) : ℝ) := by
  rw [wallFunctional, wallFunctional, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    intCast_dotProduct_intCast]
  push_cast
  ring

theorem wallFunctional_self_coeff (i : Fin (n + 2)) :
    ((2 / (wallNormal i ⬝ᵥ wallNormal i)) * (wallNormal i ⬝ᵥ wallNormal i) : ℤ) = 2 :=
  Int.ediv_mul_cancel (wallNormal_dotProduct_self_dvd i)

/-- **Distinct walls meet at a non-obtuse angle**: their inward normals have non-positive inner
product (the simple roots of type `C̃`). -/
theorem wallNormal_dotProduct_nonpos {i j : Fin (n + 2)} (hij : i ≠ j) :
    wallNormal j ⬝ᵥ wallNormal i ≤ 0 := by
  have hL : ∀ c : Fin n, c.rev.castSucc ≠ Fin.last n := fun c ↦ (Fin.castSucc_lt_last _).ne
  have h0 : ∀ c : Fin n, c.rev.succ ≠ 0 := fun c ↦ Fin.succ_ne_zero _
  have hL' : ∀ c : Fin n, Fin.last n ≠ c.rev.castSucc := fun c ↦ (hL c).symm
  have h0' : ∀ c : Fin n, (0 : Fin (n + 1)) ≠ c.rev.succ := fun c ↦ (h0 c).symm
  have hcc : ∀ c c' : Fin n, c'.castSucc.succ ≠ c.castSucc.succ →
      c'.rev.castSucc ≠ c.rev.castSucc ∧ c'.rev.succ ≠ c.rev.succ := fun c c' h ↦ by
    simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, Fin.val_rev] at h ⊢
    omega
  induction i using wall_induction with
  | zero =>
    induction j using wall_induction with
    | zero => exact absurd rfl hij
    | mid c =>
      simp only [wallNormal_zero, wallNormal_succ_castSucc, add_dotProduct, single_dotProduct,
        Pi.single_apply, hL, ↓reduceIte]
      split_ifs <;> norm_num
    | last =>
      simp only [wallNormal_zero, wallNormal_last, single_dotProduct, Pi.single_apply]
      split_ifs <;> norm_num
  | mid c =>
    induction j using wall_induction with
    | zero =>
      simp only [wallNormal_zero, wallNormal_succ_castSucc, single_dotProduct, Pi.add_apply,
        Pi.single_apply, hL', ↓reduceIte]
      split_ifs <;> norm_num
    | mid c' =>
      obtain ⟨ha, hb⟩ := hcc c c' (Ne.symm hij)
      simp only [wallNormal_succ_castSucc, add_dotProduct, single_dotProduct, Pi.add_apply,
        Pi.single_apply, ha, hb, ↓reduceIte]
      split_ifs <;> norm_num
    | last =>
      simp only [wallNormal_last, wallNormal_succ_castSucc, single_dotProduct, Pi.add_apply,
        Pi.single_apply, h0', ↓reduceIte]
      split_ifs <;> norm_num
  | last =>
    induction j using wall_induction with
    | zero =>
      simp only [wallNormal_zero, wallNormal_last, single_dotProduct, Pi.single_apply]
      split_ifs <;> norm_num
    | mid c =>
      simp only [wallNormal_last, wallNormal_succ_castSucc, add_dotProduct, single_dotProduct,
        Pi.single_apply, h0, ↓reduceIte]
      split_ifs <;> norm_num
    | last => exact absurd rfl hij

/-! ### Bonds cross exactly one mirror, their wall, orthogonally at the midpoint -/

theorem wallReflection_smul (i : Fin (n + 2)) (z : Fin (n + 1) → ℝ) :
    wallReflection i • z = z - wallFunctional i z • fun k ↦ (wallNormal i k : ℝ) := by
  rw [wallReflection_eq_mirrorReflection, mirrorReflection_smul]
  rfl

theorem wall_mem_mirrors (i : Fin (n + 2)) : wall i ∈ mirrors (Fin (n + 1)) :=
  mirror_mem_mirrors (wallNormal_dotProduct_self_dvd i) _

theorem midpoint_wallReflection_smul (i : Fin (n + 2)) (z : Fin (n + 1) → ℝ) :
    midpoint ℝ z (wallReflection i • z) =
      z - ((1 / 2 : ℝ) * wallFunctional i z) • fun k ↦ (wallNormal i k : ℝ) := by
  rw [wallReflection_smul, midpoint_eq_smul_add, invOf_eq_inv]
  module

theorem midpoint_mem_wall (i : Fin (n + 2)) (z : Fin (n + 1) → ℝ) :
    midpoint ℝ z (wallReflection i • z) ∈ wall i := by
  rw [wallReflection_eq_mirrorReflection]
  exact midpoint_mem_mirror _ _ z

/-- The coefficient `(2 / ‖n_j‖²) ⟪n_j, n_i⟫` is `2` for `j = i` and `≤ 0` otherwise. -/
theorem wallFunctional_coeff_nonpos {i j : Fin (n + 2)} (hij : i ≠ j) :
    ((2 / (wallNormal j ⬝ᵥ wallNormal j) * (wallNormal j ⬝ᵥ wallNormal i) : ℤ) : ℝ) ≤ 0 := by
  have h2 : 0 ≤ 2 / (wallNormal j ⬝ᵥ wallNormal j) :=
    Int.ediv_nonneg (by norm_num) (sum_nonneg fun k _ ↦ mul_self_nonneg _)
  exact_mod_cast mul_nonpos_of_nonneg_of_nonpos h2 (wallNormal_dotProduct_nonpos hij)

/-- **Each half of a bond lies in a chamber**: the points `z - (t a) n_i`, `0 ≤ t < 1/2`, of the
bond from `z ∈ C₀` to `s_i z = z - a n_i` lie in the fundamental chamber. -/
theorem sub_smul_wallNormal_mem {z : Fin (n + 1) → ℝ} (hz : z ∈ fundamentalChamber (Fin (n + 1)))
    (i : Fin (n + 2)) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1 / 2) :
    z - (t * wallFunctional i z) • (fun k ↦ (wallNormal i k : ℝ)) ∈
      fundamentalChamber (Fin (n + 1)) := by
  have ha := mem_fundamentalChamber_iff.1 hz
  refine mem_fundamentalChamber_iff.2 fun j ↦ ?_
  rw [wallFunctional_sub_smul]
  by_cases hji : j = i
  · subst hji
    rw [wallFunctional_self_coeff]
    have := ha j
    push_cast
    nlinarith
  · have := wallFunctional_coeff_nonpos (Ne.symm hji)
    have := ha j
    have := mul_nonneg ht0 (ha i).le
    nlinarith

theorem wallReflection_smul_sub_smul {z : Fin (n + 1) → ℝ} (i : Fin (n + 2)) (t : ℝ) :
    wallReflection i • (z - (t * wallFunctional i z) • fun k ↦ (wallNormal i k : ℝ)) =
      z - ((1 - t) * wallFunctional i z) • fun k ↦ (wallNormal i k : ℝ) := by
  rw [wallReflection_smul, wallFunctional_sub_smul, wallFunctional_self_coeff]
  push_cast
  module

/-- **A bond meets the mirrors only at its midpoint.** -/
theorem segment_inter_sUnion_mirrors {v : Fin (n + 1) → ℝ}
    (hv : v ∈ fundamentalChamber (Fin (n + 1))) (g : AffineSignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) :
    segment ℝ (g • v) ((g * wallReflection i) • v) ∩ ⋃₀ mirrors (Fin (n + 1)) =
      {midpoint ℝ (g • v) ((g * wallReflection i) • v)} := by
  have key : segment ℝ v (wallReflection i • v) ∩ ⋃₀ mirrors (Fin (n + 1)) =
      {midpoint ℝ v (wallReflection i • v)} := by
    ext x
    constructor
    · rintro ⟨hx, hxM⟩
      rw [segment_eq_image'] at hx
      obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
      have hd : v + θ • (wallReflection i • v - v) =
          v - (θ * wallFunctional i v) • fun k ↦ (wallNormal i k : ℝ) := by
        rw [wallReflection_smul]
        module
      simp only at hxM ⊢
      rw [hd] at hxM ⊢
      rcases lt_trichotomy θ (1 / 2) with hlt | rfl | hgt
      · exact absurd hxM (notMem_sUnion_mirrors_of_mem_fundamentalChamber
          (sub_smul_wallNormal_mem hv i h0 hlt))
      · rw [Set.mem_singleton_iff, midpoint_wallReflection_smul]
      · rw [← sub_sub_cancel 1 θ, ← wallReflection_smul_sub_smul,
          smul_mem_sUnion_mirrors_iff] at hxM
        exact absurd hxM (notMem_sUnion_mirrors_of_mem_fundamentalChamber
          (sub_smul_wallNormal_mem hv i (by linarith) (by linarith)))
    · rintro rfl
      exact ⟨midpoint_mem_segment _ _, wall i, wall_mem_mirrors i, midpoint_mem_wall i v⟩
  rw [mul_smul, ← smul_segment, ← smul_midpoint]
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hxM⟩
    have : y ∈ segment ℝ v (wallReflection i • v) ∩ ⋃₀ mirrors (Fin (n + 1)) :=
      ⟨hy, (smul_mem_sUnion_mirrors_iff g y).1 hxM⟩
    rw [key, Set.mem_singleton_iff] at this
    rw [this, Set.mem_singleton_iff]
  · rintro rfl
    have hm : midpoint ℝ v (wallReflection i • v) ∈
        segment ℝ v (wallReflection i • v) ∩ ⋃₀ mirrors (Fin (n + 1)) := key ▸ rfl
    exact ⟨Set.smul_mem_smul_set hm.1, (smul_mem_sUnion_mirrors_iff g _).2 hm.2⟩

/-- The midpoint of the bond of type `i` at `g` lies on the wall `g • wall i`. -/
theorem midpoint_mem_smul_wall (g : AffineSignedPerm (Fin (n + 1))) (i : Fin (n + 2))
    (v : Fin (n + 1) → ℝ) : midpoint ℝ (g • v) ((g * wallReflection i) • v) ∈ g • wall i := by
  rw [mul_smul, ← smul_midpoint]
  exact Set.smul_mem_smul_set (midpoint_mem_wall i v)

/-- **The bond crosses its wall orthogonally**: its displacement is a multiple of the normal
`g.right • n_i` of `g • wall i` (`smul_mirror`). -/
theorem mul_wallReflection_smul_sub_smul (g : AffineSignedPerm (Fin (n + 1))) (i : Fin (n + 2))
    (v : Fin (n + 1) → ℝ) : (g * wallReflection i) • v - g • v =
      -wallFunctional i v • (g.right • fun k ↦ (wallNormal i k : ℝ)) := by
  rw [mul_smul, smul_sub_smul_eq, wallReflection_smul, sub_sub_cancel_left, smul_neg, smul_comm,
    neg_smul]

/-- **The open face of a wall lies on no other mirror**: a point on `wall i` strictly on the
positive side of the other walls lies on exactly one mirror, `wall i`. -/
theorem eq_wall_of_mem {p : Fin (n + 1) → ℝ} {i : Fin (n + 2)}
    (hpos : ∀ j, j ≠ i → 0 < wallFunctional j p) (hzero : wallFunctional i p = 0)
    {H : Set (Fin (n + 1) → ℝ)} (hH : H ∈ mirrors (Fin (n + 1))) (hp : p ∈ H) : H = wall i := by
  have hnonneg : ∀ j, 0 ≤ wallFunctional j p := fun j ↦ by
    by_cases hj : j = i
    · rw [hj, hzero]
    · exact (hpos j hj).le
  have huniq : ∀ j, wallFunctional j p = 0 → j = i := fun j hj ↦ by
    by_contra hne
    exact (hpos j hne).ne' hj
  have hanti : Antitone p := Fin.antitone_iff_succ_le.2 fun q ↦ by
    have := hnonneg q.rev.castSucc.succ
    rw [wallFunctional_rev] at this
    linarith
  have hlast : 0 ≤ p (Fin.last n) := by
    have := hnonneg 0
    rw [wallFunctional_zero] at this
    linarith
  have hfirst : p 0 ≤ 1 / 2 := by
    have := hnonneg (Fin.last (n + 1))
    rw [wallFunctional_last] at this
    linarith
  have hrange : ∀ k, 0 ≤ p k ∧ p k ≤ 1 / 2 := fun k ↦
    ⟨hlast.trans (hanti (Fin.le_last k)), (hanti (Fin.zero_le k)).trans hfirst⟩
  have hstep : ∀ q : Fin n, p q.castSucc = p q.succ → i = q.rev.castSucc.succ := fun q h ↦
    (huniq _ (by rw [wallFunctional_rev, h, sub_self])).symm
  -- two equal coordinates are adjacent, across the wall `i`
  have hD4 : ∀ k l : Fin (n + 1), k < l → p k = p l →
      ∃ q : Fin n, k = q.castSucc ∧ l = q.succ ∧ i = q.rev.castSucc.succ := by
    intro k l hkl hpkl
    have hflat : ∀ q : Fin n, k ≤ q.castSucc → q.succ ≤ l → p q.castSucc = p q.succ :=
      fun q h1 h2 ↦ le_antisymm (by linarith [hanti h1, hanti h2])
        (hanti (Fin.castSucc_le_succ q))
    have hkl' : (k : ℕ) < l := hkl
    have hl := l.isLt
    obtain ⟨q, hq⟩ : ∃ q : Fin n, (q : ℕ) = k := ⟨⟨k, by omega⟩, rfl⟩
    have hqk : q.castSucc = k := Fin.ext hq
    have hql : q.succ ≤ l := by rw [Fin.le_iff_val_le_val, Fin.val_succ]; omega
    have hi := hstep q (hflat q hqk.ge hql)
    refine ⟨q, hqk.symm, ?_, hi⟩
    by_contra hne
    have hlt : (k : ℕ) + 1 < l := by
      have : (q.succ : ℕ) ≠ l := fun h ↦ hne (Fin.ext h).symm
      rw [Fin.le_iff_val_le_val, Fin.val_succ] at hql
      rw [Fin.val_succ] at this
      omega
    obtain ⟨q', hq'⟩ : ∃ q' : Fin n, (q' : ℕ) = k + 1 := ⟨⟨k + 1, by omega⟩, rfl⟩
    have h1 : k ≤ q'.castSucc := by rw [Fin.le_iff_val_le_val, Fin.val_castSucc]; omega
    have h2 : q'.succ ≤ l := by rw [Fin.le_iff_val_le_val, Fin.val_succ]; omega
    have hi' := hstep q' (hflat q' h1 h2)
    rw [hi, Fin.ext_iff] at hi'
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_rev] at hi'
    have := q.isLt
    have := q'.isLt
    omega
  have hD2 : ∀ k, p k = 0 → k = Fin.last n ∧ i = 0 := by
    intro k hk
    have hL : p (Fin.last n) = 0 := le_antisymm (hk ▸ hanti (Fin.le_last k)) hlast
    have hi0 : i = 0 := (huniq 0 (by rw [wallFunctional_zero, hL, mul_zero])).symm
    refine ⟨?_, hi0⟩
    by_contra hne
    obtain ⟨q, -, -, hq⟩ :=
      hD4 k (Fin.last n) (lt_of_le_of_ne (Fin.le_last k) hne) (hk.trans hL.symm)
    rw [hi0] at hq
    exact Fin.succ_ne_zero _ hq.symm
  have hD3 : ∀ k, p k = 1 / 2 → k = 0 ∧ i = Fin.last (n + 1) := by
    intro k hk
    have h0 : p 0 = 1 / 2 := le_antisymm hfirst (hk ▸ hanti (Fin.zero_le k))
    have hiL : i = Fin.last (n + 1) :=
      (huniq _ (by rw [wallFunctional_last, h0]; norm_num)).symm
    refine ⟨?_, hiL⟩
    by_contra hne
    obtain ⟨q, -, -, hq⟩ :=
      hD4 0 k (lt_of_le_of_ne (Fin.zero_le k) (Ne.symm hne)) (h0.trans hk.symm)
    rw [hiL, Fin.ext_iff] at hq
    simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc, Fin.val_rev] at hq
    have := q.isLt
    omega
  have hint01 : ∀ m : ℤ, (0 : ℝ) ≤ m → (m : ℝ) ≤ 1 → m = 0 ∨ m = 1 := fun m h0 h1 ↦ by
    have : 0 ≤ m := by exact_mod_cast h0
    have : m ≤ 1 := by exact_mod_cast h1
    omega
  have hint0 : ∀ m : ℤ, (-1 : ℝ) < m → (m : ℝ) < 1 → m = 0 := fun m h0 h1 ↦ by
    have : -1 < m := by exact_mod_cast h0
    have : m < 1 := by exact_mod_cast h1
    omega
  obtain ⟨n', hn', m', rfl⟩ := hH
  rcases dotProduct_self_eq_one_or_two hn' with h1 | h2
  · -- a coordinate mirror `{2 u x_k = m'}`
    obtain ⟨k, u, rfl⟩ := exists_eq_single_of_dotProduct_self_eq_one h1
    have hp' := mem_mirror.1 hp
    rw [h1, intCast_single_dotProduct] at hp'
    norm_num at hp'
    have hu2 : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    have hp'' : 2 * p k = (((u : ℤ) * m' : ℤ) : ℝ) := by
      push_cast
      rw [← hp']
      linear_combination (-(2 * p k)) * hu2
    rcases hint01 _ (by rw [← hp'']; linarith [(hrange k).1])
      (by rw [← hp'']; linarith [(hrange k).2]) with hM | hM
    · obtain ⟨rfl, rfl⟩ := hD2 k (by rw [hM] at hp''; push_cast at hp''; linarith)
      have hm' : m' = 0 := by rcases Int.units_eq_one_or u with rfl | rfl <;> simpa using hM
      subst hm'
      ext x
      rw [mem_mirror, h1, intCast_single_dotProduct, mem_wall_iff, wallFunctional_zero]
      rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
    · obtain ⟨rfl, rfl⟩ := hD3 k (by rw [hM] at hp''; push_cast at hp''; linarith)
      have hm' : m' = u := by
        rcases Int.units_eq_one_or u with rfl | rfl <;> simp at hM ⊢ <;> omega
      subst hm'
      ext x
      rw [mem_mirror, h1, intCast_single_dotProduct, mem_wall_iff, wallFunctional_last]
      rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num <;> constructor <;> intro h <;>
        linarith
  · -- a diagonal mirror `{u x_k + w x_l = m'}`
    obtain ⟨k, l, hkl, u, w, rfl⟩ := exists_eq_single_add_single_of_dotProduct_self_eq_two h2
    have hp' := mem_mirror.1 hp
    rw [h2, intCast_single_add_single_dotProduct] at hp'
    norm_num at hp'
    have hk := hrange k
    have hl := hrange l
    -- the sum `p k + p l ∈ [0, 1]` is not an integer
    have hsum : ∀ m : ℤ, p k + p l = m → False := fun m hm ↦ by
      rcases hint01 m (by linarith) (by linarith) with rfl | rfl
      · exact hkl ((hD2 k (by push_cast at hm; linarith)).1.trans
          (hD2 l (by push_cast at hm; linarith)).1.symm)
      · exact hkl ((hD3 k (by push_cast at hm; linarith)).1.trans
          (hD3 l (by push_cast at hm; linarith)).1.symm)
    -- a difference `p k - p l ∈ ℤ` vanishes, and the mirror is the wall between `k` and `l`
    have hdiff : ∀ (m : ℤ) (ε : ℤˣ), p k - p l = m → mirror (Pi.single k (ε : ℤ) +
        Pi.single l ((-ε : ℤˣ) : ℤ)) (ε * m) = wall i := fun m ε hm ↦ by
      have hm0 : m = 0 := hint0 m (by linarith) (by linarith)
      subst hm0
      have hε : ((ε : ℤ) : ℝ) ≠ 0 := by rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num
      have hmem : ∀ x : Fin (n + 1) → ℝ, x ∈ mirror (Pi.single k (ε : ℤ) +
          Pi.single l ((-ε : ℤˣ) : ℤ)) (ε * 0) ↔ x k = x l := fun x ↦ by
        rw [mem_mirror, dotProduct_single_add_single_self hkl, intCast_single_add_single_dotProduct]
        norm_num
        constructor
        · intro h
          have : ((ε : ℤ) : ℝ) * (x k - x l) = 0 := by linarith
          linarith [(mul_eq_zero.1 this).resolve_left hε]
        · intro h; rw [h]; ring
      have hpkl : p k = p l := by push_cast at hm; linarith
      rcases lt_or_gt_of_ne hkl with hlt | hgt
      · obtain ⟨q, rfl, rfl, rfl⟩ := hD4 k l hlt hpkl
        ext x
        rw [hmem, mem_wall_iff, wallFunctional_rev, sub_eq_zero]
      · obtain ⟨q, rfl, rfl, rfl⟩ := hD4 l k hgt hpkl.symm
        ext x
        rw [hmem, mem_wall_iff, wallFunctional_rev, sub_eq_zero, eq_comm]
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or w with rfl | rfl
    · exact absurd (by push_cast at hp' ⊢; linarith) (hsum m')
    · have := hdiff m' 1 (by push_cast at hp' ⊢; linarith)
      simpa using this
    · have := hdiff (-m') (-1) (by push_cast at hp' ⊢; linarith)
      simpa using this
    · exact absurd (by push_cast at hp' ⊢; linarith) (hsum (-m'))

/-- **The midpoint of a bond lies on exactly one mirror**, the wall `g • wall i` it crosses. -/
theorem eq_smul_wall_of_midpoint_mem {v : Fin (n + 1) → ℝ}
    (hv : v ∈ fundamentalChamber (Fin (n + 1))) (g : AffineSignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) {H : Set (Fin (n + 1) → ℝ)} (hH : H ∈ mirrors (Fin (n + 1)))
    (h : midpoint ℝ (g • v) ((g * wallReflection i) • v) ∈ H) : H = g • wall i := by
  rw [mul_smul, ← smul_midpoint, ← Set.mem_inv_smul_set_iff] at h
  have ha := mem_fundamentalChamber_iff.1 hv
  have hwall : g⁻¹ • H = wall i := by
    refine eq_wall_of_mem (fun j hji ↦ ?_) (mem_wall_iff.1 (midpoint_mem_wall i v))
      (smul_mem_mirrors g⁻¹ hH) h
    rw [midpoint_wallReflection_smul, wallFunctional_sub_smul]
    have := wallFunctional_coeff_nonpos (Ne.symm hji)
    have := ha j
    have := (ha i).le
    nlinarith
  rw [← hwall, smul_inv_smul]

/-- **A bond crossing a mirror is `{x, θ x}`**: if the bond of type `i` at `g` meets
`mirror n' m'`, its far end is the reflection of its near end in that mirror. -/
theorem mul_wallReflection_smul_eq_mirrorReflection_smul {v : Fin (n + 1) → ℝ}
    (hv : v ∈ fundamentalChamber (Fin (n + 1))) (g : AffineSignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) {n' : Fin (n + 1) → ℤ} (hn' : n' ⬝ᵥ n' ∣ 2) {m' : ℤ}
    (h : (segment ℝ (g • v) ((g * wallReflection i) • v) ∩ mirror n' m').Nonempty) :
    (g * wallReflection i) • v = mirrorReflection n' hn' m' • (g • v) := by
  obtain ⟨x, hxs, hxm⟩ := h
  have hx : x ∈ segment ℝ (g • v) ((g * wallReflection i) • v) ∩ ⋃₀ mirrors (Fin (n + 1)) :=
    ⟨hxs, mirror n' m', mirror_mem_mirrors hn' m', hxm⟩
  rw [segment_inter_sUnion_mirrors hv, Set.mem_singleton_iff] at hx
  subst hx
  have hH := eq_smul_wall_of_midpoint_mem hv g i (mirror_mem_mirrors hn' m') hxm
  rw [wall, smul_mirror] at hH
  have hdvd : (g.right • wallNormal i) ⬝ᵥ (g.right • wallNormal i) ∣ 2 := by
    rw [SignedPerm.dotProduct_smul_smul]
    exact wallNormal_dotProduct_self_dvd i
  rw [mirrorReflection_eq_of_mirror_eq hn' hdvd hH, ← mul_mirrorReflection_mul_inv g
    (wallNormal_dotProduct_self_dvd i), ← wallReflection_eq_mirrorReflection, mul_smul,
    mul_smul, inv_smul_smul, mul_smul]

end AffineSignedPerm
