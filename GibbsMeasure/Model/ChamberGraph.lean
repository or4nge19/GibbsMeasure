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

end AffineSignedPerm
