/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Legendre duality for a rate function on `ℝ^k`

A large deviation rate function is typically identified with the convex conjugate of a limiting
logarithmic moment generating function (a pressure, a free energy). The convex-analytic content of
that identification is the Fenchel–Moreau biconjugation theorem, which Mathlib does not have
(`grep convexConjugate`, `grep Fenchel` in `Mathlib/Analysis/Convex/`: no hits). This file proves
the case that a rate function needs, on a finite-dimensional space and for an `EReal`-valued
function, from the geometric Hahn–Banach theorem.

## Main result

* `eq_iSup_sub_of_isClosed_convex_epigraph`: let `J : (K → ℝ) → EReal` have a closed convex
  epigraph and let `g : (K → ℝ) → ℝ` be such that

  * `t · x − g t ≤ J x` for all `t` and `x` (Fenchel–Young: `g` dominates the conjugate `J*`), and
  * for every `t` the value `g t` is *attained*: there are `y` and `0 ≤ r` with `J y ≤ r` and
    `r = t · y − g t` (so `g ≤ J*`, and the supremum defining `J* t` is achieved in the
    epigraph).

  Then `J x = ⨆_t (t · x − g t)`, i.e. `J` is the convex conjugate of `g`.

The proof separates the point `(x, c)` from the closed convex epigraph of `J` by a continuous
linear functional `f` on `(K → ℝ) × ℝ`; the vertical component of `f` is nonpositive because the
epigraph is closed upwards, and the case of a purely vertical hyperplane is excluded by scaling
the horizontal component, using that the attaining points have `r ≥ 0`.

The statement is one instance of the general biconjugation theorem `J = J**` for a proper convex
lower semicontinuous `J`, whose eventual home is a convex-conjugate file in
`Mathlib/Analysis/Convex/`; it is stated here in the form a large deviation rate function
consumes, with the conjugate `g` given rather than constructed, since in the applications `g` is
a pressure that is known independently.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

/-- **Fenchel–Moreau on `ℝ^k` for an `EReal`-valued function whose conjugate is attained.**
If the epigraph of `J : (K → ℝ) → EReal` is closed and convex, if `t · x − g t ≤ J x` for all
`t, x`, and if for every `t` there is a point `(y, r)` of the epigraph with `r ≥ 0` and
`r = t · y − g t`, then `J` is the convex conjugate of `g`:
`J x = ⨆_{t ∈ ℝ^k} (t · x − g t)`. -/
theorem eq_iSup_sub_of_isClosed_convex_epigraph {K : Type*} [Fintype K] {J : (K → ℝ) → EReal}
    {g : (K → ℝ) → ℝ}
    (hconv : Convex ℝ {p : (K → ℝ) × ℝ | J p.1 ≤ (p.2 : EReal)})
    (hclosed : IsClosed {p : (K → ℝ) × ℝ | J p.1 ≤ (p.2 : EReal)})
    (hle : ∀ t x : K → ℝ, (((∑ j, t j * x j) - g t : ℝ) : EReal) ≤ J x)
    (hattained : ∀ t : K → ℝ, ∃ (y : K → ℝ) (r : ℝ),
      J y ≤ (r : EReal) ∧ 0 ≤ r ∧ r = (∑ j, t j * y j) - g t)
    (x : K → ℝ) :
    J x = ⨆ t : K → ℝ, (((∑ j, t j * x j) - g t : ℝ) : EReal) := by
  classical
  refine le_antisymm ?_ (iSup_le fun t ↦ hle t x)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.1 hcon
  set c : ℝ := (q : ℝ) with hcdef
  set C : Set ((K → ℝ) × ℝ) := {p : (K → ℝ) × ℝ | J p.1 ≤ (p.2 : EReal)} with hC
  -- the supremum is at most `c`, and it is nonnegative because `g 0 ≤ 0`
  have hstar : ∀ t : K → ℝ, (∑ j, t j * x j) - g t ≤ c :=
    fun t ↦ EReal.coe_le_coe_iff.1 (le_of_lt ((le_iSup _ t).trans_lt hq1))
  have hc0 : (0 : ℝ) < c := by
    obtain ⟨y₀, r₀, -, hr₀, hr₀eq⟩ := hattained 0
    have hlt := (le_iSup (fun t : K → ℝ ↦ (((∑ j, t j * x j) - g t : ℝ) : EReal))
      (0 : K → ℝ)).trans_lt hq1
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_sub] at hlt hr₀eq
    have h0 := EReal.coe_lt_coe_iff.1 hlt
    linarith
  -- separate `(x, c)` from the epigraph
  have hxc : ((x, c) : (K → ℝ) × ℝ) ∉ C := not_le.2 hq2
  obtain ⟨f, u, hfle, hfx⟩ := _root_.geometric_hahn_banach_closed_point hconv hclosed hxc
  set β : ℝ := f (0, 1) with hβ
  obtain ⟨tv, hfapp⟩ : ∃ tv : K → ℝ, ∀ (y : K → ℝ) (r : ℝ),
      f (y, r) = (∑ i, tv i * y i) + β * r := by
    set tvv : K → ℝ := fun i ↦ f ((fun j ↦ if i = j then (1 : ℝ) else 0), 0) with htvv
    refine ⟨tvv, fun y r ↦ ?_⟩
    have hsplit : ((y, r) : (K → ℝ) × ℝ) = (y, (0 : ℝ)) + r • ((0 : K → ℝ), (1 : ℝ)) := by
      simp
    have hy : f (y, (0 : ℝ)) = ∑ i, tvv i * y i := by
      have h := LinearMap.pi_apply_eq_sum_univ
        ((f : ((K → ℝ) × ℝ) →ₗ[ℝ] ℝ).comp (LinearMap.inl ℝ (K → ℝ) ℝ)) y
      simpa [htvv, LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply, smul_eq_mul,
        mul_comm] using h
    rw [hsplit, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, hy, smul_eq_mul,
      mul_comm]
  -- the separating functional cannot point upwards, because the epigraph is closed upwards
  have hβle : β ≤ 0 := by
    by_contra hβ'
    rw [not_le] at hβ'
    obtain ⟨y, r, hmem, -, -⟩ := hattained 0
    obtain ⟨n, hn⟩ := exists_nat_gt ((u - ((∑ i, tv i * y i) + β * r)) / β)
    have hmem' : ((y, r + n) : (K → ℝ) × ℝ) ∈ C :=
      hmem.trans (EReal.coe_le_coe_iff.2 (by simp))
    have h1 := hfle ((y, r + (n : ℝ)) : (K → ℝ) × ℝ) hmem'
    rw [hfapp] at h1
    rw [div_lt_iff₀ hβ'] at hn
    nlinarith
  rcases lt_or_eq_of_le hβle with hβneg | hβ0
  · -- a genuine separating hyperplane: the multiplier is `tv / (−β)`
    set τ : K → ℝ := fun j ↦ tv j / (-β) with hτ
    obtain ⟨y, r, hmem, -, hr⟩ := hattained τ
    have h1 := hfle ((y, r) : (K → ℝ) × ℝ) hmem
    have h2 := hfx
    rw [hfapp] at h1 h2
    have hnb : (0 : ℝ) < -β := by linarith
    have hβne : β ≠ 0 := ne_of_lt hβneg
    have hsum : ∀ z : K → ℝ, (∑ j, τ j * z j) = (∑ i, tv i * z i) / (-β) := fun z ↦ by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hτ]; ring
    have hstarτ := hstar τ
    rw [hsum] at hstarτ hr
    have hA : (∑ i, tv i * x i) ≤ (c + g τ) * (-β) := by
      rw [← div_le_iff₀ hnb]
      linarith
    have hβr : β * r = -(∑ i, tv i * y i) - β * g τ := by
      rw [hr]
      field_simp [hβne]
    linarith
  · -- a vertical hyperplane is excluded by scaling the multiplier
    have hβ0' : β = 0 := hβ0
    set δ : ℝ := (∑ i, tv i * x i) - u with hδ
    have hδpos : 0 < δ := by
      have h2 := hfx
      rw [hfapp, hβ0', zero_mul, add_zero] at h2
      linarith
    set lam : ℝ := (c + 1) / δ with hlam
    have hlampos : 0 < lam := by positivity
    obtain ⟨y, r, hmem, hr0, hr⟩ := hattained fun j ↦ lam * tv j
    have h1 := hfle ((y, r) : (K → ℝ) × ℝ) hmem
    rw [hfapp, hβ0', zero_mul, add_zero] at h1
    have hsumy : (∑ j, lam * tv j * y j) = lam * ∑ i, tv i * y i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hsumx : (∑ j, lam * tv j * x j) = lam * ∑ i, tv i * x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hstarτ := hstar fun j ↦ lam * tv j
    rw [hsumx] at hstarτ
    rw [hsumy] at hr
    have hδlt : lam * δ ≤ lam * ((∑ i, tv i * x i) - (∑ i, tv i * y i)) :=
      mul_le_mul_of_nonneg_left (by rw [hδ]; linarith) hlampos.le
    have hlamδ : lam * δ = c + 1 := by
      rw [hlam]
      field_simp
    nlinarith
