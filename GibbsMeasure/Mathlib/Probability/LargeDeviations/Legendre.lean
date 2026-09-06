/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.Convex
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

## Main results

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

The other half of the Legendre correspondence is the *attainment* of the conjugate, i.e. the
existence of a subgradient (Rockafellar, *Convex Analysis*, Theorem 23.4):

* `exists_setOf_le_mem_nhds_of_convex`: a quasiconvex `EReal`-valued function on a
  finite-dimensional real normed space is bounded above on a neighbourhood of every interior
  point of its essential domain `{J < ∞}`. A simplex around the point
  (`exists_mem_interior_convexHull_affineBasis`) is contained in the essential domain, and a
  sublevel set containing its vertices contains its convex hull.
* `exists_forall_add_le_of_eq_iSup_sub`: if `J` is the convex conjugate of a *continuous*
  `g : (K → ℝ) → ℝ` and is finite and bounded above near `x₀`, then the supremum defining
  `J x₀` is attained, so `J` has a **subgradient** at `x₀`:
  `J x₀ + t·(y − x₀) ≤ J y` for all `y`. A maximizing sequence is bounded — an affine minorant
  that is `ε`-optimal at `x₀` and below `J ≤ c` on a ball around `x₀` has slope at most
  `2(c − J x₀ + 1)/δ` — and a limit point of it attains the supremum by the continuity of `g`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set Topology

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

/-! ### Attainment of the conjugate: subgradients at interior points of the essential domain -/

/-- **A quasiconvex `EReal`-valued function is bounded above near an interior point of its
essential domain.** If every sublevel set `{J ≤ c}` is convex, `J` never takes the value `−∞`,
and `{J < ∞}` is a neighbourhood of `x₀`, then some sublevel set `{J ≤ c}` is a neighbourhood of
`x₀`. A simplex with `x₀` in its interior sits inside `{J < ∞}`
(`exists_mem_interior_convexHull_affineBasis`), the maximum `c` of `J` over its finitely many
vertices is finite, and the sublevel set `{J ≤ c}` is convex, hence contains the whole simplex. -/
theorem exists_setOf_le_mem_nhds_of_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {J : E → EReal}
    (hbot : ∀ x, J x ≠ ⊥) (hconv : ∀ c : ℝ, Convex ℝ {x | J x ≤ (c : EReal)})
    {x₀ : E} (hx₀ : {x | J x ≠ ⊤} ∈ 𝓝 x₀) :
    ∃ c : ℝ, {x : E | J x ≤ (c : EReal)} ∈ 𝓝 x₀ := by
  classical
  obtain ⟨b, hb₁, hb₂⟩ := exists_mem_interior_convexHull_affineBasis hx₀
  set c : ℝ := Finset.univ.sup' Finset.univ_nonempty fun i ↦ (J (b i)).toReal with hc
  have hrange : Set.range b ⊆ {x : E | J x ≤ (c : EReal)} := by
    rintro _ ⟨i, rfl⟩
    have hne : J (b i) ≠ ⊤ := hb₂ (subset_convexHull ℝ _ ⟨i, rfl⟩)
    show J (b i) ≤ (c : EReal)
    rw [← EReal.coe_toReal hne (hbot _)]
    exact EReal.coe_le_coe_iff.2 (Finset.le_sup' (fun i ↦ (J (b i)).toReal) (Finset.mem_univ i))
  have hsub : convexHull ℝ (Set.range b) ⊆ {x : E | J x ≤ (c : EReal)} :=
    convexHull_min hrange (hconv c)
  exact ⟨c, mem_nhds_iff.2 ⟨interior (convexHull ℝ (Set.range b)),
    interior_subset.trans hsub, isOpen_interior, hb₁⟩⟩

/-- **The conjugate of a continuous function is attained at an interior point of the essential
domain**, i.e. **a rate function has a subgradient there** (Rockafellar, *Convex Analysis*,
Theorem 23.4). Let `J : (K → ℝ) → EReal` be the convex conjugate `J x = sup_t (t·x − g t)` of a
continuous `g : (K → ℝ) → ℝ`, let `J x₀` be finite, and let `J` be bounded above by `c` on a
neighbourhood of `x₀`. Then there is `t` with

`J x₀ + t·(y − x₀) ≤ J y` for all `y`,

namely a `t` attaining the supremum at `x₀`.

The maximizing sequence `t_n` — with `t_n·x₀ − g t_n > J x₀ − 1/(n+1)` — is bounded: on a ball
`B(x₀, δ)` on which `J ≤ c`, the affine minorant `y ↦ t_n·y − g t_n` is at most `c`, so
`t_n·(y − x₀) ≤ c − J x₀ + 1` there, which bounds every coordinate of `t_n` by
`2(|c| + |J x₀| + 1)/δ`. A limit point `t₀` of the sequence then attains the supremum, by the
continuity of `g`. -/
theorem exists_forall_add_le_of_eq_iSup_sub {K : Type*} [Fintype K] {J : (K → ℝ) → EReal}
    {g : (K → ℝ) → ℝ} (hg : Continuous g)
    (hJ : ∀ x : K → ℝ, J x = ⨆ t : K → ℝ, (((∑ j, t j * x j) - g t : ℝ) : EReal))
    {x₀ : K → ℝ} {c : ℝ} (hnhds : {x : K → ℝ | J x ≤ (c : EReal)} ∈ 𝓝 x₀)
    (hfin : J x₀ ≠ ⊤) :
    ∃ t : K → ℝ, ∀ y : K → ℝ, J x₀ + ((∑ j, t j * (y j - x₀ j) : ℝ) : EReal) ≤ J y := by
  classical
  set F : (K → ℝ) → ℝ := fun t ↦ (∑ j, t j * x₀ j) - g t with hF
  have hFcont : Continuous F := by
    refine Continuous.sub (continuous_finsetSum _ fun j _ ↦ ?_) hg
    exact (continuous_apply j).mul continuous_const
  -- `J x₀` is a real number
  have hbot : J x₀ ≠ ⊥ := by
    have h := (le_iSup (fun t : K → ℝ ↦ ((F t : ℝ) : EReal)) (0 : K → ℝ)).trans_eq (hJ x₀).symm
    exact fun hc' ↦ by simp [hc'] at h
  set r₀ : ℝ := (J x₀).toReal with hr₀def
  have hr₀ : J x₀ = (r₀ : EReal) := (EReal.coe_toReal hfin hbot).symm
  have hle : ∀ t : K → ℝ, F t ≤ r₀ := by
    intro t
    have h := (le_iSup (fun t : K → ℝ ↦ ((F t : ℝ) : EReal)) t).trans_eq (hJ x₀).symm
    rw [hr₀] at h
    exact EReal.coe_le_coe_iff.1 h
  -- a maximizing sequence
  have hex : ∀ n : ℕ, ∃ t : K → ℝ, r₀ - 1 / (n + 1 : ℝ) < F t := by
    intro n
    have hlt : ((r₀ - 1 / (n + 1 : ℝ) : ℝ) : EReal) < J x₀ := by
      rw [hr₀]
      exact EReal.coe_lt_coe_iff.2 (by
        have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        linarith)
    rw [hJ x₀, lt_iSup_iff] at hlt
    obtain ⟨t, ht⟩ := hlt
    exact ⟨t, EReal.coe_lt_coe_iff.1 ht⟩
  choose t ht using hex
  -- the maximizing sequence is bounded
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set R : ℝ := 2 * (|c| + |r₀| + 1) / δ with hR
  have hbound : ∀ n : ℕ, ‖t n‖ ≤ R := by
    intro n
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ ?_
    rw [Real.norm_eq_abs, abs_le]
    have key : ∀ ε : ℝ, ε = 1 ∨ ε = -1 → ε * t n j ≤ R := by
      intro ε hε
      set y : K → ℝ := Function.update x₀ j (x₀ j + ε * (δ / 2)) with hy
      have hyx : ∀ k, y k - x₀ k = if k = j then ε * (δ / 2) else 0 := by
        intro k
        by_cases hk : k = j
        · subst hk; simp [hy]
        · simp [hy, hk]
      have hdist : dist y x₀ < δ := by
        rw [dist_eq_norm]
        refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun k ↦ ?_)
          (by linarith : δ / 2 < δ)
        rw [Real.norm_eq_abs]
        show |y k - x₀ k| ≤ δ / 2
        rw [hyx k]
        by_cases hk : k = j
        · rcases hε with rfl | rfl <;> simp [hk, abs_of_pos (by linarith : (0:ℝ) < δ / 2)]
        · simp only [hk, if_false, abs_zero]
          linarith
      have hyJ : J y ≤ (c : EReal) := hball (Metric.mem_ball.2 hdist)
      have hFy : (∑ j', t n j' * y j') - g (t n) ≤ c := by
        have h := (le_iSup (fun s : K → ℝ ↦
          (((∑ j', s j' * y j') - g s : ℝ) : EReal)) (t n)).trans_eq (hJ y).symm
        exact EReal.coe_le_coe_iff.1 (h.trans hyJ)
      have hdiff : (∑ j', t n j' * y j') - (∑ j', t n j' * x₀ j') = t n j * (ε * (δ / 2)) := by
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single j]
        · rw [← mul_sub, hyx j, if_pos rfl]
        · intro k _ hk
          rw [← mul_sub, hyx k, if_neg hk, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hlow := ht n
      have h1 : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      have hεδ : t n j * (ε * (δ / 2)) ≤ c - r₀ + 1 := by
        rw [← hdiff]
        have : (∑ j', t n j' * x₀ j') - g (t n) = F (t n) := rfl
        linarith [hFy, hlow, (by
          rw [div_le_one (by positivity)]
          linarith [Nat.cast_nonneg (α := ℝ) n] : 1 / (n + 1 : ℝ) ≤ 1)]
      have hmul : ε * t n j * (δ / 2) ≤ c - r₀ + 1 := by
        calc ε * t n j * (δ / 2) = t n j * (ε * (δ / 2)) := by ring
          _ ≤ _ := hεδ
      have hcr : c - r₀ + 1 ≤ |c| + |r₀| + 1 := by
        have := le_abs_self c
        have := neg_abs_le r₀
        linarith
      rw [hR, le_div_iff₀ hδ]
      nlinarith [hmul, hcr]
    constructor
    · have := key (-1) (Or.inr rfl); linarith [this]
    · have := key 1 (Or.inl rfl); linarith [this]
  -- a cluster point of the maximizing sequence
  have hcompact : IsCompact (Metric.closedBall (0 : K → ℝ) R) := isCompact_closedBall _ _
  have hmem : ∀ n, t n ∈ Metric.closedBall (0 : K → ℝ) R := fun n ↦ by
    simpa [Metric.mem_closedBall, dist_zero_right] using hbound n
  obtain ⟨t₀, -, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  -- `F (t n) → r₀`, hence `F t₀ = r₀`
  have hFt : Tendsto (fun n ↦ F (t n)) atTop (𝓝 r₀) := by
    have hlow : ∀ n : ℕ, r₀ - 1 / (n + 1 : ℝ) ≤ F (t n) := fun n ↦ (ht n).le
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ ↦ r₀ - 1 / (n + 1 : ℝ))
      (h := fun _ : ℕ ↦ r₀) ?_ tendsto_const_nhds hlow (fun n ↦ hle _)
    have h0 : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hconst : Tendsto (fun _ : ℕ ↦ r₀) atTop (𝓝 r₀) := tendsto_const_nhds
    simpa using hconst.sub h0
  have hFt₀ : F t₀ = r₀ := by
    refine tendsto_nhds_unique ((hFcont.tendsto t₀).comp hlim) (hFt.comp hφ.tendsto_atTop)
  refine ⟨t₀, fun y ↦ ?_⟩
  have hy : (((∑ j, t₀ j * y j) - g t₀ : ℝ) : EReal) ≤ J y :=
    (le_iSup (fun s : K → ℝ ↦ (((∑ j, s j * y j) - g s : ℝ) : EReal)) t₀).trans_eq (hJ y).symm
  refine le_trans (le_of_eq ?_) hy
  rw [hr₀, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  have hsum : (∑ j, t₀ j * (y j - x₀ j)) = (∑ j, t₀ j * y j) - ∑ j, t₀ j * x₀ j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have : F t₀ = (∑ j, t₀ j * x₀ j) - g t₀ := rfl
  rw [hsum]
  rw [this] at hFt₀
  linarith
