/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.PiProd
public import Mathlib.Analysis.PSeries

/-!
# The `p`-series on the lattice `ℤ^D`

`∑_{i ∈ ℤ^D} (e ∨ ‖i‖)^{-p} < ∞` for every real `p > D`, where `‖·‖` is the sup norm.  Cutting
the summand off at `e` removes the singularity at the origin, so no term has to be excluded.

The proof splits the exponent evenly over the `D` coordinates: with `q = p/D > 1`,
`(e ∨ ‖i‖)^{-p} = ∏_c (e ∨ ‖i‖)^{-q} ≤ ∏_c (e ∨ |i_c|)^{-q}`, and the right-hand side is
summable by `summable_pi_prod` and the one-dimensional `p`-series `summable_abs_int_rpow`.

## Main results

* `summable_max_exp_norm_rpow`
-/

@[expose] public section

/-- The one-dimensional cut-off `p`-series `∑_{k ∈ ℤ} (e ∨ |k|)^{-q} < ∞` for `q > 1`. -/
theorem summable_max_exp_abs_int_rpow {q : ℝ} (hq : 1 < q) :
    Summable fun k : ℤ ↦ (max (Real.exp 1) |(k : ℝ)|) ^ (-q) := by
  refine Summable.of_norm_bounded_eventually (g := fun k : ℤ ↦ |(k : ℝ)| ^ (-q))
    (Real.summable_abs_int_rpow hq) ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset fun k hk ↦ ?_
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hk ⊢
  by_contra hk0
  refine hk ?_
  have hkpos : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hk0)
  have hle : |(k : ℝ)| ≤ max (Real.exp 1) |(k : ℝ)| := le_max_right _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_trans (Real.exp_pos 1).le
    (le_max_left _ _)) _)]
  exact Real.rpow_le_rpow_of_nonpos hkpos hle (by linarith)

/-- **The lattice `p`-series.**  `∑_{i ∈ ℤ^D} (e ∨ ‖i‖)^{-p} < ∞` for every `p > D`, the norm
being the sup norm on `ℤ^D`. -/
theorem summable_max_exp_norm_rpow {D : ℕ} {p : ℝ} (hp : (D : ℝ) < p) :
    Summable fun i : Fin D → ℤ ↦ (max (Real.exp 1) ‖i‖) ^ (-p) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    have : Finite (Fin 0 → ℤ) := by
      have : Unique (Fin 0 → ℤ) := Pi.uniqueOfIsEmpty _
      exact Finite.of_subsingleton
    exact Summable.of_finite
  · have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    set q : ℝ := p / D with hqdef
    have hq : 1 < q := by
      rw [hqdef, lt_div_iff₀ hDpos]
      linarith
    have hqnp : -q ≤ 0 := by linarith
    have hf0 : ∀ k : ℤ, 0 ≤ (max (Real.exp 1) |(k : ℝ)|) ^ (-q) := fun k ↦
      Real.rpow_nonneg (le_trans (Real.exp_pos 1).le (le_max_left _ _)) _
    refine Summable.of_nonneg_of_le (fun i ↦ Real.rpow_nonneg
      (le_trans (Real.exp_pos 1).le (le_max_left _ _)) _) (fun i ↦ ?_)
      (summable_pi_prod (summable_max_exp_abs_int_rpow hq) hf0)
    have hbase : (0 : ℝ) < max (Real.exp 1) ‖i‖ :=
      lt_of_lt_of_le (Real.exp_pos 1) (le_max_left _ _)
    have hsplit : (max (Real.exp 1) ‖i‖) ^ (-p)
        = ∏ _c : Fin D, (max (Real.exp 1) ‖i‖) ^ (-q) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast _ D,
        ← Real.rpow_mul hbase.le]
      rw [hqdef]
      field_simp
    rw [hsplit]
    refine Finset.prod_le_prod₀ (fun c _ ↦ Real.rpow_nonneg hbase.le _) fun c _ ↦ ?_
    have hc : max (Real.exp 1) |(i c : ℝ)| ≤ max (Real.exp 1) ‖i‖ := by
      refine max_le_max le_rfl ?_
      have := norm_le_pi_norm i c
      rwa [Int.norm_eq_abs] at this
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le (Real.exp_pos 1) (le_max_left _ _)) hc hqnp
