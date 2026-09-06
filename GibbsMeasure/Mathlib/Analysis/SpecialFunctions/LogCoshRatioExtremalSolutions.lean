/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.LogCoshRatioFixedPoint

/-!
# The extremal solutions of the tree recursion

Georgii's Theorem (12.31) uses, besides the *number* of solutions of the fixed point equation
(12.22) `t = h + d φ_J(t)`, the *smallest* and *largest* of them, `t₋` and `t₊`: step 1) of his
proof squeezes the parameters of an arbitrary boundary law between them, and step 3) compares an
arbitrary Gibbs measure with the completely homogeneous chains `μ_{t₋}`, `μ_{t₊}`.

For a ferromagnetic coupling `J > 0` these extremal solutions exist:
`Real.exists_isGreatest_treeField_eq` and `Real.exists_isLeast_treeField_eq` are exactly
`Real.exists_treeField_eq_and_forall_le` and `Real.exists_treeField_eq_and_forall_ge` applied to
the family of *all* solutions, which satisfies the required bound and monotone step because a
solution is a fixed point of the increasing map `t ↦ h + d φ_J(t)`.
-/

@[expose] public section

namespace Real

variable {J h : ℝ} {d : ℕ}

/-- Every solution of (12.22) is bounded above by `h + d J` and below by `h - d J`. -/
theorem abs_sub_le_of_treeField_eq (hJ : 0 < J) {s : ℝ} (hs : treeField d J s = h) :
    s ≤ h + d * J ∧ h - d * J ≤ s := by
  have hfix : s = h + d * logCoshRatio J s := by rw [treeField] at hs; linarith
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  constructor
  · nlinarith [(logCoshRatio_lt hJ s).le]
  · nlinarith [(neg_lt_logCoshRatio hJ s).le]

/-- **Georgii, the largest solution `t₊` of (12.22).** For `J > 0` the fixed point equation
(12.22) has a greatest solution. -/
theorem exists_isGreatest_treeField_eq (hJ : 0 < J) (d : ℕ) (h : ℝ) :
    ∃ p, treeField d J p = h ∧ ∀ s, treeField d J s = h → s ≤ p := by
  have hstep : ∀ c : ℝ, (∀ s : {s : ℝ // treeField d J s = h}, (s : ℝ) ≤ c) →
      ∀ s : {s : ℝ // treeField d J s = h}, (s : ℝ) ≤ treeRecursion d J h c := by
    intro c hc s
    have hfix : (s : ℝ) = h + d * logCoshRatio J s := by
      have hs := s.2; rw [treeField] at hs; linarith
    have hmono := (monotone_logCoshRatio hJ.le) (hc s)
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    simp only [treeRecursion]
    nlinarith
  obtain ⟨p, hp, hle⟩ := exists_treeField_eq_and_forall_le hJ
    (fun s : {s : ℝ // treeField d J s = h} ↦ (abs_sub_le_of_treeField_eq hJ s.2).1) hstep
  exact ⟨p, hp, fun s hs ↦ hle ⟨s, hs⟩⟩

/-- **Georgii, the smallest solution `t₋` of (12.22).** For `J > 0` the fixed point equation
(12.22) has a least solution. -/
theorem exists_isLeast_treeField_eq (hJ : 0 < J) (d : ℕ) (h : ℝ) :
    ∃ p, treeField d J p = h ∧ ∀ s, treeField d J s = h → p ≤ s := by
  have hstep : ∀ c : ℝ, (∀ s : {s : ℝ // treeField d J s = h}, c ≤ (s : ℝ)) →
      ∀ s : {s : ℝ // treeField d J s = h}, treeRecursion d J h c ≤ (s : ℝ) := by
    intro c hc s
    have hfix : (s : ℝ) = h + d * logCoshRatio J s := by
      have hs := s.2; rw [treeField] at hs; linarith
    have hmono := (monotone_logCoshRatio hJ.le) (hc s)
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    simp only [treeRecursion]
    nlinarith
  obtain ⟨p, hp, hle⟩ := exists_treeField_eq_and_forall_ge hJ
    (fun s : {s : ℝ // treeField d J s = h} ↦ (abs_sub_le_of_treeField_eq hJ s.2).2) hstep
  exact ⟨p, hp, fun s hs ↦ hle ⟨s, hs⟩⟩

/-! ### The backward orbit of `ψ = h + d φ_J` between two fixed points

Georgii, step 4) of the proof of Theorem (12.31): between two solutions `a < b` of (12.22) the
increasing map `ψ = h + d φ_J` is a bijection of `]a, b[` onto itself, so every `t ∈ ]a, b[` has a
*backward* orbit `(u_n)` with `u_1 = t` and `u_n = ψ(u_{n+1})`. Together with the second sequence
`v` below it produces the inhomogeneous boundary laws of step 4). -/

/-- For `J > 0` and `d ≥ 1` the recursion `ψ = h + d φ_J` of (12.22) is strictly increasing. -/
theorem strictMono_treeRecursion (hJ : 0 < J) (hd : 1 ≤ d) (h : ℝ) :
    StrictMono (treeRecursion d J h) := fun a b hab ↦ by
  have hlt := strictMono_logCoshRatio hJ hab
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [treeRecursion]
  nlinarith

/-- Between two fixed points `a < b` of `ψ`, `ψ` maps `]a, b[` *onto* `]a, b[`. -/
theorem exists_mem_Ioo_treeRecursion_eq {a b : ℝ}
    (ha : treeRecursion d J h a = a) (hb : treeRecursion d J h b = b) (hab : a < b)
    {y : ℝ} (hy : y ∈ Set.Ioo a b) : ∃ x ∈ Set.Ioo a b, treeRecursion d J h x = y := by
  have hsub := intermediate_value_Ioo hab.le
    (continuous_treeRecursion J d h).continuousOn (a := a) (b := b)
  rw [ha, hb] at hsub
  obtain ⟨x, hx, hxy⟩ := hsub hy
  exact ⟨x, hx, hxy⟩

/-- `ψ` maps `]a, b[` *into* `]a, b[` when `a, b` are fixed points. -/
theorem treeRecursion_mem_Ioo (hJ : 0 < J) (hd : 1 ≤ d) {a b : ℝ}
    (ha : treeRecursion d J h a = a) (hb : treeRecursion d J h b = b) {y : ℝ}
    (hy : y ∈ Set.Ioo a b) : treeRecursion d J h y ∈ Set.Ioo a b :=
  ⟨ha ▸ strictMono_treeRecursion hJ hd h hy.1, hb ▸ strictMono_treeRecursion hJ hd h hy.2⟩

/-- **Georgii, step 4) of the proof of Theorem (12.31).** The backward orbit of `t` under the
recursion `ψ = h + d φ_J` of (12.22): `u_0 = ψ(t)`, `u_1 = t`, and `u_n = ψ(u_{n+1})` for all `n`.
It is Georgii's sequence `(t_n)_{n ≥ 1}` with `t_1 = t`, extended by `t_0 = ψ(t_1)`. -/
noncomputable def treeBackOrbit (d : ℕ) (J h t : ℝ) : ℕ → ℝ
  | 0 => treeRecursion d J h t
  | n + 1 => Function.invFun (treeRecursion d J h) (treeBackOrbit d J h t n)

@[simp] lemma treeBackOrbit_zero (d : ℕ) (J h t : ℝ) :
    treeBackOrbit d J h t 0 = treeRecursion d J h t := rfl

lemma treeBackOrbit_succ (d : ℕ) (J h t : ℝ) (n : ℕ) :
    treeBackOrbit d J h t (n + 1)
      = Function.invFun (treeRecursion d J h) (treeBackOrbit d J h t n) := rfl

section Orbit

variable (hJ : 0 < J) (hd : 1 ≤ d) {a b t : ℝ}
  (ha : treeRecursion d J h a = a) (hb : treeRecursion d J h b = b) (hab : a < b)
  (ht : t ∈ Set.Ioo a b)

include hJ hd ha hb hab ht

/-- Every term of the backward orbit stays in `]a, b[`. -/
theorem treeBackOrbit_mem_Ioo (n : ℕ) : treeBackOrbit d J h t n ∈ Set.Ioo a b := by
  induction n with
  | zero => exact treeRecursion_mem_Ioo hJ hd ha hb ht
  | succ n ih =>
    obtain ⟨x, hx, hxy⟩ := exists_mem_Ioo_treeRecursion_eq ha hb hab ih
    rw [treeBackOrbit_succ, ← hxy,
      Function.leftInverse_invFun (strictMono_treeRecursion hJ hd h).injective x]
    exact hx

/-- **Georgii, step 4): `u_n = h + d φ_J(u_{n+1})`.** -/
theorem treeRecursion_treeBackOrbit_succ (n : ℕ) :
    treeRecursion d J h (treeBackOrbit d J h t (n + 1)) = treeBackOrbit d J h t n := by
  obtain ⟨x, -, hxy⟩ := exists_mem_Ioo_treeRecursion_eq ha hb hab
    (treeBackOrbit_mem_Ioo hJ hd ha hb hab ht n)
  rw [treeBackOrbit_succ]
  exact Function.invFun_eq ⟨x, hxy⟩

omit ha hb hab ht in
/-- `u_1 = t`: the backward orbit starts at `t`. -/
theorem treeBackOrbit_one : treeBackOrbit d J h t 1 = t := by
  rw [treeBackOrbit_succ, treeBackOrbit_zero]
  exact Function.leftInverse_invFun (strictMono_treeRecursion hJ hd h).injective t

end Orbit

/-- **Georgii, step 4): the backward orbit determines `t`.** For `n ≥ 1` the map `t ↦ u_n` is
injective on `]a, b[`: applying `ψ` `n` times to `u_{n+1}` returns `u_1 = t`. -/
theorem treeBackOrbit_inj (hJ : 0 < J) (hd : 1 ≤ d) {a b : ℝ}
    (ha : treeRecursion d J h a = a) (hb : treeRecursion d J h b = b) (hab : a < b) :
    ∀ (n : ℕ) {t s : ℝ}, t ∈ Set.Ioo a b → s ∈ Set.Ioo a b →
      treeBackOrbit d J h t (n + 1) = treeBackOrbit d J h s (n + 1) → t = s := by
  intro n
  induction n with
  | zero =>
    intro t s _ _ hts
    rwa [treeBackOrbit_one hJ hd, treeBackOrbit_one hJ hd] at hts
  | succ n ih =>
    intro t s ht hs hts
    refine ih ht hs ?_
    rw [← treeRecursion_treeBackOrbit_succ hJ hd ha hb hab ht (n + 1),
      ← treeRecursion_treeBackOrbit_succ hJ hd ha hb hab hs (n + 1), hts]

/-- **Georgii, step 4) of the proof of Theorem (12.31).** The second sequence attached to a
backward orbit: the parameters of the bonds *pointing away* from the root. `v_0 = u_0` and
`v_{n+1} = h + φ_J(v_n) + (d - 1) φ_J(u_{n+2})`. -/
noncomputable def treeAwayOrbit (d : ℕ) (J h t : ℝ) : ℕ → ℝ
  | 0 => treeBackOrbit d J h t 0
  | n + 1 => h + logCoshRatio J (treeAwayOrbit d J h t n)
      + ((d : ℝ) - 1) * logCoshRatio J (treeBackOrbit d J h t (n + 2))

@[simp] lemma treeAwayOrbit_zero (d : ℕ) (J h t : ℝ) :
    treeAwayOrbit d J h t 0 = treeRecursion d J h t := rfl

lemma treeAwayOrbit_succ (d : ℕ) (J h t : ℝ) (n : ℕ) :
    treeAwayOrbit d J h t (n + 1)
      = h + logCoshRatio J (treeAwayOrbit d J h t n)
        + ((d : ℝ) - 1) * logCoshRatio J (treeBackOrbit d J h t (n + 2)) := rfl

end Real
