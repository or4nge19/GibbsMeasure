/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Fourier.AddCircleMulti
public import GibbsMeasure.Specification.InfraredBoundTheorem
public import GibbsMeasure.Specification.HeisenbergGibbsInclusion
public import GibbsMeasure.Topology.LocalConvergenceIntegral

/-!
# Georgii, Theorem (20.15): spontaneous magnetisation from the infrared bound

Work in progress.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Matrix MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Georgii's `G_Λ`, the dual group of the discrete torus -/

section DualBox

variable {d L : ℕ}

/-- The period of the cube `Λ(N)`, `N = L + 1`, as a natural number. -/
theorem intBoxLen_eq_natCast (L : ℕ) : Potential.intBoxLen L = ((2 * (L + 1) : ℕ) : ℤ) := by
  rw [Potential.intBoxLen]; push_cast; ring

variable (d L) in
/-- The parametrisation `k ↦ (k/2N)` of Georgii's `G_Λ` by the discrete torus, as an embedding. -/
def dualBoxEmb : (Fin (d + 1) → ZMod (2 * (L + 1))) ↪ UnitAddTorus (Fin (d + 1)) :=
  ⟨ZMod.toUnitAddTorus, ZMod.toUnitAddTorus_injective⟩

@[simp] theorem dualBoxEmb_apply (k : Fin (d + 1) → ZMod (2 * (L + 1))) :
    dualBoxEmb d L k = ZMod.toUnitAddTorus k := rfl

variable (d L) in
/-- **Georgii's `G_Λ`.**  The dual group of the discrete torus `Λ = (ℤ/2N)^{d+1}`: the group of
`2N`-th roots of unity in each coordinate of `G = (ℝ/ℤ)^{d+1}`, i.e. the `2N`-torsion subgroup
(`mem_dualBox`).  It is the image of the discrete torus under `k ↦ k/2N`, so `|G_Λ| = |Λ|`
(`card_dualBox`). -/
def dualBox : Finset (UnitAddTorus (Fin (d + 1))) := Finset.univ.map (dualBoxEmb d L)

/-- **`G_Λ` is the `2N`-torsion of `G`**, Georgii's `{w ∈ K : w^{2n} = 1}^d`. -/
@[simp] theorem mem_dualBox {x : UnitAddTorus (Fin (d + 1))} :
    x ∈ dualBox d L ↔ Potential.intBoxLen L • x = 0 := by
  rw [dualBox, Finset.mem_map]
  rw [intBoxLen_eq_natCast]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact ZMod.zsmul_toUnitAddTorus k
  · intro hx
    obtain ⟨k, hk⟩ := (Set.ext_iff.1 (ZMod.range_toUnitAddTorus
      (ι := Fin (d + 1)) (N := 2 * (L + 1))) x).2 hx
    exact ⟨k, Finset.mem_univ k, hk⟩

/-- **Georgii's `|G_Λ| = |Λ|`.** -/
@[simp] theorem card_dualBox :
    (dualBox d L).card = Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) := by
  rw [dualBox, Finset.card_map, Finset.card_univ]

/-- Summing over `G_Λ` is summing over the discrete torus. -/
theorem sum_dualBox {A : Type*} [AddCommMonoid A] (f : UnitAddTorus (Fin (d + 1)) → A) :
    ∑ z ∈ dualBox d L, f z = ∑ k : Fin (d + 1) → ZMod (2 * (L + 1)), f (ZMod.toUnitAddTorus k) :=
  Finset.sum_map _ _ _

/-- The neutral element `1 = (1, …, 1)` of `G` belongs to `G_Λ`. -/
@[simp] theorem zero_mem_dualBox : (0 : UnitAddTorus (Fin (d + 1))) ∈ dualBox d L := by
  simp

/-- **Orthogonality of the characters of `G_Λ`**, Georgii's "the orthogonality of the mappings
`z ↦ z^i` (`i ∈ Λ`) on `G_Λ`":

`∑_{z ∈ G_Λ} z^i = |Λ| · 1_{i ≡ 0 mod Λ}`. -/
theorem sum_dualBox_mFourier (m : Fin (d + 1) → ℤ) :
    (∑ z ∈ dualBox d L, mFourier m z)
      = if latticeToTorus L m = 0 then (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℂ)
        else 0 := by
  rw [sum_dualBox]
  exact UnitAddTorus.sum_mFourier_toUnitAddTorus m

/-- Orthogonality in the form used for the inversion: the characters indexed by the *torus* are
orthogonal, `∑_{z ∈ G_Λ} z^v = |Λ| 1_{v = 0}` for `v ∈ Λ`. -/
theorem sum_dualBox_mFourier_torusToLattice (v : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∑ z ∈ dualBox d L, mFourier (torusToLattice L v) z)
      = if v = 0 then (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℂ) else 0 := by
  rw [sum_dualBox_mFourier, latticeToTorus_torusToLattice]

end DualBox

/-! ### The inversion formula -/

section Inversion

variable {d L n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν]
  {x : UnitAddTorus (Fin (d + 1))}

/-- The reduction of the lattice modulo the periods is odd. -/
theorem latticeToTorus_neg (m : Fin (d + 1) → ℤ) :
    latticeToTorus L (-m) = -latticeToTorus L m := by
  funext c; simp

/-- **The correlation function of the periodic Gibbs distribution is even**, `°γ_Λ^Φ(σ_0·σ_{-i})
= °γ_Λ^Φ(σ_0·σ_i)`: a consequence of the shift invariance of `°γ_Λ^Φ` on the torus. -/
theorem integral_dotProduct_heisenbergPeriodicGibbsDist_neg
    (i : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∫ ω, ω 0 ⬝ᵥ ω (-i) ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
      = ∫ ω, ω 0 ⬝ᵥ ω i ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) := by
  have h := integral_dotProduct_heisenbergPeriodicGibbsDist_sub (L := L) (n := n) (J := J)
    (ν := ν) 0 i
  rw [zero_sub] at h
  exact h.symm

/-- **`C_Λ^Φ` is the value of the complex Fourier sum**, not just its real part: on `G_Λ` the
series `∑_{i ∈ Λ} z^i °γ_Λ^Φ(σ_0·σ_i)` is real, because the correlation is even and `z^{-i}` is
the conjugate of `z^i`. -/
theorem ofReal_correlationFourier (hx : Potential.intBoxLen L • x = 0) :
    ((correlationFourier L n J ν x : ℝ) : ℂ)
      = ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
          ((∫ ω, ω 0 ⬝ᵥ ω i ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) : ℝ) : ℂ)
            * mFourier (torusToLattice L i) x := by
  classical
  set c : (Fin (d + 1) → ZMod (2 * (L + 1))) → ℝ :=
    fun i ↦ ∫ ω, ω 0 ⬝ᵥ ω i ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) with hc
  refine Complex.conj_eq_iff_re.1 ?_
  rw [map_sum]
  have hstep : ∀ i : Fin (d + 1) → ZMod (2 * (L + 1)),
      conj (((c i : ℝ) : ℂ) * mFourier (torusToLattice L i) x)
        = ((c i : ℝ) : ℂ) * mFourier (torusToLattice L (-i)) x := by
    intro i
    rw [map_mul, Complex.conj_ofReal, ← mFourier_neg]
    congr 1
    refine mFourier_congr_of_latticeToTorus_eq hx ?_
    rw [latticeToTorus_neg, latticeToTorus_torusToLattice, latticeToTorus_torusToLattice]
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i]
  have hcneg : ∀ i, c (-i) = c i := fun i ↦
    integral_dotProduct_heisenbergPeriodicGibbsDist_neg (L := L) (n := n) (J := J) (ν := ν) i
  refine Fintype.sum_equiv (Equiv.neg (Fin (d + 1) → ZMod (2 * (L + 1))))
    (fun i ↦ ((c i : ℝ) : ℂ) * mFourier (torusToLattice L (-i)) x)
    (fun i ↦ ((c i : ℝ) : ℂ) * mFourier (torusToLattice L i) x) fun i ↦ ?_
  simp only [Equiv.neg_apply]
  rw [hcneg i]

/-- **Georgii's inversion formula** in the proof of (20.15):

`|Λ|⁻¹ ∑_{z ∈ G_Λ} (1 - z^{-j}) C_Λ^Φ(z) = °γ_Λ^Φ(|σ_0|²) - °γ_Λ^Φ(σ_0·σ_j)`.

The imaginary part of `z^{-j}` drops out because `C_Λ^Φ` is real and `G_Λ` is stable under
conjugation; the statement is the real form, multiplied by `|Λ|`. -/
theorem sum_dualBox_one_sub_re_mul_correlationFourier
    (j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∑ z ∈ dualBox d L,
        (1 - (mFourier (torusToLattice L j) z).re) * correlationFourier L n J ν z)
      = (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℝ)
        * ((∫ ω, ω 0 ⬝ᵥ ω 0 ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
          - ∫ ω, ω 0 ⬝ᵥ ω j ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν)) := by
  classical
  set M := (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℂ) with hM
  set c : (Fin (d + 1) → ZMod (2 * (L + 1))) → ℝ :=
    fun i ↦ ∫ ω, ω 0 ⬝ᵥ ω i ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) with hc
  -- the complex sum
  have hT : (∑ z ∈ dualBox d L,
        (1 - conj (mFourier (torusToLattice L j) z)) * ((correlationFourier L n J ν z : ℝ) : ℂ))
      = M * (((c 0 : ℝ) : ℂ) - ((c j : ℝ) : ℂ)) := by
    have hexpand : ∀ z ∈ dualBox d L,
        (1 - conj (mFourier (torusToLattice L j) z)) * ((correlationFourier L n J ν z : ℝ) : ℂ)
          = ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ((c i : ℝ) : ℂ) *
              (mFourier (torusToLattice L i) z - mFourier (torusToLattice L (i - j)) z) := by
      intro z hz
      have hzt : Potential.intBoxLen L • z = 0 := mem_dualBox.1 hz
      rw [ofReal_correlationFourier hzt, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← mFourier_torusToLattice_mul_conj hzt i j]
      ring
    rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
    have hinner : ∀ i : Fin (d + 1) → ZMod (2 * (L + 1)),
        (∑ z ∈ dualBox d L, ((c i : ℝ) : ℂ) *
            (mFourier (torusToLattice L i) z - mFourier (torusToLattice L (i - j)) z))
          = ((c i : ℝ) : ℂ) * ((if i = 0 then M else 0) - (if i - j = 0 then M else 0)) := by
      intro i
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_dualBox_mFourier_torusToLattice,
        sum_dualBox_mFourier_torusToLattice]
    rw [Finset.sum_congr rfl fun i _ ↦ hinner i]
    have hsplit : ∀ i : Fin (d + 1) → ZMod (2 * (L + 1)),
        ((c i : ℝ) : ℂ) * ((if i = 0 then M else 0) - (if i - j = 0 then M else 0))
          = (if i = 0 then ((c i : ℝ) : ℂ) * M else 0)
            - (if i = j then ((c i : ℝ) : ℂ) * M else 0) := by
      intro i
      simp only [sub_eq_zero]
      rw [mul_sub, mul_ite, mul_ite]
      simp only [mul_zero]
    rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ (0 : Fin (d + 1) → ZMod (2 * (L + 1)))
        (fun i ↦ ((c i : ℝ) : ℂ) * M),
      Finset.sum_ite_eq' Finset.univ j (fun i ↦ ((c i : ℝ) : ℂ) * M)]
    simp only [Finset.mem_univ, ite_true]
    ring
  -- take real parts
  have hre : ∀ z ∈ dualBox d L,
      ((1 - conj (mFourier (torusToLattice L j) z)) * ((correlationFourier L n J ν z : ℝ) : ℂ)).re
        = (1 - (mFourier (torusToLattice L j) z).re) * correlationFourier L n J ν z := by
    intro z _
    rw [Complex.mul_re]
    simp [Complex.sub_re, Complex.sub_im]
  have := congrArg Complex.re hT
  rw [Complex.re_sum, Finset.sum_congr rfl hre] at this
  rw [this, hM, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    Complex.ofReal_re]

end Inversion

/-! ### Comment (20.17)(1): the transform is strictly maximal at the neutral element -/

section Irreducible

variable {D : ℕ} {J : (Fin D → ℤ) → ℝ}

variable (J) in
/-- **Georgii's irreducibility of a coupling** (§20.2, above (20.15)): "there exists no proper
subgroup of `S` containing the support `{i ∈ S : J(i) ≠ 0}` of `J`".

Georgii remarks that this is no loss of generality: otherwise `γ^Φ` is a product specification
in the sense of (7.18), at least on `Ω_*`. -/
def IsIrreducibleCoupling : Prop :=
  ∀ H : AddSubgroup (Fin D → ℤ), Function.support J ⊆ (H : Set (Fin D → ℤ)) → H = ⊤

/-- The kernel of the character `i ↦ z^i` of `S = ℤ^d`, for a point `z` of the dual group `G`. -/
def mFourierKer (x : UnitAddTorus (Fin D)) : AddSubgroup (Fin D → ℤ) where
  carrier := {m | mFourier m x = 1}
  zero_mem' := by simp [mFourier_zero]
  add_mem' ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [mFourier_add, ha, hb, one_mul]
  neg_mem' ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [mFourier_neg, ha, map_one]

@[simp] theorem mem_mFourierKer {x : UnitAddTorus (Fin D)} {m : Fin D → ℤ} :
    m ∈ mFourierKer x ↔ mFourier m x = 1 := Iff.rfl

/-- A unimodular complex number with real part `1` is `1`. -/
private lemma eq_one_of_norm_eq_one_of_re_eq_one {w : ℂ} (hn : ‖w‖ = 1) (hr : w.re = 1) :
    w = 1 := by
  have hsq : w.re * w.re + w.im * w.im = 1 := by
    have h := Complex.normSq_eq_norm_sq w
    rw [hn] at h
    rw [Complex.normSq_apply] at h
    simpa using h
  have him : w.im = 0 := by nlinarith [hsq, hr]
  exact Complex.ext (by simpa using hr) (by simpa using him)

/-- A unimodular complex number other than `1` has real part `< 1`. -/
private lemma re_lt_one_of_norm_eq_one {w : ℂ} (hn : ‖w‖ = 1) (hw : w ≠ 1) : w.re < 1 := by
  have hle : w.re ≤ 1 := by
    have h := Complex.abs_re_le_norm w
    rw [hn] at h
    exact (abs_le.1 h).2
  rcases hle.lt_or_eq with h | h
  · exact h
  · exact absurd (eq_one_of_norm_eq_one_of_re_eq_one hn h) hw

/-- **The character `i ↦ z^i` is trivial only at the neutral element of `G`.** -/
theorem mFourierKer_ne_top {x : UnitAddTorus (Fin D)} (hx : x ≠ 0) : mFourierKer x ≠ ⊤ := by
  classical
  intro h
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hx
  have hm : mFourier (Pi.single c (1 : ℤ) : Fin D → ℤ) x = 1 :=
    mem_mFourierKer.1 (h ▸ AddSubgroup.mem_top (Pi.single c (1 : ℤ) : Fin D → ℤ))
  rw [mFourier_single] at hm
  refine hc ?_
  have hcirc : AddCircle.toCircle (x c) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
    refine Subtype.coe_injective ?_
    rw [AddCircle.toCircle_zero]
    simpa [fourier_one] using hm
  simpa using AddCircle.injective_toCircle one_ne_zero hcirc

/-- The real form of the transform: `Ĵ(z) = ∑_i J(i) Re(z^i)`. -/
theorem couplingFourier_eq_tsum_re (hsum : Summable J) (x : UnitAddTorus (Fin D)) :
    couplingFourier J x = ∑' m : Fin D → ℤ, J m * (mFourier m x).re := by
  have hcsum : Summable fun m : Fin D → ℤ ↦ (J m : ℂ) * mFourier m x :=
    summable_mul_mFourier (summable_ofReal_of_summable hsum) x
  have h := Complex.hasSum_re hcsum.hasSum
  simp only [Complex.re_ofReal_mul] at h
  rw [couplingFourier, ← h.tsum_eq]

/-- **Georgii, Comment (20.17)(1).**  "As `J` is nonnegative, even, and irreducible, its Fourier
transform satisfies `Ĵ(z) < Ĵ(1)` for all `z ≠ 1`."  Evenness is not needed for this.

Consequently the integral in (20.16) — and the Riemann sum in (20.19) — is well defined without
Georgii's convention `0⁻¹ = ∞`. -/
theorem couplingFourier_lt_couplingFourier_zero (hsum : Summable J) (hpos : ∀ m, 0 ≤ J m)
    (hirr : IsIrreducibleCoupling J) {x : UnitAddTorus (Fin D)} (hx : x ≠ 0) :
    couplingFourier J x < couplingFourier J (0 : UnitAddTorus (Fin D)) := by
  classical
  have hre : ∀ m : Fin D → ℤ, (mFourier m x).re ≤ 1 := fun m ↦ by
    have h := Complex.abs_re_le_norm (mFourier m x)
    rw [norm_mFourier_apply] at h
    exact (abs_le.1 h).2
  have hsummableRe : Summable fun m : Fin D → ℤ ↦ J m * (mFourier m x).re := by
    refine Summable.of_norm_bounded hsum.abs fun m ↦ ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h := Complex.abs_re_le_norm (mFourier m x)
    rw [norm_mFourier_apply] at h
    calc |J m| * |(mFourier m x).re| ≤ |J m| * 1 :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = |J m| := mul_one _
  have hsummableDiff : Summable fun m : Fin D → ℤ ↦ J m * (1 - (mFourier m x).re) :=
    (hsum.sub hsummableRe).congr fun m ↦ by ring
  have hdiff : couplingFourier J (0 : UnitAddTorus (Fin D)) - couplingFourier J x
      = ∑' m : Fin D → ℤ, J m * (1 - (mFourier m x).re) := by
    rw [couplingFourier_zero, couplingFourier_eq_tsum_re hsum, ← hsum.tsum_sub hsummableRe]
    exact tsum_congr fun m ↦ by ring
  have hterm : ∀ m : Fin D → ℤ, 0 ≤ J m * (1 - (mFourier m x).re) := fun m ↦
    mul_nonneg (hpos m) (by linarith [hre m])
  -- irreducibility produces a site where the term is strictly positive
  obtain ⟨i, hi1, hi2⟩ : ∃ i, i ∈ Function.support J ∧ i ∉ (mFourierKer x : Set (Fin D → ℤ)) :=
    Set.not_subset.1 fun hsub ↦ mFourierKer_ne_top hx (hirr _ hsub)
  have hJi : 0 < J i := lt_of_le_of_ne (hpos i) (Ne.symm hi1)
  have hlt : (mFourier i x).re < 1 :=
    re_lt_one_of_norm_eq_one (norm_mFourier_apply i x) (by simpa using hi2)
  have hpos' : 0 < J i * (1 - (mFourier i x).re) := mul_pos hJi (by linarith)
  have := hsummableDiff.tsum_pos hterm i hpos'
  rw [← hdiff] at this
  linarith

end Irreducible

/-! ### Georgii (20.19): the Riemann sums, and the finite-volume estimate -/

section RiemannSum

variable {d L n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

variable (d L J) in
/-- **Georgii's Riemann sum** of (20.19),
`|Λ(n)|⁻¹ ∑_{1 ≠ z ∈ G_{Λ(n)}} (Ĵ(1) - Ĵ(z))⁻¹`.

The sum is indexed by the discrete torus, `z = k/2N` (`dualRiemannSum_eq_sum_dualBox` writes it
over `G_Λ`), and the term `k = 0` — Georgii's `z = 1`, where he stipulates the convention
`0⁻¹ = ∞` — is omitted.  Under the hypotheses of (20.15) that convention is vacuous:
`Ĵ(z) < Ĵ(1)` for `z ≠ 1` by `couplingFourier_lt_couplingFourier_zero`, Georgii's Comment
(20.17)(1). -/
def dualRiemannSum : ℝ :=
  (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℝ)⁻¹ *
    ∑ k ∈ Finset.univ.erase (0 : Fin (d + 1) → ZMod (2 * (L + 1))),
      (couplingFourier J (0 : UnitAddTorus (Fin (d + 1)))
        - couplingFourier J (ZMod.toUnitAddTorus k))⁻¹

/-- The Riemann sum written over `G_Λ`.  Including the neutral element changes nothing, since
`(Ĵ(1) - Ĵ(1))⁻¹ = 0⁻¹ = 0` in `ℝ`. -/
theorem dualRiemannSum_eq_sum_dualBox :
    dualRiemannSum d L J = (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℝ)⁻¹ *
      ∑ z ∈ dualBox d L, (couplingFourier J (0 : UnitAddTorus (Fin (d + 1)))
        - couplingFourier J z)⁻¹ := by
  classical
  rw [dualRiemannSum, sum_dualBox]
  congr 1
  refine Finset.sum_erase _ ?_
  rw [map_zero, sub_self, _root_.inv_zero]

/-- The Riemann sum is nonnegative when `J` is nonnegative and irreducible. -/
theorem dualRiemannSum_nonneg (hsum : Summable J) (hpos : ∀ m, 0 ≤ J m)
    (hirr : IsIrreducibleCoupling J) : 0 ≤ dualRiemannSum d L J := by
  classical
  rw [dualRiemannSum]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun k hk ↦ ?_)
  have hk0 : ZMod.toUnitAddTorus k ≠ (0 : UnitAddTorus (Fin (d + 1))) := by
    intro h
    exact (Finset.mem_erase.1 hk).1 (ZMod.toUnitAddTorus_injective (by rw [h, map_zero]))
  have := couplingFourier_lt_couplingFourier_zero hsum hpos hirr hk0
  positivity

variable [IsFiniteMeasure ν]

/-- **Georgii's central estimate in the proof of (20.15)**, Step 2:

`°γ_Λ^Φ(|σ_0|²) - °γ_Λ^Φ(σ_0·σ_j) ≤ 2N |Λ|⁻¹ ∑_{1 ≠ z ∈ G_Λ} (Ĵ(1) - Ĵ(z))⁻¹`

for every cube `Λ = Λ(N)` and every site `j`.  The inverse temperature `β` is carried inside `J`
as everywhere in this development, so Georgii's factor `2Nβ⁻¹` is `2N` here with `Ĵ` the
transform of `βJ`.

The proof is the inversion formula `sum_dualBox_one_sub_re_mul_correlationFourier` together with
the infrared bound `correlationFourier_le` and `0 ≤ 1 - Re(z^{-j}) ≤ 2`; the term at the neutral
element drops out because `1 - Re(1) = 0`. -/
theorem sub_integral_dotProduct_le_dualRiemannSum (hn : 0 < n) (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) (hdom : IsGaussianDominating (L + 1) n J ν)
    (hpos : ∀ m, 0 ≤ J m) (hirr : IsIrreducibleCoupling J)
    (j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∫ ω, ω 0 ⬝ᵥ ω 0 ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
        - ∫ ω, ω 0 ⬝ᵥ ω j ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν)
      ≤ 2 * n * dualRiemannSum d L J := by
  classical
  set M := (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℝ) with hMdef
  have hM : 0 < M := by
    rw [hMdef]
    exact_mod_cast Fintype.card_pos_iff.2 ⟨0⟩
  have hterm : ∀ z ∈ dualBox d L,
      (1 - (mFourier (torusToLattice L j) z).re) * correlationFourier L n J ν z
        ≤ 2 * n * (couplingFourier J (0 : UnitAddTorus (Fin (d + 1)))
            - couplingFourier J z)⁻¹ := by
    intro z hz
    have hzt : Potential.intBoxLen L • z = 0 := mem_dualBox.1 hz
    have hC : 0 ≤ correlationFourier L n J ν z :=
      correlationFourier_nonneg hν hexp hsum heven hnd hzt
    have habs := Complex.abs_re_le_norm (mFourier (torusToLattice L j) z)
    rw [norm_mFourier_apply] at habs
    obtain ⟨hlo, hhi⟩ := abs_le.1 habs
    by_cases hz0 : z = 0
    · subst hz0
      rw [mFourier_zero_apply, sub_self, _root_.inv_zero]
      simp
    · have hstrict : couplingFourier J z < couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) :=
        couplingFourier_lt_couplingFourier_zero hsum hpos hirr hz0
      have hD : 0 < couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J z := by
        linarith
      have hCle : correlationFourier L n J ν z
          ≤ (n : ℝ) / (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J z) :=
        correlationFourier_le hn hν hexp hsum heven hnd hdom hzt (ne_of_lt hstrict)
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [div_eq_mul_inv] at hCle
      nlinarith [hCle, hC, hlo, hhi, hnn, inv_nonneg.2 hD.le]
  have hle := Finset.sum_le_sum hterm
  rw [sum_dualBox_one_sub_re_mul_correlationFourier (J := J) (ν := ν) j, ← Finset.mul_sum] at hle
  rw [dualRiemannSum_eq_sum_dualBox]
  rw [← hMdef] at hle ⊢
  have hkey : M * ((∫ ω, ω 0 ⬝ᵥ ω 0 ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
        - ∫ ω, ω 0 ⬝ᵥ ω j ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
      ≤ M * (2 * (n : ℝ) * (M⁻¹ * ∑ z ∈ dualBox d L,
          (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J z)⁻¹)) := by
    rw [show M * (2 * (n : ℝ) * (M⁻¹ * ∑ z ∈ dualBox d L,
        (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J z)⁻¹))
        = (M * M⁻¹) * (2 * (n : ℝ) * ∑ z ∈ dualBox d L,
          (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J z)⁻¹) by ring,
      mul_inv_cancel₀ hM.ne', one_mul]
    exact hle
  exact le_of_mul_le_mul_left hkey hM

end RiemannSum

/-! ### From the cube to `ℤ^d`: Georgii's fields `μ_L^Φ` -/

section Fields

variable {d n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν]

theorem zero_mem_periodicCube (L : ℕ) : (0 : Fin (d + 1) → ℤ) ∈ periodicCube (d + 1) L :=
  mem_periodicCube_of_bounds fun _ ↦ by
    have hL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
    simp only [Pi.zero_apply]
    constructor <;> linarith

omit [IsFiniteMeasure ν] in
/-- **The two-point function of Georgii's field `μ_L^Φ = °γ_{Λ(L)}^Φ × δ_{0}`** is the two-point
function of the periodic Gibbs distribution, at sites of the cube. -/
theorem integral_dotProduct_heisenbergPeriodicField (L : ℕ) {i j : Fin (d + 1) → ℤ}
    (hi : i ∈ periodicCube (d + 1) L) (hj : j ∈ periodicCube (d + 1) L) :
    (∫ ω, ω i ⬝ᵥ ω j ∂(heisenbergPeriodicField J ν L 0))
      = ∫ ζ, ζ (latticeToTorus L i) ⬝ᵥ ζ (latticeToTorus L j)
          ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) := by
  rw [heisenbergPeriodicField, integral_map (measurable_periodicJuxt L 0).aemeasurable
    (((measurable_pi_apply i).dotProduct (measurable_pi_apply j)).aestronglyMeasurable)]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  simp only [periodicJuxt_apply_of_mem ζ hi, periodicJuxt_apply_of_mem ζ hj]

/-- **Georgii, Lemma (20.8), in Bochner form**: `δ ≤ °γ_Λ^Φ(|σ_0|²)` for a `δ > 0` depending only
on the a priori measure `λ`.  The `ℝ≥0∞` form is
`exists_le_lintegral_dotProduct_self_heisenbergPeriodicGibbsDist`; the passage to the Bochner
integral uses the integrability provided by the tail estimate of (20.6). -/
theorem exists_le_integral_dotProduct_self_heisenbergPeriodicGibbsDist
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν] (hν : ν {x : Fin n → ℝ | x ≠ 0} ≠ 0)
    (hexp : HasExpSqMoments ν) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (d N : ℕ) [NeZero N] (J : (Fin (d + 1) → ℤ) → ℝ),
      Summable J → (∀ m, J (-m) = J m) → (∀ m, 0 ≤ J m) → (∀ k, IsNonnegDefiniteAt k J) →
      ∀ i₀ : Fin (d + 1) → ZMod (2 * N),
        δ ≤ ∫ ω, ω i₀ ⬝ᵥ ω i₀ ∂(heisenbergPeriodicGibbsDist N n J ν) := by
  obtain ⟨δ, hδ, hle⟩ := exists_le_lintegral_dotProduct_self_heisenbergPeriodicGibbsDist ν hν
  have hν0 : ν ≠ 0 := fun h ↦ hν (by simp [h])
  refine ⟨δ, hδ, fun d N _ J hsum heven hpos hnd i₀ ↦ ?_⟩
  have hint := integrable_exp_heisenbergExponent (N := N) (d := d + 1) (J := J) hexp hsum
  have hprob := isProbabilityMeasure_heisenbergPeriodicGibbsDist hν0 hint
  have htail := fun a (ha : 0 < a) ↦
    exists_forall_heisenbergPeriodicGibbsDist_tail_le (N := N) (d := d) (n := n)
      hν0 hexp hsum heven hnd ha
  have hI : Integrable (fun ω : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ) ↦ ω i₀ ⬝ᵥ ω i₀)
      (heisenbergPeriodicGibbsDist N n J ν) := integrable_dotProduct_of_tail htail i₀ i₀
  have hnn : (0 : ℝ) ≤ ∫ ω, ω i₀ ⬝ᵥ ω i₀ ∂(heisenbergPeriodicGibbsDist N n J ν) :=
    integral_nonneg fun ω ↦ dotProduct_self_nonneg _
  have hlint := hle d N J hsum heven hpos hnd hint i₀
  rw [← ofReal_integral_eq_lintegral_ofReal hI (.of_forall fun ω ↦ dotProduct_self_nonneg _)]
    at hlint
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 hlint

end Fields

/-! ### Georgii's truncation argument -/

section Truncation

variable {S E : Type*} [MeasurableSpace E]

/-- The two-sided truncation of a real-valued observable at level `t`. -/
private def truncObs (t : ℝ) (f : (S → E) → ℝ) : (S → E) → ℝ :=
  fun ω ↦ max (-t) (min t (f ω))

private lemma trunc_eq_of_abs_le {t x : ℝ} (h : |x| ≤ t) : max (-t) (min t x) = x := by
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

private lemma abs_sub_trunc_le {t x : ℝ} (ht : 0 ≤ t) (h : t ≤ |x|) :
    |x - max (-t) (min t x)| ≤ |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h ⊢
    rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_neg hx] at h ⊢
    rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]
    linarith

omit [MeasurableSpace E] in
private lemma abs_truncObs_le {t : ℝ} (ht : 0 ≤ t) (f : (S → E) → ℝ) (ω : S → E) :
    |truncObs t f ω| ≤ t := by
  rw [truncObs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

omit [MeasurableSpace E] in
private lemma abs_sub_truncObs_le {t : ℝ} (ht : 0 ≤ t) (f : (S → E) → ℝ) (ω : S → E) :
    |f ω - truncObs t f ω| ≤ Set.indicator {ω | t ≤ |f ω|} (fun ω ↦ |f ω|) ω := by
  by_cases h : t ≤ |f ω|
  · rw [Set.indicator_of_mem (show ω ∈ {ω | t ≤ |f ω|} from h)]
    exact abs_sub_trunc_le ht h
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | t ≤ |f ω|} from h), truncObs,
      trunc_eq_of_abs_le (not_le.1 h).le, sub_self, abs_zero]

/-- The truncation error of an integrable observable is at most its tail integral. -/
private lemma abs_integral_sub_integral_truncObs_le {ρ : Measure (S → E)} [IsFiniteMeasure ρ]
    {f : (S → E) → ℝ} (hfm : Measurable f) (hf : Integrable f ρ) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ ω, f ω ∂ρ) - ∫ ω, truncObs t f ω ∂ρ|
      ≤ ∫ ω, Set.indicator {ω | t ≤ |f ω|} (fun ω ↦ |f ω|) ω ∂ρ := by
  have habs : Measurable fun ω : S → E ↦ |f ω| := by fun_prop
  have hset : MeasurableSet {ω : S → E | t ≤ |f ω|} :=
    measurableSet_le measurable_const habs
  have hgm : Measurable (truncObs t f) := measurable_const.max (measurable_const.min hfm)
  have hgi : Integrable (truncObs t f) ρ :=
    .of_bound hgm.aestronglyMeasurable t
      (.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_truncObs_le ht f ω)
  have hind : Integrable (Set.indicator {ω : S → E | t ≤ |f ω|} (fun ω ↦ |f ω|)) ρ :=
    hf.abs.indicator hset
  rw [← integral_sub hf hgi]
  calc |∫ ω, (f ω - truncObs t f ω) ∂ρ| ≤ ∫ ω, |f ω - truncObs t f ω| ∂ρ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (f := fun ω ↦ f ω - truncObs t f ω) (μ := ρ)
    _ ≤ ∫ ω, Set.indicator {ω | t ≤ |f ω|} (fun ω ↦ |f ω|) ω ∂ρ :=
        integral_mono (hf.sub hgi).abs hind fun ω ↦ abs_sub_truncObs_le ht f ω

/-- **Local convergence integrates a uniformly integrable local observable.**

If `μ_k → μ` in the topology of local convergence (Georgii (4.2)), `f` is `𝓕_Λ`-measurable for a
finite volume `Λ`, integrable for `μ` and for every `μ_k`, and its tails
`∫ 1_{|f| ≥ t} |f| dρ` are small uniformly in `ρ ∈ {μ} ∪ {μ_k : k}`, then `μ_k(f) → μ(f)`.

This is the "obvious truncation argument" of Georgii's proof of (20.15): local convergence gives
`μ_k(g) → μ(g)` only for *bounded* local `g`, and the uniform tail bound of Lemma (20.6)(ii)
removes the truncation.  Intended home:
`GibbsMeasure/Topology/LocalConvergenceIntegral.lean`. -/
theorem tendsto_integral_of_tendsto_withLocalConvergence_of_uniformTail
    {μs : ℕ → WithLocalConvergence S E} {μ : WithLocalConvergence S E}
    (h : Filter.Tendsto μs Filter.atTop (nhds μ)) (Λ : Finset S) {f : (S → E) → ℝ}
    (hfm : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] f)
    (hint : ∀ k, Integrable f ((μs k).toMeasure : Measure (S → E)))
    (hintμ : Integrable f (μ.toMeasure : Measure (S → E)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 ≤ t ∧
      (∀ k, ∫ ω, Set.indicator {ω | t ≤ |f ω|} (fun ω ↦ |f ω|) ω
          ∂((μs k).toMeasure : Measure (S → E)) ≤ ε) ∧
      (∫ ω, Set.indicator {ω | t ≤ |f ω|} (fun ω ↦ |f ω|) ω
          ∂(μ.toMeasure : Measure (S → E)) ≤ ε)) :
    Filter.Tendsto (fun k ↦ ∫ ω, f ω ∂((μs k).toMeasure : Measure (S → E))) Filter.atTop
      (nhds (∫ ω, f ω ∂(μ.toMeasure : Measure (S → E)))) := by
  have hfm' : Measurable f := hfm.mono cylinderEvents_le_pi le_rfl
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨t, ht0, htk, htμ⟩ := htail (ε / 4) (by linarith)
  -- the truncation is bounded and local, so local convergence integrates it
  have hgm : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] (truncObs t f) :=
    measurable_const.max (measurable_const.min hfm)
  have hgc : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      fun ω ↦ ((truncObs t f ω : ℝ) : ℂ) := Complex.measurable_ofReal.comp hgm
  have hconv := tendsto_integral_of_tendsto_withLocalConvergence h Λ hgc (C := t)
    (fun ω ↦ by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_truncObs_le ht0 f ω)
  simp only [integral_complex_ofReal] at hconv
  have hreal : Filter.Tendsto
      (fun k ↦ ∫ ω, truncObs t f ω ∂((μs k).toMeasure : Measure (S → E))) Filter.atTop
      (nhds (∫ ω, truncObs t f ω ∂(μ.toMeasure : Measure (S → E)))) := by
    have hc := (Complex.continuous_re.tendsto _).comp hconv
    simpa only [Function.comp_def, Complex.ofReal_re] using hc
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hreal (ε / 4) (by linarith)
  refine ⟨K, fun k hk ↦ ?_⟩
  have h1 := abs_integral_sub_integral_truncObs_le
    (ρ := ((μs k).toMeasure : Measure (S → E))) hfm' (hint k) ht0
  have h2 := abs_integral_sub_integral_truncObs_le
    (ρ := (μ.toMeasure : Measure (S → E))) hfm' hintμ ht0
  have h3 := hK k hk
  rw [Real.dist_eq] at h3 ⊢
  have hb1 := (htk k)
  have hb2 := htμ
  calc |(∫ ω, f ω ∂((μs k).toMeasure : Measure (S → E)))
          - ∫ ω, f ω ∂(μ.toMeasure : Measure (S → E))|
      ≤ |(∫ ω, f ω ∂((μs k).toMeasure : Measure (S → E)))
            - ∫ ω, truncObs t f ω ∂((μs k).toMeasure : Measure (S → E))|
          + |(∫ ω, truncObs t f ω ∂((μs k).toMeasure : Measure (S → E)))
            - ∫ ω, truncObs t f ω ∂(μ.toMeasure : Measure (S → E))|
          + |(∫ ω, truncObs t f ω ∂(μ.toMeasure : Measure (S → E)))
            - ∫ ω, f ω ∂(μ.toMeasure : Measure (S → E))| := by
        have := abs_sub_le (∫ ω, f ω ∂((μs k).toMeasure : Measure (S → E)))
          (∫ ω, truncObs t f ω ∂((μs k).toMeasure : Measure (S → E)))
          (∫ ω, f ω ∂(μ.toMeasure : Measure (S → E)))
        have h4 := abs_sub_le (∫ ω, truncObs t f ω ∂((μs k).toMeasure : Measure (S → E)))
          (∫ ω, truncObs t f ω ∂(μ.toMeasure : Measure (S → E)))
          (∫ ω, f ω ∂(μ.toMeasure : Measure (S → E)))
        linarith
    _ < ε := by
        rw [abs_sub_comm (∫ ω, truncObs t f ω ∂(μ.toMeasure : Measure (S → E)))]
        linarith

end Truncation

/-! ### Lemma (20.6)(ii) with a constant uniform in the volume -/

section UniformTail

variable {S : Type*} {m : ℕ} {μ : Measure (S → (Fin m → ℝ))}

/-- **Georgii, Lemma (20.6)(ii), with an explicit constant.**  A tail bound
`μ(|σ_i|² ≥ t) ≤ b e^{-2(2a+1)t}` gives `μ(|σ_i·σ_j| 1_{|σ_i·σ_j| ≥ t}) ≤ 2(1+b) e^{-at}` with a
constant depending only on `a` and `b`.

`exists_lemma_20_6_of_tail` states the same thing with the constant existentially quantified,
which is not enough when the bound has to be uniform over a *sequence* of measures — as it is in
Georgii's truncation argument in the proof of (20.15).  Intended home:
`GibbsMeasure/Specification/InfraredBound.lean`, next to `exists_lemma_20_6_of_tail`. -/
theorem lintegral_indicator_abs_dotProduct_le_of_tail [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b)
    (htail : ∀ (i : S) (t : ℝ), 0 ≤ t →
      μ {ω | t ≤ ω i ⬝ᵥ ω i} ≤ ENNReal.ofReal (b * Real.exp (-(2 * (2 * a + 1) * t))))
    (i j : S) (t : ℝ) :
    ∫⁻ ω, Set.indicator {ω : S → (Fin m → ℝ) | t ≤ |ω i ⬝ᵥ ω j|}
        (fun ω ↦ ENNReal.ofReal |ω i ⬝ᵥ ω j|) ω ∂μ
      ≤ ENNReal.ofReal (2 * (1 + b) * Real.exp (-(a * t))) := by
  have ha' : (0 : ℝ) < 2 * a + 1 := by linarith
  have hEi := lintegral_exp_dotProduct_self_le_of_tail (μ := μ) ha' i (htail i)
  have hEj := lintegral_exp_dotProduct_self_le_of_tail (μ := μ) ha' j (htail j)
  refine (lintegral_indicator_abs_dotProduct_le ha i j t).trans ?_
  calc ENNReal.ofReal (Real.exp (-(a * t)))
        * ((∫⁻ ω, ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω i ⬝ᵥ ω i))) ∂μ)
          + ∫⁻ ω, ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω j ⬝ᵥ ω j))) ∂μ)
      ≤ ENNReal.ofReal (Real.exp (-(a * t)))
          * ((1 + ENNReal.ofReal b) + (1 + ENNReal.ofReal b)) :=
        mul_le_mul' le_rfl (add_le_add hEi hEj)
    _ = ENNReal.ofReal (2 * (1 + b) * Real.exp (-(a * t))) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hb,
          ← ENNReal.ofReal_add (by linarith) (by linarith), ← ENNReal.ofReal_mul
            (Real.exp_nonneg _)]
        ring_nf

/-- The Bochner form of `lintegral_indicator_abs_dotProduct_le_of_tail`. -/
theorem integral_indicator_abs_dotProduct_le_of_tail [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b)
    (htail : ∀ (i : S) (t : ℝ), 0 ≤ t →
      μ {ω | t ≤ ω i ⬝ᵥ ω i} ≤ ENNReal.ofReal (b * Real.exp (-(2 * (2 * a + 1) * t))))
    (hI : ∀ u v : S, Integrable (fun ω ↦ ω u ⬝ᵥ ω v) μ) (i j : S) (t : ℝ) :
    (∫ ω, Set.indicator {ω : S → (Fin m → ℝ) | t ≤ |ω i ⬝ᵥ ω j|} (fun ω ↦ |ω i ⬝ᵥ ω j|) ω ∂μ)
      ≤ 2 * (1 + b) * Real.exp (-(a * t)) := by
  have hmeas : Measurable fun ω : S → (Fin m → ℝ) ↦ (ω i ⬝ᵥ ω j) :=
    (measurable_pi_apply i).dotProduct (measurable_pi_apply j)
  have hset : MeasurableSet {ω : S → (Fin m → ℝ) | t ≤ |ω i ⬝ᵥ ω j|} :=
    measurableSet_le measurable_const (by fun_prop)
  have hind : Integrable
      (Set.indicator {ω : S → (Fin m → ℝ) | t ≤ |ω i ⬝ᵥ ω j|} fun ω ↦ |ω i ⬝ᵥ ω j|) μ :=
    (hI i j).abs.indicator hset
  have hnn : ∀ ω : S → (Fin m → ℝ), 0 ≤ Set.indicator {ω | t ≤ |ω i ⬝ᵥ ω j|}
      (fun ω ↦ |ω i ⬝ᵥ ω j|) ω := fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ abs_nonneg _) ω
  have hpt : ∀ ω : S → (Fin m → ℝ),
      ENNReal.ofReal (Set.indicator {ω | t ≤ |ω i ⬝ᵥ ω j|} (fun ω ↦ |ω i ⬝ᵥ ω j|) ω)
        = Set.indicator {ω | t ≤ |ω i ⬝ᵥ ω j|} (fun ω ↦ ENNReal.ofReal |ω i ⬝ᵥ ω j|) ω := by
    intro ω
    by_cases hω : ω ∈ {ω : S → (Fin m → ℝ) | t ≤ |ω i ⬝ᵥ ω j|}
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
  have hkey := lintegral_indicator_abs_dotProduct_le_of_tail (μ := μ) ha hb htail i j t
  rw [← lintegral_congr hpt,
    ← ofReal_integral_eq_lintegral_ofReal hind (.of_forall hnn)] at hkey
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hkey

end UniformTail

/-! ### Georgii (20.15), Step 2: long-range order in the infinite volume -/

section LongRangeOrder

/-- **Local equicontinuity passes to subsequences.**  Intended home:
`GibbsMeasure/Topology/ClusterPoints.lean`, next to `LocallyEquicontinuous`. -/
theorem locallyEquicontinuous_comp {S E : Type*} [MeasurableSpace E]
    {μs : ℕ → ProbabilityMeasure (S → E)} (h : LocallyEquicontinuous Filter.atTop μs)
    {ψ : ℕ → ℕ} (hψ : Filter.Tendsto ψ Filter.atTop Filter.atTop) :
    LocallyEquicontinuous Filter.atTop fun k ↦ μs (ψ k) := by
  intro Λ A hmeas hanti hempty
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h Λ A hmeas hanti hempty) (fun _ ↦ zero_le) fun k ↦ ?_
  exact hψ.limsup_comp_le_limsup (u := fun i ↦ (μs i : Measure (S → E)) (A k))

variable {d n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν]

/-- Every site of `ℤ^d` eventually lies in the cube `Λ(L)`. -/
theorem eventually_mem_periodicCube (j : Fin (d + 1) → ℤ) :
    ∀ᶠ L in Filter.atTop, j ∈ periodicCube (d + 1) L := by
  classical
  filter_upwards [Filter.eventually_ge_atTop (Finset.univ.sup fun k ↦ (j k).natAbs)] with L hL
  refine mem_periodicCube_of_bounds fun k ↦ ?_
  have h1 : (j k).natAbs ≤ L :=
    le_trans (Finset.le_sup (f := fun k ↦ (j k).natAbs) (Finset.mem_univ k)) hL
  omega

/-- **The two-point function of Georgii's field `μ_L^Φ` obeys the infrared estimate**: at every
site `j` of the cube, `μ_L^Φ(σ_0·σ_j) ≥ °γ_Λ^Φ(|σ_0|²) - 2N |Λ|⁻¹ ∑_{1 ≠ z ∈ G_Λ}(Ĵ(1)-Ĵ(z))⁻¹`. -/
theorem le_integral_dotProduct_heisenbergPeriodicField {L : ℕ} (hn : 0 < n) (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) (hdom : IsGaussianDominating (L + 1) n J ν)
    (hpos : ∀ m, 0 ≤ J m) (hirr : IsIrreducibleCoupling J) {δ : ℝ}
    (hδ : δ ≤ ∫ ω, ω 0 ⬝ᵥ ω 0 ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
    {j : Fin (d + 1) → ℤ} (hj : j ∈ periodicCube (d + 1) L) :
    δ - 2 * n * dualRiemannSum d L J
      ≤ ∫ ω, ω 0 ⬝ᵥ ω j ∂(heisenbergPeriodicField J ν L 0) := by
  rw [integral_dotProduct_heisenbergPeriodicField L (zero_mem_periodicCube L) hj,
    latticeToTorus_zero]
  have h := sub_integral_dotProduct_le_dualRiemannSum (L := L) (ν := ν) hn hν hexp hsum heven hnd
    hdom hpos hirr (latticeToTorus L j)
  linarith

/-- **Georgii, Theorem (20.15), Step 2: long-range order.**

Under his hypotheses on the a priori measure `λ` and on the coupling `J` — `λ` non-degenerate and
with all Gaussian moments (20.3), `J` even, nonnegative, irreducible, slowly summable (20.4) and
nonnegative definite relative to the reflections — together with the Riemann-sum condition (20.19)
`liminf_L |Λ(L)|⁻¹ ∑_{1 ≠ z ∈ G_{Λ(L)}}(Ĵ(1) - Ĵ(z))⁻¹ ≤ c`, there is a shift-invariant Gibbs
measure `μ ∈ 𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)` whose two-point function is bounded below *uniformly in the
distance*:

`μ(σ_0 · σ_j) ≥ δ - 2N c`  for every `j ∈ ℤ^d`.

Here `δ` is the constant of Lemma (20.8), which depends only on `λ`; since `J` carries the
inverse temperature, replacing `J` by `βJ` multiplies the Riemann sums by `β⁻¹`, so the
right-hand side is Georgii's `δ - cβ⁻¹` and is positive for large `β`.

The proof is Georgii's: the finite-volume estimate `le_integral_dotProduct_heisenbergPeriodicField`
along a subsequence of volumes realising (20.19), a cluster point of the corresponding fields
(Proposition (20.7)), and the truncation argument
`tendsto_integral_of_tendsto_withLocalConvergence_of_uniformTail` fed by Lemma (20.6)(ii). -/
theorem exists_mem_heisenbergGZero_forall_le_integral_dotProduct (hn : 0 < n) (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (heven : ∀ m, J (-m) = J m) (hJ : IsSlowlySummable J)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) (hpos : ∀ m, 0 ≤ J m) (hirr : IsIrreducibleCoupling J)
    (hdom : ∀ L : ℕ, IsGaussianDominating (L + 1) n J ν) {δ c : ℝ}
    (hδ : ∀ L : ℕ, δ ≤ ∫ ω, ω 0 ⬝ᵥ ω 0 ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
    (hc : ∃ᶠ L in Filter.atTop, dualRiemannSum d L J ≤ c) :
    ∃ μ ∈ heisenbergGZero J ν, ∀ j : Fin (d + 1) → ℤ,
      δ - 2 * n * c ≤ ∫ ω, ω 0 ⬝ᵥ ω j ∂(μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) := by
  classical
  have hsum : Summable J := hJ.summable
  obtain ⟨ψ, hψmono, hψ⟩ := Filter.extraction_of_frequently_atTop hc
  have hprob : ∀ L : ℕ, IsProbabilityMeasure (heisenbergPeriodicField J ν L 0) := fun L ↦
    isProbabilityMeasure_heisenbergPeriodicField hν hexp hsum L 0
  set μs : ℕ → ProbabilityMeasure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)) :=
    fun L ↦ ⟨heisenbergPeriodicField J ν L 0, hprob L⟩ with hμsdef
  have hμsval : ∀ L, (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
      = heisenbergPeriodicField J ν L 0 := fun _ ↦ rfl
  have hle : LocallyEquicontinuous Filter.atTop μs :=
    locallyEquicontinuous_heisenbergPeriodicField hν hexp heven hJ hnd hμsval
  have hle' : LocallyEquicontinuous Filter.atTop (fun k ↦ μs (ψ k)) :=
    locallyEquicontinuous_comp hle hψmono.tendsto_atTop
  obtain ⟨m, hm⟩ := exists_mapClusterPt_of_locallyEquicontinuous
    (μs := fun k ↦ (WithSetwiseTopology.ofMeasure (μs (ψ k))
      : WithLocalConvergence (Fin (d + 1) → ℤ) (Fin n → ℝ))) hle'
  obtain ⟨φ, hφmono, hconv⟩ :=
    exists_strictMono_tendsto_of_mapClusterPt (μs := fun k ↦ μs (ψ k)) (μ := m.toMeasure) hle' hm
  have hcomp : Filter.Tendsto (fun k ↦ ψ (φ k)) Filter.atTop Filter.atTop :=
    hψmono.tendsto_atTop.comp hφmono.tendsto_atTop
  have hmem : m.toMeasure ∈ heisenbergGZero J ν :=
    ⟨μs, hμsval, MapClusterPt.of_comp hcomp hconv.mapClusterPt⟩
  refine ⟨m.toMeasure, hmem, fun j ↦ ?_⟩
  -- uniform tail bounds for the fields and for the cluster point
  have htailFall : ∀ L : ℕ, ∀ a : ℝ, 0 < a → ∃ b : ℝ, 0 < b ∧ ∀ (i : Fin (d + 1) → ℤ) (t : ℝ),
      (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) {ω | t ≤ ω i ⬝ᵥ ω i}
        ≤ ENNReal.ofReal (b * Real.exp (-(a * t))) := by
    intro L a ha
    obtain ⟨b', hb'0, hb'⟩ :=
      exists_forall_heisenbergPeriodicField_zero_tail_le hν hexp hsum heven hnd ha
    exact ⟨b', hb'0, fun i t ↦ hb' L i t⟩
  have htailMall : ∀ a : ℝ, 0 < a → ∃ b : ℝ, 0 < b ∧ ∀ (i : Fin (d + 1) → ℤ) (t : ℝ),
      (m.toMeasure : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) {ω | t ≤ ω i ⬝ᵥ ω i}
        ≤ ENNReal.ofReal (b * Real.exp (-(a * t))) := by
    intro a ha
    obtain ⟨b', hb'0, hb'⟩ := exists_forall_tail_le_of_mem_heisenbergGZero hν hexp hsum heven hnd ha
    exact ⟨b', hb'0, fun i t ↦ hb' m.toMeasure hmem i t⟩
  obtain ⟨b₁, hb₁0, hb₁⟩ := exists_forall_heisenbergPeriodicField_zero_tail_le (J := J) (ν := ν)
    hν hexp hsum heven hnd (a := 2 * (2 * 1 + 1)) (by norm_num)
  obtain ⟨b₂, hb₂0, hb₂⟩ := exists_forall_tail_le_of_mem_heisenbergGZero (J := J) (ν := ν)
    hν hexp hsum heven hnd (a := 2 * (2 * 1 + 1)) (by norm_num)
  set b := max b₁ b₂ with hbdef
  have hb0 : 0 ≤ b := le_trans hb₁0.le (le_max_left _ _)
  have htailF : ∀ L : ℕ, ∀ (i : Fin (d + 1) → ℤ) (t : ℝ), 0 ≤ t →
      (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) {ω | t ≤ ω i ⬝ᵥ ω i}
        ≤ ENNReal.ofReal (b * Real.exp (-(2 * (2 * 1 + 1) * t))) := fun L i t _ ↦
    (hb₁ L i t).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)))
  have htailM : ∀ (i : Fin (d + 1) → ℤ) (t : ℝ), 0 ≤ t →
      (m.toMeasure : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) {ω | t ≤ ω i ⬝ᵥ ω i}
        ≤ ENNReal.ofReal (b * Real.exp (-(2 * (2 * 1 + 1) * t))) := fun i t _ ↦
    (hb₂ m.toMeasure hmem i t).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)))
  have hprobM : IsProbabilityMeasure (m.toMeasure : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) :=
    m.toMeasure.2
  have hIF : ∀ L : ℕ, ∀ u v : Fin (d + 1) → ℤ,
      Integrable (fun ω ↦ ω u ⬝ᵥ ω v) (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) :=
    fun L u v ↦ integrable_dotProduct_of_tail (htailFall L) u v
  have hIM : ∀ u v : Fin (d + 1) → ℤ, Integrable (fun ω ↦ ω u ⬝ᵥ ω v)
      (m.toMeasure : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) :=
    fun u v ↦ integrable_dotProduct_of_tail htailMall u v
  -- the observable `σ_0 · σ_j` is local
  have hfmeas : Measurable fun ω : (Fin (d + 1) → ℤ) → (Fin n → ℝ) ↦ ω 0 ⬝ᵥ ω j :=
    (measurable_pi_apply _).dotProduct (measurable_pi_apply _)
  have hdep : DependsOn (fun ω : (Fin (d + 1) → ℤ) → (Fin n → ℝ) ↦ ω 0 ⬝ᵥ ω j)
      ((({0, j} : Finset (Fin (d + 1) → ℤ)) : Set (Fin (d + 1) → ℤ))) := by
    intro ω η h
    simp only [h 0 (by simp), h j (by simp)]
  have hfm : Measurable[cylinderEvents (X := fun _ : Fin (d + 1) → ℤ ↦ (Fin n → ℝ))
      ((({0, j} : Finset (Fin (d + 1) → ℤ)) : Set (Fin (d + 1) → ℤ)))]
      fun ω ↦ ω 0 ⬝ᵥ ω j := hfmeas.cylinderEvents_of_dependsOn hdep
  -- the truncation argument
  have hlim : Filter.Tendsto
      (fun k ↦ ∫ ω, ω 0 ⬝ᵥ ω j
        ∂((μs (ψ (φ k))) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))) Filter.atTop
      (nhds (∫ ω, ω 0 ⬝ᵥ ω j ∂(m.toMeasure : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))))) := by
    refine tendsto_integral_of_tendsto_withLocalConvergence_of_uniformTail hconv
      ({0, j} : Finset (Fin (d + 1) → ℤ)) hfm (fun k ↦ hIF _ 0 j) (hIM 0 j) fun ε hε ↦ ?_
    -- choose the truncation level
    have hzero : Filter.Tendsto (fun t : ℝ ↦ 2 * (1 + b) * Real.exp (-(1 * t))) Filter.atTop
        (nhds 0) := by
      have h1 : Filter.Tendsto (fun t : ℝ ↦ -(1 * t)) Filter.atTop Filter.atBot := by
        simpa using Filter.tendsto_neg_atTop_atBot.comp Filter.tendsto_id
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (2 * (1 + b))
    obtain ⟨t, htlt, ht0⟩ :=
      ((hzero.eventually (gt_mem_nhds hε)).and (Filter.eventually_ge_atTop (0 : ℝ))).exists
    refine ⟨t, ht0, fun k ↦ ?_, ?_⟩
    · exact (integral_indicator_abs_dotProduct_le_of_tail
        (μ := ((μs (ψ (φ k))) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))))
        one_pos hb0 (htailF _) (hIF _) 0 j t).trans htlt.le
    · exact (integral_indicator_abs_dotProduct_le_of_tail
        (μ := ((m.toMeasure) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))))
        one_pos hb0 htailM hIM 0 j t).trans htlt.le
  -- the finite-volume estimate along the subsequence
  have hev : ∀ᶠ k in Filter.atTop, δ - 2 * n * c
      ≤ ∫ ω, ω 0 ⬝ᵥ ω j ∂((μs (ψ (φ k))) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) := by
    filter_upwards [hcomp.eventually (eventually_mem_periodicCube (d := d) j)] with k hk
    have h1 := le_integral_dotProduct_heisenbergPeriodicField (L := ψ (φ k)) (ν := ν) hn hν hexp
      hsum heven hnd (hdom _) hpos hirr (hδ _) hk
    have h2 : dualRiemannSum d (ψ (φ k)) J ≤ c := hψ (φ k)
    have hnn : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
    rw [hμsval]
    nlinarith [h1, h2, hnn]
  exact ge_of_tendsto hlim hev


/-- **Georgii, Theorem (20.15): long-range order at low temperature.**

Under the hypotheses of (20.15) — `λ` non-degenerate with all Gaussian moments (20.3), `J` even,
nonnegative, irreducible, slowly summable (20.4) and nonnegative definite relative to the
reflections `r_1, …, r_d`, and Gaussian domination (20.13) — together with the Riemann-sum
condition (20.19) at a constant `c`, there is a **shift-invariant Gibbs measure**
`μ ∈ 𝒢_Θ(Φ)` with

`μ(σ_0 · σ_j) ≥ δ - 2N c`  for all `j ∈ ℤ^d`,

where `δ > 0` is the constant of Lemma (20.8), which depends only on `λ`.  Since `J` carries the
inverse temperature, replacing `J` by `βJ` divides the Riemann sums by `β`, so the bound is
Georgii's `δ - cβ⁻¹` and is *positive* for `β` large: at low temperature the model has long-range
order. -/
theorem exists_mem_heisenbergGibbsMeasures_forall_le_integral_dotProduct [NeZero ν] (hn : 0 < n)
    (hνz : ν {x : Fin n → ℝ | x ≠ 0} ≠ 0) (hexp : HasExpSqMoments ν)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (hJ : IsSlowlySummable J)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) (hpos : ∀ m, 0 ≤ J m) (hirr : IsIrreducibleCoupling J)
    (hdom : ∀ L : ℕ, IsGaussianDominating (L + 1) n J ν) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, (∃ᶠ L in Filter.atTop, dualRiemannSum d L J ≤ c) →
      ∃ μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)),
        μ ∈ heisenbergGibbsMeasures J ν 1 hexp heven hJ0 hJ ∧
        (∀ a : Fin (d + 1) → ℤ,
          MeasurePreserving (shift (Fin n → ℝ) a).toFun μ μ) ∧
        ∀ j : Fin (d + 1) → ℤ, δ - 2 * n * c ≤ ∫ ω, ω 0 ⬝ᵥ ω j ∂μ := by
  have hν : ν ≠ 0 := NeZero.ne ν
  obtain ⟨δ, hδ0, hδ⟩ :=
    exists_le_integral_dotProduct_self_heisenbergPeriodicGibbsDist ν hνz hexp
  refine ⟨δ, hδ0, fun c hc ↦ ?_⟩
  obtain ⟨μ, hμmem, hμ⟩ := exists_mem_heisenbergGZero_forall_le_integral_dotProduct
    (J := J) (ν := ν) hn hν hexp heven hJ hnd hpos hirr hdom
    (δ := δ) (fun L ↦ hδ d (L + 1) J hJ.summable heven hpos hnd 0) hc
  obtain ⟨_, hsub⟩ :=
    heisenbergGZero_nonempty_and_subset (J := J) (ν := ν) hexp heven hJ0 hJ hnd
  obtain ⟨hgibbs, hshift⟩ := hsub μ hμmem
  exact ⟨(μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))), hgibbs, hshift, hμ⟩

end LongRangeOrder

end MeasureTheory.GibbsMeasure

end

end
