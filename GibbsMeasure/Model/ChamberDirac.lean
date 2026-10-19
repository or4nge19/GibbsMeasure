/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.AlgebraicTopology.CubicalCochain.Basic
public import GibbsMeasure.Mathlib.GroupTheory.SemidirectProduct
public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.Hopping
public import GibbsMeasure.Model.ChamberGraph
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The chamber Dirac matrix

The fermion of the chamber regularization of QED₃ lives on the chambers of the mirrors of `ℤᵈ`:
one site `g • v₀` for each affine signed permutation `g ∈ W = ℤᵈ ⋊ O(d, ℤ)`, and a bond of type
`i` from `g` to `g sᵢ` across each wall (`Model/ChamberGraph`). Over a quotient `p : ℤᵈ →+ X` of
the lattice (the torus `X = ℤᵈ ⧸ Γ` with `p` the quotient map, or `X = ℤᵈ` itself) the sites are
the pairs `(k, r) : X × SignedPerm (Fin d)` of a photon site and a linear part: `toChamberSite`
identifies them with the fermion sites modulo the translations in `ker p`
(`toChamberSite_eq_toChamberSite_iff`) and maps bonds to bonds
(`toChamberSite_mul_wallReflection`). This file owns the chamber Dirac matrix on these sites,
coupled to a `U(1)` link field, and the nonnegativity of its determinant.

## The formulas transcribed

From *The Field-Strength Osterwalder–Schrader Axioms for QED in Three Dimensions* ([Q] §§2.2–2.3)
and its manuscript ([M] Def 2.4–2.8, Lemma 2.10). [Q]'s coordinates `x₁, x₂, x₃` are Lean's
`x 0, x 1, x 2` and its walls `0, 1, 2, 3` are `0, 1, 2, Fin.last 3`; `0 < ρ < 1`, `q > 0`,
`M ∈ ℝ`, `wᵢ > 0` in [Q], and the statements here need only real `ρ, M, wᵢ`.

* (2.9) Inward unit normals `n₀ = e₃`, `n₁ = (e₂ - e₃)/√2`, `n₂ = (e₁ - e₂)/√2`, `n₃ = -e₁`: here
  `wallNormal i / |wallNormal i|`.
* (2.10) Sites `𝕏 = W v₀`, neighbours `(g v₀)^{(i)} = g sᵢ v₀`; `x = k + r v₀` with `π(x) = k`;
  `x^{(i)} - x = -2 dᵢ r nᵢ`, so `(x^{(i)} - x)/|x^{(i)} - x| = -r nᵢ` (`bondDirection`,
  `mul_wallReflection_smul_sub_smul_eq`).
* (2.11) Standard weights `wᵢ = 48 |Πᵢ ∩ C̄₀|`, `(w₀, w₁, w₂, w₃) = (6, 6√2, 6√2, 6)`, with
  `∑ᵢ wᵢ nᵢ = 0`.
* (2.12) `γ_μ = diag(σ_μ, -σ_μ)` (Pauli `σ_μ`), `γ_v = ∑ v_μ γ_μ`, a Hermitian Clifford triple;
  `P_n^± = (1 ± γ_n)/2`; `γ_n γ_v γ_n = -γ_{r_n v}`, `r_n v = v - 2 (v · n) n`.
* (2.13) For an oriented bond `(x, x')` of type `i`: `U_A(x, x') = exp(i q A(π(x), π(x')))`,
  `w(x, x') = (wᵢ/2) (ρ - γ_{(x' - x)/|x' - x|})` (`bondPhase`, `bondHopping`).
* (2.14) `(𝒟_A ψ)(x) = M ψ(x) - ∑ᵢ w(x, x^{(i)}) U_A(x, x^{(i)}) ψ(x^{(i)})` (`chamberDirac`).
* (2.15) Lattice mass `m = M - (ρ/2) ∑ᵢ wᵢ`.
* (2.16)–(2.17) Torus `𝕋 = (Γ, χ)`, `ψ(x + g) = χ(g) ψ(x)`, `𝒟_A^𝕋` of dimension `192 V`; Berezin
  normalization `∫ ∏ₓ ∏_α ψ_α(x) ψ̄_α(x) = 1`, `∫ e^{-S_𝕋(A)} = det 𝒟_A^𝕋`,
  `Z_𝕋[G] = ∫_{Conf(Γ)} e^{-‖F‖²/2} ∫_𝕋 e^{-S_𝕋(A)} G d(A, z)`.
* Prop 2.2: `det 𝒟_A^𝕋 ≥ 0` and `‖𝒟_A^𝕋‖ ≤ |M| + ((1 + ρ)/2) ∑ᵢ wᵢ` for real `A, M`;
  `Re 𝒟_A^𝕋 = m + (ρ/2) ∇_A^* ∇_A`, `(∇_A ψ)(x, i) = √(wᵢ/2) (ψ(x) - U_A(x, x^{(i)}) ψ(x^{(i)}))`.
  Proof: `𝒟_A = M - (ρ/2) H_A + (1/2) J_A`, `H_A^* = H_A`, `J_A^* = -J_A`,
  `∇_A^* ∇_A = ∑ᵢ wᵢ - H_A`, and (2.18) `𝒟_A^𝕋 = diag(𝒟̄_A^𝕋, (𝒟̄_A^𝕋)^*)`,
  `det 𝒟_A^𝕋 = |det 𝒟̄_A^𝕋|²` — a determinant, not a Pfaffian.
* (2.19)–(2.21) As a Laurent polynomial in the link variables `u_b`, the coefficient of
  `∏_{b ∥ e_μ} u_b^{32}` in `det 𝒟_A^𝕋` is `C_*^V`, via six layers `y_μ = -v₁, -v₂, -v₃, v₃, v₂,
  v₁` of `8V` sites, upward bond types (2.20) `(2, 1, 0, 1, 2, 3)`,
  `det w(x, x^↑) = (w_{i_k}/2)⁴ (1 - ρ²)²`, and
  `C_* = (w₀/2)^32 (w₁/2)^64 (w₂/2)^64 (w₃/2)^32 (1 - ρ²)^96 > 0`, independent of `M`.
* Prop 2.3, (2.22): `r_q^{3V} e^{-6 r_q² V} C_*^V ≤ Z_𝕋[1] ≤ (r_q C_q)^{3V}
  (|M| + ((1 + ρ)/2) ∑ᵢ wᵢ)^{192V}`, `r_q = 2π/q`.

## Lean objects

The link field is a `U(1)` field `u : CubicalCell X (Fin d) 1 → Circle` on the photon links, and
[Q]'s `U_A` is `u = fun b ↦ Circle.exp (q * A b)`. The spin matrices are any family
`γ : Fin d → Matrix s s ℂ`: [Q]'s `𝒟_A` is `γ = fun μ ↦ fromBlocks (σ μ) 0 0 (-σ μ)` on
`s = Fin 2 ⊕ Fin 2`, and `𝒟̄_A` is `γ = σ`. The chamber Dirac matrix is
`chamberDirac p γ w ρ M u = M • 1 - ∑ᵢ hoppingMatrix (chamberNeighbor p · i) (U(·, i) • w(·, i))`.

## Main results

* `conjTranspose_chamberDirac`: `𝒟_γᴴ = 𝒟_{-γ}` for Hermitian `γ` (reversing a bond inverts its
  phase, `bondPhase_chamberNeighbor`, and reverses its direction,
  `bondDirection_mul_wallReflection_right`).
* `reindex_chamberDirac_fromBlocks_neg` ((2.18)): `𝒟 = diag(𝒟̄, 𝒟̄ᴴ)`.
* `det_chamberDirac_fromBlocks_neg`, `det_chamberDirac_fromBlocks_neg_eq_normSq`,
  `det_chamberDirac_fromBlocks_neg_nonneg` ([Q] Prop 2.2, [M] Lemma 2.10):
  `det 𝒟 = (det 𝒟̄)⋆ det 𝒟̄ = |det 𝒟̄|² ≥ 0`, for every link field, weights, `ρ` and `M`.
* `det_chamberDirac_exp_add_coboundary`, `det_chamberDirac_of_bondPhase_eq`: gauge invariance,
  `det 𝒟_{A + dχ} = det 𝒟_A`; `det_chamberDirac_translate`: translation invariance.

## Owed

* The boundary character `χ` of [Q]'s torus `(Γ, χ)`: after a choice of representatives it is a
  `±1` factor on the link field, so it is covered by the statements for every `u`; that
  identification of the matrices is not proved here.
* The norm bound of Prop 2.2 and the upper bound of (2.22); the extreme Laurent coefficient
  (2.19)–(2.21) and the lower bound of (2.22); the covariance under the signed permutations
  (spin intertwiners `γ_n γ_5`, (2.12)); charge conjugation `C 𝒟_Aᵀ C⁻¹ = 𝒟_{-A}`.

## References

* [Q] *The Field-Strength Osterwalder–Schrader Axioms for QED in Three Dimensions*, §§2.2–2.4.
* [M] its manuscript, Definitions 2.4–2.8 and Lemma 2.10.
-/

@[expose] public section

open Equiv Finset Function Matrix SemidirectProduct CubicalCell
open scoped ComplexOrder

namespace AffineSignedPerm

/-! ### Chamber sites over a quotient of the lattice -/

section Sites

variable {ι X : Type*} [AddCommGroup X]

/-- The right action of `g : AffineSignedPerm ι` on the **chamber sites**
`(k, r) : X × SignedPerm ι` over `X`, through `p : ℤ^ι →+ X`:
`(k, r) · g = (k + p (r • t_g), r g_R)`, `t_g` the translation part. It is the image of
`⟨k, r⟩ * g` (`toChamberSite_mul`). -/
def chamberAct (p : (ι → ℤ) →+ X) (x : X × SignedPerm ι) (g : AffineSignedPerm ι) :
    X × SignedPerm ι :=
  (x.1 + p (x.2 • translationPart g), x.2 * g.right)

@[simp]
theorem chamberAct_one (p : (ι → ℤ) →+ X) (x : X × SignedPerm ι) : chamberAct p x 1 = x := by
  simp [chamberAct]

theorem chamberAct_chamberAct (p : (ι → ℤ) →+ X) (x : X × SignedPerm ι)
    (g h : AffineSignedPerm ι) :
    chamberAct p (chamberAct p x g) h = chamberAct p x (g * h) := by
  simp only [chamberAct, translationPart_mul, smul_add, mul_smul, map_add, add_assoc, mul_right,
    mul_assoc]

/-- The chamber site over `X` of the fermion site `g • v₀`: its photon site `p (translationPart g)`
and its linear part `g.right`. -/
def toChamberSite (p : (ι → ℤ) →+ X) (g : AffineSignedPerm ι) : X × SignedPerm ι :=
  (p (translationPart g), g.right)

theorem translationPart_inl_mul (k : Multiplicative (ι → ℤ)) (g : AffineSignedPerm ι) :
    translationPart (inl k * g) = k.toAdd + translationPart g := by
  rw [translationPart_mul, translationPart_inl, right_inl, one_smul]

theorem toChamberSite_mul (p : (ι → ℤ) →+ X) (g h : AffineSignedPerm ι) :
    toChamberSite p (g * h) = chamberAct p (toChamberSite p g) h := by
  simp [toChamberSite, chamberAct, translationPart_mul]

/-- **The chamber sites over `X` are the fermion sites modulo the translations in `ker p`**: for
`X = ℤ^ι ⧸ Γ` and `p` the quotient map, two fermion sites have the same chamber site iff they
differ by a period. -/
theorem toChamberSite_eq_toChamberSite_iff (p : (ι → ℤ) →+ X) {g g' : AffineSignedPerm ι} :
    toChamberSite p g = toChamberSite p g' ↔
      ∃ k ∈ p.ker, inl (Multiplicative.ofAdd k) * g = g' := by
  constructor
  · intro h
    simp only [toChamberSite, Prod.mk.injEq] at h
    refine ⟨translationPart g' - translationPart g, by rw [AddMonoidHom.mem_ker, map_sub, h.1,
      sub_self], SemidirectProduct.ext ?_ (by rw [mul_right, right_inl, one_mul, h.2])⟩
    change translationPart (inl _ * g) = translationPart g'
    rw [translationPart_inl_mul, toAdd_ofAdd, sub_add_cancel]
  · rintro ⟨k, hk, rfl⟩
    simp [toChamberSite, translationPart_inl_mul, AddMonoidHom.mem_ker.1 hk]

theorem toChamberSite_surjective {p : (ι → ℤ) →+ X} (hp : Surjective p) :
    Surjective (toChamberSite (X := X) p) := fun x ↦ by
  obtain ⟨k, hk⟩ := hp x.1
  exact ⟨⟨Multiplicative.ofAdd k, x.2⟩, Prod.ext hk rfl⟩

end Sites

/-! ### Bonds -/

section Bonds

variable {n : ℕ} {X : Type*} [AddCommGroup X]

/-- The **neighbour of type `i`** of a chamber site over `X`: `x · s_i`, `s_i = wallReflection i`
(`toChamberSite_mul_wallReflection`). -/
def chamberNeighbor (p : (Fin (n + 1) → ℤ) →+ X) (x : X × SignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) : X × SignedPerm (Fin (n + 1)) :=
  chamberAct p x (wallReflection i)

/-- The projection of the chamber graph onto the chamber sites over `X` maps bonds to bonds. -/
theorem toChamberSite_mul_wallReflection (p : (Fin (n + 1) → ℤ) →+ X)
    (g : AffineSignedPerm (Fin (n + 1))) (i : Fin (n + 2)) :
    toChamberSite p (g * wallReflection i) = chamberNeighbor p (toChamberSite p g) i :=
  toChamberSite_mul p g _

/-- Bonds are undirected: the neighbour of type `i` of the neighbour of type `i` is the site. -/
@[simp]
theorem chamberNeighbor_chamberNeighbor (p : (Fin (n + 1) → ℤ) →+ X)
    (x : X × SignedPerm (Fin (n + 1))) (i : Fin (n + 2)) :
    chamberNeighbor p (chamberNeighbor p x i) i = x := by
  rw [chamberNeighbor, chamberNeighbor, chamberAct_chamberAct, wallReflection_mul_self,
    chamberAct_one]

theorem chamberNeighbor_involutive (p : (Fin (n + 1) → ℤ) →+ X) (i : Fin (n + 2)) :
    Involutive (chamberNeighbor p · i) :=
  fun x ↦ chamberNeighbor_chamberNeighbor p x i

theorem chamberNeighbor_snd (p : (Fin (n + 1) → ℤ) →+ X) (x : X × SignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) : (chamberNeighbor p x i).2 = x.2 * (wallReflection i).right :=
  rfl

/-- A bond of type `≠ n + 1` stays over the photon site. -/
theorem chamberNeighbor_fst_of_ne (p : (Fin (n + 1) → ℤ) →+ X)
    (x : X × SignedPerm (Fin (n + 1))) {i : Fin (n + 2)} (hi : i ≠ Fin.last (n + 1)) :
    (chamberNeighbor p x i).1 = x.1 := by
  simp [chamberNeighbor, chamberAct, translationPart_wallReflection, hi]

/-- A bond of type `n + 1` at `(k, r)` lies over the photon link from `k` to `k + s • e μ`,
`μ = r.right 0`, `s = r.left μ` (so `r • e₀ = s • e μ`). -/
theorem chamberNeighbor_last_fst (p : (Fin (n + 1) → ℤ) →+ X)
    (x : X × SignedPerm (Fin (n + 1))) :
    (chamberNeighbor p x (Fin.last (n + 1))).1 =
      x.1 + ((x.2.left (x.2.right 0) : ℤ) • p (Pi.single (x.2.right 0) 1)) := by
  have h : (Pi.single (x.2.right 0) ((x.2.left (x.2.right 0) : ℤ)) : Fin (n + 1) → ℤ) =
      (x.2.left (x.2.right 0) : ℤ) • Pi.single (x.2.right 0) 1 := by
    ext j
    rcases eq_or_ne j (x.2.right 0) with rfl | hj <;> simp [*]
  rw [chamberNeighbor, chamberAct, translationPart_wallReflection, ite_eq_left rfl,
    SignedPerm.smul_single, Units.smul_def, smul_eq_mul, mul_one, h, map_zsmul]

/-- Chamber neighbours commute with the translations of the photon sites. -/
theorem chamberNeighbor_add_fst (p : (Fin (n + 1) → ℤ) →+ X) (x : X × SignedPerm (Fin (n + 1)))
    (a : X) (i : Fin (n + 2)) :
    chamberNeighbor p (x.1 + a, x.2) i =
      ((chamberNeighbor p x i).1 + a, (chamberNeighbor p x i).2) := by
  simp only [chamberNeighbor, chamberAct, add_right_comm]

end Bonds

/-! ### Bond phases, bond directions and hopping blocks -/

section Hopping

variable {n : ℕ} {X : Type*} [AddCommGroup X]

/-- The **phase** `U(x, x^{(i)})` of the bond of type `i` at `x` in a `U(1)` link field `u`. For
type `n + 1` it is the transporter along the photon link under the bond, from `k` to
`k + s • e μ` (`chamberNeighbor_last_fst`): `u (k, μ)` if `s = 1`, and `u (k - e μ, μ)⁻¹` if
`s = -1`. For the other types it is `1`: both ends lie over the same photon site. -/
noncomputable def bondPhase (p : (Fin (n + 1) → ℤ) →+ X)
    (u : CubicalCell X (Fin (n + 1)) 1 → Circle)
    (x : X × SignedPerm (Fin (n + 1))) (i : Fin (n + 2)) : Circle :=
  if i = Fin.last (n + 1) then
    if x.2.left (x.2.right 0) = 1 then u (linkEquiv (x.1, x.2.right 0))
    else (u (linkEquiv (x.1 - p (Pi.single (x.2.right 0) 1), x.2.right 0)))⁻¹
  else 1

theorem right_mul_wallReflection_last_right (r : SignedPerm (Fin (n + 1))) :
    (r * (wallReflection (Fin.last (n + 1))).right).right = r.right := by
  simp [wallReflection_last]

/-- Along a bond of type `n + 1` the sign `s = r.left (r.right 0)` is reversed. -/
theorem left_mul_wallReflection_last_right (r : SignedPerm (Fin (n + 1))) :
    (r * (wallReflection (Fin.last (n + 1))).right).left (r.right 0) = -r.left (r.right 0) := by
  simp [wallReflection_last, SignedPerm.mul_left_apply]

/-- **Reversing a bond inverts its phase**: `U(x', x) = U(x, x')⁻¹`. -/
theorem bondPhase_chamberNeighbor (p : (Fin (n + 1) → ℤ) →+ X)
    (u : CubicalCell X (Fin (n + 1)) 1 → Circle) (x : X × SignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) : bondPhase p u (chamberNeighbor p x i) i = (bondPhase p u x i)⁻¹ := by
  by_cases hi : i = Fin.last (n + 1)
  · subst hi
    have hr := right_mul_wallReflection_last_right x.2
    have hl := left_mul_wallReflection_last_right x.2
    simp only [bondPhase, ite_true, chamberNeighbor_last_fst, chamberNeighbor_snd, hr, hl]
    rcases Int.units_eq_one_or (x.2.left (x.2.right 0)) with h | h <;> rw [h]
    · simp [show (-1 : ℤˣ) ≠ 1 by decide]
    · simp [show (-1 : ℤˣ) ≠ 1 by decide, sub_eq_add_neg]
  · simp [bondPhase, hi]

/-- Bond phases commute with the translations of the photon sites. -/
theorem bondPhase_translate (p : (Fin (n + 1) → ℤ) →+ X)
    (u : CubicalCell X (Fin (n + 1)) 1 → Circle)
    (x : X × SignedPerm (Fin (n + 1))) (a : X) (i : Fin (n + 2)) :
    bondPhase p (fun c ↦ u ⟨c.site + a, c.dirs⟩) x i = bondPhase p u (x.1 + a, x.2) i := by
  simp only [bondPhase, linkEquiv_apply, sub_add_eq_add_sub]

/-- The reflection in a wall reverses its normal. -/
theorem wallReflection_right_smul_wallNormal (i : Fin (n + 2)) :
    (wallReflection i).right • (fun μ ↦ (wallNormal i μ : ℝ)) =
      -fun μ ↦ (wallNormal i μ : ℝ) := by
  have h := intCast_two_div_mul_dotProduct_self (wallNormal_dotProduct_self_dvd i)
  rw [wallReflection_eq_mirrorReflection]
  change SignedPerm.reflection (wallNormal i) (wallNormal_dotProduct_self_dvd i) • _ = _
  rw [SignedPerm.reflection_smul, h, two_smul, sub_add_cancel_left]

theorem intCast_wallNormal_dotProduct_self_pos (i : Fin (n + 2)) :
    (0 : ℝ) < ((wallNormal i ⬝ᵥ wallNormal i : ℤ) : ℝ) := by
  rcases dotProduct_self_eq_one_or_two (wallNormal_dotProduct_self_dvd i) with h | h <;>
    rw [h] <;> norm_num

/-- The **unit vector of a bond**, `(x^{(i)} - x) / |x^{(i)} - x| = -r n̂_i` for the bond of type
`i` at a site with linear part `r`, `n̂_i = n_i / |n_i|` the unit inward normal of wall `i`. It
does not depend on the base point (`mul_wallReflection_smul_sub_smul_eq`). -/
noncomputable def bondDirection (r : SignedPerm (Fin (n + 1))) (i : Fin (n + 2)) :
    Fin (n + 1) → ℝ :=
  -((√((wallNormal i ⬝ᵥ wallNormal i : ℤ) : ℝ))⁻¹ • (r • fun μ ↦ (wallNormal i μ : ℝ)))

/-- **Reversing a bond reverses its direction.** -/
theorem bondDirection_mul_wallReflection_right (r : SignedPerm (Fin (n + 1))) (i : Fin (n + 2)) :
    bondDirection (r * (wallReflection i).right) i = -bondDirection r i := by
  rw [bondDirection, bondDirection, mul_smul, wallReflection_right_smul_wallNormal, smul_neg,
    smul_neg]

theorem bondDirection_dotProduct_self (r : SignedPerm (Fin (n + 1))) (i : Fin (n + 2)) :
    bondDirection r i ⬝ᵥ bondDirection r i = 1 := by
  have hN := intCast_wallNormal_dotProduct_self_pos i
  rw [bondDirection, neg_dotProduct, dotProduct_neg, neg_neg, dotProduct_smul, smul_dotProduct,
    SignedPerm.dotProduct_smul_smul, intCast_dotProduct_intCast, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hN.le, inv_mul_cancel₀ hN.ne']

/-- **The bond direction is the unit vector of the bond** for every base point `v`:
`(g s_i) • v - g • v = (φ_i(v) |n_i|) • bondDirection g.right i`, with `φ_i = wallFunctional i`
positive on the fundamental chamber (`mem_fundamentalChamber_iff`) and
`bondDirection_dotProduct_self`. This is the direction `(x' - x) / |x' - x|` of (2.13). -/
theorem mul_wallReflection_smul_sub_smul_eq (g : AffineSignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) (v : Fin (n + 1) → ℝ) :
    (g * wallReflection i) • v - g • v =
      (wallFunctional i v * √((wallNormal i ⬝ᵥ wallNormal i : ℤ) : ℝ)) •
        bondDirection g.right i := by
  have hs := (Real.sqrt_pos.2 (intCast_wallNormal_dotProduct_self_pos i)).ne'
  rw [mul_wallReflection_smul_sub_smul, bondDirection, smul_neg, smul_smul, mul_assoc,
    mul_inv_cancel₀ hs, mul_one, neg_smul]

variable {s : Type*} [DecidableEq s]

/-- The **hopping block** (2.13) of the bond of type `i` at a site with linear part `r`, for spin
matrices `γ`: `w(x, x^{(i)}) = (w_i / 2) (ρ - γ_d)`, `γ_d = ∑ μ, d μ • γ μ`,
`d = bondDirection r i`. -/
noncomputable def bondHopping (γ : Fin (n + 1) → Matrix s s ℂ) (w : Fin (n + 2) → ℝ) (ρ : ℝ)
    (r : SignedPerm (Fin (n + 1))) (i : Fin (n + 2)) : Matrix s s ℂ :=
  ((w i / 2 : ℝ) : ℂ) • ((ρ : ℂ) • 1 - ∑ μ, (bondDirection r i μ : ℂ) • γ μ)

/-- **The reversed hopping block is the adjoint with the opposite spin matrices**: for Hermitian
`γ`, `w(x', x)ᴴ` is the block of `x → x'` for `-γ`. -/
theorem conjTranspose_bondHopping {γ : Fin (n + 1) → Matrix s s ℂ}
    (hγ : ∀ μ, (γ μ).IsHermitian) (w : Fin (n + 2) → ℝ) (ρ : ℝ) (r : SignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) :
    (bondHopping γ w ρ (r * (wallReflection i).right) i)ᴴ = bondHopping (-γ) w ρ r i := by
  have hγ' : ∀ μ, (γ μ)ᴴ = γ μ := fun μ ↦ (hγ μ).eq
  simp only [bondHopping, conjTranspose_smul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_sum, conjTranspose_neg, hγ', bondDirection_mul_wallReflection_right,
    Pi.neg_apply, Complex.ofReal_neg, neg_smul, smul_neg, Complex.star_def, Complex.conj_ofReal]

/-- Block-diagonal spin matrices give block-diagonal hopping blocks. -/
theorem bondHopping_fromBlocks {t : Type*} [DecidableEq t] (σ : Fin (n + 1) → Matrix s s ℂ)
    (τ : Fin (n + 1) → Matrix t t ℂ) (w : Fin (n + 2) → ℝ) (ρ : ℝ)
    (r : SignedPerm (Fin (n + 1))) (i : Fin (n + 2)) :
    bondHopping (fun μ ↦ fromBlocks (σ μ) 0 0 (τ μ)) w ρ r i =
      fromBlocks (bondHopping σ w ρ r i) 0 0 (bondHopping τ w ρ r i) := by
  ext (α | α) (β | β) <;> simp [bondHopping, Matrix.sum_apply, one_apply]

end Hopping

/-! ### The chamber Dirac matrix -/

section Dirac

variable {n : ℕ} {X : Type*} [AddCommGroup X] [DecidableEq X] {s : Type*} [DecidableEq s]
  (p : (Fin (n + 1) → ℤ) →+ X) (γ : Fin (n + 1) → Matrix s s ℂ) (w : Fin (n + 2) → ℝ)
  (ρ M : ℝ) (u : CubicalCell X (Fin (n + 1)) 1 → Circle)

/-- **The chamber Dirac matrix** (2.14) over `X` with spin matrices `γ`, weights `w`, Wilson
parameter `ρ`, mass parameter `M` and `U(1)` link field `u`:
`(𝒟 ψ)(x) = M ψ(x) - ∑ᵢ w(x, x^{(i)}) U(x, x^{(i)}) ψ(x^{(i)})`. -/
noncomputable def chamberDirac :
    Matrix ((X × SignedPerm (Fin (n + 1))) × s) ((X × SignedPerm (Fin (n + 1))) × s) ℂ :=
  (M : ℂ) • 1 - ∑ i, hoppingMatrix (chamberNeighbor p · i) fun x ↦
    (bondPhase p u x i : ℂ) • bondHopping γ w ρ x.2 i

theorem chamberDirac_apply (a b : (X × SignedPerm (Fin (n + 1))) × s) :
    chamberDirac p γ w ρ M u a b = (if a = b then (M : ℂ) else 0) -
      ∑ i, if chamberNeighbor p a.1 i = b.1 then
        (bondPhase p u a.1 i : ℂ) * bondHopping γ w ρ a.1.2 i a.2 b.2 else 0 := by
  simp [chamberDirac, one_apply, hoppingMatrix_apply, Matrix.sum_apply]

variable {γ} in
/-- **The adjoint of the chamber Dirac matrix** (Hermitian `γ`, real `M`) is the chamber Dirac
matrix with spin matrices `-γ`: the scalar hopping part is self-adjoint and the spin hopping part
skew-adjoint ([Q] Prop 2.2, [M] Lemma 2.10). -/
theorem conjTranspose_chamberDirac (hγ : ∀ μ, (γ μ).IsHermitian) :
    (chamberDirac p γ w ρ M u)ᴴ = chamberDirac p (-γ) w ρ M u := by
  simp only [chamberDirac, conjTranspose_sub, conjTranspose_smul, conjTranspose_one,
    conjTranspose_sum, conjTranspose_hoppingMatrix (chamberNeighbor_involutive p _),
    bondPhase_chamberNeighbor, chamberNeighbor_snd, conjTranspose_bondHopping hγ,
    Circle.coe_inv_eq_conj, Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]

/-- Block-diagonal spin matrices give a block-diagonal chamber Dirac matrix. -/
theorem reindex_chamberDirac_fromBlocks {t : Type*} [DecidableEq t]
    (σ : Fin (n + 1) → Matrix s s ℂ) (τ : Fin (n + 1) → Matrix t t ℂ) :
    reindex (prodSumDistrib _ s t) (prodSumDistrib _ s t)
        (chamberDirac p (fun μ ↦ fromBlocks (σ μ) 0 0 (τ μ)) w ρ M u) =
      fromBlocks (chamberDirac p σ w ρ M u) 0 0 (chamberDirac p τ w ρ M u) := by
  ext (⟨x, α⟩ | ⟨x, α⟩) (⟨y, β⟩ | ⟨y, β⟩) <;>
    simp [chamberDirac_apply, bondHopping_fromBlocks]

variable {σ : Fin (n + 1) → Matrix s s ℂ}

/-- **(2.18)**: for `γ_μ = diag(σ_μ, -σ_μ)` on `s ⊕ s` with Hermitian `σ_μ`, the chamber Dirac
matrix is `diag(𝒟̄, 𝒟̄ᴴ)`, `𝒟̄` the chamber Dirac matrix with spin matrices `σ`. -/
theorem reindex_chamberDirac_fromBlocks_neg (hσ : ∀ μ, (σ μ).IsHermitian) :
    reindex (prodSumDistrib _ s s) (prodSumDistrib _ s s)
        (chamberDirac p (fun μ ↦ fromBlocks (σ μ) 0 0 (-σ μ)) w ρ M u) =
      fromBlocks (chamberDirac p σ w ρ M u) 0 0 (chamberDirac p σ w ρ M u)ᴴ := by
  rw [reindex_chamberDirac_fromBlocks, conjTranspose_chamberDirac p w ρ M u hσ]
  rfl

variable [Fintype X] [Fintype s]

/-- **[Q] (2.18)**: `det 𝒟 = |det 𝒟̄|²`, as `det 𝒟 = (det 𝒟̄)⋆ det 𝒟̄`. -/
theorem det_chamberDirac_fromBlocks_neg (hσ : ∀ μ, (σ μ).IsHermitian) :
    det (chamberDirac p (fun μ ↦ fromBlocks (σ μ) 0 0 (-σ μ)) w ρ M u) =
      star (det (chamberDirac p σ w ρ M u)) * det (chamberDirac p σ w ρ M u) := by
  rw [← det_reindex_self (prodSumDistrib (X × SignedPerm (Fin (n + 1))) s s),
    reindex_chamberDirac_fromBlocks_neg p w ρ M u hσ, det_fromBlocks_zero₂₁, det_conjTranspose,
    mul_comm]

theorem det_chamberDirac_fromBlocks_neg_eq_normSq (hσ : ∀ μ, (σ μ).IsHermitian) :
    det (chamberDirac p (fun μ ↦ fromBlocks (σ μ) 0 0 (-σ μ)) w ρ M u) =
      (Complex.normSq (det (chamberDirac p σ w ρ M u)) : ℂ) := by
  rw [det_chamberDirac_fromBlocks_neg p w ρ M u hσ, Complex.normSq_eq_conj_mul_self]
  rfl

/-- **The chamber determinant is nonnegative** ([Q] Proposition 2.2, [M] Lemma 2.10): for every
`U(1)` link field, real weights, Wilson parameter and mass, `det 𝒟 ≥ 0` in `ℂ` (real and
nonnegative). -/
theorem det_chamberDirac_fromBlocks_neg_nonneg (hσ : ∀ μ, (σ μ).IsHermitian) :
    0 ≤ det (chamberDirac p (fun μ ↦ fromBlocks (σ μ) 0 0 (-σ μ)) w ρ M u) := by
  rw [det_chamberDirac_fromBlocks_neg p w ρ M u hσ]
  exact star_mul_self_nonneg _

end Dirac

/-! ### Gauge and translation covariance -/

section Covariance

variable {n : ℕ} {X : Type*} [AddCommGroup X] [DecidableEq X] {s : Type*} [DecidableEq s]
  (p : (Fin (n + 1) → ℤ) →+ X) (γ : Fin (n + 1) → Matrix s s ℂ) (w : Fin (n + 2) → ℝ)
  (ρ M : ℝ)

/-- **Gauge covariance**: if the bond phases of `u'` are those of `u` conjugated by
`c : X → U(1)` at the photon sites of the two ends, the chamber Dirac matrices are conjugate by
the site-diagonal unitary `c ∘ π`. -/
theorem chamberDirac_eq_diagonal_mul_mul_diagonal [Fintype X] [Fintype s]
    {u u' : CubicalCell X (Fin (n + 1)) 1 → Circle} (c : X → Circle)
    (h : ∀ x i, bondPhase p u' x i = (c x.1)⁻¹ * bondPhase p u x i * c (chamberNeighbor p x i).1) :
    chamberDirac p γ w ρ M u' = diagonal (fun a ↦ (((c a.1.1)⁻¹ : Circle) : ℂ)) *
      chamberDirac p γ w ρ M u * diagonal (fun a ↦ (c a.1.1 : ℂ)) := by
  ext a b
  rw [mul_diagonal, diagonal_mul, chamberDirac_apply, chamberDirac_apply, mul_sub, sub_mul,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  · split_ifs with hab
    · rw [hab, mul_comm, ← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul]
    · rw [mul_zero, zero_mul]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with hN
    · rw [h, ← hN, Circle.coe_mul, Circle.coe_mul]
      ring
    · rw [mul_zero, zero_mul]

theorem det_chamberDirac_of_bondPhase_eq [Fintype X] [Fintype s]
    {u u' : CubicalCell X (Fin (n + 1)) 1 → Circle} (c : X → Circle)
    (h : ∀ x i, bondPhase p u' x i = (c x.1)⁻¹ * bondPhase p u x i * c (chamberNeighbor p x i).1) :
    det (chamberDirac p γ w ρ M u') = det (chamberDirac p γ w ρ M u) := by
  have h1 : (fun a : (X × SignedPerm (Fin (n + 1))) × s ↦
      (((c a.1.1)⁻¹ : Circle) : ℂ) * (c a.1.1 : ℂ)) = fun _ ↦ 1 := by
    funext a
    rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  rw [chamberDirac_eq_diagonal_mul_mul_diagonal p γ w ρ M c h, det_mul, det_mul, mul_right_comm,
    ← det_mul, diagonal_mul_diagonal, h1, diagonal_one, det_one, one_mul]

omit [DecidableEq X] in
/-- **Gauge covariance of the bond phases** of a real gauge field ([Q] §2.4):
`U_{A + dχ}(x, x') = e^{-iqχ(π x)} U_A(x, x') e^{iqχ(π x')}`, `U_A = e^{iqA}`. -/
theorem bondPhase_exp_add_coboundary (q : ℝ) (A : CubicalCell X (Fin (n + 1)) 1 → ℝ)
    (χ : CubicalCell X (Fin (n + 1)) 0 → ℝ) (x : X × SignedPerm (Fin (n + 1)))
    (i : Fin (n + 2)) :
    bondPhase p (fun b ↦ Circle.exp
        (q * (A + CubicalCochain.coboundary (fun μ ↦ p (Pi.single μ 1)) 0 χ) b)) x i =
      (Circle.exp (q * χ (vertexEquiv x.1)))⁻¹ * bondPhase p (fun b ↦ Circle.exp (q * A b)) x i *
        Circle.exp (q * χ (vertexEquiv (chamberNeighbor p x i).1)) := by
  by_cases hi : i = Fin.last (n + 1)
  · subst hi
    rw [chamberNeighbor_last_fst]
    simp only [bondPhase, ite_true]
    rcases Int.units_eq_one_or (x.2.left (x.2.right 0)) with hs | hs <;> rw [hs]
    · simp only [ite_true, Pi.add_apply, CubicalCochain.coboundary_zero_apply, Units.val_one,
        one_smul]
      rw [← Circle.exp_neg, ← Circle.exp_add, ← Circle.exp_add]
      congr 1
      ring
    · simp only [show (-1 : ℤˣ) ≠ 1 by decide, ite_false, Pi.add_apply,
        CubicalCochain.coboundary_zero_apply, sub_add_cancel, Units.val_neg, Units.val_one,
        neg_smul, one_smul, ← sub_eq_add_neg]
      simp only [← Circle.exp_neg, ← Circle.exp_add]
      congr 1
      ring
  · simp only [bondPhase, hi, ite_false, chamberNeighbor_fst_of_ne p x hi, mul_one,
      inv_mul_cancel]

/-- **The chamber determinant is gauge invariant**: `det 𝒟_{A + dχ} = det 𝒟_A`. -/
theorem det_chamberDirac_exp_add_coboundary [Fintype X] [Fintype s] (q : ℝ)
    (A : CubicalCell X (Fin (n + 1)) 1 → ℝ) (χ : CubicalCell X (Fin (n + 1)) 0 → ℝ) :
    det (chamberDirac p γ w ρ M fun b ↦ Circle.exp
        (q * (A + CubicalCochain.coboundary (fun μ ↦ p (Pi.single μ 1)) 0 χ) b)) =
      det (chamberDirac p γ w ρ M fun b ↦ Circle.exp (q * A b)) :=
  det_chamberDirac_of_bondPhase_eq p γ w ρ M (fun k ↦ Circle.exp (q * χ (vertexEquiv k)))
    (bondPhase_exp_add_coboundary p q A χ)

/-- **Translation covariance**: translating the link field by `a` translates the chamber Dirac
matrix, `𝒟_{τ_a^* u} = 𝒟_u ∘ (τ_a × τ_a)`. -/
theorem chamberDirac_translate (u : CubicalCell X (Fin (n + 1)) 1 → Circle) (a : X) :
    chamberDirac p γ w ρ M (fun c ↦ u ⟨c.site + a, c.dirs⟩) =
      (chamberDirac p γ w ρ M u).submatrix
        (prodCongr (prodCongr (Equiv.addRight a) (.refl _)) (.refl s))
        (prodCongr (prodCongr (Equiv.addRight a) (.refl _)) (.refl s)) := by
  ext ⟨⟨k, r⟩, α⟩ ⟨⟨k', r'⟩, β⟩
  simp only [submatrix_apply, prodCongr_apply, coe_addRight, coe_refl, Prod.map_apply, id_eq,
    chamberDirac_apply, bondPhase_translate]
  congr 1
  · simp only [Prod.mk.injEq, add_left_inj]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := chamberNeighbor_add_fst p (k, r) a i
    simp only at h
    rw [h]
    simp only [Prod.ext_iff, add_left_inj]

theorem det_chamberDirac_translate [Fintype X] [Fintype s]
    (u : CubicalCell X (Fin (n + 1)) 1 → Circle) (a : X) :
    det (chamberDirac p γ w ρ M fun c ↦ u ⟨c.site + a, c.dirs⟩) =
      det (chamberDirac p γ w ρ M u) := by
  rw [chamberDirac_translate, det_submatrix_equiv_self]

end Covariance

end AffineSignedPerm
