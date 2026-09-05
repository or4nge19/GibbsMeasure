/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.ReflectionPositivity
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.Pi
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.PiReflectionComplex

/-!
# Georgii §17.1 (17.12)–(17.17) and §17.2: elementary cubes and periodic Gibbs distributions

## The coarse-graining of §17.1

Theorem (17.11) bounds products of functions of single spins.  Georgii's (17.12)–(17.17) extend
it to functions of the spins in the elementary cubes `C(i) = C + i mod Λ`, `C = {0, 1}^d`
(17.12)–(17.13), by applying (17.11) to the image `μ* = μ ∘ (ω ↦ ω*)⁻¹` of `μ` under the
coarse-graining `ω ↦ ω* = (ω_{C(i)})_{i ∈ Λ}` (`cubeView`), with state space `E^C` and the
reflections `r_k` of the cube (`cubeRefl`, (17.14)) in the rôle of the involutions `τ_k`.

* `hatReflAt`, `hatReflection`: **Georgii (17.15)**, the reflection `r̂_k` of the torus in a
  plane *through* the sites (`z ↦ -z` in the `k`-th coordinate), and `hatPosAt` is his
  `Λ̂_{+,k}`.  In the coordinates of this file (see `ReflectionPositivity.lean`) the plane meets
  the torus in `{i : i_k ∈ {0, N}}`, Georgii's `L_k`.
* `cubeView_hatReflection`: the identity `(r̂_k ω)* = r̃_k (ω*)` of Georgii's proof of (17.16).
* `isReflectionPositive_map_cubeView`: **Georgii, Lemma (17.16)**: if `μ` is `r̂_k`-positive
  then `μ*` is `r̃_k`-positive.
* `abs_integral_prod_cubeView_pow_le`: **Georgii, Corollary (17.17)**, the chessboard estimate
  for functions of the elementary cubes.

## Gibbs distributions with periodic boundary condition, §17.2

Georgii's `C`-potentials (17.18) are the shift-invariant potentials supported on the translates
of the unit cube; such a potential is determined by the single function `Φ_C : E^C → ℝ`, which
is the datum `φ` here, and its periodic Hamiltonian in `Λ` is `∑_{i ∈ Λ} Φ_{C(i)}`
(`periodicHamiltonian`).  The Gibbs distribution `°γ_Λ^Φ` with periodic boundary condition
(Example (4.20)(2)) has the density (17.20) `exp(-∑_i Φ_{C(i)})/°Z` relative to `λ^Λ`;
`periodicGibbs φ ν` is the measure `°Z · °γ_Λ^Φ` with that density before normalisation, and
`periodicGibbsDist φ ν` is `°γ_Λ^Φ` itself.

* `measurePreserving_shift_periodicGibbs`: `°γ_Λ^Φ` is `Λ`-periodic (Georgii's remark after
  (17.20)).
* `measurePreserving_hatReflection_periodicGibbs`: `°γ_Λ^Φ` is `r̂_k`-invariant when `Φ_C` is
  invariant under the reflection `r_k` of the cube, condition (iii) of (17.18).
* `isReflectionPositive_hatReflection_pi`: the product measure `λ^Λ` is `r̂_k`-positive, the
  Fubini argument of the proof of (17.21) (`MeasureTheory.integral_mul_comp_nonneg`).
* `isReflectionPositive_hatReflection_periodicGibbs`: **Georgii, Theorem (17.21)**: `°γ_Λ^Φ`
  is `r̂_k`-positive for every `k`.  Condition (iv) of (17.18) enters only through the lower
  bound on `Φ_C` it implies, which is what makes the densities bounded.
* `abs_integral_prod_cubeView_pow_le_periodicGibbsDist`: the payoff, **(17.17) applied to
  `°γ_Λ^Φ`** — the chessboard estimate for functions of the elementary cubes under the periodic
  Gibbs distribution of a `C`-potential.  This is the statement Georgii's Chapters 18 and 19 use.

## `r_k`-positivity and Lemma (17.26)

Georgii's second reflection, `r_k` of (17.5), is in a plane *between* the sites; the associated
transformation of `E^Λ` is `siteEquiv E (torusReflAt N k)` (that is, `genReflectionAt N τ k` with
`τ_k = id`), and no separate definition is needed for `r_k`-positivity: it is
`IsReflectionPositive (torusPosAt N k) (siteEquiv E (torusReflAt N k))`.

* `torusPosAt_iff_torusReflAt_notMem`: `r_k` fixes no site and exchanges the two halves.
* `isReflectionPositive_siteEquiv_pi`: `λ^Λ` is `r_k`-positive.
* `isReflectionPositive_siteEquiv_withDensity`: **Georgii, Lemma (17.26)**, the criterion for
  `r_k`-positivity of a measure whose `λ^Λ`-density is `exp[h + h* + ∫ m(dw) h_w h_w*]`.  Its
  analytic content is `MeasureTheory.integral_mul_comp_mul_exp_nonneg`.
* `isReflectionPositive_siteEquiv_withDensity_sum`: the case of a finite sum
  `exp[h + h∘r_k + ∑_a g_a · g_a∘r_k]` with real `g_a`, which is the shape a lattice model with a
  nonnegative crossing interaction has (Georgii's Example (17.30)).

Georgii's Heisenberg potentials (17.22)–(17.25), his notion (17.27) of a function on `ℤ^d`
nonnegative definite relative to `r_k`, and Theorem (17.29) with its Examples (17.30)–(17.32)
are not formalised: (17.26), which is what (17.29) is proved from, is.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The elementary cubes, Georgii (17.12)–(17.15) -/

section Cube

variable {E : Type*} [MeasurableSpace E] {N d : ℕ}

/-- A corner `c ∈ C = {0, 1}^d` of the unit cube, as a site of the torus `(ℤ/2N)^d`. -/
def cubeCast (N : ℕ) (c : Fin d → Fin 2) : Fin d → ZMod (2 * N) :=
  fun k ↦ ((c k : ℕ) : ZMod (2 * N))

/-- **Georgii (17.13).** The coarse-graining `ω ↦ ω* = (ω_{C(i)})_{i ∈ Λ}`: the value of `ω*`
at `i` is the restriction of `ω` to the elementary cube `C(i) = C + i mod Λ`, read as an
element of `E^C` through `c ↦ i + c`. -/
def cubeView (ω : (Fin d → ZMod (2 * N)) → E) (i : Fin d → ZMod (2 * N)) :
    (Fin d → Fin 2) → E :=
  fun c ↦ ω (i + cubeCast N c)

omit [MeasurableSpace E] in
@[simp] lemma cubeView_apply (ω : (Fin d → ZMod (2 * N)) → E) (i : Fin d → ZMod (2 * N))
    (c : Fin d → Fin 2) : cubeView ω i c = ω (i + cubeCast N c) := rfl

lemma measurable_cubeView : Measurable (cubeView (E := E) (N := N) (d := d)) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

/-- The reflection of the unit cube `C = {0, 1}^d` in direction `k`, `c_k ↦ 1 - c_k`. -/
def cubeSiteRefl (k : Fin d) : (Fin d → Fin 2) ≃ (Fin d → Fin 2) where
  toFun c := Function.update c k (Fin.rev (c k))
  invFun c := Function.update c k (Fin.rev (c k))
  left_inv c := by simp [Function.update_idem]
  right_inv c := by simp [Function.update_idem]

omit [MeasurableSpace E] in
lemma cubeSiteRefl_apply (k : Fin d) (c : Fin d → Fin 2) :
    cubeSiteRefl k c = Function.update c k (Fin.rev (c k)) := rfl

omit [MeasurableSpace E] in
@[simp] lemma cubeSiteRefl_symm (k : Fin d) : (cubeSiteRefl k).symm = cubeSiteRefl k := rfl

omit [MeasurableSpace E] in
lemma cubeSiteRefl_cubeSiteRefl (k : Fin d) (c : Fin d → Fin 2) :
    cubeSiteRefl k (cubeSiteRefl k c) = c := (cubeSiteRefl k).left_inv c

variable (E) in
/-- **Georgii (17.14), one factor.** The reflection `r_k` of `E^C` induced by the reflection of
the cube in direction `k`: a measurable involution of `E^C`, which plays the rôle of the spin
involution `τ_k` in the coarse-grained chessboard estimate. -/
def cubeRefl (k : Fin d) : ((Fin d → Fin 2) → E) ≃ᵐ ((Fin d → Fin 2) → E) :=
  MeasurableEquiv.arrowCongr' (cubeSiteRefl k) (MeasurableEquiv.refl E)

@[simp] lemma cubeRefl_apply (k : Fin d) (ζ : (Fin d → Fin 2) → E) (c : Fin d → Fin 2) :
    cubeRefl E k ζ c = ζ (cubeSiteRefl k c) := rfl

lemma cubeRefl_cubeRefl (k : Fin d) (ζ : (Fin d → Fin 2) → E) :
    cubeRefl E k (cubeRefl E k ζ) = ζ := by
  funext c
  rw [cubeRefl_apply, cubeRefl_apply, cubeSiteRefl_cubeSiteRefl]

/-- **Georgii (17.15).** The reflection `r̂_k` of the torus in a plane *through* the sites:
`z ↦ -z` in the `k`-th coordinate, which fixes the sites with `z_k ∈ {0, N}`. -/
def hatReflAt (N : ℕ) (k : Fin d) : (Fin d → ZMod (2 * N)) ≃ (Fin d → ZMod (2 * N)) where
  toFun i := Function.update i k (-(i k))
  invFun i := Function.update i k (-(i k))
  left_inv i := by simp [Function.update_idem]
  right_inv i := by simp [Function.update_idem]

omit [MeasurableSpace E] in
lemma hatReflAt_apply (k : Fin d) (i : Fin d → ZMod (2 * N)) :
    hatReflAt N k i = Function.update i k (-(i k)) := rfl

omit [MeasurableSpace E] in
@[simp] lemma hatReflAt_symm (k : Fin d) : (hatReflAt N k).symm = hatReflAt N k := rfl

omit [MeasurableSpace E] in
@[simp] lemma hatReflAt_apply_self (k : Fin d) (i : Fin d → ZMod (2 * N)) :
    hatReflAt N k i k = -(i k) := by simp [hatReflAt_apply]

omit [MeasurableSpace E] in
lemma hatReflAt_hatReflAt (k : Fin d) (i : Fin d → ZMod (2 * N)) :
    hatReflAt N k (hatReflAt N k i) = i := (hatReflAt N k).left_inv i

variable (E) in
/-- Georgii's `r̂_k` acting on configurations, `(r̂_k ω)_i = ω_{r̂_k i}`. -/
def hatReflection (N : ℕ) (k : Fin d) : Transformation (Fin d → ZMod (2 * N)) E :=
  siteEquiv E (hatReflAt N k)

@[simp] lemma hatReflection_toFun_apply (k : Fin d) (ω : (Fin d → ZMod (2 * N)) → E)
    (i : Fin d → ZMod (2 * N)) : (hatReflection E N k).toFun ω i = ω (hatReflAt N k i) := by
  rw [hatReflection, siteEquiv_toFun_apply, hatReflAt_symm]

lemma hatReflection_toFun (k : Fin d) (ω : (Fin d → ZMod (2 * N)) → E) :
    (hatReflection E N k).toFun ω = ω ∘ hatReflAt N k :=
  funext fun i ↦ hatReflection_toFun_apply k ω i

lemma hatReflection_involutive (k : Fin d) (ω : (Fin d → ZMod (2 * N)) → E) :
    (hatReflection E N k).toFun ((hatReflection E N k).toFun ω) = ω := by
  funext i
  rw [hatReflection_toFun_apply, hatReflection_toFun_apply, hatReflAt_hatReflAt]

/-- **Georgii's `Λ̂_{+,k}`**, the half `{i : 0 ≤ i_k ≤ N}` of the torus on one side of the plane
of `r̂_k`, including the plane itself. -/
def hatPosAt (N : ℕ) (k : Fin d) : Set (Fin d → ZMod (2 * N)) := {i | (i k).val ≤ N}

omit [MeasurableSpace E] in
@[simp] lemma mem_hatPosAt {k : Fin d} {i : Fin d → ZMod (2 * N)} :
    i ∈ hatPosAt N k ↔ (i k).val ≤ N := Iff.rfl

/-! #### The identity `(r̂_k ω)* = r̃_k (ω*)` of the proof of (17.16) -/

omit [MeasurableSpace E] in
lemma natCast_rev (v : Fin 2) :
    ((Fin.rev v : ℕ) : ZMod (2 * N)) = 1 - ((v : ℕ) : ZMod (2 * N)) := by
  have hv : (v : ℕ) ≤ 1 := by have := v.isLt; omega
  rw [Fin.val_rev, show 2 - ((v : ℕ) + 1) = 1 - (v : ℕ) by omega, Nat.cast_sub hv, Nat.cast_one]

omit [MeasurableSpace E] in
lemma hatReflAt_add_cubeCast (k : Fin d) (i : Fin d → ZMod (2 * N)) (c : Fin d → Fin 2) :
    hatReflAt N k (i + cubeCast N c) = torusReflAt N k i + cubeCast N (cubeSiteRefl k c) := by
  funext l
  by_cases hl : l = k
  · subst hl
    simp only [hatReflAt_apply, torusReflAt_apply, cubeSiteRefl_apply, Pi.add_apply,
      Function.update_self, cubeCast, natCast_rev]
    ring
  · simp only [hatReflAt_apply, torusReflAt_apply, cubeSiteRefl_apply, Pi.add_apply,
      Function.update_of_ne hl, cubeCast]

/-- **Georgii, proof of (17.16).** The coarse-graining intertwines the reflection `r̂_k`
through the sites with the two-stage reflection `r̃_k` of `(E^C)^Λ`: reflect the cubes by `r_k`
and each cube by `r_k`. -/
lemma cubeView_hatReflection (k : Fin d) (ω : (Fin d → ZMod (2 * N)) → E)
    (i : Fin d → ZMod (2 * N)) :
    cubeView ((hatReflection E N k).toFun ω) i = cubeRefl E k (cubeView ω (torusReflAt N k i)) := by
  funext c
  rw [cubeRefl_apply, cubeView_apply, cubeView_apply, hatReflection_toFun_apply,
    hatReflAt_add_cubeCast]

lemma genReflectionAt_cubeRefl_cubeView (k : Fin d) (ω : (Fin d → ZMod (2 * N)) → E) :
    (genReflectionAt N (cubeRefl E) k).toFun (cubeView ω)
      = cubeView ((hatReflection E N k).toFun ω) := by
  funext i
  rw [genReflectionAt_toFun_apply, cubeView_hatReflection]

lemma cubeView_shift (j : Fin d → ZMod (2 * N)) (ω : (Fin d → ZMod (2 * N)) → E) :
    cubeView ((shift E j).toFun ω) = (shift ((Fin d → Fin 2) → E) j).toFun (cubeView ω) := by
  funext i c
  simp [sub_add_eq_add_sub]

/-! #### Cylinder measurability of the coarse-graining -/

variable [NeZero N]

/-- The cube `C(i)` with `0 ≤ i_k ≤ N - 1` lies in `Λ̂_{+,k}`. -/
lemma measurable_cubeView_apply_cylinderEvents {k : Fin d} {i : Fin d → ZMod (2 * N)}
    (hi : (i k).val < N) :
    Measurable[cylinderEvents (X := fun _ : Fin d → ZMod (2 * N) ↦ E) (hatPosAt N k)]
      fun ω ↦ cubeView ω i := by
  let : MeasurableSpace ((Fin d → ZMod (2 * N)) → E) :=
    cylinderEvents (X := fun _ : Fin d → ZMod (2 * N) ↦ E) (hatPosAt N k)
  refine measurable_pi_lambda _ fun c ↦ ?_
  refine measurable_cylinderEvent_apply (X := fun _ : Fin d → ZMod (2 * N) ↦ E) ?_
  show ((i + cubeCast N c) k).val ≤ N
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc : ((c k : ℕ) : ZMod (2 * N)).val = (c k : ℕ) :=
    ZMod.val_natCast_of_lt (by have := (c k).isLt; omega)
  rw [Pi.add_apply, cubeCast, ZMod.val_add_of_lt (by rw [hc]; have := (c k).isLt; omega), hc]
  have := (c k).isLt
  omega

lemma measurable_cubeView_cylinderEvents (k : Fin d) :
    Measurable[cylinderEvents (X := fun _ : Fin d → ZMod (2 * N) ↦ E) (hatPosAt N k),
      cylinderEvents (X := fun _ : Fin d → ZMod (2 * N) ↦ (Fin d → Fin 2) → E) (torusPosAt N k)]
      (cubeView (E := E) (N := N) (d := d)) := by
  let : MeasurableSpace ((Fin d → ZMod (2 * N)) → E) :=
    cylinderEvents (X := fun _ : Fin d → ZMod (2 * N) ↦ E) (hatPosAt N k)
  exact measurable_cylinderEvents_iff.2 fun i hi ↦ measurable_cubeView_apply_cylinderEvents hi

/-! #### Georgii (17.16) and (17.17) -/

variable {μ : Measure ((Fin d → ZMod (2 * N)) → E)}

/-- **Georgii, Lemma (17.16).** If `μ` is `r̂_k`-positive then its coarse-graining `μ*` is
`r̃_k`-positive, for the generalized reflection built from the cube reflection `r_k`. -/
theorem isReflectionPositive_map_cubeView {k : Fin d}
    (hpos : IsReflectionPositive (hatPosAt N k) (hatReflection E N k) μ) :
    IsReflectionPositive (torusPosAt N k) (genReflectionAt N (cubeRefl E) k) (μ.map cubeView) :=
  hpos.map measurable_cubeView (measurable_cubeView_cylinderEvents k)
    (genReflectionAt_cubeRefl_cubeView k)

omit [NeZero N] in
/-- The coarse-graining of a `Λ`-periodic measure is `Λ`-periodic (Georgii, proof of (17.17)). -/
lemma measurePreserving_shift_map_cubeView
    (hper : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (j : Fin d → ZMod (2 * N)) :
    MeasurePreserving (shift ((Fin d → Fin 2) → E) j).toFun (μ.map cubeView) (μ.map cubeView) :=
  (hper j).map_of_comp_eq measurable_cubeView measurable_cubeView
    (Transformation.measurable_toFun _) (funext fun ω ↦ (cubeView_shift j ω).symm)

omit [NeZero N] in
/-- The coarse-graining of an `r̂_k`-invariant measure is `r̃_k`-invariant. -/
lemma measurePreserving_genReflectionAt_map_cubeView
    (hrefl : ∀ k, MeasurePreserving (hatReflection E N k).toFun μ μ) (k : Fin d) :
    MeasurePreserving (genReflectionAt N (cubeRefl E) k).toFun (μ.map cubeView)
      (μ.map cubeView) :=
  (hrefl k).map_of_comp_eq measurable_cubeView measurable_cubeView
    (Transformation.measurable_toFun _) (funext fun ω ↦ genReflectionAt_cubeRefl_cubeView k ω)

end Cube

/-- **Georgii, Corollary (17.17): the chessboard estimate for functions of the elementary
cubes.** Let `μ` be a finite measure on `E^Λ`, `Λ = (ℤ/2N)^d` with `d ≥ 1`, which is
`Λ`-periodic and, for every direction `k`, `r̂_k`-positive and `r̂_k`-invariant.  Then for every
family `(f_i)_{i ∈ Λ}` of bounded measurable functions on `E^C`,
`|μ(∏_i f_i ∘ σ_{C(i)})|^{|Λ|} ≤ ∏_j μ(∏_i f_j ∘ r^i ∘ σ_{C(i)})`, where
`r^i = tauPow (cubeRefl E) i` is the iterated cube reflection (17.14). -/
theorem abs_integral_prod_cubeView_pow_le {E : Type*} [MeasurableSpace E] {N d : ℕ} [NeZero N]
    {μ : Measure ((Fin (d + 1) → ZMod (2 * N)) → E)} [IsFiniteMeasure μ]
    (hper : ∀ j, MeasurePreserving (shift E j).toFun μ μ)
    (hrefl : ∀ k, MeasurePreserving (hatReflection E N k).toFun μ μ)
    (hpos : ∀ k, IsReflectionPositive (hatPosAt N k) (hatReflection E N k) μ)
    {f : (Fin (d + 1) → ZMod (2 * N)) → ((Fin (d + 1) → Fin 2) → E) → ℝ}
    (hf : ∀ i, Measurable (f i)) {C : ℝ} (hC : ∀ i ζ, |f i ζ| ≤ C) :
    |∫ ω, ∏ i, f i (cubeView ω i) ∂μ| ^ ((2 * N) ^ (d + 1))
      ≤ ∏ j, ∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i)) ∂μ := by
  have h := abs_integral_prod_pow_le_pi (μ := μ.map cubeView) (τ := cubeRefl E)
    (fun k ζ ↦ cubeRefl_cubeRefl k ζ) (measurePreserving_shift_map_cubeView hper)
    (measurePreserving_genReflectionAt_map_cubeView hrefl)
    (fun k ↦ isReflectionPositive_map_cubeView (hpos k)) hf hC
  have hL : ∫ ω', ∏ i, f i (ω' i) ∂(μ.map cubeView) = ∫ ω, ∏ i, f i (cubeView ω i) ∂μ :=
    integral_map measurable_cubeView.aemeasurable
      (Finset.measurable_prod _ fun i _ ↦ (hf i).comp (measurable_pi_apply i)).aestronglyMeasurable
  have hR : ∀ j, ∫ ω', ∏ i, f j (tauPow (cubeRefl E) i (ω' i)) ∂(μ.map cubeView)
      = ∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i)) ∂μ := fun j ↦
    integral_map measurable_cubeView.aemeasurable (Finset.measurable_prod _ fun i _ ↦
      (hf j).comp ((measurable_tauPow _ _).comp (measurable_pi_apply i))).aestronglyMeasurable
  rw [hL] at h
  simp only [hR] at h
  exact h


/-! ### Reflection positivity of product measures, and of densities

Georgii's "trivial example" of a `Λ`-periodic and reflection positive measure is the product
measure `λ^Λ`; the Fubini argument is `MeasureTheory.integral_mul_comp_nonneg`.  Reflection
positivity is inherited by a density of the form `h · h∘r̂` with `h ∈ 𝒜_+`: this is the whole
content of the proof of Theorem (17.21). -/

section Density

variable {S E : Type*} [MeasurableSpace E]

/-- **Reflection positivity passes to densities of the form `h · h∘τ̃`** with `h` a bounded
nonnegative function of the coordinates in the positive half (Georgii, proof of (17.21)). -/
lemma IsReflectionPositive.withDensity {Λpos : Set S} {τ : Transformation S E}
    {μ : Measure (S → E)} (hpos : IsReflectionPositive Λpos τ μ) {h : (S → E) → ℝ}
    (hh : Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] h) (hh0 : ∀ ω, 0 ≤ h ω) {Ch : ℝ}
    (hhC : ∀ ω, |h ω| ≤ Ch) :
    IsReflectionPositive Λpos τ
      (μ.withDensity fun ω ↦ ENNReal.ofReal (h ω * h (τ.toFun ω))) := by
  intro f hf hfb
  obtain ⟨Cf, hCf⟩ := hfb
  have hhm : Measurable h := hh.mono cylinderEvents_le_pi le_rfl
  have hρ : Measurable fun ω ↦ Real.toNNReal (h ω * h (τ.toFun ω)) :=
    (hhm.mul (hhm.comp τ.measurable_toFun)).real_toNNReal
  have hdens : (fun ω ↦ ENNReal.ofReal (h ω * h (τ.toFun ω)))
      = fun ω ↦ ((Real.toNNReal (h ω * h (τ.toFun ω)) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul hρ]
  have hpt : ∀ ω, Real.toNNReal (h ω * h (τ.toFun ω)) • (f ω * f (τ.toFun ω))
      = (f ω * h ω) * (f (τ.toFun ω) * h (τ.toFun ω)) := by
    intro ω
    rw [NNReal.smul_def, Real.coe_toNNReal _ (mul_nonneg (hh0 _) (hh0 _))]
    ring
  simp only [hpt]
  refine hpos (fun ω ↦ f ω * h ω) (hf.mul hh) ⟨|Cf| * |Ch|, fun ω ↦ ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hCf ω).trans (le_abs_self _)) ((hhC ω).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

/-- Reflection positivity is unchanged by rescaling the measure. -/
lemma IsReflectionPositive.smul {Λpos : Set S} {τ : Transformation S E} {μ : Measure (S → E)}
    (hpos : IsReflectionPositive Λpos τ μ) (c : ℝ≥0∞) : IsReflectionPositive Λpos τ (c • μ) := by
  intro f hf hfb
  rw [integral_smul_measure]
  exact mul_nonneg ENNReal.toReal_nonneg (hpos f hf hfb)

end Density

section ProductMeasure

variable {ι E : Type*} [Fintype ι] [MeasurableSpace E]

/-- A permutation of the sites preserves the product measure `ν^ι` (the finite-volume version of
`Transformation.measurePreserving_infinitePi`). -/
lemma measurePreserving_siteEquiv_pi (e : ι ≃ ι) (ν : Measure E) [SigmaFinite ν] :
    MeasurePreserving (siteEquiv E e).toFun (Measure.pi fun _ : ι ↦ ν)
      (Measure.pi fun _ : ι ↦ ν) := by
  have h := measurePreserving_piCongrLeft (α := fun _ : ι ↦ E) (fun _ : ι ↦ ν) e
  convert h using 1
  funext ω i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [siteEquiv_toFun_apply, Equiv.symm_apply_apply, MeasurableEquiv.piCongrLeft_apply_apply]

end ProductMeasure


/-! ### Georgii §17.2: Gibbs distributions with periodic boundary condition -/

section PeriodicGibbs

variable {E : Type*} [MeasurableSpace E] {N d : ℕ} [NeZero N]

/-- **The product measure `λ^Λ` is `r̂_k`-positive** (Georgii, proof of (17.21)): a bounded
function `f` of the coordinates in `Λ̂_{+,k}` factors as `g(σ_L, σ_Δ)` with `L` the plane of
`r̂_k` and `Δ` the open half, and `λ^Λ(f · f∘r̂_k) = ∫ λ^L(dω) λ^Δ(g(ω, ·))² ≥ 0`. -/
theorem isReflectionPositive_hatReflection_pi (ν : Measure E) [IsFiniteMeasure ν] (k : Fin d) :
    IsReflectionPositive (hatPosAt N k) (hatReflection E N k)
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) := by
  intro f hf hfb
  obtain ⟨C, hC⟩ := hfb
  have hfm : Measurable f := hf.mono cylinderEvents_le_pi le_rfl
  have hdep : DependsOn f (hatPosAt N k) := hf.dependsOn_of_cylinderEvents
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h := integral_mul_comp_nonneg (ν := fun _ : Fin d → ZMod (2 * N) ↦ ν) (hatReflAt N k)
    (fun _ ↦ rfl) (P := hatPosAt N k) ?_ hfm hdep hC
  · simpa only [hatReflection_toFun] using h
  intro i hi
  -- `i` is not on the plane of `r̂_k`: `i_k ∉ {0, N}`
  have hne : -(i k) ≠ i k := fun h ↦ hi (by
    rw [hatReflAt_apply, h, Function.update_eq_self])
  have h0 : i k ≠ 0 := fun h ↦ hne (by rw [h, neg_zero])
  have hneg : (-(i k)).val = 2 * N - (i k).val := by simp [ZMod.neg_val, h0]
  have hlt : (i k).val < 2 * N := ZMod.val_lt _
  have hN' : (i k).val ≠ N := fun h ↦ hne (ZMod.val_injective _ (by rw [hneg, h]; omega))
  simp only [mem_hatPosAt, hatReflAt_apply_self, hneg]
  omega

variable (E) in
/-- **Georgii (17.20), the exponent.** The periodic Hamiltonian `∑_{i ∈ Λ} Φ_{C(i)}` in the torus
`Λ` of the `C`-potential (17.18) with cube interaction `Φ_C = φ`: every elementary cube `C(i)`
contributes `φ` evaluated on the spins in that cube. -/
def periodicHamiltonian (φ : ((Fin d → Fin 2) → E) → ℝ) (ω : (Fin d → ZMod (2 * N)) → E) : ℝ :=
  ∑ i, φ (cubeView ω i)

variable (E) in
/-- **Georgii (17.20).** The Gibbs distribution in the torus `Λ` with periodic boundary
condition for the `C`-potential with cube interaction `φ`, relative to the a priori measure `ν`,
*before normalisation*: the measure `°Z_Λ^Φ · °γ_Λ^Φ` with density `exp(-∑_{i ∈ Λ} Φ_{C(i)})`
with respect to `ν^Λ`.  See `periodicGibbsDist` for `°γ_Λ^Φ` itself. -/
def periodicGibbs (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E) :
    Measure ((Fin d → ZMod (2 * N)) → E) :=
  (Measure.pi fun _ ↦ ν).withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-periodicHamiltonian E φ ω))

variable (E) in
/-- **Georgii's `°γ_Λ^Φ`**: the normalised Gibbs distribution with periodic boundary
condition, `(°Z_Λ^Φ)⁻¹ exp(-∑_i Φ_{C(i)}) λ^Λ`. -/
def periodicGibbsDist (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E) :
    Measure ((Fin d → ZMod (2 * N)) → E) :=
  (periodicGibbs E φ ν (N := N) univ)⁻¹ • periodicGibbs E φ ν (N := N)

variable {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E}

lemma measurable_periodicHamiltonian (hφ : Measurable φ) :
    Measurable (periodicHamiltonian E φ (N := N)) :=
  Finset.measurable_sum _ fun i _ ↦ hφ.comp ((measurable_pi_apply i).comp measurable_cubeView)

lemma measurable_periodicGibbsDensity (hφ : Measurable φ) :
    Measurable fun ω : (Fin d → ZMod (2 * N)) → E ↦
      ENNReal.ofReal (Real.exp (-periodicHamiltonian E φ ω)) :=
  ENNReal.measurable_ofReal.comp (measurable_periodicHamiltonian hφ).neg.exp

/-- The periodic Hamiltonian is shift invariant: a rotation of the torus permutes the elementary
cubes. -/
lemma periodicHamiltonian_shift (j : Fin d → ZMod (2 * N)) (ω : (Fin d → ZMod (2 * N)) → E) :
    periodicHamiltonian E φ ((shift E j).toFun ω) = periodicHamiltonian E φ ω := by
  simp only [periodicHamiltonian, cubeView_shift, shift_toFun_apply]
  exact Equiv.sum_comp (Equiv.subRight j) fun i ↦ φ (cubeView ω i)

/-- The periodic Hamiltonian is `r̂_k`-invariant when `Φ_C` is invariant under the reflection
`r_k` of the cube (condition (iii) of Georgii (17.18)): `r̂_k` permutes the elementary cubes and
reflects each of them. -/
lemma periodicHamiltonian_hatReflection {k : Fin d} (hφk : ∀ ζ, φ (cubeRefl E k ζ) = φ ζ)
    (ω : (Fin d → ZMod (2 * N)) → E) :
    periodicHamiltonian E φ ((hatReflection E N k).toFun ω) = periodicHamiltonian E φ ω := by
  simp only [periodicHamiltonian, cubeView_hatReflection, hφk]
  exact Equiv.sum_comp (torusReflAt N k) fun i ↦ φ (cubeView ω i)

omit [MeasurableSpace E] in
/-- A lower bound `M ≤ Φ_C` bounds the periodic Hamiltonian below by `|Λ| M`. -/
lemma card_smul_le_periodicHamiltonian {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (ω : (Fin d → ZMod (2 * N)) → E) :
    Fintype.card (Fin d → ZMod (2 * N)) • M ≤ periodicHamiltonian E φ ω := by
  rw [← Finset.card_univ]
  exact Finset.card_nsmul_le_sum _ _ _ fun i _ ↦ hM _

/-- Georgii's normalisation constant `°Z_Λ^Φ` is finite when `Φ_C` is bounded below, so that
`°Z · °γ` is a finite measure (Georgii (17.19)(1): condition (iv) of (17.18) makes the
Hamiltonians bounded). -/
lemma isFiniteMeasure_periodicGibbs [IsFiniteMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) :
    IsFiniteMeasure (periodicGibbs E φ ν (N := N)) := by
  refine isFiniteMeasure_withDensity (ne_of_lt ?_)
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-periodicHamiltonian E φ ω))
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (-(Fintype.card (Fin d → ZMod (2 * N)) • M)))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) := by
        refine lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        exact neg_le_neg (card_smul_le_periodicHamiltonian hM ω)
    _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- **Georgii, remark after (17.20): `°γ_Λ^Φ` is `Λ`-periodic.** -/
theorem measurePreserving_shift_periodicGibbs [IsFiniteMeasure ν] (hφ : Measurable φ)
    (j : Fin d → ZMod (2 * N)) :
    MeasurePreserving (shift E j).toFun (periodicGibbs E φ ν) (periodicGibbs E φ ν) :=
  (measurePreserving_siteEquiv_pi (Equiv.addRight j) ν).withDensity_of_comp_eq
    (measurable_periodicGibbsDensity hφ) fun ω ↦ by
      show ENNReal.ofReal (Real.exp (-periodicHamiltonian E φ ((shift E j).toFun ω))) = _
      rw [periodicHamiltonian_shift]

/-- **`°γ_Λ^Φ` is `r̂_k`-invariant** when `Φ_C` is invariant under the cube reflection `r_k`
(condition (iii) of (17.18)).  This is the hypothesis under which the Cauchy–Schwarz inequality
(17.8) is available for `°γ_Λ^Φ`. -/
theorem measurePreserving_hatReflection_periodicGibbs [IsFiniteMeasure ν] (hφ : Measurable φ)
    {k : Fin d} (hφk : ∀ ζ, φ (cubeRefl E k ζ) = φ ζ) :
    MeasurePreserving (hatReflection E N k).toFun (periodicGibbs E φ ν) (periodicGibbs E φ ν) :=
  (measurePreserving_siteEquiv_pi (hatReflAt N k) ν).withDensity_of_comp_eq
    (measurable_periodicGibbsDensity hφ) fun ω ↦ by
      show ENNReal.ofReal (Real.exp (-periodicHamiltonian E φ ((hatReflection E N k).toFun ω)))
        = _
      rw [periodicHamiltonian_hatReflection hφk]

/-- The elementary cubes on the positive side of the plane of `r̂_k`, and the reflected ones. -/
lemma torusReflAt_mem_filter_iff {k : Fin d} {i : Fin d → ZMod (2 * N)} :
    (torusReflAt N k i k).val < N ↔ ¬ (i k).val < N := by
  have := ZMod.val_lt (i k)
  rw [torusReflAt_apply_self, val_neg_one_sub]
  omega

/-- **Georgii, proof of (17.21).** The periodic Hamiltonian splits as `H₊ + H₊ ∘ r̂_k`, where
`H₊ = ∑_{C(i) ⊆ Λ̂_{+,k}} Φ_{C(i)}` is the contribution of the cubes on the positive side of the
plane of `r̂_k`. -/
lemma periodicHamiltonian_eq_add_hatReflection {k : Fin d} (hφk : ∀ ζ, φ (cubeRefl E k ζ) = φ ζ)
    (ω : (Fin d → ZMod (2 * N)) → E) :
    periodicHamiltonian E φ ω
      = (∑ i ∈ Finset.univ.filter (fun i ↦ (i k).val < N), φ (cubeView ω i))
        + ∑ i ∈ Finset.univ.filter (fun i ↦ (i k).val < N),
            φ (cubeView ((hatReflection E N k).toFun ω) i) := by
  classical
  rw [periodicHamiltonian,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ (i k).val < N)]
  congr 1
  simp only [cubeView_hatReflection, hφk]
  refine Finset.sum_nbij' (torusReflAt N k) (torusReflAt N k) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact torusReflAt_mem_filter_iff.2 hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun h ↦ torusReflAt_mem_filter_iff.1 h hi
  · intro i _
    exact torusReflAt_torusReflAt k i
  · intro i _
    exact torusReflAt_torusReflAt k i
  · intro i _
    rw [torusReflAt_torusReflAt]

/-- **Georgii, Theorem (17.21).** For a `C`-potential — a cube interaction `Φ_C = φ` which is
measurable, bounded below (the consequence of condition (iv) of (17.18) that is used) and
invariant under the reflection `r_k` of the cube (condition (iii)) — the Gibbs distribution
`°γ_Λ^Φ` with periodic boundary condition is `r̂_k`-positive.

The density `exp(-∑_i Φ_{C(i)})` is `h · h∘r̂_k` with `h = exp(-∑_{C(i) ⊆ Λ̂_{+,k}} Φ_{C(i)})` a
bounded function of the coordinates in `Λ̂_{+,k}`, and `λ^Λ` is `r̂_k`-positive. -/
theorem isReflectionPositive_hatReflection_periodicGibbs [IsFiniteMeasure ν] (hφ : Measurable φ)
    {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) {k : Fin d} (hφk : ∀ ζ, φ (cubeRefl E k ζ) = φ ζ) :
    IsReflectionPositive (hatPosAt N k) (hatReflection E N k) (periodicGibbs E φ ν) := by
  classical
  set Hpos : ((Fin d → ZMod (2 * N)) → E) → ℝ := fun ω ↦
    ∑ i ∈ Finset.univ.filter (fun i ↦ (i k).val < N), φ (cubeView ω i) with hHpos
  have hHm : Measurable[cylinderEvents (X := fun _ : Fin d → ZMod (2 * N) ↦ E) (hatPosAt N k)]
      Hpos := by
    let : MeasurableSpace ((Fin d → ZMod (2 * N)) → E) :=
      cylinderEvents (X := fun _ : Fin d → ZMod (2 * N) ↦ E) (hatPosAt N k)
    refine Finset.measurable_sum _ fun i hi ↦ ?_
    exact hφ.comp (measurable_cubeView_apply_cylinderEvents (by simpa using hi))
  have hHlow : ∀ ω, (Finset.univ.filter fun i : Fin d → ZMod (2 * N) ↦ (i k).val < N).card • M
      ≤ Hpos ω := fun ω ↦ Finset.card_nsmul_le_sum _ _ _ fun i _ ↦ hM _
  have hdens : (fun ω ↦ ENNReal.ofReal (Real.exp (-periodicHamiltonian E φ ω)))
      = fun ω ↦ ENNReal.ofReal
          (Real.exp (-Hpos ω) * Real.exp (-Hpos ((hatReflection E N k).toFun ω))) := by
    funext ω
    rw [periodicHamiltonian_eq_add_hatReflection hφk, neg_add, Real.exp_add]
  rw [periodicGibbs, hdens]
  refine (isReflectionPositive_hatReflection_pi ν k).withDensity (h := fun ω ↦ Real.exp (-Hpos ω))
    hHm.neg.exp (fun ω ↦ (Real.exp_pos _).le)
    (Ch := Real.exp (-((Finset.univ.filter fun i : Fin d → ZMod (2 * N) ↦ (i k).val < N).card • M)))
    fun ω ↦ ?_
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (neg_le_neg (hHlow ω))

/-! #### The normalised distribution `°γ_Λ^Φ` -/

/-- `°γ_Λ^Φ` is `Λ`-periodic. -/
theorem measurePreserving_shift_periodicGibbsDist [IsFiniteMeasure ν] (hφ : Measurable φ)
    (j : Fin d → ZMod (2 * N)) :
    MeasurePreserving (shift E j).toFun (periodicGibbsDist E φ ν) (periodicGibbsDist E φ ν) := by
  rw [periodicGibbsDist]
  exact (measurePreserving_shift_periodicGibbs hφ j).smul_measure _

/-- `°γ_Λ^Φ` is `r̂_k`-invariant when `Φ_C` is `r_k`-invariant. -/
theorem measurePreserving_hatReflection_periodicGibbsDist [IsFiniteMeasure ν] (hφ : Measurable φ)
    {k : Fin d} (hφk : ∀ ζ, φ (cubeRefl E k ζ) = φ ζ) :
    MeasurePreserving (hatReflection E N k).toFun (periodicGibbsDist E φ ν)
      (periodicGibbsDist E φ ν) := by
  rw [periodicGibbsDist]
  exact (measurePreserving_hatReflection_periodicGibbs hφ hφk).smul_measure _

/-- **Georgii, Theorem (17.21)** for the normalised distribution `°γ_Λ^Φ`. -/
theorem isReflectionPositive_hatReflection_periodicGibbsDist [IsFiniteMeasure ν]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) {k : Fin d}
    (hφk : ∀ ζ, φ (cubeRefl E k ζ) = φ ζ) :
    IsReflectionPositive (hatPosAt N k) (hatReflection E N k) (periodicGibbsDist E φ ν) := by
  rw [periodicGibbsDist]
  exact (isReflectionPositive_hatReflection_periodicGibbs hφ hM hφk).smul _

/-- Georgii's `°Z_Λ^Φ > 0`: the normalised periodic Gibbs distribution is a probability
measure as soon as the a priori measure is finite and nonzero and `Φ_C` is measurable and
bounded below. -/
theorem isProbabilityMeasure_periodicGibbsDist [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) :
    IsProbabilityMeasure (periodicGibbsDist E φ ν (N := N) (d := d)) := by
  have := isFiniteMeasure_periodicGibbs (N := N) (d := d) (ν := ν) hM
  have hpos : 0 < periodicGibbs E φ ν (N := N) (d := d) univ := by
    rw [periodicGibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_pos_iff_support (measurable_periodicGibbsDensity hφ)]
    have hsupp : Function.support (fun ω : (Fin d → ZMod (2 * N)) → E ↦
        ENNReal.ofReal (Real.exp (-periodicHamiltonian E φ ω))) = univ :=
      eq_univ_of_forall fun ω ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    rw [hsupp, Measure.pi_univ]
    exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ ↦
      (Measure.measure_univ_pos.2 hν).ne')
  constructor
  rw [periodicGibbsDist, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' (measure_ne_top _ _)

end PeriodicGibbs


/-! ### The chessboard estimate for `°γ_Λ^Φ`

Combining Georgii's Theorem (17.21) with his Corollary (17.17): the Gibbs distribution with
periodic boundary condition of a `C`-potential is `Λ`-periodic, `r̂_k`-invariant and
`r̂_k`-positive in every direction, so it satisfies the chessboard estimate for functions of the
elementary cubes.  This is the form in which the estimate enters Georgii's Chapters 18 and 19. -/

section ChessboardPeriodicGibbs

variable {E : Type*} [MeasurableSpace E] {N d : ℕ} [NeZero N]
  {φ : ((Fin (d + 1) → Fin 2) → E) → ℝ} {ν : Measure E}

/-- **Georgii, Corollary (17.17) for the Gibbs distribution with periodic boundary condition.**
Let `Φ` be a `C`-potential (17.18) on the torus `Λ = (ℤ/2N)^d` with `d ≥ 1`, that is: `Φ_C = φ`
is measurable, invariant under every reflection `r_k` of the unit cube (condition (iii)) and
bounded below, the last being what condition (iv) provides.  Let `λ = ν` be a finite nonzero a
priori measure.  Then for every family `(f_i)_{i ∈ Λ}` of bounded measurable functions on `E^C`,

`|°γ_Λ^Φ(∏_i f_i ∘ σ_{C(i)})|^{|Λ|} ≤ ∏_j °γ_Λ^Φ(∏_i f_j ∘ r^i ∘ σ_{C(i)})`,

where `r^i` is the iterated cube reflection (17.14). -/
theorem abs_integral_prod_cubeView_pow_le_periodicGibbsDist [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ)
    {f : (Fin (d + 1) → ZMod (2 * N)) → ((Fin (d + 1) → Fin 2) → E) → ℝ}
    (hf : ∀ i, Measurable (f i)) {C : ℝ} (hC : ∀ i ζ, |f i ζ| ≤ C) :
    |∫ ω, ∏ i, f i (cubeView ω i) ∂(periodicGibbsDist E φ ν (N := N))| ^ ((2 * N) ^ (d + 1))
      ≤ ∏ j, ∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i))
          ∂(periodicGibbsDist E φ ν (N := N)) := by
  have := isProbabilityMeasure_periodicGibbsDist (N := N) (d := d + 1) hν hφ hM
  exact abs_integral_prod_cubeView_pow_le (measurePreserving_shift_periodicGibbsDist hφ)
    (fun k ↦ measurePreserving_hatReflection_periodicGibbsDist hφ (hφk k))
    (fun k ↦ isReflectionPositive_hatReflection_periodicGibbsDist hφ hM (hφk k)) hf hC

end ChessboardPeriodicGibbs


/-! ### Georgii §17.2: `r_k`-positivity, Lemma (17.26)

Georgii's `r_k` is the reflection (17.5) of the torus in a plane *between* the sites; the
associated transformation of `E^Λ` is `siteEquiv E (torusReflAt N k)`, that is
`genReflectionAt N τ k` with `τ_k = id`, and `r_k`-positivity of `μ` is
`IsReflectionPositive (torusPosAt N k) (siteEquiv E (torusReflAt N k)) μ`.  Unlike `r̂_k`, `r_k`
has no fixed sites, so a product measure is `r_k`-positive for the simpler reason that the two
halves are independent (`integral_mul_comp_nonneg_of_disjoint`).  Lemma (17.26) upgrades this to
the densities that appear in the Heisenberg models of (17.22). -/

section SiteReflection

variable {E : Type*} [MeasurableSpace E] {N d : ℕ} [NeZero N]

omit [NeZero N] in
@[simp] lemma siteEquiv_torusReflAt_toFun (k : Fin d) (ω : (Fin d → ZMod (2 * N)) → E) :
    (siteEquiv E (torusReflAt N k)).toFun ω = ω ∘ torusReflAt N k := rfl

/-- **Georgii (17.4)–(17.5).** The reflection `r_k` in a plane between the sites has no fixed
sites: every site lies in exactly one of `Λ_{+,k}` and `r_k Λ_{+,k}`. -/
lemma torusPosAt_iff_torusReflAt_notMem (k : Fin d) (i : Fin d → ZMod (2 * N)) :
    i ∈ torusPosAt N k ↔ torusReflAt N k i ∉ torusPosAt N k := by
  have hlt : (i k).val < 2 * N := ZMod.val_lt _
  simp only [mem_torusPosAt, torusReflAt_apply_self, val_neg_one_sub, not_lt]
  omega

/-- **The product measure `λ^Λ` is `r_k`-positive.**  `r_k` exchanges the two halves of the torus
without fixing a site, so under `λ^Λ = λ^{Λ_{+,k}} ⊗ λ^{Λ_{-,k}}` the functions `f` and `f ∘ r_k`
are independent copies of one another and `λ^Λ(f · f∘r_k) = λ^{Λ_{+,k}}(f)^2 ≥ 0`. -/
theorem isReflectionPositive_siteEquiv_pi (ν : Measure E) [IsFiniteMeasure ν] (k : Fin d) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv E (torusReflAt N k))
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) := by
  intro f hf hfb
  obtain ⟨C, hC⟩ := hfb
  exact integral_mul_comp_nonneg_of_disjoint (ν := fun _ : Fin d → ZMod (2 * N) ↦ ν)
    (torusReflAt N k) (fun _ ↦ rfl) (torusPosAt_iff_torusReflAt_notMem k)
    (hf.mono cylinderEvents_le_pi le_rfl) hf.dependsOn_of_cylinderEvents hC

/-- **Georgii, Lemma (17.26).** Let `μ = ρ · λ^Λ` be a finite measure on `E^Λ` whose density
relative to the product measure `λ^Λ` has the form

`ρ = exp[h + h* + ∫ m(dw) h_w h_w*]`,

where `m` is a finite measure on a measurable space `W`, the functions `h` and `h_w` are complex,
measurable (jointly in `w` and `ω`) and depend only on the coordinates in `Λ_{+,k}`, all of them
are dominated by one measurable function `φ` of those coordinates, and `*` is the reflection
`r_k` combined with complex conjugation.  Then `μ` is `r_k`-positive.

The proof is `MeasureTheory.integral_mul_comp_mul_exp_nonneg`: expanding the exponential writes
`μ(f f*)` as a sum of integrals of the form `λ^Λ(g g*)= |λ^{Λ_{+,k}}(g)|² ≥ 0`. -/
theorem isReflectionPositive_siteEquiv_withDensity {W : Type*} [MeasurableSpace W]
    (ν : Measure E) [IsFiniteMeasure ν] (k : Fin d)
    {φ : ((Fin d → ZMod (2 * N)) → E) → ℝ} (hφm : Measurable φ)
    (hφdep : DependsOn φ (torusPosAt N k))
    {h : ((Fin d → ZMod (2 * N)) → E) → ℂ} (hhm : Measurable h)
    (hhdep : DependsOn h (torusPosAt N k)) (hhφ : ∀ ω, ‖h ω‖ ≤ φ ω)
    {m : Measure W} [IsFiniteMeasure m] {hw : W → ((Fin d → ZMod (2 * N)) → E) → ℂ}
    (hwm : Measurable (Function.uncurry hw)) (hwdep : ∀ w, DependsOn (hw w) (torusPosAt N k))
    (hwφ : ∀ w ω, ‖hw w ω‖ ≤ φ ω)
    {ρ : ((Fin d → ZMod (2 * N)) → E) → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ ω, 0 ≤ ρ ω)
    (hρint : Integrable ρ (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν))
    (hρ : ∀ ω, (ρ ω : ℂ) = Complex.exp (h ω + (starRingEnd ℂ) (h (ω ∘ torusReflAt N k))
      + ∫ w, hw w ω * (starRingEnd ℂ) (hw w (ω ∘ torusReflAt N k)) ∂m)) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv E (torusReflAt N k))
      ((Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν).withDensity
        fun ω ↦ ENNReal.ofReal (ρ ω)) := by
  intro f hf hfb
  obtain ⟨C, hC⟩ := hfb
  have hfm : Measurable f := hf.mono cylinderEvents_le_pi le_rfl
  have hdens : (fun ω ↦ ENNReal.ofReal (ρ ω))
      = fun ω ↦ ((Real.toNNReal (ρ ω) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul hρm.real_toNNReal]
  have hpt : ∀ ω, Real.toNNReal (ρ ω) • (f ω * f ((siteEquiv E (torusReflAt N k)).toFun ω))
      = f ω * f (ω ∘ torusReflAt N k) * ρ ω := by
    intro ω
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hρ0 ω), siteEquiv_torusReflAt_toFun]
    ring
  simp only [hpt]
  exact integral_mul_comp_mul_exp_nonneg (ν := fun _ : Fin d → ZMod (2 * N) ↦ ν)
    (torusReflAt N k) (fun _ ↦ rfl) (torusPosAt_iff_torusReflAt_notMem k) hφm hφdep hhm hhdep
    hhφ hwm hwdep hwφ hρm hρint hρ hfm hf.dependsOn_of_cylinderEvents hC

/-- **`r_k`-positivity from a nonnegative crossing interaction**, the mechanism of Georgii's
Example (17.30).  Suppose the `λ^Λ`-density of `μ` is `exp[h + h∘r_k + ∑_a g_a · g_a∘r_k]`, with
`h` and finitely many `g_a` bounded measurable real functions of the coordinates in `Λ_{+,k}`.
Then `μ` is `r_k`-positive.

This is the reflection-positivity input for a ferromagnetic nearest-neighbour model, Georgii's
Example (17.30).  The nearest-neighbour bonds crossing the plane of `r_k` are exactly the pairs
`{i, r_k i}` with `i_k ∈ {0, N - 1}`: a bond `{i, i ± e_k}` joins the two halves only when
`(i_k, j_k)` is `(N - 1, N)` or `(0, 2N - 1)`, and in both cases `j = r_k i`.  So for `J ≥ 0` the
crossing part `∑_i J σ_i · σ_{r_k i}` of the Hamiltonian is `∑_{i, b} g_{i,b} · g_{i,b}∘r_k` with
`g_{i,b} = √J σ_i^b`, while the bonds inside `Λ_{+,k}` and inside `Λ_{-,k}` contribute `h` and
`h∘r_k` because the coupling is `r_k`-symmetric.  Carrying out that decomposition for a given
Hamiltonian is a separate computation and is not done here. -/
theorem isReflectionPositive_siteEquiv_withDensity_sum {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (ν : Measure E) [IsFiniteMeasure ν]
    (k : Fin d) {h : ((Fin d → ZMod (2 * N)) → E) → ℝ} (hhm : Measurable h)
    (hhdep : DependsOn h (torusPosAt N k)) {Ch : ℝ} (hhC : ∀ ω, |h ω| ≤ Ch)
    {g : A → ((Fin d → ZMod (2 * N)) → E) → ℝ} (hgm : ∀ a, Measurable (g a))
    (hgdep : ∀ a, DependsOn (g a) (torusPosAt N k)) (hgC : ∀ a ω, |g a ω| ≤ Ch) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv E (torusReflAt N k))
      ((Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν).withDensity fun ω ↦
        ENNReal.ofReal (Real.exp (h ω + h (ω ∘ torusReflAt N k)
          + ∑ a, g a ω * g a (ω ∘ torusReflAt N k)))) := by
  intro f hf hfb
  obtain ⟨C, hC⟩ := hfb
  set ρ : ((Fin d → ZMod (2 * N)) → E) → ℝ := fun ω ↦ Real.exp (h ω + h (ω ∘ torusReflAt N k)
    + ∑ a, g a ω * g a (ω ∘ torusReflAt N k)) with hρdef
  have hrefl : Measurable fun ω : (Fin d → ZMod (2 * N)) → E ↦ ω ∘ torusReflAt N k :=
    measurable_comp_equiv (torusReflAt N k)
  have hρm : Measurable ρ := Real.continuous_exp.measurable.comp
    (((hhm.add (hhm.comp hrefl)).add (Finset.measurable_sum _ fun a _ ↦
      (hgm a).mul ((hgm a).comp hrefl))))
  have hdens : (fun ω ↦ ENNReal.ofReal (ρ ω))
      = fun ω ↦ ((Real.toNNReal (ρ ω) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul hρm.real_toNNReal]
  have hpt : ∀ ω, Real.toNNReal (ρ ω) • (f ω * f ((siteEquiv E (torusReflAt N k)).toFun ω))
      = f ω * f (ω ∘ torusReflAt N k) * ρ ω := by
    intro ω
    rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_nonneg _), siteEquiv_torusReflAt_toFun]
    ring
  simp only [hpt]
  simp only [hρdef]
  exact integral_mul_comp_mul_exp_sum_nonneg (ν := fun _ : Fin d → ZMod (2 * N) ↦ ν)
    (torusReflAt N k) (fun _ ↦ rfl) (torusPosAt_iff_torusReflAt_notMem k) hhm hhdep hhC
    hgm hgdep hgC (hf.mono cylinderEvents_le_pi le_rfl) hf.dependsOn_of_cylinderEvents hC

end SiteReflection

end MeasureTheory.GibbsMeasure
