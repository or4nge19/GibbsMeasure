/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.PeriodicGibbsLimits
public import GibbsMeasure.Potential.GibbsTransformation

/-!
# Georgii §18.2, (18.20)–(18.23): the group `T_{C,λ}` and Remark (18.22)

Georgii, *Gibbs Measures and Phase Transitions*, §18.2.  The transformations of `E^C` "which
are completely determined by their restriction to `E^C`" are of two kinds:

* (i) **spatial transformations**: the reflections `r_1, …, r_d` of (17.5) and the
  `P`-preserving rotation `r_0` of **(18.20)**, `(r_0 ω)_i = ω_{(i_2, 1 - i_1, i_3, …, i_d)}`;
* (ii) **pure spin transformations** (**(18.21)**): `τ ω = (τ_i ω_i)_{i ∈ C}` for `λ`-preserving
  measurable bijections `τ_i` of `E`.

Each is extended to `Ω = E^{ℤ^d}`: the spatial ones through the same formula on `ℤ^d`, the pure
spin ones `2`-periodically, `τ_j = τ_i` whenever `j ≡ i (mod 2)` coordinatewise.  `T_{C,λ}` is
the group they generate, and `I_{C,λ}(Φ)` the subgroup of its elements which are symmetries of
`Φ`; **Remark (18.22)** (proved in Example (5.20)(3)) says that every `μ ∈ 𝒢₀(Φ)` is
`τ`-invariant for every `τ ∈ I_{C,λ}(Φ)`.

## The transformations

Every element of `T_{C,λ}` is a *cube transformation* `τ = (π, ε; (τ_c)_{c ∈ C})`
(`CubeTransformation`): its spatial part is the **cube isometry** `cubeIso π ε`, the affine
automorphism `i ↦ (ε_k ⊙ i_{π k})_k` of `ℤ^d` — `π` a permutation of the coordinates, `ε_k ⊙ x`
either `x` or `1 - x` — which fixes the centre of the unit cube `C = {0, 1}^d`, and its spins
`τ_c` are indexed by the corners of `C` and extended `2`-periodically
(`CubeTransformation.onLattice`).  The same datum acts on `E^C` through the induced
permutation of the corners (`CubeTransformation.onCube`); this is Georgii's transformation of
`E^C`, the one in which the condition `τ G_m = G_n` of Definition (18.23)(b) and Theorem
(18.25) is stated.  Georgii's generators are `CubeTransformation.refl k` (`r_k`),
`CubeTransformation.planeRot` (`r_0`) and `CubeTransformation.pureSpin t` ((18.21)).

The spatial parts allowed here form the full group of signed coordinate permutations about the
cube centre, which contains Georgii's `⟨r_0, r_1, …, r_d⟩` (in the plane, `d = 2`, the two
coincide).  Everything below holds at this generality — Georgii's Example (5.20)(3) is stated for
the whole of `T_λ^{(m)} ∘ R ∘ Θ`, and in `d > 2` the restriction to `P`-preserving spatial parts
only matters for the plane `P` of (18.5).

## Main results

* `CubeTransformation.tauPow_latticeCubeView_onLattice`, the identity
  `r^{τ_* i} (θ_{-τ_* i} τ ω)_C = τ_C (r^i (θ_{-i} ω)_C)` behind everything: a cube transformation
  permutes the elementary cubes and acts on each through `τ_C` up to the reflections `r^i`.
  Consequently **(18.3) is equivariant**: `V(G, τ ω) = τ_* V(τ_C⁻¹ G, ω)`
  (`CubeTransformation.latticePattern_onLattice`).
* `CubeTransformation.map_onLattice_cubePotential_eq_iff`: for a `C`-potential satisfying
  (17.18)(iii), `τ` is a symmetry of `Φ` in the sense of (5.6) exactly when `Φ_C ∘ τ_C = Φ_C`;
  so `CubeTransformation.IsSymmetry` is Georgii's `I_{C,λ}(Φ)`.
* `measurePreserving_of_mem_GZero` — **Georgii, Example (5.20)(3) for a `C`-potential**: every
  `μ ∈ 𝒢₀(Φ)` is invariant under every `λ`-preserving symmetry of `Φ` which is periodizable
  along the cubes `Λ(N)` (`Potential.IsPeriodizable`).  Georgii's proof: `°γ_{Λ(N)}^Φ × δ_ω` is
  the Gibbs kernel of the periodic modification `Φ̃^{Λ(N)}`, which is invariant under the periodic
  modification `τ_N` of `τ` (`Potential.map_periodize_periodicModification`), and `τ_N = τ` on
  every local event once `Λ(N)` is large.  This needs no summability of `Φ_C`, so it covers the
  second alternative of (17.18)(iv).
* `CubeTransformation.measurePreserving_onLattice_of_mem_GZero` — **Remark (18.22)**: every
  `μ ∈ 𝒢₀(Φ)` is `τ`-invariant for every `τ ∈ I_{C,λ}(Φ)`; and
  `measurePreserving_latticeRefl_of_mem_GZero`, the case of the reflections `r_k` (Georgii's
  remark that `I_{C,λ}(Φ)` contains the iterated reflections, by (17.18)(iii)).
* `IsPStablePartition`, `IsPhiSymmetric` — **Definition (18.23)**, with
  `IsPStablePartition.pairwise_disjoint` (a `P`-stable partition is disjoint) and
  `IsPhiSymmetric.const_mul` (`I_{C,λ}(Φ) ⊆ I_{C,λ}(βΦ)`, so a `Φ`-symmetric family is
  `βΦ`-symmetric); and `tauPow_latticeCubeView_add_single_eq_on_face`, the geometric fact behind
  (18.24): the reflected cube views at two adjacent sites agree on a face of `C`.
* `latticePattern_shift_preimage_tauPow` — **(18.3) under the shift for an arbitrary pattern
  set**, `V(G, θ_a ω) = V(r^a G, ω) + a`, of which
  `MeasureTheory.GibbsMeasure.latticePattern_shift` is the `r`-symmetric case; the iterated
  reflections compose, `r^{i+j} = r^i ∘ r^j` (`tauPow_cubeRefl_latticeToTorus_zero_add`), and
  `r^{e_k} = r_k` (`tauPow_cubeRefl_latticeToTorus_zero_single`); they are involutions, so
  Georgii's `r^a G = G` is the same as `r^a ⁻¹' G = G`
  (`image_tauPow_cubeRefl_latticeToTorus_zero`).  This is the invariance behind
  Georgii's shift group `Θ̃_n = {θ_i : r^i G_n = G_n}` of Theorem (18.25)(ii); it is stated here,
  next to `latticeParity`, rather than next to `latticePattern` in
  `GibbsMeasure/Specification/PeriodicGibbsLimits.lean`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {d : ℕ}

/-! ### Arithmetic in the corner group `C = (ℤ/2)^d` -/

lemma fin_two_add_self (x : Fin 2) : x + x = 0 := by fin_cases x <;> rfl

lemma fin_two_rev_eq_add_one (x : Fin 2) : x.rev = x + 1 := by fin_cases x <;> rfl

lemma fin_two_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

lemma corner_add_self (c : Fin d → Fin 2) : c + c = 0 := by
  funext k; exact fin_two_add_self (c k)

lemma corner_add_add_cancel (p c : Fin d → Fin 2) : p + (c + p) = c := by
  rw [add_comm c p, ← add_assoc, corner_add_self, zero_add]

/-- The reflection `r_k` of the cube is the translation by the `k`-th basis corner. -/
lemma cubeSiteRefl_eq_add_single (k : Fin d) (c : Fin d → Fin 2) :
    cubeSiteRefl k c = c + Pi.single k 1 := by
  funext l
  rw [cubeSiteRefl_apply]
  by_cases hl : l = k
  · subst hl; simp [fin_two_rev_eq_add_one]
  · simp [hl]

/-- The corner permutation `cubeFlip i` is the translation by the parity of `i`. -/
lemma cubeFlip_eq_add_torusParity {N : ℕ} (i : Fin d → ZMod (2 * N)) (c : Fin d → Fin 2) :
    cubeFlip i c = c + torusParity i := by
  funext k
  simp only [cubeFlip_apply, torusParity, Pi.add_apply]
  split_ifs <;> simp [fin_two_rev_eq_add_one]

/-- **Georgii (17.14) as a translation of the corners**: `r^i ζ = ζ(· + parity i)`. -/
lemma tauPow_cubeRefl_eq_add_torusParity {N : ℕ} (i : Fin d → ZMod (2 * N))
    (ζ : (Fin d → Fin 2) → E) :
    tauPow (cubeRefl E) i ζ = fun c ↦ ζ (c + torusParity i) := by
  funext c
  rw [tauPow_cubeRefl_apply, cubeFlip_eq_add_torusParity]

/-! ### The parity of a site of `ℤ^d` -/

/-- The parity of a site of `ℤ^d`, read as a corner of the unit cube: `0` in the directions where
the coordinate is even and `1` where it is odd.  Georgii's congruence `j ≡ i (mod 2)` in the
periodic extension of (18.21) is `latticeParity j = latticeParity i`. -/
def latticeParity (i : Fin d → ℤ) : Fin d → Fin 2 := fun k ↦ if Even (i k) then 0 else 1

lemma latticeParity_apply (i : Fin d → ℤ) (k : Fin d) :
    latticeParity i k = if Even (i k) then 0 else 1 := rfl

lemma latticeParity_add (i j : Fin d → ℤ) :
    latticeParity (i + j) = latticeParity i + latticeParity j := by
  funext k
  simp only [latticeParity_apply, Pi.add_apply, Int.even_add]
  by_cases hi : Even (i k) <;> by_cases hj : Even (j k) <;> simp [hi, hj]

lemma latticeParity_zero : latticeParity (0 : Fin d → ℤ) = 0 := by
  funext k; simp [latticeParity_apply]

lemma latticeParity_neg (i : Fin d → ℤ) : latticeParity (-i) = latticeParity i := by
  funext k; simp [latticeParity_apply]

lemma latticeParity_sub (i j : Fin d → ℤ) :
    latticeParity (i - j) = latticeParity i + latticeParity j := by
  rw [sub_eq_add_neg, latticeParity_add, latticeParity_neg]

@[simp] lemma latticeParity_intCubeCast (c : Fin d → Fin 2) :
    latticeParity (intCubeCast c) = c := by
  funext k
  rcases fin_two_eq_zero_or_one (c k) with h | h
  · simp [latticeParity_apply, intCubeCast, h]
  · simp [latticeParity_apply, intCubeCast, h]

/-- The parity of a site is its reduction modulo `2`, as read by the iterated reflections. -/
lemma torusParity_latticeToTorus_zero (i : Fin d → ℤ) :
    torusParity (latticeToTorus 0 i) = latticeParity i := by
  funext k
  have h : Even (latticeToTorus 0 i k).val ↔ Even (i k) := even_val_intCast ⟨1, rfl⟩ (i k)
  by_cases h1 : Even (i k)
  · have h2 : Even (latticeToTorus 0 i k).val := h.2 h1
    simp only [torusParity, latticeParity_apply, h1, h2, ite_true]
  · have h2 : ¬ Even (latticeToTorus 0 i k).val := fun h' ↦ h1 (h.1 h')
    simp only [torusParity, latticeParity_apply, h1, h2, ite_false]

/-- **Georgii (17.14) on `ℤ^d`**: `r^i ζ = ζ(· + parity i)`. -/
lemma tauPow_cubeRefl_latticeToTorus_zero (i : Fin d → ℤ) (ζ : (Fin d → Fin 2) → E) :
    tauPow (cubeRefl E) (latticeToTorus 0 i) ζ = fun c ↦ ζ (c + latticeParity i) := by
  rw [tauPow_cubeRefl_eq_add_torusParity, torusParity_latticeToTorus_zero]

/-- Congruent sites have the same parity: the periodic extension in (18.21) is well defined. -/
lemma latticeParity_eq_of_forall_even_sub {i j : Fin d → ℤ} (h : ∀ k, Even (i k - j k)) :
    latticeParity i = latticeParity j := by
  funext k
  have := h k
  simp only [latticeParity_apply]
  rw [Int.even_sub] at this
  by_cases hj : Even (j k) <;> simp [hj, this]

/-- **The iterated reflections of (17.14) form a group**: `r^{i + j} = r^i ∘ r^j`. -/
lemma tauPow_cubeRefl_latticeToTorus_zero_add (i j : Fin d → ℤ) (ζ : (Fin d → Fin 2) → E) :
    tauPow (cubeRefl E) (latticeToTorus 0 (i + j)) ζ
      = tauPow (cubeRefl E) (latticeToTorus 0 i)
          (tauPow (cubeRefl E) (latticeToTorus 0 j) ζ) := by
  rw [tauPow_cubeRefl_latticeToTorus_zero, tauPow_cubeRefl_latticeToTorus_zero,
    tauPow_cubeRefl_latticeToTorus_zero, latticeParity_add]
  funext c
  simp only [← add_assoc]

/-- **The iterated reflections of (17.14) are involutions**: `r^a ∘ r^a = id`. -/
lemma tauPow_cubeRefl_latticeToTorus_zero_involutive (a : Fin d → ℤ) :
    Function.Involutive (tauPow (cubeRefl E) (latticeToTorus 0 a)) := by
  intro ζ
  rw [← tauPow_cubeRefl_latticeToTorus_zero_add a a ζ, tauPow_cubeRefl_latticeToTorus_zero,
    latticeParity_add, corner_add_self]
  funext c
  rw [add_zero]

/-- Consequently Georgii's condition `r^a G = G` may equally be read as `r^a ⁻¹' G = G`, which is
the form in which it is used in Theorem (18.25)(ii). -/
lemma image_tauPow_cubeRefl_latticeToTorus_zero (a : Fin d → ℤ)
    (G : Set ((Fin d → Fin 2) → E)) :
    tauPow (cubeRefl E) (latticeToTorus 0 a) '' G
      = tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G :=
  congrFun (Set.image_eq_preimage_of_inverse
    (tauPow_cubeRefl_latticeToTorus_zero_involutive (E := E) a).leftInverse
    (tauPow_cubeRefl_latticeToTorus_zero_involutive (E := E) a).rightInverse) G

/-! ### Georgii (18.3) under the shift -/

/-- **Georgii (18.3) under the shift, for an arbitrary pattern set**:
`V(G, θ_a ω) = V(r^a G, ω) + a`.  The iterated reflection `r^a` of (17.14) enters because (18.3)
reads the cube at `i` through `r^i`, and `r^i = r^a ∘ r^{i - a}`.  Georgii's `latticePattern_shift`
is the case `r^a G = G`, which for an `r`-symmetric `G` holds for every `a`. -/
lemma latticePattern_shift_preimage_tauPow (G : Set ((Fin d → Fin 2) → E)) (a : Fin d → ℤ)
    (ω : (Fin d → ℤ) → E) :
    latticePattern E G ((shift E a).toFun ω)
      = (· + a) '' latticePattern E (tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G) ω := by
  have hview : ∀ i : Fin d → ℤ,
      latticeCubeView ((shift E a).toFun ω) i = latticeCubeView ω (i - a) := fun i ↦ by
    funext c
    rw [latticeCubeView_apply, latticeCubeView_apply, shift_toFun_apply]
    congr 1
    abel
  ext i
  have hsplit : tauPow (cubeRefl E) (latticeToTorus 0 i) (latticeCubeView ω (i - a))
      = tauPow (cubeRefl E) (latticeToTorus 0 a)
        (tauPow (cubeRefl E) (latticeToTorus 0 (i - a)) (latticeCubeView ω (i - a))) := by
    rw [← tauPow_cubeRefl_latticeToTorus_zero_add]
    congr 2
    abel
  rw [mem_latticePattern, hview, hsplit]
  constructor
  · exact fun h ↦ ⟨i - a, h, by abel⟩
  · rintro ⟨j, hj, rfl⟩
    have hja : j + a - a = j := by abel
    rw [hja]
    exact hj

/-- **Georgii (18.3) under the shift when `r^a G = G`** — the invariance behind his shift group
`Θ̃_n = {θ_i : r^i G_n = G_n}` of Theorem (18.25)(ii): `V(G, θ_a ω) = V(G, ω) + a`. -/
lemma latticePattern_shift_of_preimage_tauPow_eq {G : Set ((Fin d → Fin 2) → E)} {a : Fin d → ℤ}
    (hGa : tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G = G) (ω : (Fin d → ℤ) → E) :
    latticePattern E G ((shift E a).toFun ω) = (· + a) '' latticePattern E G ω := by
  rw [latticePattern_shift_preimage_tauPow, hGa]

/-! ### Cube isometries: the signed coordinate permutations about the centre of `C` -/

/-- `signFlip b : ℤ → ℤ` is `x ↦ 1 - x` if `b` and the identity otherwise: the two affine
involutions of `ℤ` preserving `{0, 1}`. -/
def signFlip (b : Bool) (x : ℤ) : ℤ := if b then 1 - x else x

@[simp] lemma signFlip_true (x : ℤ) : signFlip true x = 1 - x := rfl

@[simp] lemma signFlip_false (x : ℤ) : signFlip false x = x := rfl

@[simp] lemma signFlip_signFlip (b : Bool) (x : ℤ) : signFlip b (signFlip b x) = x := by
  cases b <;> simp

/-- `signMul b : ℤ → ℤ` is `x ↦ -x` if `b` and the identity otherwise: the linear part of
`signFlip b`. -/
def signMul (b : Bool) (x : ℤ) : ℤ := if b then -x else x

@[simp] lemma signMul_true (x : ℤ) : signMul true x = -x := rfl

@[simp] lemma signMul_false (x : ℤ) : signMul false x = x := rfl

@[simp] lemma signMul_signMul (b : Bool) (x : ℤ) : signMul b (signMul b x) = x := by
  cases b <;> simp

lemma signMul_add (b : Bool) (x y : ℤ) : signMul b (x + y) = signMul b x + signMul b y := by
  cases b <;> simp only [signMul_true, signMul_false, neg_add]

lemma even_signMul_iff (b : Bool) (x : ℤ) : Even (signMul b x) ↔ Even x := by
  cases b <;> simp

/-- The offset of a sign: `1` if `b`, `0` otherwise, as an element of `Fin 2`. -/
def signOffset (b : Bool) : Fin 2 := if b then 1 else 0

lemma signFlip_eq_signMul_add (b : Bool) (x : ℤ) :
    signFlip b x = signMul b x + ((signOffset b : ℕ) : ℤ) := by
  cases b <;> simp [signOffset]; ring

lemma signMul_intCast_add_signOffset (b : Bool) (v : Fin 2) :
    signMul b ((v : ℕ) : ℤ) + ((signOffset b : ℕ) : ℤ)
      = (((v + signOffset b : Fin 2) : ℕ) : ℤ) := by
  cases b <;> rcases fin_two_eq_zero_or_one v with rfl | rfl <;> simp [signOffset]

/-- The permutation of the corners of `C` induced by a permutation `π` of the coordinates,
`c ↦ c ∘ π`, as an automorphism of the corner group. -/
def cornerPerm (π : Equiv.Perm (Fin d)) : (Fin d → Fin 2) ≃+ (Fin d → Fin 2) where
  toFun c := fun k ↦ c (π k)
  invFun c := fun k ↦ c (π.symm k)
  left_inv c := by funext k; simp
  right_inv c := by funext k; simp
  map_add' _ _ := rfl

@[simp] lemma cornerPerm_apply (π : Equiv.Perm (Fin d)) (c : Fin d → Fin 2) (k : Fin d) :
    cornerPerm π c k = c (π k) := rfl

@[simp] lemma cornerPerm_symm_apply (π : Equiv.Perm (Fin d)) (c : Fin d → Fin 2) (k : Fin d) :
    (cornerPerm π).symm c k = c (π.symm k) := rfl

/-- The linear part of a cube isometry: the signed coordinate permutation
`i ↦ (± i_{π k})_k` of `ℤ^d`. -/
def cubeIsoLin (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) : (Fin d → ℤ) ≃+ (Fin d → ℤ) where
  toFun i := fun k ↦ signMul (ε k) (i (π k))
  invFun j := fun k ↦ signMul (ε (π.symm k)) (j (π.symm k))
  left_inv i := by funext k; simp
  right_inv j := by funext k; simp
  map_add' i j := by funext k; simp [signMul_add]

@[simp] lemma cubeIsoLin_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i : Fin d → ℤ)
    (k : Fin d) : cubeIsoLin π ε i k = signMul (ε k) (i (π k)) := rfl

@[simp] lemma cubeIsoLin_symm_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (j : Fin d → ℤ) (k : Fin d) :
    (cubeIsoLin π ε).symm j k = signMul (ε (π.symm k)) (j (π.symm k)) := rfl

/-- The corners of the cube offset by the signs: `(offset ε)_k = 1` where `ε_k` flips. -/
def cubeIsoOffset (ε : Fin d → Bool) : Fin d → Fin 2 := fun k ↦ signOffset (ε k)

/-- The corner permutation induced by a cube isometry: `c ↦ (ε_k ⊙ c_{π k})_k`, the restriction
of `cubeIso π ε` to the corners `{0, 1}^d`. -/
def cubeIsoCorner (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) :
    (Fin d → Fin 2) ≃ (Fin d → Fin 2) :=
  (cornerPerm π).toEquiv.trans (Equiv.addRight (cubeIsoOffset ε))

lemma cubeIsoCorner_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (c : Fin d → Fin 2) :
    cubeIsoCorner π ε c = cornerPerm π c + cubeIsoOffset ε := rfl

lemma cubeIsoCorner_symm_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (c : Fin d → Fin 2) :
    (cubeIsoCorner π ε).symm c = (cornerPerm π).symm (c - cubeIsoOffset ε) := by
  rw [cubeIsoCorner, Equiv.symm_trans_apply, Equiv.addRight_symm, Equiv.coe_addRight]
  simp only [← sub_eq_add_neg]
  rfl

lemma cubeIsoCorner_symm_add (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (c p : Fin d → Fin 2) :
    (cubeIsoCorner π ε).symm (c + p) = (cubeIsoCorner π ε).symm c + (cornerPerm π).symm p := by
  rw [cubeIsoCorner_symm_apply, cubeIsoCorner_symm_apply, add_sub_right_comm, map_add]

/-- **A cube isometry** of `ℤ^d`: the affine automorphism `i ↦ (ε_k ⊙ i_{π k})_k`, where `π` is a
permutation of the coordinates and `ε_k ⊙ x` is `1 - x` or `x` according to the sign `ε_k`.
These are the isometries of `ℤ^d` fixing the centre `(1/2, …, 1/2)` of the unit cube `C`, and
they form the group in which Georgii's reflections `r_k` of (17.5) and rotation `r_0` of
(18.20) live. -/
def cubeIso (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) : (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun i := fun k ↦ signFlip (ε k) (i (π k))
  invFun j := fun k ↦ signFlip (ε (π.symm k)) (j (π.symm k))
  left_inv i := by funext k; simp
  right_inv j := by funext k; simp

@[simp] lemma cubeIso_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i : Fin d → ℤ)
    (k : Fin d) : cubeIso π ε i k = signFlip (ε k) (i (π k)) := rfl

@[simp] lemma cubeIso_symm_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (j : Fin d → ℤ)
    (k : Fin d) : (cubeIso π ε).symm j k = signFlip (ε (π.symm k)) (j (π.symm k)) := rfl

/-- A cube isometry is its linear part plus the offset corner. -/
lemma cubeIso_eq_cubeIsoLin_add (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i : Fin d → ℤ) :
    cubeIso π ε i = cubeIsoLin π ε i + intCubeCast (cubeIsoOffset ε) := by
  funext k
  simp only [cubeIso_apply, Pi.add_apply, cubeIsoLin_apply, intCubeCast, cubeIsoOffset]
  exact signFlip_eq_signMul_add _ _

/-- The linear part of a cube isometry sends the corners of `C` to the corners shifted by the
offset: `A c = corner(c) - offset`. -/
lemma cubeIsoLin_intCubeCast (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (c : Fin d → Fin 2) :
    cubeIsoLin π ε (intCubeCast c) + intCubeCast (cubeIsoOffset ε)
      = intCubeCast (cubeIsoCorner π ε c) := by
  funext k
  simp only [Pi.add_apply, cubeIsoLin_apply, intCubeCast, cubeIsoCorner_apply, cornerPerm_apply,
    cubeIsoOffset]
  exact signMul_intCast_add_signOffset _ _

/-- **A cube isometry permutes the elementary cubes**: `s(C + i) = C + A i`, the cube based at
`i` going to the cube based at the linear image of `i`, corner by corner through the induced
corner permutation. -/
lemma cubeIso_add_intCubeCast (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i : Fin d → ℤ)
    (c : Fin d → Fin 2) :
    cubeIso π ε (i + intCubeCast c) = cubeIsoLin π ε i + intCubeCast (cubeIsoCorner π ε c) := by
  rw [cubeIso_eq_cubeIsoLin_add, map_add, add_assoc, cubeIsoLin_intCubeCast]

lemma cubeIso_symm_cubeIsoLin_add_intCubeCast (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (i : Fin d → ℤ) (c : Fin d → Fin 2) :
    (cubeIso π ε).symm (cubeIsoLin π ε i + intCubeCast c)
      = i + intCubeCast ((cubeIsoCorner π ε).symm c) := by
  rw [Equiv.symm_apply_eq, cubeIso_add_intCubeCast, Equiv.apply_symm_apply]

/-- The parity of the linear image of a site is the permuted parity. -/
lemma latticeParity_cubeIsoLin (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i : Fin d → ℤ) :
    latticeParity (cubeIsoLin π ε i) = cornerPerm π (latticeParity i) := by
  funext k
  simp only [latticeParity_apply, cubeIsoLin_apply, cornerPerm_apply, even_signMul_iff]

/-- The linear part of a cube isometry preserves the periods `p·ℤ^d`. -/
lemma cubeIsoLin_mem_piPeriods (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) {p : ℤ}
    {g : Fin d → ℤ} (hg : g ∈ Potential.piPeriods fun _ : Fin d ↦ p) :
    cubeIsoLin π ε g ∈ Potential.piPeriods fun _ : Fin d ↦ p := by
  rw [Potential.mem_piPeriods] at hg ⊢
  intro k
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (hg (π k))
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨signMul (ε k) m, ?_⟩
  rw [cubeIsoLin_apply, ← hm]
  cases ε k <;> simp

/-- A cube isometry is affine with linear part `cubeIsoLin`: `s(i + g) = s i + A g`. -/
lemma cubeIso_add (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (i g : Fin d → ℤ) :
    cubeIso π ε (i + g) = cubeIso π ε i + cubeIsoLin π ε g := by
  rw [cubeIso_eq_cubeIsoLin_add, cubeIso_eq_cubeIsoLin_add, map_add]
  abel

lemma cubeIso_symm_add (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (j g : Fin d → ℤ) :
    (cubeIso π ε).symm (j + g) = (cubeIso π ε).symm j + (cubeIsoLin π ε).symm g := by
  apply (cubeIso π ε).injective
  rw [Equiv.apply_symm_apply, cubeIso_add, Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- **Georgii (17.5) on `ℤ^d`**: the reflection `r_k` of the lattice in the hyperplane
`x_k = 1/2`, `(r_k i)_k = 1 - i_k` and `(r_k i)_l = i_l` for `l ≠ k`; the cube isometry with
trivial permutation and a single sign. -/
def latticeReflAt (k : Fin d) : (Fin d → ℤ) ≃ (Fin d → ℤ) :=
  cubeIso (Equiv.refl (Fin d)) fun l ↦ decide (l = k)

lemma latticeReflAt_apply (k : Fin d) (i : Fin d → ℤ) :
    latticeReflAt k i = Function.update i k (1 - i k) := by
  funext l
  rw [latticeReflAt, cubeIso_apply, Equiv.refl_apply]
  by_cases hl : l = k
  · subst hl; simp
  · simp [hl]

@[simp] lemma latticeReflAt_symm (k : Fin d) : (latticeReflAt k).symm = latticeReflAt k := by
  ext i l
  rw [latticeReflAt, cubeIso_symm_apply, cubeIso_apply, Equiv.refl_symm, Equiv.refl_apply]

/-! ### Georgii (18.20)–(18.21): the cube transformations -/

variable (E d) in
/-- **Georgii (18.20)–(18.21).**  An element of the transformation group `T_{C,λ}`: a cube
isometry `cubeIso π ε` of `ℤ^d` (a signed permutation of the coordinates about the centre of
the unit cube — Georgii's reflections `r_k` and rotation `r_0` are `refl k` and `planeRot`)
together with spins `τ_c`, `c ∈ C`, measurable bijections of the state space.

The datum acts on `Ω = E^{ℤ^d}` by `CubeTransformation.onLattice`, with the spins extended
`2`-periodically, and on `E^C` by `CubeTransformation.onCube` through the induced permutation of
the corners; the latter is the transformation of `E^C` that Georgii writes with the same letter.
The spins are `λ`-preserving exactly for the elements of `T_{C,λ}`; this is part of
`CubeTransformation.IsSymmetry`, Georgii's `I_{C,λ}(Φ)`. -/
structure CubeTransformation where
  /-- The permutation of the coordinates. -/
  perm : Equiv.Perm (Fin d)
  /-- The signs: `sign k` flips the `k`-th coordinate, `x ↦ 1 - x`. -/
  sign : Fin d → Bool
  /-- The spin transformations `τ_c`, `c ∈ C`. -/
  spin : (Fin d → Fin 2) → E ≃ᵐ E

namespace CubeTransformation

variable (τ : CubeTransformation E d)

/-- The spatial part `τ_*` of a cube transformation: the cube isometry `cubeIso π ε`. -/
def sites : (Fin d → ℤ) ≃ (Fin d → ℤ) := cubeIso τ.perm τ.sign

/-- The linear part of the spatial part: the map induced on the base points of the elementary
cubes, `τ_*(C + i) = C + τ.lin i`. -/
def lin : (Fin d → ℤ) ≃+ (Fin d → ℤ) := cubeIsoLin τ.perm τ.sign

/-- The permutation of the corners of `C` induced by the spatial part. -/
def corner : (Fin d → Fin 2) ≃ (Fin d → Fin 2) := cubeIsoCorner τ.perm τ.sign

variable (E) in
/-- **The extension to `Ω`** (Georgii, after (18.21)): the transformation
`(τ ω)_j = τ_{parity j} (ω_{τ_*⁻¹ j})` of `E^{ℤ^d}`, with the spins extended `2`-periodically. -/
def onLattice : Transformation (Fin d → ℤ) E where
  sites := τ.sites
  spin j := τ.spin (latticeParity j)

/-- **The transformation of `E^C`** determined by the datum: `(τ ζ)_c = τ_c (ζ_{τ_*⁻¹ c})`,
the corners permuted by the spatial part. -/
def onCube : Transformation (Fin d → Fin 2) E where
  sites := τ.corner
  spin := τ.spin

@[simp] lemma onLattice_sites : (τ.onLattice E).sites = τ.sites := rfl

@[simp] lemma onLattice_spin (j : Fin d → ℤ) :
    (τ.onLattice E).spin j = τ.spin (latticeParity j) := rfl

@[simp] lemma onLattice_toFun_apply (ω : (Fin d → ℤ) → E) (j : Fin d → ℤ) :
    (τ.onLattice E).toFun ω j = τ.spin (latticeParity j) (ω (τ.sites.symm j)) := rfl

@[simp] lemma onCube_toFun_apply (ζ : (Fin d → Fin 2) → E) (c : Fin d → Fin 2) :
    τ.onCube.toFun ζ c = τ.spin c (ζ (τ.corner.symm c)) := rfl

lemma sites_add_intCubeCast (i : Fin d → ℤ) (c : Fin d → Fin 2) :
    τ.sites (i + intCubeCast c) = τ.lin i + intCubeCast (τ.corner c) :=
  cubeIso_add_intCubeCast _ _ i c

lemma sites_symm_lin_add_intCubeCast (i : Fin d → ℤ) (c : Fin d → Fin 2) :
    τ.sites.symm (τ.lin i + intCubeCast c) = i + intCubeCast (τ.corner.symm c) :=
  cubeIso_symm_cubeIsoLin_add_intCubeCast _ _ i c

lemma latticeParity_lin (i : Fin d → ℤ) :
    latticeParity (τ.lin i) = cornerPerm τ.perm (latticeParity i) :=
  latticeParity_cubeIsoLin _ _ i

lemma corner_symm_add (c p : Fin d → Fin 2) :
    τ.corner.symm (c + p) = τ.corner.symm c + (cornerPerm τ.perm).symm p :=
  cubeIsoCorner_symm_add _ _ c p

/-- **A cube transformation permutes the elementary cubes and acts on each through its
spins**: the spins of `τ ω` in the cube `C + τ.lin i` are, corner by corner, the spins of `ω` in
the cube `C + i` transformed by `τ_{parity(τ.lin i) + c}`. -/
theorem latticeCubeView_onLattice (ω : (Fin d → ℤ) → E) (i : Fin d → ℤ) :
    latticeCubeView ((τ.onLattice E).toFun ω) (τ.lin i)
      = fun c ↦ τ.spin (latticeParity (τ.lin i) + c)
          (latticeCubeView ω i (τ.corner.symm c)) := by
  funext c
  rw [latticeCubeView_apply, onLattice_toFun_apply, latticeParity_add, latticeParity_intCubeCast,
    sites_symm_lin_add_intCubeCast, latticeCubeView_apply]

/-- **The identity behind (18.22)–(18.25)**:
`r^{τ_* i} (θ_{-τ_* i} τ ω)_C = τ_C (r^i (θ_{-i} ω)_C)`.
The reflected view of `τ ω` in the cube based at `τ.lin i` is the image under Georgii's `τ` on
`E^C` of the reflected view of `ω` in the cube based at `i`. -/
theorem tauPow_latticeCubeView_onLattice (ω : (Fin d → ℤ) → E) (i : Fin d → ℤ) :
    tauPow (cubeRefl E) (latticeToTorus 0 (τ.lin i))
        (latticeCubeView ((τ.onLattice E).toFun ω) (τ.lin i))
      = τ.onCube.toFun (tauPow (cubeRefl E) (latticeToTorus 0 i) (latticeCubeView ω i)) := by
  rw [tauPow_cubeRefl_latticeToTorus_zero, tauPow_cubeRefl_latticeToTorus_zero,
    latticeCubeView_onLattice]
  funext c
  dsimp only
  rw [onCube_toFun_apply, corner_add_add_cancel, corner_symm_add, latticeParity_lin,
    AddEquiv.symm_apply_apply]

/-- **Georgii (18.3) is equivariant under the cube transformations**:
`V(G, τ ω) = τ.lin '' V(τ_C⁻¹ G, ω)`. -/
theorem latticePattern_onLattice (G : Set ((Fin d → Fin 2) → E)) (ω : (Fin d → ℤ) → E) :
    latticePattern E G ((τ.onLattice E).toFun ω)
      = τ.lin '' latticePattern E (τ.onCube.toFun ⁻¹' G) ω := by
  ext j
  obtain ⟨i, rfl⟩ := τ.lin.surjective j
  rw [τ.lin.injective.mem_set_image, mem_latticePattern, mem_latticePattern,
    tauPow_latticeCubeView_onLattice, Set.mem_preimage]

/-! #### Georgii's generators: the reflections `r_k`, the rotation `r_0`, the pure spins -/

/-- **Georgii's reflection `r_k`** of §18.2 (i), as a cube transformation: the reflection
(17.5) of the cube and of the lattice, with trivial spins. -/
def refl (k : Fin d) : CubeTransformation E d where
  perm := Equiv.refl (Fin d)
  sign l := decide (l = k)
  spin _ := MeasurableEquiv.refl E

variable (E) in
/-- The extension of `r_k` to `Ω` is the site bijection of the lattice reflection:
`(r_k ω)_i = ω_{r_k i}`. -/
lemma refl_onLattice (k : Fin d) : (refl (E := E) k).onLattice E = siteEquiv E (latticeReflAt k) :=
  rfl

@[simp] lemma refl_onLattice_toFun_apply (k : Fin d) (ω : (Fin d → ℤ) → E) (i : Fin d → ℤ) :
    ((refl (E := E) k).onLattice E).toFun ω i = ω (Function.update i k (1 - i k)) := by
  rw [refl_onLattice, siteEquiv_toFun_apply, latticeReflAt_symm, latticeReflAt_apply]

lemma corner_sub_eq_add (c p : Fin d → Fin 2) : c - p = c + p := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (corner_add_self p)]

/-- On `E^C`, `refl k` is Georgii's reflection `r_k` of the cube (17.14). -/
lemma refl_onCube_toFun (k : Fin d) : (refl (E := E) k).onCube.toFun = cubeRefl E k := by
  funext ζ c
  rw [onCube_toFun_apply, cubeRefl_apply, cubeSiteRefl_eq_add_single]
  change ζ ((cubeIsoCorner (Equiv.refl (Fin d)) fun l ↦ decide (l = k)).symm c)
    = ζ (c + Pi.single k 1)
  rw [cubeIsoCorner_symm_apply, corner_sub_eq_add]
  congr 1
  funext l
  rw [cornerPerm_symm_apply, Equiv.refl_symm, Equiv.refl_apply]
  by_cases hl : l = k
  · subst hl; simp [cubeIsoOffset, signOffset]
  · simp [cubeIsoOffset, signOffset, hl]

/-- **Georgii (18.21)**: the pure spin transformation `τ ω = (τ_i ω_i)_{i ∈ C}` of `E^C`, extended
`2`-periodically to `Ω`, `τ_j = τ_i` for `j ≡ i (mod 2)`. -/
def pureSpin (t : (Fin d → Fin 2) → E ≃ᵐ E) : CubeTransformation E d where
  perm := Equiv.refl (Fin d)
  sign _ := false
  spin := t

/-- The trivial cube isometry. -/
lemma cubeIso_refl_false : cubeIso (Equiv.refl (Fin d)) (fun _ ↦ false) = Equiv.refl _ := by
  ext i l
  rw [cubeIso_apply, Equiv.refl_apply, signFlip_false, Equiv.refl_apply]

lemma cubeIsoCorner_refl_false :
    cubeIsoCorner (Equiv.refl (Fin d)) (fun _ ↦ false) = Equiv.refl _ := by
  ext c l
  rw [cubeIsoCorner_apply, Pi.add_apply, cornerPerm_apply, Equiv.refl_apply, Equiv.refl_apply]
  simp [cubeIsoOffset, signOffset]

@[simp] lemma pureSpin_onLattice_toFun_apply (t : (Fin d → Fin 2) → E ≃ᵐ E)
    (ω : (Fin d → ℤ) → E) (j : Fin d → ℤ) :
    ((pureSpin t).onLattice E).toFun ω j = t (latticeParity j) (ω j) := by
  rw [onLattice_toFun_apply]
  change t (latticeParity j) (ω ((cubeIso (Equiv.refl (Fin d)) fun _ ↦ false).symm j)) = _
  rw [cubeIso_refl_false, Equiv.refl_symm, Equiv.refl_apply]

@[simp] lemma pureSpin_onCube_toFun_apply (t : (Fin d → Fin 2) → E ≃ᵐ E)
    (ζ : (Fin d → Fin 2) → E) (c : Fin d → Fin 2) : (pureSpin t).onCube.toFun ζ c = t c (ζ c) := by
  rw [onCube_toFun_apply]
  change t c (ζ ((cubeIsoCorner (Equiv.refl (Fin d)) fun _ ↦ false).symm c)) = _
  rw [cubeIsoCorner_refl_false, Equiv.refl_symm, Equiv.refl_apply]

/-- **Georgii (18.20)**: the `P`-preserving rotation `r_0` of the plane spanned by the first two
coordinates (Georgii's `i_1, i_2`; here `0, 1`), `(r_0 ω)_i = ω_{(i_1, 1 - i_0, i_2, …)}`: the
rotation by a quarter turn about the centre of the unit square. -/
def planeRot : CubeTransformation E (d + 2) where
  perm := Equiv.swap 0 1
  sign k := decide (k = 0)
  spin _ := MeasurableEquiv.refl E

/-- The site map of (18.20): `i ↦ (i_1, 1 - i_0, i_2, …, i_{d+1})`. -/
def planeRotSite (i : Fin (d + 2) → ℤ) : Fin (d + 2) → ℤ :=
  Function.update (Function.update i 0 (i 1)) 1 (1 - i 0)

@[simp] lemma planeRotSite_zero (i : Fin (d + 2) → ℤ) : planeRotSite i 0 = i 1 := by
  simp [planeRotSite]

@[simp] lemma planeRotSite_one (i : Fin (d + 2) → ℤ) : planeRotSite i 1 = 1 - i 0 := by
  simp [planeRotSite]

lemma planeRotSite_of_ne (i : Fin (d + 2) → ℤ) {l : Fin (d + 2)} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    planeRotSite i l = i l := by
  simp [planeRotSite, Function.update_of_ne h0, Function.update_of_ne h1]

/-- **Georgii (18.20)** for the extension to `Ω`: `(r_0 ω)_i = ω_{(i_1, 1 - i_0, i_2, …)}`. -/
@[simp] lemma planeRot_onLattice_toFun_apply (ω : (Fin (d + 2) → ℤ) → E) (i : Fin (d + 2) → ℤ) :
    ((planeRot (E := E)).onLattice E).toFun ω i = ω (planeRotSite i) := by
  rw [onLattice_toFun_apply]
  change ω ((cubeIso (Equiv.swap 0 1) fun k ↦ decide (k = 0)).symm i) = _
  congr 1
  funext l
  rw [cubeIso_symm_apply, Equiv.symm_swap]
  by_cases h0 : l = 0
  · subst h0; simp
  by_cases h1 : l = 1
  · subst h1; simp
  rw [Equiv.swap_apply_of_ne_of_ne h0 h1, planeRotSite_of_ne i h0 h1]
  simp [h0]

/-- **Georgii (18.20)** on `E^C`: `(r_0 ζ)_c = ζ_{(c_1, 1 - c_0, c_2, …)}`. -/
lemma planeRot_onCube_toFun_apply (ζ : (Fin (d + 2) → Fin 2) → E) (c : Fin (d + 2) → Fin 2) :
    (planeRot (E := E)).onCube.toFun ζ c
      = ζ (Function.update (Function.update c 0 (c 1)) 1 (c 0 + 1)) := by
  rw [onCube_toFun_apply]
  change ζ ((cubeIsoCorner (Equiv.swap 0 1) fun k ↦ decide (k = 0)).symm c) = _
  congr 1
  rw [cubeIsoCorner_symm_apply, corner_sub_eq_add]
  funext l
  rw [cornerPerm_symm_apply, Equiv.symm_swap]
  by_cases h0 : l = 0
  · subst h0
    simp [cubeIsoOffset, signOffset]
  by_cases h1 : l = 1
  · subst h1; simp [cubeIsoOffset, signOffset]
  rw [Equiv.swap_apply_of_ne_of_ne h0 h1, Function.update_of_ne h1, Function.update_of_ne h0]
  simp [cubeIsoOffset, signOffset, h0]

/-! #### Periodizability -/

lemma lin_symm_eq : τ.lin.symm = cubeIsoLin τ.perm.symm fun k ↦ τ.sign (τ.perm.symm k) :=
  AddEquiv.ext fun _ ↦ rfl

/-- **A cube transformation is periodizable along every torus of even side** (Georgii (5.20)(3):
the elements of `T_λ^{(2)} ∘ R` are periodizable along the cubes `Λ(N)`): its spatial part is
affine with a linear part preserving the periods, and its spins are `2`-periodic. -/
theorem isPeriodizable_onLattice {p : ℤ} (hp : 2 ∣ p) :
    Potential.IsPeriodizable (Potential.piPeriods fun _ : Fin d ↦ p) (τ.onLattice E) where
  spin_congr i j hij := by
    rw [onLattice_spin, onLattice_spin,
      latticeParity_eq_of_forall_even_sub fun k ↦ ?_]
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (Potential.mem_piPeriods.1 hij k)
    obtain ⟨q, rfl⟩ := hp
    exact ⟨m * q, by rw [Pi.sub_apply] at hm; rw [← hm]; simp only [smul_eq_mul]; ring⟩
  exists_sites_add g hg :=
    ⟨τ.lin g, cubeIsoLin_mem_piPeriods _ _ hg, fun i ↦ cubeIso_add _ _ i g⟩
  exists_symm_add g hg :=
    ⟨τ.lin.symm g, by rw [lin_symm_eq]; exact cubeIsoLin_mem_piPeriods _ _ hg,
      fun i ↦ cubeIso_symm_add _ _ i g⟩

end CubeTransformation

/-! ### Georgii Example (5.20)(3) for a `C`-potential -/

section Symmetry

variable {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]

lemma latticeCube_add (i j : Fin d → ℤ) :
    latticeCube (i + j) = (latticeCube i).map (Equiv.addRight j).toEmbedding := by
  ext x
  simp only [mem_latticeCube_iff, Finset.mem_map_equiv, Equiv.addRight_symm, Equiv.coe_addRight]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by abel⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc i + j + intCubeCast c = i + intCubeCast c + j := by abel
      _ = x + -j + j := by rw [hc]
      _ = x := by abel

/-- **Georgii (17.18)(ii)**: a `C`-potential is shift invariant. -/
theorem isShiftInvariant_cubePotential : (cubePotential E φ).IsShiftInvariant := by
  intro j
  rw [Potential.map_eq_iff]
  intro A η
  have hsites : (shift E j).sites = Equiv.addRight j := rfl
  simp only [cubePotential, hsites]
  rw [Finset.filter_map, Finset.sum_map]
  refine Finset.sum_congr (Finset.filter_congr fun i _ ↦ ?_) fun i _ ↦ ?_
  · change latticeCube (i + j) = A.map (Equiv.addRight j).toEmbedding ↔ latticeCube i = A
    rw [latticeCube_add]
    exact (Finset.map_injective _).eq_iff
  · congr 1
    funext c
    change (shift E j).toFun η (i + j + intCubeCast c) = η (i + intCubeCast c)
    rw [shift_toFun_apply]
    congr 1
    abel

/-- **Georgii (5.20)(3), the finite-volume step for a `C`-potential.**  For a `λ`-preserving
symmetry `τ` of `Φ` which is periodizable along the cube `Λ(N)`, the periodic modification `τ_N`
of `τ` carries Georgii's `°γ_{Λ(N)}^Φ × δ_ω` to `°γ_{Λ(N)}^Φ × δ_{τ_N ω}`: the periodic
modification `Φ̃^{Λ(N)}` is `τ_N`-invariant (`Potential.map_periodize_periodicModification`),
hence so is its Gibbsian specification, and `τ_{N*}` preserves the cube. -/
theorem map_periodicGibbsField_periodize (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
    {τ : Transformation (Fin d → ℤ) E} (hτν : ∀ i, MeasurePreserving (τ.spin i) ν ν) {n : ℕ}
    (hτ : Potential.IsPeriodizable
      (Potential.piPeriods fun _ : Fin d ↦ Potential.intBoxLen n) τ)
    (hτΦ : Potential.map τ (cubePotential E φ) = cubePotential E φ) (ω : (Fin d → ℤ) → E) :
    (periodicGibbsField E φ ν n ω).map
        (Potential.periodize τ (Potential.isTorusReduction_latticeTorus d n) hτ).toFun
      = periodicGibbsField E φ ν n
          ((Potential.periodize τ (Potential.isTorusReduction_latticeTorus d n) hτ).toFun ω) := by
  have hpot := isPotential_wrappedCubePotential (E := E) (φ := φ) (n := n) hφ
  have hinv : Specification.IsInvariant
      (Potential.periodize τ (Potential.isTorusReduction_latticeTorus d n) hτ)
      (wrappedCubeGibbsSpec E φ ν n hφ hM) := by
    unfold wrappedCubeGibbsSpec
    exact Potential.isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible _ 1 _ ν
      (fun i ↦ by rw [Potential.periodize_spin]; exact hτν i) _
      (Potential.map_periodize_periodicModification
        (Potential.isTorusReduction_latticeTorus d n) Potential.isAnchor_lexAnchor
        isShiftInvariant_cubePotential hτ hτΦ)
  have h := Specification.isInvariant_iff.1 hinv (periodicCube d n) ω
  rwa [Potential.map_periodize_sites_box, wrappedCubeGibbsSpec_periodicCube_eq_periodicGibbsField,
    wrappedCubeGibbsSpec_periodicCube_eq_periodicGibbsField] at h

/-- **Georgii, Example (5.20)(3) for a `C`-potential: `𝒢₀(Φ) ⊆ 𝒫_I(Ω, 𝓕)`.**  Every cluster point
of the Gibbs distributions with periodic boundary condition is invariant under every
`λ`-preserving symmetry `τ` of `Φ` which is periodizable along the cubes `Λ(N)`.  Georgii's
proof is Proposition (5.18) with the one-element volume families `{Λ(N)}`: the finite-volume
distributions are carried by `τ_N` to each other (`map_periodicGibbsField_periodize`), do not
see the boundary condition on events of the cube, and `τ_N = τ` on every local event once the
cube is large (`Potential.eventually_preimage_periodize_eq`).  Nothing is assumed about the size
of `Φ_C` beyond the lower bound, so the second alternative of (17.18)(iv) is covered. -/
theorem measurePreserving_of_mem_GZero (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
    {τ : Transformation (Fin d → ℤ) E} (hτν : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hτ : ∀ n : ℕ, Potential.IsPeriodizable
      (Potential.piPeriods fun _ : Fin d ↦ Potential.intBoxLen n) τ)
    (hτΦ : Potential.map τ (cubePotential E φ) = cubePotential E φ)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)} (hμ : μ ∈ GZero E φ ν) :
    MeasurePreserving τ.toFun (μ : Measure ((Fin d → ℤ) → E)) μ := by
  obtain ⟨μs, hμs, hcp⟩ := hμ
  refine ⟨τ.measurable_toFun, ?_⟩
  have hprob : IsProbabilityMeasure ((μ : Measure ((Fin d → ℤ) → E)).map τ.toFun) :=
    inferInstance
  refine separatesOn_localEvents hprob inferInstance fun A hA ↦ ?_
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  rw [Measure.map_apply τ.measurable_toFun hAm]
  refine eq_of_mapClusterPt_of_eventually_eq hcp (τ.preimage_mem_localEvents hA) hA ?_
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  filter_upwards [Potential.tendsto_latticeBox_atTop.eventually (eventually_ge_atTop Λ),
    Potential.eventually_preimage_periodize_eq
      (fun n ↦ Potential.isTorusReduction_latticeTorus d n) τ hτ
      Potential.tendsto_latticeBox_atTop hA] with n hn hpre
  obtain ⟨ω, hω⟩ := hμs n
  have hAcube : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
      ((periodicCube d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))] A :=
    cylinderEvents_mono (by exact_mod_cast hn) _ hΛ
  rw [hω, ← hpre, ← Measure.map_apply
      (Potential.periodize τ (Potential.isTorusReduction_latticeTorus d n) (hτ n)).measurable_toFun
      hAm,
    map_periodicGibbsField_periodize hφ hM hτν (hτ n) hτΦ ω,
    periodicGibbsField_apply_of_cylinderEvents n _ hAcube,
    periodicGibbsField_apply_of_cylinderEvents n ω hAcube]

end Symmetry

/-! ### Georgii's `I_{C,λ}(Φ)` and Remark (18.22) -/

namespace CubeTransformation

variable {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E} (τ : CubeTransformation E d)

/-- The cube based at `i` goes to the cube based at `τ.lin i`: `τ_*(C + i) = C + τ.lin i`. -/
lemma latticeCube_map_sites (i : Fin d → ℤ) :
    (latticeCube i).map τ.sites.toEmbedding = latticeCube (τ.lin i) := by
  ext x
  simp only [Finset.mem_map_equiv, mem_latticeCube_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨τ.corner c, ?_⟩
    rw [← τ.sites_add_intCubeCast, hc, Equiv.apply_symm_apply]
  · rintro ⟨c, rfl⟩
    exact ⟨τ.corner.symm c, by rw [τ.sites_symm_lin_add_intCubeCast]⟩

lemma latticeCube_map_sites_symm (j : Fin d → ℤ) :
    (latticeCube j).map τ.sites.symm.toEmbedding = latticeCube (τ.lin.symm j) := by
  conv_lhs => rw [← τ.lin.apply_symm_apply j, ← τ.latticeCube_map_sites, Finset.map_symm_map]

/-- `Φ_C ∘ r^i = Φ_C` for every iterated reflection, from condition (iii) of (17.18). -/
lemma apply_tauPow_cubeRefl_eq (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ) {N : ℕ}
    (i : Fin d → ZMod (2 * N)) (ζ : (Fin d → Fin 2) → E) :
    φ (tauPow (cubeRefl E) i ζ) = φ ζ := by
  have hs : ∀ k, cubeRefl E k ⁻¹' {ξ | φ ξ = φ ζ} = {ξ | φ ξ = φ ζ} := fun k ↦ by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hφk]
  have := preimage_tauPow_eq_self (cubeRefl E) hs i
  exact (Set.ext_iff.1 this ζ).2 rfl

/-- **The two readings of "`τ` is a symmetry of `Φ`" agree for a `C`-potential satisfying
(17.18)(iii)**: `τ ∈ T_{C,λ}` is a symmetry of the potential `Φ` on `ℤ^d` in the sense of
Georgii (5.6) — `Φ_{τ_* A} ∘ τ = Φ_A` for all `A` — if and only if `Φ_C ∘ τ = Φ_C` on `E^C`. -/
theorem map_onLattice_cubePotential_eq_iff (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ) :
    Potential.map (τ.onLattice E) (cubePotential E φ) = cubePotential E φ ↔
      ∀ ζ, φ (τ.onCube.toFun ζ) = φ ζ := by
  constructor
  · intro h ζ
    have h0 := (Potential.map_eq_iff _ _).1 h (latticeCube 0) fun j ↦ ζ (latticeParity j)
    rw [onLattice_sites, τ.latticeCube_map_sites, map_zero, cubePotential_latticeCube,
      cubePotential_latticeCube] at h0
    have hview : latticeCubeView (fun j ↦ ζ (latticeParity j)) 0 = ζ := by
      funext c
      rw [latticeCubeView_apply, zero_add, latticeParity_intCubeCast]
    have hview' : latticeCubeView ((τ.onLattice E).toFun fun j ↦ ζ (latticeParity j)) 0
        = τ.onCube.toFun ζ := by
      have := τ.latticeCubeView_onLattice (fun j ↦ ζ (latticeParity j)) 0
      rw [map_zero, hview] at this
      rw [this]
      funext c
      rw [onCube_toFun_apply, latticeParity_zero, zero_add]
    rwa [hview, hview'] at h0
  · intro h
    rw [Potential.map_eq_iff]
    intro A η
    by_cases hA : ∃ i, latticeCube i = A
    · obtain ⟨i, rfl⟩ := hA
      rw [onLattice_sites, τ.latticeCube_map_sites, cubePotential_latticeCube,
        cubePotential_latticeCube, ← apply_tauPow_cubeRefl_eq hφk (latticeToTorus 0 (τ.lin i)),
        τ.tauPow_latticeCubeView_onLattice, h, apply_tauPow_cubeRefl_eq hφk]
    · push Not at hA
      rw [cubePotential_eq_zero_of_forall hA, cubePotential_eq_zero_of_forall]
      · rfl
      · intro j hj
        rw [onLattice_sites] at hj
        refine hA (τ.lin.symm j) ?_
        rw [← τ.latticeCube_map_sites_symm, hj, Finset.map_symm_map]

variable (φ ν) in
/-- **Georgii's `I_{C,λ}(Φ)`**: a cube transformation belongs to the symmetry group of the
`C`-potential `Φ` if its spins preserve the a priori measure `λ` (so that it lies in
`T_{C,λ}`) and it is a symmetry of `Φ` in the sense of (5.6), `Φ_{τ_* A} ∘ τ = Φ_A`; by
`map_onLattice_cubePotential_eq_iff` the latter is `Φ_C ∘ τ = Φ_C` on `E^C` under (17.18)(iii). -/
structure IsSymmetry : Prop where
  /-- The spins preserve `λ`: `τ ∈ T_{C,λ}`. -/
  measurePreserving_spin : ∀ c, MeasurePreserving (τ.spin c) ν ν
  /-- `τ` is a symmetry of the potential `Φ` on `ℤ^d`. -/
  map_eq : Potential.map (τ.onLattice E) (cubePotential E φ) = cubePotential E φ

variable {τ}

/-- `τ ∈ I_{C,λ}(Φ)` from `λ`-preserving spins and `Φ_C ∘ τ = Φ_C` on `E^C`, under (17.18)(iii). -/
lemma IsSymmetry.of_apply_onCube (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hν : ∀ c, MeasurePreserving (τ.spin c) ν ν) (h : ∀ ζ, φ (τ.onCube.toFun ζ) = φ ζ) :
    τ.IsSymmetry φ ν :=
  ⟨hν, (τ.map_onLattice_cubePotential_eq_iff hφk).2 h⟩

/-- A symmetry of `Φ` satisfies `Φ_C ∘ τ = Φ_C` on `E^C`. -/
lemma IsSymmetry.apply_onCube (h : τ.IsSymmetry φ ν) (ζ : (Fin d → Fin 2) → E) :
    φ (τ.onCube.toFun ζ) = φ ζ := by
  have h0 := (Potential.map_eq_iff _ _).1 h.map_eq (latticeCube 0) fun j ↦ ζ (latticeParity j)
  rw [onLattice_sites, τ.latticeCube_map_sites, map_zero, cubePotential_latticeCube,
    cubePotential_latticeCube] at h0
  have hview : latticeCubeView (fun j ↦ ζ (latticeParity j)) 0 = ζ := by
    funext c
    rw [latticeCubeView_apply, zero_add, latticeParity_intCubeCast]
  have hview' : latticeCubeView ((τ.onLattice E).toFun fun j ↦ ζ (latticeParity j)) 0
      = τ.onCube.toFun ζ := by
    have := τ.latticeCubeView_onLattice (fun j ↦ ζ (latticeParity j)) 0
    rw [map_zero, hview] at this
    rw [this]
    funext c
    rw [onCube_toFun_apply, latticeParity_zero, zero_add]
  rwa [hview, hview'] at h0

/-- **Georgii, Remark (18.22).**  If `Φ ∈ 𝒞_Θ` and `τ ∈ I_{C,λ}(Φ)` then each `μ ∈ 𝒢₀(Φ)` is
`τ`-invariant.  This is Example (5.20)(3) (`measurePreserving_of_mem_GZero`): a cube
transformation is periodizable along every cube `Λ(N)` (`isPeriodizable_onLattice`). -/
theorem IsSymmetry.measurePreserving_onLattice_of_mem_GZero [IsProbabilityMeasure ν]
    (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) (hτ : τ.IsSymmetry φ ν)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)} (hμ : μ ∈ GZero E φ ν) :
    MeasurePreserving (τ.onLattice E).toFun (μ : Measure ((Fin d → ℤ) → E)) μ :=
  measurePreserving_of_mem_GZero hφ hM (fun _ ↦ hτ.measurePreserving_spin _)
    (fun n ↦ τ.isPeriodizable_onLattice ⟨(n : ℤ) + 1, rfl⟩) hτ.map_eq hμ

/-- **Georgii, Remark (18.22)** in the `E^C` form of Definition (18.23)(b): a cube transformation
with `λ`-preserving spins and `Φ_C ∘ τ = Φ_C` leaves every `μ ∈ 𝒢₀(Φ)` invariant, for a
`C`-potential satisfying (17.18)(iii). -/
theorem measurePreserving_onLattice_of_mem_GZero [IsProbabilityMeasure ν] (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hτν : ∀ c, MeasurePreserving (τ.spin c) ν ν) (hτφ : ∀ ζ, φ (τ.onCube.toFun ζ) = φ ζ)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)} (hμ : μ ∈ GZero E φ ν) :
    MeasurePreserving (τ.onLattice E).toFun (μ : Measure ((Fin d → ℤ) → E)) μ :=
  (IsSymmetry.of_apply_onCube hφk hτν hτφ).measurePreserving_onLattice_of_mem_GZero hφ hM hμ

/-- **Georgii's remark before (18.22)**: by hypothesis (17.18)(iii), the reflections `r_k`
belong to `I_{C,λ}(Φ)`. -/
lemma isSymmetry_refl (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ) (k : Fin d) :
    (refl (E := E) k).IsSymmetry φ ν :=
  IsSymmetry.of_apply_onCube hφk (fun _ ↦ MeasurePreserving.id ν)
    fun ζ ↦ by rw [refl_onCube_toFun, hφk]

end CubeTransformation

/-- **Georgii, Remark (18.22) for the reflections `r_k`** — the invariance used in the second
assertion of Theorem (18.17): every `μ ∈ 𝒢₀(Φ)` is invariant under the lattice reflection
`(r_k ω)_i = ω_{r_k i}`, `r_k i = (i_1, …, 1 - i_k, …, i_d)`, for a `C`-potential satisfying
(17.18)(iii). -/
theorem measurePreserving_latticeRefl_of_mem_GZero {φ : ((Fin d → Fin 2) → E) → ℝ}
    {ν : Measure E} [IsProbabilityMeasure ν] (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ) (k : Fin d)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)} (hμ : μ ∈ GZero E φ ν) :
    MeasurePreserving (siteEquiv E (latticeReflAt k)).toFun (μ : Measure ((Fin d → ℤ) → E)) μ :=
  (CubeTransformation.isSymmetry_refl (ν := ν) hφk k).measurePreserving_onLattice_of_mem_GZero
    hφ hM hμ

/-! ### Georgii, Definition (18.23) -/

section Partition

variable (E) in
/-- **Georgii's projection `σ_F`** onto the face `F = {c ∈ C : c_k = a}` of the unit cube: the
restriction of a cube configuration to the corners of that face. -/
def faceRestrict (k : Fin d) (a : Fin 2) (ζ : (Fin d → Fin 2) → E) :
    {c : Fin d → Fin 2 // c k = a} → E := fun c ↦ ζ c

variable {ι : Type*} (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E)

/-- **Georgii, Definition (18.23)(a).**  A family `(G_n)_{n ∈ ι}` of sets of cube configurations
is a *`P`-stable partition of local ground states* of the `C`-potential `Φ` if

* (i) `G_ε(Φ) ⊆ ⋃_n G_n` for some (hence, by monotonicity of `G_ε(Φ)` in `ε`, all small) `ε > 0`;
* (ii) for each `P`-face `F = {c ∈ C : c_k = a}`, `k ∈ P`, `a ∈ {0, 1}`, the projections
  `σ_F(G_n)` are pairwise disjoint.

Georgii's `P` is the plane of the first two coordinates, (18.5); in the plane `d = 2` it is the
whole lattice and every face of `C` is a `P`-face.  A `P`-stable partition is pairwise disjoint
(`IsPStablePartition.pairwise_disjoint`), so Georgii's "`N` distinct sets" is automatic unless
several of them are empty, a case his Φ-symmetry (b) excludes. -/
structure IsPStablePartition (P : Set (Fin d)) (G : ι → Set ((Fin d → Fin 2) → E)) : Prop where
  /-- Georgii (18.23)(a)(i). -/
  exists_localGroundStates_subset : ∃ ε : ℝ, 0 < ε ∧ localGroundStates φ ν ε ⊆ ⋃ n, G n
  /-- Georgii (18.23)(a)(ii). -/
  pairwise_disjoint_faceRestrict : ∀ k ∈ P, ∀ a : Fin 2,
    Pairwise fun m n ↦ Disjoint (faceRestrict E k a '' G m) (faceRestrict E k a '' G n)

/-- **Georgii, Definition (18.23)(b).**  The family `(G_n)` is *`Φ`-symmetric* if for all `m, n`
there is a `τ ∈ I_{C,λ}(Φ)` with `τ G_m = G_n`, `τ` acting on `E^C`. -/
def IsPhiSymmetric (G : ι → Set ((Fin d → Fin 2) → E)) : Prop :=
  ∀ m n, ∃ τ : CubeTransformation E d, τ.IsSymmetry φ ν ∧ τ.onCube.toFun '' G m = G n

variable {φ ν} {P : Set (Fin d)} {G : ι → Set ((Fin d → Fin 2) → E)}

/-- (18.23)(a)(ii) elementwise: two members of the family containing configurations which agree
on a `P`-face are the same member. -/
lemma IsPStablePartition.eq_of_faceRestrict_eq (h : IsPStablePartition φ ν P G) {k : Fin d}
    (hk : k ∈ P) {a : Fin 2} {m n : ι} {ζ ζ' : (Fin d → Fin 2) → E} (hζ : ζ ∈ G m)
    (hζ' : ζ' ∈ G n) (heq : faceRestrict E k a ζ = faceRestrict E k a ζ') : m = n := by
  by_contra hmn
  exact Set.disjoint_left.1 (h.pairwise_disjoint_faceRestrict k hk a hmn) ⟨ζ, hζ, rfl⟩
    ⟨ζ', hζ', heq.symm⟩

/-- A `P`-stable partition is pairwise disjoint as soon as `P ≠ ∅`. -/
lemma IsPStablePartition.pairwise_disjoint (h : IsPStablePartition φ ν P G) (hP : P.Nonempty) :
    Pairwise fun m n ↦ Disjoint (G m) (G n) := by
  obtain ⟨k, hk⟩ := hP
  intro m n hmn
  refine Set.disjoint_left.2 fun ζ hζm hζn ↦ hmn ?_
  exact h.eq_of_faceRestrict_eq hk (a := 0) hζm hζn rfl

/-- **`I_{C,λ}(Φ) ⊆ I_{C,λ}(βΦ)`**: `Φ`-symmetry of a family, Georgii (18.23)(b), survives a
change of the inverse temperature.  This is what lets Theorem (18.25) use at `βΦ` a partition
which is `Φ`-symmetric. -/
lemma IsPhiSymmetric.const_mul (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (h : IsPhiSymmetric φ ν G) (β : ℝ) : IsPhiSymmetric (fun ζ ↦ β * φ ζ) ν G := by
  intro m n
  obtain ⟨τ, hτ, himg⟩ := h m n
  exact ⟨τ, CubeTransformation.IsSymmetry.of_apply_onCube (fun k ζ ↦ by rw [hφk k ζ])
    hτ.measurePreserving_spin (fun ζ ↦ by rw [hτ.apply_onCube ζ]), himg⟩

end Partition

/-! ### Adjacent cubes share a face: the geometry behind (18.24) -/

@[simp] lemma latticeParity_single (k : Fin d) :
    latticeParity (Pi.single k 1 : Fin d → ℤ) = Pi.single k 1 := by
  funext l
  by_cases hl : l = k
  · subst hl; simp [latticeParity_apply]
  · simp [latticeParity_apply, hl]

/-- **The iterated reflection at a unit vector is the reflection `r_k` of the cube**:
`r^{e_k} = r_k`.  This is Georgii's last sentence of Theorem (18.25)(iii): the shift by `e_k`
acts on the pattern sets exactly as `r_k` does. -/
lemma tauPow_cubeRefl_latticeToTorus_zero_single (k : Fin d) :
    tauPow (cubeRefl E) (latticeToTorus 0 (Pi.single k 1 : Fin d → ℤ)) = ⇑(cubeRefl E k) := by
  funext ζ
  rw [tauPow_cubeRefl_latticeToTorus_zero, latticeParity_single]
  funext c
  rw [cubeRefl_apply, cubeSiteRefl_eq_add_single]

/-- **Adjacent cubes share a face** (Georgii, after (18.23)): for the neighbouring sites `i` and
`i + e_k`, the reflected cube views `r^i (θ_{-i} ω)_C` and `r^{i + e_k} (θ_{-i-e_k} ω)_C` agree on
the face `{c ∈ C : c_k = 1 - parity(i)_k}` of `C`. -/
theorem tauPow_latticeCubeView_add_single_eq_on_face (ω : (Fin d → ℤ) → E) (i : Fin d → ℤ)
    (k : Fin d) {c : Fin d → Fin 2} (hc : c k = latticeParity i k + 1) :
    tauPow (cubeRefl E) (latticeToTorus 0 (i + Pi.single k 1))
        (latticeCubeView ω (i + Pi.single k 1)) c
      = tauPow (cubeRefl E) (latticeToTorus 0 i) (latticeCubeView ω i) c := by
  rw [tauPow_cubeRefl_latticeToTorus_zero, tauPow_cubeRefl_latticeToTorus_zero]
  dsimp only
  rw [latticeCubeView_apply, latticeCubeView_apply, latticeParity_add, latticeParity_single]
  congr 1
  funext l
  simp only [Pi.add_apply, intCubeCast]
  by_cases hl : l = k
  · subst hl
    rw [hc]
    simp only [Pi.single_eq_same]
    rcases fin_two_eq_zero_or_one (latticeParity i l) with h | h <;> rw [h] <;> simp
  · simp [hl]

end MeasureTheory.GibbsMeasure
