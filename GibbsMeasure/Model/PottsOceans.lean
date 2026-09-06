/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.DiscreteSymmetryBreakingExamples

/-!
# Georgii 18.3.4–18.3.5: hard-core lattice gases, and Potts' model

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.5 — Potts' model, "a generalization of
the Ising ferromagnet to an arbitrary finite number of states".

## Georgii 18.3.4, the hard-core lattice gases (18.30) and (18.31): why they are not here

Georgii's hard-core interactions take the value `+∞`, and he says so explicitly: "*Since `Φ`
takes the value `+∞`, `Φ` is not a potential in the strict sense of Definition (2.2) to which we
have limited ourselves so far for simplicity.*"  He then argues that the whole of §18.1–§18.2
nevertheless goes through, at the cost of one *ad hoc* step: because `γ^{βΦ}` is not positive, a
Gibbs measure for `βΦ` need not be quasi-Gibbsian in the sense of his Lemma (18.16), and one has
to see by hand that `ν(B(k, ℓ)) > 0` using `B(k, ℓ) ⊇ {σ_Λ ≡ 0}` and
`γ^{βΦ}_Λ(σ_Λ ≡ 0 | ·) > 0`.

In this development a `C`-potential is the **real-valued** measurable function
`φ : E^C → ℝ` of `GibbsMeasure/Specification/PeriodicGibbsLimits.lean` (`cubePotential`,
`cubeGibbsSpec`); `[-∞, ∞]`-valued cube interactions are outside the type, and Lemma (18.16)
(`GibbsMeasure/Model/LowEnergyOceans.lean`) is proved through the positivity of the Gibbsian
kernel.  Formalising 18.3.4 therefore needs two genuine extensions, neither of which is a
corollary of what is here:

* `cubePotential`/`cubeGibbsSpec` for an `EReal`-valued `Φ_C` with `exp (-∞) = 0`, together with
  `λ`-admissibility of the resulting Hamiltonians; and
* the *ad hoc* replacement of Step 1 of Lemma (18.16) that Georgii describes.

Neither is attempted here, and no statement about the hard-core gas or about the
Widom–Rowlinson model (18.31) is claimed.  With those two extensions in place, the partition
`{G_1, G_2}` of the two local ground states of (18.30) — the two staggered occupations
`(01/10)` and `(10/01)` — is literally `isingAntiG` of `GibbsMeasure/Model/IsingOceans.lean`
transported along `0 ↦ false`, `1 ↦ true`, and the conclusion is the one of Example 18.3.2.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The a priori measure on a finite state space -/

lemma uniformOn_univ_singleton_ne_zero {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Finite E] (x : E) :
    uniformOn (Set.univ : Set E) {x} ≠ 0 := by
  rw [Ne, uniformOn_eq_zero_iff Set.finite_univ]
  simp

/-- The uniform measure of a finite type is invariant under every translation of an additive
group structure on it: it is the counting measure, normalised. -/
lemma measurePreserving_addLeft_uniformOn {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] [AddGroup H] [MeasurableAdd H] (g : H) :
    MeasurePreserving (g + ·) (uniformOn (Set.univ : Set H)) (uniformOn (Set.univ : Set H)) := by
  have hinj : Function.Injective (fun x : H ↦ g + x) := fun a b hab ↦ by simpa using hab
  have hsurj : Function.Surjective (fun x : H ↦ g + x) := fun y ↦ ⟨-g + y, by simp⟩
  refine ⟨measurable_const_add g, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply (measurable_const_add g) hs, uniformOn_univ, uniformOn_univ]
  congr 1
  calc Measure.count ((fun x ↦ g + x) ⁻¹' s)
      = Measure.count ((fun x ↦ g + x) '' ((fun x ↦ g + x) ⁻¹' s)) :=
        (Measure.count_injective_image hinj _).symm
    _ = Measure.count s := by rw [Set.image_preimage_eq s hsurj]

/-! ### Georgii (18.32): Potts' model -/

section Potts

variable {N : ℕ} {φ : ZMod (N + 2) → ℝ}

variable (φ) in
/-- **Georgii (18.32)**: the `C`-potential of Potts' model with `N + 2 ≥ 2` states,
`Φ_C = ∑_{{i,j} ⊆ C, |i-j|=1} φ(|σ_i - σ_j|)`.  Georgii's state space is `{1, …, q}` and his
`φ : {0, …, q-1} → ℝ` satisfies `φ(n) = φ(q - n) > φ(0)` for `n > 0`; the first identity says
exactly that `φ(|x - y|)` depends only on `x - y` in `ℤ/q`, so the state space here is
`ZMod (N + 2)` and the bond interaction is `ψ(x, y) = φ(x - y)` with `φ` even
(`hev` below).  Georgii's classical choice is `φ = -1_{\{0\}}`. -/
abbrev pottsCube (d : ℕ) : ((Fin d → Fin 2) → ZMod (N + 2)) → ℝ :=
  cubeBondSum d fun x y ↦ φ (x - y)

lemma measurable_pottsCube {d : ℕ} : Measurable (pottsCube φ d) :=
  measurable_cubeBondSum (by
    exact Measurable.of_discrete)

/-- **Condition (iii) of Georgii (17.18)** for (18.32). -/
lemma pottsCube_cubeRefl {d : ℕ} (k : Fin d) (ζ : (Fin d → Fin 2) → ZMod (N + 2)) :
    pottsCube φ d (cubeRefl (ZMod (N + 2)) k ζ) = pottsCube φ d ζ :=
  cubeBondSum_cubeRefl _ k ζ

variable (hmin : ∀ n : ZMod (N + 2), n ≠ 0 → φ 0 < φ n)

include hmin

lemma pottsCube_bond_ge (x y : ZMod (N + 2)) : φ 0 ≤ φ (x - y) := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [sub_self]
  · exact (hmin _ (sub_ne_zero.2 hxy)).le

/-- **Georgii's `m_Φ = 4 φ(0)`** for (18.32) in the plane. -/
lemma le_pottsCube (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) : 4 * φ 0 ≤ pottsCube φ 2 ζ := by
  have h := cubeBondSum_ge (d := 2) (ψ := fun x y ↦ φ (x - y)) (m := φ 0) (ζ := ζ)
    fun c c' ↦ pottsCube_bond_ge hmin _ _
  norm_num at h
  rw [pottsCube]
  linarith

lemma pottsCube_eq_iff_forall_adj (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) :
    pottsCube φ 2 ζ = 4 * φ 0 ↔
      ∀ c c', (cubeGraph 2).Adj c c' → φ (ζ c - ζ c') = φ 0 := by
  have key := cubeBondSum_eq_iff_forall_adj (d := 2) (ψ := fun x y ↦ φ (x - y)) (m := φ 0)
    (fun a b ↦ pottsCube_bond_ge hmin a b) ζ
  norm_num at key
  rw [pottsCube]
  convert key using 2
  ring

lemma pottsCube_const (x : ZMod (N + 2)) : pottsCube φ 2 (fun _ ↦ x) = 4 * φ 0 :=
  (pottsCube_eq_iff_forall_adj hmin _).2 fun c c' _ ↦ by rw [sub_self]

/-- **Georgii's local ground states of (18.32) are the `q` constant configurations
`(nn/nn)`**: the bond sum attains its minimum only when every bond does, i.e. when adjacent
corners carry the same spin, and the cube is connected. -/
theorem pottsCube_eq_iff (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) :
    pottsCube φ 2 ζ = 4 * φ 0 ↔ ∃ x, ζ = fun _ ↦ x := by
  rw [pottsCube_eq_iff_forall_adj hmin]
  constructor
  · intro h
    have hf : ∀ c c', (cubeGraph 2).Adj c c' → ζ c = ζ c' := by
      intro c c' hcc'
      by_contra hne
      exact absurd (h c c' hcc') (hmin _ (sub_ne_zero.2 hne)).ne'
    exact ⟨ζ 0, funext fun c ↦ cubeGraph_forall_eq_of_adj hf c⟩
  · rintro ⟨x, rfl⟩ c c' _
    rw [sub_self]

/-! #### Georgii's partition into the `q` constant ground states -/

/-- **Georgii's partition of the local ground states of (18.32)**: the `q = N + 2` constant cube
configurations `(nn/nn)`, `n ∈ E`. -/
def pottsG (n : ZMod (N + 2)) : Set ((Fin 2 → Fin 2) → ZMod (N + 2)) := {fun _ ↦ n}

omit hmin in
lemma measurableSet_pottsG (n : ZMod (N + 2)) : MeasurableSet (pottsG (N := N) n) :=
  measurableSet_singleton _

omit hmin in
lemma isRSymmetric_pottsG (n : ZMod (N + 2)) :
    IsRSymmetric (ZMod (N + 2)) (pottsG (N := N) n) :=
  isRSymmetric_singleton_const _

omit hmin in
theorem pairwise_disjoint_faceRestrict_pottsG (k : Fin 2) (a : Fin 2) :
    Pairwise fun m n ↦ Disjoint (faceRestrict (ZMod (N + 2)) k a '' pottsG (N := N) m)
      (faceRestrict (ZMod (N + 2)) k a '' pottsG (N := N) n) := by
  refine pairwise_disjoint_faceRestrict_singleton
    (ζ := fun n : ZMod (N + 2) ↦ fun _ : Fin 2 → Fin 2 ↦ n) fun m n hmn ↦ ⟨fun _ ↦ a, rfl, hmn⟩

lemma exists_pos_localGroundStates_subset_pottsG :
    ∃ ε > 0, localGroundStates (pottsCube φ 2) (uniformOn (Set.univ : Set (ZMod (N + 2)))) ε
      ⊆ ⋃ n, pottsG (N := N) n := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset (φ := pottsCube φ 2)
    (ν := uniformOn (Set.univ : Set (ZMod (N + 2)))) uniformOn_univ_singleton_ne_zero
    (le_pottsCube hmin) (ζ₀ := fun _ ↦ 0) (pottsCube_const hmin 0)
  refine ⟨ε, hε, fun ζ hζ ↦ ?_⟩
  obtain ⟨x, rfl⟩ := (pottsCube_eq_iff hmin ζ).1 (hsub hζ)
  exact Set.mem_iUnion.2 ⟨x, rfl⟩

theorem isPStablePartition_pottsG :
    IsPStablePartition (pottsCube φ 2) (uniformOn (Set.univ : Set (ZMod (N + 2)))) Set.univ
      (pottsG (N := N)) where
  exists_localGroundStates_subset := exists_pos_localGroundStates_subset_pottsG hmin
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_pottsG k a


/-! #### Georgii's cyclic permutations of the state space -/

omit hmin in
/-- **Georgii's transformations `ω → (π ω_i)_{i ∈ S}` with `π` a cyclic permutation of `E`**: the
pure spin transformation (18.21) given by the translation `x ↦ t + x` of `ZMod q`.  "It is easily
seen that `Φ` is invariant under all transformations of this form." -/
abbrev pottsShift (t : ZMod (N + 2)) : CubeTransformation (ZMod (N + 2)) 2 :=
  CubeTransformation.pureSpin fun _ ↦ MeasurableEquiv.addLeft t

omit hmin in
lemma onCube_pottsShift_apply (t : ZMod (N + 2)) (ζ : (Fin 2 → Fin 2) → ZMod (N + 2))
    (c : Fin 2 → Fin 2) : (pottsShift t).onCube.toFun ζ c = t + ζ c := by
  rw [CubeTransformation.pureSpin_onCube_toFun_apply]
  rfl

omit hmin in
theorem isSymmetry_pottsShift (t : ZMod (N + 2)) :
    (pottsShift t).IsSymmetry (pottsCube φ 2) (uniformOn (Set.univ : Set (ZMod (N + 2)))) :=
  CubeTransformation.IsSymmetry.of_apply_onCube pottsCube_cubeRefl
    (fun _ ↦ measurePreserving_addLeft_uniformOn t)
    fun ζ ↦ cubeBondSum_onCube _ (fun c c' _ x y ↦ by
      change φ ((t + x) - (t + y)) = φ (x - y)
      rw [add_sub_add_left_eq_sub]) ζ

omit hmin in
/-- **Georgii's "these transformations map the local ground states `(nn/nn)` onto each other"**:
the cyclic permutations of `E` act simply transitively on the `q` constant configurations. -/
theorem isPhiSymmetric_pottsG :
    IsPhiSymmetric (pottsCube φ 2) (uniformOn (Set.univ : Set (ZMod (N + 2))))
      (pottsG (N := N)) := by
  intro m n
  refine ⟨pottsShift (n - m), isSymmetry_pottsShift _, ?_⟩
  rw [pottsG, pottsG, Set.image_singleton]
  congr 1
  funext c
  rw [onCube_pottsShift_apply]
  ring

/-! #### Georgii 18.3.5: the conclusion -/

/-- **Georgii 18.3.5, Potts' model (18.32).**  *Theorem (18.25) implies that `ex 𝒢_Θ(βΦ)`
contains `N` distinct random perturbations of the `N` constant ground states when `β` is large
enough.*

The `q = N + 2` local ground states are the constant configurations `(nn/nn)`
(`pottsCube_eq_iff`); the partition into their singletons is stable because two distinct
constants differ at every corner, and it is `Φ`-symmetric because the cyclic permutations of `E`
act transitively on them (`isPhiSymmetric_pottsG`).  Each member is `r`-symmetric, so Georgii's
shift group `Θ̃` is all of `Θ` and the count is for the shift-invariant Gibbs measures. -/
theorem eventually_le_encard_extremePoints_potts :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * pottsCube φ 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * pottsCube φ 2 ζ),
      ((N + 2 : ℕ) : ℕ∞) ≤ ((invariantG
        (cubeGibbsSpec (ZMod (N + 2)) (fun ζ ↦ β * pottsCube φ 2 ζ)
          (uniformOn (Set.univ : Set (ZMod (N + 2)))) hφβ hMβ)
        (shiftGroup (Fin 2 → ℤ) (ZMod (N + 2)))).extremePoints ℝ≥0∞).encard := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset_pottsG hmin
  exact eventually_le_encard_extremePoints (E := ZMod (N + 2)) (φ := pottsCube φ 2)
    (ν := uniformOn (Set.univ : Set (ZMod (N + 2)))) (G := pottsG (N := N))
    measurable_pottsCube (le_pottsCube hmin) pottsCube_cubeRefl
    (isCubeConfining_univ_of_finite _ _) (isPStablePartition_pottsG hmin) isPhiSymmetric_pottsG
    measurableSet_pottsG isRSymmetric_pottsG hε hsub


open Peierls in
/-- **Georgii 18.3.5**, the `q` Gibbs measures themselves: for `β` large enough there are
`q = N + 2` pairwise mutually singular shift-invariant Gibbs measures for `βΦ`, the `n`-th one
carried by the configurations whose `(nn/nn)`-cubes percolate in an ocean, and they are
transported into each other by the cyclic permutations of `E`. -/
theorem eventually_exists_potts_gibbsMeasure_family :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * pottsCube φ 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * pottsCube φ 2 ζ),
      ∃ μ : ZMod (N + 2) → Measure ((Fin 2 → ℤ) → ZMod (N + 2)),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec (ZMod (N + 2))
          (fun ζ ↦ β * pottsCube φ 2 ζ) (uniformOn (Set.univ : Set (ZMod (N + 2))))
          hφβ hMβ) (μ n)) ∧
        (Pairwise fun m n ↦ (μ m).MutuallySingular (μ n)) ∧
        (∀ n, μ n {ω | (latticeOceanPart (ZMod (N + 2)) (pottsG n) ω).Nonempty} = 1) ∧
        (∀ (n : ZMod (N + 2)) (a : Fin 2 → ℤ),
          MeasurePreserving (shift (ZMod (N + 2)) a).toFun (μ n) (μ n)) ∧
        (∀ m n : ZMod (N + 2), (μ m).map
          ((pottsShift (n - m)).onLattice (ZMod (N + 2))).toFun = μ n) := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset_pottsG hmin
  filter_upwards [eventually_exists_gibbsMeasure_family_shift (E := ZMod (N + 2))
    (φ := pottsCube φ 2) (ν := uniformOn (Set.univ : Set (ZMod (N + 2))))
    (G := pottsG (N := N)) measurable_pottsCube (le_pottsCube hmin) pottsCube_cubeRefl
    (isCubeConfining_univ_of_finite _ _) (isPStablePartition_pottsG hmin) isPhiSymmetric_pottsG
    measurableSet_pottsG hε hsub] with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, h4, -, h6, -, h8, -⟩ := hβ hφβ hMβ
  refine ⟨ρ, h1, h2, h3, h4,
    fun n a ↦ h6 n a ((isRSymmetric_pottsG n).preimage_tauPow _), fun m n ↦ ?_⟩
  refine h8 m n _ ((isSymmetry_pottsShift (n - m)).const_mul pottsCube_cubeRefl β) ?_
  rw [pottsG, pottsG, Set.image_singleton]
  congr 1
  funext c
  rw [onCube_pottsShift_apply]
  ring

end Potts

end MeasureTheory.GibbsMeasure

end

end
