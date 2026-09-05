/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.FiniteReference
public import GibbsMeasure.Specification.QuasiGibbsian
public import GibbsMeasure.Potential.Periodic
public import GibbsMeasure.Specification.InvariantFields
public import GibbsMeasure.Specification.PatternPercolation

/-!
# From the torus to `ℤ^d`: Georgii's `𝒢₀(Φ)` and (18.10) in the limit

Georgii's periodic Gibbs distribution `°γ_{Λ(N)}^Φ` of §17.2 lives on the torus `(ℤ/2N)^d`.
Georgii's Example (5.20)(3) reads it as a random field on `Ω = (ℤ^d → E)`:
`°γ_{Λ(N)}^Φ × δ_{ω_N}` is the law of the configuration that agrees with the periodic
continuation of the torus configuration inside the cube `Λ(N)` and with a fixed `ω_N` outside,
and `𝒢₀(Φ)` is the set of cluster points, in the topology of local convergence, of any sequence
of these.

## Main results

* `latticeToTorus` — the reduction `ℤ^d → (ℤ/2N)^d`, `N = n + 1`, identifying Georgii's cube
  `Λ(N)` — here `Potential.latticeBox d n = [-N, N)^d`, a translate of his `]-N, N]^d` of (17.1)
  and the same fundamental domain of `2N ℤ^d` — with the torus
  (`latticeToTorus_injOn_latticeBox`, `image_latticeToTorus_latticeBox`).
* `latticePattern` — **Georgii (18.3)** on `ℤ^d`, with `latticePattern_periodicPullback` its
  compatibility with `torusPattern` and
  `measurableSet_cylinderEvents_forall_notMem_latticePattern` the locality of Georgii's event
  `{D ∩ V(G, ·) = ∅}`.
* `cubePotential` — **Georgii's `C`-potential (17.18)** on `ℤ^d` determined by `Φ_C = φ`, with
  `isSigmaFiniteLambdaAdmissible_cubePotential` (Georgii (17.19)(1): condition (iv) makes it
  `λ`-admissible) and `cubeGibbsSpec` its Gibbsian specification, quasilocal by
  `isQuasilocal_cubeGibbsSpec`.
* `wrappedCubePotential` — an **abbreviation of `Potential.periodicModification`**, Georgii's
  Example (4.20)(2), at the torus reduction `Potential.latticeTorus` of the cube and the
  lexicographic anchor; `wrappedCubePotential_apply` is its explicit form for a `C`-potential
  and `interactingHamiltonian_wrappedCubePotential` identifies its Hamiltonian in `Λ(N)` with
  Georgii's periodic Hamiltonian of (17.20).
* `wrappedCubeGibbsSpec_periodicCube_eq_periodicGibbsField` — **the bridge**:
  `γ^{Φ̃^{Λ(N)}}_{Λ(N)}(·|ω) = °γ_{Λ(N)}^Φ × δ_ω`.
* `GZero` — **Georgii's `𝒢₀(Φ)`**; `mem_GP_of_mem_GZero` is `𝒢₀(Φ) ⊆ 𝒢(Φ)` and
  `measurePreserving_shift_of_mem_GZero` is `𝒢₀(Φ) ⊆ 𝒫_Θ(Ω, 𝓕)`, i.e. together
  **Example (5.20)(3)**, `𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)`.
* `forall_notMem_latticePattern_le_patternWeight` — **Georgii, Lemma (18.10)** for
  `μ ∈ 𝒢₀(Φ)`, and `periodicGibbsField_forall_notMem_latticePattern_le_patternWeight` the
  finite-volume statement his proof establishes.
* `isQuasiGibbsian_of_mem_GZero` — every element of `𝒢₀(Φ)` is **quasi-Gibbsian** in the sense
  of Georgii's definition preceding (18.16); the general statement, that every Gibbs measure of
  a `λ`-specification with positive densities is quasi-Gibbsian, is
  `MeasureTheory.GibbsMeasure.isQuasiGibbsian_of_isGibbsMeasure_lambdaSpecification` in
  `GibbsMeasure.Specification.QuasiGibbsian`.
* `IsCubeConfining` — **condition (iv) of Georgii (17.18)** in the form his proof of (18.12)
  uses, with `isCubeConfining_univ` its first alternative `‖Φ_C‖ < ∞`;
  `tendsto_patternWeight_cubePi` is `t(K_ℓ^C, Φ) → 0`, and `GZero_nonempty` is **Georgii,
  Proposition (18.12)**: `𝒢₀(Φ) ≠ ∅` over a standard Borel state space.

## What is *not* here

The percolation half of §18.1 — the combination of (18.10) with Lemma (18.14), Georgii's
Lemma (18.16), Theorem (18.17), Corollary (18.18) and Example (18.19) — is in
`GibbsMeasure.Model.LowEnergyOceans`, which also records exactly which of them are proved.

## Why `𝒢₀(Φ) ⊆ 𝒢(Φ)` is proved here and not quoted

`Potential.mem_GP_of_mapClusterPt_latticePeriodic` is Example (4.20)(2) over the same cubes and
the same periodic modification, but it is stated for an *absolutely summable* potential, and its
proof runs through `Potential.abs_hamiltonian_periodicModification_sub_le`, which needs
`Φ.normAt i < ∞`.  For a `C`-potential that is Georgii's condition (17.18)(iv) in its *first*
alternative, `‖Φ_C‖ < ∞`, only.  The second alternative of (iv) — the one Georgii needs for
(18.12) and for the Heisenberg model (18.19) — allows `‖Φ_C‖ = ∞`.  A `C`-potential always has
*finite range*, so its Hamiltonians are finite sums and its periodic modification is *equal* to
it, not merely close to it, on every set meeting a fixed volume
(`wrappedCubePotential_eq_cubePotential`); `mem_GP_of_mem_GZero` uses that, and therefore needs
no summability at all.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {d n : ℕ}

/-! ### The reduction `ℤ^d → (ℤ/2N)^d` -/

variable (n) in
/-- **Georgii (17.1)–(17.2).** The reduction of the lattice modulo the group `2N ℤ^d` of
periods, `N = n + 1`, onto the torus `(ℤ/2N)^d`. -/
def latticeToTorus (i : Fin d → ℤ) : Fin d → ZMod (2 * (n + 1)) :=
  fun k ↦ ((i k : ℤ) : ZMod (2 * (n + 1)))

@[simp] lemma latticeToTorus_apply (i : Fin d → ℤ) (k : Fin d) :
    latticeToTorus n i k = ((i k : ℤ) : ZMod (2 * (n + 1))) := rfl

lemma latticeToTorus_add (i j : Fin d → ℤ) :
    latticeToTorus n (i + j) = latticeToTorus n i + latticeToTorus n j := by
  funext k; simp

/-- Two sites have the same reduction exactly when they differ by a period. -/
lemma latticeToTorus_eq_iff (i j : Fin d → ℤ) :
    latticeToTorus n i = latticeToTorus n j ↔
      i - j ∈ Potential.piPeriods fun _ : Fin d ↦ Potential.intBoxLen n := by
  rw [funext_iff, Potential.mem_piPeriods]
  refine forall_congr' fun k ↦ ?_
  rw [latticeToTorus_apply, latticeToTorus_apply, ZMod.intCast_eq_intCast_iff,
    Int.modEq_iff_dvd, AddSubgroup.mem_zmultiples_iff]
  simp only [Potential.intBoxLen, zsmul_eq_mul, Pi.sub_apply]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨-c, ?_⟩
    push_cast at hc ⊢
    linear_combination hc
  · rintro ⟨c, hc⟩
    refine ⟨-c, ?_⟩
    push_cast at hc ⊢
    linear_combination hc

/-- The reduction is unchanged by passing to the representative in the cube. -/
@[simp] lemma latticeToTorus_latticeTorus (i : Fin d → ℤ) :
    latticeToTorus n (Potential.latticeTorus d n i) = latticeToTorus n i :=
  (latticeToTorus_eq_iff _ _).2 ((Potential.isTorusReduction_latticeTorus d n).sub_mem' i)

/-- **The cube is a fundamental domain**: the reduction is injective on `Λ(N)`. -/
lemma latticeToTorus_injOn_latticeBox :
    Set.InjOn (latticeToTorus (d := d) n) (Potential.latticeBox d n) := by
  intro i hi j hj hij
  have h := (Potential.isTorusReduction_latticeTorus d n).eq_of_mem_of_sub_mem
    (i := i) (j := j) hj ((latticeToTorus_eq_iff i j).1 hij)
  rwa [(Potential.isTorusReduction_latticeTorus d n).eq_self i hi] at h


/-- A representative in the cube `Λ(N)` of a site of the torus. -/
def torusToLattice (n : ℕ) (j : Fin d → ZMod (2 * (n + 1))) : Fin d → ℤ :=
  Potential.latticeTorus d n fun k ↦ (((j k).val : ℕ) : ℤ)

lemma torusToLattice_mem (j : Fin d → ZMod (2 * (n + 1))) :
    torusToLattice n j ∈ Potential.latticeBox d n :=
  (Potential.isTorusReduction_latticeTorus d n).mapsTo _

@[simp] lemma latticeToTorus_torusToLattice (j : Fin d → ZMod (2 * (n + 1))) :
    latticeToTorus n (torusToLattice n j) = j := by
  rw [torusToLattice, latticeToTorus_latticeTorus]
  funext k
  rw [latticeToTorus_apply]
  push_cast [ZMod.natCast_val, ZMod.cast_id]
  rfl

/-- **The cube `Λ(N)` is a fundamental domain**: the reduction is a bijection from `Λ(N)` onto
the torus. -/
lemma image_latticeToTorus_latticeBox :
    (Potential.latticeBox d n).image (latticeToTorus n) = Finset.univ := by
  classical
  refine Finset.eq_univ_iff_forall.2 fun j ↦ Finset.mem_image.2
    ⟨torusToLattice n j, torusToLattice_mem j, latticeToTorus_torusToLattice j⟩

/-- Summing over the cube is summing over the torus. -/
lemma sum_latticeBox_comp_latticeToTorus {A : Type*} [AddCommMonoid A]
    (f : (Fin d → ZMod (2 * (n + 1))) → A) :
    ∑ i ∈ Potential.latticeBox d n, f (latticeToTorus n i) = ∑ j, f j := by
  classical
  rw [← image_latticeToTorus_latticeBox (d := d) (n := n),
    Finset.sum_image fun x hx y hy h ↦
      latticeToTorus_injOn_latticeBox (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) h]

/-! ### The parity of a reduced site

Georgii's iterated reflection `r^i` of (17.14) depends on `i` only through the parities of its
coordinates, so it is the same whether `i` is read in `ℤ^d`, in `(ℤ/2N)^d`, or in `(ℤ/2)^d`.
-/

lemma even_val_intCast {m : ℕ} [NeZero m] (hm : 2 ∣ m) (a : ℤ) :
    Even ((a : ZMod m)).val ↔ Even a := by
  have hval : (((a : ZMod m).val : ℤ) : ZMod m) = ((a : ℤ) : ZMod m) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rfl
  have hmod : ((a : ZMod m).val : ℤ) ≡ a [ZMOD (m : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).1 hval
  have hdvd : (2 : ℤ) ∣ (a - ((a : ZMod m).val : ℤ)) :=
    dvd_trans (by exact_mod_cast Int.natCast_dvd_natCast.2 hm) (Int.ModEq.dvd hmod)
  rw [← Int.even_coe_nat]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨e, he⟩ := hdvd
    exact ⟨c + e, by omega⟩
  · rintro ⟨c, hc⟩
    obtain ⟨e, he⟩ := hdvd
    exact ⟨c - e, by omega⟩

lemma spinIterate_intCast {X : Type*} [MeasurableSpace X] (τ : X ≃ᵐ X) (a : ℤ) (x : X) :
    spinIterate (N := n + 1) τ ((a : ZMod (2 * (n + 1)))) x
      = spinIterate (N := 1) τ ((a : ZMod (2 * 1))) x := by
  have h1 : Even ((a : ZMod (2 * (n + 1)))).val ↔ Even a :=
    even_val_intCast ⟨n + 1, rfl⟩ a
  have h2 : Even ((a : ZMod (2 * 1))).val ↔ Even a := even_val_intCast ⟨1, rfl⟩ a
  unfold spinIterate
  simp only [h1, h2]

/-- **Georgii (17.14) does not see the volume.** The iterated reflection `r^i` attached to a
site `i ∈ ℤ^d` is the same whether `i` is reduced modulo `2N` or modulo `2`. -/
lemma tauPow_latticeToTorus {X : Type*} [MeasurableSpace X] :
    ∀ {d : ℕ} (τ : Fin d → X ≃ᵐ X) (i : Fin d → ℤ) (x : X),
      tauPow τ (latticeToTorus n i) x = tauPow τ (latticeToTorus 0 i) x
  | 0, τ, i, x => by rw [tauPow_zero, tauPow_zero]
  | m + 1, τ, i, x => by
    rw [tauPow_succ, tauPow_succ]
    have htail : ∀ p : ℕ, Fin.tail (latticeToTorus (d := m + 1) p i) = latticeToTorus p
        (Fin.tail i) := fun p ↦ rfl
    rw [htail, htail, latticeToTorus_apply, latticeToTorus_apply, spinIterate_intCast]
    exact tauPow_latticeToTorus _ _ _

/-! ### The periodic pullback of a torus configuration -/

lemma latticeToTorus_sub (i j : Fin d → ℤ) :
    latticeToTorus n (i - j) = latticeToTorus n i - latticeToTorus n j := by
  funext k; simp

variable (n) in
/-- The `2N`-periodic configuration on `ℤ^d` determined by a configuration on the torus
`(ℤ/2N)^d`: Georgii's periodic continuation, read through `latticeToTorus`. -/
def periodicPullback (ζ : (Fin d → ZMod (2 * (n + 1))) → E) : (Fin d → ℤ) → E :=
  fun i ↦ ζ (latticeToTorus n i)

omit [MeasurableSpace E] in
@[simp] lemma periodicPullback_apply (ζ : (Fin d → ZMod (2 * (n + 1))) → E) (i : Fin d → ℤ) :
    periodicPullback n ζ i = ζ (latticeToTorus n i) := rfl

lemma measurable_periodicPullback : Measurable (periodicPullback (E := E) (d := d) n) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

/-- **The periodic pullback intertwines the shifts** of the torus and of the lattice. -/
lemma periodicPullback_shift (a : Fin d → ℤ) (ζ : (Fin d → ZMod (2 * (n + 1))) → E) :
    periodicPullback n ((shift E (latticeToTorus n a)).toFun ζ)
      = (shift E a).toFun (periodicPullback n ζ) := by
  funext i
  simp [latticeToTorus_sub]

/-! ### Georgii (18.3) on `ℤ^d` -/

/-- The corners of the unit cube `C = {0, 1}^d`, as sites of `ℤ^d`. -/
def intCubeCast (c : Fin d → Fin 2) : Fin d → ℤ := fun k ↦ ((c k : ℕ) : ℤ)

@[simp] lemma latticeToTorus_intCubeCast (c : Fin d → Fin 2) :
    latticeToTorus n (intCubeCast c) = cubeCast (n + 1) c := by
  funext k; simp [intCubeCast, cubeCast]

/-- The spins of `ω` in the elementary cube `C + i` of `ℤ^d`, read as a configuration on
`C = {0, 1}^d`: Georgii's `(θ_{-i} ω)_C`. -/
def latticeCubeView (ω : (Fin d → ℤ) → E) (i : Fin d → ℤ) : (Fin d → Fin 2) → E :=
  fun c ↦ ω (i + intCubeCast c)

omit [MeasurableSpace E] in
@[simp] lemma latticeCubeView_apply (ω : (Fin d → ℤ) → E) (i : Fin d → ℤ)
    (c : Fin d → Fin 2) : latticeCubeView ω i c = ω (i + intCubeCast c) := rfl

lemma measurable_latticeCubeView :
    Measurable (latticeCubeView (E := E) (d := d)) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

variable (E) in
/-- **Georgii (18.3).** `V(G, ω) = {i ∈ ℤ^d : (θ_{-i}ω)_C ∈ r^i G}`, the set of elementary
cubes on which `ω` shows the pattern `G`, read through the iterated reflection `r^i` of
(17.14).  By `tauPow_latticeToTorus` the reflection depends on `i` only through the parities
of its coordinates, which is why the definition can — and does — use the reduction modulo
`2`. -/
def latticePattern (G : Set ((Fin d → Fin 2) → E)) (ω : (Fin d → ℤ) → E) : Set (Fin d → ℤ) :=
  {i | tauPow (cubeRefl E) (latticeToTorus 0 i) (latticeCubeView ω i) ∈ G}

variable {G : Set ((Fin d → Fin 2) → E)}

lemma mem_latticePattern {ω : (Fin d → ℤ) → E} {i : Fin d → ℤ} :
    i ∈ latticePattern E G ω ↔
      tauPow (cubeRefl E) (latticeToTorus 0 i) (latticeCubeView ω i) ∈ G := Iff.rfl

/-- For an `r`-symmetric pattern the reflections drop out of (18.3). -/
lemma mem_latticePattern_of_isRSymmetric (hG : IsRSymmetric E G) (ω : (Fin d → ℤ) → E)
    (i : Fin d → ℤ) : i ∈ latticePattern E G ω ↔ latticeCubeView ω i ∈ G :=
  Set.ext_iff.1 (hG.preimage_tauPow _) (latticeCubeView ω i)

/-- (18.3) reads only the spins in the cube `C + i`. -/
lemma mem_latticePattern_congr {ω ω' : (Fin d → ℤ) → E} {i : Fin d → ℤ}
    (h : ∀ c, ω (i + intCubeCast c) = ω' (i + intCubeCast c)) :
    i ∈ latticePattern E G ω ↔ i ∈ latticePattern E G ω' := by
  have : latticeCubeView ω i = latticeCubeView ω' i := funext h
  rw [mem_latticePattern, mem_latticePattern, this]

/-- **Georgii (18.3) is shift equivariant**: `V(G, θ_a ω) = V(G, ω) + a` for an `r`-symmetric
pattern.  (For a general `G` the iterated reflections `r^i` see the parity of `a`, so the
identity holds only for even `a`; in §18.1 `G` is always `r`-symmetric.) -/
lemma latticePattern_shift (hGsym : IsRSymmetric E G) (a : Fin d → ℤ) (ω : (Fin d → ℤ) → E) :
    latticePattern E G ((shift E a).toFun ω) = (· + a) '' latticePattern E G ω := by
  have hview : ∀ i : Fin d → ℤ,
      latticeCubeView ((shift E a).toFun ω) i = latticeCubeView ω (i - a) := by
    intro i
    funext c
    rw [latticeCubeView_apply, latticeCubeView_apply, shift_toFun_apply]
    congr 1
    abel
  ext i
  rw [mem_latticePattern_of_isRSymmetric hGsym, hview]
  constructor
  · exact fun h ↦ ⟨i - a, (mem_latticePattern_of_isRSymmetric hGsym ω (i - a)).2 h, by abel⟩
  · rintro ⟨j, hj, rfl⟩
    have := (mem_latticePattern_of_isRSymmetric hGsym ω j).1 hj
    simpa using this

/-- **The pattern set of a periodic configuration is the pullback of the pattern set on the
torus**: Georgii's (18.3) on `ℤ^d` and on `Λ(N)` agree along `latticeToTorus`. -/
lemma latticePattern_periodicPullback (ζ : (Fin d → ZMod (2 * (n + 1))) → E) :
    latticePattern E G (periodicPullback n ζ) = latticeToTorus n ⁻¹' torusPattern E G ζ := by
  ext i
  have hview : latticeCubeView (periodicPullback n ζ) i = cubeView ζ (latticeToTorus n i) := by
    funext c
    simp [latticeCubeView, cubeView, latticeToTorus_add]
  rw [mem_latticePattern, hview, Set.mem_preimage, mem_torusPattern,
    ← tauPow_latticeToTorus (n := n)]

/-! ### Georgii's `°γ_{Λ(N)}^Φ × δ_ω` -/

/-- Georgii's cube `Λ(N)`, `N = n + 1`: `Potential.latticeBox d n = [-N, N)^d`, a translate of
his `]-N, N]^d` of (17.1) and the same fundamental domain of the period group `2N ℤ^d`. -/
abbrev periodicCube (d n : ℕ) : Finset (Fin d → ℤ) := Potential.latticeBox d n

variable (E) in
/-- The configuration on `ℤ^d` that agrees with the periodic continuation of the torus
configuration `ζ` inside the cube `Λ(N)` and with `ω` outside: the coupling map behind
Georgii's product `°γ_{Λ(N)}^Φ × δ_ω`. -/
def periodicJuxt (n : ℕ) (ω : (Fin d → ℤ) → E) (ζ : (Fin d → ZMod (2 * (n + 1))) → E) :
    (Fin d → ℤ) → E :=
  juxt ((periodicCube d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) ω
    fun i ↦ periodicPullback n ζ i.1

omit [MeasurableSpace E] in
lemma periodicJuxt_apply_of_mem {n : ℕ} {ω : (Fin d → ℤ) → E}
    (ζ : (Fin d → ZMod (2 * (n + 1))) → E) {i : Fin d → ℤ} (hi : i ∈ periodicCube d n) :
    periodicJuxt E n ω ζ i = ζ (latticeToTorus n i) := by
  rw [periodicJuxt, juxt_apply_of_mem (Finset.mem_coe.2 hi)]
  rfl

omit [MeasurableSpace E] in
lemma periodicJuxt_apply_of_notMem {n : ℕ} {ω : (Fin d → ℤ) → E}
    (ζ : (Fin d → ZMod (2 * (n + 1))) → E) {i : Fin d → ℤ} (hi : i ∉ periodicCube d n) :
    periodicJuxt E n ω ζ i = ω i := by
  rw [periodicJuxt, juxt_apply_of_not_mem (fun h ↦ hi (Finset.mem_coe.1 h))]

lemma measurable_periodicJuxt (n : ℕ) (ω : (Fin d → ℤ) → E) :
    Measurable (periodicJuxt E n ω) :=
  Measurable.juxt.comp (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)

variable (E) in
/-- **Georgii's `°γ_{Λ(N)}^Φ × δ_{ω}`** (Example (5.20)(3), §18.1): the Gibbs distribution in
the cube `Λ(N)` with periodic boundary condition, read as a random field on `Ω = (ℤ^d → E)`
by freezing the configuration outside `Λ(N)` to `ω`. -/
def periodicGibbsField (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E) (n : ℕ)
    (ω : (Fin d → ℤ) → E) : Measure ((Fin d → ℤ) → E) :=
  (periodicGibbsDist E φ ν (N := n + 1)).map (periodicJuxt E n ω)

variable {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E}

theorem isProbabilityMeasure_periodicGibbsField [IsProbabilityMeasure ν] (hφ : Measurable φ)
    {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) (n : ℕ) (ω : (Fin d → ℤ) → E) :
    IsProbabilityMeasure (periodicGibbsField E φ ν n ω) := by
  have := isProbabilityMeasure_periodicGibbsDist (N := n + 1) (d := d) (ν := ν)
    (IsProbabilityMeasure.ne_zero ν) hφ hM
  exact Measure.isProbabilityMeasure_map (measurable_periodicJuxt n ω).aemeasurable

variable (E) in
/-- The fully periodic field: the law on `Ω` of the `2N`-periodic continuation of the torus
configuration.  It agrees with `periodicGibbsField` on the events of the cube `Λ(N)`
(`periodicGibbsField_apply_of_cylinderEvents`) and, unlike it, is exactly shift invariant. -/
def periodicGibbsPeriodicField (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E) (n : ℕ) :
    Measure ((Fin d → ℤ) → E) :=
  (periodicGibbsDist E φ ν (N := n + 1)).map (periodicPullback n)

theorem isProbabilityMeasure_periodicGibbsPeriodicField [IsProbabilityMeasure ν]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) (n : ℕ) :
    IsProbabilityMeasure (periodicGibbsPeriodicField E φ ν n) := by
  have := isProbabilityMeasure_periodicGibbsDist (N := n + 1) (d := d) (ν := ν)
    (IsProbabilityMeasure.ne_zero ν) hφ hM
  exact Measure.isProbabilityMeasure_map
    (measurable_periodicPullback (E := E) (d := d) (n := n)).aemeasurable

/-- **The boundary condition is invisible inside the cube.**  On an event of the cube `Λ(N)`,
Georgii's `°γ_{Λ(N)}^Φ × δ_ω` does not depend on `ω`: it is the law of the periodic
continuation. -/
theorem periodicGibbsField_apply_of_cylinderEvents (n : ℕ) (ω : (Fin d → ℤ) → E)
    {A : Set ((Fin d → ℤ) → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
      ((periodicCube d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))] A) :
    periodicGibbsField E φ ν n ω A = periodicGibbsPeriodicField E φ ν n A := by
  have hpre : periodicJuxt E n ω ⁻¹' A = periodicPullback n ⁻¹' A := by
    ext ζ
    exact mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦
      periodicJuxt_apply_of_mem ζ (by simpa using hi)
  rw [periodicGibbsField, periodicGibbsPeriodicField,
    Measure.map_apply (measurable_periodicJuxt n ω) (cylinderEvents_le_pi _ hA),
    Measure.map_apply (measurable_periodicPullback (E := E) (d := d) (n := n))
      (cylinderEvents_le_pi _ hA), hpre]

/-! ### The pattern event is local -/

/-- The sites read by Georgii (18.3) over the cubes based in `D`. -/
def cubeSupport (D : Finset (Fin d → ℤ)) : Finset (Fin d → ℤ) :=
  D.biUnion fun i ↦ Finset.univ.image fun c : Fin d → Fin 2 ↦ i + intCubeCast c

omit [MeasurableSpace E] in
lemma mem_cubeSupport {D : Finset (Fin d → ℤ)} {i : Fin d → ℤ} (hi : i ∈ D)
    (c : Fin d → Fin 2) : i + intCubeCast c ∈ cubeSupport D :=
  Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2 ⟨c, Finset.mem_univ c, rfl⟩⟩

/-- **Georgii's event `{D ∩ V(G, ·) = ∅}` is a local event**: it reads only the spins in the
cubes based in `D`. -/
lemma measurableSet_cylinderEvents_forall_notMem_latticePattern
    {G : Set ((Fin d → Fin 2) → E)} (hG : MeasurableSet G) {Δ : Set (Fin d → ℤ)}
    (D : Finset (Fin d → ℤ)) (h : ∀ i ∈ D, ∀ c, i + intCubeCast c ∈ Δ) :
    MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E) Δ]
      {ω : (Fin d → ℤ) → E | ∀ i ∈ D, i ∉ latticePattern E G ω} := by
  classical
  set B : Set (↥(D : Finset (Fin d → ℤ)) → ((Fin d → Fin 2) → E)) :=
    {x | ∀ i : ↥(D : Finset (Fin d → ℤ)),
      tauPow (cubeRefl E) (latticeToTorus 0 i.1) (x i) ∉ G} with hB
  have hBmeas : MeasurableSet B := by
    have hBi : B = ⋂ i : ↥(D : Finset (Fin d → ℤ)),
        ((fun x : ↥(D : Finset (Fin d → ℤ)) → ((Fin d → Fin 2) → E) ↦ x i) ⁻¹'
          (tauPow (cubeRefl E) (latticeToTorus 0 i.1) ⁻¹' G))ᶜ := by
      ext x; simp [hB]
    rw [hBi]
    exact MeasurableSet.iInter fun i ↦
      (((measurable_pi_apply i) ((measurable_tauPow _ _) hG)).compl)
  have hmap : Measurable[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E) Δ]
      fun ω : (Fin d → ℤ) → E ↦ (fun i : ↥(D : Finset (Fin d → ℤ)) ↦ latticeCubeView ω i.1) := by
    refine Measurable.cylinderEvents_of_dependsOn ?_ ?_
    · exact measurable_pi_lambda _ fun _ ↦
        measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
    · intro x y hxy
      funext i c
      exact hxy _ (h i.1 i.2 c)
  have hEq : {ω : (Fin d → ℤ) → E | ∀ i ∈ D, i ∉ latticePattern E G ω}
      = (fun ω : (Fin d → ℤ) → E ↦ (fun i : ↥(D : Finset (Fin d → ℤ)) ↦ latticeCubeView ω i.1))
        ⁻¹' B := by
    ext ω
    simp only [hB, Set.mem_preimage, Set.mem_ofPred_eq, mem_latticePattern]
    exact ⟨fun hh i ↦ hh i.1 i.2, fun hh i hi ↦ hh ⟨i, hi⟩⟩
  rw [hEq]
  exact hmap hBmeas

/-- The local event `{D ∩ V(G, ·) = ∅}` as a member of Georgii's algebra `𝓕⁰`. -/
lemma forall_notMem_latticePattern_mem_localEvents {G : Set ((Fin d → Fin 2) → E)}
    (hG : MeasurableSet G) (D : Finset (Fin d → ℤ)) :
    {ω : (Fin d → ℤ) → E | ∀ i ∈ D, i ∉ latticePattern E G ω} ∈ localEvents (Fin d → ℤ) E :=
  mem_localEvents_of_cylinderEvents (cubeSupport D)
    (measurableSet_cylinderEvents_forall_notMem_latticePattern hG D
      fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c))

/-! ### Shift invariance of the periodic field -/

variable {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E}

/-- **The `2N`-periodic field is exactly shift invariant** (Georgii: `°γ_Λ^Φ` is
`Λ`-periodic).  Shift invariance of the elements of `𝒢₀(Φ)` follows by passing to the limit,
since `periodicGibbsField` and `periodicGibbsPeriodicField` agree on every local event once the
cube is large enough. -/
theorem measurePreserving_shift_periodicGibbsPeriodicField [IsProbabilityMeasure ν]
    (hφ : Measurable φ) (n : ℕ) (a : Fin d → ℤ) :
    MeasurePreserving (shift E a).toFun (periodicGibbsPeriodicField E φ ν n)
      (periodicGibbsPeriodicField E φ ν n) := by
  refine ⟨(shift E a).measurable_toFun, ?_⟩
  rw [periodicGibbsPeriodicField, Measure.map_map (shift E a).measurable_toFun
    (measurable_periodicPullback (E := E) (d := d) (n := n))]
  have hcomp : (shift E a).toFun ∘ periodicPullback (E := E) (d := d) n
      = periodicPullback n ∘ (shift E (latticeToTorus n a)).toFun := by
    funext ζ
    exact (periodicPullback_shift a ζ).symm
  rw [hcomp, ← Measure.map_map (measurable_periodicPullback (E := E) (d := d) (n := n))
    (shift E (latticeToTorus n a)).measurable_toFun,
    (measurePreserving_shift_periodicGibbsDist (N := n + 1) (ν := ν) hφ
      (latticeToTorus n a)).map_eq]

/-! ### Georgii's `𝒢₀(Φ)` -/

variable (E) in
/-- **Georgii's `𝒢₀(Φ)`** (Example (5.20)(3), used throughout §18.1): the set of cluster points,
in the topology of local convergence, of a sequence `(°γ_{Λ(N)}^Φ × δ_{ω_N})_{N ≥ 1}` of Gibbs
distributions in the cubes with periodic boundary condition; the boundary conditions `ω_N` are
arbitrary, and by `periodicGibbsField_apply_of_cylinderEvents` the set does not depend on
them. -/
def GZero (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E) :
    Set (ProbabilityMeasure ((Fin d → ℤ) → E)) :=
  {μ | ∃ μs : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E),
    (∀ n, ∃ ω : (Fin d → ℤ) → E, (μs n : Measure ((Fin d → ℤ) → E))
      = periodicGibbsField E φ ν n ω) ∧
    MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence (Fin d → ℤ) E) atTop
      fun n ↦ WithSetwiseTopology.ofMeasure (μs n)}

/-- Transporting a bound on a local event to a cluster point in the topology of local
convergence.

*This lemma belongs in `GibbsMeasure/Topology/ClusterPoints.lean`.*  The tree already has it,
under the name `MeasureTheory.GibbsMeasure.eval_le_of_mapClusterPt`, in
`GibbsMeasure/Model/PhaseTransition.lean`, where a `Specification`-level file may not import
it; the two should be merged into the `Topology` layer. -/
lemma apply_le_of_mapClusterPt_of_mem_localEvents {S : Type*} {ι : Type*} {l : Filter ι}
    {A : Set (S → E)} (hA : A ∈ localEvents S E) {c : ℝ≥0∞}
    {ms : ι → ProbabilityMeasure (S → E)} {m : WithLocalConvergence S E}
    (hm : MapClusterPt m l fun i ↦ WithSetwiseTopology.ofMeasure (ms i))
    (hle : ∀ᶠ i in l, (ms i : Measure (S → E)) A ≤ c) :
    (m.toMeasure : Measure (S → E)) A ≤ c := by
  set s : Set (WithLocalConvergence S E) := {v | (v.toMeasure : Measure (S → E)) A ≤ c} with hs
  have hclosed : IsClosed s := isClosed_Iic.preimage (WithSetwiseTopology.continuous_apply_enn hA)
  have hcl : ClusterPt m (Filter.map (fun i ↦ (WithSetwiseTopology.ofMeasure (ms i) :
      WithLocalConvergence S E)) l) := hm
  have hprin : (Filter.map (fun i ↦ (WithSetwiseTopology.ofMeasure (ms i) :
      WithLocalConvergence S E)) l) ≤ 𝓟 s :=
    Filter.le_principal_iff.2 (Filter.mem_map.2 hle)
  have hmem : m ∈ closure s := mem_closure_iff_clusterPt.2 (hcl.mono hprin)
  rwa [hclosed.closure_eq] at hmem

/-- Cluster points inherit shift invariance. -/
lemma measurePreserving_shift_of_mapClusterPt {ι : Type*} {l : Filter ι} [l.NeBot]
    {ms : ι → ProbabilityMeasure ((Fin d → ℤ) → E)} {m : WithLocalConvergence (Fin d → ℤ) E}
    (hm : MapClusterPt m l fun i ↦ WithSetwiseTopology.ofMeasure (ms i)) (a : Fin d → ℤ)
    (hinv : ∀ᶠ i in l, MeasurePreserving (shift E a).toFun
      (ms i : Measure ((Fin d → ℤ) → E)) (ms i)) :
    MeasurePreserving (shift E a).toFun (m.toMeasure : Measure ((Fin d → ℤ) → E)) m.toMeasure := by
  set s : Set (WithLocalConvergence (Fin d → ℤ) E) := {v | MeasurePreserving (shift E a).toFun
    (v.toMeasure : Measure ((Fin d → ℤ) → E)) v.toMeasure} with hs
  have hclosed : IsClosed s := isClosed_setOf_measurePreserving (shift E a)
  have hcl : ClusterPt m (Filter.map (fun i ↦ (WithSetwiseTopology.ofMeasure (ms i) :
      WithLocalConvergence (Fin d → ℤ) E)) l) := hm
  have hprin : (Filter.map (fun i ↦ (WithSetwiseTopology.ofMeasure (ms i) :
      WithLocalConvergence (Fin d → ℤ) E)) l) ≤ 𝓟 s :=
    Filter.le_principal_iff.2 (Filter.mem_map.2 hinv)
  have hmem : m ∈ closure s := mem_closure_iff_clusterPt.2 (hcl.mono hprin)
  rwa [hclosed.closure_eq] at hmem

/-- Two local events that the net eventually gives the same value have the same value at a
cluster point. -/
lemma eq_of_mapClusterPt_of_eventually_eq {S : Type*} {ι : Type*} {l : Filter ι} [l.NeBot]
    {ms : ι → ProbabilityMeasure (S → E)} {m : WithLocalConvergence S E}
    (hm : MapClusterPt m l fun i ↦ WithSetwiseTopology.ofMeasure (ms i))
    {A B : Set (S → E)} (hA : A ∈ localEvents S E) (hB : B ∈ localEvents S E)
    (h : ∀ᶠ i in l, (ms i : Measure (S → E)) A = (ms i : Measure (S → E)) B) :
    (m.toMeasure : Measure (S → E)) A = (m.toMeasure : Measure (S → E)) B := by
  obtain ⟨U, hUle, hUconv⟩ := mapClusterPt_iff_ultrafilter.1 hm
  have hA' := tendsto_withLocalConvergence_iff.1 hUconv A hA
  have hB' := tendsto_withLocalConvergence_iff.1 hUconv B hB
  exact tendsto_nhds_unique hA' (hB'.congr' (by filter_upwards [hUle h] with i hi using hi.symm))

/-- **Every member of `𝒢₀(Φ)` is shift invariant**: the part of Georgii's Example (5.20)(3)
that says `𝒢₀(Φ) ⊆ 𝒫_Θ(Ω, 𝓕)`.  The periodic Gibbs distribution `°γ_{Λ(N)}^Φ` is `Λ(N)`-periodic
(Georgii, remark after (17.20)), hence its periodic continuation to `ℤ^d` is exactly shift
invariant, and the boundary condition `ω_N` is invisible on any fixed local event once `Λ(N)` is
large enough. -/
theorem measurePreserving_shift_of_mem_GZero [IsProbabilityMeasure ν] (hφ : Measurable φ)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)} (hμ : μ ∈ GZero E φ ν) (a : Fin d → ℤ) :
    MeasurePreserving (shift E a).toFun (μ : Measure ((Fin d → ℤ) → E)) μ := by
  classical
  obtain ⟨μs, hμs, hcp⟩ := hμ
  refine ⟨(shift E a).measurable_toFun, ?_⟩
  have hprob : IsProbabilityMeasure ((μ : Measure ((Fin d → ℤ) → E)).map (shift E a).toFun) :=
    Measure.isProbabilityMeasure_map (shift E a).measurable_toFun.aemeasurable
  refine separatesOn_localEvents hprob inferInstance fun A hA ↦ ?_
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  rw [Measure.map_apply (shift E a).measurable_toFun hAm]
  refine eq_of_mapClusterPt_of_eventually_eq hcp
    ((shift E a).preimage_mem_localEvents hA) hA ?_
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  set Λ' : Finset (Fin d → ℤ) :=
    Λ.preimage (shift E a).sites (shift E a).sites.injective.injOn with hΛ'
  have hshiftA : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E) (Λ' : Set (Fin d → ℤ))]
      ((shift E a).toFun ⁻¹' A) := by
    rw [hΛ', Finset.coe_preimage]
    exact (shift E a).measurable_toFun_cylinderEvents (Λ : Set (Fin d → ℤ)) hΛ
  filter_upwards [Potential.tendsto_latticeBox_atTop.eventually
    (eventually_ge_atTop (Λ ∪ Λ'))] with n hn
  obtain ⟨ω, hω⟩ := hμs n
  have hsub : Λ ∪ Λ' ⊆ periodicCube d n := hn
  have hAsub : (Λ : Set (Fin d → ℤ)) ⊆ (periodicCube d n : Set (Fin d → ℤ)) := by
    exact_mod_cast Finset.Subset.trans Finset.subset_union_left hsub
  have hA'sub : (Λ' : Set (Fin d → ℤ)) ⊆ (periodicCube d n : Set (Fin d → ℤ)) := by
    exact_mod_cast Finset.Subset.trans Finset.subset_union_right hsub
  rw [hω, periodicGibbsField_apply_of_cylinderEvents n ω
      ((cylinderEvents_mono hA'sub) _ hshiftA),
    periodicGibbsField_apply_of_cylinderEvents n ω ((cylinderEvents_mono hAsub) _ hΛ),
    ← Measure.map_apply (shift E a).measurable_toFun hAm,
    (measurePreserving_shift_periodicGibbsPeriodicField hφ n a).map_eq]

/-! ### Georgii Lemma (18.10) on `ℤ^d` -/

section Ten

variable {φ : ((Fin (d + 1) → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {G : Set ((Fin (d + 1) → Fin 2) → E)}

/-- **Georgii, Lemma (18.10) for the `2N`-periodic field on `ℤ^d`.**  This is the torus estimate
`periodicGibbsDist_forall_notMem_torusPattern_le_patternWeight` read through the periodic
continuation; the hypothesis `D ⊆ Λ(N)` is Georgii's "`Λ = Λ(N)` is so large a cube that
`Λ ⊃ ⋃_{i ∈ D} C + i`", and is what makes `D` and its image in the torus equinumerous. -/
theorem periodicGibbsPeriodicField_forall_notMem_latticePattern_le_patternWeight
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hG : MeasurableSet G) (hGsym : IsRSymmetric E G) {n : ℕ}
    {D : Finset (Fin (d + 1) → ℤ)} (hD : D ⊆ periodicCube (d + 1) n) :
    periodicGibbsPeriodicField E φ ν n {ω | ∀ i ∈ D, i ∉ latticePattern E G ω}
      ≤ patternWeight φ ν G ^ D.card := by
  classical
  set D' : Finset (Fin (d + 1) → ZMod (2 * (n + 1))) := D.image (latticeToTorus n) with hD'def
  have hcard : D'.card = D.card :=
    Finset.card_image_of_injOn fun i hi j hj hij ↦
      latticeToTorus_injOn_latticeBox (Finset.mem_coe.2 (hD hi)) (Finset.mem_coe.2 (hD hj)) hij
  have hAm : MeasurableSet {ω : (Fin (d + 1) → ℤ) → E | ∀ i ∈ D, i ∉ latticePattern E G ω} :=
    cylinderEvents_le_pi _ (measurableSet_cylinderEvents_forall_notMem_latticePattern hG D
      fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c))
  have hmem : ∀ (ζ : (Fin (d + 1) → ZMod (2 * (n + 1))) → E) (i : Fin (d + 1) → ℤ),
      i ∈ latticePattern E G (periodicPullback n ζ) ↔ latticeToTorus n i ∈ torusPattern E G ζ :=
    fun ζ i ↦ by rw [latticePattern_periodicPullback]; exact Iff.rfl
  have hpre : periodicPullback (E := E) n ⁻¹'
      {ω : (Fin (d + 1) → ℤ) → E | ∀ i ∈ D, i ∉ latticePattern E G ω}
      = {ζ | ∀ j ∈ D', j ∉ torusPattern E G ζ} := by
    ext ζ
    constructor
    · intro hh j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      exact fun hc ↦ hh i hi ((hmem ζ i).2 hc)
    · intro hh i hi
      exact fun hc ↦ hh _ (Finset.mem_image.2 ⟨i, hi, rfl⟩) ((hmem ζ i).1 hc)
  rw [periodicGibbsPeriodicField,
    Measure.map_apply (measurable_periodicPullback (E := E) (d := d + 1) (n := n)) hAm, hpre,
    ← hcard]
  exact periodicGibbsDist_forall_notMem_torusPattern_le_patternWeight hφ hM hφk hG hGsym D'

/-- **Georgii, Lemma (18.10) for `°γ_{Λ(N)}^Φ × δ_ω`**, the finite-volume statement his proof
establishes: the boundary condition is invisible on the event `{D ∩ V(G, ·) = ∅}` once the cube
contains `D` together with the elementary cubes based in `D`. -/
theorem periodicGibbsField_forall_notMem_latticePattern_le_patternWeight
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hG : MeasurableSet G) (hGsym : IsRSymmetric E G) {n : ℕ}
    {D : Finset (Fin (d + 1) → ℤ)} (hn : D ∪ cubeSupport D ⊆ periodicCube (d + 1) n)
    (ω : (Fin (d + 1) → ℤ) → E) :
    periodicGibbsField E φ ν n ω {ω' | ∀ i ∈ D, i ∉ latticePattern E G ω'}
      ≤ patternWeight φ ν G ^ D.card := by
  have hDsub : D ⊆ periodicCube (d + 1) n :=
    Finset.Subset.trans Finset.subset_union_left hn
  have hSsub : (cubeSupport D : Set (Fin (d + 1) → ℤ))
      ⊆ (periodicCube (d + 1) n : Set (Fin (d + 1) → ℤ)) := by
    exact_mod_cast Finset.Subset.trans Finset.subset_union_right hn
  rw [periodicGibbsField_apply_of_cylinderEvents n ω ((cylinderEvents_mono hSsub) _
    (measurableSet_cylinderEvents_forall_notMem_latticePattern hG D
      fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c)))]
  exact periodicGibbsPeriodicField_forall_notMem_latticePattern_le_patternWeight
    hφ hM hφk hG hGsym hDsub

/-- **Georgii, Lemma (18.10).**  For an `r`-symmetric pattern `G ∈ ℰ^C`, a `C`-potential `Φ`
and `μ ∈ 𝒢₀(Φ)`,

`μ(D ∩ V(G, ·) = ∅) ≤ t(G, Φ)^{|D|}`

for every finite set `D` of sites of `ℤ^d`.  Georgii's proof: the event is local, so the bound
passes from the finite-volume distributions to the cluster point. -/
theorem forall_notMem_latticePattern_le_patternWeight
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hG : MeasurableSet G) (hGsym : IsRSymmetric E G)
    {μ : ProbabilityMeasure ((Fin (d + 1) → ℤ) → E)} (hμ : μ ∈ GZero E φ ν)
    (D : Finset (Fin (d + 1) → ℤ)) :
    (μ : Measure ((Fin (d + 1) → ℤ) → E)) {ω | ∀ i ∈ D, i ∉ latticePattern E G ω}
      ≤ patternWeight φ ν G ^ D.card := by
  classical
  obtain ⟨μs, hμs, hcp⟩ := hμ
  refine apply_le_of_mapClusterPt_of_mem_localEvents
    (forall_notMem_latticePattern_mem_localEvents hG D) hcp ?_
  filter_upwards [Potential.tendsto_latticeBox_atTop.eventually
    (eventually_ge_atTop (D ∪ cubeSupport D))] with n hn
  obtain ⟨ω, hω⟩ := hμs n
  rw [hω]
  exact periodicGibbsField_forall_notMem_latticePattern_le_patternWeight hφ hM hφk hG hGsym hn ω

end Ten

/-! ### Georgii (17.18): the `C`-potential on `ℤ^d` -/

section CPotential

variable {d n : ℕ}

/-- The elementary cube `C + i = {i + c : c ∈ {0,1}^d}` of `ℤ^d`. -/
def latticeCube (i : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Finset.univ.image fun c : Fin d → Fin 2 ↦ i + intCubeCast c

lemma mem_latticeCube_iff {i x : Fin d → ℤ} :
    x ∈ latticeCube i ↔ ∃ c : Fin d → Fin 2, i + intCubeCast c = x := by
  simp [latticeCube]

@[simp] lemma intCubeCast_zero : intCubeCast (d := d) 0 = 0 := by
  funext k; simp [intCubeCast]

lemma self_mem_latticeCube (i : Fin d → ℤ) : i ∈ latticeCube i :=
  mem_latticeCube_iff.2 ⟨0, by simp⟩

lemma le_of_mem_latticeCube {i x : Fin d → ℤ} (h : x ∈ latticeCube i) (k : Fin d) :
    i k ≤ x k := by
  obtain ⟨c, rfl⟩ := mem_latticeCube_iff.1 h
  have : (0 : ℤ) ≤ intCubeCast c k := Int.natCast_nonneg _
  simpa using this

lemma latticeCube_injective : Function.Injective (latticeCube (d := d)) := by
  intro i j h
  funext k
  have h1 : i k ≤ j k := le_of_mem_latticeCube (h ▸ self_mem_latticeCube j) k
  have h2 : j k ≤ i k := le_of_mem_latticeCube (h.symm ▸ self_mem_latticeCube i) k
  omega

lemma latticeCube_sub_intCubeCast {x : Fin d → ℤ} {i : Fin d → ℤ}
    (h : x ∈ latticeCube i) : ∃ c : Fin d → Fin 2, i = x - intCubeCast c := by
  obtain ⟨c, rfl⟩ := mem_latticeCube_iff.1 h
  exact ⟨c, by ring⟩

variable {E : Type*} [MeasurableSpace E]

variable (E) in
/-- **Georgii, Definition (17.18).** The `C`-potential on `ℤ^d` with cube interaction
`Φ_C = φ`: `Φ_A = 0` unless `A = C + i` for some `i`, and `Φ_{C+i} = Φ_C ∘ θ_{-i}`, conditions
(i) and (ii) of (17.18).  Conditions (iii) (`r_k`-invariance of `φ`) and (iv) (a lower bound on
`φ`) are hypotheses on `φ`, not part of the construction. -/
def cubePotential (φ : ((Fin d → Fin 2) → E) → ℝ) : Potential (Fin d → ℤ) E := fun A η ↦
  ∑ i ∈ A.filter fun i ↦ latticeCube i = A, φ (latticeCubeView η i)

variable {φ : ((Fin d → Fin 2) → E) → ℝ}

/-- **Georgii (17.18)(ii).** -/
@[simp] lemma cubePotential_latticeCube (i : Fin d → ℤ) (η : (Fin d → ℤ) → E) :
    cubePotential E φ (latticeCube i) η = φ (latticeCubeView η i) := by
  have hfilter : (latticeCube i).filter (fun j ↦ latticeCube j = latticeCube i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun h ↦ latticeCube_injective h.2, ?_⟩
    rintro rfl
    exact ⟨self_mem_latticeCube j, rfl⟩
  rw [cubePotential, hfilter, Finset.sum_singleton]

/-- **Georgii (17.18)(i).** -/
lemma cubePotential_eq_zero_of_forall {A : Finset (Fin d → ℤ)}
    (h : ∀ i, latticeCube i ≠ A) : cubePotential E φ A = 0 := by
  funext η
  rw [cubePotential, Finset.filter_eq_empty_iff.2 fun i _ ↦ h i, Finset.sum_empty]
  rfl

lemma cubePotential_ne_zero {A : Finset (Fin d → ℤ)} (h : cubePotential E φ A ≠ 0) :
    ∃ i, latticeCube i = A := by
  by_contra hc
  exact h (cubePotential_eq_zero_of_forall (fun i hi ↦ hc ⟨i, hi⟩))

lemma dependsOn_cubePotential (A : Finset (Fin d → ℤ)) :
    DependsOn (cubePotential E φ A) (A : Set (Fin d → ℤ)) := by
  intro η η' h
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hA : latticeCube i = A := (Finset.mem_filter.1 hi).2
  congr 1
  funext c
  exact h _ (by rw [← hA] at *; exact Finset.mem_coe.2 (mem_latticeCube_iff.2 ⟨c, rfl⟩))

lemma isPotential_cubePotential (hφ : Measurable φ) :
    Potential.IsPotential (cubePotential E φ) where
  measurable A := by
    refine Measurable.cylinderEvents_of_dependsOn ?_ (dependsOn_cubePotential A)
    exact Finset.measurable_sum _ fun i _ ↦ hφ.comp
      (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)

instance isFiniteRange_cubePotential :
    Potential.IsFiniteRange (cubePotential E φ) where
  exists_finset x := by
    classical
    refine ⟨(Finset.univ : Finset (Fin d → Fin 2)).biUnion
      fun c ↦ latticeCube (x - intCubeCast c), fun A hx hA ↦ ?_⟩
    obtain ⟨i, rfl⟩ := cubePotential_ne_zero hA
    obtain ⟨c, hc⟩ := latticeCube_sub_intCubeCast hx
    rw [hc]
    exact Finset.subset_biUnion_of_mem (fun c ↦ latticeCube (x - intCubeCast c))
      (Finset.mem_univ c)

end CPotential

/-! ### Georgii Example (4.20)(2): the periodic modification of a `C`-potential -/

section Wrapped

variable {d n : ℕ}

/-- Georgii's elementary cube `C(i) = C + i mod Λ(N)` of (17.13), read as a subset of the
cube `Λ(N) ⊆ ℤ^d`. -/
def wrappedCube (n : ℕ) (i : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Finset.univ.image fun c : Fin d → Fin 2 ↦ Potential.latticeTorus d n (i + intCubeCast c)

lemma wrappedCube_subset (n : ℕ) (i : Fin d → ℤ) : wrappedCube n i ⊆ periodicCube d n := by
  intro x hx
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
  exact (Potential.isTorusReduction_latticeTorus d n).mapsTo _

lemma wrappedCube_nonempty (n : ℕ) (i : Fin d → ℤ) : (wrappedCube n i).Nonempty :=
  ⟨_, Finset.mem_image.2 ⟨0, Finset.mem_univ 0, rfl⟩⟩

/-- The elementary cube based at `i` does not wrap around the torus `Λ(N)`, `N = n + 1`. -/
def IsUnwrapped (n : ℕ) (i : Fin d → ℤ) : Prop :=
  ∀ k, -((n : ℤ) + 1) ≤ i k ∧ i k + 1 ≤ (n : ℤ)

lemma mem_periodicCube_of_isUnwrapped {i : Fin d → ℤ} (h : IsUnwrapped n i)
    (c : Fin d → Fin 2) : i + intCubeCast c ∈ periodicCube d n := by
  refine Potential.mem_latticeBox.2 fun k ↦ ?_
  have hc : (0 : ℤ) ≤ intCubeCast c k ∧ intCubeCast c k ≤ 1 := by
    refine ⟨Int.natCast_nonneg _, ?_⟩
    have := (c k).isLt
    simp only [intCubeCast]
    omega
  obtain ⟨h1, h2⟩ := h k
  rw [Finset.mem_Ico, Potential.intBoxLeft, Potential.intBoxLen]
  simp only [Pi.add_apply]
  omega

lemma latticeTorus_add_intCubeCast {i : Fin d → ℤ} (h : IsUnwrapped n i) (c : Fin d → Fin 2) :
    Potential.latticeTorus d n (i + intCubeCast c) = i + intCubeCast c :=
  (Potential.isTorusReduction_latticeTorus d n).eq_self _ (mem_periodicCube_of_isUnwrapped h c)

lemma wrappedCube_eq_latticeCube {i : Fin d → ℤ} (h : IsUnwrapped n i) :
    wrappedCube n i = latticeCube i := by
  rw [wrappedCube, latticeCube]
  exact Finset.image_congr fun c _ ↦ latticeTorus_add_intCubeCast h c

variable {E : Type*} [MeasurableSpace E]

/-- The lexicographic anchor of an elementary cube is its corner. -/
@[simp] lemma lexAnchor_latticeCube (i : Fin d → ℤ) : Potential.lexAnchor (latticeCube i) = i := by
  classical
  have hne : (latticeCube i).Nonempty := ⟨i, self_mem_latticeCube i⟩
  have hmapne := Potential.map_toLexEmb_nonempty hne
  have hmin : ((latticeCube i).map (Potential.toLexEmb d)).min' hmapne = toLex i := by
    refine le_antisymm (Finset.min'_le _ _ (Finset.mem_map.2 ⟨i, self_mem_latticeCube i, rfl⟩)) ?_
    refine Finset.le_min' _ _ _ fun y hy ↦ ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    exact Pi.toLex_monotone fun k ↦ le_of_mem_latticeCube hx k
  rw [Potential.lexAnchor_of_nonempty hne hmapne, hmin]
  rfl

@[simp] lemma starImage_latticeCube (n : ℕ) (i : Fin d → ℤ) :
    Potential.starImage (Potential.latticeTorus d n) (latticeCube i) = wrappedCube n i := by
  classical
  rw [Potential.starImage, latticeCube, wrappedCube, Finset.image_image]
  rfl

variable {E : Type*} [MeasurableSpace E]

variable (E) in
/-- **Georgii Example (4.20)(2) for a `C`-potential.** The `Λ(N)`-periodic modification
`Φ̃^{Λ(N)}` of the `C`-potential with cube interaction `φ`, i.e. Georgii's general construction
`Potential.periodicModification` of Example (4.20)(2) at the torus reduction
`Potential.latticeTorus` of the cube `Λ(N)` and the lexicographic anchor.  Its explicit form is
`wrappedCubePotential_apply`: the interaction of the elementary cube `C(i)` of the torus,
evaluated on the periodic continuation, attached to `C(i)` read as a subset of `Λ(N)`. -/
abbrev wrappedCubePotential (φ : ((Fin d → Fin 2) → E) → ℝ) (n : ℕ) :
    Potential (Fin d → ℤ) E :=
  Potential.periodicModification (cubePotential E φ) (Potential.latticeBox d n)
    (Potential.latticeTorus d n) Potential.lexAnchor

variable {φ : ((Fin d → Fin 2) → E) → ℝ}

/-- **The explicit form of `Φ̃^{Λ(N)}` for a `C`-potential.**  The representatives `ℛ(A)` of
Georgii (4.20)(2) are the elementary cubes `C + i` with `i ∈ Λ(N)` whose reduction is `A`. -/
theorem wrappedCubePotential_apply (A : Finset (Fin d → ℤ)) (η : (Fin d → ℤ) → E) :
    wrappedCubePotential E φ n A η
      = ∑ i ∈ (periodicCube d n).filter fun i ↦ wrappedCube n i = A,
          φ fun c ↦ η (Potential.latticeTorus d n (i + intCubeCast c)) := by
  classical
  set S : Set (Finset (Fin d → ℤ)) :=
    {B | Potential.IsRep (Potential.latticeBox d n) Potential.lexAnchor B ∧
      Potential.starImage (Potential.latticeTorus d n) B = A} with hS
  have hmemS : ∀ i : Fin d → ℤ,
      latticeCube i ∈ S ↔ (i ∈ periodicCube d n ∧ wrappedCube n i = A) := by
    intro i
    simp only [hS, Set.mem_ofPred_eq, Potential.IsRep, lexAnchor_latticeCube,
      starImage_latticeCube]
    exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨⟨i, self_mem_latticeCube i⟩, h.1⟩, h.2⟩⟩
  have hsupp : ∀ B ∉ (periodicCube d n).image latticeCube,
      S.indicator (fun B ↦ cubePotential E φ B
        (Potential.periodicExtend (Potential.latticeTorus d n) η)) B = 0 := by
    intro B hB
    by_cases hmem : B ∈ S
    · rw [Set.indicator_of_mem hmem]
      by_contra hne
      obtain ⟨i, rfl⟩ := cubePotential_ne_zero
        (show cubePotential E φ B ≠ 0 from fun hc ↦ hne (by rw [hc]; rfl))
      exact hB (Finset.mem_image.2 ⟨i, ((hmemS i).1 hmem).1, rfl⟩)
    · exact Set.indicator_of_notMem hmem _
  rw [wrappedCubePotential, Potential.periodicModification_apply, tsum_eq_sum hsupp,
    Finset.sum_image fun x _ y _ h ↦ latticeCube_injective h,
    ← Finset.sum_subset (Finset.filter_subset (fun i ↦ wrappedCube n i = A) (periodicCube d n))
      fun i hi hnot ↦ Set.indicator_of_notMem
        (fun hc ↦ hnot (Finset.mem_filter.2 ⟨hi, ((hmemS i).1 hc).2⟩)) _]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  obtain ⟨hi₁, hi₂⟩ := Finset.mem_filter.1 hi
  rw [Set.indicator_of_mem ((hmemS i).2 ⟨hi₁, hi₂⟩)]
  exact cubePotential_latticeCube i _

lemma wrappedCubePotential_ne_zero {A : Finset (Fin d → ℤ)}
    (h : wrappedCubePotential E φ n A ≠ 0) : ∃ i ∈ periodicCube d n, wrappedCube n i = A := by
  by_contra hc
  refine h (funext fun η ↦ ?_)
  rw [wrappedCubePotential_apply, Finset.filter_eq_empty_iff.2 fun i hi hw ↦ hc ⟨i, hi, hw⟩,
    Finset.sum_empty]
  rfl

lemma dependsOn_wrappedCubePotential (A : Finset (Fin d → ℤ)) :
    DependsOn (wrappedCubePotential E φ n A) (A : Set (Fin d → ℤ)) := by
  intro η η' h
  rw [wrappedCubePotential_apply, wrappedCubePotential_apply]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hA : wrappedCube n i = A := (Finset.mem_filter.1 hi).2
  congr 1
  funext c
  exact h _ (by rw [← hA]; exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨c, Finset.mem_univ c, rfl⟩))

lemma isPotential_wrappedCubePotential (hφ : Measurable φ) :
    Potential.IsPotential (wrappedCubePotential E φ n) where
  measurable A := by
    refine Measurable.cylinderEvents_of_dependsOn ?_ (dependsOn_wrappedCubePotential A)
    have hfun : wrappedCubePotential E φ n A = fun η ↦
        ∑ i ∈ (periodicCube d n).filter fun i ↦ wrappedCube n i = A,
          φ fun c ↦ η (Potential.latticeTorus d n (i + intCubeCast c)) :=
      funext (wrappedCubePotential_apply A)
    rw [hfun]
    exact Finset.measurable_sum _ fun i _ ↦ hφ.comp
      (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)

instance isFiniteRange_wrappedCubePotential :
    Potential.IsFiniteRange (wrappedCubePotential E φ n) where
  exists_finset _ := ⟨periodicCube d n, fun A _ hA ↦ by
    obtain ⟨i, -, rfl⟩ := wrappedCubePotential_ne_zero hA
    exact wrappedCube_subset n i⟩

end Wrapped

/-! ### The two Hamiltonians -/

section Hamiltonians

variable {d n : ℕ} {E : Type*} [MeasurableSpace E] {φ : ((Fin d → Fin 2) → E) → ℝ}

/-- Two finite-range potentials whose interaction terms agree on every set meeting `Λ` have the
same Hamiltonian in `Λ`.

*This lemma belongs in `GibbsMeasure/Potential.lean`, next to
`Potential.interactingHamiltonian`.* -/
lemma interactingHamiltonian_congr {S F : Type*} [MeasurableSpace F]
    {Φ Ψ : Potential S F} [Potential.IsFiniteRange Φ] [Potential.IsFiniteRange Ψ] {Λ : Finset S}
    (h : ∀ A : Finset S, ((A : Set S) ∩ (Λ : Set S)).Nonempty → Φ A = Ψ A) (η : S → F) :
    Potential.interactingHamiltonian (Φ := Φ) Λ η
      = Potential.interactingHamiltonian (Φ := Ψ) Λ η := by
  have hsupp : Potential.interactingSupport (Φ := Φ) Λ
      = Potential.interactingSupport (Φ := Ψ) Λ := by
    ext A
    rw [Potential.mem_interactingSupport, Potential.mem_interactingSupport]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, fun hc ↦ h2 (by rw [h A h1]; exact hc)⟩,
      fun ⟨h1, h2⟩ ↦ ⟨h1, fun hc ↦ h2 (by rw [← h A h1]; exact hc)⟩⟩
  rw [Potential.interactingHamiltonian, Potential.interactingHamiltonian, hsupp]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  rw [h A (Potential.mem_interactingSupport.1 hA).1]

/-- **The Hamiltonian of the periodic modification in the whole cube is Georgii's periodic
Hamiltonian (17.20)**: every elementary cube `C(i)`, `i ∈ Λ(N)`, contributes `Φ_C` once. -/
theorem interactingHamiltonian_wrappedCubePotential (η : (Fin d → ℤ) → E) :
    Potential.interactingHamiltonian (Φ := wrappedCubePotential E φ n) (periodicCube d n) η
      = ∑ i ∈ periodicCube d n,
          φ fun c ↦ η (Potential.latticeTorus d n (i + intCubeCast c)) := by
  classical
  set f : (Fin d → ℤ) → ℝ :=
    fun i ↦ φ fun c ↦ η (Potential.latticeTorus d n (i + intCubeCast c)) with hf
  set T : Finset (Finset (Fin d → ℤ)) := (periodicCube d n).image (wrappedCube n) with hT
  have hsub : Potential.interactingSupport (Φ := wrappedCubePotential E φ n) (periodicCube d n)
      ⊆ T := by
    intro A hA
    obtain ⟨-, hne⟩ := Potential.mem_interactingSupport.1 hA
    obtain ⟨i, hi, rfl⟩ := wrappedCubePotential_ne_zero hne
    exact Finset.mem_image.2 ⟨i, hi, rfl⟩
  have hzero : ∀ A ∈ T,
      A ∉ Potential.interactingSupport (Φ := wrappedCubePotential E φ n) (periodicCube d n) →
      wrappedCubePotential E φ n A η = 0 := by
    intro A hA hnot
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
    by_cases hz : wrappedCubePotential E φ n (wrappedCube n i) = 0
    · rw [hz]; rfl
    · refine absurd (Potential.mem_interactingSupport.2 ⟨?_, hz⟩) hnot
      obtain ⟨x, hx⟩ := wrappedCube_nonempty n i
      exact ⟨x, Finset.mem_coe.2 hx, Finset.mem_coe.2 (wrappedCube_subset n i hx)⟩
  rw [Potential.interactingHamiltonian, Finset.sum_subset hsub hzero, hT]
  simp only [wrappedCubePotential_apply]
  exact Finset.sum_fiberwise_of_maps_to (fun x hx ↦ Finset.mem_image_of_mem _ hx) f

/-! #### The periodic modification agrees with the `C`-potential in a fixed volume -/

lemma eq_zero_of_dvd_of_abs_lt {N a : ℤ} (h : N ∣ a) (hlt : |a| < N) : a = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rfl
  · exact absurd (Int.le_of_dvd (abs_pos.2 ha) ((dvd_abs _ _).2 h)) (not_le.2 hlt)

lemma intCubeCast_mem_zero_one (c : Fin d → Fin 2) (k : Fin d) :
    0 ≤ intCubeCast c k ∧ intCubeCast c k ≤ 1 := by
  have := (c k).isLt
  simp only [intCubeCast]
  omega

lemma bounds_of_mem_periodicCube {m : ℕ} {x : Fin d → ℤ} (hx : x ∈ periodicCube d m)
    (k : Fin d) : -((m : ℤ) + 1) ≤ x k ∧ x k ≤ (m : ℤ) := by
  have := Potential.mem_latticeBox.1 hx k
  rw [Finset.mem_Ico, Potential.intBoxLeft, Potential.intBoxLen] at this
  omega

lemma mem_periodicCube_of_bounds {m : ℕ} {x : Fin d → ℤ}
    (h : ∀ k, -((m : ℤ) + 1) ≤ x k ∧ x k ≤ (m : ℤ)) : x ∈ periodicCube d m := by
  refine Potential.mem_latticeBox.2 fun k ↦ ?_
  rw [Finset.mem_Ico, Potential.intBoxLeft, Potential.intBoxLen]
  have := h k
  omega

/-- If a cube of the torus meets a small cube `Λ(M)` and `N ≥ M + 1`, its anchor lies in the
interior of `Λ(N)`, so the cube does not wrap. -/
lemma isUnwrapped_of_wrappedCube_meets {m : ℕ} (hn : m + 1 ≤ n) {i : Fin d → ℤ}
    (hi : i ∈ periodicCube d n) {x : Fin d → ℤ} (hx : x ∈ wrappedCube n i)
    (hxm : x ∈ periodicCube d m) : IsUnwrapped n i := by
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
  intro k
  obtain ⟨hi1, hi2⟩ := bounds_of_mem_periodicCube hi k
  obtain ⟨hx1, hx2⟩ := bounds_of_mem_periodicCube hxm k
  obtain ⟨hc1, hc2⟩ := intCubeCast_mem_zero_one c k
  have hnm : (m : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
  have hdvd : Potential.intBoxLen n ∣
      (Potential.latticeTorus d n (i + intCubeCast c) k - (i k + intCubeCast c k)) := by
    have := (Potential.isTorusReduction_latticeTorus d n).sub_mem' (i + intCubeCast c)
    rw [Potential.mem_piPeriods] at this
    obtain ⟨q, hq⟩ := AddSubgroup.mem_zmultiples_iff.1 (this k)
    exact ⟨q, by simpa [mul_comm] using hq.symm⟩
  rw [Potential.intBoxLen] at hdvd
  have hzero : Potential.latticeTorus d n (i + intCubeCast c) k - (i k + intCubeCast c k) = 0 := by
    refine eq_zero_of_dvd_of_abs_lt hdvd ?_
    rw [abs_lt]
    constructor <;> omega
  omega

/-- Conversely, if an elementary cube of `ℤ^d` meets `Λ(M)` and `N ≥ M + 1`, it does not wrap. -/
lemma isUnwrapped_of_latticeCube_meets {m : ℕ} (hn : m + 1 ≤ n) {i : Fin d → ℤ}
    {x : Fin d → ℤ} (hx : x ∈ latticeCube i) (hxm : x ∈ periodicCube d m) :
    IsUnwrapped n i := by
  obtain ⟨c, rfl⟩ := mem_latticeCube_iff.1 hx
  intro k
  obtain ⟨hx1, hx2⟩ := bounds_of_mem_periodicCube hxm k
  obtain ⟨hc1, hc2⟩ := intCubeCast_mem_zero_one c k
  have hnm : (m : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
  simp only [Pi.add_apply] at hx1 hx2
  omega

lemma mem_periodicCube_of_isUnwrapped' {i : Fin d → ℤ} (h : IsUnwrapped n i) :
    i ∈ periodicCube d n := by
  refine mem_periodicCube_of_bounds fun k ↦ ?_
  have := h k
  omega

/-- **Georgii Example (4.20)(2), the local comparison.** On every set that meets the small cube
`Λ(M)`, the periodic modification of the `C`-potential in `Λ(N)` agrees with the `C`-potential
itself, as soon as `N ≥ M + 1`. -/
theorem wrappedCubePotential_eq_cubePotential {m : ℕ} (hn : m + 1 ≤ n)
    {A : Finset (Fin d → ℤ)}
    (hA : ((A : Set (Fin d → ℤ)) ∩ (periodicCube d m : Set (Fin d → ℤ))).Nonempty) :
    wrappedCubePotential E φ n A = cubePotential E φ A := by
  classical
  obtain ⟨x, hxA, hxm⟩ := hA
  rw [Finset.mem_coe] at hxA
  rw [Finset.mem_coe] at hxm
  have hfilter : (periodicCube d n).filter (fun i ↦ wrappedCube n i = A)
      = A.filter fun i ↦ latticeCube i = A := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hw⟩
      have hun : IsUnwrapped n i :=
        isUnwrapped_of_wrappedCube_meets hn hi (by rw [hw]; exact hxA) hxm
      rw [wrappedCube_eq_latticeCube hun] at hw
      exact ⟨hw ▸ self_mem_latticeCube i, hw⟩
    · rintro ⟨-, hl⟩
      have hun : IsUnwrapped n i :=
        isUnwrapped_of_latticeCube_meets hn (by rw [hl]; exact hxA) hxm
      exact ⟨mem_periodicCube_of_isUnwrapped' hun, by rw [wrappedCube_eq_latticeCube hun]; exact hl⟩
  funext η
  rw [wrappedCubePotential_apply, cubePotential, hfilter]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hl : latticeCube i = A := (Finset.mem_filter.1 hi).2
  have hun : IsUnwrapped n i :=
    isUnwrapped_of_latticeCube_meets hn (by rw [hl]; exact hxA) hxm
  congr 1
  funext c
  rw [latticeCubeView_apply, latticeTorus_add_intCubeCast hun]

end Hamiltonians

/-! ### Condition (iv) of (17.18): the Gibbsian specification of a `C`-potential -/

section GibbsSpec

variable {d n : ℕ} {E : Type*} [MeasurableSpace E] {φ : ((Fin d → Fin 2) → E) → ℝ}
  {ν : Measure E} [IsProbabilityMeasure ν]

/-- A uniform lower bound on the interaction terms bounds the Boltzmann weight above.

*This lemma belongs in `GibbsMeasure/Potential.lean`, next to
`Potential.partitionFunction_ne_top_of_boltzmannWeight_le`.* -/
lemma boltzmannWeight_le_of_le {S F : Type*} [MeasurableSpace F] {Ψ : Potential S F}
    [Potential.IsFiniteRange Ψ] {c : ℝ} (h : ∀ A η, c ≤ Ψ A η) (Λ : Finset S) (σ : S → F) :
    Potential.boltzmannWeight (Φ := Ψ) 1 Λ σ
      ≤ ENNReal.ofReal (Real.exp (-((Potential.interactingSupport (Φ := Ψ) Λ).card • c))) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hsum := Finset.card_nsmul_le_sum (Potential.interactingSupport (Φ := Ψ) Λ)
    (fun A ↦ Ψ A σ) c fun A _ ↦ h A σ
  simp only [Potential.interactingHamiltonian, nsmul_eq_mul] at hsum ⊢
  linarith

/-- **Condition (iv) of Georgii (17.18)**: the interaction terms of the `C`-potential are
bounded below. -/
lemma le_cubePotential {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) (A : Finset (Fin d → ℤ))
    (η : (Fin d → ℤ) → E) : min M 0 ≤ cubePotential E φ A η := by
  by_cases h : ∃ i, latticeCube i = A
  · obtain ⟨i, rfl⟩ := h
    rw [cubePotential_latticeCube]
    exact (min_le_left _ _).trans (hM _)
  · push Not at h
    rw [show cubePotential E φ A η = 0 from congrFun (cubePotential_eq_zero_of_forall h) η]
    exact min_le_right _ _

/-- The same bound for the periodic modification: each of its interaction terms is a sum of at
most `|Λ(N)|` cube interactions. -/
lemma le_wrappedCubePotential {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) (A : Finset (Fin d → ℤ))
    (η : (Fin d → ℤ) → E) :
    ((periodicCube d n).card : ℝ) * min M 0 ≤ wrappedCubePotential E φ n A η := by
  classical
  have h1 : (((periodicCube d n).filter fun i ↦ wrappedCube n i = A).card : ℝ) * min M 0
      ≤ wrappedCubePotential E φ n A η := by
    have := Finset.card_nsmul_le_sum ((periodicCube d n).filter fun i ↦ wrappedCube n i = A)
      (fun i ↦ φ fun c ↦ η (Potential.latticeTorus d n (i + intCubeCast c))) (min M 0)
      fun i _ ↦ (min_le_left _ _).trans (hM _)
    rw [wrappedCubePotential_apply]
    simpa [nsmul_eq_mul] using this
  refine le_trans ?_ h1
  exact mul_le_mul_of_nonpos_right
    (by exact_mod_cast Finset.card_filter_le _ _) (min_le_right _ _)

/-- **Georgii (17.19)(1).** Condition (iv) of (17.18) makes a `C`-potential `λ`-admissible:
all the partition functions are finite (and, the Boltzmann weights being positive, nonzero). -/
theorem isSigmaFiniteLambdaAdmissible_cubePotential (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) :
    Specification.IsSigmaFiniteLambdaAdmissible (S := Fin d → ℤ) (E := E) ν
      ((cubePotential E φ).boltzmannFactor 1) := by
  have := isPotential_cubePotential (E := E) (φ := φ) hφ
  have hbf : (cubePotential E φ).boltzmannFactor 1
      = Potential.boltzmannWeight (Φ := cubePotential E φ) 1 :=
    funext fun Λ ↦ funext fun η ↦ Potential.boltzmannFactor_eq_boltzmannWeight 1 Λ η
  rw [hbf]
  refine (Potential.isBoltzmannAdmissible_iff_isSigmaFiniteBoltzmannAdmissible
    (cubePotential E φ) 1 ν).1
    (Potential.isBoltzmannAdmissible_of_premodifierZ_ne_top (cubePotential E φ) 1 ν
      fun Λ η ↦ ?_)
  simpa [Potential.partitionFunction] using
    Potential.partitionFunction_ne_top_of_boltzmannWeight_le (cubePotential E φ) 1 ν Λ η
      (C := ENNReal.ofReal (Real.exp
        (-((Potential.interactingSupport (Φ := cubePotential E φ) Λ).card • min M 0))))
      ENNReal.ofReal_ne_top
      fun σ ↦ boltzmannWeight_le_of_le (fun A η ↦ le_cubePotential hM A η) Λ σ

/-- The periodic modification of a `C`-potential is `λ`-admissible for the same reason. -/
theorem isSigmaFiniteLambdaAdmissible_wrappedCubePotential (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) (n : ℕ) :
    Specification.IsSigmaFiniteLambdaAdmissible (S := Fin d → ℤ) (E := E) ν
      ((wrappedCubePotential E φ n).boltzmannFactor 1) := by
  have := isPotential_wrappedCubePotential (E := E) (φ := φ) (n := n) hφ
  have hbf : (wrappedCubePotential E φ n).boltzmannFactor 1
      = Potential.boltzmannWeight (Φ := wrappedCubePotential E φ n) 1 :=
    funext fun Λ ↦ funext fun η ↦ Potential.boltzmannFactor_eq_boltzmannWeight 1 Λ η
  rw [hbf]
  refine (Potential.isBoltzmannAdmissible_iff_isSigmaFiniteBoltzmannAdmissible
    (wrappedCubePotential E φ n) 1 ν).1
    (Potential.isBoltzmannAdmissible_of_premodifierZ_ne_top (wrappedCubePotential E φ n) 1 ν
      fun Λ η ↦ ?_)
  simpa [Potential.partitionFunction] using
    Potential.partitionFunction_ne_top_of_boltzmannWeight_le (wrappedCubePotential E φ n) 1 ν Λ η
      (C := ENNReal.ofReal (Real.exp
        (-((Potential.interactingSupport (Φ := wrappedCubePotential E φ n) Λ).card •
          (((periodicCube d n).card : ℝ) * min M 0)))))
      ENNReal.ofReal_ne_top
      fun σ ↦ boltzmannWeight_le_of_le (fun A η ↦ le_wrappedCubePotential hM A η) Λ σ


variable (E) in
/-- **Georgii's Gibbsian specification `γ^Φ`** (Definition (2.9)) of the `C`-potential (17.18)
with cube interaction `Φ_C = φ`.  The hypotheses are exactly (17.18): `φ` measurable, and
condition (iv) in the form of a lower bound, which is what makes the potential `λ`-admissible
(Georgii (17.19)(1)). -/
noncomputable def cubeGibbsSpec (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E)
    [IsProbabilityMeasure ν] (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) :
    Specification (Fin d → ℤ) E :=
  haveI := isPotential_cubePotential (E := E) (φ := φ) hφ
  Potential.gibbsSpecificationOfSigmaFiniteAdmissible (cubePotential E φ) ν 1
    (isSigmaFiniteLambdaAdmissible_cubePotential hφ hM.choose_spec)

variable (E) in
/-- **Georgii's `γ^{Φ̃^{Λ(N)}}`**: the Gibbsian specification of the periodic modification of
the `C`-potential in the cube `Λ(N)`. -/
noncomputable def wrappedCubeGibbsSpec (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E)
    [IsProbabilityMeasure ν] (n : ℕ) (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) :
    Specification (Fin d → ℤ) E :=
  haveI := isPotential_wrappedCubePotential (E := E) (φ := φ) (n := n) hφ
  Potential.gibbsSpecificationOfSigmaFiniteAdmissible (wrappedCubePotential E φ n) ν 1
    (isSigmaFiniteLambdaAdmissible_wrappedCubePotential hφ hM.choose_spec n)

/-- **Georgii Example (4.20)(2): `γ^{Φ̃^{Λ(N)}}_Λ = γ^Φ_Λ` for `Λ` well inside `Λ(N)`.**  The
two potentials have the same interaction terms on every set that meets `Λ`, hence the same
Hamiltonian in `Λ`, hence the same Gibbs kernel. -/
theorem wrappedCubeGibbsSpec_apply_eq_cubeGibbsSpec (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) {m : ℕ} (hn : m + 1 ≤ n) {Λ : Finset (Fin d → ℤ)}
    (hΛ : Λ ⊆ periodicCube d m) (η : (Fin d → ℤ) → E) :
    wrappedCubeGibbsSpec E φ ν n hφ hM Λ η = cubeGibbsSpec E φ ν hφ hM Λ η := by
  have hρ : (wrappedCubePotential E φ n).boltzmannFactor 1 Λ
      = (cubePotential E φ).boltzmannFactor 1 Λ := by
    funext σ
    rw [Potential.boltzmannFactor, Potential.boltzmannFactor,
      Potential.hamiltonian_eq_interactingHamiltonian,
      Potential.hamiltonian_eq_interactingHamiltonian,
      interactingHamiltonian_congr (Φ := wrappedCubePotential E φ n) (Ψ := cubePotential E φ)
        (Λ := Λ)
        (fun A hA ↦ wrappedCubePotential_eq_cubePotential hn
          (hA.mono (Set.inter_subset_inter_right _ (by exact_mod_cast hΛ)))) σ]
  simp only [wrappedCubeGibbsSpec, cubeGibbsSpec,
    Potential.gibbsSpecificationOfSigmaFiniteAdmissible, Specification.lambdaSpecification_apply]
  congr 1
  funext σ
  rw [Specification.sigmaFinitePremodifierNorm, Specification.sigmaFinitePremodifierNorm,
    Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaZ, hρ]


/-! ### The bridge: `γ^{Φ̃^{Λ(N)}}_{Λ(N)}(·|ω) = °γ_{Λ(N)}^Φ × δ_ω` -/

/-- **Georgii (17.20).** The Hamiltonian of the periodic modification in the whole cube,
evaluated on the periodic continuation of a torus configuration, is Georgii's periodic
Hamiltonian `∑_{i ∈ Λ} Φ_{C(i)}`. -/
theorem interactingHamiltonian_periodicJuxt (n : ℕ) (ω : (Fin d → ℤ) → E)
    (ζ : (Fin d → ZMod (2 * (n + 1))) → E) :
    Potential.interactingHamiltonian (Φ := wrappedCubePotential E φ n) (periodicCube d n)
        (periodicJuxt E n ω ζ) = periodicHamiltonian E φ ζ := by
  rw [interactingHamiltonian_wrappedCubePotential]
  have hterm : ∀ i ∈ periodicCube d n,
      (φ fun c ↦ periodicJuxt E n ω ζ (Potential.latticeTorus d n (i + intCubeCast c)))
        = φ (cubeView ζ (latticeToTorus n i)) := by
    intro i _
    congr 1
    funext c
    rw [periodicJuxt_apply_of_mem _ ((Potential.isTorusReduction_latticeTorus d n).mapsTo _),
      latticeToTorus_latticeTorus, latticeToTorus_add, latticeToTorus_intCubeCast]
    rfl
  rw [Finset.sum_congr rfl hterm, periodicHamiltonian]
  exact sum_latticeBox_comp_latticeToTorus fun j ↦ φ (cubeView ζ j)

/-- The coupling map pushes the product measure on the torus to Georgii's `λ_{Λ(N)}(·|ω)`. -/
theorem map_periodicJuxt_pi (n : ℕ) (ω : (Fin d → ℤ) → E) :
    (Measure.pi fun _ : (Fin d → ZMod (2 * (n + 1))) ↦ ν).map (periodicJuxt E n ω)
      = Specification.isssd (S := Fin d → ℤ) (E := E) ν (periodicCube d n) ω := by
  classical
  have hg : Function.Injective fun i : ↥(periodicCube d n) ↦ latticeToTorus n i.1 :=
    fun i j hij ↦ Subtype.ext (latticeToTorus_injOn_latticeBox (Finset.mem_coe.2 i.2)
      (Finset.mem_coe.2 j.2) hij)
  have hcomp : periodicJuxt E n ω
      = (juxt ((periodicCube d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) ω) ∘
        fun ζ : (Fin d → ZMod (2 * (n + 1))) → E ↦
          ζ ∘ fun i : ↥(periodicCube d n) ↦ latticeToTorus n i.1 := rfl
  rw [hcomp, ← Measure.map_map Measurable.juxt (measurable_comp_right _),
    map_comp_pi_of_injective ν hg]
  rfl

variable (E) in
/-- **The bridge.**  Georgii's `°γ_{Λ(N)}^Φ × δ_ω` — the Gibbs distribution in the cube with
periodic boundary condition, read as a random field on `ℤ^d` — is the finite-volume Gibbs
distribution `γ^{Φ̃^{Λ(N)}}_{Λ(N)}(·|ω)` of the periodic modification of the `C`-potential
(Georgii, Example (4.20)(2) and (17.20)). -/
theorem wrappedCubeGibbsSpec_periodicCube_eq_periodicGibbsField (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) (n : ℕ) (ω : (Fin d → ℤ) → E) :
    wrappedCubeGibbsSpec E φ ν n hφ hM (periodicCube d n) ω = periodicGibbsField E φ ν n ω := by
  classical
  have := isPotential_wrappedCubePotential (E := E) (φ := φ) (n := n) hφ
  have hwmeas : Measurable
      ((wrappedCubePotential E φ n).boltzmannFactor 1 (periodicCube d n)) := by
    have hb : (wrappedCubePotential E φ n).boltzmannFactor 1 (periodicCube d n)
        = Potential.boltzmannWeight (Φ := wrappedCubePotential E φ n) 1 (periodicCube d n) :=
      funext fun σ ↦ Potential.boltzmannFactor_eq_boltzmannWeight 1 (periodicCube d n) σ
    rw [hb]
    exact Potential.measurable_boltzmannWeight 1 (periodicCube d n)
  have hlam : Specification.sigmaFiniteLambdaFun (S := Fin d → ℤ) (E := E) ν
      (periodicCube d n) ω = Specification.isssd (S := Fin d → ℤ) (E := E) ν
      (periodicCube d n) ω := by
    rw [Specification.sigmaFiniteLambdaFun_eq_isssdFun]
    rfl
  have hdens : (fun ζ : (Fin d → ZMod (2 * (n + 1))) → E ↦
      ENNReal.ofReal (Real.exp (-periodicHamiltonian E φ ζ)))
      = fun ζ ↦ (wrappedCubePotential E φ n).boltzmannFactor 1 (periodicCube d n)
        (periodicJuxt E n ω ζ) := by
    funext ζ
    rw [Potential.boltzmannFactor, Potential.hamiltonian_eq_interactingHamiltonian,
      interactingHamiltonian_periodicJuxt]
    norm_num
  have hmap : (periodicGibbs E φ ν (N := n + 1)).map (periodicJuxt E n ω)
      = (Specification.isssd (S := Fin d → ℤ) (E := E) ν (periodicCube d n) ω).withDensity
        ((wrappedCubePotential E φ n).boltzmannFactor 1 (periodicCube d n)) := by
    rw [periodicGibbs, hdens, map_withDensity_comp _ (measurable_periodicJuxt n ω) hwmeas,
      map_periodicJuxt_pi]
  have hmuniv : ((Specification.isssd (S := Fin d → ℤ) (E := E) ν (periodicCube d n) ω).withDensity
      ((wrappedCubePotential E φ n).boltzmannFactor 1 (periodicCube d n))) Set.univ
      = periodicGibbs E φ ν (N := n + 1) Set.univ := by
    rw [← hmap, Measure.map_apply (measurable_periodicJuxt n ω) MeasurableSet.univ]
    rfl
  have hrhs : periodicGibbsField E φ ν n ω
      = (periodicGibbs E φ ν (N := n + 1) Set.univ)⁻¹ •
        ((Specification.isssd (S := Fin d → ℤ) (E := E) ν (periodicCube d n) ω).withDensity
          ((wrappedCubePotential E φ n).boltzmannFactor 1 (periodicCube d n))) := by
    rw [periodicGibbsField, periodicGibbsDist, Measure.map_smul, hmap]
  have hZ : Specification.sigmaFiniteLambdaZ (S := Fin d → ℤ) (E := E) ν
      ((wrappedCubePotential E φ n).boltzmannFactor 1) (periodicCube d n) ω
      = periodicGibbs E φ ν (N := n + 1) Set.univ := by
    rw [← hmuniv, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      Specification.sigmaFiniteLambdaZ, hlam]
  refine Measure.ext fun A hA ↦ ?_
  rw [hrhs, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA, wrappedCubeGibbsSpec,
    Potential.gibbsSpecificationOfSigmaFiniteAdmissible_apply_set _ _ _ _ _ _ hA, hZ, hlam]


/-! ### Georgii Example (5.20)(3): `𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)` -/

/-- The Hamiltonian of a finite-range potential is a *local* function, hence quasilocal in the
sense of Georgii (2.22).

*This lemma belongs in `GibbsMeasure/Potential.lean`, next to
`Potential.interactingHamiltonian`.* -/
lemma isQuasilocalFun_interactingHamiltonian {S F : Type*} [MeasurableSpace F]
    {Ψ : Potential S F} [Potential.IsFiniteRange Ψ] [Potential.IsPotential Ψ]
    (Λ : Finset S) : IsQuasilocalFun (Potential.interactingHamiltonian (Φ := Ψ) Λ) := by
  classical
  intro ε hε
  refine ⟨(Potential.interactingSupport (Φ := Ψ) Λ).biUnion id, fun ζ η h ↦ ?_⟩
  have heq : Potential.interactingHamiltonian (Φ := Ψ) Λ ζ
      = Potential.interactingHamiltonian (Φ := Ψ) Λ η :=
    Finset.sum_congr rfl fun A hA ↦ Potential.IsPotential.eq_of_eqOn fun x hx ↦
      h x (Finset.mem_biUnion.2 ⟨A, hA, hx⟩)
  rw [heq]
  simpa using hε.le

/-- **Georgii Example (2.25).** The Gibbsian specification of a `C`-potential is quasilocal: its
Hamiltonians are local functions. -/
theorem isQuasilocal_cubeGibbsSpec (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) :
    (cubeGibbsSpec E φ ν hφ hM).IsQuasilocal := by
  have := isPotential_cubePotential (E := E) (φ := φ) hφ
  refine Potential.isQuasilocal_gibbsSpecificationOfSigmaFiniteAdmissible
    (cubePotential E φ) ν 1 _ fun Λ ↦ ?_
  have hfun : (fun η : (Fin d → ℤ) → E ↦ (1 : ℝ) * (cubePotential E φ).hamiltonian Λ η)
      = Potential.interactingHamiltonian (Φ := cubePotential E φ) Λ := by
    funext η
    rw [one_mul, Potential.hamiltonian_eq_interactingHamiltonian]
  rw [hfun]
  exact isQuasilocalFun_interactingHamiltonian Λ

/-- The kernels of the periodic modification stabilise: in a fixed volume they eventually
coincide with those of the `C`-potential. -/
theorem eventually_wrappedCubeGibbsSpec_apply_eq (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) (Λ : Finset (Fin d → ℤ)) :
    ∀ᶠ n in atTop, ∀ η : (Fin d → ℤ) → E,
      wrappedCubeGibbsSpec E φ ν n hφ hM Λ η = cubeGibbsSpec E φ ν hφ hM Λ η := by
  obtain ⟨m, hm⟩ := (Filter.tendsto_atTop_atTop.1 (Potential.tendsto_latticeBox_atTop (d := d))) Λ
  filter_upwards [eventually_ge_atTop (m + 1)] with n hn η
  exact wrappedCubeGibbsSpec_apply_eq_cubeGibbsSpec hφ hM hn (hm m le_rfl) η

/-- **Georgii, Example (5.20)(3), the Gibbs half: `𝒢₀(Φ) ⊆ 𝒢(Φ)`.**  Every cluster point of the
Gibbs distributions in the cubes with periodic boundary condition is a Gibbs measure for the
`C`-potential.  Georgii's argument is Example (4.20)(2) plus Theorem (4.17): the periodic
modifications converge to `Φ` — here they are eventually *equal* to `Φ` in any fixed volume,
because a `C`-potential has finite range. -/
theorem mem_GP_of_mem_GZero (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)} (hμ : μ ∈ GZero E φ ν) :
    μ ∈ GP (cubeGibbsSpec E φ ν hφ hM) := by
  classical
  obtain ⟨μs, hμs, hcp⟩ := hμ
  choose ωs hωs using hμs
  have hδ : ∀ n : ℕ, IsProbabilityMeasure (Measure.dirac (ωs n)) := fun _ ↦ inferInstance
  obtain ⟨δs, hδs⟩ : ∃ δs : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E),
      ∀ n, (δs n : Measure ((Fin d → ℤ) → E)) = Measure.dirac (ωs n) :=
    ⟨fun n ↦ ⟨Measure.dirac (ωs n), hδ n⟩, fun _ ↦ rfl⟩
  refine mem_GP_of_mapClusterPt (l := atTop) (isQuasilocal_cubeGibbsSpec hφ hM)
    (γs := fun n ↦ wrappedCubeGibbsSpec E φ ν n hφ hM)
    (Λs := fun n ↦ periodicCube d n) (νs := δs)
    Potential.tendsto_latticeBox_atTop ?_ ?_
  · intro Λ f _
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [eventually_wrappedCubeGibbsSpec_apply_eq (ν := ν) hφ hM Λ] with n hn
    have : Specification.action (wrappedCubeGibbsSpec E φ ν n hφ hM) Λ f
        = Specification.action (cubeGibbsSpec E φ ν hφ hM) Λ f := by
      refine lp.ext (funext fun η ↦ ?_)
      rw [Specification.action_apply, Specification.action_apply, hn η]
    rw [this, dist_self]
  · have hbind : ∀ n : ℕ,
        (wrappedCubeGibbsSpec E φ ν n hφ hM).bindPM (periodicCube d n) (δs n) = μs n := by
      intro n
      refine Subtype.ext ?_
      change (δs n : Measure ((Fin d → ℤ) → E)).bind
        (wrappedCubeGibbsSpec E φ ν n hφ hM (periodicCube d n)) = (μs n : Measure _)
      rw [hδs n, Measure.dirac_bind
          ((wrappedCubeGibbsSpec E φ ν n hφ hM).measurable_kernel_toMeasure _),
        wrappedCubeGibbsSpec_periodicCube_eq_periodicGibbsField, ← hωs n]
    have hfun : (fun n : ℕ ↦ (WithSetwiseTopology.ofMeasure
        ((wrappedCubeGibbsSpec E φ ν n hφ hM).bindPM (periodicCube d n) (δs n)) :
        WithLocalConvergence (Fin d → ℤ) E))
        = fun n ↦ WithSetwiseTopology.ofMeasure (μs n) :=
      funext fun n ↦ by rw [hbind n]
    rw [hfun]
    exact hcp


/-- **Georgii, §18.1: every Gibbs measure for a `C`-potential is quasi-Gibbsian.**  The
Gibbsian specification of a `C`-potential is a `λ`-specification whose densities are Boltzmann
factors, hence positive, so Georgii's deduction from Theorem (7.7)(b) and Remark (1.28)(2)
applies. -/
theorem isQuasiGibbsian_of_isGibbsMeasure_cubeGibbsSpec (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) {μ : Measure ((Fin d → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : (cubeGibbsSpec E φ ν hφ hM).IsGibbsMeasure μ) : IsQuasiGibbsian μ := by
  have := isPotential_cubePotential (E := E) (φ := φ) hφ
  exact isQuasiGibbsian_of_isGibbsMeasure_lambdaSpecification ν
    (Potential.isPremodifier_boltzmannFactor (Φ := cubePotential E φ) 1)
    (isSigmaFiniteLambdaAdmissible_cubePotential hφ hM.choose_spec)
    (fun Λ η ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne') hμ

/-- Every element of `𝒢₀(Φ)` is quasi-Gibbsian: this is the hypothesis of Georgii's
Lemma (18.16). -/
theorem isQuasiGibbsian_of_mem_GZero (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)} (hμ : μ ∈ GZero E φ ν) :
    IsQuasiGibbsian (μ : Measure ((Fin d → ℤ) → E)) :=
  isQuasiGibbsian_of_isGibbsMeasure_cubeGibbsSpec hφ hM (mem_GP_of_mem_GZero hφ hM hμ)

end GibbsSpec

/-! ### Georgii Proposition (18.12): `𝒢₀(Φ) ≠ ∅` -/

section Existence

variable {d : ℕ} {E : Type*} [MeasurableSpace E] {φ : ((Fin d → Fin 2) → E) → ℝ}
  {ν : Measure E} [IsProbabilityMeasure ν]

variable (E d) in
/-- Georgii's `K^C`: the `r`-symmetric pattern "every spin of the elementary cube lies in
`K`". -/
def cubePi (K : Set E) : Set ((Fin d → Fin 2) → E) := {ζ | ∀ k, ζ k ∈ K}

variable {K : Set E}

omit [MeasurableSpace E] in
@[simp] lemma mem_cubePi {ζ : (Fin d → Fin 2) → E} : ζ ∈ cubePi d E K ↔ ∀ k, ζ k ∈ K := Iff.rfl

lemma measurableSet_cubePi (hK : MeasurableSet K) : MeasurableSet (cubePi d E K) := by
  have hEq : cubePi d E K = ⋂ k : Fin d → Fin 2, (fun f : (Fin d → Fin 2) → E ↦ f k) ⁻¹' K := by
    ext ζ; simp [cubePi]
  rw [hEq]
  exact MeasurableSet.iInter fun k ↦ (measurable_pi_apply k) hK

lemma isRSymmetric_cubePi : IsRSymmetric E (cubePi d E K) := by
  intro k
  ext ζ
  simp only [Set.mem_preimage, mem_cubePi, cubeRefl_apply]
  exact ⟨fun h c ↦ by simpa [cubeSiteRefl_cubeSiteRefl] using h (cubeSiteRefl k c),
    fun h c ↦ h _⟩

/-- If the elementary cube at `i` shows the pattern `K^C`, then in particular `ω_i ∈ K`. -/
lemma mem_of_mem_latticePattern_cubePi {ω : (Fin d → ℤ) → E} {i : Fin d → ℤ}
    (h : i ∈ latticePattern E (cubePi d E K) ω) : ω i ∈ K := by
  have := (mem_latticePattern_of_isRSymmetric isRSymmetric_cubePi ω i).1 h 0
  simpa using this

/-- **The weight of the pattern `K^C` is small when `Φ_C` is large off `K^C`.** -/
lemma patternWeight_le_of_forall_le {G : Set ((Fin d → Fin 2) → E)}
    (hG : MeasurableSet G) {c : ℝ} (hc : ∀ ζ ∈ Gᶜ, c ≤ φ ζ) :
    patternWeight φ ν G
      ≤ ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - c)) * groundStateCost φ ν := by
  have hp : (0 : ℝ) < (2 ^ d : ℝ)⁻¹ := inv_pos.2 (pow_pos two_pos d)
  by_cases h0 : cubeMeasure d ν Gᶜ = 0
  · rw [patternWeight, h0, ENNReal.zero_rpow_of_pos hp, mul_zero, zero_mul]
    exact zero_le
  · have hne : NeZero ((cubeMeasure d ν).restrict Gᶜ) := by
      refine ⟨fun hz ↦ h0 ?_⟩
      rw [← Measure.restrict_apply_univ, hz, Measure.coe_zero, Pi.zero_apply]
    have hcle : c ≤ energyOutside φ ν G :=
      le_essInf_of_ae_le _ (ae_restrict_of_forall_mem hG.compl hc) (isCoboundedUnder_ge_ae φ)
    rw [patternWeight]
    calc ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - energyOutside φ ν G))
          * cubeMeasure d ν Gᶜ ^ ((2 ^ d : ℝ)⁻¹) * groundStateCost φ ν
        ≤ ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - c)) * 1 * groundStateCost φ ν :=
          mul_le_mul' (mul_le_mul'
            (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith)))
            (ENNReal.rpow_le_one prob_le_one hp.le)) le_rfl
      _ = _ := by rw [mul_one]

variable (φ ν) in
/-- **Georgii, condition (iv) of Definition (17.18).**  Either `‖Φ_C‖ < ∞` — then `K ℓ = E`
will do, `isCubeConfining_univ` — or there is a sequence `(K_ℓ)` in `ℰ` such that `Φ_C` is
bounded on each `K_ℓ^C` and `inf_{ω ∉ K_ℓ^C} Φ_C → ∞` as `ℓ → ∞`.  The positivity
`λ(K_ℓ) > 0` is hypothesis (i) of Georgii's Corollary (4.13); Georgii's `K_ℓ ↑ E` gives it
after discarding finitely many `ℓ`, which changes nothing below. -/
structure IsCubeConfining (K : ℕ → Set E) : Prop where
  /-- The `K_ℓ` are measurable. -/
  measurableSet : ∀ ℓ, MeasurableSet (K ℓ)
  /-- Georgii (4.13)(i). -/
  measure_pos : ∀ ℓ, 0 < ν (K ℓ)
  /-- `Φ_C` is bounded on each `K_ℓ^C`. -/
  bddOn : ∀ ℓ, ∃ c : ℝ, ∀ ζ ∈ cubePi d E (K ℓ), |φ ζ| ≤ c
  /-- `inf_{ω ∉ K_ℓ^C} Φ_C → ∞`. -/
  tendsto_atTop : ∀ c : ℝ, ∃ ℓ₀ : ℕ, ∀ ℓ, ℓ₀ ≤ ℓ → ∀ ζ ∈ (cubePi d E (K ℓ))ᶜ, c ≤ φ ζ

/-- **Condition (iv) of (17.18), first alternative**: a bounded cube interaction is confining
with `K_ℓ = E`. -/
lemma isCubeConfining_univ (hb : ∃ c : ℝ, ∀ ζ, |φ ζ| ≤ c) :
    IsCubeConfining φ ν fun _ : ℕ ↦ (Set.univ : Set E) where
  measurableSet _ := MeasurableSet.univ
  measure_pos _ := by simp
  bddOn _ := hb.imp fun _ hc ↦ fun ζ _ ↦ hc ζ
  tendsto_atTop _ := ⟨0, fun _ _ ζ hζ ↦ absurd (fun k ↦ Set.mem_univ (ζ k)) hζ⟩

/-- **Georgii, proof of (18.12)**: `t(K_ℓ^C, Φ) → 0` as `ℓ → ∞`. -/
theorem tendsto_patternWeight_cubePi {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    {K : ℕ → Set E} (hK : IsCubeConfining φ ν K) :
    Tendsto (fun ℓ ↦ patternWeight φ ν (cubePi d E (K ℓ))) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Eventually.of_forall fun _ ↦ le_top
  have hg0 : groundStateCost φ ν ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_groundStateCost)).ne'
  have hgtop : groundStateCost φ ν ≠ ⊤ := (groundStateCost_lt_top hM).ne
  set r : ℝ≥0∞ := ε / groundStateCost φ ν with hr
  have hr0 : r ≠ 0 := by
    rw [hr]
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hε.ne', hgtop⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - c)) ≤ r := by
    rcases eq_or_ne r ⊤ with hrt | hrt
    · exact ⟨0, by rw [hrt]; exact le_top⟩
    · refine ⟨localGroundEnergy φ ν - Real.log r.toReal, ?_⟩
      have hrpos : 0 < r.toReal := ENNReal.toReal_pos hr0 hrt
      rw [sub_sub_cancel, Real.exp_log hrpos]
      exact le_of_eq (ENNReal.ofReal_toReal hrt)
  obtain ⟨ℓ₀, hℓ₀⟩ := hK.tendsto_atTop c
  filter_upwards [eventually_ge_atTop ℓ₀] with ℓ hℓ
  calc patternWeight φ ν (cubePi d E (K ℓ))
      ≤ ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - c)) * groundStateCost φ ν :=
        patternWeight_le_of_forall_le (measurableSet_cubePi (hK.measurableSet ℓ)) (hℓ₀ ℓ hℓ)
    _ ≤ r * groundStateCost φ ν := mul_le_mul' hc le_rfl
    _ = ε := ENNReal.div_mul_cancel hg0 hgtop

section Twelve

variable {φ' : ((Fin (d + 1) → Fin 2) → E) → ℝ}

variable (φ') in
/-- The sites read by the Hamiltonian of the `C`-potential in a volume `Λ`: Georgii's `Δ` in
hypothesis (iii) of Corollary (4.13). -/
def hamSupport (Λ : Finset (Fin (d + 1) → ℤ)) : Finset (Fin (d + 1) → ℤ) :=
  Λ ∪ (Potential.interactingSupport (Φ := cubePotential E φ') Λ).biUnion id

lemma subset_hamSupport (Λ : Finset (Fin (d + 1) → ℤ)) : Λ ⊆ hamSupport φ' Λ :=
  Finset.subset_union_left

/-- **Hypothesis (iii) of Georgii's Corollary (4.13) for a `C`-potential.**  On configurations
whose spins in `hamSupport φ Λ` lie in `K`, the Hamiltonian in `Λ` is bounded by the bound for
`Φ_C` on `K^C` times the number of interacting cubes. -/
lemma abs_interactingHamiltonian_cubePotential_le {K : Set E} {c : ℝ}
    (hc : ∀ ζ ∈ cubePi (d + 1) E K, |φ' ζ| ≤ c) (Λ : Finset (Fin (d + 1) → ℤ))
    {ω : (Fin (d + 1) → ℤ) → E} (hω : ∀ i ∈ hamSupport φ' Λ, ω i ∈ K) :
    |Potential.interactingHamiltonian (Φ := cubePotential E φ') Λ ω|
      ≤ (Potential.interactingSupport (Φ := cubePotential E φ') Λ).card * c := by
  classical
  rw [Potential.interactingHamiltonian]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ A ∈ Potential.interactingSupport (Φ := cubePotential E φ') Λ,
        |cubePotential E φ' A ω|
      ≤ ∑ _A ∈ Potential.interactingSupport (Φ := cubePotential E φ') Λ, c := by
        refine Finset.sum_le_sum fun A hA ↦ ?_
        obtain ⟨i, rfl⟩ := cubePotential_ne_zero (Potential.mem_interactingSupport.1 hA).2
        rw [cubePotential_latticeCube]
        refine hc _ fun k ↦ hω _ (Finset.mem_union_right _
          (Finset.mem_biUnion.2 ⟨latticeCube i, hA, mem_latticeCube_iff.2 ⟨k, rfl⟩⟩))
    _ = (Potential.interactingSupport (Φ := cubePotential E φ') Λ).card * c := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Georgii, Proposition (18.12).**  For a standard Borel state space and a `C`-potential —
measurability of `Φ_C`, condition (iii) of (17.18), and condition (iv) in the form of a lower
bound together with a confining sequence `(K_ℓ)` — the set `𝒢₀(Φ)` of limits of Gibbs
distributions with periodic boundary condition is nonempty; a fortiori so is `𝒢_Θ(Φ)`
(`mem_GP_of_mem_GZero`, `measurePreserving_shift_of_mem_GZero`).

Georgii's proof: Corollary (4.13) applied to the periodic modifications `Φ̃^{Λ(N)}`, with
hypothesis (ii) supplied by the proof of Lemma (18.10) — `t(K_ℓ^C, Φ) → 0` — and hypothesis
(iii) by the boundedness of `Φ_C` on the cubes of `K_ℓ`; then Proposition (4.9). -/
theorem GZero_nonempty [StandardBorelSpace E] (hφ : Measurable φ') {M : ℝ}
    (hM : ∀ ζ, M ≤ φ' ζ) (hφk : ∀ (k : Fin (d + 1)) ζ, φ' (cubeRefl E k ζ) = φ' ζ)
    {K : ℕ → Set E} (hK : IsCubeConfining φ' ν K) (ω : (Fin (d + 1) → ℤ) → E) :
    (GZero E φ' ν).Nonempty := by
  classical
  have hMex : ∃ M : ℝ, ∀ ζ, M ≤ φ' ζ := ⟨M, hM⟩
  have hpot : ∀ n : ℕ, Potential.IsPotential (wrappedCubePotential E φ' n) :=
    fun n ↦ isPotential_wrappedCubePotential hφ
  obtain ⟨δ, hδ⟩ : ∃ δ : ProbabilityMeasure ((Fin (d + 1) → ℤ) → E),
      (δ : Measure ((Fin (d + 1) → ℤ) → E)) = Measure.dirac ω :=
    ⟨⟨Measure.dirac ω, inferInstance⟩, rfl⟩
  set μs : ℕ → ProbabilityMeasure ((Fin (d + 1) → ℤ) → E) :=
    fun n ↦ (wrappedCubeGibbsSpec E φ' ν n hφ hMex).bindPM (periodicCube (d + 1) n) δ with hμsdef
  have hμval : ∀ n, (μs n : Measure ((Fin (d + 1) → ℤ) → E))
      = periodicGibbsField E φ' ν n ω := by
    intro n
    change (δ : Measure ((Fin (d + 1) → ℤ) → E)).bind
      (wrappedCubeGibbsSpec E φ' ν n hφ hMex (periodicCube (d + 1) n)) = _
    rw [hδ, Measure.dirac_bind
        ((wrappedCubeGibbsSpec E φ' ν n hφ hMex).measurable_kernel_toMeasure _),
      wrappedCubeGibbsSpec_periodicCube_eq_periodicGibbsField]
  have hadm : ∀ n : ℕ, Specification.IsPremodifierAdmissible (S := Fin (d + 1) → ℤ) (E := E) ν
      ((wrappedCubePotential E φ' n).boltzmannFactor 1) := fun n ↦
    (Specification.isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible ν _).2
      (isSigmaFiniteLambdaAdmissible_wrappedCubePotential hφ hMex.choose_spec n)
  have hle : LocallyEquicontinuous atTop μs := by
    refine Potential.locallyEquicontinuous_of_confinement_hamiltonian
      (fun n ↦ wrappedCubePotential E φ' n) ν 1 hadm (fun n ↦ periodicCube (d + 1) n)
      Potential.tendsto_latticeBox_atTop (fun _ ↦ δ) μs ?_ K hK.measurableSet hK.measure_pos
      ?_ ?_
    · intro n
      have hspec : wrappedCubeGibbsSpec E φ' ν n hφ hMex
          = (Specification.isssd (S := Fin (d + 1) → ℤ) (E := E) ν).modification
            (Specification.premodifierNorm ν
              ((wrappedCubePotential E φ' n).boltzmannFactor 1))
            (Specification.IsPremodifier.isModifier_premodifierNorm ν
              (Potential.isPremodifier_boltzmannFactor
                (Φ := wrappedCubePotential E φ' n) 1) (hadm n)) :=
        Specification.lambdaSpecification_eq_modification_isssd ν
          (Potential.isPremodifier_boltzmannFactor (Φ := wrappedCubePotential E φ' n) 1)
          (isSigmaFiniteLambdaAdmissible_wrappedCubePotential hφ hMex.choose_spec n)
      change (wrappedCubeGibbsSpec E φ' ν n hφ hMex).bindPM (periodicCube (d + 1) n) δ = _
      rw [hspec]
    · -- Georgii's hypothesis (ii), from Lemma (18.10) and `t(K_ℓ^C, Φ) → 0`
      intro i
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_patternWeight_cubePi hM hK)
        (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall fun ℓ ↦ ?_)
      refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [Potential.tendsto_latticeBox_atTop.eventually
        (eventually_ge_atTop (({i} : Finset (Fin (d + 1) → ℤ)) ∪ cubeSupport {i}))] with n hn
      have hsub : {ω' : (Fin (d + 1) → ℤ) → E | ω' i ∉ K ℓ}
          ⊆ {ω' | ∀ j ∈ ({i} : Finset (Fin (d + 1) → ℤ)),
              j ∉ latticePattern E (cubePi (d + 1) E (K ℓ)) ω'} := by
        intro ω' hω' j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact fun hc ↦ hω' (mem_of_mem_latticePattern_cubePi hc)
      calc (μs n : Measure ((Fin (d + 1) → ℤ) → E)) {ω' | ω' i ∉ K ℓ}
          ≤ (μs n : Measure ((Fin (d + 1) → ℤ) → E))
            {ω' | ∀ j ∈ ({i} : Finset (Fin (d + 1) → ℤ)),
              j ∉ latticePattern E (cubePi (d + 1) E (K ℓ)) ω'} := measure_mono hsub
        _ ≤ patternWeight φ' ν (cubePi (d + 1) E (K ℓ)) := by
            rw [hμval n]
            have hb : periodicGibbsField E φ' ν n ω
                {ω' | ∀ j ∈ ({i} : Finset (Fin (d + 1) → ℤ)),
                  j ∉ latticePattern E (cubePi (d + 1) E (K ℓ)) ω'}
                ≤ patternWeight φ' ν (cubePi (d + 1) E (K ℓ)) ^
                  ({i} : Finset (Fin (d + 1) → ℤ)).card :=
              periodicGibbsField_forall_notMem_latticePattern_le_patternWeight
                hφ hM hφk (measurableSet_cubePi (hK.measurableSet ℓ)) isRSymmetric_cubePi hn ω
            rwa [Finset.card_singleton, pow_one] at hb
    · -- Georgii's hypothesis (iii)
      intro Λ
      refine ⟨hamSupport φ' Λ, subset_hamSupport Λ, fun ℓ ↦ ?_⟩
      obtain ⟨c, hc⟩ := hK.bddOn ℓ
      refine ⟨(Potential.interactingSupport (Φ := cubePotential E φ') Λ).card * c, ?_⟩
      obtain ⟨m, hm⟩ := (Filter.tendsto_atTop_atTop.1
        (Potential.tendsto_latticeBox_atTop (d := d + 1))) Λ
      filter_upwards [eventually_ge_atTop (m + 1)] with n hn ω' hω'
      rw [Potential.hamiltonian_eq_interactingHamiltonian,
        interactingHamiltonian_congr (Φ := wrappedCubePotential E φ' n)
          (Ψ := cubePotential E φ') (Λ := Λ)
          (fun A hA ↦ wrappedCubePotential_eq_cubePotential hn
            (hA.mono (Set.inter_subset_inter_right _ (by exact_mod_cast hm m le_rfl)))) ω']
      exact abs_interactingHamiltonian_cubePotential_le hc Λ hω'
  obtain ⟨m, hm⟩ := exists_mapClusterPt_of_locallyEquicontinuous
    (μs := fun n ↦ (WithSetwiseTopology.ofMeasure (μs n) : WithLocalConvergence _ E)) hle
  exact ⟨m.toMeasure, μs, fun n ↦ ⟨ω, hμval n⟩, hm⟩

/-- **Georgii, Proposition (18.12), first alternative of (17.18)(iv).**  A bounded cube
interaction over a standard Borel state space has `𝒢₀(Φ) ≠ ∅`. -/
theorem GZero_nonempty_of_bounded [StandardBorelSpace E] (hφ : Measurable φ') {M : ℝ}
    (hM : ∀ ζ, M ≤ φ' ζ) (hφk : ∀ (k : Fin (d + 1)) ζ, φ' (cubeRefl E k ζ) = φ' ζ)
    (hb : ∃ c : ℝ, ∀ ζ, |φ' ζ| ≤ c) (ω : (Fin (d + 1) → ℤ) → E) : (GZero E φ' ν).Nonempty :=
  GZero_nonempty hφ hM hφk (isCubeConfining_univ hb) ω

/-- **Georgii, Proposition (18.12): `𝒢₀(Φ) ≠ ∅` and thus `𝒢_Θ(Φ) ≠ ∅`.**  There is a
shift-invariant Gibbs measure for every `C`-potential over a standard Borel state space. -/
theorem exists_mem_GP_and_measurePreserving_shift [StandardBorelSpace E] (hφ : Measurable φ')
    {M : ℝ} (hM : ∀ ζ, M ≤ φ' ζ) (hφk : ∀ (k : Fin (d + 1)) ζ, φ' (cubeRefl E k ζ) = φ' ζ)
    {K : ℕ → Set E} (hK : IsCubeConfining φ' ν K) (ω : (Fin (d + 1) → ℤ) → E) :
    ∃ μ ∈ GP (cubeGibbsSpec E φ' ν hφ ⟨M, hM⟩),
      ∀ a : Fin (d + 1) → ℤ,
        MeasurePreserving (shift E a).toFun (μ : Measure ((Fin (d + 1) → ℤ) → E)) μ := by
  obtain ⟨μ, hμ⟩ := GZero_nonempty hφ hM hφk hK ω
  exact ⟨μ, mem_GP_of_mem_GZero hφ ⟨M, hM⟩ hμ,
    fun a ↦ measurePreserving_shift_of_mem_GZero hφ hμ a⟩

end Twelve

end Existence

end MeasureTheory.GibbsMeasure
