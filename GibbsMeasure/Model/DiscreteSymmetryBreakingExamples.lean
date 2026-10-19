/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.DiscreteSymmetryBreaking
public import GibbsMeasure.Model.HeisenbergOceans
public import GibbsMeasure.Model.Ising

/-!
# Georgii §18.3: the toolkit for the examples of discrete symmetry breaking

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.  Each model of that section is an
instance of **Theorem (18.25)**
(`MeasureTheory.GibbsMeasure.eventually_exists_gibbsMeasure_family` of
`GibbsMeasure/Model/DiscreteSymmetryBreaking.lean`): one exhibits a `C`-potential `Φ`, computes
its local ground state energy `m_Φ` (18.1) and its local `ε`-ground states `G_ε(Φ)` (18.2),
splits the latter into a `Φ`-symmetric `P`-stable partition (18.23), and reads off the `N`
mutually singular Gibbs measures.  As Georgii does, `d = 2` throughout §18.3 except in the
last example, so that the plane `P` of (18.5) is the whole lattice and every face of `C` is a
`P`-face.

This file collects what all the examples share; the models themselves are in
`GibbsMeasure/Model/IsingOceans.lean` and its companions.

## Main results

* `cubeGraph_adj_iff_add_single` — adjacency in the cube `C = {0,1}^d` is translation by a basis
  corner, `c' = c + e_k`; hence `cubeGraph_adj_cubeIsoCorner`: **every cube isometry induces an
  automorphism of the cube graph**, because its corner permutation is `c ↦ c ∘ π + offset` and
  the offset cancels in characteristic `2`.
* `cubeBondSum_comp`, `cubeBondSum_onCube`, `cubeBondSum_onCube_of_spin_refl` — consequently a
  bond sum `∑_{{i,j} ⊆ C, |i-j|=1} ψ(σ_i, σ_j)` (`cubeBondSum` of
  `GibbsMeasure/Model/HeisenbergOceans.lean`) is invariant under every cube transformation
  `τ ∈ T_{C,λ}` whose spins leave `ψ` invariant along the edges; likewise `cubeSiteSum_onCube`
  for the site sum `∑_{i ∈ C} v(σ_i)` of an external field and `sqDiagSum_onCube_of_spin_refl`
  for the next-nearest-neighbour term `∑_{{i,j} ⊆ C, |i-j|=√2}` of the plane.  These discharge
  the hypothesis `Φ_C ∘ τ = Φ_C` of `CubeTransformation.IsSymmetry.of_apply_onCube` for
  Georgii's generators `r_0` (`planeRot`), `r_1, …, r_d` (`refl k`), the two diagonal
  reflections `sqTranspose`, `sqAntiTranspose` and the pure spin transformations (18.21).
* `cubeBondSum_eq_iff_forall_adj` — **a bond sum attains its trivial lower bound exactly when
  every bond does**, which with the connectedness of the cube identifies the local ground states
  of every nearest-neighbour interaction with a unique minimum on the diagonal (Potts, the
  isotropic Heisenberg model).
* `sum_univ_cubeCorners`, `cubeBondSum_two`, `sqOf`, `funext_sqCorner` — the four corners and the
  four edges of the unit square, in Georgii's notation `ω = (w z / u v)`: `u = ω_{(0,0)}`,
  `v = ω_{(1,0)}`, `w = ω_{(0,1)}`, `z = ω_{(1,1)}`, together with the action of the dihedral
  group of the square on those four spins (`onCube_refl_zero_sqOf`, `onCube_refl_one_sqOf`,
  `onCube_planeRot_sqOf`, `onCube_sqTranspose_sqOf`, `onCube_sqAntiTranspose_sqOf`).
* `localGroundEnergy_eq`, `localGroundStates_eq_setOf_le` and
  `exists_pos_localGroundStates_subset` — for a **finite** state space whose a priori measure
  charges every point, the essential infimum (18.1) is the plain minimum, `G_ε(Φ)` is
  `{Φ_C ≤ min Φ_C + ε}`, and for small `ε` it is the set of *exact* local ground states.  This
  is how "`Φ_C` only takes the values `-4, 0, 4`, therefore `G_ε(Φ)` consists of the local
  ground states when `0 < ε < 4`" becomes a proof.  `localGroundEnergy_eq_of_isOpenPosMeasure` is
  the continuous counterpart, and `isCubeConfining_univ_of_finite` makes condition (17.18)(iv)
  automatic over a finite state space.  (Intended home:
  `GibbsMeasure/Specification/LocalGroundStates.lean`.)
* `pairwise_disjoint_faceRestrict_singleton`, `isPhiSymmetric_of_ne`,
  `isRSymmetric_singleton_const`, `CubeTransformation.IsSymmetry.const_mul` — the two halves of
  Definition (18.23) in the form in which the examples verify them: a finite check on the four
  faces of `C`, and a symmetry for each *off-diagonal* pair.  (Intended home:
  `GibbsMeasure/Specification/PeriodicGibbsSymmetry.lean`.)
* `exists_gibbsMeasure_family_shift_of_crossingBound_lt_one` and
  `eventually_exists_gibbsMeasure_family_shift` — **Theorem (18.25) with the last sentence of
  (iii)**, `θ_{e_k}(μ_n) = μ_m` when `r_k G_m = G_n`, which
  `exists_gibbsMeasure_family_of_crossingBound_lt_one` of
  `GibbsMeasure/Model/DiscreteSymmetryBreaking.lean` proves but does not expose; Georgii needs
  it in 18.3.2.  `eventually_le_encard_extremePoints` is the last statement of (18.25) for an
  `r`-symmetric partition, `|ex 𝒢_Θ(βΦ)| ≥ N`, and `eventually_le_encard_extremePoints_G` the
  unrestricted `|ex 𝒢(βΦ)| ≥ N` through Corollary (7.29), which is what Georgii uses in
  18.3.3(c) where the partition is not `r`-symmetric.  (Intended home:
  `GibbsMeasure/Model/DiscreteSymmetryBreaking.lean`.)

## The examples

`GibbsMeasure/Model/IsingOceans.lean` (18.3.1, 18.3.2),
`GibbsMeasure/Model/GertsikDobrushin.lean` (18.3.3, all four of Georgii's parameter regions),
`GibbsMeasure/Model/PottsOceans.lean` (18.3.5, and the module doc there explains why 18.3.4 is
not formalised), `GibbsMeasure/Model/AnisotropicHeisenbergOceans.lean` (18.3.6).  Georgii's
18.3.7 (the anisotropic antiferromagnet in a field and the plane rotor (18.35)), 18.3.8
(Shlosman's plane rotor), 18.3.9 (unbounded spins with a double-well self-potential) and 18.3.10
(Slawny's `□`-model, with (18.40)–(18.41)) are not formalised.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {d : ℕ}

/-! ### Adjacency in the cube `C = {0,1}^d` -/

section CubeCombinatorics

variable {E : Type*}

/-- **Adjacency in the cube is translation by a basis corner**: `c` and `c'` are adjacent
exactly when `c' + c = e_k` for some direction `k` (the corners form the group `(ℤ/2)^d`, so
`c' - c = c' + c`). -/
lemma cubeGraph_adj_iff_add_single {c c' : Fin d → Fin 2} :
    (cubeGraph d).Adj c c' ↔ ∃ k, c' + c = Pi.single k 1 := by
  rw [cubeGraph_adj]
  refine exists_congr fun k ↦ ?_
  rw [cubeSiteRefl_eq_add_single]
  constructor
  · rintro rfl
    rw [add_right_comm, corner_add_self, zero_add]
  · intro h
    rw [← h, add_left_comm, corner_add_self, add_zero]

/-- The corner permutation of a cube isometry is translation-equivariant up to the coordinate
permutation: `s(c') + s(c) = (c' + c) ∘ π`, the offset cancelling in characteristic `2`. -/
lemma cubeIsoCorner_add_cubeIsoCorner (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (c c' : Fin d → Fin 2) :
    cubeIsoCorner π ε c' + cubeIsoCorner π ε c = cornerPerm π (c' + c) := by
  rw [cubeIsoCorner_apply, cubeIsoCorner_apply, map_add]
  funext l
  have h := congrFun (corner_add_self (cubeIsoOffset ε)) l
  simp only [Pi.add_apply, Pi.zero_apply] at h
  simp only [Pi.add_apply, cornerPerm_apply]
  rw [add_add_add_comm, h, add_zero]

/-- **A cube isometry induces an automorphism of the cube graph.**  This is what makes Georgii's
rotation `r_0` and reflections `r_k` symmetries of every nearest-neighbour cube interaction. -/
lemma cubeGraph_adj_cubeIsoCorner (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (c c' : Fin d → Fin 2) :
    (cubeGraph d).Adj (cubeIsoCorner π ε c) (cubeIsoCorner π ε c') ↔ (cubeGraph d).Adj c c' := by
  rw [cubeGraph_adj_iff_add_single, cubeGraph_adj_iff_add_single,
    cubeIsoCorner_add_cubeIsoCorner]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨π k, ?_⟩
    funext l
    have h := congrFun hk (π.symm l)
    simp only [cornerPerm_apply, Equiv.apply_symm_apply] at h
    rw [h, Pi.single_apply, Pi.single_apply]
    simp only [Equiv.symm_apply_eq]
  · rintro ⟨k, hk⟩
    refine ⟨π.symm k, ?_⟩
    funext l
    rw [cornerPerm_apply, hk, Pi.single_apply, Pi.single_apply]
    simp only [Equiv.eq_symm_apply]

/-! ### Site sums, and bond sums under a graph automorphism -/

variable (d) in
/-- **Georgii's site term** `∑_{i ∈ C} v(σ_i)` of a cube interaction: the external field
`-h ∑_{i ∈ C} σ_i` of (18.28), the particle number of (18.30) and the self-potential
`∑_{i ∈ C} v(σ_i)` of (18.38). -/
def cubeSiteSum (v : E → ℝ) (ζ : (Fin d → Fin 2) → E) : ℝ := ∑ c, v (ζ c)

lemma cubeSiteSum_def (v : E → ℝ) (ζ : (Fin d → Fin 2) → E) :
    cubeSiteSum d v ζ = ∑ c, v (ζ c) := rfl

/-- **Condition (iii) of Georgii (17.18)** for a site sum: it is invariant under every reflection
`r_k` of the cube, for any `v`. -/
lemma cubeSiteSum_cubeRefl [MeasurableSpace E] (v : E → ℝ) (k : Fin d)
    (ζ : (Fin d → Fin 2) → E) : cubeSiteSum d v (cubeRefl E k ζ) = cubeSiteSum d v ζ :=
  Fintype.sum_equiv (cubeSiteRefl k) _ _ fun _ ↦ rfl

/-- The cube has `2^d` corners. -/
lemma sum_const_cubeCorners (m : ℝ) : ∑ _c : Fin d → Fin 2, m = ((2 ^ d : ℕ) : ℝ) * m := by
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma cubeSiteSum_ge {v : E → ℝ} {m : ℝ} {ζ : (Fin d → Fin 2) → E} (hm : ∀ c, m ≤ v (ζ c)) :
    ((2 ^ d : ℕ) : ℝ) * m ≤ cubeSiteSum d v ζ :=
  (sum_const_cubeCorners m).symm.trans_le (Finset.sum_le_sum fun c _ ↦ hm c)

lemma cubeSiteSum_le {v : E → ℝ} {M : ℝ} {ζ : (Fin d → Fin 2) → E} (hM : ∀ c, v (ζ c) ≤ M) :
    cubeSiteSum d v ζ ≤ ((2 ^ d : ℕ) : ℝ) * M :=
  (Finset.sum_le_sum fun c _ ↦ hM c).trans (sum_const_cubeCorners M).le

/-- **A bond sum is invariant under a graph automorphism of the cube.** -/
lemma cubeBondSum_comp_equiv {ψ : E → E → ℝ} (e : (Fin d → Fin 2) ≃ (Fin d → Fin 2))
    (he : ∀ c c', (cubeGraph d).Adj (e c) (e c') ↔ (cubeGraph d).Adj c c')
    (ζ : (Fin d → Fin 2) → E) : cubeBondSum d ψ (fun c ↦ ζ (e c)) = cubeBondSum d ψ ζ := by
  unfold cubeBondSum
  congr 1
  refine Fintype.sum_equiv e _ _ fun c ↦ ?_
  refine Finset.sum_equiv e (fun c' ↦ ?_) fun _ _ ↦ rfl
  simp only [SimpleGraph.mem_neighborFinset]
  exact (he c c').symm

/-- **A bond sum under a cube transformation.**  Composing with a graph automorphism `e` of the
cube and per-corner spin maps `t` which leave the bond interaction invariant along every edge
leaves the bond sum unchanged. -/
lemma cubeBondSum_comp {ψ : E → E → ℝ} (e : (Fin d → Fin 2) ≃ (Fin d → Fin 2))
    (he : ∀ c c', (cubeGraph d).Adj (e c) (e c') ↔ (cubeGraph d).Adj c c')
    (t : (Fin d → Fin 2) → E → E)
    (ht : ∀ c c', (cubeGraph d).Adj c c' → ∀ x y, ψ (t c x) (t c' y) = ψ x y)
    (ζ : (Fin d → Fin 2) → E) :
    cubeBondSum d ψ (fun c ↦ t c (ζ (e c))) = cubeBondSum d ψ ζ := by
  rw [← cubeBondSum_comp_equiv (ψ := ψ) e he ζ]
  unfold cubeBondSum
  congr 1
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun c' hc' ↦ ?_
  exact ht c c' ((SimpleGraph.mem_neighborFinset _ _ _).1 hc') _ _

/-- **A bond sum attains its trivial lower bound exactly when every bond does.**  With the
connectedness of the cube (`cubeGraph_forall_eq_of_adj`) this identifies the local ground states
of every nearest-neighbour cube interaction whose bond interaction has a unique minimum on the
diagonal. -/
lemma cubeBondSum_eq_iff_forall_adj {ψ : E → E → ℝ} {m : ℝ} (hm : ∀ x y, m ≤ ψ x y)
    (ζ : (Fin d → Fin 2) → E) :
    cubeBondSum d ψ ζ = (2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d * m) ↔
      ∀ c c', (cubeGraph d).Adj c c' → ψ (ζ c) (ζ c') = m := by
  rw [cubeBondSum_def, ← sum_neighborFinset_cubeGraph_const m]
  constructor
  · intro heq c c' hcc'
    have hmul : ∑ a : Fin d → Fin 2, ∑ b ∈ (cubeGraph d).neighborFinset a, ψ (ζ a) (ζ b)
        = ∑ _a : Fin d → Fin 2, ∑ _b ∈ (cubeGraph d).neighborFinset _a, m := by
      have h2 : (2 : ℝ)⁻¹ ≠ 0 := by norm_num
      exact mul_left_cancel₀ h2 heq
    have houter := (Finset.sum_eq_sum_iff_of_le fun a _ ↦
      Finset.sum_le_sum fun b _ ↦ hm (ζ a) (ζ b)).1 hmul.symm c (Finset.mem_univ c)
    have := (Finset.sum_eq_sum_iff_of_le fun b _ ↦ hm (ζ c) (ζ b)).1 houter c'
      ((SimpleGraph.mem_neighborFinset _ _ _).2 hcc')
    exact this.symm
  · intro h
    congr 1
    exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun c' hc' ↦
      h c c' ((SimpleGraph.mem_neighborFinset _ _ _).1 hc')

lemma continuous_cubeBondSum [TopologicalSpace E] {ψ : E → E → ℝ}
    (hψ : Continuous (Function.uncurry ψ)) : Continuous (cubeBondSum d ψ) := by
  refine continuous_const.mul (continuous_finset_sum _ fun c _ ↦
    continuous_finset_sum _ fun c' _ ↦ ?_)
  have h : Continuous fun ζ : (Fin d → Fin 2) → E ↦ (ζ c, ζ c') :=
    (continuous_apply c).prodMk (continuous_apply c')
  exact hψ.comp h

/-! ### The four corners and the four edges of the unit square -/

/-- The corner `(a, b)` of the unit square, in Georgii's notation `ω = (w z / u v)` with
`u = ω_{(0,0)}`, `v = ω_{(1,0)}`, `w = ω_{(0,1)}`, `z = ω_{(1,1)}`. -/
abbrev sqCorner (a b : Fin 2) : Fin 2 → Fin 2 := ![a, b]

/-- The four corners of the unit square. -/
lemma sum_univ_cubeCorners {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Fin 2) → M) :
    ∑ c, f c = f (sqCorner 0 0) + f (sqCorner 1 0) + f (sqCorner 0 1) + f (sqCorner 1 1) := by
  have h : ∀ a b : Fin 2, (piFinTwoEquiv fun _ : Fin 2 ↦ Fin 2).symm (a, b) = sqCorner a b := by
    intro a b
    funext l
    fin_cases l <;> rfl
  rw [← Equiv.sum_comp (piFinTwoEquiv fun _ : Fin 2 ↦ Fin 2).symm f, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, h]
  abel

/-- The unit square has four corners. -/
lemma sqCorner_surjective (c : Fin 2 → Fin 2) :
    c = sqCorner 0 0 ∨ c = sqCorner 1 0 ∨ c = sqCorner 0 1 ∨ c = sqCorner 1 1 := by
  rcases fin_two_eq_zero_or_one (c 0) with h0 | h0 <;>
    rcases fin_two_eq_zero_or_one (c 1) with h1 | h1
  · exact Or.inl (by funext l; fin_cases l <;> simpa using ‹_›)
  · exact Or.inr (Or.inr (Or.inl (by funext l; fin_cases l <;> simpa using ‹_›)))
  · exact Or.inr (Or.inl (by funext l; fin_cases l <;> simpa using ‹_›))
  · exact Or.inr (Or.inr (Or.inr (by funext l; fin_cases l <;> simpa using ‹_›)))

/-- Two configurations of the unit square which agree at the four corners are equal. -/
lemma funext_sqCorner {M : Type*} {f g : (Fin 2 → Fin 2) → M}
    (h00 : f (sqCorner 0 0) = g (sqCorner 0 0)) (h10 : f (sqCorner 1 0) = g (sqCorner 1 0))
    (h01 : f (sqCorner 0 1) = g (sqCorner 0 1)) (h11 : f (sqCorner 1 1) = g (sqCorner 1 1)) :
    f = g := by
  funext c
  rcases sqCorner_surjective c with rfl | rfl | rfl | rfl <;> assumption

lemma sum_add (c p : Fin d → Fin 2) : ∑ k, (c + p) k = ∑ k, c k + ∑ k, p k :=
  Finset.sum_add_distrib

/-- The corner sum changes by `1` under a reflection of the cube. -/
lemma sum_add_single (c : Fin d → Fin 2) (k : Fin d) :
    ∑ l, (c + (Pi.single k 1 : Fin d → Fin 2)) l = ∑ l, c l + 1 := by
  rw [sum_add]
  congr 1
  simp

lemma neighborFinset_cubeGraph_two (a b : Fin 2) :
    (cubeGraph 2).neighborFinset (sqCorner a b) = {sqCorner (a + 1) b, sqCorner a (b + 1)} := by
  ext c
  simp only [SimpleGraph.mem_neighborFinset, cubeGraph_adj, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left
      funext l; fin_cases l <;> simp [cubeSiteRefl_apply, fin_two_rev_eq_add_one]
    · right
      funext l; fin_cases l <;> simp [cubeSiteRefl_apply, fin_two_rev_eq_add_one]
  · rintro (rfl | rfl)
    · exact ⟨0, by funext l; fin_cases l <;> simp [cubeSiteRefl_apply, fin_two_rev_eq_add_one]⟩
    · exact ⟨1, by funext l; fin_cases l <;> simp [cubeSiteRefl_apply, fin_two_rev_eq_add_one]⟩

/-- **The bond sum of the unit square**: the four edges `{u, v}`, `{w, z}`, `{u, w}`, `{v, z}` of
Georgii's `ω = (w z / u v)`, for a symmetric bond interaction. -/
lemma cubeBondSum_two {ψ : E → E → ℝ} (hψ : ∀ x y, ψ x y = ψ y x)
    (ζ : (Fin 2 → Fin 2) → E) :
    cubeBondSum 2 ψ ζ =
      ψ (ζ (sqCorner 0 0)) (ζ (sqCorner 1 0)) + ψ (ζ (sqCorner 0 1)) (ζ (sqCorner 1 1))
        + ψ (ζ (sqCorner 0 0)) (ζ (sqCorner 0 1)) + ψ (ζ (sqCorner 1 0)) (ζ (sqCorner 1 1)) := by
  rw [cubeBondSum_def, sum_univ_cubeCorners]
  simp only [neighborFinset_cubeGraph_two]
  have h01 : (0 : Fin 2) + 1 = 1 := rfl
  have h10 : (1 : Fin 2) + 1 = 0 := rfl
  rw [Finset.sum_insert (by simp [funext_iff, Fin.forall_fin_two]),
    Finset.sum_insert (by simp [funext_iff, Fin.forall_fin_two]),
    Finset.sum_insert (by simp [funext_iff, Fin.forall_fin_two]),
    Finset.sum_insert (by simp [funext_iff, Fin.forall_fin_two])]
  simp only [Finset.sum_singleton, h01, h10]
  rw [hψ (ζ (sqCorner 1 0)) (ζ (sqCorner 0 0)), hψ (ζ (sqCorner 0 1)) (ζ (sqCorner 0 0)),
    hψ (ζ (sqCorner 1 1)) (ζ (sqCorner 0 1)), hψ (ζ (sqCorner 1 1)) (ζ (sqCorner 1 0))]
  ring


/-- **A configuration of the unit square from its four corner spins**, in Georgii's notation
`ω = (w z / u v)`: `u = ω_{(0,0)}`, `v = ω_{(1,0)}`, `w = ω_{(0,1)}`, `z = ω_{(1,1)}`. -/
def sqOf (u v w z : E) : (Fin 2 → Fin 2) → E :=
  fun c ↦ if c 1 = 0 then (if c 0 = 0 then u else v) else (if c 0 = 0 then w else z)

@[simp] lemma sqOf_sqCorner_zero_zero (u v w z : E) : sqOf u v w z (sqCorner 0 0) = u := by
  simp [sqOf]

@[simp] lemma sqOf_sqCorner_one_zero (u v w z : E) : sqOf u v w z (sqCorner 1 0) = v := by
  simp [sqOf]

@[simp] lemma sqOf_sqCorner_zero_one (u v w z : E) : sqOf u v w z (sqCorner 0 1) = w := by
  simp [sqOf]

@[simp] lemma sqOf_sqCorner_one_one (u v w z : E) : sqOf u v w z (sqCorner 1 1) = z := by
  simp [sqOf]

/-- Every configuration of the unit square is determined by its four corner spins. -/
lemma eq_sqOf (ζ : (Fin 2 → Fin 2) → E) :
    ζ = sqOf (ζ (sqCorner 0 0)) (ζ (sqCorner 1 0)) (ζ (sqCorner 0 1)) (ζ (sqCorner 1 1)) :=
  (funext_sqCorner (by simp) (by simp) (by simp) (by simp)).symm

/-- The antipodal corner of `(a, b)` is `(a + 1, b + 1)`; in the plane the antipodal pairs are
exactly the two diagonals. -/
@[simp] lemma sqCorner_add_one (a b : Fin 2) :
    sqCorner a b + 1 = sqCorner (a + 1) (b + 1) := by
  funext l
  fin_cases l <;> simp

/-! ### The next-nearest-neighbour term of the unit square

Georgii's `∑_{{i,j} ⊆ C, |i-j| = √2}` of (18.29) and (18.36)–(18.37).  In the plane the unit
square has exactly two diagonals, `{(0,0),(1,1)}` and `{(1,0),(0,1)}`; in general `d` this is the
sum over the graph on the corners in which two corners are adjacent when they differ in exactly
two coordinates, and it should be defined — together with `cubeBondSum` — as the bond sum over an
arbitrary graph on the corners of `C` (intended home:
`GibbsMeasure/Model/HeisenbergOceans.lean`, where `cubeBondSum` lives). -/

@[simp] lemma cubeSiteRefl_zero_sqCorner (a b : Fin 2) :
    cubeSiteRefl 0 (sqCorner a b) = sqCorner (a + 1) b := by
  rw [cubeSiteRefl_eq_add_single]
  funext l
  fin_cases l <;> simp

@[simp] lemma cubeSiteRefl_one_sqCorner (a b : Fin 2) :
    cubeSiteRefl 1 (sqCorner a b) = sqCorner a (b + 1) := by
  rw [cubeSiteRefl_eq_add_single]
  funext l
  fin_cases l <;> simp

/-- **Georgii's next-nearest-neighbour term of the unit square**,
`∑_{{i,j} ⊆ C, |i-j| = √2} ψ(σ_i, σ_j)`: the two diagonals of `C = {0,1}²`. -/
def sqDiagSum (ψ : E → E → ℝ) (ζ : (Fin 2 → Fin 2) → E) : ℝ :=
  ψ (ζ (sqCorner 0 0)) (ζ (sqCorner 1 1)) + ψ (ζ (sqCorner 1 0)) (ζ (sqCorner 0 1))

lemma sqDiagSum_def (ψ : E → E → ℝ) (ζ : (Fin 2 → Fin 2) → E) :
    sqDiagSum ψ ζ
      = ψ (ζ (sqCorner 0 0)) (ζ (sqCorner 1 1)) + ψ (ζ (sqCorner 1 0)) (ζ (sqCorner 0 1)) := rfl

lemma sqDiagSum_ge {ψ : E → E → ℝ} {m : ℝ} {ζ : (Fin 2 → Fin 2) → E}
    (hm : ∀ x y, m ≤ ψ x y) : 2 * m ≤ sqDiagSum ψ ζ := by
  have := hm (ζ (sqCorner 0 0)) (ζ (sqCorner 1 1))
  have := hm (ζ (sqCorner 1 0)) (ζ (sqCorner 0 1))
  rw [sqDiagSum_def]
  linarith

lemma sqDiagSum_le {ψ : E → E → ℝ} {M : ℝ} {ζ : (Fin 2 → Fin 2) → E}
    (hM : ∀ x y, ψ x y ≤ M) : sqDiagSum ψ ζ ≤ 2 * M := by
  have := hM (ζ (sqCorner 0 0)) (ζ (sqCorner 1 1))
  have := hM (ζ (sqCorner 1 0)) (ζ (sqCorner 0 1))
  rw [sqDiagSum_def]
  linarith

end CubeCombinatorics

/-! ### Cube interactions under a cube transformation -/

section MeasurableState

variable {E : Type*} [MeasurableSpace E]

lemma measurable_cubeSiteSum {v : E → ℝ} (hv : Measurable v) : Measurable (cubeSiteSum d v) :=
  Finset.measurable_sum _ fun c _ ↦ hv.comp (measurable_pi_apply c)

/-- **Georgii's condition `Φ_C ∘ τ = Φ_C` for a bond sum.**  A cube transformation `τ` acts on
`E^C` through the corner permutation of its cube isometry — an automorphism of the cube graph
(`cubeGraph_adj_cubeIsoCorner`) — and through its spins; so a bond sum is `τ`-invariant as soon
as the bond interaction is invariant under the pairs of spins along the edges. -/
lemma cubeBondSum_onCube {ψ : E → E → ℝ} (τ : CubeTransformation E d)
    (ht : ∀ c c', (cubeGraph d).Adj c c' → ∀ x y, ψ (τ.spin c x) (τ.spin c' y) = ψ x y)
    (ζ : (Fin d → Fin 2) → E) :
    cubeBondSum d ψ (τ.onCube.toFun ζ) = cubeBondSum d ψ ζ := by
  have he : ∀ c c', (cubeGraph d).Adj (τ.corner.symm c) (τ.corner.symm c')
      ↔ (cubeGraph d).Adj c c' := by
    intro c c'
    have := cubeGraph_adj_cubeIsoCorner τ.perm τ.sign (τ.corner.symm c) (τ.corner.symm c')
    simpa only [CubeTransformation.corner, Equiv.apply_symm_apply] using this.symm
  exact cubeBondSum_comp (ψ := ψ) τ.corner.symm he (fun c ↦ τ.spin c) ht ζ

/-- **Georgii's condition `Φ_C ∘ τ = Φ_C` for a site sum.** -/
lemma cubeSiteSum_onCube {v : E → ℝ} (τ : CubeTransformation E d)
    (ht : ∀ c x, v (τ.spin c x) = v x) (ζ : (Fin d → Fin 2) → E) :
    cubeSiteSum d v (τ.onCube.toFun ζ) = cubeSiteSum d v ζ := by
  have h : cubeSiteSum d v (τ.onCube.toFun ζ) = ∑ c, v (ζ (τ.corner.symm c)) :=
    Finset.sum_congr rfl fun c _ ↦ ht c _
  rw [h]
  exact Fintype.sum_equiv τ.corner.symm _ _ fun _ ↦ rfl

/-- A bond sum is invariant under every *spatial* cube transformation — Georgii's `r_0` and
`r_k`, which have trivial spins. -/
lemma cubeBondSum_onCube_of_spin_refl {ψ : E → E → ℝ} (τ : CubeTransformation E d)
    (hτ : ∀ c, τ.spin c = MeasurableEquiv.refl E) (ζ : (Fin d → Fin 2) → E) :
    cubeBondSum d ψ (τ.onCube.toFun ζ) = cubeBondSum d ψ ζ :=
  cubeBondSum_onCube τ (fun c c' _ x y ↦ by rw [hτ c, hτ c']; rfl) ζ

/-- A site sum is invariant under every *spatial* cube transformation. -/
lemma cubeSiteSum_onCube_of_spin_refl {v : E → ℝ} (τ : CubeTransformation E d)
    (hτ : ∀ c, τ.spin c = MeasurableEquiv.refl E) (ζ : (Fin d → Fin 2) → E) :
    cubeSiteSum d v (τ.onCube.toFun ζ) = cubeSiteSum d v ζ :=
  cubeSiteSum_onCube τ (fun c x ↦ by rw [hτ c]; rfl) ζ

/-! ### Definition (18.23) in the form in which the examples verify it

Intended home: `GibbsMeasure/Specification/PeriodicGibbsSymmetry.lean`, next to
`IsPStablePartition`. -/

section Partition

variable {ι : Type*} {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E}

/-- **Georgii's stability condition (18.23)(a)(ii) for a partition into singletons**: the
projections of the `G_n = {ζ_n}` to a face `F` are disjoint as soon as any two of the `ζ_n`
differ somewhere on `F`. -/
lemma pairwise_disjoint_faceRestrict_singleton {ζ : ι → (Fin d → Fin 2) → E} {k : Fin d}
    {a : Fin 2} (h : Pairwise fun m n ↦ ∃ c : Fin d → Fin 2, c k = a ∧ ζ m c ≠ ζ n c) :
    Pairwise fun m n ↦
      Disjoint (faceRestrict E k a '' {ζ m}) (faceRestrict E k a '' {ζ n}) := by
  intro m n hmn
  obtain ⟨c, hc, hne⟩ := h hmn
  rw [Set.image_singleton, Set.image_singleton, Set.disjoint_singleton]
  exact fun heq ↦ hne (congrFun heq ⟨c, hc⟩)

/-- **The identity of Georgii's group `T_{C,λ}`** (18.20)–(18.21): the pure spin transformation
with trivial spins acts on `E^C` as the identity. -/
lemma onCube_toFun_pureSpin_refl (ζ : (Fin d → Fin 2) → E) :
    (CubeTransformation.pureSpin (fun _ : Fin d → Fin 2 ↦ MeasurableEquiv.refl E)).onCube.toFun ζ
      = ζ := by
  funext c
  rw [CubeTransformation.pureSpin_onCube_toFun_apply]
  rfl

/-- The identity belongs to `I_{C,λ}(Φ)` for every `C`-potential satisfying (17.18)(iii). -/
lemma isSymmetry_pureSpin_refl [IsProbabilityMeasure ν]
    (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ) :
    (CubeTransformation.pureSpin
      (fun _ : Fin d → Fin 2 ↦ MeasurableEquiv.refl E)).IsSymmetry φ ν :=
  CubeTransformation.IsSymmetry.of_apply_onCube hφk (fun _ ↦ MeasurePreserving.id ν)
    fun ζ ↦ by rw [onCube_toFun_pureSpin_refl]

/-- **The singleton of a constant cube configuration is `r`-symmetric**: the reflections of `C`
merely permute the corners.  So Georgii's shift group `Θ̃_n` of Theorem (18.25)(ii) is the whole
of `Θ` for a partition into constant configurations. -/
lemma isRSymmetric_singleton_const (b : E) :
    IsRSymmetric E ({fun _ ↦ b} : Set ((Fin d → Fin 2) → E)) := by
  intro k
  ext ζ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, cubeRefl_apply]
  refine ⟨fun h c ↦ ?_, fun h c ↦ h _⟩
  have := h (cubeSiteRefl k c)
  rwa [cubeSiteRefl_cubeSiteRefl] at this

/-- **`I_{C,λ}(Φ) ⊆ I_{C,λ}(βΦ)`** for a single transformation, the one-transformation form of
`IsPhiSymmetric.const_mul`.  (Intended home:
`GibbsMeasure/Specification/PeriodicGibbsSymmetry.lean`.) -/
lemma CubeTransformation.IsSymmetry.const_mul {τ : CubeTransformation E d}
    (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ) (hτ : τ.IsSymmetry φ ν) (β : ℝ) :
    τ.IsSymmetry (fun ζ ↦ β * φ ζ) ν :=
  IsSymmetry.of_apply_onCube (fun k ζ ↦ by rw [hφk k ζ]) hτ.measurePreserving_spin
    fun ζ ↦ by rw [hτ.apply_onCube ζ]

/-- **Georgii, Definition (18.23)(b)**: only the *off-diagonal* pairs need a symmetry, the
diagonal being covered by the identity of `T_{C,λ}`. -/
lemma isPhiSymmetric_of_ne [IsProbabilityMeasure ν]
    (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ) {G : ι → Set ((Fin d → Fin 2) → E)}
    (h : ∀ m n, m ≠ n → ∃ τ : CubeTransformation E d,
      τ.IsSymmetry φ ν ∧ τ.onCube.toFun '' G m = G n) :
    IsPhiSymmetric φ ν G := by
  intro m n
  rcases eq_or_ne m n with rfl | hmn
  · refine ⟨_, isSymmetry_pureSpin_refl hφk, ?_⟩
    rw [Set.image_congr (fun ζ _ ↦ onCube_toFun_pureSpin_refl ζ)]
    exact Set.image_id' _
  · exact h m n hmn

/-- A cube transformation with trivial spins is a symmetry of `Φ` as soon as `Φ_C ∘ τ = Φ_C`. -/
lemma CubeTransformation.isSymmetry_of_spin_refl [IsProbabilityMeasure ν]
    (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ) {τ : CubeTransformation E d}
    (hτ : ∀ c, τ.spin c = MeasurableEquiv.refl E) (hφτ : ∀ ζ, φ (τ.onCube.toFun ζ) = φ ζ) :
    τ.IsSymmetry φ ν :=
  IsSymmetry.of_apply_onCube hφk (fun c ↦ by rw [hτ c]; exact MeasurePreserving.id ν) hφτ

end Partition

/-! #### The reflections and the rotation on the corners of the unit square -/

@[simp] lemma cubeRefl_zero_sqCorner (ζ : (Fin 2 → Fin 2) → E) (a b : Fin 2) :
    cubeRefl E 0 ζ (sqCorner a b) = ζ (sqCorner (a + 1) b) := by
  rw [cubeRefl_apply, cubeSiteRefl_zero_sqCorner]

@[simp] lemma cubeRefl_one_sqCorner (ζ : (Fin 2 → Fin 2) → E) (a b : Fin 2) :
    cubeRefl E 1 ζ (sqCorner a b) = ζ (sqCorner a (b + 1)) := by
  rw [cubeRefl_apply, cubeSiteRefl_one_sqCorner]

@[simp] lemma onCube_planeRot_sqCorner (ζ : (Fin 2 → Fin 2) → E) (a b : Fin 2) :
    (CubeTransformation.planeRot (E := E) (d := 0)).onCube.toFun ζ (sqCorner a b)
      = ζ (sqCorner b (a + 1)) := by
  rw [CubeTransformation.planeRot_onCube_toFun_apply]
  congr 1
  funext l
  fin_cases l <;> simp

variable (E) in
/-- **The reflection of the unit square in its main diagonal**: the cube isometry that transposes
the two coordinates.  Together with `sqAntiTranspose`, `CubeTransformation.refl 0`,
`CubeTransformation.refl 1` and `CubeTransformation.planeRot` it generates the dihedral group of
the square inside `T_{C,λ}`. -/
def sqTranspose : CubeTransformation E 2 where
  perm := Equiv.swap 0 1
  sign := fun _ ↦ false
  spin := fun _ ↦ MeasurableEquiv.refl E

variable (E) in
/-- **The reflection of the unit square in its antidiagonal.** -/
def sqAntiTranspose : CubeTransformation E 2 where
  perm := Equiv.swap 0 1
  sign := fun _ ↦ true
  spin := fun _ ↦ MeasurableEquiv.refl E

@[simp] lemma sqTranspose_spin (c : Fin 2 → Fin 2) :
    (sqTranspose E).spin c = MeasurableEquiv.refl E := rfl

@[simp] lemma sqAntiTranspose_spin (c : Fin 2 → Fin 2) :
    (sqAntiTranspose E).spin c = MeasurableEquiv.refl E := rfl

@[simp] lemma onCube_sqTranspose_sqCorner (ζ : (Fin 2 → Fin 2) → E) (a b : Fin 2) :
    (sqTranspose E).onCube.toFun ζ (sqCorner a b) = ζ (sqCorner b a) := by
  have hcorner : (cubeIsoCorner (Equiv.swap (0 : Fin 2) 1) (fun _ ↦ false)).symm (sqCorner a b)
      = sqCorner b a := by
    fin_cases a <;> fin_cases b <;> decide
  rw [CubeTransformation.onCube_toFun_apply,
    show (sqTranspose E).corner = cubeIsoCorner (Equiv.swap (0 : Fin 2) 1) (fun _ ↦ false) from
      rfl, hcorner, sqTranspose_spin]
  rfl

@[simp] lemma onCube_sqAntiTranspose_sqCorner (ζ : (Fin 2 → Fin 2) → E) (a b : Fin 2) :
    (sqAntiTranspose E).onCube.toFun ζ (sqCorner a b) = ζ (sqCorner (b + 1) (a + 1)) := by
  have hcorner : (cubeIsoCorner (Equiv.swap (0 : Fin 2) 1) (fun _ ↦ true)).symm (sqCorner a b)
      = sqCorner (b + 1) (a + 1) := by
    fin_cases a <;> fin_cases b <;> decide
  rw [CubeTransformation.onCube_toFun_apply,
    show (sqAntiTranspose E).corner = cubeIsoCorner (Equiv.swap (0 : Fin 2) 1) (fun _ ↦ true) from
      rfl, hcorner, sqAntiTranspose_spin]
  rfl

/-! #### The dihedral group of the square on the four corner spins

In Georgii's notation `ω = (w z / u v)` the generators act by
`r_1 : (u,v,w,z) ↦ (v,u,z,w)`, `r_2 : ↦ (w,z,u,v)`, `r_0 : ↦ (w,u,z,v)`,
`sqTranspose : ↦ (u,w,v,z)` and `sqAntiTranspose : ↦ (z,v,w,u)`. -/

lemma onCube_refl_zero_sqOf (u v w z : E) :
    (CubeTransformation.refl (E := E) 0).onCube.toFun (sqOf u v w z) = sqOf v u z w := by
  rw [CubeTransformation.refl_onCube_toFun]
  refine funext_sqCorner ?_ ?_ ?_ ?_ <;>
    simp only [cubeRefl_zero_sqCorner, show (0 + 1 : Fin 2) = 1 from rfl,
      show (1 + 1 : Fin 2) = 0 from rfl, sqOf_sqCorner_zero_zero, sqOf_sqCorner_one_zero,
      sqOf_sqCorner_zero_one, sqOf_sqCorner_one_one]

lemma onCube_refl_one_sqOf (u v w z : E) :
    (CubeTransformation.refl (E := E) 1).onCube.toFun (sqOf u v w z) = sqOf w z u v := by
  rw [CubeTransformation.refl_onCube_toFun]
  refine funext_sqCorner ?_ ?_ ?_ ?_ <;>
    simp only [cubeRefl_one_sqCorner, show (0 + 1 : Fin 2) = 1 from rfl,
      show (1 + 1 : Fin 2) = 0 from rfl, sqOf_sqCorner_zero_zero, sqOf_sqCorner_one_zero,
      sqOf_sqCorner_zero_one, sqOf_sqCorner_one_one]

lemma onCube_planeRot_sqOf (u v w z : E) :
    (CubeTransformation.planeRot (E := E) (d := 0)).onCube.toFun (sqOf u v w z)
      = sqOf w u z v := by
  refine funext_sqCorner ?_ ?_ ?_ ?_ <;>
    simp only [onCube_planeRot_sqCorner, show (0 + 1 : Fin 2) = 1 from rfl,
      show (1 + 1 : Fin 2) = 0 from rfl, sqOf_sqCorner_zero_zero, sqOf_sqCorner_one_zero,
      sqOf_sqCorner_zero_one, sqOf_sqCorner_one_one]

lemma onCube_sqTranspose_sqOf (u v w z : E) :
    (sqTranspose E).onCube.toFun (sqOf u v w z) = sqOf u w v z := by
  refine funext_sqCorner ?_ ?_ ?_ ?_ <;>
    simp only [onCube_sqTranspose_sqCorner, sqOf_sqCorner_zero_zero, sqOf_sqCorner_one_zero,
      sqOf_sqCorner_zero_one, sqOf_sqCorner_one_one]

lemma onCube_sqAntiTranspose_sqOf (u v w z : E) :
    (sqAntiTranspose E).onCube.toFun (sqOf u v w z) = sqOf z v w u := by
  refine funext_sqCorner ?_ ?_ ?_ ?_ <;>
    simp only [onCube_sqAntiTranspose_sqCorner, show (0 + 1 : Fin 2) = 1 from rfl,
      show (1 + 1 : Fin 2) = 0 from rfl, sqOf_sqCorner_zero_zero, sqOf_sqCorner_one_zero,
      sqOf_sqCorner_zero_one, sqOf_sqCorner_one_one]

/-- **Condition (iii) of Georgii (17.18)** for the next-nearest-neighbour term: the reflections
`r_1, r_2` of the square permute its two diagonals. -/
lemma sqDiagSum_cubeRefl {ψ : E → E → ℝ} (hψ : ∀ x y, ψ x y = ψ y x) (k : Fin 2)
    (ζ : (Fin 2 → Fin 2) → E) : sqDiagSum ψ (cubeRefl E k ζ) = sqDiagSum ψ ζ := by
  fin_cases k
  · simp only [Fin.zero_eta, sqDiagSum_def, cubeRefl_zero_sqCorner,
      show (1 + 1 : Fin 2) = 0 from rfl, show (0 + 1 : Fin 2) = 1 from rfl]
    rw [add_comm]
  · simp only [Fin.mk_one, sqDiagSum_def, cubeRefl_one_sqCorner,
      show (1 + 1 : Fin 2) = 0 from rfl, show (0 + 1 : Fin 2) = 1 from rfl]
    rw [hψ (ζ (sqCorner 0 1)) (ζ (sqCorner 1 0)), hψ (ζ (sqCorner 1 1)) (ζ (sqCorner 0 0)),
      add_comm]

/-- **Georgii's rotation `r_0`** (18.20) permutes the two diagonals of the square. -/
lemma sqDiagSum_onCube_planeRot {ψ : E → E → ℝ} (hψ : ∀ x y, ψ x y = ψ y x)
    (ζ : (Fin 2 → Fin 2) → E) :
    sqDiagSum ψ ((CubeTransformation.planeRot (E := E) (d := 0)).onCube.toFun ζ)
      = sqDiagSum ψ ζ := by
  simp only [sqDiagSum_def, onCube_planeRot_sqCorner, show (1 + 1 : Fin 2) = 0 from rfl,
    show (0 + 1 : Fin 2) = 1 from rfl]
  rw [hψ (ζ (sqCorner 0 1)) (ζ (sqCorner 1 0)), add_comm]

@[simp] lemma sqDiagSum_onCube_pureSpin {ψ : E → E → ℝ} (t : (Fin 2 → Fin 2) → E ≃ᵐ E)
    (ζ : (Fin 2 → Fin 2) → E) :
    sqDiagSum ψ ((CubeTransformation.pureSpin t).onCube.toFun ζ)
      = ψ (t (sqCorner 0 0) (ζ (sqCorner 0 0))) (t (sqCorner 1 1) (ζ (sqCorner 1 1)))
        + ψ (t (sqCorner 1 0) (ζ (sqCorner 1 0))) (t (sqCorner 0 1) (ζ (sqCorner 0 1))) := by
  simp only [sqDiagSum_def, CubeTransformation.pureSpin_onCube_toFun_apply]

/-- **The next-nearest-neighbour term as a sum over the antipodal pairs**: in the plane the two
diagonals of `C` are the pairs `{c, c + (1,1)}`, and every corner lies on exactly one of them. -/
lemma sqDiagSum_eq_half_sum {ψ : E → E → ℝ} (hψ : ∀ x y, ψ x y = ψ y x)
    (ζ : (Fin 2 → Fin 2) → E) :
    sqDiagSum ψ ζ = (2 : ℝ)⁻¹ * ∑ c, ψ (ζ c) (ζ (c + 1)) := by
  rw [sum_univ_cubeCorners, sqDiagSum_def]
  simp only [sqCorner_add_one, show (0 + 1 : Fin 2) = 1 from rfl, show (1 + 1 : Fin 2) = 0 from rfl]
  rw [hψ (ζ (sqCorner 0 1)) (ζ (sqCorner 1 0)), hψ (ζ (sqCorner 1 1)) (ζ (sqCorner 0 0))]
  ring

/-- The corner permutation of a cube isometry of the square preserves the antipodal pairing:
`s(c) + s(c + (1,1)) = (1,1)`. -/
lemma cubeIsoCorner_symm_add_one (π : Equiv.Perm (Fin 2)) (ε : Fin 2 → Bool)
    (c : Fin 2 → Fin 2) :
    (cubeIsoCorner π ε).symm (c + 1) = (cubeIsoCorner π ε).symm c + 1 := by
  have hkey := cubeIsoCorner_add_cubeIsoCorner π ε ((cubeIsoCorner π ε).symm c)
    ((cubeIsoCorner π ε).symm (c + 1))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hkey
  have hone : (c + 1) + c = 1 := by
    funext l
    have := congrFun (corner_add_self c) l
    simp only [Pi.add_apply, Pi.zero_apply] at this
    simp only [Pi.add_apply, Pi.one_apply]
    rw [add_right_comm, this, zero_add]
  rw [hone] at hkey
  have hperm : (cornerPerm π).symm 1 = (1 : Fin 2 → Fin 2) := by funext l; simp
  have := congrArg (cornerPerm π).symm hkey
  rw [AddEquiv.symm_apply_apply, hperm] at this
  calc (cubeIsoCorner π ε).symm (c + 1)
      = ((cubeIsoCorner π ε).symm (c + 1) + (cubeIsoCorner π ε).symm c)
          + (cubeIsoCorner π ε).symm c := by rw [add_assoc, corner_add_self, add_zero]
    _ = 1 + (cubeIsoCorner π ε).symm c := by rw [← this]
    _ = (cubeIsoCorner π ε).symm c + 1 := add_comm _ _

lemma measurable_sqDiagSum {ψ : E → E → ℝ} (hψ : Measurable (Function.uncurry ψ)) :
    Measurable (sqDiagSum ψ) := by
  unfold sqDiagSum
  refine Measurable.add ?_ ?_
  · have h : Measurable fun ζ : (Fin 2 → Fin 2) → E ↦ (ζ (sqCorner 0 0), ζ (sqCorner 1 1)) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact hψ.comp h
  · have h : Measurable fun ζ : (Fin 2 → Fin 2) → E ↦ (ζ (sqCorner 1 0), ζ (sqCorner 0 1)) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact hψ.comp h

/-- **The next-nearest-neighbour term of the square is invariant under every spatial cube
transformation**: a cube isometry permutes the two diagonals of `C`, because its corner
permutation preserves the antipodal pairing (`cubeIsoCorner_symm_add_one`). -/
lemma sqDiagSum_onCube_of_spin_refl {ψ : E → E → ℝ} (hψ : ∀ x y, ψ x y = ψ y x)
    (τ : CubeTransformation E 2) (hτ : ∀ c, τ.spin c = MeasurableEquiv.refl E)
    (ζ : (Fin 2 → Fin 2) → E) : sqDiagSum ψ (τ.onCube.toFun ζ) = sqDiagSum ψ ζ := by
  have hval : ∀ c, τ.onCube.toFun ζ c = ζ (τ.corner.symm c) := fun c ↦ by
    rw [CubeTransformation.onCube_toFun_apply, hτ c]
    rfl
  rw [sqDiagSum_eq_half_sum hψ, sqDiagSum_eq_half_sum hψ]
  congr 1
  have hstep : ∀ c : Fin 2 → Fin 2, τ.corner.symm (c + 1) = τ.corner.symm c + 1 :=
    cubeIsoCorner_symm_add_one τ.perm τ.sign
  calc ∑ c, ψ (τ.onCube.toFun ζ c) (τ.onCube.toFun ζ (c + 1))
      = ∑ c, ψ (ζ (τ.corner.symm c)) (ζ (τ.corner.symm c + 1)) := by
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [hval c, hval (c + 1), hstep c]
    _ = ∑ c, ψ (ζ c) (ζ (c + 1)) :=
        Equiv.sum_comp τ.corner.symm fun c ↦ ψ (ζ c) (ζ (c + 1))

/-- **Condition (iv) of Georgii (17.18) is automatic over a finite state space**: a real-valued
function on the finite set `E^C` is bounded. -/
lemma isCubeConfining_univ_of_finite [Finite E] (φ : ((Fin d → Fin 2) → E) → ℝ)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    IsCubeConfining φ ν fun _ : ℕ ↦ (Set.univ : Set E) := by
  have : Finite ((Fin d → Fin 2) → E) := Pi.finite
  obtain ⟨c, hc⟩ := (Set.finite_range fun ζ ↦ |φ ζ|).bddAbove
  exact isCubeConfining_univ ⟨c, fun ζ ↦ hc ⟨ζ, rfl⟩⟩

/-! #### A continuous cube interaction over a state space charging open sets

Intended home: `GibbsMeasure/Specification/LocalGroundStates.lean`. -/

/-- **Georgii (18.1) for a continuous cube interaction**: if `λ^C` charges every nonempty open
set and `Φ_C` is continuous, bounded below by `m` and attains `m`, then `m_Φ = m`.  This is the
argument behind every "clearly, `m_Φ = …`" of §18.3 with a continuous state space; the discrete
version is `localGroundEnergy_eq`. -/
theorem localGroundEnergy_eq_of_isOpenPosMeasure [TopologicalSpace E]
    {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
    [(cubeMeasure d ν).IsOpenPosMeasure] (hφc : Continuous φ) {m : ℝ} (hm : ∀ ζ, m ≤ φ ζ)
    {ζ₀ : (Fin d → Fin 2) → E} (hζ₀ : φ ζ₀ = m) : localGroundEnergy φ ν = m := by
  refine le_antisymm ?_ (le_localGroundEnergy hm)
  rw [localGroundEnergy_eq_sSup hm]
  refine csSup_le ⟨m - 1, ?_⟩ fun c hc ↦ ?_
  · have hempty : {ζ : (Fin d → Fin 2) → E | φ ζ ≤ m - 1} = (∅ : Set _) := by
      ext ζ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      linarith [hm ζ]
    change cubeMeasure d ν {ζ | φ ζ ≤ m - 1} = 0
    rw [hempty, measure_empty]
  · by_contra hlt
    rw [not_le] at hlt
    have hUopen : IsOpen (φ ⁻¹' Set.Iio c) := hφc.isOpen_preimage _ isOpen_Iio
    have hUne : (φ ⁻¹' Set.Iio c).Nonempty := ⟨ζ₀, by rw [Set.mem_preimage, hζ₀]; exact hlt⟩
    have hpos : 0 < cubeMeasure d ν (φ ⁻¹' Set.Iio c) := hUopen.measure_pos _ hUne
    have hsub : φ ⁻¹' Set.Iio c ⊆ {ζ : (Fin d → Fin 2) → E | φ ζ ≤ c} := by
      intro ζ hζ
      rw [Set.mem_preimage, Set.mem_Iio] at hζ
      exact hζ.le
    exact absurd hc ((measure_mono hsub).trans_lt' hpos).ne'

/-- A measure-preserving map of a finite measure preserves its normalisation. -/
lemma MeasurePreserving.probNormalize {α : Type*} [MeasurableSpace α] {T : α → α}
    {ν : Measure α} (h : MeasurePreserving T ν ν) :
    MeasurePreserving T ν.probNormalize ν.probNormalize := by
  refine ⟨h.measurable, ?_⟩
  rw [Measure.probNormalize_def, Measure.map_smul _ h.measurable.aemeasurable, h.map_eq]

/-! ### A finite state space: the essential infimum (18.1) is a minimum

Intended home: `GibbsMeasure/Specification/LocalGroundStates.lean`, next to
`localGroundEnergy`. -/

section FiniteState

variable {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E}

/-- If the a priori measure charges every point of `E` then `λ^C` charges every configuration of
the cube. -/
lemma cubeMeasure_singleton_ne_zero [MeasurableSingletonClass E] [SigmaFinite ν]
    (hν : ∀ x : E, ν {x} ≠ 0) (ζ : (Fin d → Fin 2) → E) : cubeMeasure d ν {ζ} ≠ 0 := by
  have h : ({ζ} : Set ((Fin d → Fin 2) → E)) = Set.univ.pi fun c ↦ {ζ c} := by
    ext ξ
    simp [Set.mem_singleton_iff, funext_iff, eq_comm]
  rw [h, Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.2 fun c _ ↦ hν (ζ c)

/-- **Georgii (18.1) over a finite state space**: `m_Φ = min Φ_C`.  The `λ^C`-essential infimum
is the plain infimum as soon as `λ^C` charges every configuration. -/
lemma localGroundEnergy_eq_ciInf [MeasurableSingletonClass E] [Finite E] [Nonempty E]
    [SigmaFinite ν] (hν : ∀ x : E, ν {x} ≠ 0) : localGroundEnergy φ ν = ⨅ ζ, φ ζ :=
  essInf_eq_ciInf (cubeMeasure_singleton_ne_zero hν) (Set.finite_range φ).bddBelow

/-- **Georgii (18.1) over a finite state space**, in the form in which it is used: if `Φ_C ≥ m`
everywhere and `Φ_C(ζ₀) = m` for one configuration `ζ₀` then `m_Φ = m`. -/
lemma localGroundEnergy_eq [MeasurableSingletonClass E] [Finite E] [Nonempty E] [SigmaFinite ν]
    (hν : ∀ x : E, ν {x} ≠ 0) {m : ℝ} (hm : ∀ ζ, m ≤ φ ζ) {ζ₀ : (Fin d → Fin 2) → E}
    (hζ₀ : φ ζ₀ = m) : localGroundEnergy φ ν = m := by
  rw [localGroundEnergy_eq_ciInf hν]
  exact le_antisymm (hζ₀ ▸ ciInf_le (Set.finite_range φ).bddBelow ζ₀) (le_ciInf hm)

/-- **Georgii (18.2) over a finite state space**: `G_ε(Φ) = {Φ_C ≤ m + ε}` once `m_Φ = m` is
known. -/
lemma localGroundStates_eq_setOf_le [MeasurableSingletonClass E] [Finite E] [Nonempty E]
    [SigmaFinite ν] (hν : ∀ x : E, ν {x} ≠ 0) {m : ℝ} (hm : ∀ ζ, m ≤ φ ζ)
    {ζ₀ : (Fin d → Fin 2) → E} (hζ₀ : φ ζ₀ = m) (ε : ℝ) :
    localGroundStates φ ν ε = {ζ | φ ζ ≤ m + ε} := by
  rw [localGroundStates, localGroundEnergy_eq hν hm hζ₀]


/-- **Over a finite state space the local `ε`-ground states shrink to the exact local ground
states**: `Φ_C` takes finitely many values, so for `ε` below the gap to the second smallest of
them `G_ε(Φ) = {Φ_C = m_Φ}`.  This is what makes Georgii's "if `ε > 0` is small enough" in
(18.23)(a)(i) a computation with the *exact* ground states in every discrete example. -/
theorem exists_pos_localGroundStates_subset [MeasurableSingletonClass E] [Finite E] [Nonempty E]
    [SigmaFinite ν] (hν : ∀ x : E, ν {x} ≠ 0) {m : ℝ} (hm : ∀ ζ, m ≤ φ ζ)
    {ζ₀ : (Fin d → Fin 2) → E} (hζ₀ : φ ζ₀ = m) :
    ∃ ε > 0, localGroundStates φ ν ε ⊆ {ζ | φ ζ = m} := by
  classical
  have : Fintype ((Fin d → Fin 2) → E) := Fintype.ofFinite _
  set T : Finset ((Fin d → Fin 2) → E) := Finset.univ.filter (fun ζ ↦ φ ζ ≠ m) with hT
  have hmemT : ∀ ζ, ζ ∈ T ↔ φ ζ ≠ m := by
    intro ζ
    rw [hT, Finset.mem_filter]
    simp
  rcases T.eq_empty_or_nonempty with hTe | hTn
  · refine ⟨1, one_pos, fun ζ _ ↦ ?_⟩
    by_contra hne
    exact Finset.eq_empty_iff_forall_notMem.1 hTe ζ ((hmemT ζ).2 hne)
  · have hlt : m < T.inf' hTn φ :=
      (Finset.lt_inf'_iff hTn).2 fun ξ hξ ↦ lt_of_le_of_ne (hm ξ) (Ne.symm ((hmemT ξ).1 hξ))
    refine ⟨(T.inf' hTn φ - m) / 2, by linarith, fun ζ hζ ↦ ?_⟩
    by_contra hne
    have hinf : T.inf' hTn φ ≤ φ ζ := Finset.inf'_le _ ((hmemT ζ).2 hne)
    have hle : φ ζ ≤ localGroundEnergy φ ν + (T.inf' hTn φ - m) / 2 := hζ
    rw [localGroundEnergy_eq hν hm hζ₀] at hle
    linarith

end FiniteState


/-! ### Theorem (18.25), last statement, at low temperature

Intended home: `GibbsMeasure/Model/DiscreteSymmetryBreaking.lean`, next to
`le_encard_extremePoints_invariantG_shiftGroup_of_isRSymmetric` and
`exists_gibbsMeasure_family_of_crossingBound_lt_one`, of which this is the common refinement. -/

section ExtremePoints

open Peierls

variable {N : ℕ} {φ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {G : Fin N → Set ((Fin 2 → Fin 2) → E)}

/-- **The last statement of Georgii, Theorem (18.25)**, `|ex 𝒢_Θ̃(βΦ)| ≥ N`, for an `r`-symmetric
partition (so that `Θ̃ = Θ`), with Georgii's explicit threshold `4 z(t(G_ε(Φ), βΦ)) < 1` of
Comment (18.26)(1).  It combines `exists_gibbsMeasure_family_of_crossingBound_lt_one` — from
which the construction of the `μ ∈ 𝒢₀(βΦ)` and the positivity of `μ(ξ⁰_P(⋃_n G_n, ·) ≠ ∅)` are
taken verbatim — with `le_encard_extremePoints_invariantG_shiftGroup_of_isRSymmetric`. -/
theorem le_encard_extremePoints_of_crossingBound_lt_one [StandardBorelSpace E]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E} (hK : IsCubeConfining φ ν K)
    (hpart : IsPStablePartition φ ν Set.univ G) (hsym : IsPhiSymmetric φ ν G)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hGsym : ∀ n, IsRSymmetric E (G n)) {ε : ℝ}
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) {β : ℝ} (hβ : 0 < β)
    (hδ : 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)) < 1)
    (hφβ : Measurable fun ζ ↦ β * φ ζ) (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * φ ζ) :
    (N : ℕ∞) ≤ ((invariantG (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν hφβ hMβ)
      (shiftGroup (Fin 2 → ℤ) E)).extremePoints ℝ≥0∞).encard := by
  classical
  have : Nonempty E := ν.nonempty_of_neZero
  obtain ⟨μ, hμ⟩ := GZero_nonempty (d := 1) (ν := ν) hφβ (M := β * M)
    (fun ζ ↦ mul_le_mul_of_nonneg_left (hM ζ) hβ.le) (fun k ζ ↦ by rw [hφk k ζ])
    (hK.const_mul hβ) fun _ ↦ Classical.arbitrary E
  have hbound := le_measure_mem_latticeOceanPart_localGroundStates hφ hM hφk ε hβ.le hμ
  have hmono : (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (0 : Site) ∈ latticeOceanPart E (localGroundStates φ ν ε) ω}
        ≤ (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticeOceanPart E (⋃ n, G n) ω} :=
    measure_mono fun ω hω ↦ latticeOceanPart_mono (E := E) hGε ω hω
  have hzero : (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (0 : Site) ∈ latticeOceanPart E (⋃ n, G n) ω}
        ≤ (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty} :=
    measure_mono fun ω hω ↦ ⟨0, hω⟩
  have hpos : 0 < (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty} :=
    lt_of_lt_of_le (tsub_pos_of_lt hδ) ((hbound.trans hmono).trans hzero)
  exact le_encard_extremePoints_invariantG_shiftGroup_of_isRSymmetric (φ₀ := φ) hφβ hMβ hpart
    (hsym.const_mul hφk β) hGmeas hGsym hμ hpos

/-- **The last statement of Georgii, Theorem (18.25)** as he states it: `|ex 𝒢_Θ(βΦ)| ≥ N` for
all sufficiently large `β`, when the partition is `r`-symmetric. -/
theorem eventually_le_encard_extremePoints [StandardBorelSpace E]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E} (hK : IsCubeConfining φ ν K)
    (hpart : IsPStablePartition φ ν Set.univ G) (hsym : IsPhiSymmetric φ ν G)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hGsym : ∀ n, IsRSymmetric E (G n)) {ε : ℝ} (hε : 0 < ε)
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * φ ζ) (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * φ ζ),
      (N : ℕ∞) ≤ ((invariantG (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν hφβ hMβ)
        (shiftGroup (Fin 2 → ℤ) E)).extremePoints ℝ≥0∞).encard := by
  have hz : ∀ᶠ β : ℝ in atTop, 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)) < 1 := by
    have h := tendsto_crossingBound_patternWeight_localGroundStates (ν := ν) hφ hM hε
    have h4 : Tendsto (fun β : ℝ ↦ 4 * Peierls.crossingBound
        (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) h (Or.inr (by norm_num))
    exact h4.eventually_lt_const (by norm_num)
  filter_upwards [eventually_gt_atTop 0, hz] with β hβ hδ hφβ hMβ
  exact le_encard_extremePoints_of_crossingBound_lt_one hφ hM hφk hK hpart hsym hGmeas hGsym
    hGε hβ hδ hφβ hMβ

end ExtremePoints

/-! ### Theorem (18.25) with the last sentence of (iii)

Intended home: `GibbsMeasure/Model/DiscreteSymmetryBreaking.lean`.  Its
`exists_gibbsMeasure_family_of_crossingBound_lt_one` proves everything below, but does not expose
the last sentence of (18.25)(iii), `θ_{e_k}(μ_n) = μ_m` when `r_k G_m = G_n`, whose ingredient
`map_shift_cond_setOf_latticeOceanPart_nonempty` is already there.  Georgii needs that sentence
in 18.3.2. -/

section ShiftTransport

open Peierls

variable {ι : Type*} {φ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {G : ι → Set ((Fin 2 → Fin 2) → E)}

/-- **Georgii, Theorem (18.25)** at Georgii's explicit threshold `4 z(t(G_ε(Φ), βΦ)) < 1`, with
assertions (i), (ii), (iii) *and* the last sentence of (iii): if `r_k G_m = G_n` then the shift
`θ_{e_k}` in direction `k` carries `μ_n` to `μ_m`. -/
theorem exists_gibbsMeasure_family_shift_of_crossingBound_lt_one [StandardBorelSpace E]
    [Finite ι] (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E} (hK : IsCubeConfining φ ν K)
    (hpart : IsPStablePartition φ ν Set.univ G) (hsym : IsPhiSymmetric φ ν G)
    (hGmeas : ∀ n, MeasurableSet (G n)) {ε : ℝ}
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) {β : ℝ} (hβ : 0 < β)
    (hδ : 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)) < 1)
    (hφβ : Measurable fun ζ ↦ β * φ ζ) (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * φ ζ) :
    ∃ ρ : ι → Measure ((Fin 2 → ℤ) → E),
      (∀ n, IsProbabilityMeasure (ρ n)) ∧
      (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν hφβ hMβ) (ρ n)) ∧
      (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧
      (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
      (∀ n, 1 - 4 * Peierls.crossingBound
          (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))
            ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
      (∀ (n : ι) (a : Fin 2 → ℤ), tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G n = G n →
        MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
      (∀ (n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry (fun ζ ↦ β * φ ζ) ν →
        τ.onCube.toFun '' G n = G n → MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) ∧
      (∀ (m n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry (fun ζ ↦ β * φ ζ) ν →
        τ.onCube.toFun '' G m = G n → (ρ m).map (τ.onLattice E).toFun = ρ n) ∧
      (∀ (m n : ι) (k : Fin 2), cubeRefl E k ⁻¹' G m = G n →
        (ρ n).map (shift E (Pi.single k 1)).toFun = ρ m) := by
  classical
  have : Nonempty E := ν.nonempty_of_neZero
  obtain ⟨μ, hμ⟩ := GZero_nonempty (d := 1) (ν := ν) hφβ (M := β * M)
    (fun ζ ↦ mul_le_mul_of_nonneg_left (hM ζ) hβ.le) (fun k ζ ↦ by rw [hφk k ζ])
    (hK.const_mul hβ) fun _ ↦ Classical.arbitrary E
  have hbound := le_measure_mem_latticeOceanPart_localGroundStates hφ hM hφk ε hβ.le hμ
  have hmono : (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (0 : Site) ∈ latticeOceanPart E (localGroundStates φ ν ε) ω}
        ≤ (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticeOceanPart E (⋃ n, G n) ω} :=
    measure_mono fun ω hω ↦ latticeOceanPart_mono (E := E) hGε ω hω
  have hzero : (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (0 : Site) ∈ latticeOceanPart E (⋃ n, G n) ω}
        ≤ (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty} :=
    measure_mono fun ω hω ↦ ⟨0, hω⟩
  have hpos : 0 < (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty} :=
    lt_of_lt_of_le (tsub_pos_of_lt hδ) ((hbound.trans hmono).trans hzero)
  have hsymβ : IsPhiSymmetric (fun ζ ↦ β * φ ζ) ν G := hsym.const_mul hφk β
  refine ⟨fun n ↦ (μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}],
    isProbabilityMeasure_cond_setOf_latticeOceanPart_nonempty hφβ hMβ hpart hsymβ hμ hpos,
    isGibbsMeasure_cond_setOf_latticeOceanPart_nonempty hφβ hMβ hpart hsymβ hGmeas hμ hpos,
    fun m n hmn ↦ mutuallySingular_cond_setOf_latticeOceanPart_nonempty hpart hGmeas hmn,
    cond_apply_self_setOf_latticeOceanPart_nonempty hφβ hMβ hpart hsymβ hμ hpos,
    fun n ↦ (hbound.trans hmono).trans (le_cond_measure_setOf_zero_mem_latticeOceanPart hφβ hMβ
      hpart hsymβ hμ (measurableSet_setOf_latticeOceanPart_nonempty_family (G := G) hGmeas)
      hpos n),
    fun n a ha ↦ measurePreserving_shift_cond_setOf_latticeOceanPart_nonempty hφβ hGmeas hμ n ha,
    fun n τ hτ hGτ ↦ measurePreserving_onLattice_cond_setOf_latticeOceanPart_nonempty hφβ hMβ
      hGmeas hμ n hτ hGτ,
    fun m n τ hτ hGτ ↦ map_onLattice_cond_setOf_latticeOceanPart_nonempty hφβ hMβ hsymβ hGmeas hμ
      m n hτ hGτ,
    fun m n k hGk ↦ map_shift_cond_setOf_latticeOceanPart_nonempty hφβ hMβ hsymβ hGmeas hμ
      m n hGk⟩

/-- **Georgii, Theorem (18.25)** as he states it — "if `β` is sufficiently large" — with the last
sentence of (iii). -/
theorem eventually_exists_gibbsMeasure_family_shift [StandardBorelSpace E] [Finite ι]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E} (hK : IsCubeConfining φ ν K)
    (hpart : IsPStablePartition φ ν Set.univ G) (hsym : IsPhiSymmetric φ ν G)
    (hGmeas : ∀ n, MeasurableSet (G n)) {ε : ℝ} (hε : 0 < ε)
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * φ ζ) (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * φ ζ),
      ∃ ρ : ι → Measure ((Fin 2 → ℤ) → E),
        (∀ n, IsProbabilityMeasure (ρ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν hφβ hMβ) (ρ n)) ∧
        (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧
        (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
        (∀ n, 1 - 4 * Peierls.crossingBound
            (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))
              ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
        (∀ (n : ι) (a : Fin 2 → ℤ), tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G n = G n →
          MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
        (∀ (n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry (fun ζ ↦ β * φ ζ) ν →
          τ.onCube.toFun '' G n = G n → MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) ∧
        (∀ (m n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry (fun ζ ↦ β * φ ζ) ν →
          τ.onCube.toFun '' G m = G n → (ρ m).map (τ.onLattice E).toFun = ρ n) ∧
        (∀ (m n : ι) (k : Fin 2), cubeRefl E k ⁻¹' G m = G n →
          (ρ n).map (shift E (Pi.single k 1)).toFun = ρ m) := by
  have hz : ∀ᶠ β : ℝ in atTop, 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)) < 1 := by
    have h := tendsto_crossingBound_patternWeight_localGroundStates (ν := ν) hφ hM hε
    have h4 : Tendsto (fun β : ℝ ↦ 4 * Peierls.crossingBound
        (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) h (Or.inr (by norm_num))
    exact h4.eventually_lt_const (by norm_num)
  filter_upwards [eventually_gt_atTop 0, hz] with β hβ hδ hφβ hMβ
  exact exists_gibbsMeasure_family_shift_of_crossingBound_lt_one hφ hM hφk hK hpart hsym hGmeas
    hGε hβ hδ hφβ hMβ

end ShiftTransport

/-! ### Theorem (18.25), last statement, without shift invariance

Georgii's `|ex 𝒢_Θ̃(βΦ)| ≥ N` needs the ergodic decomposition for the subgroup `Θ̃`; when the
partition is not `r`-symmetric that subgroup is proper, and the count is
`eventually_le_encard_extremePoints_invariantG_of_shift_range` of
`GibbsMeasure/Model/DiscreteSymmetryBreaking.lean`, resting on (14.10)/(14.18) for a subgroup
(`GibbsMeasure/Specification/InvariantDecompositionSubgroup.lean`).  The *unrestricted*
count `|ex 𝒢(βΦ)| ≥ N` is unconditional, by Corollary (7.29)
(`le_encard_extremePoints_iff` of `GibbsMeasure/Specification/ExtremeCorollaries.lean`): the `N`
Gibbs measures of (18.25) are separated by the pairwise disjoint tail events `A_n`, hence linearly
independent.  Georgii uses exactly this in 18.3.3(c).  (Intended home:
`GibbsMeasure/Model/DiscreteSymmetryBreaking.lean`.) -/

section ExtremePointsG

open Peierls

variable {N : ℕ} {φ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {Gs : Fin N → Set ((Fin 2 → Fin 2) → E)}

/-- **`|ex 𝒢(βΦ)| ≥ N`** at Georgii's explicit threshold `4 z(t(G_ε(Φ), βΦ)) < 1`. -/
theorem le_encard_extremePoints_G_of_crossingBound_lt_one [StandardBorelSpace E]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E} (hK : IsCubeConfining φ ν K)
    (hpart : IsPStablePartition φ ν Set.univ Gs) (hsym : IsPhiSymmetric φ ν Gs)
    (hGmeas : ∀ n, MeasurableSet (Gs n)) {ε : ℝ}
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, Gs n) {β : ℝ} (hβ : 0 < β)
    (hδ : 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)) < 1)
    (hφβ : Measurable fun ζ ↦ β * φ ζ) (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * φ ζ) :
    (N : ℕ∞) ≤ ((MeasureTheory.GibbsMeasure.G
      (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν hφβ hMβ)).extremePoints ℝ≥0∞).encard := by
  classical
  obtain ⟨ρ, h1, h2, h3, h4, -, -, -, -, -⟩ :=
    exists_gibbsMeasure_family_shift_of_crossingBound_lt_one hφ hM hφk hK hpart hsym hGmeas hGε
      hβ hδ hφβ hMβ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hne : (MeasureTheory.GibbsMeasure.G
      (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν hφβ hMβ)).Nonempty :=
    ⟨ρ ⟨0, hN⟩, h1 _, h2 _⟩
  refine (le_encard_extremePoints_iff hne N).2 ⟨ρ, fun n ↦ ⟨h1 n, h2 n⟩, ?_⟩
  refine linearIndependent_of_measure_eq_one_of_measure_eq_zero
    (A := fun n ↦ {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (Gs n) ω).Nonempty}) h4
    fun m n hmn ↦ ?_
  have hprob : IsProbabilityMeasure (ρ n) := h1 n
  have hcompl : ρ n {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (Gs n) ω).Nonempty}ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff (measurableSet_setOf_latticeOceanPart_nonempty (hGmeas n))]
    exact h4 n
  refine measure_mono_null (fun ω hω ↦ ?_) hcompl
  exact Set.disjoint_left.1 (hpart.disjoint_setOf_latticeOceanPart_nonempty hmn) hω

/-- **`|ex 𝒢(βΦ)| ≥ N`** for all sufficiently large `β`. -/
theorem eventually_le_encard_extremePoints_G [StandardBorelSpace E]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E} (hK : IsCubeConfining φ ν K)
    (hpart : IsPStablePartition φ ν Set.univ Gs) (hsym : IsPhiSymmetric φ ν Gs)
    (hGmeas : ∀ n, MeasurableSet (Gs n)) {ε : ℝ} (hε : 0 < ε)
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, Gs n) :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * φ ζ) (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * φ ζ),
      (N : ℕ∞) ≤ ((MeasureTheory.GibbsMeasure.G
        (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν hφβ hMβ)).extremePoints ℝ≥0∞).encard := by
  have hz : ∀ᶠ β : ℝ in atTop, 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)) < 1 := by
    have h := tendsto_crossingBound_patternWeight_localGroundStates (ν := ν) hφ hM hε
    have h4 : Tendsto (fun β : ℝ ↦ 4 * Peierls.crossingBound
        (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) h (Or.inr (by norm_num))
    exact h4.eventually_lt_const (by norm_num)
  filter_upwards [eventually_gt_atTop 0, hz] with β hβ hδ hφβ hMβ
  exact le_encard_extremePoints_G_of_crossingBound_lt_one hφ hM hφk hK hpart hsym hGmeas hGε
    hβ hδ hφβ hMβ

end ExtremePointsG

/-! ### Georgii's shift group `Θ̃ = {θ_i : i₁ + i₂ ≡ 0 mod 2}`

The staggered examples of §18.3 — 18.3.2 (the Ising antiferromagnet), 18.3.4 (the hard-core
lattice gas), 18.3.7 (anisotropic Heisenberg antiferromagnets) and 18.3.8 (Shlosman's plane
rotor) — all break the shift group down to the *even* sublattice: the iterated reflection `r^i`
fixes a staggered pattern exactly when `i₁ + i₂` is even.  That subgroup of `ℤ²` is free abelian
of rank `2`, and here it is realised as the range of the additive endomorphism
`f(a) = (a₀ + a₁, a₀ − a₁)`, which is the form in which the count
`le_encard_extremePoints_invariantG_of_shift_range` of
`GibbsMeasure/Model/DiscreteSymmetryBreaking.lean` — the last statement of Theorem (18.25) — is
stated.  (Intended home: `GibbsMeasure/Model/DiscreteSymmetryBreaking.lean`.) -/

section EvenSublattice

/-- **The even sublattice of `ℤ²` as the range of an endomorphism**: `f(a) = (a₀+a₁, a₀−a₁)`.
Its image is `{b : b₀ + b₁ even}`, because `f(a)₀ + f(a)₁ = 2a₀`, and conversely
`b = f((b₀+b₁)/2, b₀ − (b₀+b₁)/2)` whenever `b₀ + b₁` is even. -/
def evenLatticeHom : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun a := ![a 0 + a 1, a 0 - a 1]
  map_zero' := by funext k; fin_cases k <;> simp
  map_add' a b := by funext k; fin_cases k <;> simp <;> ring

@[simp] lemma evenLatticeHom_apply_zero (a : Fin 2 → ℤ) : evenLatticeHom a 0 = a 0 + a 1 := rfl

@[simp] lemma evenLatticeHom_apply_one (a : Fin 2 → ℤ) : evenLatticeHom a 1 = a 0 - a 1 := rfl

/-- Every shift in the range of `evenLatticeHom` is one of Georgii's even shifts. -/
lemma even_evenLatticeHom (a : Fin 2 → ℤ) : Even (evenLatticeHom a 0 + evenLatticeHom a 1) :=
  ⟨a 0, by simp⟩

/-- Conversely, every even shift is in the range of `evenLatticeHom`. -/
lemma exists_evenLatticeHom_eq {b : Fin 2 → ℤ} (hb : Even (b 0 + b 1)) :
    ∃ a : Fin 2 → ℤ, evenLatticeHom a = b := by
  obtain ⟨k, hk⟩ := hb
  refine ⟨![k, b 0 - k], funext fun j ↦ ?_⟩
  fin_cases j
  · simp
  · simp
    omega

/-- `f(1,0) = (1,1) ≠ 0` has infinite additive order: Georgii's "contains a non-trivial
shift". -/
lemma not_isOfFinAddOrder_evenLatticeHom :
    ¬ IsOfFinAddOrder (evenLatticeHom ![1, 0]) := by
  refine not_isOfFinAddOrder_of_isAddTorsionFree fun h ↦ ?_
  have h0 := congrFun h 0
  simp at h0

variable (E : Type*) [MeasurableSpace E]

/-- **Georgii's shift group `Θ̃ = {θ_i : i ∈ P, r^i G_n = G_n}`** for a staggered partition of the
plane: the group of shifts by the even sublattice of `ℤ²`, presented as the range of
`evenLatticeHom` so that Theorem (14.10) for a subgroup (`InvariantDecompositionSubgroup.lean`)
applies to it along the cubes of `ℤ²`. -/
def evenShiftGroup : Subgroup (Transformation (Fin 2 → ℤ) E) :=
  ((shiftHom E).comp (AddMonoidHom.toMultiplicative evenLatticeHom)).range

variable {E}

lemma mem_evenShiftGroup {τ : Transformation (Fin 2 → ℤ) E} :
    τ ∈ evenShiftGroup E ↔ ∃ a : Fin 2 → ℤ, shift E (evenLatticeHom a) = τ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Multiplicative.toAdd x, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.ofAdd a, rfl⟩

/-- **`Θ̃` is Georgii's group of even shifts**: `θ_b ∈ Θ̃` exactly when `b₁ + b₂` is even. -/
lemma mem_evenShiftGroup_iff_even {τ : Transformation (Fin 2 → ℤ) E} :
    τ ∈ evenShiftGroup E ↔ ∃ b : Fin 2 → ℤ, Even (b 0 + b 1) ∧ shift E b = τ := by
  rw [mem_evenShiftGroup]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨evenLatticeHom a, even_evenLatticeHom a, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := exists_evenLatticeHom_eq hb
    exact ⟨a, rfl⟩

lemma shift_mem_evenShiftGroup {b : Fin 2 → ℤ} (hb : Even (b 0 + b 1)) :
    shift E b ∈ evenShiftGroup E :=
  mem_evenShiftGroup_iff_even.2 ⟨b, hb, rfl⟩

end EvenSublattice

end MeasurableState

end MeasureTheory.GibbsMeasure

end

end
