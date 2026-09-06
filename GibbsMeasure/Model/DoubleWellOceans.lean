/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.AnisotropicAntiferroOceans

/-!
# Georgii 18.3.9: unbounded spin systems with double-well potentials

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.9.  The state space is `E = ℝ` and the
`C`-potential is **(18.38)**

`Φ_C = ∑_{{i,j} ⊆ C, |i-j|=1} u(σ_i - σ_j) + ∑_{i ∈ C} v(σ_i)`,

with `u, v : ℝ → ℝ` even and continuous, `u` *attractive* (its minimum is attained at `0` only)
and `v` a *double well*: `v(x) → ∞` as `|x| → ∞`, and `v(0) > min v`, so that the minimisers of
`v` come in pairs `±a`.

## The a priori measure

Georgii takes `λ` = Lebesgue measure and imposes `λ(e^{-βv}) < ∞` for all `β > 0`; since `λ` is
infinite, Theorem (18.25) does not apply directly, and he repairs this by passing to the finite
a priori measure `λ̄ = e^{-4v} λ` and the potential `Φ̄` obtained from `Φ` by replacing `v` with
`v̄ = (1 - 1/β)v`: as every site of `ℤ²` lies in exactly `4 = 2^d` cubes,
`e^{-βΦ̄} dλ̄ = e^{-βΦ} dλ`, so the two Gibbs specifications coincide.

Here the theorem is proved for an **arbitrary a priori probability measure `ν` on `ℝ` with full
support, invariant under `x ↦ -x`** — Georgii's normalised `λ̄` (which is symmetric because `v`
is even, and has full support because its density is positive) is one such `ν`, and the
conclusion is Georgii's with `v` replaced by his `v̄`, which satisfies the same two hypotheses.
The one step of his argument which is *not* formalised is the final identification of
`γ^{βΦ̄, λ̄}` with `γ^{βΦ, λ}`: `cubeGibbsSpec` of
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean` is defined only for a *probability* a
priori measure, so `𝒢(βΦ)` for Lebesgue `λ` — the left-hand side of Georgii's last sentence — is
not expressible in the tree at all.  Everything that is expressible is proved.

## Main results

* `doubleWellCube`, `doubleWellCube_eq_min_iff` — the interaction (18.38) and **Georgii's "the
  local ground states of `Φ` consist of all configurations `(x x / x x)` with `v(x) = min v`"**;
  `localGroundEnergy_doubleWellCube` is `m_Φ = 4u(0) + 4 min v`.
* `doubleWellG` — **Georgii's partition `{G_+, G_-}` "according to whether `x > 0` or `x < 0`"**,
  with `isPStablePartition_doubleWellG` its stability (18.23)(a)(ii) and
  `isPhiSymmetric_doubleWellG` its `Φ`-symmetry through the spin reflection `τ : ω ↦ -ω`.
* `isCompact_sublevel_doubleWellCube` — the sublevel sets of `Φ_C` are compact, which is what
  replaces the compactness of the state space in `exists_pos_localGroundStates_subset_of_isCompact`
  and is where `v(x) → ∞` is used.
* `isCubeConfining_doubleWellCube` — **condition (iv) of Georgii (17.18) in its second
  alternative**, with `K_ℓ = [-(ℓ+1), ℓ+1]`: this is the hypothesis of (17.18) that an unbounded
  `Φ_C` must satisfy, and the reason this example is not covered by `isCubeConfining_univ`.
* `eventually_two_le_encard_extremePoints_doubleWell` and
  `eventually_exists_doubleWell_gibbsMeasure_pair` — **Georgii's conclusion**: for `β` large
  enough `𝒢(βΦ)` contains two mutually singular, shift-invariant Gibbs measures exchanged by the
  spin reflection, so `|ex 𝒢_Θ(βΦ)| ≥ 2`.
-/

@[expose] public section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Georgii (18.38): the interaction -/

variable (u v : ℝ → ℝ) (d : ℕ) in
/-- **Georgii (18.38)**: the `C`-potential of an unbounded spin system with attractive
nearest-neighbour interaction `u` and self-potential `v`. -/
def doubleWellCube : ((Fin d → Fin 2) → ℝ) → ℝ := fun ζ ↦
  cubeBondSum d (fun x y ↦ u (x - y)) ζ + cubeSiteSum d v ζ

variable {u v : ℝ → ℝ} {d : ℕ}

lemma continuous_doubleWellCube (hu : Continuous u) (hv : Continuous v) :
    Continuous (doubleWellCube u v d) := by
  refine Continuous.add (continuous_cubeBondSum ?_) ?_
  · exact hu.comp (continuous_fst.sub continuous_snd)
  · unfold cubeSiteSum
    exact continuous_finsetSum _ fun c _ ↦ hv.comp (continuous_apply c)

lemma measurable_doubleWellCube (hu : Continuous u) (hv : Continuous v) :
    Measurable (doubleWellCube u v d) := (continuous_doubleWellCube hu hv).measurable

/-- **Condition (iii) of Georgii (17.18)** for (18.38). -/
lemma doubleWellCube_cubeRefl (k : Fin d) (ζ : (Fin d → Fin 2) → ℝ) :
    doubleWellCube u v d (cubeRefl ℝ k ζ) = doubleWellCube u v d ζ := by
  simp only [doubleWellCube, cubeBondSum_cubeRefl, cubeSiteSum_cubeRefl]

section Bounds

variable {a : ℝ} (humin : ∀ x, u 0 ≤ u x) (hvmin : ∀ x, v a ≤ v x)

include humin hvmin

/-- **Georgii's `m_Φ = 4u(0) + 4 min v`** in the plane: the bond term is at least `4u(0)` and
the site term at least `4 min v`. -/
lemma le_doubleWellCube (ζ : (Fin 2 → Fin 2) → ℝ) :
    4 * u 0 + 4 * v a ≤ doubleWellCube u v 2 ζ := by
  have hb := cubeBondSum_ge (d := 2) (ψ := fun x y ↦ u (x - y)) (m := u 0) (ζ := ζ)
    fun c c' ↦ humin _
  have hs := cubeSiteSum_ge (d := 2) (v := v) (m := v a) (ζ := ζ) fun c ↦ hvmin _
  norm_num at hb hs
  rw [doubleWellCube]
  linarith

/-- The value of (18.38) at a constant ground state. -/
lemma doubleWellCube_const (x : ℝ) (hx : v x = v a) :
    doubleWellCube u v 2 (fun _ ↦ x) = 4 * u 0 + 4 * v a := by
  have hb : cubeBondSum 2 (fun x y ↦ u (x - y)) (fun _ ↦ x) = 4 * u 0 := by
    have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * u 0)) = 4 * u 0 := by
      push_cast; ring
    rw [← hval]
    exact (cubeBondSum_eq_iff_forall_adj (fun x y ↦ humin _) _).2 fun c c' _ ↦ by
      simp only [sub_self]
  have hs : cubeSiteSum 2 v (fun _ ↦ x) = 4 * v a := by
    rw [cubeSiteSum_def, sum_univ_cubeCorners, hx]
    ring
  rw [doubleWellCube, hb, hs]

end Bounds

/-- **Georgii's "the local ground states of `Φ` consist of all configurations `(x x / x x)` with
`v(x) = min v`"**: the attractiveness of `u` forces the configuration to be constant (the cube is
connected) and the site term then forces the common value to minimise `v`. -/
theorem doubleWellCube_eq_min_iff {a : ℝ} (humin : ∀ x, u 0 ≤ u x)
    (humin' : ∀ x, x ≠ 0 → u 0 < u x) (hvmin : ∀ x, v a ≤ v x) (ζ : (Fin 2 → Fin 2) → ℝ) :
    doubleWellCube u v 2 ζ = 4 * u 0 + 4 * v a ↔
      (∃ x, ζ = fun _ ↦ x) ∧ ∀ c, v (ζ c) = v a := by
  have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * u 0)) = 4 * u 0 := by
      push_cast; ring
  have hb := cubeBondSum_ge (d := 2) (ψ := fun x y ↦ u (x - y)) (m := u 0) (ζ := ζ)
    fun c c' ↦ humin _
  have hs := cubeSiteSum_ge (d := 2) (v := v) (m := v a) (ζ := ζ) fun c ↦ hvmin _
  rw [hval] at hb
  norm_num at hs
  constructor
  · intro heq
    rw [doubleWellCube] at heq
    have hbeq : cubeBondSum 2 (fun x y ↦ u (x - y)) ζ = 4 * u 0 := by linarith
    have hseq : cubeSiteSum 2 v ζ = 4 * v a := by linarith
    refine ⟨⟨ζ 0, funext fun c ↦ ?_⟩, fun c ↦ ?_⟩
    · refine cubeGraph_forall_eq_of_adj (fun c c' hcc' ↦ ?_) c
      have h := (cubeBondSum_eq_iff_forall_adj (fun x y ↦ humin _) ζ).1 (by rw [hbeq, hval])
        c c' hcc'
      by_contra hne
      exact absurd h (ne_of_gt (humin' _ (sub_ne_zero.2 hne)))
    · by_contra hne
      have hlt : v a < v (ζ c) := lt_of_le_of_ne (hvmin _) (Ne.symm hne)
      have hsum : cubeSiteSum 2 v ζ
          = ∑ c' : Fin 2 → Fin 2, v (ζ c') := rfl
      have hgt : 4 * v a < ∑ c' : Fin 2 → Fin 2, v (ζ c') := by
        rw [sum_univ_cubeCorners]
        rcases sqCorner_surjective c with rfl | rfl | rfl | rfl <;>
          [skip; skip; skip; skip] <;>
          · have h1 := hvmin (ζ (sqCorner 0 0))
            have h2 := hvmin (ζ (sqCorner 1 0))
            have h3 := hvmin (ζ (sqCorner 0 1))
            have h4 := hvmin (ζ (sqCorner 1 1))
            linarith
      rw [hsum] at hseq
      linarith
  · rintro ⟨⟨x, rfl⟩, hvx⟩
    exact doubleWellCube_const humin hvmin x (hvx 0)


/-! ### The sublevel sets of `Φ_C` are compact -/

/-- The attractiveness of `u` in the form used below. -/
lemma umin_le (humin' : ∀ x, x ≠ 0 → u 0 < u x) (x : ℝ) : u 0 ≤ u x := by
  rcases eq_or_ne x 0 with rfl | h
  · exact le_rfl
  · exact (humin' x h).le

/-- Three of the four site energies are at least the minimum. -/
lemma add_three_le_cubeSiteSum {a : ℝ} (hvmin : ∀ x, v a ≤ v x) (ζ : (Fin 2 → Fin 2) → ℝ)
    (c₀ : Fin 2 → Fin 2) : v (ζ c₀) + 3 * v a ≤ cubeSiteSum 2 v ζ := by
  rw [cubeSiteSum_def, sum_univ_cubeCorners]
  have h1 := hvmin (ζ (sqCorner 0 0))
  have h2 := hvmin (ζ (sqCorner 1 0))
  have h3 := hvmin (ζ (sqCorner 0 1))
  have h4 := hvmin (ζ (sqCorner 1 1))
  rcases sqCorner_surjective c₀ with rfl | rfl | rfl | rfl <;> linarith

/-- **The spins of a configuration of bounded energy are bounded**: this is where Georgii's
hypothesis `v(x) → ∞` enters.  It gives at once the compactness of the sublevel sets of `Φ_C`
and condition (iv) of (17.18). -/
theorem exists_bound_doubleWellCube {a : ℝ} (humin : ∀ x, u 0 ≤ u x) (hvmin : ∀ x, v a ≤ v x)
    (hvco : ∀ M : ℝ, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → M ≤ v x) (M : ℝ) :
    ∃ R : ℝ, ∀ ζ : (Fin 2 → Fin 2) → ℝ, doubleWellCube u v 2 ζ ≤ M → ∀ c, |ζ c| < R := by
  obtain ⟨R, hR⟩ := hvco (M - 4 * u 0 - 3 * v a + 1)
  refine ⟨R, fun ζ hζ c ↦ ?_⟩
  by_contra hle
  rw [not_lt] at hle
  have hb := cubeBondSum_ge (d := 2) (ψ := fun x y ↦ u (x - y)) (m := u 0) (ζ := ζ)
    fun c c' ↦ humin _
  norm_num at hb
  have hs := add_three_le_cubeSiteSum hvmin ζ c
  have hv := hR (ζ c) hle
  rw [doubleWellCube] at hζ
  linarith

/-- The sublevel sets of the interaction (18.38) are compact: they are closed by continuity and
bounded by `exists_bound_doubleWellCube`. -/
theorem isCompact_sublevel_doubleWellCube {a : ℝ} (hu : Continuous u) (hv : Continuous v)
    (humin : ∀ x, u 0 ≤ u x) (hvmin : ∀ x, v a ≤ v x)
    (hvco : ∀ M : ℝ, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → M ≤ v x) (M : ℝ) :
    IsCompact {ζ : (Fin 2 → Fin 2) → ℝ | doubleWellCube u v 2 ζ ≤ M} := by
  obtain ⟨R, hR⟩ := exists_bound_doubleWellCube humin hvmin hvco M
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_doubleWellCube hu hv) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : (Fin 2 → Fin 2) → ℝ)) (r := R)).subset ?_
  intro ζ hζ
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg ?_).2 fun c ↦ ?_
  · rcases isEmpty_or_nonempty (Fin 2 → Fin 2) with h | h
    · exact absurd (h.false (0 : Fin 2 → Fin 2)) not_false
    · exact le_of_lt (lt_of_le_of_lt (abs_nonneg (ζ 0)) (hR ζ hζ 0))
  · rw [Real.norm_eq_abs]
    exact (hR ζ hζ c).le

/-! ### Georgii's partition `{G_+, G_-}` -/

/-- **Georgii's partition of the local ground states of (18.38)** "according to whether `x > 0`
or `x < 0`": the configurations all of whose spins are positive, resp. negative. -/
def doubleWellG (n : Fin 2) : Set ((Fin 2 → Fin 2) → ℝ) := {ζ | ∀ c, 0 < anisoSign n * ζ c}

lemma mem_doubleWellG {n : Fin 2} {ζ : (Fin 2 → Fin 2) → ℝ} :
    ζ ∈ doubleWellG n ↔ ∀ c, 0 < anisoSign n * ζ c := Iff.rfl

lemma isOpen_doubleWellG (n : Fin 2) : IsOpen (doubleWellG n) := by
  have h : doubleWellG n = ⋂ c, {ζ : (Fin 2 → Fin 2) → ℝ | 0 < anisoSign n * ζ c} := by
    ext ζ; simp [doubleWellG, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun c ↦
    isOpen_lt continuous_const (continuous_const.mul (continuous_apply c))

lemma measurableSet_doubleWellG (n : Fin 2) : MeasurableSet (doubleWellG n) :=
  (isOpen_doubleWellG n).measurableSet

/-- **`{G_+, G_-}` is `r`-symmetric**: the reflections of the cube only permute the corners, so
Georgii's shift group `Θ̃` is all of `Θ` here. -/
lemma isRSymmetric_doubleWellG (n : Fin 2) : IsRSymmetric ℝ (doubleWellG n) := by
  intro k
  ext ζ
  simp only [Set.mem_preimage, mem_doubleWellG, cubeRefl_apply]
  exact ⟨fun h c ↦ by simpa [cubeSiteRefl_cubeSiteRefl] using h (cubeSiteRefl k c),
    fun h c ↦ h _⟩

/-- **Georgii's stability of `{G_+, G_-}`**: the two sets are separated by the sign of any one
spin of a face. -/
theorem pairwise_disjoint_faceRestrict_doubleWellG (k : Fin 2) (a : Fin 2) :
    Pairwise fun m n ↦ Disjoint (faceRestrict ℝ k a '' doubleWellG m)
      (faceRestrict ℝ k a '' doubleWellG n) := by
  intro m n hmn
  rw [Set.disjoint_left]
  rintro g ⟨ζ, hζ, rfl⟩ ⟨ξ, hξ, hfe⟩
  have hcorner : ζ (fun _ ↦ a) = ξ (fun _ ↦ a) :=
    (congrFun hfe (⟨fun _ ↦ a, rfl⟩ : {c : Fin 2 → Fin 2 // c k = a})).symm
  have h1 := hζ (fun _ ↦ a)
  have h2 := hξ (fun _ ↦ a)
  rw [← hcorner] at h2
  rw [anisoSign_eq_neg_of_ne hmn] at h1
  nlinarith [h1, h2]

/-- **Georgii's `G_ε(Φ) ⊆ G_+ ∪ G_-` for small `ε`** for (18.38): the exact local ground states
are the constants at a minimiser of `v`, and `0` is not one of them. -/
theorem exists_localGroundStates_subset_doubleWellG {a : ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] [(cubeMeasure 2 ν).IsOpenPosMeasure] (hu : Continuous u)
    (hv : Continuous v) (humin' : ∀ x, x ≠ 0 → u 0 < u x) (hvmin : ∀ x, v a ≤ v x)
    (hvco : ∀ M : ℝ, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → M ≤ v x) (hva : v a < v 0) :
    ∃ ε > 0, localGroundStates (doubleWellCube u v 2) ν ε ⊆ ⋃ n, doubleWellG n := by
  have humin := umin_le humin'
  refine exists_pos_localGroundStates_subset_of_isCompact (continuous_doubleWellCube hu hv)
    (le_doubleWellCube humin hvmin) (ζ₀ := fun _ ↦ a)
    (doubleWellCube_const humin hvmin a rfl) one_pos
    (isCompact_sublevel_doubleWellCube hu hv humin hvmin hvco _)
    (isOpen_iUnion fun n ↦ isOpen_doubleWellG n) ?_
  intro ζ hζ
  obtain ⟨⟨x, rfl⟩, hvx⟩ := (doubleWellCube_eq_min_iff humin humin' hvmin _).1 hζ
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hvx
    exact absurd (hvx 0) (ne_of_gt hva)
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · exact Set.mem_iUnion.2 ⟨1, fun c ↦ by simp only [anisoSign_one]; linarith⟩
  · exact Set.mem_iUnion.2 ⟨0, fun c ↦ by simp only [anisoSign_zero]; linarith⟩

/-! ### Georgii's spin reflection `τ : ω ↦ -ω` -/

/-- **Georgii's spin reflection `τ : ω ↦ -ω`**, a pure spin transformation (18.21). -/
def doubleWellFlip : CubeTransformation ℝ 2 :=
  CubeTransformation.pureSpin fun _ ↦ (MeasurableEquiv.neg ℝ)

@[simp] lemma onCube_doubleWellFlip (ζ : (Fin 2 → Fin 2) → ℝ) (c : Fin 2 → Fin 2) :
    doubleWellFlip.onCube.toFun ζ c = -ζ c := by
  rw [doubleWellFlip, CubeTransformation.pureSpin_onCube_toFun_apply]
  rfl

/-- `Φ_C ∘ τ = Φ_C` for (18.38): `u` and `v` are even. -/
lemma doubleWellCube_onCube_doubleWellFlip (hueven : ∀ x, u (-x) = u x)
    (hveven : ∀ x, v (-x) = v x) (ζ : (Fin 2 → Fin 2) → ℝ) :
    doubleWellCube u v 2 (doubleWellFlip.onCube.toFun ζ) = doubleWellCube u v 2 ζ := by
  have hbond : cubeBondSum 2 (fun x y ↦ u (x - y)) (doubleWellFlip.onCube.toFun ζ)
      = cubeBondSum 2 (fun x y ↦ u (x - y)) ζ := by
    refine cubeBondSum_onCube _ (fun c c' _ x y ↦ ?_) ζ
    change u (-x - -y) = u (x - y)
    rw [show -x - -y = -(x - y) by ring, hueven]
  have hsite : cubeSiteSum 2 v (doubleWellFlip.onCube.toFun ζ) = cubeSiteSum 2 v ζ := by
    refine cubeSiteSum_onCube _ (fun c x ↦ ?_) ζ
    change v (-x) = v x
    rw [hveven]
  rw [doubleWellCube, doubleWellCube, hbond, hsite]

lemma isSymmetry_doubleWellFlip {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ ↦ -x) ν ν) (hueven : ∀ x, u (-x) = u x)
    (hveven : ∀ x, v (-x) = v x) :
    doubleWellFlip.IsSymmetry (doubleWellCube u v 2) ν :=
  CubeTransformation.IsSymmetry.of_apply_onCube doubleWellCube_cubeRefl (fun c ↦ hν)
    (doubleWellCube_onCube_doubleWellFlip hueven hveven)

/-- **Georgii's "`G_+` and `G_-` are related to each other by the spin reflection `τ`".** -/
lemma image_onCube_doubleWellFlip_doubleWellG {m n : Fin 2} (hmn : m ≠ n) :
    doubleWellFlip.onCube.toFun '' doubleWellG m = doubleWellG n := by
  have hstep : ∀ p q : Fin 2, p ≠ q → ∀ ζ : (Fin 2 → Fin 2) → ℝ, ζ ∈ doubleWellG p →
      doubleWellFlip.onCube.toFun ζ ∈ doubleWellG q := by
    intro p q hpq ζ hζ c
    have h := hζ c
    rw [onCube_doubleWellFlip, anisoSign_eq_neg_of_ne (Ne.symm hpq)]
    nlinarith [h]
  refine Set.Subset.antisymm ?_ fun ξ hξ ↦ ⟨doubleWellFlip.onCube.toFun ξ,
    hstep n m (Ne.symm hmn) ξ hξ, ?_⟩
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact hstep m n hmn ζ hζ
  · funext c
    rw [onCube_doubleWellFlip, onCube_doubleWellFlip, neg_neg]

lemma isPhiSymmetric_doubleWellG {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ ↦ -x) ν ν) (hueven : ∀ x, u (-x) = u x)
    (hveven : ∀ x, v (-x) = v x) :
    IsPhiSymmetric (doubleWellCube u v 2) ν doubleWellG :=
  isPhiSymmetric_of_ne doubleWellCube_cubeRefl fun m n hmn ↦
    ⟨doubleWellFlip, isSymmetry_doubleWellFlip hν hueven hveven,
      image_onCube_doubleWellFlip_doubleWellG hmn⟩

/-! ### Condition (iv) of Georgii (17.18): the confining sets `K_ℓ` -/

/-- **Georgii's condition (17.18)(iv), second alternative**, for the unbounded interaction
(18.38): with `K_ℓ = [-(ℓ+1), ℓ+1]`, `Φ_C` is bounded on `K_ℓ^C` and tends to `∞` outside. -/
theorem isCubeConfining_doubleWellCube {a : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    [ν.IsOpenPosMeasure] (hu : Continuous u) (hv : Continuous v) (humin : ∀ x, u 0 ≤ u x)
    (hvmin : ∀ x, v a ≤ v x) (hvco : ∀ M : ℝ, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → M ≤ v x) :
    IsCubeConfining (doubleWellCube u v 2) ν fun ℓ : ℕ ↦ Set.Icc (-(ℓ + 1 : ℝ)) (ℓ + 1) where
  measurableSet ℓ := measurableSet_Icc
  measure_pos ℓ := by
    refine lt_of_lt_of_le ?_ (measure_mono (Set.Ioo_subset_Icc_self (a := -(ℓ + 1 : ℝ))))
    have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
    exact isOpen_Ioo.measure_pos ν ⟨0, Set.mem_Ioo.2 ⟨by linarith, by linarith⟩⟩
  bddOn ℓ := by
    have hcpt : IsCompact (cubePi 2 ℝ (Set.Icc (-(ℓ + 1 : ℝ)) (ℓ + 1))) := by
      have h : cubePi 2 ℝ (Set.Icc (-(ℓ + 1 : ℝ)) (ℓ + 1))
          = Set.univ.pi fun _ : Fin 2 → Fin 2 ↦ Set.Icc (-(ℓ + 1 : ℝ)) (ℓ + 1) := by
        ext ζ
        simp only [cubePi, Set.mem_ofPred_eq, Set.mem_univ_pi]
      rw [h]
      exact isCompact_univ_pi fun _ ↦ isCompact_Icc
    obtain ⟨c, hc⟩ := hcpt.exists_bound_of_continuousOn
      (continuous_doubleWellCube hu hv).continuousOn
    exact ⟨c, fun ζ hζ ↦ by simpa [Real.norm_eq_abs] using hc ζ hζ⟩
  tendsto_atTop c := by
    obtain ⟨R, hR⟩ := hvco (c - 4 * u 0 - 3 * v a)
    refine ⟨⌈R⌉₊, fun ℓ hℓ ζ hζ ↦ ?_⟩
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, ζ c₀ ∉ Set.Icc (-(ℓ + 1 : ℝ)) (ℓ + 1) := by
      by_contra hcon
      push Not at hcon
      exact hζ hcon
    have habs : R ≤ |ζ c₀| := by
      rw [Set.mem_Icc, not_and_or] at hc₀
      have hRl : R ≤ (ℓ : ℝ) + 1 := by
        have h1 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
        have h2 : ((⌈R⌉₊ : ℕ) : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
        linarith
      rcases hc₀ with h | h
      · rw [not_le] at h
        calc R ≤ (ℓ : ℝ) + 1 := hRl
          _ ≤ -ζ c₀ := by linarith
          _ ≤ |ζ c₀| := neg_le_abs _
      · rw [not_le] at h
        calc R ≤ (ℓ : ℝ) + 1 := hRl
          _ ≤ ζ c₀ := h.le
          _ ≤ |ζ c₀| := le_abs_self _
    have hb := cubeBondSum_ge (d := 2) (ψ := fun x y ↦ u (x - y)) (m := u 0) (ζ := ζ)
      fun c c' ↦ humin _
    norm_num at hb
    have hs := add_three_le_cubeSiteSum hvmin ζ c₀
    have hvR := hR (ζ c₀) habs
    rw [doubleWellCube]
    linarith


/-! ### Georgii 18.3.9: the conclusion -/

section Conclusion

variable {a : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure]
  (hu : Continuous u) (hueven : ∀ x, u (-x) = u x) (humin' : ∀ x, x ≠ 0 → u 0 < u x)
  (hv : Continuous v) (hveven : ∀ x, v (-x) = v x) (hvmin : ∀ x, v a ≤ v x)
  (hvco : ∀ M : ℝ, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → M ≤ v x) (hva : v a < v 0)
  (hν : MeasurePreserving (fun x : ℝ ↦ -x) ν ν)

include hu hueven humin' hv hveven hvmin hvco hva hν

/-- **Georgii's "`Φ` exhibits a `τ`-symmetric stable ground state degeneracy of order two"** for
(18.38). -/
theorem isPStablePartition_doubleWellG :
    IsPStablePartition (doubleWellCube u v 2) ν Set.univ doubleWellG where
  exists_localGroundStates_subset :=
    exists_localGroundStates_subset_doubleWellG hu hv humin' hvmin hvco hva
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_doubleWellG k a

/-- **Georgii 18.3.9, unbounded spins with a double-well self-potential (18.38).**  *All
hypotheses of Theorem (18.25) are satisfied, and `|ex 𝒢_Θ(βΦ)| ≥ 2` when `β` is large enough.*

The local ground states are the constant configurations at a minimiser of `v`
(`doubleWellCube_eq_min_iff`), which split into the positive and the negative ones because
`v(0) > min v`; the partition is stable because the two sets are separated by the sign of any
spin, `Φ`-symmetric through the spin reflection `τ : ω ↦ -ω`, and `r`-symmetric, so Georgii's
`Θ̃` is all of `Θ`.  Condition (17.18)(iv) holds in its second alternative
(`isCubeConfining_doubleWellCube`), which is what the unboundedness of `Φ_C` requires. -/
theorem eventually_two_le_encard_extremePoints_doubleWell :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * doubleWellCube u v 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * doubleWellCube u v 2 ζ),
      (2 : ℕ∞) ≤ ((invariantG (cubeGibbsSpec ℝ (fun ζ ↦ β * doubleWellCube u v 2 ζ) ν hφβ hMβ)
        (shiftGroup (Fin 2 → ℤ) ℝ)).extremePoints ℝ≥0∞).encard := by
  obtain ⟨ε, hε, hGε⟩ := exists_localGroundStates_subset_doubleWellG (ν := ν) hu hv humin' hvmin
    hvco hva
  exact eventually_le_encard_extremePoints (E := ℝ) (φ := doubleWellCube u v 2) (ν := ν)
    (G := doubleWellG) (measurable_doubleWellCube hu hv)
    (le_doubleWellCube (umin_le humin') hvmin) doubleWellCube_cubeRefl
    (isCubeConfining_doubleWellCube hu hv (umin_le humin') hvmin hvco)
    (isPStablePartition_doubleWellG hu hueven humin' hv hveven hvmin hvco hva hν)
    (isPhiSymmetric_doubleWellG hν hueven hveven) measurableSet_doubleWellG
    isRSymmetric_doubleWellG hε hGε

open Peierls in
/-- **Georgii 18.3.9**, the two Gibbs measures themselves: for `β` large enough there are two
mutually singular shift-invariant Gibbs measures for `βΦ`, carried by the configurations whose
positive resp. negative cubes percolate in an ocean, and exchanged by the spin reflection. -/
theorem eventually_exists_doubleWell_gibbsMeasure_pair :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * doubleWellCube u v 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * doubleWellCube u v 2 ζ),
      ∃ μ : Fin 2 → Measure ((Fin 2 → ℤ) → ℝ),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure
          (cubeGibbsSpec ℝ (fun ζ ↦ β * doubleWellCube u v 2 ζ) ν hφβ hMβ) (μ n)) ∧
        (μ 0).MutuallySingular (μ 1) ∧
        (∀ n, μ n {ω | (latticeOceanPart ℝ (doubleWellG n) ω).Nonempty} = 1) ∧
        (∀ (n : Fin 2) (b : Fin 2 → ℤ), MeasurePreserving (shift ℝ b).toFun (μ n) (μ n)) ∧
        (μ 0).map (doubleWellFlip.onLattice ℝ).toFun = μ 1 ∧
        (μ 1).map (doubleWellFlip.onLattice ℝ).toFun = μ 0 := by
  obtain ⟨ε, hε, hGε⟩ := exists_localGroundStates_subset_doubleWellG (ν := ν) hu hv humin' hvmin
    hvco hva
  filter_upwards [eventually_exists_gibbsMeasure_family_shift (E := ℝ)
    (φ := doubleWellCube u v 2) (ν := ν) (G := doubleWellG) (measurable_doubleWellCube hu hv)
    (le_doubleWellCube (umin_le humin') hvmin) doubleWellCube_cubeRefl
    (isCubeConfining_doubleWellCube hu hv (umin_le humin') hvmin hvco)
    (isPStablePartition_doubleWellG hu hueven humin' hv hveven hvmin hvco hva hν)
    (isPhiSymmetric_doubleWellG hν hueven hveven) measurableSet_doubleWellG hε hGε]
    with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, h4, -, h6, -, h8, -⟩ := hβ hφβ hMβ
  have hflipβ : doubleWellFlip.IsSymmetry (fun ζ ↦ β * doubleWellCube u v 2 ζ) ν :=
    (isSymmetry_doubleWellFlip hν hueven hveven).const_mul doubleWellCube_cubeRefl β
  exact ⟨ρ, h1, h2, h3 (by decide), h4,
    fun n b ↦ h6 n b ((isRSymmetric_doubleWellG n).preimage_tauPow _),
    h8 0 1 _ hflipβ (image_onCube_doubleWellFlip_doubleWellG (by decide)),
    h8 1 0 _ hflipβ (image_onCube_doubleWellFlip_doubleWellG (by decide))⟩

end Conclusion

end MeasureTheory.GibbsMeasure

end

end
