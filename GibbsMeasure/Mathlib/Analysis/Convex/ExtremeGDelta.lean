/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.GDelta.MetrizableSpace
public import GibbsMeasure.Mathlib.Topology.Compactness.SigmaCompact

/-!
# The extreme points of a compact metrizable set form a `Gδ`

Let `K` be a compact subset of a Hausdorff topological module `X` over an ordered semiring `𝕜`
(with continuous addition and scalar multiplication), and suppose `K` is metrizable. The
non-extreme points of `K` are the points `a • y + b • z` with `y ≠ z` in `K` and `a, b > 0`,
`a + b = 1`: the image of an *open* subset of the compact metrizable space
`Δ × K × K` (`Δ` the one-dimensional standard simplex in `𝕜 × 𝕜`) under a continuous map.
Open subsets of a compact metrizable space are σ-compact, so `K \ K.extremePoints 𝕜` is
σ-compact (`IsCompact.isSigmaCompact_diff_extremePoints`), and if the ambient space is
metrizable, `K.extremePoints 𝕜` is a `Gδ` (`IsCompact.isGδ_extremePoints`).

No convexity of `K` is needed. For `𝕜 = ℝ`, `ℝ≥0` or `ℝ≥0∞` the hypotheses on `𝕜` hold.
-/

@[expose] public section

open Set Topology TopologicalSpace

variable {𝕜 X : Type*} [Semiring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜] [PseudoMetrizableSpace 𝕜]
  [AddCommMonoid X] [Module 𝕜 X] [TopologicalSpace X] [T2Space X] [ContinuousAdd X]
  [ContinuousSMul 𝕜 X] {K : Set X}

omit [PseudoMetrizableSpace 𝕜] in
/-- The one-dimensional standard simplex `{(a, b) : 0 ≤ a, 0 ≤ b, a + b = 1}` is compact. -/
lemma isCompact_setOf_nonneg_and_add_eq_one :
    IsCompact {p : 𝕜 × 𝕜 | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} := by
  refine (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (0 : 𝕜) 1 ×ˢ Icc (0 : 𝕜) 1)).of_isClosed_subset ?_ ?_
  · simp only [ofPred_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_eq (continuous_fst.add continuous_snd) continuous_const))
  · rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    exact ⟨⟨ha, hab ▸ le_add_of_nonneg_right hb⟩, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩⟩

/-- **Non-extreme points of a compact metrizable set are σ-compact.** If `K` is a compact subset
of a Hausdorff topological `𝕜`-module and `K` is (pseudo-)metrizable, then `K \ K.extremePoints 𝕜`
is σ-compact: it is `K ∩ g '' U` for the continuous map `g (a, b, y, z) = a • y + b • z` on
`Δ × K × K` and the open set `U = {a > 0, b > 0, y ≠ z}` of that compact metrizable space. -/
theorem IsCompact.isSigmaCompact_diff_extremePoints (hK : IsCompact K)
    [PseudoMetrizableSpace K] : IsSigmaCompact (K \ K.extremePoints 𝕜) := by
  set Δ : Set (𝕜 × 𝕜) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} with hΔ
  have : CompactSpace Δ := isCompact_iff_compactSpace.1 isCompact_setOf_nonneg_and_add_eq_one
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let g : Δ × K × K → X := fun p ↦ (p.1 : 𝕜 × 𝕜).1 • (p.2.1 : X) + (p.1 : 𝕜 × 𝕜).2 • (p.2.2 : X)
  have hg : Continuous g := by fun_prop
  set U : Set (Δ × K × K) :=
    {p | 0 < (p.1 : 𝕜 × 𝕜).1 ∧ 0 < (p.1 : 𝕜 × 𝕜).2 ∧ p.2.1 ≠ p.2.2} with hU
  have hUo : IsOpen U := by
    simp only [hU, ofPred_and]
    have h₁ : Continuous fun p : Δ × K × K ↦ (p.1 : 𝕜 × 𝕜) :=
      continuous_subtype_val.comp continuous_fst
    exact (isOpen_lt continuous_const h₁.fst).inter ((isOpen_lt continuous_const h₁.snd).inter
      (isOpen_ne_fun continuous_snd.fst continuous_snd.snd))
  have hKU : K \ K.extremePoints 𝕜 = K ∩ g '' U := by
    ext x
    simp only [mem_sdiff, mem_inter_iff, mem_extremePoints, not_and, mem_image, hU, mem_ofPred_eq,
      g]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, ?_⟩
      have h' := h hx
      push Not at h'
      obtain ⟨x₁, hx₁, x₂, hx₂, ⟨a, b, ha, hb, hab, rfl⟩, hne⟩ := h'
      refine ⟨(⟨(a, b), ha.le, hb.le, hab⟩, ⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩), ⟨ha, hb, ?_⟩, rfl⟩
      intro h12
      obtain rfl : x₁ = x₂ := congrArg Subtype.val h12
      have hx' : a • x₁ + b • x₁ = x₁ := by rw [← add_smul, hab, one_smul]
      exact hne hx'.symm hx'.symm
    · rintro ⟨hx, ⟨⟨⟨a, b⟩, ha0, hb0, hab⟩, ⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩, ⟨ha, hb, hne⟩, rfl⟩
      refine ⟨hx, fun _ h ↦ ?_⟩
      obtain ⟨h₁, h₂⟩ := h x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, rfl⟩
      exact hne (Subtype.ext (h₁.trans h₂.symm))
  rw [hKU]
  exact (hUo.isSigmaCompact.image hg).inter_left hK.isClosed

/-- **The extreme points of a compact set in a metrizable topological module form a `Gδ`.**
(Georgii, Comment (14.13): for a compact metrizable convex set, `ex K` is a `Gδ` in `K`.) -/
theorem IsCompact.isGδ_extremePoints [PseudoMetrizableSpace X] (hK : IsCompact K) :
    IsGδ (K.extremePoints 𝕜) := by
  rw [← sdiff_sdiff_cancel_left (extremePoints_subset (𝕜 := 𝕜) (A := K))]
  exact hK.isClosed.isGδ_diff hK.isSigmaCompact_diff_extremePoints
