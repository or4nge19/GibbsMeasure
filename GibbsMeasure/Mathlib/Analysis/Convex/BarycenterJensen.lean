/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Convex.Barycenter
public import Mathlib.Analysis.Convex.Approximation
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Jensen's inequality for barycentres, and strongly affine functions

Let `K` be a compact convex subset of a locally convex Hausdorff real topological vector space and
let `μ` be a probability measure carried by `K` with barycentre `x`
(`MeasureTheory.IsBarycenter`). This file proves the two halves of Jensen's inequality in the
barycentric formulation, and combines them into the statement that an affine lower semicontinuous
function is *strongly affine*: it commutes with barycentres.

## Main statements

* `MeasureTheory.IsBarycenter.le_integral_of_convexOn`, the convex half: for `f` convex and lower
  semicontinuous on `K`, `f x ≤ ∫ f dμ`. This is the elementary half: `f` is the pointwise
  supremum of the continuous affine functions below it (`ConvexOn.exists_affine_le_of_lt`), and
  each of those integrates to its value at `x`.
* `MeasureTheory.IsBarycenter.integral_le_of_concaveOn`, the concave half: for `f` concave and
  lower semicontinuous on `K`, `∫ f dμ ≤ f x`. This is the hard half — a concave *lower*
  semicontinuous function is **not** an infimum of continuous affine functions — and it is proved
  by a direct approximation: `μ` is split along a finite partition adapted both to the level sets
  of `f` and to a covering of `K` by small convex sets, so that `x` becomes an honest finite convex
  combination `∑ pᵢ • yᵢ` with `f yᵢ` bounded below by the level of the `i`-th cell.
* `MeasureTheory.IsBarycenter.integral_eq_of_affine`, **Phelps' Lemma 9.7**: an affine lower
  semicontinuous function satisfies `∫ f dμ = f x`.
* `MeasureTheory.IsBarycenter.lintegral_eq_of_affineENNReal`, the `ℝ≥0∞`-valued form, which is the
  one a functional such as Georgii's excess free energy `𝒜(· | Φ) : 𝒫_Θ → [0, ∞]` needs: no
  integrability or boundedness hypothesis, and the value `∞` is allowed. Its two halves are
  `MeasureTheory.IsBarycenter.le_lintegral_of_convexENNReal` — which rests on the `[0, ∞]`-valued
  minorant lemma `ConvexOnENNReal.exists_affine_le_of_lt`, a Hahn-Banach separation from the
  epigraph `epigraphENNReal` — and
  `MeasureTheory.IsBarycenter.lintegral_le_of_concaveENNReal`.
* `iInf_closedConvexHull_eq_iInf_closure`, **Georgii (15.54)**: for a concave lower
  semicontinuous `g : K → [0, ∞]`, the infimum over the closed convex hull of `C ⊆ K` equals the
  infimum over the closure of `C`.

## Implementation notes

The concave half needs inner regularity of `μ` (`MeasureTheory.Measure.WeaklyRegular`): the level
set `{f > t}` is only *relatively* open in `K`, so before covering it by small convex sets one has
to shrink it to a closed — hence compact — subset. Weak regularity is automatic for a finite
measure on a pseudometrizable space
(`MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure`), which covers
every application in this library.

Relative (rather than ambient) semicontinuity is what the applications provide: a functional such
as the specific entropy is defined on probability measures only, and extending it off `K` destroys
either the semicontinuity or the affineness. All statements below therefore use
`LowerSemicontinuousOn f K` and `ConvexOn ℝ K f` / `ConcaveOn ℝ K f`.

## References

* R. R. Phelps, *Lectures on Choquet's Theorem*, Lecture Notes in Mathematics 1757, Springer 2001.
* H.-O. Georgii, *Gibbs Measures and Phase Transitions*, 2nd edition, Step 3 of the proof of
  Theorem (15.45).
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal NNReal Pointwise

namespace MeasureTheory

section Jensen

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [T2Space V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  {K : Set V} {μ : Measure V} {x : V} {f : V → ℝ}

/-! ### The convex half of Jensen's inequality -/

/-- **Jensen's inequality for a barycentre, convex case.** If `f` is convex and lower
semicontinuous on a compact convex set `K` carrying the probability measure `μ`, then the value of
`f` at the barycentre is at most its `μ`-average.

The proof is the elementary half of the theory: below any value `a < f x` there is a continuous
affine minorant of `f` on `K` taking the value `a` at `x` (`ConvexOn.exists_affine_le_of_lt`,
a Hahn-Banach separation of `(x, a)` from the closed convex epigraph of `f`), and a continuous
affine function integrates to its value at the barycentre. -/
theorem IsBarycenter.le_integral_of_convexOn [IsProbabilityMeasure μ]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hμ : μ Kᶜ = 0) (hx : IsBarycenter μ x)
    (hfconv : ConvexOn ℝ K f) (hflsc : LowerSemicontinuousOn f K) (hfi : Integrable f μ) :
    f x ≤ ∫ y, f y ∂μ := by
  have hxK : x ∈ K := hx.mem_of_convex hK hKconv hμ
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha1, ha2⟩ := exists_between hcon
  obtain ⟨l, c, hle, heq⟩ :=
    hfconv.exists_affine_le_of_lt (𝕜 := ℝ) hxK ha2 hK.isClosed hflsc
  have hli : Integrable (fun y => l y + c) μ :=
    (l.integrable_of_measure_compl_eq_zero hK hμ).add (integrable_const c)
  have hmono : ∫ y, (l y + c) ∂μ ≤ ∫ y, f y ∂μ := by
    refine integral_mono_ae hli hfi ?_
    filter_upwards [(mem_ae_iff.2 hμ : ∀ᵐ y ∂μ, y ∈ K)] with y hy
    simpa using hle ⟨y, hy⟩
  have hcalc : ∫ y, (l y + c) ∂μ = a := by
    rw [integral_add (l.integrable_of_measure_compl_eq_zero hK hμ) (integrable_const c),
      hx l, integral_const]
    simpa using heq
  rw [hcalc] at hmono
  exact absurd hmono (not_le.2 ha1)


/-! ### Splitting a barycentre along a finite partition -/

/-- **Splitting a barycentre along a finite partition.** If `A` is a finite measurable partition of
the carrier of a probability measure `μ`, and each piece `A i` sits, up to a `μ`-null set, inside a
nonempty compact convex set `C i`, then the barycentre `x` of `μ` is the convex combination
`∑ i, μ (A i) • y i` of points `y i ∈ C i`.

The point `y i` is the barycentre of `μ` conditioned on `A i`, which exists in `C i` by
`MeasureTheory.exists_isBarycenter_of_isCompact`; the identity is then checked against every
continuous linear functional and the points are separated by Hahn-Banach. -/
theorem IsBarycenter.exists_convexCombination_of_partition {ι : Type*} [Fintype ι]
    {A C : ι → Set V} [IsProbabilityMeasure μ]
    (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Function.onFun Disjoint A))
    (hAcov : ∀ᵐ y ∂μ, y ∈ ⋃ i, A i)
    (hCcomp : ∀ i, IsCompact (C i)) (hCconv : ∀ i, Convex ℝ (C i)) (hCne : ∀ i, (C i).Nonempty)
    (hAC : ∀ i, μ (A i \ C i) = 0) (hx : IsBarycenter μ x) :
    ∃ y : ι → V, (∀ i, y i ∈ C i) ∧ ∑ i, (μ (A i)).toReal • y i = x := by
  -- `μ` is carried by the compact set `⋃ i, C i`, so every functional is integrable.
  have hCcompact : IsCompact (⋃ i, C i) := isCompact_iUnion hCcomp
  have hcarrier : μ (⋃ i, C i)ᶜ = 0 := by
    refine measure_mono_null (fun y hy => ?_) (measure_union_null
      (mem_ae_iff.1 hAcov) (measure_iUnion_null hAC) :
      μ ((⋃ i, A i)ᶜ ∪ ⋃ i, A i \ C i) = 0)
    by_cases hyA : y ∈ ⋃ i, A i
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hyA
      exact Or.inr (mem_iUnion.2 ⟨i, hi, fun h => hy (mem_iUnion.2 ⟨i, h⟩)⟩)
    · exact Or.inl hyA
  have hint : ∀ l : StrongDual ℝ V, Integrable l μ :=
    fun l => l.integrable_of_measure_compl_eq_zero hCcompact hcarrier
  -- the conditional barycentres
  have key : ∀ i, ∃ z ∈ C i, ∀ l : StrongDual ℝ V,
      ∫ w in A i, l w ∂μ = (μ (A i)).toReal * l z := by
    intro i
    rcases eq_or_ne (μ (A i)) 0 with h0 | h0
    · obtain ⟨z, hz⟩ := hCne i
      exact ⟨z, hz, fun l => by
        simp [Measure.restrict_eq_zero.2 h0, h0]⟩
    · have hfin : μ (A i) ≠ ∞ := measure_ne_top _ _
      have htr : (μ (A i)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, hfin⟩
      have hprob : IsProbabilityMeasure ((μ (A i))⁻¹ • μ.restrict (A i)) := by
        constructor
        rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
          ENNReal.inv_mul_cancel h0 hfin]
      have hνC : ((μ (A i))⁻¹ • μ.restrict (A i)) (C i)ᶜ = 0 := by
        rw [Measure.smul_apply, Measure.restrict_apply (hCcomp i).isClosed.measurableSet.compl,
          show (C i)ᶜ ∩ A i = A i \ C i from by rw [inter_comm]; rfl, hAC i, smul_eq_mul,
          mul_zero]
      obtain ⟨z, hz, hbar⟩ :=
        exists_isBarycenter_of_isCompact (hCcomp i) (hCconv i) _ hνC
      refine ⟨z, hz, fun l => ?_⟩
      have h := hbar l
      rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul] at h
      field_simp at h
      linarith [h]
  choose y hyC hybar using key
  refine ⟨y, hyC, ?_⟩
  by_contra hne
  obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hne
  refine absurd ?_ hl.ne
  have hsplit : ∫ w, l w ∂μ = ∑ i, ∫ w in A i, l w ∂μ := by
    rw [integral_eq_setIntegral hAcov,
      integral_iUnion_fintype hAm hAd (fun i => (hint l).integrableOn)]
  calc l (∑ i, (μ (A i)).toReal • y i)
      = ∑ i, (μ (A i)).toReal * l (y i) := by simp [map_sum]
    _ = ∑ i, ∫ w in A i, l w ∂μ := by simp [hybar]
    _ = ∫ w, l w ∂μ := hsplit.symm
    _ = l x := hx l



/-- The masses of a finite measurable partition of the carrier of a probability measure sum
to one. -/
theorem sum_toReal_measure_of_partition {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {ι : Type*} [Fintype ι] {A : ι → Set Ω}
    (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Function.onFun Disjoint A))
    (hAcov : ∀ᵐ y ∂ν, y ∈ ⋃ i, A i) : ∑ i, (ν (A i)).toReal = 1 := by
  have h2 : ν (⋃ i, A i) = ∑ i, ν (A i) := by
    rw [measure_iUnion hAd hAm, tsum_fintype]
  have h3 : ν (⋃ i, A i) = 1 := by
    refine le_antisymm ((measure_mono (subset_univ (⋃ i, A i))).trans_eq measure_univ) ?_
    calc (1 : ℝ≥0∞) = ν univ := measure_univ.symm
      _ ≤ ν (⋃ i, A i) :=
          measure_mono_ae (by filter_upwards [hAcov] with y hy using fun _ => hy)
  have h1 : ∑ i, ν (A i) = 1 := h2 ▸ h3
  have := congrArg ENNReal.toReal h1
  rwa [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), ENNReal.toReal_one] at this

/-! ### The estimate behind the concave half -/

/-- The estimate behind the concave half of Jensen's inequality. Suppose the carrier of `μ` is cut
into finitely many measurable pieces `A i`, each sitting inside a compact convex cell `C i ⊆ K`,
and suppose `f` is bounded below by `s i` on the cell and above by `s i + e i` on the piece. Then
the `μ`-average of `f` exceeds `f x` by at most the average of the widths `e i`.

Indeed the barycentre is the convex combination `x = ∑ i, μ (A i) • y i` of the conditional
barycentres `y i ∈ C i` (`MeasureTheory.IsBarycenter.exists_convexCombination_of_partition`), so
`∑ i, μ (A i) * s i ≤ ∑ i, μ (A i) * f (y i) ≤ f x` by concavity, while
`∫ f dμ ≤ ∑ i, μ (A i) * (s i + e i)` piece by piece. -/
theorem IsBarycenter.integral_le_add_of_partition {ι : Type*} [Fintype ι]
    {A C : ι → Set V} {s e : ι → ℝ} [IsProbabilityMeasure μ]
    (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Function.onFun Disjoint A))
    (hAcov : ∀ᵐ y ∂μ, y ∈ ⋃ i, A i)
    (hCcomp : ∀ i, IsCompact (C i)) (hCconv : ∀ i, Convex ℝ (C i)) (hCne : ∀ i, (C i).Nonempty)
    (hCK : ∀ i, C i ⊆ K) (hAC : ∀ i, μ (A i \ C i) = 0)
    (hx : IsBarycenter μ x) (hfconc : ConcaveOn ℝ K f) (hfi : Integrable f μ)
    (hlow : ∀ i, μ (A i) ≠ 0 → ∀ v ∈ C i, s i ≤ f v)
    (hhigh : ∀ i, ∀ᵐ v ∂(μ.restrict (A i)), f v ≤ s i + e i) :
    ∫ y, f y ∂μ ≤ f x + ∑ i, (μ (A i)).toReal * e i := by
  obtain ⟨y, hyC, hycomb⟩ :=
    hx.exists_convexCombination_of_partition hAm hAd hAcov hCcomp hCconv hCne hAC
  set p : ι → ℝ := fun i => (μ (A i)).toReal with hp
  have hp0 : ∀ i, 0 ≤ p i := fun i => ENNReal.toReal_nonneg
  have hpsum : ∑ i, p i = 1 := sum_toReal_measure_of_partition hAm hAd hAcov
  -- concavity at the barycentre
  have hjensen : ∑ i, p i * f (y i) ≤ f x := by
    rw [← hycomb]
    simpa [smul_eq_mul] using
      hfconc.le_map_sum (t := Finset.univ) (w := p) (p := y)
        (fun i _ => hp0 i) hpsum (fun i _ => hCK i (hyC i))
  -- the level bound below
  have hlevel : ∑ i, p i * s i ≤ ∑ i, p i * f (y i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rcases eq_or_ne (μ (A i)) 0 with h0 | h0
    · simp [hp, h0]
    · exact mul_le_mul_of_nonneg_left (hlow i h0 _ (hyC i)) (hp0 i)
  -- the level bound above, piece by piece
  have hpiece : ∀ i, ∫ w in A i, f w ∂μ ≤ p i * (s i + e i) := by
    intro i
    have := integral_mono_ae (hfi.integrableOn) (integrable_const (s i + e i)) (hhigh i)
    rw [integral_const, measureReal_restrict_apply_univ] at this
    simpa [hp, mul_comm, measureReal_def] using this
  have hsplit : ∫ w, f w ∂μ = ∑ i, ∫ w in A i, f w ∂μ := by
    rw [integral_eq_setIntegral hAcov,
      integral_iUnion_fintype hAm hAd (fun i => hfi.integrableOn)]
  calc ∫ w, f w ∂μ = ∑ i, ∫ w in A i, f w ∂μ := hsplit
    _ ≤ ∑ i, p i * (s i + e i) := Finset.sum_le_sum fun i _ => hpiece i
    _ = ∑ i, p i * s i + ∑ i, p i * e i := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ f x + ∑ i, p i * e i := by gcongr; exact hlevel.trans hjensen


/-! ### Two auxiliary facts about neighbourhoods of `0` -/

omit [T2Space V] [MeasurableSpace V] [OpensMeasurableSpace V] in
/-- In a locally convex space every neighbourhood `U` of `0` contains a symmetric open convex
neighbourhood `W` of `0` with `W + W + W ⊆ U`. -/
theorem _root_.exists_isOpen_convex_symm_add_three_subset {U : Set V} (hU : U ∈ 𝓝 (0 : V)) :
    ∃ W : Set V, IsOpen W ∧ (0 : V) ∈ W ∧ Convex ℝ W ∧ (∀ v ∈ W, -v ∈ W) ∧
      ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, a + b + c ∈ U := by
  obtain ⟨U₁, hU₁, h₁⟩ := exists_nhds_zero_half hU
  obtain ⟨U₂, hU₂, h₂⟩ := exists_nhds_zero_half hU₁
  obtain ⟨S, hS, hSconv, hSsub⟩ :=
    (locallyConvexSpace_iff_exists_convex_subset ℝ V).1 inferInstance 0 (U₂ ∩ U₁)
      (inter_mem hU₂ hU₁)
  refine ⟨interior S ∩ -interior S, isOpen_interior.inter isOpen_interior.neg, ?_,
    hSconv.interior.inter hSconv.interior.neg, ?_, ?_⟩
  · exact ⟨mem_interior_iff_mem_nhds.2 hS, by simpa using mem_interior_iff_mem_nhds.2 hS⟩
  · rintro v ⟨hv1, hv2⟩
    exact ⟨by simpa using hv2, by simpa using hv1⟩
  · rintro a ⟨ha, -⟩ b ⟨hb, -⟩ c ⟨hc, -⟩
    have hsub : interior S ⊆ U₂ ∩ U₁ := interior_subset.trans hSsub
    exact h₁ _ (h₂ _ (hsub ha).1 _ (hsub hb).1) _ (hsub hc).2

omit [Module ℝ V] [T2Space V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V] [MeasurableSpace V]
  [OpensMeasurableSpace V] in
/-- In a topological additive group the closure of an open neighbourhood `W` of `0` is contained
in `W + W`. -/
theorem _root_.exists_add_eq_of_mem_closure {W : Set V} (hW : IsOpen W) (h0 : (0 : V) ∈ W)
    {v : V} (hv : v ∈ closure W) : ∃ a ∈ W, ∃ b ∈ W, v = a + b := by
  have hopen : IsOpen ((fun u => v - u) ⁻¹' W) := hW.preimage (continuous_const.sub continuous_id)
  have hmem : v ∈ (fun u => v - u) ⁻¹' W := by simpa using h0
  obtain ⟨u, hu1, hu2⟩ := mem_closure_iff.1 hv _ hopen hmem
  exact ⟨v - u, hu1, u, hu2, by abel⟩

/-! ### The concave half of Jensen's inequality -/

/-- **Jensen's inequality for a barycentre, concave case**; the hard half of Phelps' Lemma 9.7.
If `f` is concave and lower semicontinuous on a compact convex `K` carrying the probability
measure `μ`, and bounded above on `K`, then its `μ`-average is at most its value at the barycentre.

This direction is *not* a supremum of continuous affine minorants: a concave lower semicontinuous
function is in general not an infimum of continuous affine functions. The proof instead makes `x`
into a genuine finite convex combination. Given `ε > 0`, cut `K` by the level sets
`L j = {t j < f ≤ t j + δ}` of a subdivision of the range of `f` of mesh `δ`, shrink each `L j` to
a compact subset `Q j` (weak regularity), and use lower semicontinuity to find one convex
symmetric neighbourhood `W` of `0` with `Q j + W + W + W ⊆ {f > t j}` for every `j`. Cutting `K`
further by a finite cover by translates of `W` produces cells `C ⊆ K` that are compact and convex,
carry the corresponding pieces of `μ`, and on which `f` still exceeds `t j`. The conditional
barycentres in those cells then witness `x` as a convex combination, and concavity finishes the
argument (`MeasureTheory.IsBarycenter.integral_le_add_of_partition`). -/
theorem IsBarycenter.integral_le_of_concaveOn [μ.WeaklyRegular] [IsProbabilityMeasure μ]
    (hK : IsCompact K) (hμ : μ Kᶜ = 0) (hx : IsBarycenter μ x)
    (hfconc : ConcaveOn ℝ K f) (hflsc : LowerSemicontinuousOn f K) (hfi : Integrable f μ)
    (hfb : BddAbove (f '' K)) :
    ∫ y, f y ∂μ ≤ f x := by
  classical
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hKne : K.Nonempty := by
    rcases K.eq_empty_or_nonempty with rfl | h
    · rw [compl_empty, measure_univ] at hμ; exact absurd hμ one_ne_zero
    · exact h
  obtain ⟨m, hm⟩ := hflsc.bddBelow_of_isCompact hK
  obtain ⟨M, hM⟩ := hfb
  have hm' : ∀ y ∈ K, m ≤ f y := fun y hy => hm ⟨y, hy, rfl⟩
  have hM' : ∀ y ∈ K, f y ≤ M := fun y hy => hM ⟨y, hy, rfl⟩
  obtain ⟨y₀, hy₀⟩ := hKne
  have hmM : m ≤ M := (hm' y₀ hy₀).trans (hM' y₀ hy₀)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := ε / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  set t : ℕ → ℝ := fun j => m - δ + j * δ with htdef
  have htmono : Monotone t := fun j k hjk => by
    have : (j : ℝ) ≤ k := Nat.cast_le.2 hjk
    simp only [htdef]
    nlinarith
  have htsucc : ∀ j, t (j + 1) = t j + δ := by
    intro j; simp only [htdef]; push_cast; ring
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M < t N := by
    obtain ⟨N, hNgt⟩ := exists_nat_gt ((M - m + δ) / δ)
    refine ⟨N, ?_⟩
    have : (M - m + δ) < N * δ := by
      rw [div_lt_iff₀ hδpos] at hNgt; linarith
    simp only [htdef]; linarith
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp only [htdef, Nat.cast_zero, zero_mul, add_zero] at hN
    linarith
  -- the open hulls of the strict superlevel sets
  set W : ℕ → Set V := fun j => ⋃₀ {U | IsOpen U ∧ ∀ v ∈ U ∩ K, t j < f v} with hWdef
  have hWopen : ∀ j, IsOpen (W j) := fun j => isOpen_sUnion fun U hU => hU.1
  have hWlt : ∀ j, ∀ v ∈ W j ∩ K, t j < f v := by
    rintro j v ⟨⟨U, hU, hvU⟩, hvK⟩
    exact hU.2 v ⟨hvU, hvK⟩
  have hWsup : ∀ j, ∀ v ∈ K, t j < f v → v ∈ W j := by
    intro j v hvK hlt
    obtain ⟨U, hUopen, hvU, hUsub⟩ := mem_nhdsWithin.1 (hflsc v hvK (t j) hlt)
    exact ⟨U, ⟨hUopen, fun w hw => hUsub ⟨hw.1, hw.2⟩⟩, hvU⟩
  have hWanti : ∀ {j k : ℕ}, j ≤ k → W k ⊆ W j := by
    rintro j k hjk v ⟨U, hU, hvU⟩
    exact ⟨U, ⟨hU.1, fun w hw => lt_of_le_of_lt (htmono hjk) (hU.2 w hw)⟩, hvU⟩
  -- the level sets
  set L : ℕ → Set V := fun j => (K ∩ W j) \ W (j + 1) with hLdef
  have hLmeas : ∀ j, MeasurableSet (L j) :=
    fun j => (hKmeas.inter (hWopen j).measurableSet).diff (hWopen (j + 1)).measurableSet
  have hLK : ∀ j, L j ⊆ K := fun j v hv => hv.1.1
  have hLlow : ∀ j, ∀ v ∈ L j, t j < f v := fun j v hv => hWlt j v ⟨hv.1.2, hv.1.1⟩
  have hLhigh : ∀ j, ∀ v ∈ L j, f v ≤ t (j + 1) := by
    intro j v hv
    by_contra hcon
    exact hv.2 (hWsup (j + 1) v hv.1.1 (lt_of_not_ge hcon))
  have hLdisj : Pairwise (Function.onFun Disjoint L) := by
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact Set.disjoint_left.2 fun v hv hv' => hv.2 (hWanti h hv'.1.2)
    · exact Set.disjoint_left.2 fun v hv hv' => hv'.2 (hWanti h hv.1.2)
  have hLcov : ∀ v ∈ K, ∃ j < N, v ∈ L j := by
    intro v hv
    have hnot : v ∉ W N := fun h => absurd (hWlt N v ⟨h, hv⟩) (not_lt.2 ((hM' v hv).trans hN.le))
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 hN0
    have hex : ∃ j, v ∉ W (j + 1) := ⟨N - 1, by rwa [Nat.sub_add_cancel hN1]⟩
    have hle : Nat.find hex ≤ N - 1 := by
      refine Nat.find_le ?_
      show v ∉ W (N - 1 + 1)
      rwa [Nat.sub_add_cancel hN1]
    refine ⟨Nat.find hex, by omega, ⟨⟨hv, ?_⟩, Nat.find_spec hex⟩⟩
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0]
        exact hWsup 0 v hv (by simp only [htdef]; push_cast; linarith [hm' v hv])
      · have := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
        rw [Nat.sub_add_cancel hpos] at this
        exact not_not.1 this
  -- inner compact approximation of the level sets
  set ρ : ℝ := δ / (N * (M - m + δ) + 1) with hρdef
  have hMmδ : 0 < M - m + δ := by linarith
  have hρpos : 0 < ρ := by
    apply div_pos hδpos
    have : (0:ℝ) ≤ N * (M - m + δ) := by positivity
    linarith
  have hη0 : ENNReal.ofReal ρ ≠ 0 := by simp [hρpos]
  have hQex : ∀ j : Fin N, ∃ F, F ⊆ L j ∧ IsClosed F ∧ μ (L j \ F) < ENNReal.ofReal ρ :=
    fun j => (hLmeas j).exists_isClosed_sdiff_lt (measure_ne_top _ _) hη0
  choose Q hQL hQclosed hQμ using hQex
  have hQcomp : ∀ j, IsCompact (Q j) :=
    fun j => hK.of_isClosed_subset (hQclosed j) ((hQL j).trans (hLK j))
  have hQW : ∀ j : Fin N, Q j ⊆ W j := fun j v hv => ((hQL j) hv).1.2
  -- a single small symmetric convex neighbourhood working for every level
  have hUex : ∀ j : Fin N, ∃ U ∈ 𝓝 (0 : V), Q j + U ⊆ W j :=
    fun j => compact_open_separated_add_right (hQcomp j) (hWopen j) (hQW j)
  choose U hU hUsub using hUex
  have hUbig : (⋂ j : Fin N, U j) ∈ 𝓝 (0 : V) := Filter.iInter_mem.2 hU
  obtain ⟨W', hW'open, hW'0, hW'conv, hW'symm, hW'add⟩ :=
    exists_isOpen_convex_symm_add_three_subset hUbig
  -- the spatial cover
  set T : V → Set V := fun z => (fun v => v - z) ⁻¹' W' with hTdef
  set Tc : V → Set V := fun z => (fun v => v - z) ⁻¹' closure W' with hTcdef
  have hTopen : ∀ z, IsOpen (T z) :=
    fun z => hW'open.preimage (continuous_id.sub continuous_const)
  have hTself : ∀ z, z ∈ T z := fun z => by simpa [hTdef] using hW'0
  have hTcclosed : ∀ z, IsClosed (Tc z) :=
    fun z => isClosed_closure.preimage (continuous_id.sub continuous_const)
  have hTcconv : ∀ z, Convex ℝ (Tc z) := by
    intro z
    have := hW'conv.closure.translate_preimage_right (-z)
    simpa [hTcdef, sub_eq_neg_add] using this
  have hTTc : ∀ z, T z ⊆ Tc z := fun z v hv => subset_closure hv
  obtain ⟨tf, htfK, htfcov⟩ :=
    hK.elim_nhds_subcover T (fun z _ => (hTopen z).mem_nhds (hTself z))
  set n : ℕ := tf.card with hndef
  set z : Fin n → V := fun i => ((tf.equivFin.symm i : { a // a ∈ tf }) : V) with hzdef
  have hzK : ∀ i, z i ∈ K := fun i => htfK _ (tf.equivFin.symm i).2
  have hzcov : ∀ v ∈ K, ∃ i, v ∈ T (z i) := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := mem_iUnion₂.1 (htfcov hv)
    refine ⟨tf.equivFin ⟨w, hw⟩, ?_⟩
    simpa [hzdef] using hvw
  -- the spatial partition
  set B : Fin n → Set V := fun i => (K ∩ T (z i)) \ ⋃ (i' : Fin n) (_ : i' < i), T (z i') with hBdef
  have hBmeas : ∀ i, MeasurableSet (B i) := by
    intro i
    refine (hKmeas.inter (hTopen _).measurableSet).diff ?_
    exact MeasurableSet.iUnion fun i' => MeasurableSet.iUnion fun _ => (hTopen _).measurableSet
  have hBT : ∀ i, B i ⊆ K ∩ T (z i) := fun i v hv => hv.1
  have hBdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i i' hii'
    rcases lt_or_gt_of_ne hii' with h | h
    · exact Set.disjoint_left.2 fun v hv hv' =>
        hv'.2 (mem_iUnion₂.2 ⟨i, h, hv.1.2⟩)
    · exact Set.disjoint_left.2 fun v hv hv' =>
        hv.2 (mem_iUnion₂.2 ⟨i', h, hv'.1.2⟩)
  have hBcov : ∀ v ∈ K, ∃ i, v ∈ B i := by
    intro v hv
    obtain ⟨i, hi⟩ := hzcov v hv
    set sfin : Finset (Fin n) := {i' | v ∈ T (z i')} with hsfin
    have hsne : sfin.Nonempty := ⟨i, by simp [hsfin, hi]⟩
    refine ⟨sfin.min' hsne, ⟨hv, ?_⟩, ?_⟩
    · have := sfin.min'_mem hsne
      simpa [hsfin] using this
    · rintro hmem
      obtain ⟨i', hi', hvi'⟩ := mem_iUnion₂.1 hmem
      have hmem' : i' ∈ sfin := by simp [hsfin, hvi']
      exact absurd (sfin.min'_le i' hmem') (not_le.2 hi')
  -- assemble the partition of `V` and apply the estimate
  set A : Option (Fin N × Fin n) → Set V :=
    fun k => k.elim (⋃ (j : Fin N) (i : Fin n), Q j ∩ B i)ᶜ (fun q => Q q.1 ∩ B q.2) with hAdef
  set Cc : Option (Fin N × Fin n) → Set V :=
    fun k => k.elim K (fun q => K ∩ Tc (z q.2)) with hCdef
  set sfun : Option (Fin N × Fin n) → ℝ := fun k => k.elim (m - δ) (fun q => t q.1) with hsdef
  set efun : Option (Fin N × Fin n) → ℝ := fun k => k.elim (M - m + δ) (fun _ => δ) with hedef
  have hQBunion : (⋃ (j : Fin N) (i : Fin n), Q j ∩ B i) = ⋃ j : Fin N, Q j := by
    refine Subset.antisymm (iUnion_mono fun j => iUnion_subset fun i => inter_subset_left) ?_
    refine iUnion_subset fun j v hv => ?_
    obtain ⟨i, hi⟩ := hBcov v (hLK j ((hQL j) hv))
    exact mem_iUnion₂.2 ⟨j, i, hv, hi⟩
  have hAm : ∀ k, MeasurableSet (A k) := by
    rintro (_ | ⟨j, i⟩)
    · exact (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun i =>
        (hQclosed j).measurableSet.inter (hBmeas i)).compl
    · exact (hQclosed j).measurableSet.inter (hBmeas i)
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    rintro (_ | ⟨j, i⟩) (_ | ⟨j', i'⟩) hne
    · exact absurd rfl hne
    · exact Set.disjoint_left.2 fun v hv hv' => hv (mem_iUnion₂.2 ⟨j', i', hv'⟩)
    · exact Set.disjoint_left.2 fun v hv hv' => hv' (mem_iUnion₂.2 ⟨j, i, hv⟩)
    · by_cases hjj : j = j'
      · subst hjj
        have hii : i ≠ i' := fun h => hne (by rw [h])
        exact Set.disjoint_left.2 fun v hv hv' =>
          (Set.disjoint_left.1 (hBdisj hii)) hv.2 hv'.2
      · have hjj' : (j : ℕ) ≠ (j' : ℕ) := fun h => hjj (Fin.ext h)
        exact Set.disjoint_left.2 fun v hv hv' =>
          (Set.disjoint_left.1 (hLdisj hjj')) ((hQL j) hv.1) ((hQL j') hv'.1)
  have hAcovset : (⋃ k, A k) = univ := by
    refine eq_univ_of_forall fun v => ?_
    by_cases hv : v ∈ ⋃ (j : Fin N) (i : Fin n), Q j ∩ B i
    · obtain ⟨j, i, hji⟩ := mem_iUnion₂.1 hv
      exact mem_iUnion.2 ⟨some (j, i), hji⟩
    · exact mem_iUnion.2 ⟨none, hv⟩
  have hAcov : ∀ᵐ y ∂μ, y ∈ ⋃ k, A k := by
    rw [hAcovset]; exact Eventually.of_forall fun _ => mem_univ _
  have hCcomp : ∀ k, IsCompact (Cc k) := by
    rintro (_ | ⟨j, i⟩)
    · exact hK
    · exact hK.inter_right (hTcclosed _)
  have hCconv : ∀ k, Convex ℝ (Cc k) := by
    rintro (_ | ⟨j, i⟩)
    · exact hfconc.1
    · exact hfconc.1.inter (hTcconv _)
  have hCne : ∀ k, (Cc k).Nonempty := by
    rintro (_ | ⟨j, i⟩)
    · exact ⟨y₀, hy₀⟩
    · exact ⟨z i, hzK i, by simpa [hTcdef] using subset_closure hW'0⟩
  have hCK : ∀ k, Cc k ⊆ K := by
    rintro (_ | ⟨j, i⟩)
    · exact Subset.rfl
    · exact inter_subset_left
  have hAC : ∀ k, μ (A k \ Cc k) = 0 := by
    rintro (_ | ⟨j, i⟩)
    · exact measure_mono_null (fun v hv => hv.2) hμ
    · refine measure_mono_null (fun v hv => ?_) (measure_empty (μ := μ))
      exact absurd ⟨(hLK j ((hQL j) hv.1.1)), hTTc _ (hBT i hv.1.2).2⟩ hv.2
  have hlow : ∀ k, μ (A k) ≠ 0 → ∀ v ∈ Cc k, sfun k ≤ f v := by
    rintro (_ | ⟨j, i⟩) hk v hv
    · have hs : sfun none = m - δ := rfl
      rw [hs]
      linarith [hm' v hv]
    · obtain ⟨w, hw⟩ : (Q j ∩ B i).Nonempty := by
        rw [nonempty_iff_ne_empty]
        rintro he
        exact hk (by rw [show A (some (j, i)) = Q j ∩ B i from rfl, he, measure_empty])
      obtain ⟨a, ha, b, hb, hab⟩ :=
        exists_add_eq_of_mem_closure hW'open hW'0 (show v - z i ∈ closure W' from hv.2)
      have hwT : w - z i ∈ W' := (hBT i hw.2).2
      have hvw : v - w ∈ ⋂ j' : Fin N, U j' := by
        have : v - w = a + b + (-(w - z i)) := by rw [← hab]; abel
        rw [this]
        exact hW'add a ha b hb _ (hW'symm _ hwT)
      have hvWj : v ∈ W j := by
        refine hUsub j ?_
        have : v = w + (v - w) := by abel
        rw [this]
        exact Set.add_mem_add hw.1 (mem_iInter.1 hvw j)
      exact (hWlt j v ⟨hvWj, hv.1⟩).le
  have hhigh : ∀ k, ∀ᵐ v ∂(μ.restrict (A k)), f v ≤ sfun k + efun k := by
    rintro (_ | ⟨j, i⟩)
    · filter_upwards [ae_restrict_of_ae (mem_ae_iff.2 hμ : ∀ᵐ v ∂μ, v ∈ K)] with v hv
      have : m - δ + (M - m + δ) = M := by ring
      rw [show sfun none = m - δ from rfl, show efun none = M - m + δ from rfl, this]
      exact hM' v hv
    · filter_upwards [ae_restrict_mem (hAm (some (j, i)))] with v hv
      have := hLhigh j v ((hQL j) hv.1)
      rw [htsucc] at this
      exact this
  have hmain := hx.integral_le_add_of_partition hAm hAd hAcov hCcomp hCconv hCne hCK hAC
    hfconc hfi hlow hhigh
  -- bound the total width
  have hpnone : (μ (A none)).toReal ≤ N * ρ := by
    have hsub : A none ⊆ Kᶜ ∪ ⋃ j : Fin N, (L j \ Q j) := by
      intro v hv
      rw [show A none = (⋃ (j : Fin N) (i : Fin n), Q j ∩ B i)ᶜ from rfl, hQBunion] at hv
      by_cases hvK : v ∈ K
      · obtain ⟨j, hjN, hjL⟩ := hLcov v hvK
        exact Or.inr (mem_iUnion.2 ⟨⟨j, hjN⟩, hjL, fun h => hv (mem_iUnion.2 ⟨⟨j, hjN⟩, h⟩)⟩)
      · exact Or.inl hvK
    have h1 : μ (A none) ≤ ENNReal.ofReal (N * ρ) := by
      refine (measure_mono hsub).trans ?_
      refine (measure_union_le _ _).trans ?_
      rw [hμ, zero_add]
      refine (measure_iUnion_fintype_le _ _).trans ?_
      calc ∑ j : Fin N, μ (L j \ Q j) ≤ ∑ _j : Fin N, ENNReal.ofReal ρ :=
            Finset.sum_le_sum fun j _ => (hQμ j).le
        _ = N * ENNReal.ofReal ρ := by simp
        _ = ENNReal.ofReal (N * ρ) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    calc (μ (A none)).toReal ≤ (ENNReal.ofReal (N * ρ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ = N * ρ := ENNReal.toReal_ofReal (by positivity)
  have hsum1 : ∑ k, (μ (A k)).toReal = 1 := sum_toReal_measure_of_partition hAm hAd hAcov
  have hwidth : ∑ k, (μ (A k)).toReal * efun k ≤ ε := by
    rw [Fintype.sum_option]
    have hsome : ∑ q : Fin N × Fin n, (μ (A (some q))).toReal * efun (some q)
        = δ * ∑ q : Fin N × Fin n, (μ (A (some q))).toReal := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by
        rw [show efun (some q) = δ from rfl]; ring
    have hsplit : (μ (A none)).toReal + ∑ q : Fin N × Fin n, (μ (A (some q))).toReal = 1 := by
      have h := hsum1
      rw [Fintype.sum_option] at h
      exact h
    have hle1 : ∑ q : Fin N × Fin n, (μ (A (some q))).toReal ≤ 1 := by
      have : (0:ℝ) ≤ (μ (A none)).toReal := ENNReal.toReal_nonneg
      linarith
    have hnone : (μ (A none)).toReal * efun none ≤ δ := by
      rw [show efun none = M - m + δ from rfl]
      calc (μ (A none)).toReal * (M - m + δ) ≤ (N * ρ) * (M - m + δ) := by
            exact mul_le_mul_of_nonneg_right hpnone hMmδ.le
        _ ≤ δ := by
            have hden : (0:ℝ) < (N:ℝ) * (M - m + δ) + 1 := by positivity
            have hfrac : ((N:ℝ) * (M - m + δ)) / ((N:ℝ) * (M - m + δ) + 1) ≤ 1 := by
              rw [div_le_one hden]; linarith
            rw [hρdef, show ((N:ℝ) * (δ / ((N:ℝ) * (M - m + δ) + 1))) * (M - m + δ)
              = δ * (((N:ℝ) * (M - m + δ)) / ((N:ℝ) * (M - m + δ) + 1)) by
                field_simp]
            nlinarith [hδpos.le, hfrac]
    rw [hsome]
    have : δ * ∑ q : Fin N × Fin n, (μ (A (some q))).toReal ≤ δ :=
      by nlinarith [hδpos.le, hle1]
    linarith [hnone, this, hδdef]
  linarith [hmain, hwidth]


/-! ### Phelps' Lemma 9.7: affine lower semicontinuous functions are strongly affine -/

/-- **Phelps' Lemma 9.7.** An affine, lower semicontinuous, bounded above function on a compact
convex set `K` commutes with barycentres: if `x` is the barycentre of a probability measure `μ`
carried by `K`, then `∫ f dμ = f x`. (One says that `f` is *strongly affine*.)

Both halves are Jensen's inequality: `f x ≤ ∫ f dμ` because `f` is convex
(`MeasureTheory.IsBarycenter.le_integral_of_convexOn`), and `∫ f dμ ≤ f x` because `f` is concave
(`MeasureTheory.IsBarycenter.integral_le_of_concaveOn`). -/
theorem IsBarycenter.integral_eq_of_affine [μ.WeaklyRegular] [IsProbabilityMeasure μ]
    (hK : IsCompact K) (hμ : μ Kᶜ = 0) (hx : IsBarycenter μ x)
    (hfconv : ConvexOn ℝ K f) (hfconc : ConcaveOn ℝ K f) (hflsc : LowerSemicontinuousOn f K)
    (hfi : Integrable f μ) (hfb : BddAbove (f '' K)) :
    ∫ y, f y ∂μ = f x :=
  le_antisymm (hx.integral_le_of_concaveOn hK hμ hfconc hflsc hfi hfb)
    (hx.le_integral_of_convexOn hK hfconv.1 hμ hfconv hflsc hfi)

end Jensen

/-! ### The `ℝ≥0∞`-valued form -/

section ENNRealJensen

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [T2Space V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  {K : Set V} {μ : Measure V} {x : V} {g : V → ℝ≥0∞}

/-- Concavity of an `ℝ≥0∞`-valued function on a set: the value at a convex combination of two
points of `s` dominates the corresponding combination of the values. Georgii's excess free energy
`𝒜(· | Φ)` on the shift-invariant probability measures satisfies this (with equality). -/
def _root_.ConcaveOnENNReal (s : Set V) (g : V → ℝ≥0∞) : Prop :=
  ∀ ⦃y⦄, y ∈ s → ∀ ⦃w⦄, w ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    ENNReal.ofReal a * g y + ENNReal.ofReal b * g w ≤ g (a • y + b • w)

omit [TopologicalSpace V] [T2Space V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [MeasurableSpace V] [OpensMeasurableSpace V] in
/-- The truncation `min g n` of an `ℝ≥0∞`-concave function is concave, in the real-valued sense,
after `ENNReal.toReal`. -/
theorem _root_.ConcaveOnENNReal.concaveOn_toReal_min {s : Set V} (hs : Convex ℝ s)
    (hg : ConcaveOnENNReal s g) (n : ℝ≥0) :
    ConcaveOn ℝ s (fun y => (min (g y) (n : ℝ≥0∞)).toReal) := by
  refine ⟨hs, fun y hy w hw a b ha hb hab => ?_⟩
  have hne : ∀ v : V, min (g v) (n : ℝ≥0∞) ≠ ∞ :=
    fun v => ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have key : ENNReal.ofReal a * min (g y) (n : ℝ≥0∞) + ENNReal.ofReal b * min (g w) (n : ℝ≥0∞)
      ≤ min (g (a • y + b • w)) (n : ℝ≥0∞) := by
    refine le_min ?_ ?_
    · refine le_trans ?_ (hg hy hw ha hb hab)
      gcongr <;> exact min_le_left _ _
    · calc ENNReal.ofReal a * min (g y) (n : ℝ≥0∞) + ENNReal.ofReal b * min (g w) (n : ℝ≥0∞)
          ≤ ENNReal.ofReal a * (n : ℝ≥0∞) + ENNReal.ofReal b * (n : ℝ≥0∞) := by
            gcongr <;> exact min_le_right _ _
        _ = (n : ℝ≥0∞) := by
            rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]
  have hfa : ENNReal.ofReal a * min (g y) (n : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hne y)
  have hfb' : ENNReal.ofReal b * min (g w) (n : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hne w)
  have h1 := ENNReal.toReal_mono (hne _) key
  rw [ENNReal.toReal_add hfa hfb', ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at h1
  simpa [smul_eq_mul] using h1

omit [AddCommGroup V] [Module ℝ V] [T2Space V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [MeasurableSpace V] [OpensMeasurableSpace V] in
/-- The truncation `min g n` of a lower semicontinuous `ℝ≥0∞`-valued function is lower
semicontinuous, in the real-valued sense, after `ENNReal.toReal`. -/
theorem _root_.LowerSemicontinuousOn.toReal_min {s : Set V}
    (hg : LowerSemicontinuousOn g s) (n : ℝ≥0) :
    LowerSemicontinuousOn (fun y => (min (g y) (n : ℝ≥0∞)).toReal) s := by
  intro y hy r hr
  rcases lt_or_ge r 0 with hr0 | hr0
  · exact Eventually.of_forall fun w => lt_of_lt_of_le hr0 ENNReal.toReal_nonneg
  have hne : ∀ v : V, min (g v) (n : ℝ≥0∞) ≠ ∞ :=
    fun v => ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hlt : ENNReal.ofReal r < min (g y) (n : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal (hne y)]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0 |>.2 hr
  filter_upwards [hg y hy (ENNReal.ofReal r) (lt_of_lt_of_le hlt (min_le_left _ _))] with w hw
  have : ENNReal.ofReal r < min (g w) (n : ℝ≥0∞) :=
    lt_min hw (lt_of_lt_of_le hlt (min_le_right _ _))
  have := ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (hne w) |>.2 this
  rwa [ENNReal.toReal_ofReal hr0] at this


/-- Convexity of an `ℝ≥0∞`-valued function on a set. Together with `ConcaveOnENNReal` this is
affineness with values in `[0, ∞]`, the setting of Georgii's excess free energy. -/
def _root_.ConvexOnENNReal (s : Set V) (g : V → ℝ≥0∞) : Prop :=
  ∀ ⦃y⦄, y ∈ s → ∀ ⦃w⦄, w ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    g (a • y + b • w) ≤ ENNReal.ofReal a * g y + ENNReal.ofReal b * g w

/-- The epigraph of an `ℝ≥0∞`-valued function over `K`, inside `V × ℝ`; only nonnegative heights
are used, so that `ENNReal.ofReal` is additive along convex combinations. -/
def _root_.epigraphENNReal (K : Set V) (g : V → ℝ≥0∞) : Set (V × ℝ) :=
  {p | p.1 ∈ K ∧ 0 ≤ p.2 ∧ g p.1 ≤ ENNReal.ofReal p.2}

omit [TopologicalSpace V] [T2Space V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem _root_.convex_epigraphENNReal (hKconv : Convex ℝ K) (hgconv : ConvexOnENNReal K g) :
    Convex ℝ (epigraphENNReal K g) := by
  rintro ⟨y, s⟩ ⟨hyK, hs0, hs⟩ ⟨w, t⟩ ⟨hwK, ht0, ht⟩ a b ha hb hab
  have has : 0 ≤ a * s := mul_nonneg ha hs0
  have hbt : 0 ≤ b * t := mul_nonneg hb ht0
  refine ⟨hKconv hyK hwK ha hb hab, by simpa using add_nonneg has hbt, ?_⟩
  calc g (a • y + b • w) ≤ ENNReal.ofReal a * g y + ENNReal.ofReal b * g w :=
        hgconv hyK hwK ha hb hab
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal s + ENNReal.ofReal b * ENNReal.ofReal t := by gcongr
    _ = ENNReal.ofReal (a • s + b • t) := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
          ← ENNReal.ofReal_add has hbt]
        rfl

omit [AddCommGroup V] [Module ℝ V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem _root_.isClosed_epigraphENNReal (hK : IsCompact K) (hglsc : LowerSemicontinuousOn g K) :
    IsClosed (epigraphENNReal K g) := by
  set Op : Set (V × ℝ) :=
    ⋃₀ {U | IsOpen U ∧ ∀ p ∈ U, p.1 ∈ K → ENNReal.ofReal p.2 < g p.1} with hOp
  have hOpen : IsOpen Op := isOpen_sUnion fun U hU => hU.1
  have hsub : ∀ p : V × ℝ, p.1 ∈ K → ENNReal.ofReal p.2 < g p.1 → p ∈ Op := by
    rintro ⟨y, t⟩ hyK hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    obtain ⟨W, hWopen, hyW, hWsub⟩ := mem_nhdsWithin.1 (hglsc y hyK c hc2)
    refine ⟨W ×ˢ {t' : ℝ | ENNReal.ofReal t' < c},
      ⟨hWopen.prod (isOpen_lt (ENNReal.continuous_ofReal.comp continuous_id) continuous_const),
        ?_⟩, hyW, hc1⟩
    rintro ⟨y', t'⟩ ⟨hy', ht'⟩ hy'K
    exact lt_trans ht' (hWsub ⟨hy', hy'K⟩)
  have hEq : epigraphENNReal K g = (K ×ˢ Ici (0 : ℝ)) \ Op := by
    ext ⟨y, t⟩
    constructor
    · rintro ⟨hyK, ht0, ht⟩
      refine ⟨⟨hyK, ht0⟩, fun hmem => ?_⟩
      obtain ⟨U, hU, hyU⟩ := hmem
      exact absurd (hU.2 _ hyU hyK) (not_lt.2 ht)
    · rintro ⟨⟨hyK, ht0⟩, hnot⟩
      exact ⟨hyK, ht0, not_lt.1 fun hlt => hnot (hsub (y, t) hyK hlt)⟩
  rw [hEq]
  exact (hK.isClosed.prod isClosed_Ici).sdiff hOpen

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
/-- **The minorant lemma for `[0, ∞]`-valued convex lower semicontinuous functions.** Below any
value `r < g x` at a point of a compact convex set there is a continuous affine function
`y ↦ l y + d` with `ENNReal.ofReal (l y + d) ≤ g y` on `K` and `r < l x + d`.

This is `ConvexOn.exists_affine_le_of_lt` for functions that may take the value `∞`: the epigraph
`{(y, t) | y ∈ K, 0 ≤ t, g y ≤ ofReal t}` is closed and convex, and `(x, r)` is separated from it
by Hahn-Banach. The functional `L` obtained has nonnegative last coordinate `κ`; if `κ > 0` the
separating hyperplane is the graph of the minorant, and if `κ = 0` a large multiple of the
separating functional works because `g ≥ 0`. -/
theorem _root_.ConvexOnENNReal.exists_affine_le_of_lt (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hglsc : LowerSemicontinuousOn g K) (hgconv : ConvexOnENNReal K g)
    {r : ℝ} (hr : 0 ≤ r) (hlt : ENNReal.ofReal r < g x) :
    ∃ (l : V →L[ℝ] ℝ) (d : ℝ), (∀ y ∈ K, ENNReal.ofReal (l y + d) ≤ g y) ∧ r < l x + d := by
  by_cases hall : ∀ y ∈ K, g y = ⊤
  · exact ⟨0, r + 1, fun y hy => by rw [hall y hy]; exact le_top, by simp⟩
  push Not at hall
  obtain ⟨y₀, hy₀K, hy₀⟩ := hall
  have hnot : (x, r) ∉ epigraphENNReal K g := fun h => absurd h.2.2 (not_le.2 hlt)
  obtain ⟨L, u, hLx, hLE⟩ := geometric_hahn_banach_point_closed
    (convex_epigraphENNReal hKconv hgconv) (isClosed_epigraphENNReal hK hglsc) hnot
  set l : V →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ V ℝ) with hl
  set κ : ℝ := L (0, 1) with hκ
  have hLeq : ∀ (y : V) (t : ℝ), L (y, t) = l y + t * κ := by
    intro y t
    have h1 : ((y, t) : V × ℝ) = (y, 0) + (0, t) := by simp
    have h2 : ((0, t) : V × ℝ) = t • ((0, 1) : V × ℝ) := by simp
    rw [h1, map_add, h2, map_smul]
    simp [hl, hκ]
  have hmemE : ∀ y ∈ K, g y ≠ ⊤ → ((y, (g y).toReal) : V × ℝ) ∈ epigraphENNReal K g :=
    fun y hy hfin => ⟨hy, ENNReal.toReal_nonneg, by rw [ENNReal.ofReal_toReal hfin]⟩
  have hEfin : ∀ y ∈ K, g y ≠ ⊤ → u < l y + (g y).toReal * κ := by
    intro y hy hfin
    have := hLE _ (hmemE y hy hfin)
    rwa [hLeq] at this
  have hLx' : l x + r * κ < u := by rw [hLeq] at hLx; exact hLx
  -- `κ ≥ 0`, because the epigraph is stable under increasing the height
  have hκ0 : 0 ≤ κ := by
    by_contra hcon
    push Not at hcon
    have hall' : ∀ t : ℝ, (g y₀).toReal ≤ t → u < l y₀ + t * κ := by
      intro t ht
      have hmem : ((y₀, t) : V × ℝ) ∈ epigraphENNReal K g :=
        ⟨hy₀K, le_trans ENNReal.toReal_nonneg ht,
          le_trans (le_of_eq (ENNReal.ofReal_toReal hy₀).symm) (ENNReal.ofReal_le_ofReal ht)⟩
      have := hLE _ hmem
      rwa [hLeq] at this
    set t : ℝ := max ((g y₀).toReal) ((u - l y₀) / κ) with hT
    have h1 := hall' t (le_max_left _ _)
    have h2 : (u - l y₀) / κ ≤ t := le_max_right _ _
    have h3 : t * κ ≤ (u - l y₀) / κ * κ := mul_le_mul_of_nonpos_right h2 hcon.le
    rw [div_mul_cancel₀ _ (ne_of_lt hcon)] at h3
    linarith
  rcases eq_or_lt_of_le hκ0 with hκeq | hκpos
  · -- `κ = 0`: a large multiple of the separating functional is a minorant
    have hxlt : l x < u := by rw [← hκeq] at hLx'; linarith
    have hKlt : ∀ y ∈ K, g y ≠ ⊤ → u < l y := by
      intro y hy hfin
      have := hEfin y hy hfin
      rw [← hκeq] at this
      linarith
    set lam : ℝ := (r + 1) / (u - l x) with hlam
    have hlampos : 0 < lam := div_pos (by linarith) (by linarith)
    have hne : u - l x ≠ 0 := ne_of_gt (by linarith)
    have hlamu : lam * (u - l x) = r + 1 := by rw [hlam]; field_simp
    refine ⟨(-lam) • l, lam * u, fun y hy => ?_, ?_⟩
    · by_cases hfin : g y = ⊤
      · rw [hfin]; exact le_top
      · have hy' := hKlt y hy hfin
        have hle : ((-lam) • l) y + lam * u ≤ 0 := by
          simp only [smul_apply, smul_eq_mul]
          nlinarith
        rw [ENNReal.ofReal_eq_zero.2 hle]
        exact bot_le
    · simp only [smul_apply, smul_eq_mul]
      nlinarith
  · -- `κ > 0`: the separating hyperplane is the graph of the minorant
    have hκne : κ ≠ 0 := ne_of_gt hκpos
    refine ⟨(-κ⁻¹) • l, u / κ, fun y hy => ?_, ?_⟩
    · by_cases hfin : g y = ⊤
      · rw [hfin]; exact le_top
      · have hEp := hEfin y hy hfin
        have hrw : ((-κ⁻¹) • l) y + u / κ = (u - l y) / κ := by
          simp only [smul_apply, smul_eq_mul]
          field_simp
          ring
        have hlt' : ((-κ⁻¹) • l) y + u / κ ≤ (g y).toReal := by
          rw [hrw, div_le_iff₀ hκpos]
          linarith
        calc ENNReal.ofReal (((-κ⁻¹) • l) y + u / κ) ≤ ENNReal.ofReal ((g y).toReal) :=
              ENNReal.ofReal_le_ofReal hlt'
          _ = g y := ENNReal.ofReal_toReal hfin
    · have hrw : ((-κ⁻¹) • l) x + u / κ = (u - l x) / κ := by
        simp only [smul_apply, smul_eq_mul]
        field_simp
        ring
      rw [hrw, lt_div_iff₀ hκpos]
      linarith

/-- **The `ℝ≥0∞`-valued half of Phelps' Lemma 9.7 that Georgii uses.** If `g` takes values in
`[0, ∞]`, is lower semicontinuous and concave on a compact convex set `K` carrying the probability
measure `μ`, then `∫⁻ g dμ ≤ g x` at the barycentre `x`.

No integrability or boundedness hypothesis is needed: the statement is obtained from the
real-valued concave Jensen inequality
(`MeasureTheory.IsBarycenter.integral_le_of_concaveOn`) applied to the bounded truncations
`(min g n).toReal`, together with monotone convergence. -/
theorem IsBarycenter.lintegral_le_of_concaveENNReal [μ.WeaklyRegular] [IsProbabilityMeasure μ]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hμ : μ Kᶜ = 0) (hx : IsBarycenter μ x)
    (hgm : Measurable g) (hglsc : LowerSemicontinuousOn g K) (hgconc : ConcaveOnENNReal K g) :
    ∫⁻ y, g y ∂μ ≤ g x := by
  have hne : ∀ (n : ℕ) (v : V), min (g v) (n : ℝ≥0∞) ≠ ∞ :=
    fun n v => ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  -- the truncated integrals
  have hstep : ∀ n : ℕ, ∫⁻ y, min (g y) (n : ℝ≥0∞) ∂μ ≤ g x := by
    intro n
    set fn : V → ℝ := fun y => (min (g y) (n : ℝ≥0∞)).toReal with hfn
    have hmeas : Measurable fn := (hgm.min measurable_const).ennreal_toReal
    have hbdd : ∀ y, fn y ≤ (n : ℝ) := by
      intro y
      have := ENNReal.toReal_mono (by simp : ((n : ℝ≥0∞)) ≠ ∞) (min_le_right (g y) (n : ℝ≥0∞))
      simpa [hfn] using this
    have hnn : ∀ y, 0 ≤ fn y := fun y => ENNReal.toReal_nonneg
    have hint : Integrable fn μ :=
      (integrable_const (n : ℝ)).mono' hmeas.aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn y)]
                                          exact hbdd y)
    have hconc : ConcaveOn ℝ K fn :=
      ConcaveOnENNReal.concaveOn_toReal_min hKconv hgconc (n : ℝ≥0)
    have hlsc : LowerSemicontinuousOn fn K := LowerSemicontinuousOn.toReal_min hglsc (n : ℝ≥0)
    have hb : BddAbove (fn '' K) := ⟨(n : ℝ), by rintro _ ⟨y, -, rfl⟩; exact hbdd y⟩
    have hmain := hx.integral_le_of_concaveOn hK hμ hconc hlsc hint hb
    have hle : ENNReal.ofReal (∫ y, fn y ∂μ) ≤ ENNReal.ofReal (fn x) :=
      ENNReal.ofReal_le_ofReal hmain
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)] at hle
    calc ∫⁻ y, min (g y) (n : ℝ≥0∞) ∂μ
        = ∫⁻ y, ENNReal.ofReal (fn y) ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [hfn, ENNReal.ofReal_toReal (hne n y)]
      _ ≤ ENNReal.ofReal (fn x) := hle
      _ = min (g x) (n : ℝ≥0∞) := by rw [hfn, ENNReal.ofReal_toReal (hne n x)]
      _ ≤ g x := min_le_left _ _
  -- monotone convergence
  have hsup : ∀ y : V, ⨆ n : ℕ, min (g y) (n : ℝ≥0∞) = g y := by
    intro y
    refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
    rcases eq_or_ne (g y) ∞ with h | h
    · have heq : ∀ n : ℕ, min (g y) (n : ℝ≥0∞) = (n : ℝ≥0∞) := fun n => by
        rw [h]; exact min_eq_right le_top
      refine le_of_eq ?_
      calc g y = ∞ := h
        _ = ⨆ n : ℕ, (n : ℝ≥0∞) := ENNReal.iSup_natCast.symm
        _ = ⨆ n : ℕ, min (g y) (n : ℝ≥0∞) := (iSup_congr heq).symm
    · obtain ⟨n, hn⟩ := exists_nat_ge (g y).toReal
      refine le_iSup_of_le n ?_
      rw [min_eq_left]
      rw [← ENNReal.ofReal_toReal h]
      exact (ENNReal.ofReal_le_ofReal hn).trans (by simp)
  calc ∫⁻ y, g y ∂μ = ∫⁻ y, ⨆ n : ℕ, min (g y) (n : ℝ≥0∞) ∂μ := by
        simp_rw [hsup]
    _ = ⨆ n : ℕ, ∫⁻ y, min (g y) (n : ℝ≥0∞) ∂μ := by
        refine lintegral_iSup (fun n => hgm.min measurable_const) ?_
        intro a b hab y
        exact min_le_min_left _ (by exact_mod_cast hab)
    _ ≤ g x := iSup_le hstep


/-- **The convex half of Phelps' Lemma 9.7, with values in `[0, ∞]`.** If `g : K → [0, ∞]` is
convex and lower semicontinuous on a compact convex set `K` carrying the probability measure `μ`,
then `g x ≤ ∫⁻ g dμ` at the barycentre `x`. -/
theorem IsBarycenter.le_lintegral_of_convexENNReal [IsProbabilityMeasure μ]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hμ : μ Kᶜ = 0) (hx : IsBarycenter μ x)
    (hglsc : LowerSemicontinuousOn g K) (hgconv : ConvexOnENNReal K g) :
    g x ≤ ∫⁻ y, g y ∂μ := by
  have hxK : x ∈ K := hx.mem_of_convex hK hKconv hμ
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨c', hc1, hc2⟩ := exists_between hc
  have hc'fin : c' ≠ ⊤ := ne_top_of_lt hc2
  have hr0 : (0 : ℝ) ≤ c'.toReal := ENNReal.toReal_nonneg
  have hreq : ENNReal.ofReal c'.toReal = c' := ENNReal.ofReal_toReal hc'fin
  have hc2' : ENNReal.ofReal c'.toReal < g x := by rw [hreq]; exact hc2
  obtain ⟨l, d, hle, hgt⟩ :=
    ConvexOnENNReal.exists_affine_le_of_lt hK hKconv hglsc hgconv hr0 hc2'
  set h : V → ℝ := fun y => max (l y + d) 0 with hh
  have hcont : Continuous h := (l.continuous.add continuous_const).max continuous_const
  have hnn : ∀ y, 0 ≤ h y := fun y => le_max_right _ _
  have hint : Integrable h μ :=
    hcont.integrable_of_ae_mem_isCompact hK hK.measurableSet (mem_ae_iff.2 hμ)
  have hint' : Integrable (fun y => l y + d) μ :=
    (l.integrable_of_measure_compl_eq_zero hK hμ).add (integrable_const d)
  have hmono : ∫ y, (l y + d) ∂μ ≤ ∫ y, h y ∂μ :=
    integral_mono hint' hint fun y => le_max_left _ _
  have hbar : ∫ y, (l y + d) ∂μ = l x + d := by
    rw [integral_add (l.integrable_of_measure_compl_eq_zero hK hμ) (integrable_const d),
      hx l, integral_const]
    simp
  have hlin : ∫⁻ y, ENNReal.ofReal (h y) ∂μ ≤ ∫⁻ y, g y ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [(mem_ae_iff.2 hμ : ∀ᵐ y ∂μ, y ∈ K)] with y hy
    have : ENNReal.ofReal (h y) = ENNReal.ofReal (l y + d) := by
      simp only [hh]
      rcases le_or_gt (l y + d) 0 with hcase | hcase
      · rw [max_eq_right hcase]
        simp [ENNReal.ofReal_eq_zero.2 hcase]
      · rw [max_eq_left hcase.le]
    rw [this]
    exact hle y hy
  refine lt_of_lt_of_le hc1 (le_trans ?_ hlin)
  rw [← hreq, ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

/-- **Phelps' Lemma 9.7, with values in `[0, ∞]`.** An affine lower semicontinuous
`g : K → [0, ∞]` on a compact convex set commutes with barycentres: `∫⁻ g dμ = g x`. This is the
form Georgii's excess free energy functional `𝒜(· | Φ) : 𝒫_Θ → [0, ∞]` needs — no integrability
or boundedness hypothesis, and the value `∞` is allowed. -/
theorem IsBarycenter.lintegral_eq_of_affineENNReal [μ.WeaklyRegular] [IsProbabilityMeasure μ]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hμ : μ Kᶜ = 0) (hx : IsBarycenter μ x)
    (hgm : Measurable g) (hglsc : LowerSemicontinuousOn g K)
    (hgconv : ConvexOnENNReal K g) (hgconc : ConcaveOnENNReal K g) :
    ∫⁻ y, g y ∂μ = g x :=
  le_antisymm (hx.lintegral_le_of_concaveENNReal hK hKconv hμ hgm hglsc hgconc)
    (hx.le_lintegral_of_convexENNReal hK hKconv hμ hglsc hgconv)

end ENNRealJensen



/-! ### The infimum of a concave lower semicontinuous function on a closed convex hull -/

section ClosedConvexHull

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [T2Space V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace.PseudoMetrizableSpace V] [MeasurableSpace V] [BorelSpace V]
  {K C : Set V} {x : V} {g : V → ℝ≥0∞}

/-- A concave lower semicontinuous `g : K → [0, ∞]` on a compact convex set is bounded below on
the closed convex hull of a closed subset `C` by its infimum over `C` itself.

Every point of `closedConvexHull ℝ C` is the barycentre of a probability measure carried by `C`
(`MeasureTheory.exists_isBarycenter_of_mem_closedConvexHull`), and a concave lower semicontinuous
function dominates its average at the barycentre
(`MeasureTheory.IsBarycenter.lintegral_le_of_concaveENNReal`). Note that this fails for a merely
lower semicontinuous function: passing to the closed convex hull can decrease an infimum. -/
theorem _root_.iInf_le_of_mem_closedConvexHull
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hC : IsClosed C) (hCK : C ⊆ K)
    (hgm : Measurable g) (hglsc : LowerSemicontinuousOn g K) (hgconc : ConcaveOnENNReal K g)
    (hx : x ∈ closedConvexHull ℝ C) :
    (⨅ ν ∈ C, g ν) ≤ g x := by
  obtain ⟨w, hwprob, hwC, hwbar⟩ :=
    exists_isBarycenter_of_mem_closedConvexHull hK hKconv hC hCK hx
  have : IsProbabilityMeasure w := hwprob
  have hwK : w Kᶜ = 0 := measure_mono_null (compl_subset_compl.2 hCK) hwC
  calc (⨅ ν ∈ C, g ν) = ∫⁻ _ν, (⨅ ν ∈ C, g ν) ∂w := by simp
    _ ≤ ∫⁻ ν, g ν ∂w := lintegral_mono_ae (by
        filter_upwards [mem_ae_iff.2 hwC] with ν hν using iInf₂_le ν hν)
    _ ≤ g x := hwbar.lintegral_le_of_concaveENNReal hK hKconv hwK hgm hglsc hgconc

/-- **Georgii (15.54).** On a compact convex set `K`, the infimum of a concave lower
semicontinuous `g : K → [0, ∞]` over the closed convex hull of a subset `C` coincides with its
infimum over the closure of `C`.

This is Step 3 of Georgii's proof of the large-deviation upper bound (15.46): the upper bound is
first proved with the closed convex hull of `C` on the right-hand side, and this identity removes
the convex hull. Georgii's `𝒜(· | Φ)` is affine — hence in particular concave — and lower
semicontinuous, with values in `[0, ∞]`. -/
theorem _root_.iInf_closedConvexHull_eq_iInf_closure
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hCK : C ⊆ K)
    (hgm : Measurable g) (hglsc : LowerSemicontinuousOn g K) (hgconc : ConcaveOnENNReal K g) :
    (⨅ ν ∈ closedConvexHull ℝ C, g ν) = ⨅ ν ∈ closure C, g ν := by
  have hclC : closure C ⊆ closedConvexHull ℝ C := closure_subset_closedConvexHull
  have hcch : closedConvexHull ℝ C ⊆ closedConvexHull ℝ (closure C) :=
    le_of_eq closedConvexHull_closure_eq_closedConvexHull.symm
  refine le_antisymm (le_iInf₂ fun ν hν => iInf₂_le ν (hclC hν)) (le_iInf₂ fun ν hν => ?_)
  exact iInf_le_of_mem_closedConvexHull hK hKconv isClosed_closure
    (closure_minimal hCK hK.isClosed) hgm hglsc hgconc (hcch hν)

end ClosedConvexHull

end MeasureTheory
