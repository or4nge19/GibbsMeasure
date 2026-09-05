/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Barycentres of measures on a compact convex set

Let `V` be a real topological vector space. A point `x : V` is a *barycentre* (Phelps calls it the
*resultant*) of a measure `μ` on `V` if

`∫ y, ℓ y ∂μ = ℓ x` for every continuous linear functional `ℓ : V →L[ℝ] ℝ`,

that is, if `x` represents `μ` weakly. This is the notion of barycentre used in Choquet theory; it
does not presuppose a Bochner integral, so it makes sense on a locally convex space that is not
normed. When `V` *is* a Banach space and `id` is integrable, the barycentre is the Bochner integral
`∫ y, y ∂μ` (`MeasureTheory.isBarycenter_integral`).

## Main definitions

* `MeasureTheory.IsBarycenter μ x`: `x` is a barycentre of `μ`.

## Main statements

* `MeasureTheory.IsBarycenter.unique`: in a locally convex Hausdorff space a measure has at most
  one barycentre, by Hahn-Banach separation of points.
* `MeasureTheory.exists_isBarycenter_of_isCompact`, **existence of the barycentre**: a probability
  measure carried by a compact convex set `K` has a barycentre, and it lies in `K`. The proof is
  the finite intersection property: for finitely many functionals `ℓ₁, …, ℓₙ` the vector of
  integrals `(∫ ℓ₁ dμ, …, ∫ ℓₙ dμ)` lies in the compact convex set `(ℓ₁, …, ℓₙ) '' K ⊆ ℝⁿ` by
  Jensen's inequality for convex sets (`Convex.integral_mem`), so the closed sets
  `{x ∈ K | ℓ x = ∫ ℓ dμ}` have the finite intersection property.
* `MeasureTheory.IsBarycenter.mem_closedConvexHull`, the elementary half of the representation
  theorem: the barycentre of a probability measure carried by a compact set `C` lies in the closed
  convex hull of `C`. A separating functional would otherwise bound the integral away from its
  value.
* `MeasureTheory.exists_isBarycenter_of_mem_closedConvexHull`, **the representation theorem**:
  conversely, if `C` is a closed subset of a compact convex set `K`, then *every*
  point of the closed convex hull of `C` is the barycentre of a probability measure carried by
  `C`. The set of such barycentres contains `C` (Dirac measures), is convex (mixtures) and is
  compact, hence closed: it is the image of a closed subset of
  `ProbabilityMeasure C × K` — compact because the space of probability measures on a compact
  space is compact (`instCompactSpaceProbabilityMeasure`, a consequence of
  Riesz-Markov-Kakutani) — under a continuous map.
* `MeasureTheory.mem_closedConvexHull_iff_exists_isBarycenter`: the two previous statements
  combined, the form in which Choquet theory uses them.

## Implementation notes

Measures are `MeasureTheory.Measure V` on the ambient space `V`, and "`μ` is carried by `C`" is
`μ Cᶜ = 0`; this is Phelps' phrasing (a measure on `K` "represents" a point) and it is what a
consumer of the theory has: a measure on the ambient space that happens to sit on a small set.
Measures on the subtype `↥C` and the type `MeasureTheory.ProbabilityMeasure ↥C` appear only inside
the proof of `MeasureTheory.exists_isBarycenter_of_mem_closedConvexHull`, where the weak topology
on probability measures and its compactness are needed; the passage back to `V` is
`MeasureTheory.Measure.map Subtype.val`, wrapped in `MeasureTheory.isBarycenter_map`.

`MeasureTheory.IsBarycenter` is *not* stated with an integrability side condition: since the
Bochner integral of a non-integrable function is `0` by convention, restricting the identity to
the integrable functionals would *weaken* the definition. Every result below either assumes a
compact carrier — whence integrability of the continuous functionals,
`Continuous.integrable_of_ae_mem_isCompact` — or takes integrability as a hypothesis.

## References

* R. R. Phelps, *Lectures on Choquet's Theorem*, Lecture Notes in Mathematics 1757, Springer
  2001, §1: the resultant of a measure on a compact convex set, and the measures representing the
  points of a closed convex hull.
* H.-O. Georgii, *Gibbs Measures and Phase Transitions*, 2nd edition: Step 3 of the proof of
  Theorem (15.46) is an application of these facts, cited there as Proposition 1.2 and Lemma 9.7
  of Phelps (1966).
-/

@[expose] public section

open BoundedContinuousFunction Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory

section Defs

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [MeasurableSpace V]
  {μ ν : Measure V} {x y : V}

/-- `IsBarycenter μ x` states that the point `x` is a *barycentre* of the measure `μ`: every
continuous linear functional takes at `x` the value of its `μ`-average,
`∫ y, ℓ y ∂μ = ℓ x`. Phelps calls `x` the *resultant* `r(μ)` of `μ`.

In a locally convex Hausdorff space a measure has at most one barycentre
(`MeasureTheory.IsBarycenter.unique`), and a probability measure carried by a compact convex set
has one (`MeasureTheory.exists_isBarycenter_of_isCompact`). -/
def IsBarycenter (μ : Measure V) (x : V) : Prop :=
  ∀ ℓ : StrongDual ℝ V, ∫ y, ℓ y ∂μ = ℓ x

theorem isBarycenter_iff : IsBarycenter μ x ↔ ∀ ℓ : StrongDual ℝ V, ∫ y, ℓ y ∂μ = ℓ x := Iff.rfl

/-- A point is the barycentre of the Dirac mass at that point. -/
theorem isBarycenter_dirac [OpensMeasurableSpace V] (x : V) :
    IsBarycenter (Measure.dirac x) x :=
  fun ℓ => integral_dirac' _ x ℓ.continuous.stronglyMeasurable

/-- Barycentres are affine in the measure: if `x` is a barycentre of `μ` and `y` one of `ν`, then
`a • x + b • y` is a barycentre of the mixture `a • μ + b • ν` for any `a, b ≥ 0`; in particular
for a convex combination, `a + b = 1`. -/
theorem IsBarycenter.smul_add_smul {a b : ℝ} (hx : IsBarycenter μ x) (hy : IsBarycenter ν y)
    (hμ : ∀ ℓ : StrongDual ℝ V, Integrable ℓ μ) (hν : ∀ ℓ : StrongDual ℝ V, Integrable ℓ ν)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsBarycenter (ENNReal.ofReal a • μ + ENNReal.ofReal b • ν) (a • x + b • y) := by
  intro ℓ
  rw [integral_add_measure ((hμ ℓ).smul_measure (by simp)) ((hν ℓ).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, hx ℓ, hy ℓ, map_add, map_smul, map_smul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

/-- The barycentre condition is invariant under pushing a measure forward: if `x` weakly
represents the `μ`-averages of `ℓ ∘ f` for every functional `ℓ`, then `x` is a barycentre of the
image measure `μ.map f`. -/
theorem isBarycenter_map [OpensMeasurableSpace V] {Ω : Type*} [MeasurableSpace Ω] {m : Measure Ω}
    {f : Ω → V} (hf : AEMeasurable f m) (h : ∀ ℓ : StrongDual ℝ V, ∫ ω, ℓ (f ω) ∂m = ℓ x) :
    IsBarycenter (m.map f) x := fun ℓ => by
  rw [integral_map hf ℓ.continuous.aestronglyMeasurable]; exact h ℓ

end Defs

section Affine

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] {μ : Measure V} {x : V}

/-- The defining identity of a barycentre holds for every *continuous affine* functional, not just
for the linear ones: this is the form in which Choquet theory uses barycentres. -/
theorem IsBarycenter.integral_continuousAffineMap [IsProbabilityMeasure μ] (hx : IsBarycenter μ x)
    (f : V →ᴬ[ℝ] ℝ) (hf : Integrable f μ) : ∫ y, f y ∂μ = f x := by
  have hdecomp : ∀ y : V, f y = f.contLinear y + f 0 := fun y => by simpa using f.map_vadd 0 y
  have hsub : (fun y => f.contLinear y) = fun y => f y - f 0 :=
    funext fun y => by rw [hdecomp y]; ring
  have hlin : Integrable (fun y => f.contLinear y) μ := hsub ▸ hf.sub (integrable_const (f 0))
  have h1 : ∫ y, f y ∂μ = ∫ y, (f.contLinear y + f 0) ∂μ :=
    integral_congr_ae (.of_forall hdecomp)
  rw [h1, integral_add hlin (integrable_const _), hx f.contLinear, integral_const]
  simp [hdecomp x]

end Affine

section Unique

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [MeasurableSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V] [T1Space V]
  {μ : Measure V} {x y : V}

/-- A measure on a locally convex Hausdorff space has at most one barycentre: the continuous
linear functionals separate the points of `V` (Hahn-Banach). -/
theorem IsBarycenter.unique (hx : IsBarycenter μ x) (hy : IsBarycenter μ y) : x = y := by
  by_contra hxy
  obtain ⟨ℓ, hℓ⟩ := geometric_hahn_banach_point_point hxy
  exact absurd ((hx ℓ).symm.trans (hy ℓ)) hℓ.ne

end Unique

section Banach

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] {μ : Measure V}

/-- In a Banach space the barycentre of an integrable measure is its Bochner integral. -/
theorem isBarycenter_integral (hμ : Integrable id μ) : IsBarycenter μ (∫ y, y ∂μ) :=
  fun ℓ => ℓ.integral_comp_comm hμ

end Banach

/-!
### Existence: Phelps, Proposition 1.1
-/

section Exists

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [T2Space V]
  [MeasurableSpace V] [OpensMeasurableSpace V] {K : Set V} {μ : Measure V}

/-- A continuous linear functional is integrable against a finite measure carried by a compact
set. -/
theorem _root_.ContinuousLinearMap.integrable_of_measure_compl_eq_zero [IsFiniteMeasure μ]
    (ℓ : StrongDual ℝ V) (hK : IsCompact K) (hμ : μ Kᶜ = 0) : Integrable ℓ μ :=
  ℓ.continuous.integrable_of_ae_mem_isCompact hK hK.measurableSet (mem_ae_iff.2 hμ)

/-- **Existence of the barycentre** (Phelps, §1): a probability measure carried by a compact
convex set `K` has a barycentre, and it lies in `K`.

The sets `{x | ℓ x = ∫ ℓ dμ}`, for `ℓ` a continuous linear functional, are closed, and they meet
`K` in a family with the finite intersection property: for a finite family `u` of functionals, put
`T = (ℓ)_{ℓ ∈ u} : V →L[ℝ] (u → ℝ)`; then `T '' K` is compact and convex and carries `T` almost
everywhere, so `∫ T dμ ∈ T '' K` by Jensen's inequality for convex sets, and a preimage of
`∫ T dμ` in `K` lies in all the sets `{x | ℓ x = ∫ ℓ dμ}` for `ℓ ∈ u`. Compactness of `K` finishes
the proof. Uniqueness is `MeasureTheory.IsBarycenter.unique`. -/
theorem exists_isBarycenter_of_isCompact (hK : IsCompact K) (hKconv : Convex ℝ K) (μ : Measure V)
    [IsProbabilityMeasure μ] (hμ : μ Kᶜ = 0) : ∃ x ∈ K, IsBarycenter μ x := by
  have hae : ∀ᵐ y ∂μ, y ∈ K := mem_ae_iff.2 hμ
  have key : ∀ u : Finset (StrongDual ℝ V),
      (K ∩ ⋂ ℓ ∈ u, {y : V | ℓ y = ∫ z, ℓ z ∂μ}).Nonempty := by
    intro u
    set T : V →L[ℝ] ({ℓ' // ℓ' ∈ u} → ℝ) :=
      ContinuousLinearMap.pi fun ℓ : u => (ℓ : StrongDual ℝ V) with hT
    have hTi : Integrable (fun y => T y) μ :=
      T.continuous.integrable_of_ae_mem_isCompact hK hK.measurableSet hae
    obtain ⟨x, hxK, hxT⟩ : (∫ y, T y ∂μ) ∈ T '' K :=
      Convex.integral_mem (hKconv.linear_image T.toLinearMap) (hK.image T.continuous).isClosed
        (hae.mono fun y hy => mem_image_of_mem _ hy) hTi
    refine ⟨x, hxK, mem_iInter₂.2 fun ℓ hℓ => ?_⟩
    have h1 := ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {ℓ' // ℓ' ∈ u} => ℝ) ⟨ℓ, hℓ⟩) hTi
    have h2 : (T x) ⟨ℓ, hℓ⟩ = (∫ y, T y ∂μ) ⟨ℓ, hℓ⟩ := congrFun hxT _
    simpa [hT] using h2.trans h1.symm
  obtain ⟨x, hxK, hx⟩ :=
    hK.inter_iInter_nonempty _ (fun ℓ : StrongDual ℝ V => isClosed_eq ℓ.continuous continuous_const)
      key
  exact ⟨x, hxK, fun ℓ => (mem_iInter.1 hx ℓ).symm⟩

end Exists

/-!
### The barycentre lies in the closed convex hull of the carrier
-/

section MemClosedConvexHull

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [T2Space V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V] [MeasurableSpace V]
  [OpensMeasurableSpace V] {C K : Set V} {μ : Measure V} {x : V}

omit [T2Space V] [OpensMeasurableSpace V] in
/-- The elementary half of the representation theorem, in the form that only asks for
integrability: a barycentre of a probability measure carried by `C` lies in the closed convex hull
of `C`. -/
theorem IsBarycenter.mem_closedConvexHull_of_integrable [IsProbabilityMeasure μ]
    (hint : ∀ ℓ : StrongDual ℝ V, Integrable ℓ μ) (hμ : μ Cᶜ = 0) (hx : IsBarycenter μ x) :
    x ∈ closedConvexHull ℝ C := by
  by_contra hxC
  obtain ⟨ℓ, u, hℓx, hℓC⟩ :=
    geometric_hahn_banach_point_closed convex_closedConvexHull isClosed_closedConvexHull hxC
  have hle : ∀ᵐ y ∂μ, u ≤ ℓ y := by
    filter_upwards [(mem_ae_iff.2 hμ : ∀ᵐ y ∂μ, y ∈ C)] with y hy
    exact (hℓC y (subset_closedConvexHull hy)).le
  have h : u ≤ ∫ y, ℓ y ∂μ := by
    have := integral_mono_ae (integrable_const u) (hint ℓ) hle
    simpa using this
  rw [hx ℓ] at h
  exact absurd h (not_le.2 hℓx)

/-- The elementary half of the representation theorem (Phelps, §1): the barycentre of a
probability measure carried by a compact set `C` lies in the closed convex hull of `C`. -/
theorem IsBarycenter.mem_closedConvexHull [IsProbabilityMeasure μ] (hC : IsCompact C)
    (hμ : μ Cᶜ = 0) (hx : IsBarycenter μ x) : x ∈ closedConvexHull ℝ C :=
  hx.mem_closedConvexHull_of_integrable
    (fun ℓ => ℓ.integrable_of_measure_compl_eq_zero hC hμ) hμ

/-- The barycentre of a probability measure carried by a compact convex set `K` lies in `K`. -/
theorem IsBarycenter.mem_of_convex [IsProbabilityMeasure μ] (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hμ : μ Kᶜ = 0) (hx : IsBarycenter μ x) : x ∈ K :=
  closedConvexHull_min Subset.rfl hKconv hK.isClosed (hx.mem_closedConvexHull hK hμ)

/-- **Existence and uniqueness of the barycentre** (Phelps, §1): a probability measure carried by
a compact convex set has a *unique* barycentre. It lies in the set, by
`MeasureTheory.IsBarycenter.mem_of_convex`. -/
theorem existsUnique_isBarycenter [IsProbabilityMeasure μ] (hK : IsCompact K)
    (hKconv : Convex ℝ K) (hμ : μ Kᶜ = 0) : ∃! x, IsBarycenter μ x := by
  obtain ⟨x, -, hx⟩ := exists_isBarycenter_of_isCompact hK hKconv μ hμ
  exact ⟨x, hx, fun y hy => hy.unique hx⟩

end MemClosedConvexHull

/-!
### Every point of the closed convex hull is a barycentre
-/

section ClosedConvexHull

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] {C K : Set V} {x : V}

/-- **The representation theorem** (Phelps, §1): if `C` is a closed subset of a compact convex set
`K` in a topological vector space, then every point of the closed convex hull of `C` is the
barycentre of a probability measure carried by `C`.

The proof exhibits the set `B` of such barycentres as a closed convex set containing `C`. It is
the image under the (continuous) second projection of

`G = {(m, x) ∈ ProbabilityMeasure ↥C × ↥K | ∀ ℓ, ∫ ℓ dm = ℓ x}`,

a closed subset of a compact space: `↥C` is compact, hence so is `ProbabilityMeasure ↥C` in the
topology of weak convergence, and for each `ℓ` both sides of the defining equation are continuous
in `(m, x)` — the left-hand side because `ℓ` restricted to the compact set `C` is a *bounded*
continuous function. Dirac measures show `C ⊆ B`, and mixtures show that `B` is convex. -/
theorem exists_isBarycenter_of_mem_closedConvexHull (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hC : IsClosed C) (hCK : C ⊆ K) (hx : x ∈ closedConvexHull ℝ C) :
    ∃ μ : Measure V, IsProbabilityMeasure μ ∧ μ Cᶜ = 0 ∧ IsBarycenter μ x := by
  have hCcomp : IsCompact C := hK.of_isClosed_subset hC hCK
  have : CompactSpace C := isCompact_iff_compactSpace.mp hCcomp
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- the restriction of a functional to `C`, as a bounded continuous function
  set g : StrongDual ℝ V → (C →ᵇ ℝ) := fun ℓ =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun y => ℓ (y : V), ℓ.continuous.comp continuous_subtype_val⟩
  have hgint : ∀ (ℓ : StrongDual ℝ V) (ν : Measure C), ∀ [IsFiniteMeasure ν],
      Integrable (fun y : C => ℓ (y : V)) ν :=
    fun ℓ ν _ => BoundedContinuousFunction.integrable ν (g ℓ)
  -- the graph of the barycentre relation over `C`
  set G : Set (ProbabilityMeasure C × K) :=
    {p | ∀ ℓ : StrongDual ℝ V, ∫ y, ℓ (y : V) ∂(p.1 : Measure C) = ℓ (p.2 : V)} with hG
  have hGclosed : IsClosed G := by
    rw [hG, ofPred_forall]
    refine isClosed_iInter fun ℓ => isClosed_eq ?_ ?_
    · exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (g ℓ)).comp
        continuous_fst
    · exact ℓ.continuous.comp (continuous_subtype_val.comp continuous_snd)
  set B : Set V := (fun p : ProbabilityMeasure C × K => (p.2 : V)) '' G
  have hBcomp : IsCompact B :=
    hGclosed.isCompact.image (continuous_subtype_val.comp continuous_snd)
  -- `C ⊆ B`, via Dirac measures
  have hCB : C ⊆ B := by
    intro c hc
    refine ⟨(⟨Measure.dirac ⟨c, hc⟩, Measure.dirac.isProbabilityMeasure⟩, ⟨c, hCK hc⟩), ?_, rfl⟩
    intro ℓ
    exact integral_dirac' _ _ ((ℓ.continuous.comp continuous_subtype_val).stronglyMeasurable)
  -- `B` is convex, via mixtures
  have hBconv : Convex ℝ B := by
    rintro _ ⟨p₁, hp₁, rfl⟩ _ ⟨p₂, hp₂, rfl⟩ a b ha hb hab
    have hprob : IsProbabilityMeasure
        (ENNReal.ofReal a • (p₁.1 : Measure C) + ENNReal.ofReal b • (p₂.1 : Measure C)) := by
      constructor
      simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        measure_univ, mul_one]
      rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
    obtain ⟨ν, hν⟩ : ∃ ν : ProbabilityMeasure C, (ν : Measure C) =
        ENNReal.ofReal a • (p₁.1 : Measure C) + ENNReal.ofReal b • (p₂.1 : Measure C) :=
      ⟨⟨_, hprob⟩, rfl⟩
    refine ⟨(ν, ⟨a • (p₁.2 : V) + b • (p₂.2 : V), hKconv p₁.2.2 p₂.2.2 ha hb hab⟩), ?_, rfl⟩
    intro ℓ
    rw [show ((ν, ⟨a • (p₁.2 : V) + b • (p₂.2 : V),
        hKconv p₁.2.2 p₂.2.2 ha hb hab⟩) : ProbabilityMeasure C × K).1 = ν from rfl, hν,
      integral_add_measure ((hgint ℓ _).smul_measure (by simp))
        ((hgint ℓ _).smul_measure (by simp)),
      integral_smul_measure, integral_smul_measure, hp₁ ℓ, hp₂ ℓ, map_add, map_smul, map_smul,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
  -- hence `B` contains the closed convex hull of `C`
  obtain ⟨p, hp, hpx⟩ := closedConvexHull_min hCB hBconv hBcomp.isClosed hx
  refine ⟨(p.1 : Measure C).map Subtype.val,
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hC.measurableSet.compl]
    simp [preimage_compl]
  · refine isBarycenter_map measurable_subtype_coe.aemeasurable fun ℓ => ?_
    rw [hp ℓ]
    exact congrArg ℓ hpx

/-- **The representation theorem, as a characterisation**: for a closed subset `C` of a compact
convex set `K`, the closed convex hull of `C` is exactly the set of barycentres of the probability
measures carried by `C`.
This is the form Choquet theory uses: it turns a point of `closedConvexHull ℝ C` into an integral
representation over `C`. -/
theorem mem_closedConvexHull_iff_exists_isBarycenter [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [LocallyConvexSpace ℝ V] (hK : IsCompact K) (hKconv : Convex ℝ K) (hC : IsClosed C)
    (hCK : C ⊆ K) :
    x ∈ closedConvexHull ℝ C ↔
      ∃ μ : Measure V, IsProbabilityMeasure μ ∧ μ Cᶜ = 0 ∧ IsBarycenter μ x := by
  refine ⟨exists_isBarycenter_of_mem_closedConvexHull hK hKconv hC hCK, ?_⟩
  rintro ⟨μ, hμ, hμC, hx⟩
  exact hx.mem_closedConvexHull (hK.of_isClosed_subset hC hCK) hμC

end ClosedConvexHull

end MeasureTheory
