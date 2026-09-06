/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The closed convex hull in a product of lines

In `ι → ℝ` with the product topology — a locally convex space which is neither normed nor
metrizable when `ι` is uncountable — membership of the closed convex hull of a set `X` is a
*finite-dimensional* condition: `v ∈ cx̄ X` as soon as every finite restriction `v|_s` lies in the
closed convex hull of `X|_s` in `↥s → ℝ`.

The application is Jensen's inequality for a set-valued constraint: the coordinatewise integral of
a family of points of `X` lies in `cx̄ X`, with no integrability assumption beyond the coordinates
(`integral_mem_closedConvexHull_pi`). Over a finite-dimensional target this is
`MeasureTheory.Convex.integral_mem`; the content here is the passage to an arbitrary index set.

## Main statements

* `mem_closedConvexHull_pi_of_forall_finset`: the finite-dimensional criterion.
* `integral_mem_closedConvexHull_pi`: the coordinatewise barycentre of a probability measure
  carried by `X` lies in `cx̄ X`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

variable {ι : Type*} {X : Set (ι → ℝ)} {v : ι → ℝ}

/-- **Membership of the closed convex hull in `ι → ℝ` is a finite-dimensional condition.** If every
finite restriction of `v` lies in the closed convex hull of the corresponding restriction of `X`,
then `v` lies in the closed convex hull of `X`.

The converse holds too, by continuity and linearity of the restriction, but is not needed. -/
theorem mem_closedConvexHull_pi_of_forall_finset
    (h : ∀ s : Finset ι, s.restrict v ∈ closedConvexHull ℝ ((s.restrict : (ι → ℝ) → s → ℝ) '' X)) :
    v ∈ closedConvexHull ℝ X := by
  classical
  rw [closedConvexHull_eq_closure_convexHull, mem_closure_iff_nhds]
  intro t ht
  -- a basic neighbourhood of `v`: finitely many coordinates
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hIfin, V, hV, hVt⟩ := ht
  set s : Finset ι := hIfin.toFinset with hs
  -- the restriction of the convex hull is the convex hull of the restriction
  have hlin : IsLinearMap ℝ (s.restrict : (ι → ℝ) → s → ℝ) :=
    ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have himg : (s.restrict : (ι → ℝ) → s → ℝ) '' convexHull ℝ X
      = convexHull ℝ ((s.restrict : (ι → ℝ) → s → ℝ) '' X) := hlin.image_convexHull _
  -- the corresponding neighbourhood of `v|ₛ` in the finite product
  have hW : (Set.univ.pi fun i : s ↦ V i) ∈ 𝓝 (s.restrict v) :=
    set_pi_mem_nhds Set.finite_univ fun i _ ↦ hV i
  have hmem := h s
  rw [closedConvexHull_eq_closure_convexHull, mem_closure_iff_nhds] at hmem
  obtain ⟨y, hyW, hyhull⟩ := hmem _ hW
  rw [← himg] at hyhull
  obtain ⟨w, hwhull, rfl⟩ := hyhull
  refine ⟨w, hVt ?_, hwhull⟩
  intro i hi
  have : (⟨i, hIfin.mem_toFinset.2 hi⟩ : s) ∈ (Set.univ : Set s) := Set.mem_univ _
  exact hyW _ this

/-- **Jensen's inequality for a set constraint, coordinatewise.** If `f a ∈ X` for almost every `a`
and each coordinate `a ↦ f a i` is integrable, then the coordinatewise barycentre
`i ↦ ∫ f a i ∂κ` lies in the closed convex hull of `X`. -/
theorem integral_mem_closedConvexHull_pi {α : Type*} [MeasurableSpace α] {κ : Measure α}
    [IsProbabilityMeasure κ] {f : α → ι → ℝ} (hmem : ∀ᵐ a ∂κ, f a ∈ X)
    (hint : ∀ i, Integrable (fun a ↦ f a i) κ) :
    (fun i ↦ ∫ a, f a i ∂κ) ∈ closedConvexHull ℝ X := by
  refine mem_closedConvexHull_pi_of_forall_finset fun s ↦ ?_
  have hintr : ∀ i : s, Integrable (fun a ↦ s.restrict (f a) i) κ := fun i ↦ hint (i : ι)
  have hIr : Integrable (fun a ↦ s.restrict (f a)) κ := Integrable.of_eval hintr
  have hval : s.restrict (fun i ↦ ∫ a, f a i ∂κ) = ∫ a, s.restrict (f a) ∂κ := by
    funext i
    rw [MeasureTheory.eval_integral hintr i]
    rfl
  rw [hval]
  refine Convex.integral_mem convex_closedConvexHull isClosed_closedConvexHull ?_ hIr
  filter_upwards [hmem] with a ha
  exact subset_closedConvexHull (𝕜 := ℝ) ⟨f a, ha, rfl⟩

end
