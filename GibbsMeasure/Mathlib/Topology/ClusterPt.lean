/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.ClusterPt

/-!
# Cluster points as limits along a finer filter

A cluster point of `u` along `F` is a genuine limit of `u` along a finer filter. This is the
non-metrizable substitute for "pass to a convergent subsequence": in a compact space that is not
first countable one still gets `∃ l ≤ F, l.NeBot ∧ Tendsto u l (𝓝 x)`, which is all that the usual
subsequence arguments use.
-/

@[expose] public section

open Filter Topology

variable {α X : Type*} [TopologicalSpace X] {u : α → X} {F : Filter α} {x : X}

/-- **A cluster point is a limit along a finer filter.** The witness is `F ⊓ comap u (𝓝 x)`. -/
theorem MapClusterPt.exists_le_tendsto (h : MapClusterPt x F u) :
    ∃ l : Filter α, l ≤ F ∧ l.NeBot ∧ Tendsto u l (𝓝 x) := by
  refine ⟨F ⊓ comap u (𝓝 x), inf_le_left, ?_, ?_⟩
  · rw [Filter.neBot_inf_comap_iff_map, inf_comm]
    exact h.clusterPt.neBot
  · exact (map_mono inf_le_right).trans map_comap_le

/-- **A cluster point of a filter is a limit along a finer filter.** -/
theorem ClusterPt.exists_le_tendsto {G : Filter X} (h : ClusterPt x G) :
    ∃ l : Filter X, l ≤ G ∧ l.NeBot ∧ Tendsto id l (𝓝 x) :=
  MapClusterPt.exists_le_tendsto (u := id) (by rwa [MapClusterPt, map_id])

end
