/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Cluster points in a product

A cluster point of a net of pairs projects to a cluster point in each factor
(`MapClusterPt.fst`, `MapClusterPt.snd`), and conversely a *convergent* first coordinate can be
paired with a cluster point of the second one (`Filter.Tendsto.mapClusterPt_prod`): an
eventually-true statement and a frequently-true statement hold frequently together.  In a
Hausdorff space a cluster point of a convergent net is its limit
(`MapClusterPt.eq_of_tendsto`).

These are the three facts behind the standard "pass to a subsequence in the compact factor"
argument for a product of two topologies of which only one is metrizable — for instance the
product of the Euclidean topology on a simplex with the topology of local convergence on random
fields, in Georgii's Proposition (19.13).
-/

@[expose] public section

open Filter Topology

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {F : Filter ι}
  {f : ι → X} {g : ι → Y} {x : X} {y : Y}

/-- The first coordinate of a cluster point of a net of pairs is a cluster point of the first
coordinates. -/
theorem MapClusterPt.fst {u : ι → X × Y} {p : X × Y} (h : MapClusterPt p F u) :
    MapClusterPt p.1 F fun i ↦ (u i).1 :=
  h.continuousAt_comp (f := Prod.fst) continuous_fst.continuousAt

/-- The second coordinate of a cluster point of a net of pairs is a cluster point of the second
coordinates. -/
theorem MapClusterPt.snd {u : ι → X × Y} {p : X × Y} (h : MapClusterPt p F u) :
    MapClusterPt p.2 F fun i ↦ (u i).2 :=
  h.continuousAt_comp (f := Prod.snd) continuous_snd.continuousAt

/-- **A cluster point of a convergent net is its limit**, in a Hausdorff space. -/
theorem MapClusterPt.eq_of_tendsto [T2Space X] {x' : X} (h : MapClusterPt x F f)
    (h' : Tendsto f F (𝓝 x')) : x = x' :=
  eq_of_nhds_neBot (h.clusterPt.mono h')

/-- **Pairing a limit with a cluster point.**  If `f` converges to `x` and `y` is a cluster point
of `g`, then `(x, y)` is a cluster point of the net of pairs: a neighbourhood basis of `(x, y)`
is made of products `U × V`, `f` is eventually in `U`, and `g` is frequently in `V`. -/
theorem Filter.Tendsto.mapClusterPt_prod (hf : Tendsto f F (𝓝 x)) (hg : MapClusterPt y F g) :
    MapClusterPt (x, y) F fun i ↦ (f i, g i) := by
  rw [mapClusterPt_iff_frequently]
  intro s hs
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hs
  have hfU : ∀ᶠ i in F, f i ∈ U := hf hU
  have hgV : ∃ᶠ i in F, g i ∈ V := mapClusterPt_iff_frequently.1 hg V hV
  exact (hgV.and_eventually hfU).mono fun i hi ↦ hUV ⟨hi.2, hi.1⟩

end
