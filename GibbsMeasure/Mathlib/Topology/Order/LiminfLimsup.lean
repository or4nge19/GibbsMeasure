/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Order.Compact

/-!
# Ultrafilter limits and `limsup`

In a compact linearly ordered topological space, the limit along an ultrafilter is dominated by
the `limsup` along any coarser filter.
-/

@[expose] public section

open Filter Topology

/-- The ultrafilter limit of a function into a compact linear order is dominated by the `limsup`
along any coarser filter. -/
theorem Ultrafilter.lim_le_limsup {α ι : Type*} [CompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [T2Space α] {U : Ultrafilter ι} {l : Filter ι} (hU : ↑U ≤ l) (f : ι → α) :
    (U.map f).lim ≤ limsup f l := by
  have h : Tendsto f (↑U) (𝓝 (U.map f).lim) := (U.map f).le_nhds_lim
  rw [← h.limsup_eq]
  exact limsup_le_limsup_of_le hU

/-- The `liminf` along a coarser filter is dominated by the ultrafilter limit. -/
theorem Ultrafilter.liminf_le_lim {α ι : Type*} [CompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [T2Space α] {U : Ultrafilter ι} {l : Filter ι} (hU : ↑U ≤ l) (f : ι → α) :
    liminf f l ≤ (U.map f).lim := by
  have h : Tendsto f (↑U) (𝓝 (U.map f).lim) := (U.map f).le_nhds_lim
  rw [← h.liminf_eq]
  exact liminf_le_liminf_of_le hU
