/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Separation.GDelta

/-!
# σ-compact sets and `Gδ` sets in perfectly normal spaces

In a compact perfectly normal space (closed sets are `Gδ`; e.g. any compact metrizable space) an
open set is a countable union of closed, hence compact, sets: it is σ-compact
(`IsOpen.isSigmaCompact`). Dually, in a Hausdorff perfectly normal space the difference of a closed
set and a σ-compact set is a `Gδ` set (`IsClosed.isGδ_diff`).
-/

@[expose] public section

open Set

variable {X : Type*} [TopologicalSpace X] {s t : Set X}

/-- The intersection of a σ-compact set with a closed set is σ-compact. -/
lemma IsSigmaCompact.inter_right (hs : IsSigmaCompact s) (ht : IsClosed t) :
    IsSigmaCompact (s ∩ t) := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact ⟨fun n ↦ K n ∩ t, fun n ↦ (hK n).inter_right ht, by rw [← iUnion_inter]⟩

/-- The intersection of a closed set with a σ-compact set is σ-compact. -/
lemma IsSigmaCompact.inter_left (hs : IsSigmaCompact s) (ht : IsClosed t) :
    IsSigmaCompact (t ∩ s) :=
  inter_comm s t ▸ hs.inter_right ht

/-- In a compact perfectly normal space (e.g. a compact metrizable space), every open set is
σ-compact: its complement is a closed, hence `Gδ`, set, so the open set is a countable union of
closed, hence compact, sets. (For pseudo-emetric spaces the `Fσ` decomposition is Mathlib's
`IsOpen.exists_iUnion_isClosed`.) -/
lemma IsOpen.isSigmaCompact [CompactSpace X] [PerfectlyNormalSpace X] (hs : IsOpen s) :
    IsSigmaCompact s := by
  obtain ⟨U, hU, hsU⟩ := hs.isClosed_compl.isGδ.eq_iInter_nat
  refine ⟨fun n ↦ (U n)ᶜ, fun n ↦ (hU n).isClosed_compl.isCompact, ?_⟩
  rw [← compl_iInter, ← hsU, compl_compl]

/-- In a Hausdorff perfectly normal space (e.g. a metrizable space), the difference of a closed
set and a σ-compact set is a `Gδ` set. -/
lemma IsClosed.isGδ_diff [T2Space X] [PerfectlyNormalSpace X] (hs : IsClosed s)
    (ht : IsSigmaCompact t) : IsGδ (s \ t) := by
  obtain ⟨K, hK, rfl⟩ := ht
  rw [sdiff_iUnion]
  exact IsGδ.iInter fun n ↦ sdiff_eq s (K n) ▸ hs.isGδ.inter (hK n).isClosed.isOpen_compl.isGδ
