/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Finset
public import GibbsMeasure.Mathlib.Data.Finset.Map

/-!
# Summation over finite subsets, ordered by ambient volume

For a family indexed by `Finset ι`, `SummationFilter.volume ι` sums along the net of partial sums
over `{A | A ⊆ Δ}`, `Δ : Finset ι` ranging over `atTop`.

This is the summation convention of Georgii, *Gibbs Measures and Phase Transitions*, (2.1). It is
coarser than unconditional summation, so `Summable f` implies `Summable f (SummationFilter.volume
    ι)`
with the same sum.
-/

@[expose] public section

open Filter

namespace SummationFilter

variable (ι : Type*)

/-- Summation along the net of partial sums over the subsets of a finite volume. -/
def volume : SummationFilter (Finset ι) := ⟨Filter.map Finset.powerset atTop⟩

variable {ι}

lemma volume_filter : (volume ι).filter = Filter.map Finset.powerset atTop := rfl

instance : (volume ι).LeAtTop := ⟨Filter.tendsto_finset_powerset_atTop_atTop⟩

instance : (volume ι).NeBot := ⟨Filter.map_neBot⟩

instance _root_.Filter.isCountablyGenerated_atTop_finset [Countable ι] :
    (atTop : Filter (Finset ι)).IsCountablyGenerated := by
  rw [Filter.atTop_finset_eq_iInf]; infer_instance

instance [Countable ι] : (volume ι).filter.IsCountablyGenerated := by
  rw [volume_filter]; infer_instance

lemma tendsto_volume_filter {α : Type*} [TopologicalSpace α] {f : Finset (Finset ι) → α} {a : α}
    (h : Tendsto (fun Δ : Finset ι ↦ f Δ.powerset) atTop (nhds a)) :
    Tendsto f (volume ι).filter (nhds a) := h

end SummationFilter

namespace HasSum

variable {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : Finset ι → α} {a : α}

/-- Unconditional summability implies summability along `SummationFilter.volume`, with the same sum.
This is the step from unconditional convergence to convergence of the net of Georgii's Convention
(2.1); it is what makes an absolutely summable potential (2.11) satisfy (2.2)(ii). -/
lemma volume (h : HasSum f a) : HasSum f a (SummationFilter.volume ι) :=
  h.mono_left (SummationFilter.le_atTop (L := SummationFilter.volume ι))

end HasSum

namespace Summable

variable {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : Finset ι → α}

lemma volume (h : Summable f) : Summable f (SummationFilter.volume ι) :=
  h.mono_filter (SummationFilter.le_atTop (L := SummationFilter.volume ι))

end Summable

/-! ### Reindexing along a bijection of the index set

Summation along `SummationFilter.volume` is invariant under a bijection `σ : ι ≃ κ` of the index
set: `∑'[volume ι] A, f (A.map σ) = ∑'[volume κ] B, f B`. -/

namespace SummationFilter

variable {ι κ α : Type*} [AddCommMonoid α] (σ : ι ≃ κ) (f : Finset κ → α)

/-- Reindexing the powerset of `Δ` along `σ` gives the powerset of `σ '' Δ`. -/
lemma sum_powerset_map_equiv (Δ : Finset ι) :
    ∑ A ∈ Δ.powerset, f (A.map σ.toEmbedding) = ∑ B ∈ (Δ.map σ.toEmbedding).powerset, f B := by
  have h : Δ.powerset.map (Finset.mapEmbedding σ.toEmbedding).toEmbedding
      = (Δ.map σ.toEmbedding).powerset := by
    ext B
    simp only [Finset.mem_map, Finset.mem_powerset, RelEmbedding.coe_toEmbedding,
      Finset.mapEmbedding_apply]
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact Finset.map_subset_map.2 hA
    · intro hB
      refine ⟨B.map σ.symm.toEmbedding, ?_, Finset.map_map_symm σ B⟩
      rw [← Finset.map_subset_map (f := σ.toEmbedding), Finset.map_map_symm]
      exact hB
  rw [← h, Finset.sum_map]
  rfl

variable [TopologicalSpace α]

/-- Summation along `SummationFilter.volume` is invariant under a bijection of the index set. -/
lemma hasSum_volume_map_equiv_iff (a : α) :
    HasSum (fun A ↦ f (A.map σ.toEmbedding)) a (volume ι) ↔ HasSum f a (volume κ) := by
  simp only [HasSum, volume_filter, Filter.tendsto_map'_iff, Function.comp_def,
    sum_powerset_map_equiv σ f]
  conv_rhs => rw [← σ.finsetOrderIso.map_atTop, Filter.tendsto_map'_iff]
  exact Iff.rfl

lemma summable_volume_map_equiv_iff :
    Summable (fun A ↦ f (A.map σ.toEmbedding)) (volume ι) ↔ Summable f (volume κ) :=
  exists_congr fun a ↦ hasSum_volume_map_equiv_iff σ f a

lemma tsum_volume_map_equiv [T2Space α] :
    ∑'[volume ι] A, f (A.map σ.toEmbedding) = ∑'[volume κ] B, f B := by
  by_cases h : Summable f (volume κ)
  · exact ((hasSum_volume_map_equiv_iff σ f _).2 h.hasSum).tsum_eq
  · rw [tsum_eq_zero_of_not_summable h,
      tsum_eq_zero_of_not_summable (mt (summable_volume_map_equiv_iff σ f).1 h)]

end SummationFilter
