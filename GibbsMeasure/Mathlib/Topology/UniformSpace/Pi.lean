/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.UniformSpace.Pi

/-!
# Entourages of a product uniformity are finitely supported

Every entourage of `∀ i, α i` contains the set of pairs agreeing on some finite set of coordinates.
Consequently a uniformly continuous map out of a product depends, up to any prescribed entourage of
the target, on only finitely many coordinates.
-/

@[expose] public section

open Filter Set
open scoped Uniformity

variable {ι : Type*} {α : ι → Type*} [∀ i, UniformSpace (α i)]

/-- The pairs agreeing on `Λ`. -/
def Set.agreeOn (Λ : Set ι) (α : ι → Type*) : Set ((∀ i, α i) × (∀ i, α i)) :=
  {p | ∀ i ∈ Λ, p.1 i = p.2 i}

lemma Set.agreeOn_subset_comap {Λ : Set ι} {i : ι} (hi : i ∈ Λ) {V : Set (α i × α i)}
    (hV : V ∈ 𝓤 (α i)) :
    Set.agreeOn Λ α ⊆ (fun p : (∀ i, α i) × (∀ i, α i) ↦ (p.1 i, p.2 i)) ⁻¹' V :=
  fun p hp ↦ by simpa [hp i hi] using refl_mem_uniformity hV

/-- Every entourage of a product uniformity contains the pairs agreeing on some finite set of
coordinates. -/
theorem exists_finset_agreeOn_subset_of_mem_uniformity
    {W : Set ((∀ i, α i) × (∀ i, α i))} (hW : W ∈ 𝓤 (∀ i, α i)) :
    ∃ Λ : Finset ι, Set.agreeOn (Λ : Set ι) α ⊆ W := by
  classical
  rw [Pi.uniformity, Filter.mem_iInf] at hW
  obtain ⟨I, hIfin, V, hV, rfl⟩ := hW
  refine ⟨hIfin.toFinset, subset_iInter fun i ↦ ?_⟩
  obtain ⟨U, hU, hUV⟩ := hV i
  exact (Set.agreeOn_subset_comap (by simpa using i.2) hU).trans hUV

/-- A uniformly continuous map out of a product depends, up to a prescribed entourage of the target,
on only finitely many coordinates. -/
theorem UniformContinuous.exists_finset_forall_mem {β : Type*} [UniformSpace β]
    {f : (∀ i, α i) → β} (hf : UniformContinuous f) {V : Set (β × β)} (hV : V ∈ 𝓤 β) :
    ∃ Λ : Finset ι, ∀ x y : ∀ i, α i, (∀ i ∈ Λ, x i = y i) → (f x, f y) ∈ V := by
  obtain ⟨Λ, hΛ⟩ := exists_finset_agreeOn_subset_of_mem_uniformity (hf hV)
  refine ⟨Λ, fun x y hxy ↦ ?_⟩
  exact hΛ (a := (x, y)) fun i hi ↦ hxy i (by simpa using hi)
