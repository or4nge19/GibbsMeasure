/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Logic.Function.DependsOn
public import Mathlib.Topology.EMetricSpace.Defs

/-!
# Oscillation of a function on a product outside a set of coordinates

`oscOutside s f` is the supremum of `edist (f ζ) (f η)` over pairs `ζ, η` agreeing on `s`. It
vanishes whenever `f` depends only on `s`, and conversely when the target is an `EMetricSpace`
(`oscOutside_eq_zero_iff_dependsOn`).
-/

@[expose] public section

open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} {F : Type*} [PseudoEMetricSpace F]
  {s t : Set ι} {f : (∀ i, X i) → F}

/-- The oscillation of `f` under variation of the coordinates outside `s`. -/
noncomputable def oscOutside (s : Set ι) (f : (∀ i, X i) → F) : ℝ≥0∞ :=
  ⨆ ζ, ⨆ η, ⨆ _ : ∀ i ∈ s, ζ i = η i, edist (f ζ) (f η)

lemma le_oscOutside {ζ η : ∀ i, X i} (h : ∀ i ∈ s, ζ i = η i) :
    edist (f ζ) (f η) ≤ oscOutside s f :=
  le_iSup_of_le ζ (le_iSup_of_le η (le_iSup_of_le h le_rfl))

lemma oscOutside_le {c : ℝ≥0∞} (h : ∀ ζ η : ∀ i, X i, (∀ i ∈ s, ζ i = η i) → edist (f ζ) (f η) ≤
    c) :
    oscOutside s f ≤ c :=
  iSup_le fun ζ ↦ iSup_le fun η ↦ iSup_le fun hζη ↦ h ζ η hζη

lemma oscOutside_antitone (h : s ⊆ t) : oscOutside t f ≤ oscOutside s f :=
  oscOutside_le fun _ _ hζη ↦ le_oscOutside fun i hi ↦ hζη i (h hi)

lemma DependsOn.oscOutside_eq_zero (hf : DependsOn f s) : oscOutside s f = 0 :=
  le_antisymm (oscOutside_le fun _ _ hζη ↦ by simp [hf hζη]) bot_le

lemma oscOutside_eq_zero_iff_dependsOn {F : Type*} [EMetricSpace F] {f : (∀ i, X i) → F} :
    oscOutside s f = 0 ↔ DependsOn f s :=
  ⟨fun h _ _ hxy ↦ edist_eq_zero.1 (le_antisymm (h ▸ le_oscOutside hxy) bot_le),
    DependsOn.oscOutside_eq_zero⟩

