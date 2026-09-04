/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Comparing a continuous real function with an `EReal`-valued semicontinuous one

`{x | f x ≤ g x}` is closed when `f` is a continuous real function and `g` is an
`EReal`-valued upper semicontinuous one: the complement is the union over the rationals `q` of
the open sets `{g < q} ∩ {q < f}`, by the density of the rationals in `EReal`.

Intended home: `Mathlib/Topology/Semicontinuity/Basic.lean`.
-/

@[expose] public section

open Set Topology

namespace UpperSemicontinuous

variable {X : Type*} [TopologicalSpace X]

/-- If `f : X → ℝ` is continuous and `g : X → EReal` is upper semicontinuous, then
`{x | f x ≤ g x}` is closed. -/
theorem isClosed_setOf_coe_le {f : X → ℝ} (hf : Continuous f) {g : X → EReal}
    (hg : UpperSemicontinuous g) : IsClosed {x | (f x : EReal) ≤ g x} := by
  rw [← isOpen_compl_iff]
  have hset : {x | (f x : EReal) ≤ g x}ᶜ
      = ⋃ q : ℚ, {x | g x < ((q : ℝ) : EReal)} ∩ {x | (q : ℝ) < f x} := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, not_le, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      obtain ⟨q, h1, h2⟩ := EReal.lt_iff_exists_rat_btwn.1 h
      exact ⟨q, h1, EReal.coe_lt_coe_iff.1 h2⟩
    · rintro ⟨q, h1, h2⟩
      exact h1.trans (EReal.coe_lt_coe_iff.2 h2)
  rw [hset]
  exact isOpen_iUnion fun q ↦ (hg.isOpen_preimage _).inter (isOpen_lt continuous_const hf)

end UpperSemicontinuous
