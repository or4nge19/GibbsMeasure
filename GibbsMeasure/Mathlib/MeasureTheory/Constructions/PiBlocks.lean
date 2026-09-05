/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Reindexing a finite product of copies of a probability measure

Let `ν` be a probability measure on `E` and let `κ` be a finite index type.  Mathlib knows how
`Measure.pi` transforms under a *bijection* of the index type
(`MeasureTheory.measurePreserving_piCongrLeft`) but not under a mere injection, and it has no
statement that disjoint blocks of coordinates are independent.  Both are recorded here.

## Main results

* `MeasureTheory.map_comp_pi_of_injective`: precomposition with an injection `g : ι → κ` maps
  `ν^κ` to `ν^ι`.  Finiteness of the index sets is not enough: the discarded coordinates must
  carry total mass one, so `ν` really has to be a probability measure.
* `MeasureTheory.map_curry_pi`: currying identifies `ν^{J × ι}` with `(ν^ι)^J`.
* `MeasureTheory.measurePreserving_blocks`: if `g : J → ι → κ` describes `J` pairwise disjoint
  blocks of coordinates, each indexed by `ι` — that is, if `(j, i) ↦ g j i` is injective — then
  reading `ν^κ` block by block produces independent copies of `ν^ι`.
* `MeasureTheory.pi_setOf_forall_comp_mem`: the resulting product formula
  `ν^κ {ω | ∀ j, ω ∘ g j ∈ B j} = ∏ j, ν^ι (B j)`.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {E ι κ J : Type*} [MeasurableSpace E] [Fintype ι] [Fintype κ] [Fintype J]

omit [Fintype ι] [Fintype κ] in
lemma measurable_comp_right (g : ι → κ) : Measurable fun ω : κ → E ↦ ω ∘ g :=
  measurable_pi_lambda _ fun i ↦ measurable_pi_apply (g i)

section Injective

variable (ν : Measure E) [IsProbabilityMeasure ν] {g : ι → κ}

/-- **Restricting a product of copies of a probability measure along an injection.**  If
`g : ι → κ` is injective then the law of `ω ∘ g` under `ν^κ` is `ν^ι`: the coordinates outside
the range of `g` are integrated out, and each contributes the total mass `1`. -/
theorem map_comp_pi_of_injective (hg : Function.Injective g) :
    (Measure.pi fun _ : κ ↦ ν).map (fun ω ↦ ω ∘ g) = Measure.pi fun _ : ι ↦ ν := by
  classical
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  -- the box `∏ᵢ s i` pulls back to the box which is `s i` at `g i` and `univ` elsewhere
  set t : κ → Set E := Function.extend g s fun _ ↦ univ with htdef
  have htg : ∀ i, t (g i) = s i := fun i ↦ hg.extend_apply s _ i
  have htout : ∀ k, (¬ ∃ i, g i = k) → t k = univ := fun k hk ↦ Function.extend_apply' s _ k hk
  have htmem : ∀ k, MeasurableSet (t k) := by
    intro k
    by_cases hk : ∃ i, g i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [htg i]
      exact hs i
    · rw [htout k hk]
      exact MeasurableSet.univ
  have hpre : (fun ω : κ → E ↦ ω ∘ g) ⁻¹' (univ.pi s) = univ.pi t := by
    ext ω
    simp only [mem_preimage, mem_univ_pi, Function.comp_apply]
    refine ⟨fun h k ↦ ?_, fun h i ↦ ?_⟩
    · by_cases hk : ∃ i, g i = k
      · obtain ⟨i, rfl⟩ := hk
        rw [htg i]
        exact h i
      · rw [htout k hk]
        exact mem_univ _
    · rw [← htg i]; exact h _
  rw [Measure.map_apply (measurable_comp_right g) (MeasurableSet.univ_pi hs), hpre,
    Measure.pi_pi]
  -- only the coordinates in the range of `g` contribute
  have hsub : ∀ k ∈ (Finset.univ : Finset κ), k ∉ Finset.univ.image g → ν (t k) = 1 := by
    intro k _ hk
    have hk' : ¬ ∃ i, g i = k := fun ⟨i, hi⟩ ↦ hk (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩)
    rw [htout k hk', measure_univ]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image g)) hsub,
    Finset.prod_image (fun x _ y _ h ↦ hg h)]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [htg i]

/-- The measure-preserving form of `MeasureTheory.map_comp_pi_of_injective`. -/
theorem measurePreserving_comp_pi_of_injective (hg : Function.Injective g) :
    MeasurePreserving (fun ω : κ → E ↦ ω ∘ g) (Measure.pi fun _ : κ ↦ ν)
      (Measure.pi fun _ : ι ↦ ν) :=
  ⟨measurable_comp_right g, map_comp_pi_of_injective ν hg⟩

end Injective

section Curry

/-- **Currying a product of copies of a probability measure over a product index type.**  Under
`ν^{J × ι}` the `J` "rows" `i ↦ x (j, i)` are independent with law `ν^ι`. -/
theorem map_curry_pi (J ι : Type*) [Fintype J] [Fintype ι] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : J × ι ↦ ν).map (fun x j i ↦ x (j, i))
      = Measure.pi fun _ : J ↦ Measure.pi fun _ : ι ↦ ν := by
  classical
  have hmeas : Measurable fun x : J × ι → E ↦ fun j i ↦ x (j, i) :=
    measurable_pi_lambda _ fun j ↦ measurable_pi_lambda _ fun i ↦ measurable_pi_apply (j, i)
  -- the boxes of `(ι → E)` form a π-system generating its σ-algebra, and `ν^ι` is spanned by
  -- the constant sequence `univ`
  set C : Set (Set (ι → E)) :=
    Set.pi univ '' Set.pi univ fun _ : ι ↦ {s : Set E | MeasurableSet s} with hC
  have huniv : (univ : Set (ι → E)) ∈ C :=
    ⟨fun _ ↦ univ, fun i _ ↦ MeasurableSet.univ, Set.pi_univ _⟩
  have hspan : (Measure.pi fun _ : ι ↦ ν).FiniteSpanningSetsIn C :=
    { set := fun _ ↦ univ
      set_mem := fun _ ↦ huniv
      finite := fun _ ↦ measure_lt_top _ _
      spanning := Set.iUnion_const _ }
  refine (Measure.pi_eq_generateFrom (C := fun _ : J ↦ C) (fun _ ↦ _root_.generateFrom_pi)
    (fun _ ↦ _root_.isPiSystem_pi) (fun _ ↦ hspan) fun S hS ↦ ?_).symm
  choose B hB hSB using hS
  have hBmeas : ∀ j i, MeasurableSet (B j i) := fun j i ↦ hB j i (mem_univ i)
  have hpre : (fun x : J × ι → E ↦ fun j i ↦ x (j, i)) ⁻¹' (univ.pi S)
      = univ.pi fun p : J × ι ↦ B p.1 p.2 := by
    ext x
    simp only [mem_preimage, mem_univ_pi, Prod.forall]
    constructor
    · intro h j i
      have hj := h j
      rw [← hSB j, mem_univ_pi] at hj
      exact hj i
    · intro h j
      rw [← hSB j, mem_univ_pi]
      exact fun i ↦ h j i
  rw [Measure.map_apply hmeas
      (MeasurableSet.univ_pi fun j ↦ hSB j ▸ MeasurableSet.univ_pi (hBmeas j)),
    hpre, Measure.pi_pi, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun j _ ↦ by rw [← hSB j, Measure.pi_pi]

end Curry

section Blocks

variable (ν : Measure E) [IsProbabilityMeasure ν] {g : J → ι → κ}

/-- **Disjoint blocks of coordinates are independent.**  If `g : J → ι → κ` picks out `J`
pairwise disjoint blocks of coordinates of `κ`, each indexed by `ι` — equivalently, if
`(j, i) ↦ g j i` is injective — then reading a `ν^κ`-distributed configuration block by block
gives `J` independent copies of a `ν^ι`-distributed configuration. -/
theorem measurePreserving_blocks (hg : Function.Injective fun p : J × ι ↦ g p.1 p.2) :
    MeasurePreserving (fun (ω : κ → E) (j : J) (i : ι) ↦ ω (g j i))
      (Measure.pi fun _ : κ ↦ ν) (Measure.pi fun _ : J ↦ Measure.pi fun _ : ι ↦ ν) := by
  have h₁ := measurePreserving_comp_pi_of_injective (κ := κ) (ι := J × ι) ν hg
  have h₂ : MeasurePreserving (fun x : J × ι → E ↦ fun j i ↦ x (j, i))
      (Measure.pi fun _ : J × ι ↦ ν) (Measure.pi fun _ : J ↦ Measure.pi fun _ : ι ↦ ν) :=
    ⟨measurable_pi_lambda _ fun j ↦ measurable_pi_lambda _ fun i ↦ measurable_pi_apply (j, i),
      map_curry_pi J ι ν⟩
  exact h₂.comp h₁

/-- The measure of the event that each of `J` disjoint blocks of coordinates falls in a
prescribed set is the product of the probabilities of those sets. -/
theorem pi_setOf_forall_comp_mem (hg : Function.Injective fun p : J × ι ↦ g p.1 p.2)
    {B : J → Set (ι → E)} (hB : ∀ j, MeasurableSet (B j)) :
    (Measure.pi fun _ : κ ↦ ν) {ω | ∀ j, (fun i ↦ ω (g j i)) ∈ B j}
      = ∏ j, (Measure.pi fun _ : ι ↦ ν) (B j) := by
  have h := (measurePreserving_blocks ν hg).measure_preimage
    (MeasurableSet.univ_pi hB).nullMeasurableSet
  have hset : (fun (ω : κ → E) (j : J) (i : ι) ↦ ω (g j i)) ⁻¹' (univ.pi B)
      = {ω : κ → E | ∀ j, (fun i ↦ ω (g j i)) ∈ B j} := by
    ext ω; simp
  rw [hset] at h
  rw [h, Measure.pi_pi]

end Blocks

end MeasureTheory
