/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.FreeBoundary
public import GibbsMeasure.Potential.Transformation
public import GibbsMeasure.Topology.Subsequence

/-!
# Periodic boundary conditions

Georgii Example (4.20)(2): the `Δ`-periodic modification `Φ̃^Δ` of a shift-invariant potential,
and the fact that every cluster point of the finite-volume Gibbs distributions with periodic
boundary condition is a Gibbs measure for `Φ`.
-/

@[expose] public section

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure Set Topology
open scoped ENNReal Topology

noncomputable section

namespace Potential

/-! ### Translations of finite volumes -/

section Translate

variable {S : Type*} [AddCommGroup S] {B : Finset S} {g h : S}

/-- The translate `A + g` of a finite set of sites. -/
def translate (B : Finset S) (g : S) : Finset S := B.map ⟨(· + g), add_left_injective g⟩

@[simp] lemma mem_translate {x : S} : x ∈ translate B g ↔ x - g ∈ B := by
  simp only [translate, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨x - g, hx, by abel⟩

lemma mem_translate_of_mem {x : S} (hx : x ∈ B) : x + g ∈ translate B g := by
  simp [mem_translate, hx]

@[simp] lemma translate_zero (B : Finset S) : translate B 0 = B := by
  ext x; simp

lemma translate_translate (B : Finset S) (g h : S) :
    translate (translate B g) h = translate B (g + h) := by
  ext x; simp [mem_translate, sub_sub, add_comm]

@[simp] lemma translate_nonempty : (translate B g).Nonempty ↔ B.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x - g, mem_translate.1 hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x + g, mem_translate_of_mem hx⟩

lemma translate_subset_iff {Δ : Finset S} : translate B g ⊆ Δ ↔ ∀ x ∈ B, x + g ∈ Δ := by
  constructor
  · intro h x hx; exact h (mem_translate_of_mem hx)
  · intro h x hx
    have := h _ (mem_translate.1 hx)
    simpa using this

end Translate

/-! ### Georgii (4.20)(2): the torus `S / p·S` -/

section Torus

variable {S : Type*} [AddCommGroup S]

/-- **Georgii (4.20)(2).** `π` reduces `S` modulo the period subgroup `G` onto the finite
fundamental domain `Δ`, Georgii's identification of the box `Δ` with the torus `S / p·S`. -/
structure IsTorusReduction (G : AddSubgroup S) (Δ : Finset S) (π : S → S) : Prop where
  /-- `π` takes values in the box `Δ`. -/
  mapsTo : ∀ i, π i ∈ Δ
  /-- `π` is the identity on the box `Δ`. -/
  eq_self : ∀ i ∈ Δ, π i = i
  /-- `π i` is congruent to `i` modulo the periods. -/
  sub_mem : ∀ i, i - π i ∈ G
  /-- Congruent sites have the same reduction. -/
  reduce_eq : ∀ i j, i - j ∈ G → π i = π j

namespace IsTorusReduction

variable {G : AddSubgroup S} {Δ : Finset S} {π : S → S} (hπ : IsTorusReduction G Δ π)
include hπ

lemma idem (i : S) : π (π i) = π i := hπ.eq_self _ (hπ.mapsTo i)

lemma add_mem (i : S) {g : S} (hg : g ∈ G) : π (i + g) = π i :=
  hπ.reduce_eq _ _ (by simpa using G.neg_mem hg)

lemma sub_mem' (i : S) : π i - i ∈ G := by
  simpa using G.neg_mem (hπ.sub_mem i)

/-- `Δ` is a fundamental domain: a site of `Δ` congruent to `i` is `π i`. -/
lemma eq_of_mem_of_sub_mem {i j : S} (hj : j ∈ Δ) (h : i - j ∈ G) : π i = j := by
  rw [hπ.reduce_eq i j h, hπ.eq_self j hj]

end IsTorusReduction

end Torus

/-! ### The periodic continuation `σ̃_Δ` and the projection `A ↦ A*` -/

section PeriodicExtend

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [DecidableEq S]
  {G : AddSubgroup S} {Δ : Finset S} {π : S → S} {A B : Finset S} {g i : S} {η ζ : S → E}

/-- **Georgii (4.20)(2).** The periodic continuation `σ̃_Δ(ω) = (ω_{j(i)})_{i ∈ S}`, where `j(i)`
is the representative `π i ∈ Δ` of `i`. -/
def periodicExtend (π : S → S) (η : S → E) : S → E := fun i ↦ η (π i)

/-- **Georgii (4.20)(2).** `A* = {i ∈ Δ : i ≡ j for some j ∈ A}`. -/
def starImage (π : S → S) (A : Finset S) : Finset S := A.image π

omit [AddCommGroup S] in
@[simp] lemma mem_starImage {x : S} : x ∈ starImage π A ↔ ∃ a ∈ A, π a = x := Finset.mem_image

lemma starImage_subset (hπ : IsTorusReduction G Δ π) (A : Finset S) : starImage π A ⊆ Δ := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := mem_starImage.1 hx
  exact hπ.mapsTo a

lemma starImage_eq_self (hπ : IsTorusReduction G Δ π) (hA : A ⊆ Δ) : starImage π A = A := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ mem_starImage.2 ⟨x, hx, hπ.eq_self x (hA hx)⟩⟩
  obtain ⟨a, ha, rfl⟩ := mem_starImage.1 hx
  rw [hπ.eq_self a (hA ha)]; exact ha

omit [AddCommGroup S] in
@[simp] lemma starImage_nonempty : (starImage π A).Nonempty ↔ A.Nonempty := by
  simp [starImage, Finset.image_nonempty]

lemma starImage_translate (hπ : IsTorusReduction G Δ π) (hg : g ∈ G) (A : Finset S) :
    starImage π (translate A g) = starImage π A := by
  ext x
  constructor
  · rintro hx
    obtain ⟨a, ha, rfl⟩ := mem_starImage.1 hx
    exact mem_starImage.2 ⟨a - g, mem_translate.1 ha, by
      simpa using (hπ.add_mem (a - g) hg).symm⟩
  · rintro hx
    obtain ⟨a, ha, rfl⟩ := mem_starImage.1 hx
    exact mem_starImage.2 ⟨a + g, mem_translate_of_mem ha, hπ.add_mem a hg⟩

omit [MeasurableSpace E] [AddCommGroup S] [DecidableEq S] in
@[simp] lemma periodicExtend_apply (π : S → S) (η : S → E) (i : S) :
    periodicExtend π η i = η (π i) := rfl

omit [MeasurableSpace E] [DecidableEq S] in
lemma periodicExtend_of_mem (hπ : IsTorusReduction G Δ π) (hi : i ∈ Δ) (η : S → E) :
    periodicExtend π η i = η i := by rw [periodicExtend_apply, hπ.eq_self i hi]

variable {Φ : Potential S E}

omit [DecidableEq S] in
/-- Interactions inside the box are unaffected by the periodic continuation. -/
lemma apply_periodicExtend_of_subset [IsPotential Φ] (hπ : IsTorusReduction G Δ π)
    (hA : A ⊆ Δ) (η : S → E) : Φ A (periodicExtend π η) = Φ A η :=
  IsPotential.eq_of_eqOn fun _ hx ↦ periodicExtend_of_mem hπ (hA hx) η

omit [AddCommGroup S] in
/-- `Φ_B ∘ σ̃_Δ` depends only on the coordinates in `B*`. -/
lemma dependsOn_apply_periodicExtend [IsPotential Φ] (π : S → S) (B : Finset S) :
    DependsOn (fun η : S → E ↦ Φ B (periodicExtend π η)) (starImage π B : Set S) := by
  intro η ζ h
  refine IsPotential.eq_of_eqOn fun x hx ↦ ?_
  have hmem : π x ∈ (starImage π B : Set S) := by
    exact_mod_cast mem_starImage.2 ⟨x, hx, rfl⟩
  exact h (π x) hmem

/-- **Georgii (5.8)** for a general additive group of sites: `Φ_{A+g}(η) = Φ_A(η(· + g))`. -/
def IsShiftInvariantOn (Φ : Potential S E) : Prop :=
  ∀ (g : S) (A : Finset S) (η : S → E), Φ (translate A g) η = Φ A fun i ↦ η (i + g)

omit [DecidableEq S] in
/-- A shift-invariant potential has translation-invariant sup-norms. -/
lemma iSup_enorm_translate (hΦ : IsShiftInvariantOn Φ) (A : Finset S) (g : S) :
    ⨆ η, ‖Φ (translate A g) η‖ₑ = ⨆ η, ‖Φ A η‖ₑ := by
  refine le_antisymm (iSup_le fun η ↦ ?_) (iSup_le fun η ↦ ?_)
  · rw [hΦ g A η]
    exact le_iSup (fun ζ ↦ ‖Φ A ζ‖ₑ) _
  · refine le_trans (le_of_eq ?_) (le_iSup (fun ζ ↦ ‖Φ (translate A g) ζ‖ₑ) (fun i ↦ η (i - g)))
    rw [hΦ g A (fun i ↦ η (i - g))]
    simp

omit [DecidableEq S] in
/-- Shift-invariance and periodicity: `Φ_{B+g} ∘ σ̃_Δ = Φ_B ∘ σ̃_Δ` for a period `g`. -/
lemma apply_periodicExtend_translate (hπ : IsTorusReduction G Δ π)
    (hΦ : IsShiftInvariantOn Φ) (hg : g ∈ G) (B : Finset S) (η : S → E) :
    Φ (translate B g) (periodicExtend π η) = Φ B (periodicExtend π η) := by
  rw [hΦ g B (periodicExtend π η)]
  congr 1
  funext i
  simp [hπ.add_mem i hg]

end PeriodicExtend

/-! ### Georgii (4.20)(2): the representatives `ℛ(A)` -/

section Representatives

variable {S : Type*} [AddCommGroup S] {G : AddSubgroup S} {Δ : Finset S} {π : S → S}
  {anchor : Finset S → S} {B B' : Finset S} {g : S}

/-- An *anchor* is a translation-equivariant choice of a site in every nonempty finite volume
(for instance the least site for a translation-invariant linear order). It selects one
representative in each class of translates. -/
structure IsAnchor (anchor : Finset S → S) : Prop where
  /-- The anchor of a nonempty volume is one of its sites. -/
  mem : ∀ ⦃B : Finset S⦄, B.Nonempty → anchor B ∈ B
  /-- The anchor is translation-equivariant on nonempty volumes. -/
  map_translate : ∀ ⦃B : Finset S⦄, B.Nonempty → ∀ g : S, anchor (translate B g) = anchor B + g

/-- **Georgii (4.20)(2), the representatives `ℛ`.** `B` represents its class of translates
modulo the periods when its anchor lies in the box `Δ`. -/
def IsRep (Δ : Finset S) (anchor : Finset S → S) (B : Finset S) : Prop :=
  B.Nonempty ∧ anchor B ∈ Δ

/-- The unique translate of `B` modulo the periods that represents the class of `B`. -/
def red (π : S → S) (anchor : Finset S → S) (B : Finset S) : Finset S :=
  translate B (π (anchor B) - anchor B)

lemma isRep_of_subset (ha : IsAnchor anchor) (hB : B.Nonempty) (hBΔ : B ⊆ Δ) :
    IsRep Δ anchor B := ⟨hB, hBΔ (ha.mem hB)⟩

lemma red_vector_mem (hπ : IsTorusReduction G Δ π) (B : Finset S) :
    π (anchor B) - anchor B ∈ G := hπ.sub_mem' _

@[simp] lemma red_nonempty : (red π anchor B).Nonempty ↔ B.Nonempty := translate_nonempty

lemma isRep_red (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor) (hB : B.Nonempty) :
    IsRep Δ anchor (red π anchor B) := by
  refine ⟨red_nonempty.2 hB, ?_⟩
  rw [red, ha.map_translate hB]
  simpa using hπ.mapsTo (anchor B)

lemma red_eq_self (hπ : IsTorusReduction G Δ π) (h : IsRep Δ anchor B) :
    red π anchor B = B := by
  rw [red, hπ.eq_self _ h.2]
  simp

lemma red_translate (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor) (hg : g ∈ G)
    (hB : B.Nonempty) : red π anchor (translate B g) = red π anchor B := by
  rw [red, red, ha.map_translate hB, translate_translate, hπ.add_mem _ hg]
  congr 1
  abel

lemma starImage_red [DecidableEq S] (hπ : IsTorusReduction G Δ π) (B : Finset S) :
    starImage π (red π anchor B) = starImage π B :=
  starImage_translate hπ (red_vector_mem hπ B) B

/-- Two representatives in the same class of translates coincide. -/
lemma eq_of_isRep_of_translate (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor)
    (hB : IsRep Δ anchor B) (hB' : IsRep Δ anchor B') (hg : g ∈ G)
    (hBB' : B' = translate B g) : B' = B := by
  have hanchor : anchor B' = anchor B + g := by rw [hBB', ha.map_translate hB.1]
  have h0 : anchor B' = anchor B := by
    have h1 : π (anchor B') = π (anchor B) := by
      refine hπ.reduce_eq _ _ ?_
      rw [hanchor]
      simpa using hg
    rwa [hπ.eq_self _ hB'.2, hπ.eq_self _ hB.2] at h1
  have : g = 0 := by
    have := hanchor
    rw [h0] at this
    simpa using this.symm
  rw [hBB', this, translate_zero]

/-- A representative that is not contained in the box has no translate inside the box:
this is what makes Georgii's cancellation of the interior terms exact. -/
lemma not_subset_translate_of_isRep (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor)
    (hB : IsRep Δ anchor B) (hBΔ : ¬ B ⊆ Δ) (hg : g ∈ G) : ¬ translate B g ⊆ Δ := by
  intro hsub
  have hne : (translate B g).Nonempty := translate_nonempty.2 hB.1
  have heq : translate B g = B :=
    eq_of_isRep_of_translate hπ ha hB (isRep_of_subset ha hne hsub) hg rfl
  exact hBΔ (heq ▸ hsub)

/-- Georgii's "we can assume without loss that `B ∩ Λ ≠ ∅` for all `B ∈ ℛ(A)`": a representative
whose projection meets `Λ` has a translate, in the same class, that meets `Λ` itself. -/
lemma exists_translate_not_disjoint [DecidableEq S] (hπ : IsTorusReduction G Δ π)
    (ha : IsAnchor anchor) {Λ : Finset S} (hB : IsRep Δ anchor B)
    (hBΛ : ¬ Disjoint (starImage π B) Λ) :
    ∃ g ∈ G, ¬ Disjoint (translate B g) Λ ∧ red π anchor (translate B g) = B := by
  obtain ⟨i, hiB, hiΛ⟩ := Finset.not_disjoint_iff.1 hBΛ
  obtain ⟨j, hjB, rfl⟩ := mem_starImage.1 hiB
  have hg : π j - j ∈ G := hπ.sub_mem' j
  refine ⟨π j - j, hg, ?_, ?_⟩
  · refine Finset.not_disjoint_iff.2 ⟨π j, ?_, hiΛ⟩
    simpa using mem_translate_of_mem (g := π j - j) hjB
  · rw [red_translate hπ ha hg hB.1, red_eq_self hπ hB]

/-- **Georgii (4.20)(2), the reindexing estimate.** A translation-invariant weight, summed over
the representatives whose projection meets `Λ`, is dominated by its sum over all volumes meeting
`Λ`; the side condition `q` is any property inherited by translates of representatives. -/
lemma tsum_indicator_isRep_le [DecidableEq S] (hπ : IsTorusReduction G Δ π)
    (ha : IsAnchor anchor) (Λ : Finset S) (f : Finset S → ℝ≥0∞)
    (hf : ∀ (B : Finset S) (g : S), g ∈ G → f (translate B g) = f B)
    (q : Finset S → Prop)
    (hq : ∀ (B : Finset S) (g : S), IsRep Δ anchor B → g ∈ G → q B → q (translate B g)) :
    ∑' B : Finset S,
        {B : Finset S | IsRep Δ anchor B ∧ ¬ Disjoint (starImage π B) Λ ∧ q B}.indicator f B
      ≤ ∑' B : Finset S, {B : Finset S | ¬ Disjoint B Λ ∧ q B}.indicator f B := by
  classical
  set P : Set (Finset S) :=
    {B : Finset S | IsRep Δ anchor B ∧ ¬ Disjoint (starImage π B) Λ ∧ q B} with hP
  set Q : Set (Finset S) := {B : Finset S | ¬ Disjoint B Λ ∧ q B} with hQ
  have hex : ∀ B : P, ∃ B' : Finset S, ¬ Disjoint B' Λ ∧ red π anchor B' = (B : Finset S)
      ∧ q B' := by
    rintro ⟨B, hB1, hB2, hB3⟩
    obtain ⟨g, hgG, h1, h2⟩ := exists_translate_not_disjoint hπ ha hB1 hB2
    exact ⟨translate B g, h1, h2, hq B g hB1 hgG hB3⟩
  choose sec hsecΛ hsecred hsecq using hex
  have hsecQ : ∀ B : P, sec B ∈ Q := fun B ↦ ⟨hsecΛ B, hsecq B⟩
  have hinj : Function.Injective sec := by
    intro B₁ B₂ h
    have : (B₁ : Finset S) = (B₂ : Finset S) := by
      rw [← hsecred B₁, ← hsecred B₂, h]
    exact Subtype.ext this
  have hval : ∀ B : P, f (sec B) = f (B : Finset S) := by
    intro B
    rw [← hsecred B, red]
    exact (hf (sec B) _ (red_vector_mem hπ (sec B))).symm
  calc ∑' B : Finset S, P.indicator f B
      = ∑' B : P, f (B : Finset S) := (tsum_subtype P f).symm
    _ = ∑' B : P, Q.indicator f (sec B) := by
        refine tsum_congr fun B ↦ ?_
        rw [Set.indicator_of_mem (hsecQ B), hval B]
    _ ≤ ∑' B' : Finset S, Q.indicator f B' :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj _

/-- The reindexing estimate at a single site: `∑_{B ∈ ℛ, i ∈ B*} ‖Φ_B‖ ≤ ∑_{B ∋ i} ‖Φ_B‖`. -/
lemma tsum_indicator_isRep_le_of_mem [DecidableEq S] (hπ : IsTorusReduction G Δ π)
    (ha : IsAnchor anchor) (i : S) (f : Finset S → ℝ≥0∞)
    (hf : ∀ (B : Finset S) (g : S), g ∈ G → f (translate B g) = f B) :
    ∑' B : Finset S, {B : Finset S | IsRep Δ anchor B ∧ i ∈ starImage π B}.indicator f B
      ≤ ∑' B : Finset S, {B : Finset S | i ∈ B}.indicator f B := by
  have h := tsum_indicator_isRep_le hπ ha {i} f hf (fun _ ↦ True) (fun _ _ _ _ _ ↦ trivial)
  have h1 : {B : Finset S | IsRep Δ anchor B ∧ ¬ Disjoint (starImage π B) ({i} : Finset S)
        ∧ True} = {B : Finset S | IsRep Δ anchor B ∧ i ∈ starImage π B} := by
    ext B
    simp [Finset.disjoint_singleton_right]
  have h2 : {B : Finset S | ¬ Disjoint B ({i} : Finset S) ∧ True} = {B : Finset S | i ∈ B} := by
    ext B
    simp [Finset.disjoint_singleton_right]
  rwa [h1, h2] at h

end Representatives

/-! ### Georgii (4.20)(2): the periodic modification `Φ̃^Δ` -/

section PeriodicModification

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [DecidableEq S]
  {G : AddSubgroup S} {Δ : Finset S} {π : S → S} {anchor : Finset S → S}
  {Φ : Potential S E} {A B : Finset S} {i : S}

/-- **Georgii (4.20)(2).** The `Δ`-periodic modification `Φ̃^Δ_A = ∑_{B ∈ ℛ(A)} Φ_B ∘ σ̃_Δ`
of a potential; for `A ⊄ Δ` the sum is empty, so `Φ̃^Δ_A = 0`. -/
def periodicModification (Φ : Potential S E) (Δ : Finset S) (π : S → S)
    (anchor : Finset S → S) : Potential S E :=
  fun A η ↦ ∑' B : Finset S,
    {B : Finset S | IsRep Δ anchor B ∧ starImage π B = A}.indicator
      (fun B ↦ Φ B (periodicExtend π η)) B

/-- The total interaction weight `∑_{B ∈ ℛ(A)} ‖Φ_B‖` of the representatives over `A`. -/
def repWeight (Φ : Potential S E) (Δ : Finset S) (π : S → S) (anchor : Finset S → S)
    (A : Finset S) : ℝ≥0∞ :=
  ∑' B : Finset S, {B : Finset S | IsRep Δ anchor B ∧ starImage π B = A}.indicator
    (fun B ↦ ⨆ η, ‖Φ B η‖ₑ) B

omit [AddCommGroup S] in
lemma periodicModification_apply (Φ : Potential S E) (Δ : Finset S) (π : S → S)
    (anchor : Finset S → S) (A : Finset S) (η : S → E) :
    periodicModification Φ Δ π anchor A η = ∑' B : Finset S,
      {B : Finset S | IsRep Δ anchor B ∧ starImage π B = A}.indicator
        (fun B ↦ Φ B (periodicExtend π η)) B := rfl

/-- **`Φ̃^Δ_A = 0` for `A ⊄ Δ`**: every representative projects into the box. -/
lemma periodicModification_of_not_subset (hπ : IsTorusReduction G Δ π) (hA : ¬ A ⊆ Δ) :
    periodicModification Φ Δ π anchor A = 0 := by
  funext η
  rw [periodicModification_apply]
  have h0 : ∀ B : Finset S,
      {B : Finset S | IsRep Δ anchor B ∧ starImage π B = A}.indicator
        (fun B ↦ Φ B (periodicExtend π η)) B = (0 : ℝ) := by
    intro B
    refine Set.indicator_of_notMem (fun hmem ↦ hA ?_) _
    rw [← hmem.2]
    exact starImage_subset hπ B
  simp [h0]

omit [AddCommGroup S] in
/-- The sup-norm of `Φ̃^Δ_A` is bounded by the weight of `ℛ(A)`. -/
lemma iSup_enorm_periodicModification_le (Φ : Potential S E) (Δ : Finset S) (π : S → S)
    (anchor : Finset S → S) (A : Finset S) :
    ⨆ η, ‖periodicModification Φ Δ π anchor A η‖ₑ ≤ repWeight Φ Δ π anchor A := by
  refine iSup_le fun η ↦ ?_
  rw [periodicModification_apply]
  refine le_trans enorm_tsum_le_tsum_enorm (ENNReal.tsum_le_tsum fun B ↦ ?_)
  by_cases hB : B ∈ {B : Finset S | IsRep Δ anchor B ∧ starImage π B = A}
  · rw [Set.indicator_of_mem hB, Set.indicator_of_mem hB]
    exact le_iSup (fun ζ ↦ ‖Φ B ζ‖ₑ) (periodicExtend π η)
  · rw [Set.indicator_of_notMem hB, Set.indicator_of_notMem hB]
    simp

/-- The weight of `ℛ(A)` is bounded by `‖Φ‖ᵢ` for any site `i` of `A`: Georgii's reindexing. -/
lemma repWeight_le_normAt (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor)
    (hΦ : IsShiftInvariantOn Φ) (hi : i ∈ A) :
    repWeight Φ Δ π anchor A ≤ Φ.normAt i := by
  refine le_trans (ENNReal.tsum_le_tsum fun B ↦ ?_)
    (tsum_indicator_isRep_le_of_mem hπ ha i (fun B ↦ ⨆ η, ‖Φ B η‖ₑ)
      fun B g hg ↦ iSup_enorm_translate hΦ B g)
  by_cases hB : B ∈ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}
  · rw [Set.indicator_of_mem hB,
      Set.indicator_of_mem (show B ∈ {C : Finset S | IsRep Δ anchor C ∧ i ∈ starImage π C} from
        ⟨hB.1, hB.2 ▸ hi⟩)]
  · rw [Set.indicator_of_notMem hB]
    exact zero_le

lemma repWeight_ne_top [IsAbsolutelySummable Φ] (hπ : IsTorusReduction G Δ π)
    (ha : IsAnchor anchor) (hΦ : IsShiftInvariantOn Φ) (A : Finset S) :
    repWeight Φ Δ π anchor A ≠ ⊤ := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · have h0 : ∀ B : Finset S,
        {B : Finset S | IsRep Δ anchor B ∧ starImage π B = (∅ : Finset S)}.indicator
          (fun B ↦ ⨆ η, ‖Φ B η‖ₑ) B = (0 : ℝ≥0∞) := by
      intro B
      refine Set.indicator_of_notMem (fun hmem ↦ ?_) _
      exact (starImage_nonempty.2 hmem.1.1).ne_empty hmem.2
    simp [repWeight, h0]
  · exact ne_top_of_le_ne_top (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)
      (repWeight_le_normAt hπ ha hΦ hi)

/-- **Georgii (4.20)(2).** The periodic modification of a shift-invariant `Φ ∈ ℬ` has interaction
norms bounded by those of `Φ`: `‖Φ̃^Δ‖ᵢ ≤ ‖Φ‖ᵢ`. -/
lemma normAt_periodicModification_le (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor)
    (hΦ : IsShiftInvariantOn Φ) (i : S) :
    (periodicModification Φ Δ π anchor).normAt i ≤ Φ.normAt i := by
  classical
  set w : Finset S → ℝ≥0∞ := fun B ↦ ⨆ η, ‖Φ B η‖ₑ with hw
  set g : Finset S → Finset S → ℝ≥0∞ := fun A B ↦
    if i ∈ A then {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}.indicator w B else 0
    with hg
  have step1 : (periodicModification Φ Δ π anchor).normAt i
      ≤ ∑' A : Finset S, ∑' B : Finset S, g A B := by
    refine ENNReal.tsum_le_tsum fun A ↦ ?_
    by_cases hA : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {C : Finset S | i ∈ C} from hA)]
      have heq : ∑' B : Finset S, g A B = repWeight Φ Δ π anchor A := by
        simp only [hg, hA, ↓reduceIte]
        rfl
      rw [heq]
      exact iSup_enorm_periodicModification_le Φ Δ π anchor A
    · rw [Set.indicator_of_notMem (show A ∉ {C : Finset S | i ∈ C} from hA) _]
      exact zero_le
  have step2 : ∑' A : Finset S, ∑' B : Finset S, g A B
      = ∑' B : Finset S, {C : Finset S | IsRep Δ anchor C ∧ i ∈ starImage π C}.indicator w B := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun B ↦ ?_
    rw [tsum_eq_single (starImage π B) ?_]
    · by_cases hB : B ∈ {C : Finset S | IsRep Δ anchor C ∧ i ∈ starImage π C}
      · rw [Set.indicator_of_mem hB, hg]
        simp only [hB.2, ↓reduceIte]
        rw [Set.indicator_of_mem (show B ∈ {C : Finset S | IsRep Δ anchor C
          ∧ starImage π C = starImage π B} from ⟨hB.1, rfl⟩)]
      · rw [Set.indicator_of_notMem hB, hg]
        by_cases hi : i ∈ starImage π B
        · simp only [hi, ↓reduceIte]
          refine Set.indicator_of_notMem (fun hmem ↦ hB ⟨hmem.1, hi⟩) _
        · simp [hi]
    · intro A hA
      simp only [hg]
      split_ifs with h
      · exact Set.indicator_of_notMem (fun hmem ↦ hA hmem.2.symm) _
      · rfl
  calc (periodicModification Φ Δ π anchor).normAt i
      ≤ ∑' A : Finset S, ∑' B : Finset S, g A B := step1
    _ = ∑' B : Finset S,
          {C : Finset S | IsRep Δ anchor C ∧ i ∈ starImage π C}.indicator w B := step2
    _ ≤ ∑' B : Finset S, {C : Finset S | i ∈ C}.indicator w B :=
        tsum_indicator_isRep_le_of_mem hπ ha i w fun B g hg ↦ iSup_enorm_translate hΦ B g
    _ = Φ.normAt i := rfl

/-- **Georgii (4.20)(2).** The periodic modification of a shift-invariant `Φ ∈ ℬ` is
absolutely summable, hence `λ`-admissible. -/
lemma isAbsolutelySummable_periodicModification [IsAbsolutelySummable Φ]
    (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor) (hΦ : IsShiftInvariantOn Φ) :
    IsAbsolutelySummable (periodicModification Φ Δ π anchor) where
  normAt_ne_top i := ne_top_of_le_ne_top (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)
    (normAt_periodicModification_le hπ ha hΦ i)

omit [AddCommGroup S] [DecidableEq S] in
lemma measurable_periodicExtend (π : S → S) :
    Measurable (periodicExtend π : (S → E) → S → E) :=
  measurable_pi_lambda _ fun i ↦ measurable_pi_apply (π i)

/-- The representative series defining `Φ̃^Δ_A` converges absolutely. -/
lemma summable_periodicModification_terms [IsAbsolutelySummable Φ]
    (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor) (hΦ : IsShiftInvariantOn Φ)
    (A : Finset S) (η : S → E) :
    Summable fun B : Finset S ↦
      {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}.indicator
        (fun B ↦ Φ B (periodicExtend π η)) B := by
  refine Summable.of_enorm (ne_of_lt (lt_of_le_of_lt ?_
    (lt_top_iff_ne_top.2 (repWeight_ne_top hπ ha hΦ A))))
  refine ENNReal.tsum_le_tsum fun B ↦ ?_
  by_cases hB : B ∈ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}
  · rw [Set.indicator_of_mem hB, Set.indicator_of_mem hB]
    exact le_iSup (fun ζ ↦ ‖Φ B ζ‖ₑ) _
  · rw [Set.indicator_of_notMem hB _, Set.indicator_of_notMem hB _]
    simp

/-- **Georgii (4.20)(2).** The periodic modification is a potential: `Φ̃^Δ_A` is
`𝓕_A`-measurable. -/
lemma isPotential_periodicModification [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ]
    (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor) (hΦ : IsShiftInvariantOn Φ) :
    IsPotential (periodicModification Φ Δ π anchor) where
  measurable A := by
    have hdep : DependsOn (periodicModification Φ Δ π anchor A) (A : Set S) := by
      intro η ζ h
      rw [periodicModification_apply, periodicModification_apply]
      refine tsum_congr fun B ↦ ?_
      by_cases hB : B ∈ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}
      · rw [Set.indicator_of_mem hB, Set.indicator_of_mem hB]
        refine dependsOn_apply_periodicExtend π B ?_
        rw [hB.2]
        exact h
      · rw [Set.indicator_of_notMem hB _, Set.indicator_of_notMem hB _]
    refine Measurable.cylinderEvents_of_dependsOn ?_ hdep
    have hmeasB : ∀ B : Finset S, Measurable (fun η : S → E ↦ Φ B (periodicExtend π η)) :=
      fun B ↦ ((IsPotential.measurable (Φ := Φ) B).mono
        (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (B : Set S))) le_rfl).comp
          (measurable_periodicExtend π)
    refine measurable_of_tendsto_metrizable' atTop
      (f := fun s : Finset (Finset S) ↦ fun η : S → E ↦ ∑ B ∈ s,
        {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}.indicator
          (fun B ↦ Φ B (periodicExtend π η)) B) (fun s ↦ ?_) ?_
    · refine Finset.measurable_sum _ fun B _ ↦ ?_
      by_cases hB : B ∈ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}
      · simpa only [Set.indicator_of_mem hB] using hmeasB B
      · simpa only [Set.indicator_of_notMem hB] using measurable_const (a := (0 : ℝ))
    · exact tendsto_pi_nhds.2 fun η ↦
        (summable_periodicModification_terms hπ ha hΦ A η).hasSum

/-! ### Georgii (4.20)(2): the Hamiltonian estimate -/

/-- For `∅ ≠ A ⊆ Δ`, the term `B = A` of the representative series is `Φ_A` itself; the rest is
Georgii's error term. -/
lemma periodicModification_sub_eq [IsPotential Φ] [IsAbsolutelySummable Φ]
    (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor) (hΦ : IsShiftInvariantOn Φ)
    (hA : A.Nonempty) (hAΔ : A ⊆ Δ) (η : S → E) :
    periodicModification Φ Δ π anchor A η - Φ A η
      = ∑' B : Finset S, {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A ∧ C ≠ A}.indicator
          (fun B ↦ Φ B (periodicExtend π η)) B := by
  classical
  have hsum := summable_periodicModification_terms hπ ha hΦ A η
  rw [periodicModification_apply, hsum.tsum_eq_add_tsum_ite A]
  have h1 : {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}.indicator
      (fun B ↦ Φ B (periodicExtend π η)) A = Φ A η := by
    rw [Set.indicator_of_mem
      (show A ∈ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A} from
        ⟨isRep_of_subset ha hA hAΔ, starImage_eq_self hπ hAΔ⟩)]
    exact apply_periodicExtend_of_subset hπ hAΔ η
  have h2 : ∀ B : Finset S, (if B = A then (0 : ℝ) else
      {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}.indicator
        (fun B ↦ Φ B (periodicExtend π η)) B)
      = {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A ∧ C ≠ A}.indicator
          (fun B ↦ Φ B (periodicExtend π η)) B := by
    intro B
    by_cases hBA : B = A
    · subst hBA
      have hnot : B ∉ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = B ∧ C ≠ B} :=
        fun h ↦ h.2.2 rfl
      rw [Set.indicator_of_notMem hnot _]
      simp
    · simp only [hBA, ↓reduceIte]
      by_cases hB : B ∈ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A}
      · rw [Set.indicator_of_mem hB,
          Set.indicator_of_mem (show B ∈ {C : Finset S | IsRep Δ anchor C
            ∧ starImage π C = A ∧ C ≠ A} from ⟨hB.1, hB.2, hBA⟩)]
      · rw [Set.indicator_of_notMem hB _,
          Set.indicator_of_notMem (fun h ↦ hB ⟨h.1, h.2.1⟩) _]
  rw [h1, tsum_congr h2]
  ring

/-- The bound for the `A`-term of `H^{Φ̃^Δ}_Λ − H^Φ_Λ`: Georgii's two sums. -/
def periodicTermBound (Φ : Potential S E) (Δ : Finset S) (π : S → S) (anchor : Finset S → S)
    (Λ A : Finset S) : ℝ≥0∞ :=
  {C : Finset S | ¬ Disjoint C Λ ∧ ¬ C ⊆ Δ}.indicator (fun C ↦ ⨆ η, ‖Φ C η‖ₑ) A
    + ∑' B : Finset S,
        {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A ∧ C ≠ A ∧ ¬ Disjoint A Λ}.indicator
          (fun C ↦ ⨆ η, ‖Φ C η‖ₑ) B

lemma enorm_hamiltonianTerms_periodicModification_sub_le [IsPotential Φ] [IsAbsolutelySummable Φ]
    (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor) (hΦ : IsShiftInvariantOn Φ)
    (Λ A : Finset S) (η : S → E) :
    ‖(periodicModification Φ Δ π anchor).hamiltonianTerms Λ η A - Φ.hamiltonianTerms Λ η A‖ₑ
      ≤ periodicTermBound Φ Δ π anchor Λ A := by
  classical
  by_cases hd : Disjoint A Λ
  · rw [hamiltonianTerms_of_disjoint (Φ := periodicModification Φ Δ π anchor) hd,
      hamiltonianTerms_of_disjoint (Φ := Φ) hd]
    simp
  · rw [hamiltonianTerms_of_not_disjoint (Φ := periodicModification Φ Δ π anchor) hd,
      hamiltonianTerms_of_not_disjoint (Φ := Φ) hd]
    obtain ⟨x, hxA, -⟩ := Finset.not_disjoint_iff.1 hd
    have hAne : A.Nonempty := ⟨x, hxA⟩
    by_cases hAΔ : A ⊆ Δ
    · have h1 : {C : Finset S | ¬ Disjoint C Λ ∧ ¬ C ⊆ Δ}.indicator
          (fun C ↦ ⨆ η, ‖Φ C η‖ₑ) A = 0 :=
        Set.indicator_of_notMem (fun h ↦ h.2 hAΔ) _
      rw [periodicModification_sub_eq hπ ha hΦ hAne hAΔ η, periodicTermBound, h1, zero_add]
      refine le_trans enorm_tsum_le_tsum_enorm (ENNReal.tsum_le_tsum fun B ↦ ?_)
      by_cases hB : B ∈ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A ∧ C ≠ A}
      · rw [Set.indicator_of_mem hB,
          Set.indicator_of_mem (show B ∈ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A
            ∧ C ≠ A ∧ ¬ Disjoint A Λ} from ⟨hB.1, hB.2.1, hB.2.2, hd⟩)]
        exact le_iSup (fun ζ ↦ ‖Φ B ζ‖ₑ) _
      · rw [Set.indicator_of_notMem hB _]
        simp
    · have h0 : periodicModification Φ Δ π anchor A η = 0 := by
        rw [periodicModification_of_not_subset (anchor := anchor) hπ hAΔ]
        rfl
      rw [h0, periodicTermBound,
        Set.indicator_of_mem (show A ∈ {C : Finset S | ¬ Disjoint C Λ ∧ ¬ C ⊆ Δ} from ⟨hd, hAΔ⟩)]
      refine le_trans ?_ le_self_add
      rw [zero_sub, enorm_neg]
      exact le_iSup (fun ζ ↦ ‖Φ A ζ‖ₑ) η

lemma tsum_periodicTermBound_le (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor)
    (hΦ : IsShiftInvariantOn Φ) (Λ : Finset S) :
    ∑' A : Finset S, periodicTermBound Φ Δ π anchor Λ A ≤ 2 * Φ.tailWeight Δ Λ := by
  classical
  set w : Finset S → ℝ≥0∞ := fun B ↦ ⨆ η, ‖Φ B η‖ₑ with hw
  have hswap : ∑' A : Finset S, ∑' B : Finset S,
      {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A ∧ C ≠ A
        ∧ ¬ Disjoint A Λ}.indicator w B
      ≤ Φ.tailWeight Δ Λ := by
    rw [ENNReal.tsum_comm]
    refine le_trans (ENNReal.tsum_le_tsum fun B ↦ ?_)
      (tsum_indicator_isRep_le hπ ha Λ w (fun B g hg ↦ iSup_enorm_translate hΦ B g)
        (fun C ↦ ¬ C ⊆ Δ)
        (fun B g hB hg hq ↦ not_subset_translate_of_isRep hπ ha hB hq hg))
    rw [tsum_eq_single (starImage π B) ?_]
    · by_cases hB : B ∈ {C : Finset S | IsRep Δ anchor C ∧ starImage π C = starImage π B
        ∧ C ≠ starImage π B ∧ ¬ Disjoint (starImage π B) Λ}
      · rw [Set.indicator_of_mem hB,
          Set.indicator_of_mem (show B ∈ {C : Finset S | IsRep Δ anchor C
            ∧ ¬ Disjoint (starImage π C) Λ ∧ ¬ C ⊆ Δ} from
              ⟨hB.1, hB.2.2.2, fun hsub ↦ hB.2.2.1 (starImage_eq_self hπ hsub).symm⟩)]
      · rw [Set.indicator_of_notMem hB _]
        exact zero_le
    · intro A hA
      exact Set.indicator_of_notMem (fun hmem ↦ hA hmem.2.1.symm) _
  calc ∑' A : Finset S, periodicTermBound Φ Δ π anchor Λ A
      = (∑' A : Finset S, {C : Finset S | ¬ Disjoint C Λ ∧ ¬ C ⊆ Δ}.indicator w A)
        + ∑' A : Finset S, ∑' B : Finset S,
          {C : Finset S | IsRep Δ anchor C ∧ starImage π C = A ∧ C ≠ A
            ∧ ¬ Disjoint A Λ}.indicator w B := ENNReal.tsum_add
    _ ≤ Φ.tailWeight Δ Λ + Φ.tailWeight Δ Λ := add_le_add le_rfl hswap
    _ = 2 * Φ.tailWeight Δ Λ := (two_mul _).symm

/-- **Georgii (4.20)(2), the Hamiltonian estimate.**
`‖H^{Φ̃^Δ − Φ}_Λ‖ ≤ 2 ∑_{A ∩ Λ ≠ ∅, A ⊄ Δ} ‖Φ_A‖`, in `ℝ≥0∞`. -/
theorem enorm_hamiltonian_periodicModification_sub_le [Countable S] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor)
    (hΦ : IsShiftInvariantOn Φ) (Λ : Finset S) (η : S → E) :
    ‖(periodicModification Φ Δ π anchor).hamiltonian Λ η - Φ.hamiltonian Λ η‖ₑ
      ≤ 2 * Φ.tailWeight Δ Λ := by
  have := isAbsolutelySummable_periodicModification (Φ := Φ) hπ ha hΦ
  have hsT : Summable ((periodicModification Φ Δ π anchor).hamiltonianTerms Λ η) :=
    summable_hamiltonianTerms Λ η
  have hsΦ : Summable (Φ.hamiltonianTerms Λ η) := summable_hamiltonianTerms Λ η
  have hdiff : (periodicModification Φ Δ π anchor).hamiltonian Λ η - Φ.hamiltonian Λ η
      = ∑' B : Finset S, ((periodicModification Φ Δ π anchor).hamiltonianTerms Λ η B
          - Φ.hamiltonianTerms Λ η B) := by
    rw [hamiltonian_eq_tsum (Φ := periodicModification Φ Δ π anchor) Λ η,
      hamiltonian_eq_tsum (Φ := Φ) Λ η]
    exact (hsT.tsum_sub hsΦ).symm
  rw [hdiff]
  refine le_trans enorm_tsum_le_tsum_enorm (le_trans (ENNReal.tsum_le_tsum fun A ↦
    enorm_hamiltonianTerms_periodicModification_sub_le hπ ha hΦ Λ A η) ?_)
  exact tsum_periodicTermBound_le hπ ha hΦ Λ

/-- **Georgii (4.20)(2), the Hamiltonian estimate.**
`|H^{Φ̃^Δ}_Λ(η) − H^Φ_Λ(η)| ≤ 2 ∑_{A ∩ Λ ≠ ∅, A ⊄ Δ} ‖Φ_A‖ = 2 · tail Δ Λ`. -/
theorem abs_hamiltonian_periodicModification_sub_le [Countable S] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (hπ : IsTorusReduction G Δ π) (ha : IsAnchor anchor)
    (hΦ : IsShiftInvariantOn Φ) (Λ : Finset S) (η : S → E) :
    |(periodicModification Φ Δ π anchor).hamiltonian Λ η - Φ.hamiltonian Λ η|
      ≤ 2 * Φ.tail Δ Λ := by
  have h := enorm_hamiltonian_periodicModification_sub_le hπ ha hΦ Λ η
  rw [← ENNReal.toReal_le_toReal (by simp)
    (ENNReal.mul_ne_top (by simp) (tailWeight_ne_top (Φ := Φ) Δ Λ))] at h
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), tail,
    ENNReal.toReal_mul] using h

end PeriodicModification

/-! ### Georgii Example (4.20)(2): periodic boundary conditions -/

section PeriodicBoundary

variable {S E : Type*} [Countable S] [MeasurableSpace E] [AddCommGroup S] [DecidableEq S]
  {Φ : Potential S E} [IsPotential Φ] [IsAbsolutelySummable Φ]
  {ι : Type*} {l : Filter ι} {G : ι → AddSubgroup S} {Δ : ι → Finset S} {π : ι → S → S}
  {anchor : Finset S → S}
  (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

/-- **Georgii (4.19) for the periodic modifications**: `γ^{Φ̃^Δ} → γ^Φ` uniformly in the
𝓛-topology as `Δ ↑ S`, with `D`-function `2 · tail Δ Λ`. -/
theorem tendsto_dist_action_periodicModification
    [∀ i, IsPotential (periodicModification Φ (Δ i) (π i) anchor)]
    [∀ i, IsAbsolutelySummable (periodicModification Φ (Δ i) (π i) anchor)]
    (hπ : ∀ i, IsTorusReduction (G i) (Δ i) (π i)) (ha : IsAnchor anchor)
    (hΦ : IsShiftInvariantOn Φ) (hΔ : Tendsto Δ l atTop) :
    ∀ (Λ : Finset S) ⦃f : lp (fun _ : S → E ↦ ℝ) ∞⦄, f ∈ localFunctions S E →
      Tendsto (fun i ↦ dist
        ((gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ i) (π i) anchor) ν β).action Λ f)
        ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).action Λ f)) l (𝓝 0) :=
  tendsto_dist_action_gibbsSpecification_of_mem_localFunctions ν β
    (Φs := fun i ↦ periodicModification Φ (Δ i) (π i) anchor)
    (D := fun i Λ ↦ 2 * Φ.tail (Δ i) Λ)
    (fun i Λ η ↦ abs_hamiltonian_periodicModification_sub_le (hπ i) ha hΦ Λ η)
    (fun Λ ↦ by simpa using ((tendsto_tail_atTop (Φ := Φ) Λ).comp hΔ).const_mul 2)

/-- **Georgii Example (4.20)(2).** Every cluster point of the periodic-boundary net
`Δ ↦ ν_Δ γ^{Φ̃^Δ}_Δ`, `Δ ↑ S`, is a Gibbs measure for the shift-invariant potential `Φ ∈ ℬ`. -/
theorem mem_GP_of_mapClusterPt_periodicModification [l.NeBot]
    [∀ i, IsPotential (periodicModification Φ (Δ i) (π i) anchor)]
    [∀ i, IsAbsolutelySummable (periodicModification Φ (Δ i) (π i) anchor)]
    (hπ : ∀ i, IsTorusReduction (G i) (Δ i) (π i)) (ha : IsAnchor anchor)
    (hΦ : IsShiftInvariantOn Φ) (hΔ : Tendsto Δ l atTop)
    (νs : ι → ProbabilityMeasure (S → E)) {μ : ProbabilityMeasure (S → E)}
    (hcp : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      fun i ↦ WithSetwiseTopology.ofMeasure
        ((gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ i) (π i) anchor) ν β).bindPM (Δ i) (νs i))) :
    μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) :=
  mem_GP_of_mapClusterPt (isQuasilocal_gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β)
    hΔ (tendsto_dist_action_periodicModification ν β hπ ha hΦ hΔ) hcp

/-- **Georgii Example (4.20)(2)** for a configurational boundary condition: every cluster point
of the net `(γ^{Φ̃^Δ}_Δ(·|ω))_Δ` of Gibbs distributions with periodic boundary condition belongs
to `𝒢(Φ)`. -/
theorem mem_GP_of_mapClusterPt_periodicModification_finiteVolumeDistributions [l.NeBot]
    [∀ i, IsPotential (periodicModification Φ (Δ i) (π i) anchor)]
    [∀ i, IsAbsolutelySummable (periodicModification Φ (Δ i) (π i) anchor)]
    (hπ : ∀ i, IsTorusReduction (G i) (Δ i) (π i)) (ha : IsAnchor anchor)
    (hΦ : IsShiftInvariantOn Φ) (hΔ : Tendsto Δ l atTop) (ω : S → E)
    {μ : ProbabilityMeasure (S → E)}
    (hcp : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      fun i ↦ WithSetwiseTopology.ofMeasure
        (finiteVolumeDistributions (gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ i) (π i) anchor) ν β) ω (Δ i))) :
    μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) := by
  refine mem_GP_of_mapClusterPt_periodicModification ν β hπ ha hΦ hΔ
    (fun _ ↦ ⟨Measure.dirac ω, inferInstance⟩) ?_
  have h : ∀ i : ι,
      (gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ i) (π i) anchor) ν β).bindPM (Δ i)
          ⟨Measure.dirac ω, inferInstance⟩
        = finiteVolumeDistributions (gibbsSpecificationOfAbsolutelySummable
            (Φ := periodicModification Φ (Δ i) (π i) anchor) ν β) ω (Δ i) :=
    fun i ↦ Subtype.ext (Measure.dirac_bind
      ((gibbsSpecificationOfAbsolutelySummable
        (Φ := periodicModification Φ (Δ i) (π i) anchor) ν β).measurable_kernel_toMeasure (Δ i)) ω)
  simpa only [h] using hcp

end PeriodicBoundary

/-! ### The boxes of `ℤ` as tori: the hypotheses are satisfiable -/

section IntBoxes

/-- Reduction of `ℤ` modulo `p` onto the box `[m, m + p)`, Georgii's identification of a box
with the torus `ℤ / pℤ`. -/
def intReduce (m p : ℤ) : ℤ → ℤ := fun i ↦ m + (i - m) % p

/-- **Georgii (4.20)(2) on `ℤ`.** The box `[m, m + p)` is a fundamental domain for `pℤ`, with
reduction `intReduce m p`. -/
lemma isTorusReduction_intReduce {p : ℤ} (hp : 0 < p) (m : ℤ) :
    IsTorusReduction (AddSubgroup.zmultiples p) (Finset.Ico m (m + p)) (intReduce m p) where
  mapsTo i := by
    rw [Finset.mem_Ico, intReduce]
    constructor
    · simpa using Int.emod_nonneg (i - m) hp.ne'
    · have := Int.emod_lt_of_pos (i - m) hp
      omega
  eq_self i hi := by
    rw [Finset.mem_Ico] at hi
    rw [intReduce, Int.emod_eq_of_lt (by omega) (by omega)]
    ring
  sub_mem i := by
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨(i - m) / p, ?_⟩
    rw [intReduce, smul_eq_mul, Int.emod_def]
    ring
  reduce_eq i j h := by
    rw [AddSubgroup.mem_zmultiples_iff] at h
    obtain ⟨k, hk⟩ := h
    rw [smul_eq_mul] at hk
    have hdvd : p ∣ (i - m) - (j - m) := ⟨k, by linear_combination -hk⟩
    rw [intReduce, intReduce]
    have : (i - m) % p = (j - m) % p :=
      Int.ModEq.symm (Int.modEq_iff_dvd.2 (by simpa using hdvd))
    rw [this]

/-- The least site of a nonempty volume: a translation-equivariant anchor on `ℤ`. -/
def minAnchor (B : Finset ℤ) : ℤ := if h : B.Nonempty then B.min' h else 0

/-- **Georgii (4.20)(2) on `ℤ`.** `minAnchor` selects one representative in each class of
translates, so the representative sets `ℛ(A)` exist. -/
lemma isAnchor_minAnchor : IsAnchor minAnchor where
  mem B hB := by
    simp only [minAnchor, hB, ↓reduceDIte]
    exact B.min'_mem hB
  map_translate B hB g := by
    have hBg : (translate B g).Nonempty := translate_nonempty.2 hB
    simp only [minAnchor, hB, hBg, ↓reduceDIte]
    refine le_antisymm (Finset.min'_le _ _ (mem_translate_of_mem (B.min'_mem hB))) ?_
    have hmem : (translate B g).min' hBg - g ∈ B :=
      mem_translate.1 ((translate B g).min'_mem hBg)
    have := B.min'_le _ hmem
    omega

end IntBoxes

/-! ### The lattice `ℤ^d`: Georgii (5.8) is the translation-invariance used above -/

section ShiftBridge

variable {E : Type*} [MeasurableSpace E] {d : ℕ}

/-- The repo's shift-invariance on `ℤ^d` (Georgii (5.8)) is the translation-invariance
`IsShiftInvariantOn` used in Georgii (4.20)(2). -/
lemma isShiftInvariantOn_of_isShiftInvariant {Φ : Potential (Fin d → ℤ) E}
    (hΦ : Φ.IsShiftInvariant) : IsShiftInvariantOn Φ := by
  intro g A η
  have h := congrFun (congrFun (hΦ g) (translate A g)) η
  rw [Potential.map_apply] at h
  have hmap : (translate A g).map (shift E g).sites.symm.toEmbedding = A := by
    ext x
    simp [translate, shift]
  have hinv : (shift E g).inv.toFun η = fun i ↦ η (i + g) := by
    funext i
    simp
  rw [hmap, hinv] at h
  exact h.symm

end ShiftBridge

/-! ### Georgii (4.20)(2) on `ℤ`: the net of boxes -/

section IntPeriodicBoundary

/-- The left endpoint of the `n`-th box of `ℤ`. -/
def intBoxLeft (n : ℕ) : ℤ := -((n : ℤ) + 1)

/-- The side length of the `n`-th box of `ℤ`. -/
def intBoxLen (n : ℕ) : ℤ := 2 * ((n : ℤ) + 1)

lemma intBoxLen_pos (n : ℕ) : 0 < intBoxLen n := by
  rw [intBoxLen]; positivity

/-- Georgii's net `𝒮_□` in dimension one: the boxes `Δ_n = [-(n+1), n+1)`. -/
def intBox (n : ℕ) : Finset ℤ := Finset.Ico (intBoxLeft n) (intBoxLeft n + intBoxLen n)

/-- The `n`-th box of `ℤ`, viewed as the torus `ℤ / (2(n+1))ℤ`. -/
def intTorus (n : ℕ) : ℤ → ℤ := intReduce (intBoxLeft n) (intBoxLen n)

lemma isTorusReduction_intTorus (n : ℕ) :
    IsTorusReduction (AddSubgroup.zmultiples (intBoxLen n)) (intBox n) (intTorus n) :=
  isTorusReduction_intReduce (intBoxLen_pos n) _

/-- **`Δ_n ↑ ℤ`**: the boxes exhaust the lattice. -/
lemma tendsto_intBox_atTop : Filter.Tendsto intBox Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun Λ ↦ ⟨Λ.sup Int.natAbs, fun n hn x hx ↦ ?_⟩
  have hle : x.natAbs ≤ Λ.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hx
  rw [intBox, Finset.mem_Ico, intBoxLeft, intBoxLen]
  omega

variable {E : Type*} [MeasurableSpace E] {Φ : Potential ℤ E} [IsPotential Φ]
  [IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

lemma isPotential_periodicModification_intBox (hΦ : IsShiftInvariantOn Φ) (n : ℕ) :
    IsPotential (periodicModification Φ (intBox n) (intTorus n) minAnchor) :=
  isPotential_periodicModification (isTorusReduction_intTorus n) isAnchor_minAnchor hΦ

omit [IsPotential Φ] in
lemma isAbsolutelySummable_periodicModification_intBox (hΦ : IsShiftInvariantOn Φ) (n : ℕ) :
    IsAbsolutelySummable (periodicModification Φ (intBox n) (intTorus n) minAnchor) :=
  isAbsolutelySummable_periodicModification (isTorusReduction_intTorus n) isAnchor_minAnchor hΦ

/-- **Georgii Example (4.20)(2) on `ℤ`.** Every cluster point of the periodic-boundary net
`(γ^{Φ̃^{Δ_n}}_{Δ_n})_n` over the boxes `Δ_n = [-(n+1), n+1)` is a Gibbs measure for the
shift-invariant potential `Φ ∈ ℬ`. -/
theorem mem_GP_of_mapClusterPt_intPeriodic
    [∀ n, IsPotential (periodicModification Φ (intBox n) (intTorus n) minAnchor)]
    [∀ n, IsAbsolutelySummable (periodicModification Φ (intBox n) (intTorus n) minAnchor)]
    (hΦ : IsShiftInvariantOn Φ) (νs : ℕ → ProbabilityMeasure (ℤ → E))
    {μ : ProbabilityMeasure (ℤ → E)}
    (hcp : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence ℤ E) atTop
      fun n : ℕ ↦ WithSetwiseTopology.ofMeasure
        ((gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (intBox n) (intTorus n) minAnchor) ν β).bindPM
            (intBox n) (νs n))) :
    μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) :=
  mem_GP_of_mapClusterPt_periodicModification ν β
    (G := fun n ↦ AddSubgroup.zmultiples (intBoxLen n)) isTorusReduction_intTorus
    isAnchor_minAnchor hΦ tendsto_intBox_atTop νs hcp

end IntPeriodicBoundary

/-! ### Georgii (4.20): the finite-volume Gibbs distribution with free / periodic boundary
condition -/

section SupportedIn

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Ψ : Potential S E} {Δ : Finset S}
  (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

omit [Countable S] in
/-- Integrals of `𝓕_Δ`-measurable functions against the free kernel do not see the boundary
condition. -/
lemma lintegral_isssd_eq_of_cylinderEvents (Δ : Finset S) (ω : S → E) {f : (S → E) → ℝ≥0∞}
    (hf : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] f) :
    ∫⁻ x, f x ∂(Specification.isssd (S := S) (E := E) ν Δ ω)
      = ∫⁻ x, f x ∂(Measure.infinitePi fun _ : S ↦ ν) := by
  have hm : cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi (X := fun _ : S ↦ E)
  have htrim : (Specification.isssd (S := S) (E := E) ν Δ ω).trim hm
      = (Measure.infinitePi fun _ : S ↦ ν).trim hm := by
    refine @Measure.ext _ (cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)) _ _ fun A hA ↦ ?_
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]
    exact Specification.isssd_apply_of_mem_cylinderEvents ν Δ ω hA
  rw [← lintegral_trim hm hf, ← lintegral_trim hm hf, htrim]

omit [Countable S] in
/-- A potential supported in `Δ` has a Hamiltonian in `Δ` depending only on the sites of `Δ`. -/
lemma dependsOn_hamiltonian_of_supported [IsPotential Ψ]
    (hΨ : ∀ A : Finset S, ¬ A ⊆ Δ → Ψ A = 0) : DependsOn (Ψ.hamiltonian Δ) (Δ : Set S) := by
  intro x y hxy
  have hterms : Ψ.hamiltonianTerms Δ x = Ψ.hamiltonianTerms Δ y := by
    funext A
    by_cases hd : Disjoint A Δ
    · rw [hamiltonianTerms_of_disjoint hd, hamiltonianTerms_of_disjoint hd]
    · rw [hamiltonianTerms_of_not_disjoint hd, hamiltonianTerms_of_not_disjoint hd]
      by_cases hsub : A ⊆ Δ
      · exact IsPotential.eq_of_eqOn fun i hi ↦ hxy i (by exact_mod_cast hsub hi)
      · rw [hΨ A hsub]
        rfl
  rw [hamiltonian, hamiltonian, hterms]

lemma measurable_hamiltonian_of_supported [IsPotential Ψ] [IsSummable Ψ]
    (hΨ : ∀ A : Finset S, ¬ A ⊆ Δ → Ψ A = 0) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] (Ψ.hamiltonian Δ) :=
  (measurable_hamiltonian (Φ := Ψ) Δ).cylinderEvents_of_dependsOn
    (dependsOn_hamiltonian_of_supported hΨ)

lemma measurable_boltzmannFactor_of_supported [IsPotential Ψ] [IsSummable Ψ]
    (hΨ : ∀ A : Finset S, ¬ A ⊆ Δ → Ψ A = 0) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] (Ψ.boltzmannFactor β Δ) := by
  have hH := measurable_hamiltonian_of_supported (Ψ := Ψ) hΨ
  exact ((hH.const_mul (-β)).exp).ennreal_ofReal

/-- For a potential supported in `Δ`, the partition function in `Δ` does not depend on the
boundary condition. -/
lemma premodifierZ_eq_of_supported [IsPotential Ψ] [IsSummable Ψ]
    (hΨ : ∀ A : Finset S, ¬ A ⊆ Δ → Ψ A = 0) (ω : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν (Ψ.boltzmannFactor β) Δ ω
      = ∫⁻ x, Ψ.boltzmannFactor β Δ x ∂(Measure.infinitePi fun _ : S ↦ ν) :=
  lintegral_isssd_eq_of_cylinderEvents ν Δ ω (measurable_boltzmannFactor_of_supported β hΨ)

lemma measurable_premodifierNorm_of_supported [IsPotential Ψ] [IsSummable Ψ]
    (hΨ : ∀ A : Finset S, ¬ A ⊆ Δ → Ψ A = 0) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)]
      (Specification.premodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor β) Δ) := by
  have heq : Specification.premodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor β) Δ
      = fun x ↦ Ψ.boltzmannFactor β Δ x
        * (∫⁻ y, Ψ.boltzmannFactor β Δ y ∂(Measure.infinitePi fun _ : S ↦ ν))⁻¹ := by
    funext x
    rw [Specification.premodifierNorm, premodifierZ_eq_of_supported ν β hΨ x, div_eq_mul_inv]
  rw [heq]
  exact (measurable_boltzmannFactor_of_supported β hΨ).mul_const _

/-- **Georgii (4.20).** For a potential supported in `Δ` — the free-boundary truncation `Φ^Δ` or
the periodic modification `Φ̃^Δ` — the restriction of `γ^Ψ_Δ(·|ω)` to `𝓕_Δ` does not depend on the
boundary condition `ω`. -/
theorem gibbsSpecificationOfAbsolutelySummable_apply_eq_of_supported [IsPotential Ψ]
    [IsAbsolutelySummable Ψ] (hΨ : ∀ A : Finset S, ¬ A ⊆ Δ → Ψ A = 0) (ω ω' : S → E)
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Ψ) ν β Δ ω A
      = gibbsSpecificationOfAbsolutelySummable (Φ := Ψ) ν β Δ ω' A := by
  have hAfull : MeasurableSet A := cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hA
  have hρ := measurable_premodifierNorm_of_supported (Ψ := Ψ) ν β hΨ
  have key : ∀ ζ : S → E, gibbsSpecificationOfAbsolutelySummable (Φ := Ψ) ν β Δ ζ A
      = ∫⁻ x, A.indicator
          (Specification.premodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor β) Δ) x
          ∂(Measure.infinitePi fun _ : S ↦ ν) := by
    intro ζ
    rw [gibbsSpecificationOfAbsolutelySummable, Specification.modification_apply,
      withDensity_apply _ hAfull, ← lintegral_indicator hAfull]
    exact lintegral_isssd_eq_of_cylinderEvents ν Δ ζ (hρ.indicator hA)
  rw [key ω, key ω']

/-- **Georgii Example (4.20)(1).** The Gibbs distribution in `Δ` with free boundary condition:
the restriction of `γ^{Φ^Δ}_Δ(·|ω)` to `𝓕_Δ` does not depend on `ω`. -/
theorem gibbsSpecification_truncation_apply_eq {Φ : Potential S E} [IsPotential Φ]
    [IsAbsolutelySummable Φ] (Δ : Finset S) (ω ω' : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β Δ ω A
      = gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β Δ ω' A :=
  gibbsSpecificationOfAbsolutelySummable_apply_eq_of_supported ν β
    (fun _ hB ↦ truncation_of_not_subset hB) ω ω' hA


/-- **Georgii Example (4.20)(2).** The Gibbs distribution in `Δ` with periodic boundary
condition: the restriction of `γ^{Φ̃^Δ}_Δ(·|ω)` to `𝓕_Δ` does not depend on `ω`. -/
theorem gibbsSpecification_periodicModification_apply_eq [AddCommGroup S] [DecidableEq S]
    {Gp : AddSubgroup S} {π : S → S} {anchor : Finset S → S} {Φ : Potential S E}
    [IsPotential (periodicModification Φ Δ π anchor)]
    [IsAbsolutelySummable (periodicModification Φ Δ π anchor)]
    (hπ : IsTorusReduction Gp Δ π) (ω ω' : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    gibbsSpecificationOfAbsolutelySummable (Φ := periodicModification Φ Δ π anchor) ν β Δ ω A
      = gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ Δ π anchor) ν β Δ ω' A :=
  gibbsSpecificationOfAbsolutelySummable_apply_eq_of_supported ν β
    (fun _ hB ↦ periodicModification_of_not_subset hπ hB) ω ω' hA

end SupportedIn

end Potential

end

end
