/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.UniformAverage
public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Specification.InvariantFields
public import GibbsMeasure.Specification.KolmogorovZeroOne
public import Mathlib.GroupTheory.Complement

/-!
# The ergodic random fields are dense in `𝓟_Θ` (Georgii Theorem (14.12))

Let `S` be a countable infinite abelian group of sites (Georgii: `ℤ^d`), `Θ` its shift group and
`𝓟_Θ = invariantFields Θ` the shift-invariant random fields (14.1). **Theorem (14.12)**: relative
to the topology of local convergence, `ex 𝓟_Θ` — the ergodic random fields, by (14.5)(a) — is
dense in `𝓟_Θ`.

## Georgii's construction

Fix `μ ∈ 𝓟_Θ`. For a box `Λ(n) = [-n, n]^d` Georgii tiles `ℤ^d` by the translates
`Λ(n) + (2n+1) i`, `i ∈ ℤ^d`, and sets

* `μ_n = ∏_{i ∈ S} σ_{Λ(n) + (2n+1) i}(μ)`, the product over the tiles of the marginals of `μ`;
* `v_n = |Λ(n)|⁻¹ ∑_{j ∈ Λ(n)} θ_j(μ_n)`.

Then `v_n → μ` locally (a local event `A ∈ 𝓕_Δ` has `θ_j⁻¹ A ⊆ 𝓕_{Λ(n)}` for all but a vanishing
fraction of the `j ∈ Λ(n)`, and `μ_n = μ` on `𝓕_{Λ(n)}`), `v_n` is shift-invariant (because
`θ_{(2n+1) i} μ_n = μ_n`), and `v_n` is ergodic: by Proposition (14.9) an invariant event agrees
`v_n`-a.s. with a tail event, and `μ_n` is tail-trivial by Kolmogorov's 0–1 law. No ergodic
theorem is used.

## The formalisation

The only structure the argument consumes is that `Λ(n)` is a **fundamental domain** of the
subgroup `(2n+1) ℤ^d`, and that the fraction of `Λ(n)` within distance `δ` of its complement
vanishes. Both are stated abstractly and the box on `ℤ^d` is an instance:

* The tiling is Mathlib's `AddSubgroup.IsComplement (C : Set S) (H : Set S)` for a finite `C` and
  a subgroup `H`: every site is uniquely `c + h`. `tileRep hCH x ∈ C` and `tileIdx hCH x ∈ H` are
  the two coordinates (`AddSubgroup.IsComplement.equiv`, the additive form of Mathlib's
  `Subgroup.IsComplement.equiv`).
* `tilingEquiv hCH : (H → C → E) ≃ᵐ (S → E)` glues a family of tile configurations, indexed by
  `H`, into a configuration: `(tilingEquiv ζ) (c + h) = ζ h c`.
* `tileProduct hCH μ`, Georgii's `μ_n`, is the image under `tilingEquiv` of the product
  `Measure.infinitePi (fun _ : H ↦ μ.map C.restrict)` of copies of the `C`-marginal of `μ`. Its
  tail-triviality (`tileProduct_mem_trivialOn_tail`) is Kolmogorov's 0–1 law for that product
  (`forall_tail_measure_eq_zero_or_one_infinitePi`), transported along `tilingEquiv`, which is
  measurable from the tail σ-algebra of `H → C → E` to that of `S → E`
  (`measurable_tilingEquiv_tail`).
* `tileAverage hCH μ`, Georgii's `v_n`, is `uniformAverage` of `j ↦ θ_j(μ_n)` over `C`.

## Main results

* `tileAverage_mem_extremePoints_invariantFields` — for a tiling `(C, H)` and `μ ∈ 𝓟_Θ`, the
  averaged tile product `v` is an extreme (= ergodic, (14.5)(a)) shift-invariant random field.
* `tendsto_tileAverage` — along a sequence of tilings `(Cₙ, Hₙ)` satisfying the Følner-type
  condition `|{j ∈ Cₙ : δ - j ∉ Cₙ}| / |Cₙ| → 0` for every `δ`, `vₙ → μ` locally.
* `exists_tendsto_extremePoints_invariantFields_shiftGroup`,
  `closure_setOf_mem_extremePoints_invariantFields_shiftGroup`,
  `dense_setOf_mem_extremePoints_invariantFields_shiftGroup` — **Theorem (14.12)** on any countable
  infinite abelian group admitting such a sequence of tilings, in sequence, closure and `Dense`
  form.
* `isComplement_piFinset_Icc`, `tendsto_card_filter_sub_notMem_piFinset_Icc_div` — the cubes
  `Λ(n) = [-n, n]^d = Fintype.piFinset fun _ ↦ Finset.Icc (-n) n` (`cube d n` in
  `GibbsMeasure/Model/ShiftAverage.lean`, definitionally) tile `ℤ^d` along `(2n+1) ℤ^d` and
  satisfy the Følner condition; hence **Theorem (14.12) on `ℤ^d`** for `d ≥ 1`:
  `exists_tendsto_extremePoints_invariantFields_shiftGroup_int`,
  `closure_setOf_mem_extremePoints_invariantFields_shiftGroup_int`,
  `dense_setOf_mem_extremePoints_invariantFields_shiftGroup_int`.

## Hypotheses

`Countable S` and `Infinite S` enter only through Proposition (14.9)
(`exists_measurableSet_tail_measure_symmDiff_eq_zero_shiftGroup`) and the countability of `Θ`
needed for (14.5)(a); `d ≥ 1` (`NeZero d`) is what makes `ℤ^d` infinite. The state space `E` is an
arbitrary measurable space; Kolmogorov's 0–1 law for `infinitePi` needs no countability of the
index. Commutativity of `S` is used to compose shifts, `θ_i ∘ θ_j = θ_{i + j}`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal Topology symmDiff

noncomputable section

/-! ### Additive complements

The additive form of Mathlib's `Subgroup.IsComplement.equiv` and the lemmas about it that the
tiling needs. (`Subgroup.IsComplement.equiv` is not `to_additive`-tagged in Mathlib.) -/

namespace AddSubgroup.IsComplement

variable {G : Type*} [AddGroup G] {S T : Set G}

/-- The equivalence `G ≃ S × T` whose inverse is `(+) : S × T → G`; additive form of
`Subgroup.IsComplement.equiv`. -/
def equiv (h : IsComplement S T) : G ≃ S × T :=
  (Equiv.ofBijective (fun x : S × T ↦ (x.1 : G) + x.2) h).symm

@[simp] lemma equiv_symm_apply (h : IsComplement S T) (x : S × T) :
    (h.equiv.symm x : G) = x.1 + x.2 := rfl

@[simp] lemma equiv_fst_add_equiv_snd (h : IsComplement S T) (g : G) :
    ((h.equiv g).1 : G) + (h.equiv g).2 = g :=
  (Equiv.ofBijective (fun x : S × T ↦ (x.1 : G) + x.2) h).right_inv g

/-- The decomposition of `s + t` with `s ∈ S`, `t ∈ T` is `(s, t)`. -/
lemma equiv_add (h : IsComplement S T) {s t : G} (hs : s ∈ S) (ht : t ∈ T) :
    h.equiv (s + t) = (⟨s, hs⟩, ⟨t, ht⟩) :=
  ((Equiv.symm_apply_eq h.equiv (x := (⟨s, hs⟩, ⟨t, ht⟩)) (y := s + t)).1 rfl).symm

end AddSubgroup.IsComplement

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- The tail σ-algebra is preserved by every transformation of configuration space: `τ⁻¹ B ∈ 𝓣`
for `B ∈ 𝓣` (Georgii, remark after (5.1), passed to the limit). -/
lemma Transformation.measurableSet_tail_preimage (τ : Transformation S E) {B : Set (S → E)}
    (hB : MeasurableSet[tailSigmaAlgebra S E] B) :
    MeasurableSet[tailSigmaAlgebra S E] (τ.toFun ⁻¹' B) := by
  refine MeasurableSpace.measurableSet_iInf.2 fun Λ ↦ ?_
  have h := τ.measurable_toFun_cylinderEvents ((Λ.map τ.sites.toEmbedding : Finset S) : Set S)ᶜ
    (measurableSet_cylinderEvents_compl_of_measurableSet_tail _ hB)
  have hset : τ.sites ⁻¹' ((Λ.map τ.sites.toEmbedding : Finset S) : Set S)ᶜ = (Λ : Set S)ᶜ := by
    ext i
    simp
  rwa [hset] at h

/-! ### Tilings: a finite fundamental domain of a subgroup -/

section Tiling

variable [AddCommGroup S] {C : Finset S} {H : AddSubgroup S}
  (hCH : AddSubgroup.IsComplement (C : Set S) (H : Set S))

/-- The representative in the fundamental domain `C` of a site `x = c + h`. -/
def tileRep (x : S) : C := ⟨(hCH.equiv x).1, Finset.mem_coe.1 (hCH.equiv x).1.2⟩

/-- The tile index `h ∈ H` of a site `x = c + h`. -/
def tileIdx (x : S) : H := ⟨(hCH.equiv x).2, SetLike.mem_coe.1 (hCH.equiv x).2.2⟩

lemma coe_tileRep_add_coe_tileIdx (x : S) : (tileRep hCH x : S) + (tileIdx hCH x : S) = x :=
  hCH.equiv_fst_add_equiv_snd x

lemma tileRep_add {c k : S} (hc : c ∈ C) (hk : k ∈ H) : tileRep hCH (c + k) = ⟨c, hc⟩ :=
  Subtype.ext (by
    change ((hCH.equiv (c + k)).1 : S) = c
    rw [hCH.equiv_add (Finset.mem_coe.2 hc) (SetLike.mem_coe.2 hk)])

lemma tileIdx_add {c k : S} (hc : c ∈ C) (hk : k ∈ H) : tileIdx hCH (c + k) = ⟨k, hk⟩ :=
  Subtype.ext (by
    change ((hCH.equiv (c + k)).2 : S) = k
    rw [hCH.equiv_add (Finset.mem_coe.2 hc) (SetLike.mem_coe.2 hk)])

lemma tileRep_add_of_mem (x : S) {k : S} (hk : k ∈ H) : tileRep hCH (x + k) = tileRep hCH x := by
  conv_lhs => rw [← coe_tileRep_add_coe_tileIdx hCH x, add_assoc]
  exact tileRep_add hCH (tileRep hCH x).2 (add_mem (tileIdx hCH x).2 hk)

lemma tileIdx_add_of_mem (x : S) {k : S} (hk : k ∈ H) :
    tileIdx hCH (x + k) = tileIdx hCH x + ⟨k, hk⟩ := by
  conv_lhs => rw [← coe_tileRep_add_coe_tileIdx hCH x, add_assoc]
  exact tileIdx_add hCH (tileRep hCH x).2 (add_mem (tileIdx hCH x).2 hk)

lemma tileRep_sub_of_mem (x : S) {k : S} (hk : k ∈ H) : tileRep hCH (x - k) = tileRep hCH x := by
  rw [sub_eq_add_neg]
  exact tileRep_add_of_mem hCH x (neg_mem hk)

lemma tileIdx_sub_of_mem (x : S) {k : S} (hk : k ∈ H) :
    tileIdx hCH (x - k) = tileIdx hCH x - ⟨k, hk⟩ := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact tileIdx_add_of_mem hCH x (neg_mem hk)

lemma coe_tileRep_of_mem {c : S} (hc : c ∈ C) : (tileRep hCH c : S) = c := by
  have h := tileRep_add hCH hc (zero_mem H)
  rw [add_zero] at h
  rw [h]

lemma tileIdx_of_mem {c : S} (hc : c ∈ C) : tileIdx hCH c = 0 := by
  have h := tileIdx_add hCH hc (zero_mem H)
  rw [add_zero] at h
  exact h

/-- The tiles are indexed by `H` and each tile is a copy of `C`: a configuration on `S` is a
family, indexed by `H`, of configurations on `C`, via `(tilingEquiv ζ) (c + h) = ζ h c`. -/
def tilingEquiv : (H → C → E) ≃ᵐ (S → E) where
  toFun ζ i := ζ (tileIdx hCH i) (tileRep hCH i)
  invFun ω h c := ω (c + h)
  left_inv ζ := by
    funext h c
    simp only
    rw [tileIdx_add hCH c.2 h.2, tileRep_add hCH c.2 h.2]
  right_inv ω := by
    funext i
    simp only
    rw [coe_tileRep_add_coe_tileIdx]
  measurable_toFun :=
    measurable_pi_lambda (fun (ζ : H → C → E) (i : S) ↦ ζ (tileIdx hCH i) (tileRep hCH i))
      fun i ↦ (measurable_pi_apply (tileRep hCH i)).comp (measurable_pi_apply (tileIdx hCH i))
  measurable_invFun :=
    measurable_pi_lambda (fun (ω : S → E) (h : H) (c : C) ↦ ω (c + h)) fun h ↦
      measurable_pi_lambda (fun (ω : S → E) (c : C) ↦ ω (c + h)) fun c ↦
        measurable_pi_apply ((c : S) + h)

@[simp] lemma tilingEquiv_apply (ζ : H → C → E) (i : S) :
    tilingEquiv (E := E) hCH ζ i = ζ (tileIdx hCH i) (tileRep hCH i) := rfl

@[simp] lemma tilingEquiv_symm_apply (ω : S → E) (h : H) (c : C) :
    (tilingEquiv (E := E) hCH).symm ω h c = ω (c + h) := rfl

/-- `tilingEquiv` is measurable from the tail σ-algebra of `H → C → E` to the tail σ-algebra of
`S → E`: a tail event of `S → E` is, in tile coordinates, a tail event. Indeed an event in
`𝓕_{(C + Λ')ᶜ}` depends only on the tiles indexed outside `Λ'`. -/
lemma measurable_tilingEquiv_tail :
    Measurable[tailSigmaAlgebra H (C → E), tailSigmaAlgebra S E] (tilingEquiv (E := E) hCH) := by
  classical
  refine Measurable.of_comap_le (le_iInf fun Λ' ↦ ?_)
  set Λ : Finset S := (C ×ˢ Λ').image fun p : S × H ↦ p.1 + (p.2 : S) with hΛ
  refine (MeasurableSpace.comap_mono (iInf_le _ Λ)).trans (Measurable.comap_le ?_)
  let : MeasurableSpace (H → C → E) := cylinderEvents (X := fun _ : H ↦ C → E) ((Λ' : Set H)ᶜ)
  rw [measurable_iff_comap_le, cylinderEvents_eq_comap_domRestrict (X := fun _ : S ↦ E),
    MeasurableSpace.comap_comp]
  refine Measurable.comap_le (measurable_pi_lambda _ fun j ↦ ?_)
  obtain ⟨x, hx⟩ := j
  have hj : tileIdx hCH x ∈ ((Λ' : Set H)ᶜ) := by
    intro hmem
    refine hx ?_
    rw [hΛ, Finset.mem_coe, Finset.mem_image]
    exact ⟨(tileRep hCH x, tileIdx hCH x), Finset.mem_product.2 ⟨(tileRep hCH x).2, hmem⟩,
      coe_tileRep_add_coe_tileIdx hCH x⟩
  change Measurable fun ζ : H → C → E ↦ ζ (tileIdx hCH x) (tileRep hCH x)
  exact (measurable_pi_apply (tileRep hCH x)).comp (measurable_cylinderEvent_apply hj)

/-! ### Georgii's `μ_n`: the product of the tile marginals -/

variable (μ : Measure (S → E))

/-- **Georgii, proof of (14.12): `μ_n = ∏_{i ∈ S} σ_{Λ(n) + (2n+1) i}(μ)`.** The product over the
tiles `C + h`, `h ∈ H`, of the `C`-marginal `σ_C(μ) = μ.map C.restrict` of `μ`, glued by
`tilingEquiv`. -/
def tileProduct : Measure (S → E) :=
  (Measure.infinitePi fun _ : H ↦ μ.map C.restrict).map (tilingEquiv (E := E) hCH)

variable [IsProbabilityMeasure μ]

instance isProbabilityMeasure_map_finsetRestrict (Λ : Finset S) :
    IsProbabilityMeasure (μ.map Λ.restrict) :=
  Measure.isProbabilityMeasure_map (Finset.measurable_restrict Λ).aemeasurable

instance isProbabilityMeasure_tileProduct : IsProbabilityMeasure (tileProduct hCH μ) :=
  Measure.isProbabilityMeasure_map (tilingEquiv hCH).measurable.aemeasurable

/-- `μ_n` agrees with `μ` on the σ-algebra `𝓕_C` of the tile `C` itself: its `C`-marginal is
`σ_C(μ)`. -/
theorem tileProduct_apply_of_measurableSet_cylinderEvents {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (C : Set S)] A) :
    tileProduct hCH μ A = μ A := by
  rw [cylinderEvents_eq_comap_finsetRestrict] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  have hres : C.restrict ∘ ⇑(tilingEquiv (E := E) hCH) = fun ζ : H → C → E ↦ ζ 0 := by
    funext ζ c
    change ζ (tileIdx hCH c) (tileRep hCH c) = ζ 0 c
    rw [tileIdx_of_mem hCH c.2]
    congr
    exact Subtype.ext (coe_tileRep_of_mem hCH c.2)
  rw [tileProduct, MeasurableEquiv.map_apply, ← Set.preimage_comp, hres,
    ← Measure.map_apply (measurable_pi_apply (0 : H)) hB,
    Measure.infinitePi_map_eval (fun _ : H ↦ μ.map C.restrict) 0,
    Measure.map_apply (Finset.measurable_restrict C) hB]

/-- **Georgii, proof of (14.12): `θ_{(2n+1) i}(μ_n) = μ_n`.** `μ_n` is invariant under the shifts
of the tiling subgroup `H`, since these permute the tiles and the tile marginals are all equal. -/
theorem map_shift_tileProduct {k : S} (hk : k ∈ H) :
    (tileProduct hCH μ).map (shift E k).toFun = tileProduct hCH μ := by
  set e : H ≃ H := Equiv.addRight (⟨k, hk⟩ : H) with he
  have hcomp : (shift E k).toFun ∘ ⇑(tilingEquiv (E := E) hCH) =
      ⇑(tilingEquiv (E := E) hCH) ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ : H ↦ C → E) e) := by
    funext ζ i
    simp only [Function.comp_apply, shift_toFun_apply, tilingEquiv_apply]
    rw [tileIdx_sub_of_mem hCH i hk, tileRep_sub_of_mem hCH i hk]
    have hi : tileIdx hCH i = e (tileIdx hCH i - ⟨k, hk⟩) := by
      simp only [he, Equiv.coe_addRight, sub_add_cancel]
    conv_rhs => rw [hi, MeasurableEquiv.piCongrLeft_apply_apply]
  rw [tileProduct, Measure.map_map (shift E k).measurable_toFun (tilingEquiv hCH).measurable,
    hcomp, ← Measure.map_map (tilingEquiv hCH).measurable
      (MeasurableEquiv.piCongrLeft (fun _ : H ↦ C → E) e).measurable]
  congr 1
  exact Measure.infinitePi_map_piCongrLeft (fun _ : H ↦ μ.map C.restrict) e

/-- **Kolmogorov's 0–1 law for `μ_n`** (Georgii, proof of (14.12), via (7.14)): the product of
the tile marginals is trivial on the tail σ-algebra. -/
theorem tileProduct_mem_trivialOn_tail : tileProduct hCH μ ∈ trivialOn (tailSigmaAlgebra S E) := by
  intro B hB
  rw [tileProduct, MeasurableEquiv.map_apply]
  exact forall_tail_measure_eq_zero_or_one_infinitePi (fun _ : H ↦ μ.map C.restrict)
    (measurable_tilingEquiv_tail hCH hB)

/-! ### Georgii's `v_n`: the shift average of `μ_n` over a tile -/

/-- **Georgii, proof of (14.12): `v_n = |Λ(n)|⁻¹ ∑_{j ∈ Λ(n)} θ_j(μ_n)`.** The uniform average over
the tile `C` of the shifted tile products. -/
def tileAverage : Measure (S → E) :=
  uniformAverage (fun j ↦ (tileProduct hCH μ).map (shift E j).toFun) C

omit [IsProbabilityMeasure μ] in
lemma tileAverage_apply (A : Set (S → E)) :
    tileAverage hCH μ A = (C.card : ℝ≥0∞)⁻¹ * ∑ j ∈ C, (tileProduct hCH μ).map (shift E j).toFun A :=
  uniformAverage_apply _ C A

instance isProbabilityMeasure_map_shift (j : S) :
    IsProbabilityMeasure (μ.map (shift E j).toFun) :=
  Measure.isProbabilityMeasure_map (shift E j).measurable_toFun.aemeasurable

include hCH in
/-- A fundamental domain is non-empty. -/
lemma nonempty_of_isComplement : C.Nonempty := Finset.coe_nonempty.1 hCH.nonempty_left

instance isProbabilityMeasure_tileAverage : IsProbabilityMeasure (tileAverage hCH μ) :=
  isProbabilityMeasure_uniformAverage _ (fun _ ↦ inferInstance) (nonempty_of_isComplement hCH)

/-- `tileAverage` as a probability measure, for use inside statements about the topology of local
convergence. -/
noncomputable def tileAveragePM (μ : ProbabilityMeasure (S → E)) : ProbabilityMeasure (S → E) :=
  ⟨tileAverage hCH (μ : Measure (S → E)), isProbabilityMeasure_tileAverage hCH (μ : Measure (S → E))⟩

@[simp] lemma coe_tileAveragePM (μ : ProbabilityMeasure (S → E)) :
    (tileAveragePM hCH μ : Measure (S → E)) = tileAverage hCH (μ : Measure (S → E)) := rfl

/-- Shifting `μ_n` by any site `x` is shifting it by the representative of `x` in the tile `C`,
since the `H`-part of the shift is absorbed by `map_shift_tileProduct`. -/
lemma map_shift_tileProduct_eq_map_shift_tileRep (x : S) :
    (tileProduct hCH μ).map (shift E x).toFun =
      (tileProduct hCH μ).map (shift E (tileRep hCH x : S)).toFun := by
  conv_lhs => rw [← coe_tileRep_add_coe_tileIdx hCH x]
  rw [← shift_toFun_comp_shift_toFun,
    ← Measure.map_map (shift E _).measurable_toFun (shift E _).measurable_toFun,
    map_shift_tileProduct hCH μ (tileIdx hCH x).2]

/-- **Georgii, proof of (14.12): `v_n` is shift-invariant.** A shift by `j'` permutes the family
`θ_j(μ_n)`, `j ∈ C`: `θ_{j'} θ_j μ_n = θ_{j' + j} μ_n = θ_{c} μ_n` where `c ∈ C` is the
representative of `j' + j`, and `j ↦ c` is a bijection of `C`. -/
theorem map_shift_tileAverage (j' : S) :
    (tileAverage hCH μ).map (shift E j').toFun = tileAverage hCH μ := by
  unfold tileAverage uniformAverage
  rw [Measure.map_smul, Measure.map_finset_sum (shift E j').measurable_toFun.aemeasurable]
  congr 1
  calc ∑ j ∈ C, ((tileProduct hCH μ).map (shift E j).toFun).map (shift E j').toFun
      = ∑ j ∈ C, (tileProduct hCH μ).map (shift E (tileRep hCH (j' + j) : S)).toFun :=
        Finset.sum_congr rfl fun j _ ↦ by
          rw [Measure.map_map (shift E j').measurable_toFun (shift E j).measurable_toFun,
            shift_toFun_comp_shift_toFun, map_shift_tileProduct_eq_map_shift_tileRep]
    _ = ∑ j ∈ C, (tileProduct hCH μ).map (shift E j).toFun := by
        refine Finset.sum_nbij' (fun j ↦ (tileRep hCH (j' + j) : S))
          (fun j ↦ (tileRep hCH (j - j') : S)) (fun j _ ↦ (tileRep hCH _).2)
          (fun j _ ↦ (tileRep hCH _).2) (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j _ ↦ rfl)
        · have h1 : (tileRep hCH (j' + j) : S) = j' + j - tileIdx hCH (j' + j) :=
            eq_sub_of_add_eq (coe_tileRep_add_coe_tileIdx hCH _)
          rw [h1, show j' + j - (tileIdx hCH (j' + j) : S) - j' = j - tileIdx hCH (j' + j) by abel,
            tileRep_sub_of_mem hCH _ (tileIdx hCH _).2, coe_tileRep_of_mem hCH hj]
        · have h1 : (tileRep hCH (j - j') : S) = j - j' - tileIdx hCH (j - j') :=
            eq_sub_of_add_eq (coe_tileRep_add_coe_tileIdx hCH _)
          rw [h1, show j' + (j - j' - (tileIdx hCH (j - j') : S)) = j - tileIdx hCH (j - j') by abel,
            tileRep_sub_of_mem hCH _ (tileIdx hCH _).2, coe_tileRep_of_mem hCH hj]

/-- `v_n ∈ 𝓟_Θ`: the averaged tile product is a shift-invariant random field. -/
theorem tileAverage_mem_invariantFields_shiftGroup :
    tileAverage hCH μ ∈ invariantFields (shiftGroup S E) :=
  mem_invariantFields_shiftGroup.2 ⟨inferInstance, fun j ↦
    ⟨(shift E j).measurable_toFun, map_shift_tileAverage hCH μ j⟩⟩

/-- On the invariant σ-algebra `𝓘`, `v_n` and `μ_n` agree: `θ_j(μ_n)(A) = μ_n(A)` for `A ∈ 𝓘`
(Georgii, proof of (14.12)). -/
theorem tileAverage_apply_of_measurableSet_invariantEvents {A : Set (S → E)}
    (hA : MeasurableSet[invariantEvents (shiftGroup S E)] A) :
    tileAverage hCH μ A = tileProduct hCH μ A := by
  obtain ⟨hAm, hAinv⟩ := measurableSet_invariantEvents.1 hA
  rw [tileAverage_apply]
  have hterm : ∀ j ∈ C, (tileProduct hCH μ).map (shift E j).toFun A = tileProduct hCH μ A :=
    fun j _ ↦ by rw [Measure.map_apply (shift E j).measurable_toFun hAm, hAinv _ (shift_mem_shiftGroup j)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast (nonempty_of_isComplement hCH).card_pos.ne')
      (ENNReal.natCast_ne_top _), one_mul]

/-- **Georgii, proof of (14.12): `v_n` is ergodic.** For `A ∈ 𝓘`, Proposition (14.9) provides a
tail event `B` with `v_n(A ∆ B) = 0`; then `μ_n(A ∆ θ_j⁻¹ B) = 0` for `j ∈ C`, so
`v_n(A) = μ_n(A) = μ_n(θ_j⁻¹ B) ∈ {0, 1}` by Kolmogorov's 0–1 law for `μ_n`. -/
theorem tileAverage_mem_trivialOn_invariantEvents [Countable S] [Infinite S]
    (hμ : μ ∈ invariantFields (shiftGroup S E)) :
    tileAverage hCH μ ∈ trivialOn (invariantEvents (shiftGroup S E)) := by
  intro A hA
  obtain ⟨hAm, hAinv⟩ := measurableSet_invariantEvents.1 hA
  obtain ⟨B, hB, hAB⟩ := exists_measurableSet_tail_measure_symmDiff_eq_zero_shiftGroup
    (tileAverage_mem_invariantFields_shiftGroup hCH μ) hA
  obtain ⟨j, hj⟩ := nonempty_of_isComplement hCH
  have hBm : MeasurableSet B :=
    cylinderEvents_le_pi _ (measurableSet_cylinderEvents_compl_of_measurableSet_tail ∅ hB)
  -- `μ_n (θ_j⁻¹ (A ∆ B)) = 0`
  have hterm : tileProduct hCH μ ((shift E j).toFun ⁻¹' (A ∆ B)) = 0 := by
    rw [tileAverage_apply, mul_eq_zero] at hAB
    rcases hAB with h0 | h0
    · exact absurd h0 (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    · have := (Finset.sum_eq_zero_iff.1 h0) j hj
      rwa [Measure.map_apply (shift E j).measurable_toFun (hAm.symmDiff hBm)] at this
  rw [Set.preimage_symmDiff, hAinv _ (shift_mem_shiftGroup j)] at hterm
  rw [tileAverage_apply_of_measurableSet_invariantEvents hCH μ hA,
    measure_congr (measure_symmDiff_eq_zero_iff.1 hterm)]
  exact tileProduct_mem_trivialOn_tail hCH μ _ ((shift E j).measurableSet_tail_preimage hB)

/-- **Georgii, proof of (14.12): `v_n ∈ ex 𝓟_Θ`.** The averaged tile product of a shift-invariant
random field is an extreme shift-invariant random field, by (14.5)(a). -/
theorem tileAverage_mem_extremePoints_invariantFields [Countable S] [Infinite S]
    (hμ : μ ∈ invariantFields (shiftGroup S E)) :
    tileAverage hCH μ ∈ (invariantFields (shiftGroup S E)).extremePoints ℝ≥0∞ :=
  (mem_extremePoints_invariantFields_iff_mem_trivialOn
    (tileAverage_mem_invariantFields_shiftGroup hCH μ)).2
    (tileAverage_mem_trivialOn_invariantEvents hCH μ hμ)

/-- **Georgii, proof of (14.12)**, in the language of Definition (14.6): `v_n` is ergodic. -/
theorem ergodicSMul_tileAverage [Countable S] [Infinite S]
    (hμ : μ ∈ invariantFields (shiftGroup S E)) :
    ErgodicSMul (shiftGroup S E) (S → E) (tileAverage hCH μ) :=
  (ergodicSMul_iff_mem_extremePoints_invariantFields
    (tileAverage_mem_invariantFields_shiftGroup hCH μ).2).2
    (tileAverage_mem_extremePoints_invariantFields hCH μ hμ)

/-! ### The local estimate `|v_n(A) - μ(A)|` -/

/-- **Georgii, proof of (14.12): the estimate
`|v_n(f) - μ(f)| ≤ 2 ‖f‖ |{j ∈ Λ(n) : (Δ - j) ⊄ Λ(n)}| / |Λ(n)|`**, for the indicator of a local
event `A ∈ 𝓕_Δ`. For the `j ∈ C` with `Δ - j ⊆ C` the event `θ_j⁻¹ A` lies in `𝓕_C`, where `μ_n`
and `μ` agree, and `μ (θ_j⁻¹ A) = μ A` by shift-invariance. -/
theorem abs_tileAverage_real_sub_le [DecidableEq S] (hμ : μ ∈ invariantFields (shiftGroup S E))
    {Δ : Finset S} {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    |(tileAverage hCH μ).real A - μ.real A| ≤
      (({j ∈ C | ¬ ∀ δ ∈ Δ, δ - j ∈ C} : Finset S).card : ℝ) / C.card := by
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hC : (0 : ℝ) < C.card := by exact_mod_cast (nonempty_of_isComplement hCH).card_pos
  set m : S → ℝ := fun j ↦ ((tileProduct hCH μ).map (shift E j).toFun).real A with hm
  have hgood : ∀ j, (∀ δ ∈ Δ, δ - j ∈ C) → m j = μ.real A := by
    intro j hj
    rw [hm]
    simp only
    rw [measureReal_def, measureReal_def, Measure.map_apply (shift E j).measurable_toFun hAm]
    have hsub : (shift E j).sites ⁻¹' (Δ : Set S) ⊆ (C : Set S) := by
      intro i hi
      have hi' : i + j ∈ Δ := by simpa [shift] using hi
      simpa using hj _ hi'
    have hpre : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (C : Set S)]
        ((shift E j).toFun ⁻¹' A) :=
      cylinderEvents_mono hsub _ ((shift E j).measurable_toFun_cylinderEvents _ hA)
    rw [tileProduct_apply_of_measurableSet_cylinderEvents hCH μ hpre,
      ((mem_invariantFields_shiftGroup.1 hμ).2 j).measure_preimage hAm.nullMeasurableSet]
  have hbad : ∀ j, |m j - μ.real A| ≤ 1 := by
    intro j
    have h0 : 0 ≤ m j := measureReal_nonneg
    have h1 : m j ≤ 1 := by
      rw [hm]; simp only
      rw [measureReal_def]
      exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have h2 : 0 ≤ μ.real A := measureReal_nonneg
    have h3 : μ.real A ≤ 1 := by
      rw [measureReal_def]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    rw [abs_le]; constructor <;> linarith
  rw [tileAverage, uniformAverage_real_apply _ fun _ ↦ inferInstance]
  have hrw : (C.card : ℝ)⁻¹ * ∑ j ∈ C, m j - μ.real A =
      (C.card : ℝ)⁻¹ * ∑ j ∈ C, (m j - μ.real A) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ hC.ne', one_mul]
  change |(C.card : ℝ)⁻¹ * ∑ j ∈ C, m j - μ.real A| ≤ _
  rw [hrw, abs_mul, abs_of_pos (inv_pos.2 hC), div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (inv_pos.2 hC).le
  rw [← Finset.sum_filter_add_sum_filter_not C (fun j ↦ ¬ ∀ δ ∈ Δ, δ - j ∈ C)]
  have h0 : ∑ j ∈ C with ¬ ¬ ∀ δ ∈ Δ, δ - j ∈ C, |m j - μ.real A| = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [Finset.mem_filter, not_not] at hj
      rw [hgood j hj.2, sub_self, abs_zero]
  rw [h0, add_zero]
  calc ∑ j ∈ C with ¬ ∀ δ ∈ Δ, δ - j ∈ C, |m j - μ.real A|
      ≤ ∑ j ∈ C with ¬ ∀ δ ∈ Δ, δ - j ∈ C, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦ hbad j
    _ = _ := by simp

/-- The exceptional set of the estimate `abs_tileAverage_real_sub_le` is controlled site by site:
`{j ∈ C : Δ - j ⊄ C} ⊆ ⋃_{δ ∈ Δ} {j ∈ C : δ - j ∉ C}`. -/
lemma card_filter_not_forall_sub_mem_le [DecidableEq S] (C Δ : Finset S) :
    ({j ∈ C | ¬ ∀ δ ∈ Δ, δ - j ∈ C} : Finset S).card ≤
      ∑ δ ∈ Δ, ({j ∈ C | δ - j ∉ C} : Finset S).card := by
  refine (Finset.card_le_card ?_).trans Finset.card_biUnion_le
  intro j hj
  rw [Finset.mem_filter, not_forall] at hj
  obtain ⟨hjC, δ, hδ⟩ := hj
  rw [not_imp] at hδ
  exact Finset.mem_biUnion.2 ⟨δ, hδ.1, Finset.mem_filter.2 ⟨hjC, hδ.2⟩⟩

end Tiling

/-! ### Georgii Theorem (14.12) along a sequence of tilings -/

section Sequence

variable [AddCommGroup S] [DecidableEq S] {C : ℕ → Finset S} {H : ℕ → AddSubgroup S}

/-- **Georgii, proof of (14.12): `v_n → μ` in the topology of local convergence.** Along a
sequence of tilings `(Cₙ, Hₙ)` of `S` for which the fraction
`|{j ∈ Cₙ : δ - j ∉ Cₙ}| / |Cₙ|` of the tile near its boundary vanishes for every `δ ∈ S` (a
Følner-type condition on the tiles), the averaged tile products of `μ ∈ 𝓟_Θ` converge locally to
`μ`. -/
theorem tendsto_tileAverage (hCH : ∀ n, AddSubgroup.IsComplement (C n : Set S) (H n : Set S))
    (hfol : ∀ δ : S, Tendsto (fun n ↦ (({j ∈ C n | δ - j ∉ C n} : Finset S).card : ℝ) /
      (C n).card) atTop (𝓝 0))
    {μ : ProbabilityMeasure (S → E)} (hμ : (μ : Measure (S → E)) ∈ invariantFields (shiftGroup S E)) :
    Tendsto (fun n ↦ (WithSetwiseTopology.ofMeasure (tileAveragePM (hCH n) μ) : WithLocalConvergence S E)) atTop
      (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  rw [tendsto_withLocalConvergence_iff]
  intro A hA
  obtain ⟨Δ, hΔ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  change Tendsto (fun n ↦ ((tileAveragePM (hCH n) μ : ProbabilityMeasure (S → E)) : Measure (S → E)) A)
    atTop (𝓝 ((μ : Measure (S → E)) A))
  simp only [coe_tileAveragePM]
  rw [← ENNReal.tendsto_toReal_iff (fun _ ↦ measure_ne_top _ _) (measure_ne_top _ _),
    ← tendsto_sub_nhds_zero_iff]
  have hlim : Tendsto (fun n ↦ ∑ δ ∈ Δ,
      (({j ∈ C n | δ - j ∉ C n} : Finset S).card : ℝ) / (C n).card) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Δ fun δ _ ↦ hfol δ
  refine squeeze_zero_norm' (Eventually.of_forall fun n ↦ ?_) hlim
  rw [Real.norm_eq_abs, ← measureReal_def, ← measureReal_def]
  refine (abs_tileAverage_real_sub_le (hCH n) (μ := (μ : Measure (S → E))) hμ hΔ).trans ?_
  have hC : (0 : ℝ) < (C n).card := by exact_mod_cast (nonempty_of_isComplement (hCH n)).card_pos
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_filter_not_forall_sub_mem_le (C n) Δ)
    hC.le

variable [Countable S] [Infinite S]

/-- **Georgii, Theorem (14.12)**, sequence form: on a countable infinite abelian group of sites
admitting a sequence of tilings `(Cₙ, Hₙ)` with vanishing boundary fractions, every
shift-invariant random field `μ ∈ 𝓟_Θ` is the local limit of a sequence of extreme (ergodic)
shift-invariant random fields — Georgii's `vₙ`. -/
theorem exists_tendsto_extremePoints_invariantFields_shiftGroup
    (hCH : ∀ n, AddSubgroup.IsComplement (C n : Set S) (H n : Set S))
    (hfol : ∀ δ : S, Tendsto (fun n ↦ (({j ∈ C n | δ - j ∉ C n} : Finset S).card : ℝ) /
      (C n).card) atTop (𝓝 0))
    {μ : ProbabilityMeasure (S → E)}
    (hμ : (μ : Measure (S → E)) ∈ invariantFields (shiftGroup S E)) :
    ∃ ν : ℕ → ProbabilityMeasure (S → E),
      (∀ n, (ν n : Measure (S → E)) ∈ (invariantFields (shiftGroup S E)).extremePoints ℝ≥0∞) ∧
        Tendsto (fun n ↦ (WithSetwiseTopology.ofMeasure (ν n) : WithLocalConvergence S E)) atTop
          (𝓝 (WithSetwiseTopology.ofMeasure μ)) :=
  ⟨fun n ↦ tileAveragePM (hCH n) μ,
    fun n ↦ by
      simpa only [coe_tileAveragePM] using
        tileAverage_mem_extremePoints_invariantFields (hCH n) (μ := (μ : Measure (S → E))) hμ,
    tendsto_tileAverage hCH hfol hμ⟩

/-- **Georgii, Theorem (14.12)**, closure form: in the topology of local convergence, the closure
of `ex 𝓟_Θ` is `𝓟_Θ`. (`𝓟_Θ` is closed by the remark after (5.12).) -/
theorem closure_setOf_mem_extremePoints_invariantFields_shiftGroup
    (hCH : ∀ n, AddSubgroup.IsComplement (C n : Set S) (H n : Set S))
    (hfol : ∀ δ : S, Tendsto (fun n ↦ (({j ∈ C n | δ - j ∉ C n} : Finset S).card : ℝ) /
      (C n).card) atTop (𝓝 0)) :
    closure {ν : WithLocalConvergence S E |
        (ν.toMeasure : Measure (S → E)) ∈ (invariantFields (shiftGroup S E)).extremePoints ℝ≥0∞} =
      {ν : WithLocalConvergence S E |
        (ν.toMeasure : Measure (S → E)) ∈ invariantFields (shiftGroup S E)} := by
  refine subset_antisymm (closure_minimal (fun ν hν ↦ hν.1) ?_) fun ν hν ↦ ?_
  · convert isClosed_setOf_forall_measurePreserving (S := S) (E := E)
      (shiftGroup S E : Set (Transformation S E)) using 1
    ext ν
    simp only [mem_setOf_eq, mem_invariantFields_iff, SetLike.mem_coe]
    exact and_iff_right inferInstance
  · obtain ⟨w, hw, hlim⟩ := exists_tendsto_extremePoints_invariantFields_shiftGroup hCH hfol hν
    exact mem_closure_of_tendsto hlim (Eventually.of_forall hw)

/-- **Georgii, Theorem (14.12)**: relative to the topology of local convergence, `𝓟_Θ` has a dense
extreme boundary. -/
theorem dense_setOf_mem_extremePoints_invariantFields_shiftGroup
    (hCH : ∀ n, AddSubgroup.IsComplement (C n : Set S) (H n : Set S))
    (hfol : ∀ δ : S, Tendsto (fun n ↦ (({j ∈ C n | δ - j ∉ C n} : Finset S).card : ℝ) /
      (C n).card) atTop (𝓝 0)) :
    Dense {ν : ↥{ν : WithLocalConvergence S E |
        (ν.toMeasure : Measure (S → E)) ∈ invariantFields (shiftGroup S E)} |
      ((ν : WithLocalConvergence S E).toMeasure : Measure (S → E)) ∈
        (invariantFields (shiftGroup S E)).extremePoints ℝ≥0∞} := by
  rw [Subtype.dense_iff]
  intro ν hν
  rw [← closure_setOf_mem_extremePoints_invariantFields_shiftGroup hCH hfol] at hν
  refine closure_mono ?_ hν
  intro ρ hρ
  exact ⟨⟨ρ, hρ.1⟩, hρ, rfl⟩

end Sequence

/-! ### The cubes `Λ(n) = [-n, n]^d` tile `ℤ^d` along `(2n+1) ℤ^d` -/

section Lattice

variable {d : ℕ}

/-- **Georgii, proof of (14.12): the tiling `ℤ^d = ⋃_i Λ(n) + (2n+1) i`.** The cube
`Λ(n) = [-n, n]^d` is a fundamental domain of the subgroup `(2n+1) ℤ^d`: every `x ∈ ℤ^d` is
uniquely `c + (2n+1) i` with `c ∈ Λ(n)`, namely `c_k = (x_k + n) mod (2n+1) - n`. -/
theorem isComplement_piFinset_Icc (n : ℕ) :
    AddSubgroup.IsComplement
      ((Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n : Finset (Fin d → ℤ)) :
        Set (Fin d → ℤ))
      (AddSubgroup.pi Set.univ fun _ : Fin d ↦ AddSubgroup.zmultiples (2 * (n : ℤ) + 1) :
        Set (Fin d → ℤ)) := by
  refine AddSubgroup.isComplement_iff_existsUnique.2 fun g ↦ ?_
  set L : ℤ := 2 * (n : ℤ) + 1 with hL
  have hL0 : L ≠ 0 := by omega
  have hLpos : 0 < L := by omega
  set r : Fin d → ℤ := fun k ↦ (g k + n) % L - n with hr
  have hr_mem : ∀ k, -(n : ℤ) ≤ r k ∧ r k ≤ n := fun k ↦ by
    have h1 := Int.emod_nonneg (g k + n) hL0
    have h2 := Int.emod_lt_of_pos (g k + n) hLpos
    simp only [hr]
    omega
  have hrC : r ∈ (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n : Finset (Fin d → ℤ)) :=
    Fintype.mem_piFinset.2 fun k ↦ Finset.mem_Icc.2 (hr_mem k)
  have hqH : g - r ∈ AddSubgroup.pi Set.univ fun _ : Fin d ↦ AddSubgroup.zmultiples L := by
    refine (AddSubgroup.mem_pi _).2 fun k _ ↦ Int.mem_zmultiples_iff.2 ⟨(g k + n) / L, ?_⟩
    have := Int.emod_add_mul_ediv (g k + n) L
    simp only [Pi.sub_apply, hr]
    linarith
  refine ⟨(⟨r, Finset.mem_coe.2 hrC⟩, ⟨g - r, SetLike.mem_coe.2 hqH⟩), by simp, ?_⟩
  rintro ⟨⟨c, hc⟩, ⟨h, hh⟩⟩ (heq : c + h = g)
  have hcr : c = r := by
    have hmemC := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hc)
    have hsub : c - r ∈ AddSubgroup.pi Set.univ fun _ : Fin d ↦ AddSubgroup.zmultiples L := by
      have : c - r = (g - r) - h := by rw [← heq]; abel
      rw [this]
      exact sub_mem hqH (SetLike.mem_coe.1 hh)
    funext k
    have hdvd : L ∣ (c - r) k :=
      Int.mem_zmultiples_iff.1 ((AddSubgroup.mem_pi _).1 hsub k (Set.mem_univ k))
    have hck := Finset.mem_Icc.1 (hmemC k)
    have hrk := hr_mem k
    have hlt : ((c - r) k).natAbs < L.natAbs := by
      simp only [Pi.sub_apply]
      omega
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt
    simp only [Pi.sub_apply] at this
    linarith
  subst hcr
  refine Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)
  change h = g - r
  rw [← heq, add_sub_cancel_left]

/-- The cardinality `|Λ(n)| = (2n+1)^d`. -/
lemma card_piFinset_Icc (n : ℕ) :
    (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n : Finset (Fin d → ℤ)).card =
      (2 * n + 1) ^ d := by
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
  congr 1
  omega

/-- The cubes are nested: `Λ(n) ⊆ Λ(n')` for `n ≤ n'`. -/
lemma piFinset_Icc_subset {n n' : ℕ} (h : n ≤ n') :
    (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n : Finset (Fin d → ℤ)) ⊆
      Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n' : ℤ)) n' := by
  intro x hx
  rw [Fintype.mem_piFinset] at hx ⊢
  intro k
  have := Finset.mem_Icc.1 (hx k)
  rw [Finset.mem_Icc]
  omega

/-- `(2(n - m) + 1) / (2n + 1) → 1`. -/
lemma tendsto_two_mul_sub_add_one_div (m : ℕ) :
    Tendsto (fun n : ℕ ↦ (2 * ((n - m : ℕ) : ℝ) + 1) / (2 * n + 1)) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ ↦ (2 * n + 1 : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos).atTop_add tendsto_const_nhds
  have h : Tendsto (fun n : ℕ ↦ (1 : ℝ) - 2 * m / (2 * n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hden)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  have hpos : (2 * n + 1 : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub hn]
  field_simp
  ring

/-- **Georgii, proof of (14.12): the boundary fraction of the cubes vanishes.** For every
`δ ∈ ℤ^d`, `|{j ∈ Λ(n) : δ - j ∉ Λ(n)}| / |Λ(n)| → 0`: the exceptional `j` lie outside
`Λ(n - m)`, `m = ‖δ‖_∞`, and `|Λ(n - m)| / |Λ(n)| = ((2(n-m)+1)/(2n+1))^d → 1`. -/
theorem tendsto_card_filter_sub_notMem_piFinset_Icc_div (δ : Fin d → ℤ) :
    Tendsto (fun n : ℕ ↦
      (({j ∈ (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n : Finset (Fin d → ℤ)) |
          δ - j ∉ (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n :
            Finset (Fin d → ℤ))} : Finset (Fin d → ℤ)).card : ℝ) /
        (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n : Finset (Fin d → ℤ)).card)
      atTop (𝓝 0) := by
  classical
  set Λ : ℕ → Finset (Fin d → ℤ) :=
    fun n ↦ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n with hΛ
  set m : ℕ := Finset.univ.sup fun k ↦ (δ k).natAbs with hm
  have hδ : ∀ k, (δ k).natAbs ≤ m := fun k ↦
    Finset.le_sup (f := fun k ↦ (δ k).natAbs) (Finset.mem_univ k)
  -- the exceptional set lies outside `Λ(n - m)`
  have hsub : ∀ n, m ≤ n → {j ∈ Λ n | δ - j ∉ Λ n} ⊆ Λ n \ Λ (n - m) := by
    intro n hn j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_sdiff]
    refine ⟨hj.1, fun hj' ↦ hj.2 ?_⟩
    rw [hΛ] at hj' ⊢
    simp only at hj' ⊢
    rw [Fintype.mem_piFinset] at hj' ⊢
    intro k
    have h1 := Finset.mem_Icc.1 (hj' k)
    have h2 := hδ k
    rw [Finset.mem_Icc, Pi.sub_apply]
    omega
  have hratio : ∀ n, m ≤ n → ((Λ n \ Λ (n - m)).card : ℝ) / (Λ n).card =
      1 - ((2 * ((n - m : ℕ) : ℝ) + 1) / (2 * n + 1)) ^ d := by
    intro n hn
    have hle := Finset.card_le_card (piFinset_Icc_subset (d := d) (Nat.sub_le n m))
    rw [Finset.card_sdiff_of_subset (piFinset_Icc_subset (Nat.sub_le n m)), Nat.cast_sub hle,
      hΛ]
    simp only
    rw [card_piFinset_Icc, card_piFinset_Icc, div_pow]
    have hpos : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) ^ d := by positivity
    push_cast
    field_simp
  have hlim : Tendsto (fun n : ℕ ↦
      1 - ((2 * ((n - m : ℕ) : ℝ) + 1) / (2 * n + 1)) ^ d) atTop (𝓝 0) := by
    have h1 := (tendsto_two_mul_sub_add_one_div m).pow d
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n ↦ by positivity) ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  rw [← hratio n hn]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card (hsub n hn))
    (Nat.cast_nonneg _)

variable [NeZero d]

/-- **Georgii, Theorem (14.12) on `ℤ^d`**, sequence form: every shift-invariant random field on
`(ℤ^d → E)`, `d ≥ 1`, is the local limit of Georgii's ergodic `vₙ`, built from the cube tiling
`Λ(n) + (2n+1) ℤ^d`. -/
theorem exists_tendsto_extremePoints_invariantFields_shiftGroup_int
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμ : (μ : Measure ((Fin d → ℤ) → E)) ∈ invariantFields (shiftGroup (Fin d → ℤ) E)) :
    ∃ ν : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E),
      (∀ n, (ν n : Measure ((Fin d → ℤ) → E)) ∈
        (invariantFields (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞) ∧
        Tendsto (fun n ↦ (WithSetwiseTopology.ofMeasure (ν n) :
          WithLocalConvergence (Fin d → ℤ) E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) :=
  exists_tendsto_extremePoints_invariantFields_shiftGroup (isComplement_piFinset_Icc (d := d))
    tendsto_card_filter_sub_notMem_piFinset_Icc_div hμ

/-- **Georgii, Theorem (14.12) on `ℤ^d`**, closure form: the closure of `ex 𝓟_Θ` in the topology
of local convergence is `𝓟_Θ`. -/
theorem closure_setOf_mem_extremePoints_invariantFields_shiftGroup_int :
    closure {ν : WithLocalConvergence (Fin d → ℤ) E |
        (ν.toMeasure : Measure ((Fin d → ℤ) → E)) ∈
          (invariantFields (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞} =
      {ν : WithLocalConvergence (Fin d → ℤ) E |
        (ν.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ invariantFields (shiftGroup (Fin d → ℤ) E)} :=
  closure_setOf_mem_extremePoints_invariantFields_shiftGroup (isComplement_piFinset_Icc (d := d))
    tendsto_card_filter_sub_notMem_piFinset_Icc_div

/-- **Georgii, Theorem (14.12) on `ℤ^d`.** Relative to the topology of local convergence,
`𝓟_Θ(Ω, 𝓕)` has a dense extreme boundary. -/
theorem dense_setOf_mem_extremePoints_invariantFields_shiftGroup_int :
    Dense {ν : ↥{ν : WithLocalConvergence (Fin d → ℤ) E |
        (ν.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ invariantFields (shiftGroup (Fin d → ℤ) E)} |
      ((ν : WithLocalConvergence (Fin d → ℤ) E).toMeasure : Measure ((Fin d → ℤ) → E)) ∈
        (invariantFields (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞} :=
  dense_setOf_mem_extremePoints_invariantFields_shiftGroup (isComplement_piFinset_Icc (d := d))
    tendsto_card_filter_sub_notMem_piFinset_Icc_div

end Lattice

end MeasureTheory.GibbsMeasure

end
