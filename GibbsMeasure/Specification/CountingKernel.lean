/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification
public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix

/-!
# Cylinders and the counting-measure reference kernel

For a countable state space `E` with the discrete σ-algebra and counting measure as a priori
measure, the reference kernel `λ_Λ(·|η) = Specification.sigmaFiniteLambdaFun Measure.count Λ η` of
Georgii's Notation (1.26) is the sum of the Dirac measures at the configurations agreeing with `η`
off the finite volume `Λ`. This file collects the resulting elementary calculus, on an arbitrary
site space `S`:

* `cyl Λ η`: the cylinder `{σ : σ_Λ = η_Λ}`, Mathlib's `cylinder Λ` over a singleton, together
  with `cylindersIn V`, the π-system of cylinders over finite subsets of `V`, and
  `cylinderEvents_eq_generateFrom_cylindersIn`.
* `ext_of_forall_map_restrict`, `ext_of_forall_exists_cyl_eq`: a finite measure on `S → E` is
  determined by its finite-dimensional marginals, hence by its cylinder probabilities along a
  cofinal family of volumes.
* `lintegral_lambdaCount` and its `insert`/`singleton`/`union`/`prod` forms: integrating against
  `λ_Λ(·|η)` is summing over the configurations on `Λ`.
* `map_restrict_withDensity_insert`, `map_restrict_withDensity_union`: marginalising a density
  integrates out the coordinates that are dropped.
* `sigmaFiniteLambdaZ_count_ne_zero`, `sigmaFiniteLambdaZ_count_ne_top_of_finite`: the partition
  function of a pre-modification for counting measure.

These are the general-`S` statements behind Georgii's Chapters 3, 11 (`S = ℤ`) and 12 (`S` the
vertex set of a tree).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] [Countable E]
  [MeasurableSingletonClass E]

local notation "λ₀" => Specification.sigmaFiniteLambdaFun (S := S) (E := E) Measure.count


section Cyl

/-- The cylinder `{σ_Λ = η_Λ}`: Mathlib's `cylinder Λ` over the singleton `{η_Λ}`. -/
abbrev cyl (Λ : Finset S) (η : S → E) : Set (S → E) := cylinder Λ {Λ.restrict η}

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma mem_cyl {Λ : Finset S} {η σ : S → E} : σ ∈ cyl Λ η ↔ ∀ k ∈ Λ, σ k = η k := by
  simp only [cyl, mem_cylinder, Set.mem_singleton_iff, funext_iff]
  exact ⟨fun h k hk ↦ h ⟨k, hk⟩, fun h k ↦ h k.1 k.2⟩

omit [DecidableEq S] [Countable E] in
lemma measurableSet_cyl (Λ : Finset S) (η : S → E) : MeasurableSet (cyl Λ η) :=
  MeasurableSet.cylinder _ (measurableSet_singleton _)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_congr {Λ : Finset S} {η η' : S → E} (h : ∀ k ∈ Λ, η k = η' k) :
    cyl Λ η = cyl Λ η' := by
  ext σ
  simp only [mem_cyl]
  exact ⟨fun h' k hk ↦ (h' k hk).trans (h k hk), fun h' k hk ↦ (h' k hk).trans (h k hk).symm⟩

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_update_of_notMem {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E) (y : E) :
    cyl Λ (Function.update η j y) = cyl Λ η :=
  cyl_congr fun _ hk ↦ Function.update_of_ne (ne_of_mem_of_not_mem hk hj) _ _

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_mono {Λ Δ : Finset S} (h : Λ ⊆ Δ) (η : S → E) : cyl Δ η ⊆ cyl Λ η := fun _ hσ ↦
  mem_cyl.2 fun k hk ↦ mem_cyl.1 hσ k (h hk)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma mem_cyl_self (Λ : Finset S) (η : S → E) : η ∈ cyl Λ η := mem_cyl.2 fun _ _ ↦ rfl

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_insert_eq_inter (Λ : Finset S) (j : S) (η : S → E) :
    cyl (insert j Λ) η = {σ | σ j = η j} ∩ cyl Λ η := by
  ext σ
  simp only [mem_cyl, Finset.mem_insert, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_eq_or_imp]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- A cylinder over `Λ` is the disjoint union of the cylinders over `Λ ∪ {j}`, `j ∉ Λ`, obtained
by filling in the free coordinate `j`. -/
lemma cyl_eq_iUnion_insert {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E) :
    cyl Λ η = ⋃ y : E, cyl (insert j Λ) (Function.update η j y) := by
  ext σ
  simp only [Set.mem_iUnion, cyl_insert_eq_inter, cyl_update_of_notMem hj, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Function.update_self]
  exact ⟨fun h ↦ ⟨σ j, rfl, h⟩, fun ⟨_, _, h⟩ ↦ h⟩

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pairwise_disjoint_cyl_insert_update (Λ : Finset S) (j : S) (η : S → E) :
    Pairwise (Function.onFun Disjoint fun y : E ↦ cyl (insert j Λ) (Function.update η j y)) := by
  intro y y' hyy'
  rw [Function.onFun, Set.disjoint_left]
  intro σ hσ hσ'
  have h1 := mem_cyl.1 hσ j (Finset.mem_insert_self j Λ)
  have h2 := mem_cyl.1 hσ' j (Finset.mem_insert_self j Λ)
  rw [Function.update_self] at h1 h2
  exact hyy' (h1.symm.trans h2)

/-- The measure of a cylinder is the sum over a free coordinate of the measures of the finer
cylinders. -/
lemma measure_cyl_eq_tsum_insert (μ : Measure (S → E)) {Λ : Finset S} {j : S} (hj : j ∉ Λ)
    (η : S → E) :
    μ (cyl Λ η) = ∑' y : E, μ (cyl (insert j Λ) (Function.update η j y)) := by
  rw [cyl_eq_iUnion_insert hj η, measure_iUnion (pairwise_disjoint_cyl_insert_update Λ j η)
    fun _ ↦ measurableSet_cyl _ _]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma preimage_singleton_eq_cyl (i : S) (x : E) (η : S → E) :
    (fun σ : S → E ↦ σ i) ⁻¹' {x} = cyl {i} (Function.update η i x) := by
  ext σ
  rw [Set.mem_preimage, Set.mem_singleton_iff, mem_cyl]
  simp

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma preimage_inter_preimage_eq_cyl {i j : S} (hij : i ≠ j) (x y : E) (η : S → E) :
    (fun σ : S → E ↦ σ i) ⁻¹' {x} ∩ (fun σ ↦ σ j) ⁻¹' {y}
      = cyl {i, j} (Function.update (Function.update η i x) j y) := by
  ext σ
  simp only [mem_cyl, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Function.update_of_ne hij,
    Function.update_self]

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_empty (η : S → E) : cyl (∅ : Finset S) η = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_cyl.2 fun _ h ↦ absurd h (Finset.notMem_empty _)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma restrict_preimage_singleton (Λ : Finset S) (η : S → E) :
    Λ.restrict ⁻¹' ({Λ.restrict η} : Set (Λ → E)) = cyl Λ η := rfl

omit [DecidableEq S] [Countable E] in
/-- A cylinder over `Δ ⊆ V` is measurable for the cylinder σ-algebra of `V`. -/
lemma measurableSet_cylinderEvents_cyl {V : Set S} {Δ : Finset S} (h : (Δ : Set S) ⊆ V)
    (ζ : S → E) : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) V] (cyl Δ ζ) := by
  have : cyl Δ ζ = ⋂ k ∈ Δ, (fun σ : S → E ↦ σ k) ⁻¹' {ζ k} := by
    ext σ
    rw [mem_cyl]
    simp
  rw [this]
  exact MeasurableSet.biInter Δ.countable_toSet fun k hk ↦
    measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (h (Finset.mem_coe.2 hk))
      (measurableSet_singleton _)

omit [DecidableEq S] in
lemma measurable_measure_cyl (μ : Measure (S → E)) (Δ : Finset S) :
    Measurable fun ξ : S → E ↦ μ (cyl Δ ξ) := by
  have : (fun ξ : S → E ↦ μ (cyl Δ ξ)) = (fun x : Δ → E ↦ μ (Δ.restrict ⁻¹' {x})) ∘ Δ.restrict :=
    rfl
  rw [this]
  exact (measurable_of_countable _).comp (Finset.measurable_restrict (X := fun _ : S ↦ E) Δ)

/-- The cylinders over finite subsets of `V`: a π-system generating `cylinderEvents V`. -/
def cylindersIn (V : Set S) : Set (Set (S → E)) :=
  {A | ∃ (W : Finset S) (ω : S → E), (W : Set S) ⊆ V ∧ A = cyl W ω}

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma isPiSystem_cylindersIn (V : Set S) : IsPiSystem (cylindersIn (E := E) V) := by
  classical
  rintro _ ⟨W₁, ω₁, hW₁, rfl⟩ _ ⟨W₂, ω₂, hW₂, rfl⟩ ⟨σ, hσ₁, hσ₂⟩
  refine ⟨W₁ ∪ W₂, σ, by rw [Finset.coe_union]; exact Set.union_subset hW₁ hW₂, ?_⟩
  ext τ
  simp only [Set.mem_inter_iff, mem_cyl, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ k hk
    rcases hk with hk | hk
    · exact (h1 k hk).trans (mem_cyl.1 hσ₁ k hk).symm
    · exact (h2 k hk).trans (mem_cyl.1 hσ₂ k hk).symm
  · intro h
    exact ⟨fun k hk ↦ (h k (Or.inl hk)).trans (mem_cyl.1 hσ₁ k hk),
      fun k hk ↦ (h k (Or.inr hk)).trans (mem_cyl.1 hσ₂ k hk)⟩

omit [DecidableEq S] in
/-- For a countable state space, `cylinderEvents V` is generated by the cylinders over finite
subsets of `V`. -/
lemma cylinderEvents_eq_generateFrom_cylindersIn [Nonempty E] (V : Set S) :
    cylinderEvents (X := fun _ : S ↦ E) V = MeasurableSpace.generateFrom (cylindersIn V) := by
  classical
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine iSup₂_le fun k hk s hs ↦ ?_
    obtain ⟨t, -, rfl⟩ := hs
    have : (fun σ : S → E ↦ σ k) ⁻¹' t
        = ⋃ x ∈ t, cyl {k} (Function.update (fun _ ↦ Classical.arbitrary E) k x) := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
      constructor
      · intro h
        exact ⟨σ k, h, mem_cyl.2 fun m hm ↦ by
          rw [Finset.mem_singleton.1 hm, Function.update_self]⟩
      · rintro ⟨x, hx, h⟩
        have := mem_cyl.1 h k (Finset.mem_singleton_self k)
        rw [Function.update_self] at this
        rw [this]
        exact hx
    rw [this]
    exact MeasurableSet.biUnion t.to_countable fun x _ ↦
      MeasurableSpace.measurableSet_generateFrom ⟨{k}, _, by simpa using hk, rfl⟩
  · rintro _ ⟨W, ω, hW, rfl⟩
    exact measurableSet_cylinderEvents_cyl hW ω

end Cyl

/-! ### Marginals -/

section Marginals

omit [DecidableEq S] [Countable E] [MeasurableSingletonClass E] in
lemma map_restrict_eq_of_subset {μ ν : Measure (S → E)} {Λ Δ : Finset S} (h : Λ ⊆ Δ)
    (hμν : μ.map Δ.restrict = ν.map Δ.restrict) : μ.map Λ.restrict = ν.map Λ.restrict := by
  rw [← Finset.restrict₂_comp_restrict (π := fun _ : S ↦ E) h,
    ← Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : S ↦ E) h)
      (Finset.measurable_restrict (X := fun _ : S ↦ E) Δ),
    ← Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : S ↦ E) h)
      (Finset.measurable_restrict (X := fun _ : S ↦ E) Δ), hμν]

omit [DecidableEq S] in
/-- Two measures with the same cylinder probabilities over `Λ` have the same marginal on `Λ`. -/
lemma map_restrict_eq_of_forall_cyl [Nonempty E] {μ ν : Measure (S → E)} (Λ : Finset S)
    (h : ∀ η, μ (cyl Λ η) = ν (cyl Λ η)) : μ.map Λ.restrict = ν.map Λ.restrict := by
  refine Measure.ext_of_singleton fun x ↦ ?_
  rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ)
    (measurableSet_singleton _), Measure.map_apply
    (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ) (measurableSet_singleton _)]
  have hx : x = Λ.restrict (juxt (Λ : Set S) (Classical.arbitrary (S → E)) x) := by
    · funext k
      exact (juxt_apply_of_mem k.2 x).symm
  rw [hx, restrict_preimage_singleton]
  exact h _

omit [DecidableEq S] [Countable E] [MeasurableSingletonClass E] in
/-- A finite measure is determined by its finite-dimensional marginals (`IsProjectiveLimit.unique`
for the family of its own marginals). -/
lemma ext_of_forall_map_restrict {μ ν : Measure (S → E)} [IsFiniteMeasure μ]
    (h : ∀ Λ : Finset S, μ.map Λ.restrict = ν.map Λ.restrict) : μ = ν :=
  IsProjectiveLimit.unique (P := fun Λ : Finset S ↦ μ.map Λ.restrict) (fun _ ↦ rfl)
    fun Λ ↦ (h Λ).symm

omit [DecidableEq S] in
/-- Two finite measures agreeing on the cylinders over a cofinal family of volumes are equal. -/
lemma ext_of_forall_exists_cyl_eq [Nonempty E] {μ ν : Measure (S → E)} [IsFiniteMeasure μ]
    (h : ∀ Λ : Finset S, ∃ H : Finset S, Λ ⊆ H ∧ ∀ η, μ (cyl H η) = ν (cyl H η)) : μ = ν :=
  ext_of_forall_map_restrict fun Λ ↦ by
    obtain ⟨H, hΛH, hH⟩ := h Λ
    exact map_restrict_eq_of_subset hΛH (map_restrict_eq_of_forall_cyl H hH)

end Marginals

/-! ### The counting reference kernel `λ_Λ` -/

section LambdaCount

omit [DecidableEq S] in
lemma measurable_pair (g : E → E → ℝ≥0∞) (k l : S) :
    Measurable fun σ : S → E ↦ g (σ k) (σ l) :=
  (measurable_of_countable fun p : E × E ↦ g p.1 p.2).comp
    (f := fun σ : S → E ↦ (σ k, σ l)) ((measurable_pi_apply k).prodMk (measurable_pi_apply l))

omit [DecidableEq S] in
lemma measurable_coord (g : E → ℝ≥0∞) (k : S) : Measurable fun σ : S → E ↦ g (σ k) :=
  (measurable_of_countable g).comp (measurable_pi_apply k)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma juxt_restrict (Λ : Finset S) (η : S → E) : juxt (Λ : Set S) η (Λ.restrict η) = η := by
  funext k
  by_cases hk : k ∈ Λ
  · rw [juxt_apply_of_mem (Finset.mem_coe.2 hk)]; rfl
  · rw [juxt_apply_of_not_mem (by simpa using hk)]

/-- Splitting off the coordinate `j` of a product over `insert j Λ`. -/
def insertPiEquiv (Λ : Finset S) (j : S) (hj : j ∉ Λ) :
    (Π _k : (insert j Λ : Finset S), E) ≃ (Π _k : Λ, E) × E where
  toFun x := (fun k ↦ x ⟨↑k, Finset.mem_insert_of_mem k.2⟩, x ⟨j, Finset.mem_insert_self j Λ⟩)
  invFun p := fun k ↦ if h : (k : S) ∈ Λ then p.1 ⟨↑k, h⟩ else p.2
  left_inv x := by
    funext k
    obtain ⟨k, hk⟩ := k
    by_cases h : k ∈ Λ
    · simp only [dite_eq_left h]
    · have hkj : k = j := by
        rcases Finset.mem_insert.1 hk with h' | h'
        · exact h'
        · exact absurd h' h
      subst hkj
      simp only [dite_eq_right h]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext k
      exact dite_eq_left k.2
    · exact dite_eq_right hj

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma juxt_insertPiEquiv_symm {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E) (x : Λ → E)
    (y : E) :
    juxt ((insert j Λ : Finset S) : Set S) η ((insertPiEquiv Λ j hj).symm (x, y))
      = Function.update (juxt (Λ : Set S) η x) j y := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, juxt_apply_of_mem (Finset.mem_coe.2 (Finset.mem_insert_self i Λ))]
    exact dite_eq_right hj
  · rw [Function.update_of_ne hij]
    by_cases hiΛ : i ∈ Λ
    · rw [juxt_apply_of_mem (Finset.mem_coe.2 (Finset.mem_insert_of_mem hiΛ)),
        juxt_apply_of_mem (Finset.mem_coe.2 hiΛ)]
      exact dite_eq_left hiΛ
    · rw [juxt_apply_of_not_mem (show i ∉ ((insert j Λ : Finset S) : Set S) by simp [hij, hiΛ]),
        juxt_apply_of_not_mem (show i ∉ (Λ : Set S) by simpa using hiΛ)]

omit [DecidableEq S] in
/-- For counting measure, integrating against `λ_Λ(·|η)` sums over the configurations on `Λ`. -/
lemma lintegral_lambdaCount (Λ : Finset S) (η : S → E) {F : (S → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ Λ η) = ∑' x : Λ → E, F (juxt (Λ : Set S) η x) := by
  rw [Specification.sigmaFiniteLambdaFun_apply_eq_map, lintegral_map hF Measurable.juxt]
  erw [Measure.pi_count (X := fun _ : ((Λ : Set S) : Type _) ↦ E)]
  rw [lintegral_count]
  rfl

omit [DecidableEq S] in
lemma lintegral_lambdaCount_congr (Λ : Finset S) (η : S → E) {F G : (S → E) → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (h : ∀ ζ, (∀ k ∉ Λ, ζ k = η k) → F ζ = G ζ) :
    ∫⁻ ζ, F ζ ∂(λ₀ Λ η) = ∫⁻ ζ, G ζ ∂(λ₀ Λ η) := by
  rw [lintegral_lambdaCount Λ η hF, lintegral_lambdaCount Λ η hG]
  exact tsum_congr fun x ↦ h _ (juxt_agree_on_compl Λ η x)

omit [DecidableEq S] in
lemma lintegral_lambdaCount_empty (η : S → E) {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ ∅ η) = F η := by
  rw [lintegral_lambdaCount ∅ η hF]
  have : IsEmpty ((∅ : Finset S) : Type _) := ⟨fun k ↦ absurd k.2 (Finset.notMem_empty _)⟩
  have hj : ∀ x : ((∅ : Finset S) : Type _) → E, juxt ((∅ : Finset S) : Set S) η x = η :=
    fun x ↦ funext fun k ↦ juxt_apply_of_not_mem (show k ∉ ((∅ : Finset S) : Set S) by simp) x
  simp_rw [hj]
  rw [tsum_fintype, Fintype.sum_unique]

omit [Countable E] [MeasurableSingletonClass E] in
lemma measurable_update_left' (j : S) (y : E) :
    Measurable fun σ : S → E ↦ Function.update σ j y :=
  measurable_update_left

/-- Integrating against `λ_{Λ ∪ {j}}(·|η)` for counting measure: sum over the free coordinate
`j`, then integrate against `λ_Λ(·|η)`. -/
lemma lintegral_lambdaCount_insert {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E)
    {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ (insert j Λ) η) = ∫⁻ ζ, ∑' y, F (Function.update ζ j y) ∂(λ₀ Λ η) := by
  have hG : Measurable fun ζ : S → E ↦ ∑' y, F (Function.update ζ j y) :=
    Measurable.tsum fun y ↦ hF.comp (measurable_update_left' j y)
  rw [lintegral_lambdaCount _ _ hF, lintegral_lambdaCount _ _ hG]
  calc ∑' x : ↥(insert j Λ) → E, F (juxt ((insert j Λ : Finset S) : Set S) η x)
      = ∑' p : (Λ → E) × E, F (juxt ((insert j Λ : Finset S) : Set S) η
          ((insertPiEquiv Λ j hj).symm p)) := (Equiv.tsum_eq _ _).symm
    _ = ∑' (x : Λ → E) (y : E), F (juxt ((insert j Λ : Finset S) : Set S) η
          ((insertPiEquiv Λ j hj).symm (x, y))) :=
        ENNReal.tsum_prod (f := fun x y ↦ F (juxt ((insert j Λ : Finset S) : Set S) η
          ((insertPiEquiv Λ j hj).symm (x, y))))
    _ = ∑' (x : Λ → E) (y : E), F (Function.update (juxt (Λ : Set S) η x) j y) := by
        simp_rw [juxt_insertPiEquiv_symm hj η]

lemma lintegral_lambdaCount_singleton (j : S) (η : S → E) {F : (S → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ {j} η) = ∑' y, F (Function.update η j y) := by
  rw [← Finset.insert_empty, lintegral_lambdaCount_insert (Finset.notMem_empty j) η hF,
    lintegral_lambdaCount_empty (F := fun ζ ↦ ∑' y, F (Function.update ζ j y)) _
      (Measurable.tsum fun y ↦ hF.comp (measurable_update_left' j y))]

omit [DecidableEq S] in
/-- Integrating over the cylinder `{σ_Λ = σ_Λ}` against `λ_Λ(·|η)` evaluates at the configuration
`σ_Λ η_{Λᶜ}`. -/
lemma setLIntegral_lambdaCount_cyl' (Λ : Finset S) (η σ : S → E) {F : (S → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ζ in cyl Λ σ, F ζ ∂(λ₀ Λ η) = F (juxt (Λ : Set S) η (Λ.restrict σ)) := by
  rw [← lintegral_indicator (measurableSet_cyl Λ σ), lintegral_lambdaCount Λ η
    (hF.indicator (measurableSet_cyl Λ σ))]
  rw [tsum_eq_single (Λ.restrict σ) fun x hx ↦ ?_]
  · exact Set.indicator_of_mem (show juxt (Λ : Set S) η (Λ.restrict σ) ∈ cyl Λ σ from
      mem_cyl.2 fun k hk ↦ juxt_apply_of_mem (Finset.mem_coe.2 hk) _) _
  · refine Set.indicator_of_notMem (fun h ↦ hx (funext fun k ↦ ?_)) _
    have := mem_cyl.1 h k k.2
    rwa [juxt_apply_of_mem (Finset.mem_coe.2 k.2)] at this

omit [DecidableEq S] in
lemma setLIntegral_lambdaCount_cyl (Λ : Finset S) (η : S → E) {F : (S → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ζ in cyl Λ η, F ζ ∂(λ₀ Λ η) = F η := by
  rw [setLIntegral_lambdaCount_cyl' Λ η η hF, juxt_restrict]

/-- Integrating over the cylinder `{σ_H = ζ_H}`, `Λ ⊆ H`, against `λ_Λ(·|ω)`: the value at
`ζ_Λ ω_{Λᶜ}` if `ω` agrees with `ζ` on `H \ Λ`, and `0` otherwise. -/
lemma setLIntegral_lambdaCount_cyl_of_subset {Λ H : Finset S} (hΛH : Λ ⊆ H) (ω ζ : S → E)
    {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ξ in cyl H ζ, F ξ ∂(λ₀ Λ ω)
      = (cyl (H \ Λ) ζ).indicator (fun ω ↦ F (juxt (Λ : Set S) ω (Λ.restrict ζ))) ω := by
  rw [← lintegral_indicator (measurableSet_cyl H ζ),
    lintegral_lambdaCount Λ ω (hF.indicator (measurableSet_cyl H ζ))]
  by_cases hω : ω ∈ cyl (H \ Λ) ζ
  · rw [Set.indicator_of_mem hω, tsum_eq_single (Λ.restrict ζ) fun x hx ↦ ?_]
    · refine Set.indicator_of_mem (mem_cyl.2 fun k hk ↦ ?_) _
      by_cases hkΛ : k ∈ Λ
      · rw [juxt_apply_of_mem (Finset.mem_coe.2 hkΛ)]; rfl
      · rw [juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by simpa using hkΛ)]
        exact mem_cyl.1 hω k (Finset.mem_sdiff.2 ⟨hk, hkΛ⟩)
    · refine Set.indicator_of_notMem (fun h ↦ hx (funext fun k ↦ ?_)) _
      have := mem_cyl.1 h k (hΛH k.2)
      rwa [juxt_apply_of_mem (Finset.mem_coe.2 k.2)] at this
  · rw [Set.indicator_of_notMem hω]
    refine ENNReal.tsum_eq_zero.2 fun x ↦ Set.indicator_of_notMem (fun h ↦ hω (mem_cyl.2
      fun k hk ↦ ?_)) _
    have hk' := Finset.mem_sdiff.1 hk
    have := mem_cyl.1 h k hk'.1
    rwa [juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by simpa using hk'.2)] at this

omit [DecidableEq S] in
/-- The partition function of a pre-modification for counting measure dominates the weight of the
boundary condition itself. -/
lemma sigmaFiniteLambdaZ_count_ne_zero {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hρ : Specification.IsPremodifier ρ) {Λ : Finset S} {ω : S → E} (h : ρ Λ ω ≠ 0) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count ρ Λ ω ≠ 0 := by
  rw [Specification.sigmaFiniteLambdaZ, lintegral_lambdaCount Λ ω (hρ.measurable Λ)]
  refine ne_of_gt ((pos_iff_ne_zero.2 h).trans_le ?_)
  have := ENNReal.le_tsum (f := fun x : Λ → E ↦ ρ Λ (juxt (Λ : Set S) ω x)) (Λ.restrict ω)
  rwa [juxt_restrict] at this

omit [DecidableEq S] in
/-- On a finite state space the partition functions of a finite weight are finite. -/
lemma sigmaFiniteLambdaZ_count_ne_top_of_finite [Finite E] {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hρ : Specification.IsPremodifier ρ) (htop : ∀ Λ ω, ρ Λ ω ≠ ⊤) (Λ : Finset S) (ω : S → E) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count ρ Λ ω ≠ ⊤ := by
  rw [Specification.sigmaFiniteLambdaZ, lintegral_lambdaCount Λ ω (hρ.measurable Λ)]
  have : Fintype (Λ → E) := Fintype.ofFinite _
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun _ _ ↦ htop _ _

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma restrict_update_of_notMem {Λ : Finset S} {j : S} (h : j ∉ Λ) (σ : S → E) (z : E) :
    Λ.restrict (Function.update σ j z) = Λ.restrict σ := by
  funext k
  exact Function.update_of_ne (ne_of_mem_of_not_mem k.2 h) z σ

/-- Marginalising a density on `Λ ∪ {j}` to `Λ` sums the free coordinate. -/
lemma map_restrict_withDensity_insert {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E)
    {w w' : (S → E) → ℝ≥0∞} (hw : Measurable w)
    (h : ∀ ζ, ∑' y, w (Function.update ζ j y) = w' ζ) :
    ((λ₀ (insert j Λ) η).withDensity w).map Λ.restrict
      = ((λ₀ Λ η).withDensity w').map Λ.restrict := by
  ext A hA
  have hA' : MeasurableSet (Λ.restrict ⁻¹' A : Set (S → E)) :=
    Finset.measurable_restrict (X := fun _ : S ↦ E) Λ hA
  rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ) hA,
    Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ) hA,
    withDensity_apply _ hA', withDensity_apply _ hA', ← lintegral_indicator hA',
    ← lintegral_indicator hA', lintegral_lambdaCount_insert hj η (hw.indicator hA')]
  refine lintegral_congr fun ζ ↦ ?_
  by_cases hζ : ζ ∈ Λ.restrict ⁻¹' A
  · have hmem : ∀ y, Function.update ζ j y ∈ Λ.restrict ⁻¹' A := fun y ↦ by
      change Λ.restrict (Function.update ζ j y) ∈ A
      rwa [restrict_update_of_notMem hj]
    simp_rw [Set.indicator_of_mem (hmem _), Set.indicator_of_mem hζ, h]
  · have hmem : ∀ y, Function.update ζ j y ∉ Λ.restrict ⁻¹' A := fun y hy ↦ by
      change Λ.restrict (Function.update ζ j y) ∈ A at hy
      rw [restrict_update_of_notMem hj] at hy
      exact hζ hy
    simp_rw [Set.indicator_of_notMem (hmem _), Set.indicator_of_notMem hζ, tsum_zero]

/-- Integrating against `λ_{Λ₁ ∪ Λ₂}` for disjoint volumes: integrate over `Λ₂`, then over `Λ₁`
(counting measure; Georgii's Notation (1.26) `λ_{Λ₁} λ_{Λ₂} = λ_{Λ₁ ∪ Λ₂}`). -/
lemma lintegral_lambdaCount_union {Λ₁ Λ₂ : Finset S} (h : Disjoint Λ₁ Λ₂) (η : S → E)
    {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ (Λ₁ ∪ Λ₂) η) = ∫⁻ ζ, ∫⁻ ξ, F ξ ∂(λ₀ Λ₂ ζ) ∂(λ₀ Λ₁ η) := by
  induction Λ₂ using Finset.induction_on generalizing F with
  | empty =>
    simp_rw [lintegral_lambdaCount_empty _ hF]
    rw [Finset.union_empty]
  | insert j Λ₂ hj ih =>
    rw [Finset.disjoint_insert_right] at h
    have hG : Measurable fun ζ : S → E ↦ ∑' y, F (Function.update ζ j y) :=
      Measurable.tsum fun y ↦ hF.comp (measurable_update_left' j y)
    rw [Finset.union_insert, lintegral_lambdaCount_insert (by simp [h.1, hj]) η hF, ih h.2 hG]
    exact lintegral_congr fun ζ ↦ (lintegral_lambdaCount_insert hj ζ hF).symm

omit [DecidableEq S] in
lemma measurable_lintegral_lambdaCount (Λ : Finset S) {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun ζ : S → E ↦ ∫⁻ ξ, F ξ ∂(λ₀ Λ ζ) :=
  hF.lintegral_kernel.mono cylinderEvents_le_pi le_rfl

omit [DecidableEq S] in
/-- Integrating a product of one-site functions over `λ_V` factorises. -/
lemma lintegral_lambdaCount_prod (V : Finset S) (ζ : S → E) (f : S → E → ℝ≥0∞) :
    ∫⁻ ξ, ∏ k ∈ V, f k (ξ k) ∂(λ₀ V ζ) = ∏ k ∈ V, ∑' y, f k y := by
  classical
  induction V using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [lintegral_lambdaCount_empty _ measurable_const]
  | insert j V hj ih =>
    have hF : Measurable fun ξ : S → E ↦ ∏ k ∈ insert j V, f k (ξ k) :=
      Finset.measurable_prod _ fun k _ ↦ measurable_coord (f k) k
    rw [lintegral_lambdaCount_insert hj ζ hF, Finset.prod_insert hj, ← ih,
      ← lintegral_const_mul _ (Finset.measurable_prod _ fun k _ ↦ measurable_coord (f k) k)]
    refine lintegral_congr fun ξ ↦ ?_
    simp_rw [Finset.prod_insert hj, Function.update_self]
    have hprod : ∀ y, ∏ k ∈ V, f k (Function.update ξ j y k) = ∏ k ∈ V, f k (ξ k) := fun y ↦
      Finset.prod_congr rfl fun k hk ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
    simp_rw [hprod]
    rw [ENNReal.tsum_mul_right]

/-- Marginalising a density on `H ∪ V` to `H` integrates out the coordinates in `V`. -/
lemma map_restrict_withDensity_union {H V : Finset S} (hHV : Disjoint H V) (η : S → E)
    {w : (S → E) → ℝ≥0∞} (hw : Measurable w) :
    ((λ₀ (H ∪ V) η).withDensity w).map H.restrict
      = ((λ₀ H η).withDensity fun ζ ↦ ∫⁻ ξ, w ξ ∂(λ₀ V ζ)).map H.restrict := by
  ext A hA
  have hA' : MeasurableSet (H.restrict ⁻¹' A : Set (S → E)) :=
    Finset.measurable_restrict (X := fun _ : S ↦ E) H hA
  rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) H) hA,
    Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) H) hA,
    withDensity_apply _ hA', withDensity_apply _ hA', ← lintegral_indicator hA',
    ← lintegral_indicator hA', lintegral_lambdaCount_union hHV η (hw.indicator hA')]
  refine lintegral_congr fun ζ ↦ ?_
  have hres : ∀ ξ : S → E, (∀ k ∉ V, ξ k = ζ k) → H.restrict ξ = H.restrict ζ := fun ξ hξ ↦
    funext fun k ↦ hξ k (Finset.disjoint_left.1 hHV k.2)
  by_cases hζ : ζ ∈ H.restrict ⁻¹' A
  · rw [Set.indicator_of_mem hζ]
    exact lintegral_lambdaCount_congr V ζ (hw.indicator hA') hw fun ξ hξ ↦
      Set.indicator_of_mem (show ξ ∈ H.restrict ⁻¹' A by
        change H.restrict ξ ∈ A; rwa [hres ξ hξ]) _
  · rw [Set.indicator_of_notMem hζ]
    rw [lintegral_lambdaCount_congr V ζ (hw.indicator hA') measurable_const
      (G := fun _ ↦ 0) fun ξ hξ ↦ Set.indicator_of_notMem (fun h ↦ hζ (by
        change H.restrict ξ ∈ A at h; rwa [hres ξ hξ] at h)) _]
    simp

/-- The measure of a cylinder over `H` is the sum over the spins in a disjoint finite `V` of the
measures of the cylinders over `H ∪ V`. -/
lemma measure_cyl_eq_lintegral_lambdaCount (μ : Measure (S → E)) {H V : Finset S}
    (hHV : Disjoint H V) (ζ : S → E) :
    μ (cyl H ζ) = ∫⁻ ξ, μ (cyl (H ∪ V) ξ) ∂(λ₀ V ζ) := by
  induction V using Finset.induction_on generalizing ζ with
  | empty => rw [Finset.union_empty, lintegral_lambdaCount_empty _ (measurable_measure_cyl μ H)]
  | insert j V hj ih =>
    rw [Finset.disjoint_insert_right] at hHV
    rw [ih hHV.2, lintegral_lambdaCount_insert hj ζ (measurable_measure_cyl μ _)]
    refine lintegral_congr fun ξ ↦ ?_
    rw [Finset.union_insert, measure_cyl_eq_tsum_insert μ (Λ := H ∪ V) (j := j)
      (by simp [hHV.1, hj]) ξ]

end LambdaCount

variable [Nonempty E] in
/-- A fixed configuration, used as the boundary condition of the reference kernel `λ_Λ` when the
object being defined does not depend on it. -/
def baseConfig : S → E := fun _ ↦ Classical.arbitrary E

end MeasureTheory.GibbsMeasure

end
