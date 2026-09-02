/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Group.Action
public import GibbsMeasure.Mathlib.Probability.Kernel.InvariantSigmaAlgebra

/-!
# The mean ergodic theorem along Følner sets

Let a group `G` act on a finite measure space `(Ω, μ)` by measure-preserving maps, let `𝓘` be the
σ-algebra `MeasurableSpace.smulInvariants G Ω` of strictly invariant events, and let `F : κ → Finset G`
be a *Følner net* of finite sets along a filter `l`: eventually non-empty, with
`|(g • F k) ∆ F k| / |F k| → 0` for every `g`. For `f : Ω → E` put
`R_k f = |F k|⁻¹ ∑_{i ∈ F k} f ∘ (i • ·)`. Then

* **`L²` ergodic theorem**, Georgii (14.A3): for `f ∈ L²(μ)`, `R_k f → μ[f | 𝓘]` in `L²`
  (`MeasureTheory.tendsto_eLpNorm_inv_card_smul_sum_sub_condExp_two`, and at the level of
  `Lp E 2 μ`, `MeasureTheory.Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL2`);
* **mean ergodic theorem**, Georgii (14.A5): for `f ∈ L¹(μ)`, `R_k f → μ[f | 𝓘]` in `L¹`
  (`MeasureTheory.tendsto_eLpNorm_inv_card_smul_sum_sub_condExp_one`,
  `MeasureTheory.tendsto_integral_norm_inv_card_smul_sum_sub_condExp`, and at the level of
  `Lp E 1 μ`,
  `MeasureTheory.Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL1CLM`).

Georgii states both for `ℤ^d` acting on a probability space along a sequence of cubes
`Λ_n` with `|Λ_n| → ∞`. Nothing in the proof uses the cubes beyond the Følner property, nor the
group beyond its acting by measure-preserving maps; the statements here are at that generality.
For an additive group acting by `+ᵥ`, see the `Additive` section: the invariant σ-algebra is then
`MeasurableSpace.smulInvariants (Multiplicative G) Ω`
(`MeasureTheory.tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_one` and companions).

## The Hilbert space theorem

The `L²` statement is a fact about a family `T : G → E →ₗᵢ[𝕜] E` of linear isometries of a
Hilbert space satisfying `T i (T g x) = T (g * i) x` — the *Koopman* law of the operators
`f ↦ f ∘ (g • ·)`, which is why it is stated with `g * i` and left translates `g • F`:

* `LinearIsometry.tendsto_inv_card_smul_sum_starProjection_of_foelner`: the averages
  `|F k|⁻¹ ∑_{i ∈ F k} T i x` converge to the orthogonal projection of `x` onto the closed
  subspace of common fixed points (`LinearIsometry.invariants T`, or any `K` with
  `x ∈ K ↔ ∀ g, T g x = x`).

This is the von Neumann mean ergodic theorem for an amenable group. Mathlib proves the
one-operator case, `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`, by the
decomposition `E = ker (f - 1) ⊕ closure (range (f - 1))`; we follow the same route rather than
Georgii's closed-convex-hull argument (his Lemma (14.A2) is
`exists_norm_eq_iInf_of_complete_convex`), because the decomposition needs no group structure:
the orthogonal complement of the coboundaries `T g x - x` is the fixed subspace for *any* family
of isometries (`LinearIsometry.mem_of_mem_orthogonal_span`), the averages are `1`-Lipschitz
(`LinearIsometry.norm_inv_card_smul_sum_le`), hence equicontinuous, so the set where they
converge to `0` is closed, and on a coboundary they are bounded by `|(g • F) ∆ F| / |F| · ‖x‖`
(`LinearIsometry.norm_inv_card_smul_sum_sub_le`). The core statement
`LinearIsometry.tendsto_inv_card_smul_sum_starProjection` is indexed by an arbitrary type with a
family of injective "translations", so that it serves the multiplicative and the additive
conventions alike (`to_additive` cannot translate a statement containing `(F.card : 𝕜)⁻¹`).

## Hypotheses actually used

* `IsFiniteMeasure μ`: only to identify the orthogonal projection onto `lpMeas 𝓘` with the
  conditional expectation `μ[· | 𝓘]` (`MemLp.condExpL2_ae_eq_condExp`) and to pass from `L²` to
  `L¹`. The `Lp E 2 μ` statement
  `Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL2` holds for any invariant
  measure.
* `Countable G`: the a.e.-invariant representative of an `𝓘`-measurable class must be made
  *strictly* invariant, by discarding the null set `⋃_g {f ∘ (g • ·) ≠ f}`
  (`MeasurableSpace.exists_stronglyMeasurable_invariants_ae_eq`, Georgii's Remark (14.3)(2)).
  This is not decorative: for an uncountable group acting trivially outside a null set the
  averages converge to `f`, while `μ[f | 𝓘]` can be a genuine average. A Følner net of finite
  sets along a countably generated filter — in particular a Følner sequence — forces countability
  (`countable_of_tendsto_card_smul_symmDiff_div_card` in
  `GibbsMeasure.Mathlib.GroupTheory.Foelner`).
* `∀ᶠ k in l, (F k).Nonempty`: the average over the empty set is `0`, and the Følner ratio
  `0 / 0 = 0` says nothing about it.
* `InnerProductSpace ℝ E`, `CompleteSpace E`: the target is a real Hilbert space so that
  `Lp E 2 μ` is one. The `L¹` theorem is deduced from the `L²` theorem on the dense set of simple
  functions, so it inherits this hypothesis; for a general Banach space one would reduce to
  indicator functions.
* Mathlib's `IsFoelner G Measure.count l (fun k ↦ ↑(F k))` is equivalent to the elementary
  hypothesis used here, `isFoelner_count_iff` in `GibbsMeasure.Mathlib.GroupTheory.Foelner`;
  for an abelian group `|(g +ᵥ F) ∆ F|` is `Finset.transDist F g` by definition.
-/

@[expose] public section

open Filter Finset
open scoped Topology Pointwise symmDiff ENNReal

namespace LinearIsometry

section NormedSpace

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The average `|F|⁻¹ ∑_{i ∈ F} T i x` of a family of isometries is a contraction. -/
lemma norm_inv_card_smul_sum_le (T : ι → E →ₗᵢ[𝕜] E) (F : Finset ι) (x : E) :
    ‖(F.card : 𝕜)⁻¹ • ∑ i ∈ F, T i x‖ ≤ ‖x‖ := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  have hc : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  calc ‖(F.card : 𝕜)⁻¹ • ∑ i ∈ F, T i x‖ = (F.card : ℝ)⁻¹ * ‖∑ i ∈ F, T i x‖ := by
        rw [norm_smul, norm_inv, RCLike.norm_natCast]
    _ ≤ (F.card : ℝ)⁻¹ * ∑ i ∈ F, ‖T i x‖ := by gcongr; exact norm_sum_le _ _
    _ = ‖x‖ := by
        simp only [norm_map, Finset.sum_const, nsmul_eq_mul]
        rw [inv_mul_cancel_left₀ hc.ne']

/-- The averages `x ↦ |F k|⁻¹ ∑_{i ∈ F k} T i x` form an equicontinuous family. -/
lemma equicontinuous_inv_card_smul_sum (T : ι → E →ₗᵢ[𝕜] E) (F : κ → Finset ι) :
    Equicontinuous fun k x ↦ ((F k).card : 𝕜)⁻¹ • ∑ i ∈ F k, T i x := by
  refine Metric.equicontinuous_of_continuity_modulus (fun t ↦ t) tendsto_id
    (fun k x ↦ ((F k).card : 𝕜)⁻¹ • ∑ i ∈ F k, T i x) fun x y k ↦ ?_
  simp only [dist_eq_norm, ← smul_sub, ← Finset.sum_sub_distrib, ← map_sub]
  exact norm_inv_card_smul_sum_le T (F k) (x - y)

/-- **The Følner estimate on a coboundary.** If `T i ∘ S = T (τ i)` for an injective `τ`, then
the average of `T i (S x) - T i x` over `F` is bounded by `|τ(F) ∆ F| / |F| · ‖x‖`: the two sums
`∑_{i ∈ F} T (τ i) x` and `∑_{i ∈ F} T i x` differ only on the symmetric difference of `F` and its
translate. -/
lemma norm_inv_card_smul_sum_sub_le (T : ι → E →ₗᵢ[𝕜] E) {τ : ι → ι} (hτ : Function.Injective τ)
    {S : E →ₗᵢ[𝕜] E} (hS : ∀ i x, T i (S x) = T (τ i) x) [DecidableEq ι] (F : Finset ι) (x : E) :
    ‖(F.card : 𝕜)⁻¹ • ∑ i ∈ F, (T i (S x) - T i x)‖ ≤
      (((F.image τ) ∆ F).card / F.card) * ‖x‖ := by
  have h1 : ∑ i ∈ F, T i (S x) = ∑ j ∈ F.image τ, T j x := by
    simp only [hS]
    rw [Finset.sum_image fun a _ b _ h ↦ hτ h]
  have hsd : (((F.image τ) ∆ F).card : ℝ) = ((F.image τ) \ F).card + (F \ (F.image τ)).card := by
    rw [Finset.symmDiff_def, Finset.card_union_eq_card_add_card.2 disjoint_sdiff_sdiff]
    push_cast; rfl
  have hb : ∀ s : Finset ι, ‖∑ j ∈ s, T j x‖ ≤ s.card * ‖x‖ := fun s ↦
    (norm_sum_le _ _).trans (by simp [norm_map])
  calc ‖(F.card : 𝕜)⁻¹ • ∑ i ∈ F, (T i (S x) - T i x)‖
      = (F.card : ℝ)⁻¹ * ‖∑ j ∈ (F.image τ) \ F, T j x - ∑ j ∈ F \ (F.image τ), T j x‖ := by
        rw [Finset.sum_sub_distrib, h1, Finset.sum_sdiff_sub_sum_sdiff, norm_smul, norm_inv,
          RCLike.norm_natCast]
    _ ≤ (F.card : ℝ)⁻¹ * (((F.image τ) \ F).card * ‖x‖ + (F \ (F.image τ)).card * ‖x‖) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (hb _) (hb _))
    _ = (((F.image τ) ∆ F).card / F.card) * ‖x‖ := by rw [hsd]; ring

variable (T : ι → E →ₗᵢ[𝕜] E)

/-- The closed subspace of vectors fixed by every member of a family of linear isometries. -/
def invariants : Submodule 𝕜 E := ⨅ i, LinearMap.eqLocus (T i : E →ₗ[𝕜] E) LinearMap.id

@[simp] lemma mem_invariants {x : E} : x ∈ invariants T ↔ ∀ i, T i x = x := by
  simp [invariants, Submodule.mem_iInf, LinearMap.mem_eqLocus]

lemma coe_invariants : (invariants T : Set E) = ⋂ i, {x | T i x = x} := by
  ext x; simp

lemma isClosed_invariants : IsClosed (invariants T : Set E) := by
  rw [coe_invariants]
  exact isClosed_iInter fun i ↦ isClosed_eq (T i).continuous continuous_id

end NormedSpace

section Hilbert

variable {𝕜 E ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

instance hasOrthogonalProjection_invariants (T : ι → E →ₗᵢ[𝕜] E) :
    (invariants T).HasOrthogonalProjection :=
  haveI := (isClosed_invariants T).completeSpace_coe
  .ofCompleteSpace _

omit [CompleteSpace E] in
/-- A vector orthogonal to every coboundary `T i x - x` is fixed by every `T i`: from
`⟪T i v - v, v⟫ = 0` and `‖T i v‖ = ‖v‖` the parallelogram law gives `T i v = v`. No relation
between the isometries is needed. -/
lemma mem_of_mem_orthogonal_span (T : ι → E →ₗᵢ[𝕜] E) {K : Submodule 𝕜 E}
    (hK : ∀ x, x ∈ K ↔ ∀ i, T i x = x) {v : E}
    (hv : v ∈ (Submodule.span 𝕜 (⋃ i, Set.range fun x ↦ T i x - x))ᗮ) : v ∈ K := by
  refine (hK v).2 fun i ↦ ?_
  have h : ⟪T i v - v, v⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_iUnion.2 ⟨i, Set.mem_range_self v⟩)) hv
  rw [inner_sub_left, sub_eq_zero] at h
  exact eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜) (by rw [norm_map])
    (by rw [h, inner_self_eq_norm_sq])

/-- **Mean ergodic theorem for a family of isometries**, core form. Let `T : ι → E →ₗᵢ[𝕜] E` be
isometries of a Hilbert space with `T i ∘ T g = T (τ g i)` for injective translations `τ g`, let
`K` be the subspace of common fixed points (given with its orthogonal projection), and let
`F : κ → Finset ι` be eventually non-empty with `|τ g (F k) ∆ F k| / |F k| → 0` for every `g`.
Then the averages `|F k|⁻¹ ∑_{i ∈ F k} T i x` converge to the orthogonal projection of `x` onto
`K`. For a group acting on itself by translation see
`tendsto_inv_card_smul_sum_starProjection_of_foelner` and its additive companion. -/
theorem tendsto_inv_card_smul_sum_starProjection {l : Filter κ} (T : ι → E →ₗᵢ[𝕜] E)
    {τ : ι → ι → ι} (hτ : ∀ i, Function.Injective (τ i))
    (hT : ∀ g i x, T i (T g x) = T (τ g i) x)
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection] (hK : ∀ x, x ∈ K ↔ ∀ i, T i x = x)
    [DecidableEq ι] {F : κ → Finset ι} (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g, Tendsto (fun k ↦ (((F k).image (τ g) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    (x : E) :
    Tendsto (fun k ↦ ((F k).card : 𝕜)⁻¹ • ∑ i ∈ F k, T i x) l (𝓝 (K.starProjection x)) := by
  classical
  set R : κ → E → E := fun k y ↦ ((F k).card : 𝕜)⁻¹ • ∑ i ∈ F k, T i y with hR
  have hlin : ∀ k y z, R k y + R k z = R k (y + z) := fun k y z ↦ by
    simp [hR, map_add, Finset.sum_add_distrib, smul_add]
  have hfix : ∀ y ∈ K, Tendsto (fun k ↦ R k y) l (𝓝 y) := by
    intro y hy
    refine tendsto_const_nhds.congr' (hne.mono fun k hk ↦ ?_)
    simp only [hR, (hK y).1 hy, Finset.sum_const, ← Nat.cast_smul_eq_nsmul 𝕜]
    rw [inv_smul_smul₀ (Nat.cast_ne_zero.2 hk.card_pos.ne')]
  have hzero : ∀ y ∈ Kᗮ, Tendsto (fun k ↦ R k y) l (𝓝 0) := by
    intro y hy
    have hclosed : IsClosed {y | Tendsto (fun k ↦ R k y) l (𝓝 0)} :=
      (equicontinuous_inv_card_smul_sum T F).isClosed_setOfPred_tendsto
        (f := fun _ ↦ (0 : E)) continuous_const
    have hN : Kᗮ ≤ (Submodule.span 𝕜 (⋃ i, Set.range fun x ↦ T i x - x)).topologicalClosure := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure]
      exact Submodule.orthogonal_le fun v hv ↦ mem_of_mem_orthogonal_span T hK hv
    have hy' : y ∈ closure (Submodule.span 𝕜 (⋃ i, Set.range fun x ↦ T i x - x) : Set E) :=
      hN hy
    refine closure_minimal ?_ hclosed hy'
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, x, rfl⟩ : ∃ g x, T g x - x = z := by simpa using hz
      have hbound : ∀ k, ‖R k (T g x - x)‖ ≤
          (((F k).image (τ g) ∆ F k).card : ℝ) / (F k).card * ‖x‖ := fun k ↦ by
        simp only [hR, map_sub]
        exact norm_inv_card_smul_sum_sub_le T (hτ g) (fun i x ↦ hT g i x) (F k) x
      exact squeeze_zero_norm hbound (by simpa using (hF g).mul_const ‖x‖)
    | zero => simpa [hR] using tendsto_const_nhds
    | add y z _ _ hy hz => simpa [← hlin] using hy.add hz
    | smul a y _ hy =>
      have : ∀ k, R k (a • y) = a • R k y := fun k ↦ by
        simp [hR, map_smul, Finset.smul_sum, smul_comm a]
      simpa [this] using hy.const_smul a
  have := (hfix _ (K.starProjection_apply_mem x)).add
    (hzero _ (Submodule.sub_starProjection_mem_orthogonal x))
  simpa [hlin] using this

section Group

variable {G : Type*} [Group G] [DecidableEq G] {l : Filter κ}

/-- **Von Neumann's mean ergodic theorem along a Følner net.** Let `T : G → E →ₗᵢ[𝕜] E` be
isometries of a Hilbert space satisfying the Koopman law `T i (T g x) = T (g * i) x`, let `K` be
the subspace of common fixed points, and let `F` be a Følner net of finite sets:
`|(g • F k) ∆ F k| / |F k| → 0`. Then `|F k|⁻¹ ∑_{i ∈ F k} T i x → K.starProjection x`.
This is Georgii (14.A3) in Hilbert-space form. -/
theorem tendsto_inv_card_smul_sum_starProjection_of_foelner (T : G → E →ₗᵢ[𝕜] E)
    (hT : ∀ g i x, T i (T g x) = T (g * i) x)
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection] (hK : ∀ x, x ∈ K ↔ ∀ g, T g x = x)
    {F : κ → Finset G} (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    (x : E) :
    Tendsto (fun k ↦ ((F k).card : 𝕜)⁻¹ • ∑ i ∈ F k, T i x) l (𝓝 (K.starProjection x)) :=
  tendsto_inv_card_smul_sum_starProjection T (τ := fun g i ↦ g * i)
    (fun g ↦ mul_right_injective g) hT hK hne (fun g ↦ hF g) x

/-- `tendsto_inv_card_smul_sum_starProjection_of_foelner` with the fixed subspace
`LinearIsometry.invariants T`. -/
theorem tendsto_inv_card_smul_sum_starProjection_invariants (T : G → E →ₗᵢ[𝕜] E)
    (hT : ∀ g i x, T i (T g x) = T (g * i) x)
    {F : κ → Finset G} (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    (x : E) :
    Tendsto (fun k ↦ ((F k).card : 𝕜)⁻¹ • ∑ i ∈ F k, T i x) l
      (𝓝 ((invariants T).starProjection x)) :=
  tendsto_inv_card_smul_sum_starProjection_of_foelner T hT (fun _ ↦ mem_invariants T) hne hF x

end Group

section AddGroup

variable {G : Type*} [AddGroup G] [DecidableEq G] {l : Filter κ}

/-- **Von Neumann's mean ergodic theorem along a Følner net**, for an additive group:
`tendsto_inv_card_smul_sum_starProjection_of_foelner` with `T i (T g x) = T (g + i) x` and
`|(g +ᵥ F k) ∆ F k| / |F k| → 0`. -/
theorem tendsto_inv_card_smul_sum_starProjection_of_addFoelner (T : G → E →ₗᵢ[𝕜] E)
    (hT : ∀ g i x, T i (T g x) = T (g + i) x)
    {K : Submodule 𝕜 E} [K.HasOrthogonalProjection] (hK : ∀ x, x ∈ K ↔ ∀ g, T g x = x)
    {F : κ → Finset G} (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    (x : E) :
    Tendsto (fun k ↦ ((F k).card : 𝕜)⁻¹ • ∑ i ∈ F k, T i x) l (𝓝 (K.starProjection x)) :=
  tendsto_inv_card_smul_sum_starProjection T (τ := fun g i ↦ g + i)
    (fun g ↦ add_right_injective g) hT hK hne (fun g ↦ hF g) x

/-- `tendsto_inv_card_smul_sum_starProjection_of_addFoelner` with the fixed subspace
`LinearIsometry.invariants T`. -/
theorem tendsto_inv_card_smul_sum_starProjection_invariants_of_addFoelner (T : G → E →ₗᵢ[𝕜] E)
    (hT : ∀ g i x, T i (T g x) = T (g + i) x)
    {F : κ → Finset G} (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    (x : E) :
    Tendsto (fun k ↦ ((F k).card : 𝕜)⁻¹ • ∑ i ∈ F k, T i x) l
      (𝓝 ((invariants T).starProjection x)) :=
  tendsto_inv_card_smul_sum_starProjection_of_addFoelner T hT (fun _ ↦ mem_invariants T) hne hF x

end AddGroup

end Hilbert

end LinearIsometry

namespace MeasureTheory

section Mul

variable {Ω G : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Group G] [MulAction G Ω]
  [MeasurableConstSMul G Ω]

section Representative

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [Zero X]

/-- **Georgii, Remark (14.3)(2), for vector-valued functions.** Over a countable group, a strongly
measurable function that is a.e. invariant under each group element agrees a.e. with a function
that is strongly measurable for the invariant σ-algebra `𝓘`, hence strictly invariant: kill `f`
on the invariant null set `⋃_g {f ∘ (g • ·) ≠ f}`. Countability is used for that null set and
nowhere else; no invariance of `μ` is needed. -/
theorem _root_.MeasurableSpace.exists_stronglyMeasurable_invariants_ae_eq [Countable G]
    {f : Ω → X} (hf : StronglyMeasurable f) (hae : ∀ g : G, (fun ω ↦ f (g • ω)) =ᵐ[μ] f) :
    ∃ f' : Ω → X, StronglyMeasurable[MeasurableSpace.smulInvariants G Ω] f' ∧ f =ᵐ[μ] f' := by
  classical
  set P : Ω → Prop := fun ω ↦ ∀ g : G, f (g • ω) = f ω with hP
  have hPinv : ∀ (c : G) ω, P (c • ω) ↔ P ω := by
    intro c ω
    constructor
    · intro h g
      have h1 : f (g • ω) = f (c • ω) := by
        rw [← h (g * c⁻¹), smul_smul, inv_mul_cancel_right]
      have h2 : f ω = f (c • ω) := by
        rw [← h c⁻¹, inv_smul_smul]
      rw [h1, h2]
    · intro h g
      rw [smul_smul, h (g * c), h c]
  set N : Set Ω := {ω | ¬ P ω} with hN
  have hmem : ∀ ω, ω ∈ N ↔ ¬ P ω := fun ω ↦ Iff.rfl
  have hNeq : N = ⋃ g : G, {ω | f (g • ω) = f ω}ᶜ := by
    ext ω; simp [hN, hP]
  have hNm : MeasurableSet N := by
    rw [hNeq]
    exact MeasurableSet.iUnion fun g ↦
      ((hf.comp_measurable (measurable_const_smul g)).measurableSet_eq_fun hf).compl
  have hN0 : μ N = 0 := by
    rw [hNeq]
    exact measure_iUnion_null fun g ↦ ae_iff.1 (hae g)
  refine ⟨Nᶜ.indicator f, ?_, ?_⟩
  · have hf' : StronglyMeasurable (Nᶜ.indicator f) := hf.indicator hNm.compl
    have hinv : ∀ (c : G) ω, Nᶜ.indicator f (c • ω) = Nᶜ.indicator f ω := by
      intro c ω
      by_cases hω : P ω
      · have hc : P (c • ω) := (hPinv c ω).2 hω
        have hω' : ω ∈ Nᶜ := fun h ↦ (hmem ω).1 h hω
        have hc' : c • ω ∈ Nᶜ := fun h ↦ (hmem _).1 h hc
        rw [Set.indicator_of_mem hω', Set.indicator_of_mem hc', hω c]
      · have hc : ¬ P (c • ω) := fun h ↦ hω ((hPinv c ω).1 h)
        have hω' : ω ∉ Nᶜ := fun h ↦ h ((hmem ω).2 hω)
        have hc' : c • ω ∉ Nᶜ := fun h ↦ h ((hmem _).2 hc)
        rw [Set.indicator_of_notMem hω', Set.indicator_of_notMem hc']
    borelize X
    exact (stronglyMeasurable_iff_measurable_separable (m := MeasurableSpace.smulInvariants G Ω)).2
      ⟨MeasurableSpace.measurable_invariants_of_forall_smul_eq hf'.measurable hinv,
        hf'.isSeparable_range⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    rw [Set.indicator_of_mem (Set.mem_compl hω)]

end Representative

section Koopman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SMulInvariantMeasure G Ω μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Koopman operator `Lp.compMeasurePreservingₗᵢ ℝ (g • ·) _` of a measure-preserving action
is `f ↦ f ∘ (g • ·)`. -/
lemma Lp.coeFn_compMeasurePreservingₗᵢ_smul (g : G) (f : Lp E p μ) :
    ⇑(Lp.compMeasurePreservingₗᵢ ℝ (g • ·) (measurePreserving_smul g μ) f) =ᵐ[μ]
      fun ω ↦ f (g • ω) :=
  Lp.coeFn_compMeasurePreserving f _

/-- The Koopman operators form an anti-representation: `T i ∘ T g = T (g * i)`. -/
lemma Lp.compMeasurePreservingₗᵢ_smul_compMeasurePreservingₗᵢ_smul (g i : G) (f : Lp E p μ) :
    Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ)
        (Lp.compMeasurePreservingₗᵢ ℝ (g • ·) (measurePreserving_smul g μ) f) =
      Lp.compMeasurePreservingₗᵢ ℝ ((g * i) • ·) (measurePreserving_smul (g * i) μ) f := by
  have h1 := Lp.coeFn_compMeasurePreservingₗᵢ_smul i
    (Lp.compMeasurePreservingₗᵢ ℝ (g • ·) (measurePreserving_smul g μ) f)
  have h2 := (measurePreserving_smul i μ).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreservingₗᵢ_smul g f)
  have h3 : (fun ω ↦ f (g • i • ω)) =ᵐ[μ] fun ω ↦ f ((g * i) • ω) :=
    Eventually.of_forall fun ω ↦ by simp only [mul_smul]
  have h4 := Lp.coeFn_compMeasurePreservingₗᵢ_smul (g * i) f
  exact Lp.ext (h1.trans (h2.trans (h3.trans h4.symm)))

/-- Georgii's average `R_F f = |F|⁻¹ ∑_{i ∈ F} f ∘ (i • ·)` of (14.A1), as an element of `L^p`. -/
lemma Lp.coeFn_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul (F : Finset G) (f : Lp E p μ) :
    ⇑((F.card : ℝ)⁻¹ •
        ∑ i ∈ F, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) f) =ᵐ[μ]
      fun ω ↦ (F.card : ℝ)⁻¹ • ∑ i ∈ F, f (i • ω) := by
  refine (Lp.coeFn_smul _ _).trans ?_
  have := (Lp.coeFn_finsetSum F fun i ↦
    Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) f).trans
    (eventuallyEq_sum fun i _ ↦ Lp.coeFn_compMeasurePreservingₗᵢ_smul i f)
  filter_upwards [this] with ω hω
  simp only [Pi.smul_apply, hω, Finset.sum_apply]

/-- Over a countable group, the `𝓘`-measurable classes in `L^p` are exactly the common fixed
points of the Koopman operators. The forward direction holds for any group. -/
theorem Lp.mem_lpMeas_invariants_iff [Countable G] (f : Lp E p μ) :
    f ∈ lpMeas E ℝ (MeasurableSpace.smulInvariants G Ω) p μ ↔
      ∀ g : G, Lp.compMeasurePreservingₗᵢ ℝ (g • ·) (measurePreserving_smul g μ) f = f := by
  constructor
  · intro h g
    obtain ⟨f', hf', hff'⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 h
    have hinv : ∀ ω, f' (g • ω) = f' ω := by
      borelize E
      exact MeasurableSpace.smul_eq_of_measurable_invariants hf'.measurable g
    refine Lp.ext ((Lp.coeFn_compMeasurePreservingₗᵢ_smul g f).trans ?_)
    calc (fun ω ↦ f (g • ω)) =ᵐ[μ] (fun ω ↦ f' (g • ω)) :=
          (measurePreserving_smul g μ).quasiMeasurePreserving.ae_eq_comp hff'
      _ = f' := funext hinv
      _ =ᵐ[μ] f := hff'.symm
  · intro h
    have hae : ∀ g : G, (fun ω ↦ f (g • ω)) =ᵐ[μ] f := fun g ↦ by
      have := Lp.coeFn_compMeasurePreservingₗᵢ_smul g f
      rw [h g] at this
      exact this.symm
    obtain ⟨f', hf', hff'⟩ :=
      MeasurableSpace.exists_stronglyMeasurable_invariants_ae_eq (Lp.stronglyMeasurable f) hae
    exact mem_lpMeas_iff_aestronglyMeasurable.2 ⟨f', hf', hff'⟩

end Koopman

section MeanErgodic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SMulInvariantMeasure G Ω μ] [IsFiniteMeasure μ] [Countable G] [DecidableEq G]
  {κ : Type*} {l : Filter κ} {F : κ → Finset G}

omit [IsFiniteMeasure μ] in
/-- **Georgii (14.A3), the `L²` ergodic theorem**, in `Lp E 2 μ`: along a Følner net of finite
sets the averages `|F k|⁻¹ ∑_{i ∈ F k} f ∘ (i • ·)` converge to `condExpL2 f`, the orthogonal
projection onto the `𝓘`-measurable subspace. The measure need only be invariant. -/
theorem Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL2
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    (f : Lp E 2 μ) :
    Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ •
        ∑ i ∈ F k, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) f) l
      (𝓝 (condExpL2 E ℝ (MeasurableSpace.smulInvariants_le (M := G)) f : Lp E 2 μ)) := by
  have : Fact (MeasurableSpace.smulInvariants G Ω ≤ _) := ⟨MeasurableSpace.smulInvariants_le (M := G)⟩
  have h := LinearIsometry.tendsto_inv_card_smul_sum_starProjection_of_foelner
    (fun g : G ↦ Lp.compMeasurePreservingₗᵢ ℝ (g • ·) (measurePreserving_smul g μ))
    (fun g i f ↦ Lp.compMeasurePreservingₗᵢ_smul_compMeasurePreservingₗᵢ_smul g i f)
    (K := lpMeas E ℝ (MeasurableSpace.smulInvariants G Ω) 2 μ)
    (fun f ↦ Lp.mem_lpMeas_invariants_iff f) hne hF f
  exact h

/-- **Georgii (14.A3), the `L²` ergodic theorem.** For `f ∈ L²(μ)`,
`‖|F k|⁻¹ ∑_{i ∈ F k} f ∘ (i • ·) - μ[f | 𝓘]‖₂ → 0` along a Følner net of finite sets. -/
theorem tendsto_eLpNorm_inv_card_smul_sum_sub_condExp_two (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    {f : Ω → E} (hf : MemLp f 2 μ) :
    Tendsto (fun k ↦ eLpNorm (fun ω ↦ ((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω) -
      (μ[f | MeasurableSpace.smulInvariants G Ω]) ω) 2 μ) l (𝓝 0) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
    (Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL2 hne hF (hf.toLp f))
  refine h.congr fun k ↦ eLpNorm_congr_ae ?_
  have h1 := Lp.coeFn_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul (F k) (hf.toLp f)
  have h2 : ∀ᵐ ω ∂μ, ∀ i ∈ F k, (hf.toLp f) (i • ω) = f (i • ω) := by
    rw [eventually_all_finset]
    exact fun i _ ↦ (measurePreserving_smul i μ).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
  have h3 := hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) (MeasurableSpace.smulInvariants_le (M := G))
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  simp only [Pi.sub_apply, hω1, hω3, Finset.sum_congr rfl hω2]

/-- The `L¹` ergodic theorem for an `L¹` class with an `L²` representative: `L²`-convergence
implies `L¹`-convergence on a finite measure space, and both conditional expectations agree. -/
theorem Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL1CLM_of_ae_eq
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    {s : Lp E 1 μ} {s₂ : Lp E 2 μ} (hss₂ : ⇑s₂ =ᵐ[μ] ⇑s) :
    Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ •
        ∑ i ∈ F k, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) s) l
      (𝓝 (condExpL1CLM E (MeasurableSpace.smulInvariants_le (M := G)) μ s)) := by
  have hm : MeasurableSpace.smulInvariants G Ω ≤ _ := MeasurableSpace.smulInvariants_le (M := G)
  have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
    (Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL2 hne hF s₂)
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hae : ∀ k, (⇑(((F k).card : ℝ)⁻¹ •
        ∑ i ∈ F k, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) s) -
        ⇑(condExpL1CLM E hm μ s)) =ᵐ[μ]
      (⇑(((F k).card : ℝ)⁻¹ •
        ∑ i ∈ F k, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) s₂) -
        ⇑(condExpL2 E ℝ hm s₂ : Lp E 2 μ)) := by
    intro k
    have e1 := Lp.coeFn_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul (F k) s
    have e2 := Lp.coeFn_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul (F k) s₂
    have e3 : ∀ᵐ ω ∂μ, ∀ i ∈ F k, s₂ (i • ω) = s (i • ω) := by
      rw [eventually_all_finset]
      exact fun i _ ↦ (measurePreserving_smul i μ).quasiMeasurePreserving.ae_eq_comp hss₂
    have e4 : ⇑(condExpL1CLM E hm μ s) =ᵐ[μ] μ[⇑s | MeasurableSpace.smulInvariants G Ω] := by
      have := condExp_ae_eq_condExpL1CLM hm (L1.integrable_coeFn s)
      rw [Integrable.toL1_coeFn] at this
      exact this.symm
    have e5 : μ[⇑s | MeasurableSpace.smulInvariants G Ω] =ᵐ[μ]
        μ[⇑s₂ | MeasurableSpace.smulInvariants G Ω] :=
      condExp_congr_ae hss₂.symm
    have e6 : ⇑(condExpL2 E ℝ hm s₂ : Lp E 2 μ) =ᵐ[μ]
        μ[⇑s₂ | MeasurableSpace.smulInvariants G Ω] := by
      have := (Lp.memLp s₂).condExpL2_ae_eq_condExp (𝕜 := ℝ) hm
      rwa [Lp.toLp_coeFn] at this
    filter_upwards [e1, e2, e3, e4, e5, e6] with ω h1 h2 h3 h4 h5 h6
    rw [Pi.sub_apply, Pi.sub_apply, h1, h2, h4, h5, h6, Finset.sum_congr rfl h3]
  have hbound : ∀ k, eLpNorm (⇑(((F k).card : ℝ)⁻¹ •
        ∑ i ∈ F k, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) s) -
        ⇑(condExpL1CLM E hm μ s)) 1 μ ≤
      eLpNorm (⇑(((F k).card : ℝ)⁻¹ •
        ∑ i ∈ F k, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) s₂) -
        ⇑(condExpL2 E ℝ hm s₂ : Lp E 2 μ)) 2 μ *
        μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := fun k ↦ by
    rw [eLpNorm_congr_ae (hae k)]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ one_le_two
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ bot_le) hbound
  have hc : μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hc)

/-- **Georgii (14.A5), the mean ergodic theorem**, in `Lp E 1 μ`: along a Følner net of finite
sets the averages converge to `condExpL1CLM f`. The averages are uniformly `1`-Lipschitz, so the
set of `f` on which they converge to `condExpL1CLM f` is closed; it contains the simple functions,
which lie in `L²`, and these are dense. -/
theorem Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL1CLM
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    (f : Lp E 1 μ) :
    Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ •
        ∑ i ∈ F k, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) f) l
      (𝓝 (condExpL1CLM E (MeasurableSpace.smulInvariants_le (M := G)) μ f)) := by
  have hm : MeasurableSpace.smulInvariants G Ω ≤ _ := MeasurableSpace.smulInvariants_le (M := G)
  have hclosed : IsClosed {f : Lp E 1 μ | Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ •
      ∑ i ∈ F k, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) f) l
        (𝓝 (condExpL1CLM E hm μ f))} :=
    (LinearIsometry.equicontinuous_inv_card_smul_sum
      (fun g : G ↦ Lp.compMeasurePreservingₗᵢ (E := E) (p := 1) ℝ (g • ·)
        (measurePreserving_smul g μ)) F).isClosed_setOfPred_tendsto (l := l)
      (condExpL1CLM E hm μ).continuous
  have hsub : (Lp.simpleFunc E 1 μ : Set (Lp E 1 μ)) ⊆ {f : Lp E 1 μ | Tendsto (fun k ↦
      ((F k).card : ℝ)⁻¹ •
      ∑ i ∈ F k, Lp.compMeasurePreservingₗᵢ ℝ (i • ·) (measurePreserving_smul i μ) f) l
        (𝓝 (condExpL1CLM E hm μ f))} := by
    intro s hs
    have hs₂ : MemLp (Lp.simpleFunc.toSimpleFunc (⟨s, hs⟩ : Lp.simpleFunc E 1 μ)) 2 μ :=
      SimpleFunc.memLp_of_isFiniteMeasure _ 2 μ
    exact Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL1CLM_of_ae_eq hne hF
      (hs₂.coeFn_toLp.trans (Lp.simpleFunc.toSimpleFunc_eq_toFun ⟨s, hs⟩))
  have := closure_minimal hsub hclosed
  rw [(Lp.simpleFunc.dense (E := E) (μ := μ) (p := 1) ENNReal.one_ne_top).closure_eq] at this
  exact this (Set.mem_univ f)

/-- **Georgii (14.A5), the mean ergodic theorem.** For integrable `f`,
`‖|F k|⁻¹ ∑_{i ∈ F k} f ∘ (i • ·) - μ[f | 𝓘]‖₁ → 0` along a Følner net of finite sets. -/
theorem tendsto_eLpNorm_inv_card_smul_sum_sub_condExp_one (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    {f : Ω → E} (hf : Integrable f μ) :
    Tendsto (fun k ↦ eLpNorm (fun ω ↦ ((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω) -
      (μ[f | MeasurableSpace.smulInvariants G Ω]) ω) 1 μ) l (𝓝 0) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
    (Lp.tendsto_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul_condExpL1CLM hne hF (hf.toL1 f))
  refine h.congr fun k ↦ eLpNorm_congr_ae ?_
  have h1 := Lp.coeFn_inv_card_smul_sum_compMeasurePreservingₗᵢ_smul (F k) (hf.toL1 f)
  have h2 : ∀ᵐ ω ∂μ, ∀ i ∈ F k, (hf.toL1 f) (i • ω) = f (i • ω) := by
    rw [eventually_all_finset]
    exact fun i _ ↦ (measurePreserving_smul i μ).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1
  have h3 := condExp_ae_eq_condExpL1CLM (MeasurableSpace.smulInvariants_le (M := G)) hf
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  simp only [Pi.sub_apply, hω1, ← hω3, Finset.sum_congr rfl hω2]

/-- **Georgii (14.A5), the mean ergodic theorem**, integral form: for integrable `f`,
`∫ ‖|F k|⁻¹ ∑_{i ∈ F k} f (i • ω) - μ[f | 𝓘] ω‖ dμ(ω) → 0`. For `μ` ergodic and `f = 1_A` this is
the form used in Georgii's Theorem (14.7). -/
theorem tendsto_integral_norm_inv_card_smul_sum_sub_condExp (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ g : G, Tendsto (fun k ↦ (((g • F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    {f : Ω → E} (hf : Integrable f μ) :
    Tendsto (fun k ↦ ∫ ω, ‖((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω) -
      (μ[f | MeasurableSpace.smulInvariants G Ω]) ω‖ ∂μ) l (𝓝 0) := by
  have h := tendsto_eLpNorm_inv_card_smul_sum_sub_condExp_one hne hF hf
  have hmeas : ∀ k, AEStronglyMeasurable (fun ω ↦ ((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i • ω) -
      (μ[f | MeasurableSpace.smulInvariants G Ω]) ω) μ := fun k ↦
    (((integrable_finsetSum (F k) fun i _ ↦
      (measurePreserving_smul i μ).integrable_comp_of_integrable hf).smul _).sub
        integrable_condExp).aestronglyMeasurable
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at this
  refine this.congr fun k ↦ ?_
  simp only [Function.comp, eLpNorm_one_eq_lintegral_enorm]
  exact (integral_norm_eq_lintegral_enorm (hmeas k)).symm

end MeanErgodic

end Mul

/-! ### Additive groups

For an additive group acting by `+ᵥ`, the invariant σ-algebra of the action is
`MeasurableSpace.smulInvariants (Multiplicative G) Ω`: `MeasurableSpace.smulInvariants` is stated for
`SMul`, and `Multiplicative G` acts on `Ω` by `ofAdd g • ω = g +ᵥ ω`. The statements are
transported along this identification. -/

section Additive

variable {G : Type*} [AddGroup G] [DecidableEq G]

/-- Translation of a finite set by `g` corresponds, under `Multiplicative.ofAdd`, to the pointwise
action of `ofAdd g` on the image; hence the Følner ratios agree. -/
lemma card_smul_map_ofAdd_symmDiff (g : Multiplicative G) (F : Finset G) :
    ((g • F.map Multiplicative.ofAdd.toEmbedding) ∆ F.map Multiplicative.ofAdd.toEmbedding).card =
      ((Multiplicative.toAdd g +ᵥ F) ∆ F).card := by
  have h : g • F.map Multiplicative.ofAdd.toEmbedding =
      (Multiplicative.toAdd g +ᵥ F).map Multiplicative.ofAdd.toEmbedding := by
    ext x
    simp only [Finset.mem_smul_finset, Finset.mem_map, Finset.mem_vadd_finset,
      Equiv.coe_toEmbedding, smul_eq_mul, vadd_eq_add]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨Multiplicative.toAdd g + a, ⟨a, ha, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨Multiplicative.ofAdd a, ⟨a, ha, rfl⟩, by simp⟩
  rw [h]
  simp only [Finset.map_eq_image, Equiv.coe_toEmbedding]
  rw [← Finset.image_symmDiff _ _ Multiplicative.ofAdd.injective,
    Finset.card_image_of_injective _ Multiplicative.ofAdd.injective]

omit [DecidableEq G] in
/-- The average over `F.map ofAdd` of `f ∘ (· • ω)` is the average over `F` of `f ∘ (· +ᵥ ω)`. -/
lemma inv_card_smul_sum_map_ofAdd {Ω E : Type*} [AddAction G Ω] [AddCommMonoid E] [Module ℝ E]
    (F : Finset G) (f : Ω → E) (ω : Ω) :
    ((F.map Multiplicative.ofAdd.toEmbedding).card : ℝ)⁻¹ •
        ∑ i ∈ F.map Multiplicative.ofAdd.toEmbedding, f (i • ω) =
      (F.card : ℝ)⁻¹ • ∑ i ∈ F, f (i +ᵥ ω) := by
  rw [Finset.card_map, Finset.sum_map]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [AddAction G Ω]
  [MeasurableConstVAdd G Ω] [VAddInvariantMeasure G Ω μ] [IsFiniteMeasure μ] [Countable G]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {κ : Type*} {l : Filter κ} {F : κ → Finset G}
  (hne : ∀ᶠ k in l, (F k).Nonempty)
  (hF : ∀ g : G, Tendsto (fun k ↦ (((g +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
include hne hF

omit hne [MeasurableSpace Ω] [IsFiniteMeasure μ] [Countable G] in
/-- The Følner hypothesis for `F`, read on `Multiplicative G`. -/
lemma tendsto_card_smul_map_ofAdd_symmDiff_div_card (g : Multiplicative G) :
    Tendsto (fun k ↦ (((g • (F k).map Multiplicative.ofAdd.toEmbedding) ∆
      (F k).map Multiplicative.ofAdd.toEmbedding).card : ℝ) /
        ((F k).map Multiplicative.ofAdd.toEmbedding).card) l (𝓝 0) := by
  simpa only [card_smul_map_ofAdd_symmDiff, Finset.card_map] using hF (Multiplicative.toAdd g)

/-- **Georgii (14.A3), the `L²` ergodic theorem**, for an additive group acting by `+ᵥ`
(Georgii's `ℤ^d`): for `f ∈ L²(μ)` and a Følner net of finite sets,
`‖|F k|⁻¹ ∑_{i ∈ F k} f ∘ (i +ᵥ ·) - μ[f | 𝓘]‖₂ → 0`, where `𝓘` is the invariant σ-algebra
`MeasurableSpace.smulInvariants (Multiplicative G) Ω`. -/
theorem tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_two {f : Ω → E} (hf : MemLp f 2 μ) :
    Tendsto (fun k ↦ eLpNorm (fun ω ↦ ((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i +ᵥ ω) -
      (μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω) 2 μ) l (𝓝 0) := by
  have : MeasurableConstSMul (Multiplicative G) Ω :=
    ⟨fun c ↦ measurable_const_vadd (Multiplicative.toAdd c)⟩
  have : SMulInvariantMeasure (Multiplicative G) Ω μ :=
    ⟨fun c _ hs ↦ VAddInvariantMeasure.measure_preimage_vadd (Multiplicative.toAdd c) hs⟩
  have : Countable (Multiplicative G) := ‹Countable G›
  have h := tendsto_eLpNorm_inv_card_smul_sum_sub_condExp_two (G := Multiplicative G)
    (F := fun k ↦ (F k).map Multiplicative.ofAdd.toEmbedding)
    (hne.mono fun k hk ↦ Finset.map_nonempty.2 hk)
    (tendsto_card_smul_map_ofAdd_symmDiff_div_card hF) hf
  simpa only [inv_card_smul_sum_map_ofAdd] using h

/-- **Georgii (14.A5), the mean ergodic theorem**, for an additive group acting by `+ᵥ`
(Georgii's `ℤ^d`): for integrable `f` and a Følner net of finite sets,
`‖|F k|⁻¹ ∑_{i ∈ F k} f ∘ (i +ᵥ ·) - μ[f | 𝓘]‖₁ → 0`, where `𝓘` is the invariant σ-algebra
`MeasurableSpace.smulInvariants (Multiplicative G) Ω`. -/
theorem tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_one {f : Ω → E}
    (hf : Integrable f μ) :
    Tendsto (fun k ↦ eLpNorm (fun ω ↦ ((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i +ᵥ ω) -
      (μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω) 1 μ) l (𝓝 0) := by
  have : MeasurableConstSMul (Multiplicative G) Ω :=
    ⟨fun c ↦ measurable_const_vadd (Multiplicative.toAdd c)⟩
  have : SMulInvariantMeasure (Multiplicative G) Ω μ :=
    ⟨fun c _ hs ↦ VAddInvariantMeasure.measure_preimage_vadd (Multiplicative.toAdd c) hs⟩
  have : Countable (Multiplicative G) := ‹Countable G›
  have h := tendsto_eLpNorm_inv_card_smul_sum_sub_condExp_one (G := Multiplicative G)
    (F := fun k ↦ (F k).map Multiplicative.ofAdd.toEmbedding)
    (hne.mono fun k hk ↦ Finset.map_nonempty.2 hk)
    (tendsto_card_smul_map_ofAdd_symmDiff_div_card hF) hf
  simpa only [inv_card_smul_sum_map_ofAdd] using h

/-- **Georgii (14.A5), the mean ergodic theorem**, integral form, for an additive group acting
by `+ᵥ`: for integrable `f` and a Følner net of finite sets,
`∫ ‖|F k|⁻¹ ∑_{i ∈ F k} f (i +ᵥ ω) - μ[f | 𝓘] ω‖ dμ(ω) → 0`. -/
theorem tendsto_integral_norm_inv_card_smul_sum_vadd_sub_condExp {f : Ω → E}
    (hf : Integrable f μ) :
    Tendsto (fun k ↦ ∫ ω, ‖((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i +ᵥ ω) -
      (μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω‖ ∂μ) l (𝓝 0) := by
  have : MeasurableConstSMul (Multiplicative G) Ω :=
    ⟨fun c ↦ measurable_const_vadd (Multiplicative.toAdd c)⟩
  have : SMulInvariantMeasure (Multiplicative G) Ω μ :=
    ⟨fun c _ hs ↦ VAddInvariantMeasure.measure_preimage_vadd (Multiplicative.toAdd c) hs⟩
  have : Countable (Multiplicative G) := ‹Countable G›
  have h := tendsto_integral_norm_inv_card_smul_sum_sub_condExp (G := Multiplicative G)
    (F := fun k ↦ (F k).map Multiplicative.ofAdd.toEmbedding)
    (hne.mono fun k hk ↦ Finset.map_nonempty.2 hk)
    (tendsto_card_smul_map_ofAdd_symmDiff_div_card hF) hf
  simpa only [inv_card_smul_sum_map_ofAdd] using h

end Additive

end MeasureTheory
