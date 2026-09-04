/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Extending an isometry of a subspace by the identity on its orthogonal complement

For a subspace `K` of an inner product space `E` admitting an orthogonal projection and a linear
isometric equivalence `f` of `K`, `K.orthogonalExtend f` is the linear isometric equivalence of
`E` acting as `f` on `K` and as the identity on `Kᗮ`, i.e. `f ⊕ id` under the orthogonal
decomposition `E ≃ K × Kᗮ` (`Submodule.orthogonalDecomposition`).

* `Submodule.orthogonalExtend_trans`, `Submodule.orthogonalExtend_mul`: `orthogonalExtend` is a
  group homomorphism `(K ≃ₗᵢ K) →* (E ≃ₗᵢ E)`.
* `Submodule.eq_orthogonalExtend`: an isometry of `E` fixing `Kᗮ` pointwise and acting as `f`
  on `K` is `K.orthogonalExtend f`.
* `Submodule.orthogonalExtend_reflection_orthogonal_span_singleton`: the reflection of `E` in the
  hyperplane orthogonal to a vector `v ∈ K` is the extension of the reflection of `K` in the
  hyperplane of `K` orthogonal to `v`.

Intended home: `Mathlib/Analysis/InnerProductSpace/ProdL2.lean`.
-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

/-- The linear isometric equivalence of `E` acting as `f` on the subspace `K` and as the identity
on its orthogonal complement `Kᗮ`. -/
def orthogonalExtend (f : K ≃ₗᵢ[𝕜] K) : E ≃ₗᵢ[𝕜] E :=
  K.orthogonalDecomposition.trans
    ((LinearIsometryEquiv.withLpProdCongr 2 f (LinearIsometryEquiv.refl 𝕜 Kᗮ)).trans
      K.orthogonalDecomposition.symm)

@[simp]
theorem orthogonalExtend_apply (f : K ≃ₗᵢ[𝕜] K) (x : E) :
    K.orthogonalExtend f x = (f (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x := by
  simp [orthogonalExtend]

/-- `K.orthogonalExtend f` acts as `f` on `K`. -/
theorem orthogonalExtend_apply_coe (f : K ≃ₗᵢ[𝕜] K) (x : K) :
    K.orthogonalExtend f x = f x := by
  rw [orthogonalExtend_apply, orthogonalProjectionOnto_mem_subspace_eq_self,
    (starProjection_apply_eq_zero_iff (K := Kᗮ)).2 (K.le_orthogonal_orthogonal x.2), add_zero]

/-- `K.orthogonalExtend f` is the identity on `Kᗮ`. -/
theorem orthogonalExtend_apply_of_mem_orthogonal (f : K ≃ₗᵢ[𝕜] K) {x : E} (hx : x ∈ Kᗮ) :
    K.orthogonalExtend f x = x := by
  rw [orthogonalExtend_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hx, map_zero,
    coe_zero, zero_add, starProjection_eq_self_iff.2 hx]

/-- An isometry of `E` fixing `Kᗮ` pointwise and acting as `f` on `K` is `K.orthogonalExtend f`.
-/
theorem eq_orthogonalExtend {g : E ≃ₗᵢ[𝕜] E} {f : K ≃ₗᵢ[𝕜] K} (hK : ∀ x : K, g x = f x)
    (hK' : ∀ x ∈ Kᗮ, g x = x) : g = K.orthogonalExtend f := by
  ext x
  conv_lhs => rw [← K.starProjection_add_starProjection_orthogonal x]
  rw [map_add, orthogonalExtend_apply, hK' _ (Kᗮ.starProjection_apply_mem x)]
  congr 1
  exact hK (K.orthogonalProjectionOnto x)

@[simp]
theorem orthogonalExtend_refl :
    K.orthogonalExtend (LinearIsometryEquiv.refl 𝕜 K) = LinearIsometryEquiv.refl 𝕜 E :=
  (K.eq_orthogonalExtend (fun _ ↦ rfl) fun _ _ ↦ rfl).symm

theorem orthogonalExtend_trans (f g : K ≃ₗᵢ[𝕜] K) :
    (K.orthogonalExtend f).trans (K.orthogonalExtend g) = K.orthogonalExtend (f.trans g) :=
  K.eq_orthogonalExtend
    (fun x ↦ by rw [LinearIsometryEquiv.trans_apply, orthogonalExtend_apply_coe,
      orthogonalExtend_apply_coe, LinearIsometryEquiv.trans_apply])
    fun x hx ↦ by
      rw [LinearIsometryEquiv.trans_apply, orthogonalExtend_apply_of_mem_orthogonal K _ hx,
        orthogonalExtend_apply_of_mem_orthogonal K _ hx]

theorem orthogonalExtend_mul (f g : K ≃ₗᵢ[𝕜] K) :
    K.orthogonalExtend f * K.orthogonalExtend g = K.orthogonalExtend (f * g) := by
  rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.mul_def, orthogonalExtend_trans]

@[simp]
theorem orthogonalExtend_one : K.orthogonalExtend 1 = 1 :=
  K.orthogonalExtend_refl

/-- `orthogonalExtend` as a group homomorphism `(K ≃ₗᵢ[𝕜] K) →* (E ≃ₗᵢ[𝕜] E)`. -/
@[simps]
def orthogonalExtendMonoidHom : (K ≃ₗᵢ[𝕜] K) →* (E ≃ₗᵢ[𝕜] E) where
  toFun := K.orthogonalExtend
  map_one' := K.orthogonalExtend_one
  map_mul' f g := (K.orthogonalExtend_mul f g).symm

/-- The reflection of `E` in the hyperplane orthogonal to a vector `v ∈ K` is the extension of
the reflection of `K` in the hyperplane of `K` orthogonal to `v`. -/
theorem orthogonalExtend_reflection_orthogonal_span_singleton [FiniteDimensional 𝕜 K] (v : K) :
    K.orthogonalExtend (𝕜 ∙ v)ᗮ.reflection = (𝕜 ∙ (v : E))ᗮ.reflection := by
  symm
  refine K.eq_orthogonalExtend (fun x ↦ ?_) fun x hx ↦ ?_
  · rw [reflection_orthogonal_apply, reflection_orthogonal_apply, reflection_apply,
      reflection_apply, starProjection_singleton, starProjection_singleton]
    simp [coe_inner]
  · exact reflection_mem_subspace_eq_self
      (mem_orthogonal_singleton_iff_inner_right.2 ((K.mem_orthogonal x).1 hx v v.2))

end Submodule

end
