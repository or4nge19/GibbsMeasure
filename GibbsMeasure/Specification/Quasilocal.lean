module

public import GibbsMeasure.Topology.ConfigurationSpace
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Continuous quasilocal functions (Feller version)

In statistical mechanics, *local observables* are functions depending only on finitely many spins.
This file formalizes the **continuous/Feller** version of quasilocal observables: a bounded
continuous observable is quasilocal if it is in the uniform closure of bounded continuous cylinder
observables.

Georgii's Definition 2.20 is more general: local functions are bounded measurable functions
measurable with respect to a finite-volume σ-algebra, and quasilocal functions are the uniform
closure of those local measurable functions. The continuous API here is intentionally named and
documented as the Feller version; it is the right interface for weak-topology/Feller arguments, not
a replacement for the full measurable Georgii algebra.

This file sets up the basic API:
- `ConfigurationSpace.IsCylinderFunction` (defined in `Topology/ConfigurationSpace.lean`);
- `BoundedContinuousFunction.cylinderFunctions`: the submodule of bounded continuous cylinder
  functions;
- `BoundedContinuousFunction.fellerQuasilocalFunctions`: its topological (uniform) closure;
- `BoundedContinuousFunction.IsFellerQuasilocal`: membership predicate.

We deliberately keep this file purely functional-analytic: it does *not* yet talk about
specifications. The latter will require a Feller-type hypothesis to act on bounded continuous
functions.
-/

@[expose] public section

open scoped Topology

namespace BoundedContinuousFunction

open GibbsMeasure.ConfigurationSpace

variable {S E F : Type*}
variable [TopologicalSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The submodule of **cylinder functions** inside `C_b(S → E, F)`. -/
noncomputable def cylinderFunctions
    (S E F : Type*) [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Submodule ℝ ((S → E) →ᵇ F) where
  carrier := {f | IsCylinderFunction (S := S) (E := E) (fun σ => f σ)}
  zero_mem' := by
    simpa using
      (GibbsMeasure.ConfigurationSpace.IsCylinderFunction.const (S := S) (E := E) (F := F) 0)
  add_mem' := by
    intro f g hf hg
    -- Stability under addition is a property of cylinder functions on `(S → E)`.
    exact GibbsMeasure.ConfigurationSpace.IsCylinderFunction.add (S := S) (E := E) hf hg
  smul_mem' := by
    intro c f hf
    exact GibbsMeasure.ConfigurationSpace.IsCylinderFunction.smul (S := S) (E := E) (c := c) hf

/-- The submodule of **continuous/Feller quasilocal functions**: the uniform closure of
`cylinderFunctions` inside `C_b(S → E, F)`. -/
noncomputable def fellerQuasilocalFunctions (S E F : Type*) [TopologicalSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Submodule ℝ ((S → E) →ᵇ F) :=
  (cylinderFunctions (S := S) (E := E) (F := F)).topologicalClosure

/-- Compatibility alias for the continuous/Feller quasilocal submodule. Prefer
`fellerQuasilocalFunctions` in new declarations that need to avoid confusion with Georgii's full
bounded-measurable quasilocal algebra. -/
noncomputable abbrev quasilocalFunctions (S E F : Type*) [TopologicalSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Submodule ℝ ((S → E) →ᵇ F) :=
  fellerQuasilocalFunctions (S := S) (E := E) (F := F)

/-- A bounded continuous function is **Feller-quasilocal** if it belongs to
`fellerQuasilocalFunctions`. -/
def IsFellerQuasilocal (f : (S → E) →ᵇ F) : Prop :=
  f ∈ fellerQuasilocalFunctions (S := S) (E := E) (F := F)

/-- Compatibility alias for the continuous/Feller quasilocal predicate. Prefer
`IsFellerQuasilocal` when the distinction from Georgii's measurable quasilocality matters. -/
abbrev IsQuasilocal (f : (S → E) →ᵇ F) : Prop :=
  IsFellerQuasilocal f

@[simp] lemma mem_cylinderFunctions {f : (S → E) →ᵇ F} :
    f ∈ cylinderFunctions (S := S) (E := E) (F := F) ↔
      IsCylinderFunction (S := S) (E := E) (fun σ => f σ) := by
  rfl

@[simp] lemma mem_quasilocalFunctions {f : (S → E) →ᵇ F} :
    f ∈ quasilocalFunctions (S := S) (E := E) (F := F) ↔ IsQuasilocal f := by
  rfl

/-- Membership in the continuous/Feller quasilocal submodule. -/
@[simp] lemma mem_fellerQuasilocalFunctions {f : (S → E) →ᵇ F} :
    f ∈ fellerQuasilocalFunctions (S := S) (E := E) (F := F) ↔ IsFellerQuasilocal f := by
  rfl

lemma cylinderFunctions_le_quasilocalFunctions :
    cylinderFunctions (S := S) (E := E) (F := F) ≤ quasilocalFunctions (S := S) (E := E) (F := F) :=
  Submodule.le_topologicalClosure _

lemma cylinderFunctions_le_fellerQuasilocalFunctions :
    cylinderFunctions (S := S) (E := E) (F := F) ≤
      fellerQuasilocalFunctions (S := S) (E := E) (F := F) :=
  Submodule.le_topologicalClosure _

lemma isQuasilocal_of_mem_cylinderFunctions {f : (S → E) →ᵇ F}
    (hf : f ∈ cylinderFunctions (S := S) (E := E) (F := F)) :
    IsQuasilocal f :=
  cylinderFunctions_le_quasilocalFunctions (S := S) (E := E) (F := F) hf

lemma isFellerQuasilocal_of_mem_cylinderFunctions {f : (S → E) →ᵇ F}
    (hf : f ∈ cylinderFunctions (S := S) (E := E) (F := F)) :
    IsFellerQuasilocal f :=
  cylinderFunctions_le_fellerQuasilocalFunctions (S := S) (E := E) (F := F) hf

end BoundedContinuousFunction
