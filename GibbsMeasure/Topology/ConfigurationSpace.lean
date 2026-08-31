module

public import GibbsMeasure.Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Basic

/-!
# Topology and measurability of configuration spaces

This file provides basic topology and measurability facts for configuration spaces of the form
`S → E`.

The main points are:
- The product topology on `S → E` is available via the standard `Pi` instances.
- If `S` is countable and `E` is second-countable Borel, then `S → E` is a `BorelSpace` as well
  (Mathlib instance `Pi.borelSpace`). In particular, the *existing* measurable space on `S → E`
  (the product `MeasurableSpace.pi`) coincides with `borel (S → E)`.

We also record the standard notion of a **cylinder (local) observable**: a function depending only
on finitely many coordinates.
-/

@[expose] public section

namespace MeasureTheory.GibbsMeasure

namespace ConfigurationSpace

open Function

variable {S E : Type*}

/-! ### Cylinder (local) observables -/

/-- A function on `S → E` is a *cylinder function* if it depends on only finitely many coordinates,
i.e. `Function.DependsOn f ↑Λ` for some `Λ : Finset S`. -/
def IsCylinderFunction {F : Type*} (f : (S → E) → F) : Prop :=
  ∃ Λ : Finset S, DependsOn f (Λ : Set S)

namespace IsCylinderFunction

variable {F : Type*} {f g : (S → E) → F}

lemma congr (hf : IsCylinderFunction (S := S) (E := E) f) (hfg : f = g) :
    IsCylinderFunction (S := S) (E := E) g := hfg ▸ hf

lemma const (c : F) : IsCylinderFunction (S := S) (E := E) fun _ ↦ c :=
  ⟨∅, by simpa using (dependsOn_const (α := fun _ : S ↦ E) c).mono (Set.empty_subset _)⟩

lemma comp {G : Type*} (F' : F → G) (hf : IsCylinderFunction (S := S) (E := E) f) :
    IsCylinderFunction (S := S) (E := E) fun σ ↦ F' (f σ) :=
  hf.imp fun _ h ↦ DependsOn.comp F' h

lemma comp₂ {G H : Type*} (F' : F → G → H) {g : (S → E) → G}
    (hf : IsCylinderFunction (S := S) (E := E) f)
    (hg : IsCylinderFunction (S := S) (E := E) g) :
    IsCylinderFunction (S := S) (E := E) fun σ ↦ F' (f σ) (g σ) := by
  classical
  obtain ⟨Λf, hf⟩ := hf
  obtain ⟨Λg, hg⟩ := hg
  exact ⟨Λf ∪ Λg, DependsOn.comp₂ F'
    (hf.mono (by simpa using Set.subset_union_left))
    (hg.mono (by simpa using Set.subset_union_right))⟩

lemma add [Add F] (hf : IsCylinderFunction (S := S) (E := E) f)
    (hg : IsCylinderFunction (S := S) (E := E) g) :
    IsCylinderFunction (S := S) (E := E) fun σ ↦ f σ + g σ := comp₂ (· + ·) hf hg

lemma mul [Mul F] (hf : IsCylinderFunction (S := S) (E := E) f)
    (hg : IsCylinderFunction (S := S) (E := E) g) :
    IsCylinderFunction (S := S) (E := E) fun σ ↦ f σ * g σ := comp₂ (· * ·) hf hg

lemma smul {𝕜 : Type*} [SMul 𝕜 F] {c : 𝕜} (hf : IsCylinderFunction (S := S) (E := E) f) :
    IsCylinderFunction (S := S) (E := E) fun σ ↦ c • f σ := comp _ hf

lemma neg [Neg F] (hf : IsCylinderFunction (S := S) (E := E) f) :
    IsCylinderFunction (S := S) (E := E) fun σ ↦ -f σ := comp _ hf

lemma sub [Sub F] (hf : IsCylinderFunction (S := S) (E := E) f)
    (hg : IsCylinderFunction (S := S) (E := E) g) :
    IsCylinderFunction (S := S) (E := E) fun σ ↦ f σ - g σ := comp₂ (· - ·) hf hg

end IsCylinderFunction

/-! ### Borel measurability alignment for countable products -/

variable (S E)

/-- If `S` is countable and `E` is second-countable Borel, then the product measurable space on
`S → E` is the Borel σ-algebra of the product topology. -/
lemma measurableSpace_pi_eq_borel
    [Countable S] [TopologicalSpace E] [MeasurableSpace E] [SecondCountableTopology E] [BorelSpace E] :
    (inferInstance : MeasurableSpace (S → E)) = borel (S → E) := by
  simpa using (BorelSpace.measurable_eq (α := S → E))

end ConfigurationSpace

end MeasureTheory.GibbsMeasure
