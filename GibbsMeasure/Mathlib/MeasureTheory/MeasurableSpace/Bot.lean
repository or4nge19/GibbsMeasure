module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic

public section

open Function Set MeasureTheory

variable {α β : Type*}

/-- On an empty domain, any map is constant at the default value of the codomain. -/
lemma exists_eq_const_of_not_nonempty [Inhabited β] {f : α → β} (hα : ¬Nonempty α) :
    ∃ c : β, f = fun _ ↦ c :=
  ⟨default, funext fun x => False.elim (hα ⟨x⟩)⟩

variable [MeasurableSpace α] [MeasurableSpace β]

/-- A `⊥`-measurable map into a space with measurable singletons is constant on a nonempty domain. -/
lemma exists_eq_const_of_measurable_bot_of_nonempty [Nonempty α] [MeasurableSingletonClass β]
    {f : α → β} (hf : Measurable[⊥] f) : ∃ c : β, f = fun _ ↦ c := by
  classical
  let x0 : α := Classical.choice ‹Nonempty α›
  let c : β := f x0
  refine ⟨c, ?_⟩
  funext x
  have hpre : MeasurableSet[⊥] (f ⁻¹' ({c} : Set β)) :=
    hf (measurableSet_singleton c)
  have hbot :
      f ⁻¹' ({c} : Set β) = ∅ ∨ f ⁻¹' ({c} : Set β) = Set.univ :=
    (MeasurableSpace.measurableSet_bot_iff (s := f ⁻¹' ({c} : Set β))).1 hpre
  have hx0 : x0 ∈ f ⁻¹' ({c} : Set β) := by simp [c]
  have huniv : f ⁻¹' ({c} : Set β) = Set.univ := by
    rcases hbot with h0 | huniv
    · rw [h0] at hx0
      exact absurd hx0 (Set.notMem_empty x0)
    · exact huniv
  have hx : x ∈ f ⁻¹' ({c} : Set β) := by simp [huniv]
  simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx

/-- A `⊥`-measurable map into a measurable-singleton codomain is globally constant. -/
lemma exists_eq_const_of_measurable_bot [Inhabited β] [MeasurableSingletonClass β] {f : α → β}
    (hf : Measurable[⊥] f) : ∃ c : β, f = fun _ ↦ c := by
  classical
  cases isEmpty_or_nonempty α with
  | inl hα => exact exists_eq_const_of_not_nonempty (not_nonempty_iff.mpr hα)
  | inr _ => exact exists_eq_const_of_measurable_bot_of_nonempty hf
