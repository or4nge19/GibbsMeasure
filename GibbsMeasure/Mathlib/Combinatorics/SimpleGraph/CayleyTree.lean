/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.List.Chain

/-!
# Cayley trees

Georgii §12.2 works on `𝒞𝒯(d)`, "the unique connected tree with `|∂i| = d + 1` for all `i`".
`SimpleGraph.IsCayleyTree G d` is that property: `G` is a tree, regular of degree `d + 1`.

Georgii also uses that `𝒞𝒯(d)` is bipartite (for the alternating boundary laws of the
antiferromagnetic case). That is Mathlib's `SimpleGraph.IsTree.isBipartite` (a tree is
`2`-colourable), which holds for every tree; `SimpleGraph.IsTree.exists_bool_coloring` repackages
it as Georgii's decomposition `S = S₀ ⊔ S₁`, i.e. a `c : V → Bool` with `c u ≠ c v` along every
bond.

`SimpleGraph.hasse ℤ` is a Cayley tree of degree `1` (`SimpleGraph.isCayleyTree_hasse_int`); the
proof that it is acyclic goes through the general "cut" lemma
`SimpleGraph.Walk.mem_of_adj_closed`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Reachability and cuts -/

/-- A set closed under the adjacency relation is closed under walks. -/
lemma Walk.mem_of_adj_closed {S : Set V} (hS : ∀ ⦃u v⦄, G.Adj u v → u ∈ S → v ∈ S) :
    ∀ {u v : V}, G.Walk u v → u ∈ S → v ∈ S
  | _, _, Walk.nil, hu => hu
  | _, _, Walk.cons h p, hu => Walk.mem_of_adj_closed hS p (hS h hu)

/-- If `S` is closed under adjacency, no vertex of `S` is reachable from outside `S`. -/
lemma not_reachable_of_adj_closed {S : Set V} (hS : ∀ ⦃u v⦄, G.Adj u v → u ∈ S → v ∈ S)
    {u v : V} (hu : u ∈ S) (hv : v ∉ S) : ¬ G.Reachable u v := by
  rintro ⟨p⟩
  exact hv (p.mem_of_adj_closed hS hu)

/-- **Georgii §12.2, the bipartition of a tree.** A tree admits a two-valued colouring of its
vertices: Mathlib's `SimpleGraph.IsTree.isBipartite` says a tree is `2`-colourable, and `Fin 2`
is `Bool`. -/
theorem IsTree.exists_bool_coloring (hG : G.IsTree) :
    ∃ c : V → Bool, ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v := by
  obtain ⟨C⟩ := hG.isBipartite
  refine ⟨fun v ↦ decide ((C v : Fin 2) = 1), fun u v huv hcon ↦ C.valid huv ?_⟩
  rw [decide_eq_decide] at hcon
  have hiff : ((C u : Fin 2).val = 1) ↔ ((C v : Fin 2).val = 1) := by
    simpa [Fin.ext_iff] using hcon
  have hu : ((C u : Fin 2)).val < 2 := (C u).isLt
  have hv : ((C v : Fin 2)).val < 2 := (C v).isLt
  exact Fin.ext (by omega)

/-! ### Cayley trees -/

/-- **Georgii §12.2.** The Cayley tree `𝒞𝒯(d)`: a tree in which every vertex has exactly `d + 1`
neighbours. Georgii's `S = 𝒞𝒯(d)` is the (unique up to isomorphism) such graph; every statement
of §12.2 is a statement about an arbitrary graph with this property. -/
structure IsCayleyTree (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ) : Prop where
  /-- A Cayley tree is a tree. -/
  isTree : G.IsTree
  /-- Every vertex of `𝒞𝒯(d)` has `d + 1` neighbours. -/
  isRegularOfDegree : G.IsRegularOfDegree (d + 1)

namespace IsCayleyTree

variable [G.LocallyFinite] {d : ℕ} (hG : G.IsCayleyTree d)
include hG

lemma isAcyclic : G.IsAcyclic := hG.isTree.isAcyclic

lemma connected : G.Connected := hG.isTree.connected

lemma nonempty : Nonempty V := hG.connected.nonempty

/-- A Cayley tree is bipartite (Mathlib's `SimpleGraph.IsTree.isBipartite`); this is Georgii's
decomposition `S = S₀ ∪ S₁` used for alternating boundary laws. -/
lemma isBipartite : G.IsBipartite := hG.isTree.isBipartite

/-- **Georgii §12.2, the bipartition `S = S₀ ⊔ S₁`.** A Cayley tree carries a two-valued colouring
of its vertices, i.e. a decomposition `S = S₀ ⊔ S₁` with `|b ∩ S₀| = |b ∩ S₁| = 1` for every bond
`b ∈ B`. This is what Georgii's *alternating* boundary laws are indexed by. -/
lemma exists_bool_coloring : ∃ c : V → Bool, ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v :=
  hG.isTree.exists_bool_coloring

lemma card_neighborFinset (i : V) : (G.neighborFinset i).card = d + 1 := by
  rw [G.card_neighborFinset_eq_degree, hG.isRegularOfDegree i]

/-- Along an oriented bond `ij` of `𝒞𝒯(d)` there are exactly `d` other neighbours of `i`: this is
the `d` in Georgii's equations (12.16), (12.21), (12.22). -/
lemma card_neighborFinset_erase [DecidableEq V] {i j : V} (hij : G.Adj i j) :
    ((G.neighborFinset i).erase j).card = d := by
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset i j).2 hij), hG.card_neighborFinset,
    Nat.add_sub_cancel]

/-- Every vertex of a Cayley tree has a neighbour. -/
lemma exists_adj_right (i : V) : ∃ j : V, G.Adj i j := by
  have hcard : (G.neighborFinset i).card = d + 1 := hG.card_neighborFinset i
  obtain ⟨j, hj⟩ := Finset.card_pos.1 (by rw [hcard]; exact Nat.succ_pos d)
  exact ⟨j, (G.mem_neighborFinset i j).1 hj⟩

/-- A Cayley tree has at least one bond. -/
lemma exists_adj : ∃ i j : V, G.Adj i j := by
  obtain ⟨i⟩ := hG.nonempty
  obtain ⟨j, hj⟩ := hG.exists_adj_right i
  exact ⟨i, j, hj⟩

end IsCayleyTree

/-! ### `ℤ` is the Cayley tree of degree `1` -/

/-- `SimpleGraph.hasse ℤ` is acyclic: deleting the bond `{i, i+1}` separates `{k ≤ i}` from
`{k ≥ i + 1}`. -/
theorem isAcyclic_hasse_int : (hasse ℤ).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  have key : ∀ i : ℤ, (hasse ℤ).IsBridge s(i, i + 1) := by
    intro i
    rw [isBridge_iff]
    refine not_reachable_of_adj_closed (S := {k : ℤ | k ≤ i}) ?_ (Set.mem_ofPred.2 le_rfl)
      (by simp)
    rintro u v huv hu
    rw [deleteEdges_adj] at huv
    obtain ⟨hadj, hne⟩ := huv
    rcases (hasse_int_adj u v).1 hadj with h | h
    · by_cases hui : u = i
      · exact absurd (by rw [Set.mem_singleton_iff, hui, ← h, hui]) hne
      · have : u < i := lt_of_le_of_ne hu hui
        simp only [Set.mem_ofPred_eq] at hu ⊢
        omega
    · simp only [Set.mem_ofPred_eq] at hu ⊢
      omega
  intro u v huv
  rcases (hasse_int_adj u v).1 huv with h | h
  · rw [← h]; exact key u
  · rw [Sym2.eq_swap, ← h]; exact key v

theorem isTree_hasse_int : (hasse ℤ).IsTree where
  connected := by
    have : Nonempty ℤ := ⟨0⟩
    exact ⟨hasse_preconnected_of_succ ℤ⟩
  isAcyclic := isAcyclic_hasse_int

theorem isRegularOfDegree_hasse_int : (hasse ℤ).IsRegularOfDegree 2 := by
  intro i
  rw [← card_neighborFinset_eq_degree, neighborFinset_hasse_int]
  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]

/-- **`ℤ` is Georgii's `𝒞𝒯(1)`**: the Cayley tree of degree `1`. -/
theorem isCayleyTree_hasse_int : (hasse ℤ).IsCayleyTree 1 where
  isTree := isTree_hasse_int
  isRegularOfDegree := isRegularOfDegree_hasse_int

end SimpleGraph

/-! ### The Cayley tree `𝒞𝒯(d)` exists for every `d`

Georgii's `𝒞𝒯(d)` is realised as the Cayley graph of the free product of `d + 1` copies of
`ℤ/2`: the vertices are the *reduced words* over `Fin (d + 1)`, i.e. the lists of letters with no
two consecutive letters equal, and two words are adjacent when one is obtained from the other by
appending a single letter. -/

/-- A **reduced word** over `Fin n`: a list of letters in which no two consecutive letters agree.
Reduced words are the normal forms of the free product of `n` copies of `ℤ/2`; for `n = d + 1`
they are the vertices of Georgii's Cayley tree `𝒞𝒯(d)`
(`SimpleGraph.isCayleyTree_reducedWordTree`). -/
abbrev ReducedWord (n : ℕ) : Type := {l : List (Fin n) // l.IsChain (· ≠ ·)}

namespace ReducedWord

variable {n : ℕ}

/-- The empty word. -/
def nil : ReducedWord n := ⟨[], List.isChain_nil⟩

@[simp] lemma coe_nil : (nil : ReducedWord n).1 = [] := rfl

lemma isChain_append_singleton {w : ReducedWord n} {a : Fin n} (ha : w.1.getLast? ≠ some a) :
    (w.1 ++ [a]).IsChain (· ≠ ·) := by
  refine w.2.append (List.isChain_singleton a) fun x hx y hy ↦ ?_
  rw [Option.mem_def] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some_inj] at hy
  subst hy
  exact fun hxy ↦ ha (hxy ▸ hx)

/-- The `a`-th neighbour of the reduced word `w`: append the letter `a` if `a` is not the last
letter of `w`, and delete the last letter if it is. This is left multiplication by the `a`-th
generator in the free product of `n` copies of `ℤ/2`. -/
def step (w : ReducedWord n) (a : Fin n) : ReducedWord n :=
  if ha : w.1.getLast? = some a then ⟨w.1.dropLast, w.2.dropLast⟩
  else ⟨w.1 ++ [a], isChain_append_singleton ha⟩

lemma step_of_getLast? {w : ReducedWord n} {a : Fin n} (ha : w.1.getLast? = some a) :
    (step w a).1 = w.1.dropLast := by simp [step, ha]

lemma step_of_getLast?_ne {w : ReducedWord n} {a : Fin n} (ha : w.1.getLast? ≠ some a) :
    (step w a).1 = w.1 ++ [a] := by simp [step, ha]

lemma step_injective (w : ReducedWord n) : Function.Injective (step w) := by
  intro a b hab
  have hab' : (step w a).1 = (step w b).1 := congrArg Subtype.val hab
  by_cases ha : w.1.getLast? = some a <;> by_cases hb : w.1.getLast? = some b
  · exact Option.some_injective _ (ha.symm.trans hb)
  · rw [step_of_getLast? ha, step_of_getLast?_ne hb] at hab'
    have := congrArg List.length hab'
    simp only [List.length_dropLast, List.length_append, List.length_cons,
      List.length_nil] at this
    omega
  · rw [step_of_getLast?_ne ha, step_of_getLast? hb] at hab'
    have := congrArg List.length hab'
    simp only [List.length_dropLast, List.length_append, List.length_cons,
      List.length_nil] at this
    omega
  · rw [step_of_getLast?_ne ha, step_of_getLast?_ne hb] at hab'
    simpa using hab'

end ReducedWord

namespace SimpleGraph

open ReducedWord

variable {n : ℕ}

/-- **The Cayley tree of degree `n - 1`.** The graph on reduced words over `Fin n` in which two
words are adjacent when one is obtained from the other by appending a letter. For `n = d + 1`
this is Georgii's `𝒞𝒯(d)` (`SimpleGraph.isCayleyTree_reducedWordTree`). -/
def reducedWordTree (n : ℕ) : SimpleGraph (ReducedWord n) where
  Adj u v := (∃ a, v.1 = u.1 ++ [a]) ∨ (∃ a, u.1 = v.1 ++ [a])
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun u h ↦ by
    rcases h with ⟨a, ha⟩ | ⟨a, ha⟩ <;> simpa using congrArg List.length ha⟩

lemma reducedWordTree_adj {u v : ReducedWord n} :
    (reducedWordTree n).Adj u v ↔ (∃ a, v.1 = u.1 ++ [a]) ∨ (∃ a, u.1 = v.1 ++ [a]) := Iff.rfl

/-- The neighbours of a reduced word `w` are exactly the `step w a`, `a : Fin n`. -/
lemma reducedWordTree_adj_iff_exists_step {u v : ReducedWord n} :
    (reducedWordTree n).Adj u v ↔ ∃ a, v = step u a := by
  constructor
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · have hlast : u.1.getLast? ≠ some a := fun hcon ↦ by
        have h := (List.isChain_append.1 (ha ▸ v.2)).2.2
        exact h a hcon a (by simp) rfl
      exact ⟨a, Subtype.ext (ha.trans (step_of_getLast?_ne hlast).symm)⟩
    · refine ⟨a, Subtype.ext ?_⟩
      rw [step_of_getLast? (by rw [ha, List.getLast?_concat]), ha, List.dropLast_concat]
  · rintro ⟨a, rfl⟩
    by_cases ha : u.1.getLast? = some a
    · exact Or.inr ⟨a, by rw [step_of_getLast? ha, List.dropLast_append_getLast? a ha]⟩
    · exact Or.inl ⟨a, step_of_getLast?_ne ha⟩

instance : (reducedWordTree n).LocallyFinite := fun w ↦
  Fintype.ofFinset (Finset.univ.image (step w)) fun v ↦ by
    simp [mem_neighborSet, reducedWordTree_adj_iff_exists_step, eq_comm]

lemma neighborFinset_reducedWordTree (w : ReducedWord n) :
    (reducedWordTree n).neighborFinset w = Finset.univ.image (step w) := by
  ext v
  simp [mem_neighborFinset, reducedWordTree_adj_iff_exists_step, eq_comm]

/-- Every vertex of `reducedWordTree n` has exactly `n` neighbours. -/
theorem isRegularOfDegree_reducedWordTree : (reducedWordTree n).IsRegularOfDegree n := fun w ↦ by
  rw [← card_neighborFinset_eq_degree, neighborFinset_reducedWordTree,
    Finset.card_image_of_injective _ (step_injective w), Finset.card_univ, Fintype.card_fin]

private lemma reachable_nil_of_length_le (m : ℕ) :
    ∀ w : ReducedWord n, w.1.length ≤ m → (reducedWordTree n).Reachable w nil := by
  induction m with
  | zero =>
    intro w hw
    exact (Subtype.ext (List.length_eq_zero_iff.1 (Nat.le_zero.1 hw)) : w = nil) ▸ Reachable.refl _
  | succ m ih =>
    intro w hw
    rcases eq_or_ne w.1 [] with h | h
    · exact (Subtype.ext h : w = nil) ▸ Reachable.refl _
    · set a := w.1.getLast h with ha
      have hlast : w.1.getLast? = some a := List.getLast?_eq_some_getLast h
      have hadj : (reducedWordTree n).Adj w (step w a) :=
        reducedWordTree_adj_iff_exists_step.2 ⟨a, rfl⟩
      refine hadj.reachable.trans (ih _ ?_)
      rw [step_of_getLast? hlast, List.length_dropLast]
      have : w.1.length ≠ 0 := fun hcon ↦ h (List.length_eq_zero_iff.1 hcon)
      omega

theorem connected_reducedWordTree : (reducedWordTree n).Connected := by
  have : Nonempty (ReducedWord n) := ⟨nil⟩
  exact ⟨fun u v ↦ (reachable_nil_of_length_le _ u le_rfl).trans
    (reachable_nil_of_length_le _ v le_rfl).symm⟩

private lemma isBridge_reducedWordTree_aux {u v : ReducedWord n} {a : Fin n}
    (hv : v.1 = u.1 ++ [a]) : (reducedWordTree n).IsBridge s(u, v) := by
  rw [isBridge_iff]
  intro hr
  refine not_reachable_of_adj_closed (G := (reducedWordTree n).deleteEdges {s(u, v)})
    (S := {x : ReducedWord n | v.1 <+: x.1}) ?_ (Set.mem_ofPred.2 List.prefix_rfl) ?_ hr.symm
  · rintro x y hxy hx
    have hx' : v.1 <+: x.1 := hx
    rw [deleteEdges_adj] at hxy
    obtain ⟨hadj, hne⟩ := hxy
    rcases hadj with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact Set.mem_ofPred.2 (hb ▸ hx'.trans (List.prefix_append _ _))
    · rw [hb] at hx'
      rcases List.prefix_concat_iff.1 hx' with heq | hpre
      · exfalso
        obtain ⟨hyu, -⟩ := List.append_inj' (heq.symm.trans hv) rfl
        have hyu' : y = u := Subtype.ext hyu
        have hxv : x = v := Subtype.ext (hb.trans heq.symm)
        rw [hxv, hyu'] at hne
        exact hne (by rw [Sym2.eq_swap]; exact rfl)
      · exact Set.mem_ofPred.2 hpre
  · intro hcon
    have hlen := List.IsPrefix.length_le (show v.1 <+: u.1 from hcon)
    rw [hv] at hlen
    simp at hlen

theorem isAcyclic_reducedWordTree : (reducedWordTree n).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rcases huv with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact isBridge_reducedWordTree_aux ha
  · rw [Sym2.eq_swap]; exact isBridge_reducedWordTree_aux ha

theorem isTree_reducedWordTree : (reducedWordTree n).IsTree where
  connected := connected_reducedWordTree
  isAcyclic := isAcyclic_reducedWordTree

/-- **Georgii's `𝒞𝒯(d)` exists for every `d`.** The graph of reduced words over `Fin (d + 1)`
is a tree in which every vertex has exactly `d + 1` neighbours. -/
theorem isCayleyTree_reducedWordTree (d : ℕ) : (reducedWordTree (d + 1)).IsCayleyTree d where
  isTree := isTree_reducedWordTree
  isRegularOfDegree := isRegularOfDegree_reducedWordTree

end SimpleGraph
