/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.PeierlsEstimate
public import GibbsMeasure.Model.ShiftAverage

/-!
# Georgii Theorem (6.9): spontaneous magnetisation of the 2D Ising ferromagnet

The plus phase of Georgii's proof of (6.9) is a cluster point, in the topology of local
convergence, of the cube-averaged `+`-boundary distributions `plusCubeAverage`; averaging over the
cube translates is what makes the limit shift invariant (Georgii (5.20)(1)).  The cluster point is
not unique *a priori*, so the construction is packaged here as three statements about an arbitrary
cluster point — `mem_GP_of_mapClusterPt_plusCubeAverage`,
`measurePreserving_shift_of_mapClusterPt_plusCubeAverage`,
`eq_false_le_of_mapClusterPt_plusCubeAverage_of_cube` — rather than as a bare existence theorem.
For `β ≥ 0` the cluster point *is* unique and equals the monotone local limit `plusState` of
`GibbsMeasure/Model/PlusPhase.lean`: see `eq_plusState_of_mapClusterPt_plusCubeAverage` there and
`Peierls.plusPhase_eq_plusState` in `GibbsMeasure/Model/LowTemperatureLimit.lean`.
-/

@[expose] public section


open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.Peierls

/-! ### M1: the minus cluster of a site -/

/-- Georgii (6.14): the connected cluster of `a` inside the minus sites of `ζ`. -/
def minusCluster (a : Site) (ζ : Site → Bool) : Set Site :=
  {i | ReachIn (latticeGraph 2) {j | ζ j = false} a i}

lemma mem_minusCluster_self {a : Site} {ζ : Site → Bool} (ha : ζ a = false) :
    a ∈ minusCluster a ζ := ReachIn.refl ha

lemma minusCluster_subset {a : Site} {ζ : Site → Bool} :
    minusCluster a ζ ⊆ {j | ζ j = false} := fun _ h ↦ h.mem_right

lemma eq_false_of_mem_minusCluster {a i : Site} {ζ : Site → Bool} (hi : i ∈ minusCluster a ζ) :
    ζ i = false := minusCluster_subset hi

/-- The minus cluster lies in any volume off which `ζ` is `+1`. -/
lemma minusCluster_subset_of_forall_eq_true {a : Site} {ζ : Site → Bool} {Λ : Set Site}
    (hout : ∀ i ∉ Λ, ζ i = true) : minusCluster a ζ ⊆ Λ := by
  intro i hi
  by_contra h
  have h1 : ζ i = false := eq_false_of_mem_minusCluster hi
  rw [hout i h] at h1
  exact Bool.noConfusion h1

/-- Maximality of the minus cluster. -/
lemma mem_minusCluster_of_adj {a i j : Site} {ζ : Site → Bool} (hi : i ∈ minusCluster a ζ)
    (hadj : (latticeGraph 2).Adj i j) (hj : ζ j = false) : j ∈ minusCluster a ζ :=
  hi.trans (ReachIn.of_adj (minusCluster_subset hi) hj hadj)

/-- Two sites of the minus cluster are joined by a walk inside the cluster. -/
lemma reachIn_minusCluster {a u v : Site} {ζ : Site → Bool} (hu : u ∈ minusCluster a ζ)
    (hv : v ∈ minusCluster a ζ) : ReachIn (latticeGraph 2) (minusCluster a ζ) u v := by
  have huv : ReachIn (latticeGraph 2) {j | ζ j = false} u v := hu.symm.trans hv
  refine huv.induction (P := fun x ↦ ReachIn (latticeGraph 2) (minusCluster a ζ) u x)
    (ReachIn.refl hu) ?_
  intro p q _ hq hpq hup
  exact hup.trans (ReachIn.of_adj hup.mem_right (mem_minusCluster_of_adj hup.mem_right hpq hq) hpq)

/-- The minus cluster is connected. -/
lemma minusCluster_connected {a : Site} {ζ : Site → Bool} (ha : ζ a = false) :
    ((latticeGraph 2).induce (minusCluster a ζ)).Connected :=
  induce_connected_iff.2 ⟨⟨a, mem_minusCluster_self ha⟩, fun _ _ hu hv ↦ reachIn_minusCluster hu hv⟩

/-- Georgii (6.14): every boundary bond of the minus cluster is discordant. -/
lemma edgeBoundary_minusCluster_subset_discordant (a : Site) (ζ : Site → Bool) :
    edgeBoundary (minusCluster a ζ) ⊆ discordant ζ := by
  rintro e ⟨i, hi, j, hj, hadj, rfl⟩
  rw [mem_discordant_mk]
  refine ⟨hadj, ?_⟩
  have h1 : ζ i = false := eq_false_of_mem_minusCluster hi
  have h2 : ζ j = true := by
    rcases Bool.eq_false_or_eq_true (ζ j) with h | h
    · exact h
    · exact absurd (mem_minusCluster_of_adj hi hadj h) hj
  rw [h1, h2]
  simp

lemma outerBoundary_minusCluster_subset_discordant (a : Site) (ζ : Site → Bool) :
    outerBoundary (minusCluster a ζ) ⊆ discordant ζ :=
  (outerBoundary_subset_edgeBoundary _).trans (edgeBoundary_minusCluster_subset_discordant a ζ)

/-! ### M2: walks avoiding a set of bonds, and the interior of a bond set -/

/-- A walk inside `s` has all its edge endpoints in `s`. -/
lemma exists_walk_of_reachIn {s : Set Site} {u v : Site}
    (h : ReachIn (latticeGraph 2) s u v) :
    ∃ w : (latticeGraph 2).Walk u v, ∀ e ∈ w.edges, ∀ x ∈ e, x ∈ s := by
  refine h.induction (P := fun i ↦ ∃ w : (latticeGraph 2).Walk u i, ∀ e ∈ w.edges, ∀ x ∈ e, x ∈ s)
    ⟨SimpleGraph.Walk.nil, by simp⟩ ?_
  rintro p q hp hq hpq ⟨w, hw⟩
  refine ⟨w.concat hpq, fun e he x hx ↦ ?_⟩
  rw [SimpleGraph.Walk.edges_concat] at he
  simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · exact hw e he x hx
  · rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact hp
    · exact hq

/-- `ReachAvoid c i j`: a lattice walk from `i` to `j` using no bond of `c`. -/
def ReachAvoid (c : Set (Sym2 Site)) (i j : Site) : Prop :=
  ∃ w : (latticeGraph 2).Walk i j, ∀ e ∈ w.edges, e ∉ c

/-- `Escapes c i`: `i` reaches arbitrarily distant sites by walks avoiding the bonds of `c`. -/
def Escapes (c : Set (Sym2 Site)) (i : Site) : Prop :=
  ∀ N : ℕ, ∃ j, j ∉ box N ∧ ReachAvoid c i j

/-- The interior of a set of bonds: the sites which cannot escape to infinity avoiding `c`. -/
def interiorOf (c : Set (Sym2 Site)) : Set Site := {i | ¬ Escapes c i}

lemma mem_interiorOf_iff {c : Set (Sym2 Site)} {i : Site} :
    i ∈ interiorOf c ↔ ¬ Escapes c i := Iff.rfl

lemma reachAvoid_of_reachIn {c : Set (Sym2 Site)} {s : Set Site} {u v : Site}
    (hcs : ∀ e ∈ c, ∃ x ∈ e, x ∉ s) (h : ReachIn (latticeGraph 2) s u v) : ReachAvoid c u v := by
  obtain ⟨w, hw⟩ := exists_walk_of_reachIn h
  refine ⟨w, fun e he hec ↦ ?_⟩
  obtain ⟨x, hx, hxs⟩ := hcs e hec
  exact hxs (hw e he x hx)

/-- A site far away from all the bonds of `c` escapes. -/
lemma escapes_of_notMem_box {c : Set (Sym2 Site)} {N : ℕ}
    (hc : ∀ e ∈ c, ∃ x ∈ e, x ∈ box N) {x : Site} (hx : x ∉ box N) : Escapes c x := by
  intro M
  have hKN : (N : ℤ) < max |x 0| |x 1| := lt_of_notMem_box hx
  have hK0 : (0 : ℤ) ≤ max |x 0| |x 1| := le_trans (abs_nonneg _) (le_max_left _ _)
  have hstep := reachIn_corner (N := N) hKN (M + 1)
  have hcast : max |x 0| |x 1| + ((M + 1 : ℕ) : ℤ) = max |x 0| |x 1| + M + 1 := by
    push_cast; ring
  rw [hcast] at hstep
  refine ⟨mk (max |x 0| |x 1| + M + 1) (max |x 0| |x 1| + M + 1), corner_notMem_box (by omega), ?_⟩
  refine reachAvoid_of_reachIn (s := (box N)ᶜ) (fun e he ↦ ?_)
    ((reachIn_corner_of_notMem_box hx).trans hstep)
  obtain ⟨y, hy, hyb⟩ := hc e he
  exact ⟨y, hy, by simpa using hyb⟩

lemma interiorOf_subset_box {c : Set (Sym2 Site)} {N : ℕ}
    (hc : ∀ e ∈ c, ∃ x ∈ e, x ∈ box N) : interiorOf c ⊆ box N := by
  intro x hx
  by_contra h
  exact hx (escapes_of_notMem_box hc h)

lemma escapes_of_adj {c : Set (Sym2 Site)} {i j : Site} (hadj : (latticeGraph 2).Adj i j)
    (hij : s(i, j) ∉ c) (hj : Escapes c j) : Escapes c i := by
  intro N
  obtain ⟨k, hk, hr⟩ := hj N
  obtain ⟨w, hw⟩ := hr
  refine ⟨k, hk, SimpleGraph.Walk.cons hadj w, fun e he ↦ ?_⟩
  rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
  rcases he with rfl | he
  · exact hij
  · exact hw e he

/-- (M2)(b): the edge boundary of the interior of `c` consists of bonds of `c`. -/
lemma edgeBoundary_interiorOf_subset (c : Set (Sym2 Site)) :
    edgeBoundary (interiorOf c) ⊆ c := by
  rintro e ⟨i, hi, j, hj, hadj, rfl⟩
  by_contra hc
  exact hi (escapes_of_adj hadj hc (not_not.1 hj))

/-- (M2)(c): a finite set of sites lies in the interior of its outer boundary. -/
lemma subset_interiorOf_outerBoundary {D : Set Site} (hD : D.Finite) :
    D ⊆ interiorOf (outerBoundary D) := by
  obtain ⟨N, hDN⟩ := exists_subset_box hD
  intro i hi hesc
  obtain ⟨j, hj, hr⟩ := hesc N
  obtain ⟨w, hw⟩ := hr
  obtain ⟨e, he, heOB⟩ :=
    exists_outerBoundary_bond_of_walk_of_mem w hi (mem_outside_of_notMem_box hDN hj)
  exact hw e he heOB

/-- Every site of the infinite outside escapes across the outer boundary. -/
lemma escapes_outerBoundary_of_mem_outside {D : Set Site} (hD : D.Finite) {j : Site}
    (hj : j ∈ outside D) : Escapes (outerBoundary D) j := by
  obtain ⟨N, hDN⟩ := exists_subset_box hD
  intro M
  have h1 : (N : ℤ) ≤ ((max N M : ℕ) : ℤ) := by exact_mod_cast Nat.le_max_left N M
  have h2 : (M : ℤ) ≤ ((max N M : ℕ) : ℤ) := by exact_mod_cast Nat.le_max_right N M
  set z : Site := mk (((max N M : ℕ) : ℤ) + 1) (((max N M : ℕ) : ℤ) + 1) with hz
  have hzN : z ∉ box N := corner_notMem_box (by omega)
  have hzM : z ∉ box M := corner_notMem_box (by omega)
  refine ⟨z, hzM, ?_⟩
  refine reachAvoid_of_reachIn (s := Dᶜ) (fun e he ↦ ?_)
    (reachIn_of_mem_outside hD hj (mem_outside_of_notMem_box hDN hzN))
  obtain ⟨i, hi, j', hj', hadj, rfl⟩ := he
  exact ⟨i, Sym2.mem_mk_left i j', by simpa using hi⟩

/-- (M2): the boundary identity `∂(int c) = c` for `c` the outer boundary of a finite set. -/
lemma edgeBoundary_interiorOf_outerBoundary {D : Set Site} (hD : D.Finite) :
    edgeBoundary (interiorOf (outerBoundary D)) = outerBoundary D := by
  refine Set.Subset.antisymm (edgeBoundary_interiorOf_subset _) ?_
  rintro e ⟨i, hi, j, hj, hadj, rfl⟩
  rw [mem_edgeBoundary_mk]
  exact ⟨hadj, Or.inl ⟨subset_interiorOf_outerBoundary hD hi,
    fun h ↦ h (escapes_outerBoundary_of_mem_outside hD hj)⟩⟩

/-- (M2)(d): the interior of the outer boundary stays in any box containing `D`. -/
lemma interiorOf_outerBoundary_subset_box {D : Set Site} {N : ℕ} (hDN : D ⊆ box N) :
    interiorOf (outerBoundary D) ⊆ box N := by
  refine interiorOf_subset_box (fun e he ↦ ?_)
  obtain ⟨i, hi, j, hj, hadj, rfl⟩ := he
  exact ⟨i, Sym2.mem_mk_left i j, hDN hi⟩

/-! ### The cube as a box -/

lemma coe_cube_eq_box (N : ℕ) : ((cube 2 N : Finset Site) : Set Site) = box N := by
  ext x
  simp only [Finset.mem_coe, mem_cube, box, Set.mem_ofPred_eq]
  refine forall_congr' fun k ↦ ?_
  rw [Int.abs_eq_natAbs]
  exact ⟨fun h ↦ by exact_mod_cast h, fun h ↦ by exact_mod_cast h⟩

/-! ### M3: the contour estimate for interior-closed bond sets -/

/-- **Georgii (6.15)** for a bond set which is the edge boundary of its own interior. -/
lemma isingSpecification_subset_discordant_le (β : ℝ) {Λ : Finset Site} {c : Finset (Sym2 Site)}
    (hsub : interiorOf ↑c ⊆ ↑Λ) (hbd : edgeBoundary (interiorOf ↑c) = ↑c) (ω : Site → Bool) :
    isingSpecification (latticeGraph 2) 1 0 β Λ ω
        {ζ : Site → Bool | (↑c : Set (Sym2 Site)) ⊆ discordant ζ} ≤
      ENNReal.ofReal (Real.exp (-2 * β * c.card)) := by
  classical
  set D : Finset Site := Λ.filter (fun x ↦ x ∈ interiorOf (↑c : Set (Sym2 Site))) with hD
  have hDcoe : (↑D : Set Site) = interiorOf (↑c : Set (Sym2 Site)) := by
    ext x
    simp only [hD, Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hsub h, h⟩⟩
  have hDΛ : D ⊆ Λ := Finset.filter_subset _ _
  have hEB : edgeBoundary (↑D : Set Site) = (↑c : Set (Sym2 Site)) := by rw [hDcoe, hbd]
  have hcard : (edgeBoundary (↑D : Set Site)).ncard = c.card := by
    rw [hEB, Set.ncard_coe_finset]
  have hev : {ζ : Site → Bool | (↑c : Set (Sym2 Site)) ⊆ discordant ζ}
      = {ζ : Site → Bool | edgeBoundary (↑D : Set Site) ⊆ discordant ζ} := by rw [hEB]
  rw [hev]
  have h := isingSpecification_edgeBoundary_subset_discordant_le β hDΛ ω
  rwa [hcard] at h

/-! ### M4: the covering of the event `σ_a = -1` by contours -/

/-- Contour candidates: connected bond sets of `m` bonds through a fixed anchor bond, whose
interior is closed and contained in `Λ`. -/
def contourCandidates (Λ : Finset Site) (e₀ : Sym2 Site) (m : ℕ) : Set (Finset (Sym2 Site)) :=
  {c | c ∈ connectedBondSets e₀ m ∧
    edgeBoundary (interiorOf (↑c : Set (Sym2 Site))) = (↑c : Set (Sym2 Site)) ∧
    interiorOf (↑c : Set (Sym2 Site)) ⊆ (↑Λ : Set Site)}

lemma finite_contourCandidates (Λ : Finset Site) (e₀ : Sym2 Site) (m : ℕ) :
    (contourCandidates Λ e₀ m).Finite :=
  (finite_connectedBondSets e₀ m).subset fun _ h ↦ h.1

/-- The contour candidates as a finset. -/
def contourFinset (Λ : Finset Site) (e₀ : Sym2 Site) (m : ℕ) : Finset (Finset (Sym2 Site)) :=
  (finite_contourCandidates Λ e₀ m).toFinset

lemma mem_contourFinset {Λ : Finset Site} {e₀ : Sym2 Site} {m : ℕ} {c : Finset (Sym2 Site)} :
    c ∈ contourFinset Λ e₀ m ↔ c ∈ contourCandidates Λ e₀ m :=
  Set.Finite.mem_toFinset _

/-- A weakening of Georgii (6.13) (`ℓ · 3 ^ (ℓ - 1)` circuits of length `ℓ` surrounding `a`): at
most `4096 ^ m` plaquette-connected bond sets of `m` bonds contain a given bond.  Georgii's own
count is `PeierlsSharp.ncard_anchored_circuits_le`. -/
lemma card_contourFinset_le (Λ : Finset Site) (e₀ : Sym2 Site) (m : ℕ) :
    (contourFinset Λ e₀ m).card ≤ 4096 ^ m := by
  have h1 : ((contourFinset Λ e₀ m : Finset (Finset (Sym2 Site))) : Set (Finset (Sym2 Site)))
      = contourCandidates Λ e₀ m := Set.Finite.coe_toFinset _
  refine le_trans ?_ (ncard_connectedBondSets_le_pow e₀ m)
  rw [← Set.ncard_coe_finset (contourFinset Λ e₀ m), h1]
  exact Set.ncard_le_ncard (fun c hc ↦ hc.1) (finite_connectedBondSets e₀ m)

/-- The union of the contour events of length `ℓ + 1` anchored on the horizontal half-line
from `a`. -/
def contourUnion (N : ℕ) (a : Site) (l : ℕ) : Set (Site → Bool) :=
  ⋃ k ∈ Finset.range (l + 1),
    ⋃ c ∈ contourFinset (cube 2 N) s(a + k • e0, a + (k + 1) • e0) (l + 1),
      {ζ : Site → Bool | (↑c : Set (Sym2 Site)) ⊆ discordant ζ}

/-- A weakening of Georgii (6.14): if `ζ` is `+1` off the cube and `-1` at `a`, the outer
boundary of the minus cluster of `a` is a connected set of discordant bonds anchored on the
horizontal half-line from `a`, so the event is covered by the contour events.  That this bond
set is a *circuit*, which is Georgii's actual conclusion, is
`PeierlsSharp.sharp_minus_event_subset_iUnion`. -/
theorem minus_event_subset_iUnion (N : ℕ) (a : Site) :
    {ζ : Site → Bool | ζ a = false ∧ ∀ i ∉ cube 2 N, ζ i = true} ⊆
      ⋃ l : ℕ, contourUnion N a l := by
  rintro ζ ⟨ha, hout⟩
  set D : Set Site := minusCluster a ζ with hDdef
  have haD : a ∈ D := mem_minusCluster_self ha
  have hDsub : D ⊆ ((cube 2 N : Finset Site) : Set Site) :=
    minusCluster_subset_of_forall_eq_true (fun i hi ↦ hout i (by simpa using hi))
  have hDbox : D ⊆ box N := by rw [← coe_cube_eq_box N]; exact hDsub
  have hDfin : D.Finite := (box_finite N).subset hDbox
  have hOBfin : (outerBoundary D).Finite := outerBoundary_finite hDfin
  set c : Finset (Sym2 Site) := hOBfin.toFinset with hcdef
  have hccoe : (↑c : Set (Sym2 Site)) = outerBoundary D := Set.Finite.coe_toFinset _
  have hcard : c.card = (outerBoundary D).ncard := by rw [← hccoe, Set.ncard_coe_finset]
  have hpos : 0 < c.card := by
    rw [hcard]
    exact (Set.ncard_pos hOBfin).2 (outerBoundary_nonempty hDfin ⟨a, haD⟩)
  obtain ⟨k, hk, hbond⟩ := exists_anchor_bond hDfin haD
  have hkc : k < c.card := by rw [hcard]; exact hk
  have hsucc : c.card - 1 + 1 = c.card := by omega
  refine Set.mem_iUnion.2 ⟨c.card - 1, ?_⟩
  rw [contourUnion]
  refine Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (by omega), ?_⟩
  refine Set.mem_iUnion₂.2 ⟨c, ?_, ?_⟩
  · rw [mem_contourFinset, hsucc]
    refine ⟨⟨?_, ?_, rfl⟩, ?_, ?_⟩
    · rw [hccoe]
      exact outerBoundary_connected hDfin ⟨a, haD⟩ (minusCluster_connected ha)
    · rw [← Finset.mem_coe, hccoe]; exact hbond
    · rw [hccoe]; exact edgeBoundary_interiorOf_outerBoundary hDfin
    · rw [hccoe, coe_cube_eq_box N]; exact interiorOf_outerBoundary_subset_box hDbox
  · show (↑c : Set (Sym2 Site)) ⊆ discordant ζ
    rw [hccoe]
    exact outerBoundary_minusCluster_subset_discordant a ζ

/-! ### The Peierls sum -/

/-- The kernel with a `+1` boundary condition gives no mass to a minus spin outside `Λ`. -/
lemma isingSpecification_eq_false_null (b : ℝ) (L : Finset Site) {i : Site} (hi : i ∉ L)
    {w : Site → Bool} (hw : w i = true) :
    isingSpecification (latticeGraph 2) 1 0 b L w {z : Site → Bool | z i = false} = 0 := by
  have hiL : i ∈ ((L : Set Site))ᶜ := by simpa using hi
  have hpre : (fun z : Site → Bool ↦ z i) ⁻¹' {false} = {z : Site → Bool | z i = false} := rfl
  have hB : MeasurableSet[cylinderEvents (X := fun _ : Site ↦ Bool) ((L : Set Site))ᶜ]
      {z : Site → Bool | z i = false} := by
    rw [← hpre]
    exact measurable_cylinderEvent_apply (X := fun _ : Site ↦ Bool) hiL
      (measurableSet_singleton false)
  have h := ((isingSpecification (latticeGraph 2) 1 0 b).isProper L).inter_eq_indicator_mul
    cylinderEvents_le_pi MeasurableSet.univ hB (x := w)
  rw [Set.univ_inter] at h
  rw [h]
  simp [hw]

/-- The kernel with the `+1` boundary condition is supported on configurations equal to `+1`
off `Λ`. -/
lemma isingSpecification_boundary_null (b : ℝ) (L : Finset Site) :
    isingSpecification (latticeGraph 2) 1 0 b L (fun _ ↦ true)
      {z : Site → Bool | ¬ ∀ i ∉ L, z i = true} = 0 := by
  have hsub : {z : Site → Bool | ¬ ∀ i ∉ L, z i = true} ⊆
      ⋃ i : {i : Site // i ∉ L}, {z : Site → Bool | z (i : Site) = false} := by
    intro z hz
    have hz' : ¬ ∀ i ∉ L, z i = true := hz
    push Not at hz'
    obtain ⟨i, hi, hzi⟩ := hz'
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, by simpa using hzi⟩
  exact measure_mono_null hsub
    (measure_iUnion_null fun i ↦ isingSpecification_eq_false_null b L i.2 rfl)

/-- The Peierls series `r(β) = ∑_{ℓ ≥ 1} ℓ · 4096^ℓ · e^{-2βℓ}` for the contour count of
`card_contourFinset_le`.  Georgii's own series is `r(β) = 1 ∧ ∑_{ℓ ≥ 1} ℓ (3 e^{-2β})^ℓ`; the
truncation at `1` is unnecessary here because the bound is only used above the threshold, where
the series converges — below it, `r b = ⊤`. -/
def r (b : ℝ) : ℝ≥0∞ :=
  ∑' l : ℕ, ((l : ℝ≥0∞) + 1) * 4096 ^ (l + 1) *
    ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1)))

/-- The Peierls bound for a single family of contours of a given length. -/
lemma isingSpecification_contourUnion_le (b : ℝ) (N : ℕ) (a : Site) (l : ℕ) :
    isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true) (contourUnion N a l) ≤
      ((l : ℝ≥0∞) + 1) * 4096 ^ (l + 1) *
        ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1))) := by
  classical
  set X := ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1))) with hX
  have hinner : ∀ k : ℕ,
      isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
        (⋃ c ∈ contourFinset (cube 2 N) s(a + k • e0, a + (k + 1) • e0) (l + 1),
          {z : Site → Bool | (↑c : Set (Sym2 Site)) ⊆ discordant z}) ≤ 4096 ^ (l + 1) * X := by
    intro k
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ X (fun c hc ↦ ?_)) ?_
    · obtain ⟨⟨-, -, hcard⟩, hbd, hsub⟩ := mem_contourFinset.1 hc
      have h := isingSpecification_subset_discordant_le (Λ := cube 2 N) b hsub hbd (fun _ ↦ true)
      rw [hcard] at h
      rw [hX]
      refine le_trans h (le_of_eq ?_)
      norm_num
    · rw [nsmul_eq_mul]
      gcongr
      exact_mod_cast card_contourFinset_le (cube 2 N) s(a + k • e0, a + (k + 1) • e0) (l + 1)
  rw [contourUnion]
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ (4096 ^ (l + 1) * X) (fun k _ ↦ hinner k)) ?_
  rw [Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by push_cast; ring)

/-- **Georgii (6.9), the Peierls estimate**: in a cube with the `+1` boundary condition, the
probability of a minus spin at `a` is at most `r(β)`. -/
theorem isingSpecification_cube_eq_false_le (b : ℝ) (N : ℕ) (a : Site) :
    isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
      {z : Site → Bool | z a = false} ≤ r b := by
  have hsplit : {z : Site → Bool | z a = false} ⊆
      {z : Site → Bool | z a = false ∧ ∀ i ∉ cube 2 N, z i = true} ∪
        {z : Site → Bool | ¬ ∀ i ∉ cube 2 N, z i = true} := by
    intro z hz
    by_cases h : ∀ i ∉ cube 2 N, z i = true
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr h
  calc isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
        {z : Site → Bool | z a = false}
      ≤ isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          ({z : Site → Bool | z a = false ∧ ∀ i ∉ cube 2 N, z i = true} ∪
            {z : Site → Bool | ¬ ∀ i ∉ cube 2 N, z i = true}) := measure_mono hsplit
    _ ≤ isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          {z : Site → Bool | z a = false ∧ ∀ i ∉ cube 2 N, z i = true} +
        isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          {z : Site → Bool | ¬ ∀ i ∉ cube 2 N, z i = true} := measure_union_le _ _
    _ = isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          {z : Site → Bool | z a = false ∧ ∀ i ∉ cube 2 N, z i = true} := by
          rw [isingSpecification_boundary_null b (cube 2 N), add_zero]
    _ ≤ isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          (⋃ l : ℕ, contourUnion N a l) := measure_mono (minus_event_subset_iUnion N a)
    _ ≤ ∑' l : ℕ, isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          (contourUnion N a l) := measure_iUnion_le _
    _ ≤ r b := ENNReal.tsum_le_tsum (isingSpecification_contourUnion_le b N a)

/-! ### M5: `r(β) → 0` as `β → ∞` -/

lemma tsum_pow_succ_le {y : ℝ≥0∞} (hy : y ≤ 2⁻¹) : ∑' l : ℕ, y ^ (l + 1) ≤ 2 * y := by
  have h1 : ∑' l : ℕ, y ^ (l + 1) = (∑' l : ℕ, y ^ l) * y := by
    rw [← ENNReal.tsum_mul_right]
    exact tsum_congr fun l ↦ by rw [pow_succ]
  have h3 : (2 : ℝ≥0∞)⁻¹ ≤ 1 - y := by
    have h := tsub_le_tsub_left hy (1 : ℝ≥0∞)
    rwa [ENNReal.one_sub_inv_two] at h
  have h2 : (1 - y)⁻¹ ≤ 2 := by
    calc (1 - y)⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹)⁻¹ := ENNReal.inv_le_inv.2 h3
      _ = 2 := by rw [inv_inv]
  rw [h1, ENNReal.tsum_geometric]
  gcongr

/-- The Peierls series is dominated by a geometric series. -/
theorem r_le_of_ofReal_exp_le {b : ℝ}
    (hx : (8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b)) ≤ 2⁻¹) :
    r b ≤ 2 * (8192 * ENNReal.ofReal (Real.exp (-2 * b))) := by
  set x := ENNReal.ofReal (Real.exp (-2 * b)) with hxdef
  refine le_trans (ENNReal.tsum_le_tsum (fun l ↦ ?_)) (tsum_pow_succ_le hx)
  have hexp : ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1))) = x ^ (l + 1) := by
    rw [hxdef, ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hl : ((l : ℝ≥0∞) + 1) ≤ 2 ^ (l + 1) := by
    have h : (l : ℕ) + 1 ≤ 2 ^ (l + 1) := le_of_lt Nat.lt_two_pow_self
    have h' : (((l + 1 : ℕ) : ℝ≥0∞)) ≤ ((2 ^ (l + 1) : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h
    push_cast at h'
    exact h'
  calc ((l : ℝ≥0∞) + 1) * 4096 ^ (l + 1) * ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1)))
      ≤ 2 ^ (l + 1) * 4096 ^ (l + 1) * x ^ (l + 1) := by rw [hexp]; gcongr
    _ = (8192 * x) ^ (l + 1) := by
        rw [mul_pow]
        congr 1
        rw [← mul_pow]
        norm_num

/-! ### M6: the plus phase -/

/-- Translation covariance of the Peierls estimate, for any bound `ρ` dominating the cube
estimate: the estimate holds in every translate of a cube, by shift-invariance of the Ising
specification. -/
lemma isingSpecification_translate_eq_false_le_of_cube {ρ : ℝ → ℝ≥0∞} {b : ℝ}
    (hcube : ∀ (N : ℕ) (a : Site), isingSpecification (latticeGraph 2) 1 0 b (cube 2 N)
      (fun _ ↦ true) {z : Site → Bool | z a = false} ≤ ρ b)
    (N : ℕ) (j a : Site) :
    isingSpecification (latticeGraph 2) 1 0 b
        ((cube 2 N).map (Equiv.addRight j).toEmbedding) (fun _ ↦ true)
      {z : Site → Bool | z a = false} ≤ ρ b := by
  have hinv := (Specification.isInvariant_iff.1
    (isInvariant_shift_isingSpecification 2 1 0 b j)) (cube 2 N) (fun _ ↦ true)
  have hconst : (shift Bool j).toFun (fun _ ↦ true) = (fun _ ↦ true) := by
    funext i
    rw [shift_toFun_apply]
  have hsites : (shift Bool j).sites.toEmbedding = (Equiv.addRight j).toEmbedding := rfl
  rw [hconst, hsites] at hinv
  have hmeas : MeasurableSet {z : Site → Bool | z a = false} := by
    have h : {z : Site → Bool | z a = false} = (fun z : Site → Bool ↦ z a) ⁻¹' {false} := rfl
    rw [h]
    exact (measurable_pi_apply a) (measurableSet_singleton false)
  rw [← hinv, Measure.map_apply (shift Bool j).measurable_toFun hmeas]
  have hpre : (shift Bool j).toFun ⁻¹' {z : Site → Bool | z a = false}
      = {z : Site → Bool | z (a - j) = false} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, shift_toFun_apply]
  rw [hpre]
  exact hcube N (a - j)

lemma isingSpecification_translate_eq_false_le (b : ℝ) (N : ℕ) (j a : Site) :
    isingSpecification (latticeGraph 2) 1 0 b
        ((cube 2 N).map (Equiv.addRight j).toEmbedding) (fun _ ↦ true)
      {z : Site → Bool | z a = false} ≤ r b :=
  isingSpecification_translate_eq_false_le_of_cube
    (fun N a ↦ isingSpecification_cube_eq_false_le b N a) N j a

/-- The Peierls estimate for the cube-averaged Gibbs distributions with the `+1` boundary
condition (Georgii (6.9), the averaged sequence), for any bound dominating the cube estimate. -/
lemma average_eq_false_le_of_cube {ρ : ℝ → ℝ≥0∞} {b : ℝ}
    (hcube : ∀ (N : ℕ) (a : Site), isingSpecification (latticeGraph 2) 1 0 b (cube 2 N)
      (fun _ ↦ true) {z : Site → Bool | z a = false} ≤ ρ b)
    (N : ℕ) (a : Site) :
    (isingSpecification (latticeGraph 2) 1 0 b).average
        (Measure.dirac (fun _ ↦ true)) (cubeTranslates 2 N N)
      {z : Site → Bool | z a = false} ≤ ρ b := by
  rw [Specification.average_apply]
  have hne : (cubeTranslates 2 N N).Nonempty := cubeTranslates_nonempty 2 N N
  have hterm : ∀ L ∈ cubeTranslates 2 N N,
      (Measure.dirac (fun _ ↦ true : Site → Bool)).bind
        (isingSpecification (latticeGraph 2) 1 0 b L) {z : Site → Bool | z a = false} ≤ ρ b := by
    intro L hL
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hL
    rw [Measure.dirac_bind
      ((isingSpecification (latticeGraph 2) 1 0 b).measurable_kernel_toMeasure _)]
    exact isingSpecification_translate_eq_false_le_of_cube hcube N i a
  calc ((cubeTranslates 2 N N).card : ℝ≥0∞)⁻¹ * ∑ L ∈ cubeTranslates 2 N N,
        (Measure.dirac (fun _ ↦ true : Site → Bool)).bind
          (isingSpecification (latticeGraph 2) 1 0 b L) {z : Site → Bool | z a = false}
      ≤ ((cubeTranslates 2 N N).card : ℝ≥0∞)⁻¹ * ∑ _L ∈ cubeTranslates 2 N N, ρ b := by
        gcongr with L hL
        exact hterm L hL
    _ = ((cubeTranslates 2 N N).card : ℝ≥0∞)⁻¹ * (((cubeTranslates 2 N N).card : ℝ≥0∞) * ρ b) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ρ b := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hne.card_pos.ne')
          (ENNReal.natCast_ne_top _), one_mul]


lemma average_eq_false_le (b : ℝ) (N : ℕ) (a : Site) :
    (isingSpecification (latticeGraph 2) 1 0 b).average
        (Measure.dirac (fun _ ↦ true)) (cubeTranslates 2 N N)
      {z : Site → Bool | z a = false} ≤ r b :=
  average_eq_false_le_of_cube (fun N a ↦ isingSpecification_cube_eq_false_le b N a) N a

/-- `{ζ | ζ a = -1}` is a local event. -/
lemma spin_eq_false_mem_localEvents (a : Site) :
    {z : Site → Bool | z a = false} ∈ localEvents Site Bool := by
  refine mem_localEvents_of_cylinderEvents {a} ?_
  have hmem : a ∈ (({a} : Finset Site) : Set Site) := by simp
  exact measurable_cylinderEvent_apply (X := fun _ : Site ↦ Bool) hmem
    (measurableSet_singleton false)

end MeasureTheory.GibbsMeasure.Peierls

namespace MeasureTheory.GibbsMeasure

/-! ### Closed conditions on the values of a net pass to its local cluster points -/

variable {S E : Type*} [MeasurableSpace E]

/-- **A closed condition on the value at a local event passes to the cluster points.**  Evaluation
at a local event is continuous for the topology of local convergence (Georgii (4.2)), so the set
of random fields whose value at `A` lies in a closed set `C` is closed. -/
lemma mem_of_mapClusterPt_of_isClosed {ι : Type*} {l : Filter ι} {A : Set (S → E)}
    (hA : A ∈ localEvents S E) {C : Set ℝ≥0∞} (hC : IsClosed C)
    {ms : ι → ProbabilityMeasure (S → E)} {m : WithLocalConvergence S E}
    (hm : MapClusterPt m l fun i ↦ WithSetwiseTopology.ofMeasure (ms i))
    (hle : ∀ᶠ i in l, (ms i : Measure (S → E)) A ∈ C) :
    (m.toMeasure : Measure (S → E)) A ∈ C := by
  set s : Set (WithLocalConvergence S E) := {v | (v.toMeasure : Measure (S → E)) A ∈ C} with hs
  have hclosed : IsClosed s := hC.preimage (WithSetwiseTopology.continuous_apply_enn hA)
  have hcl : ClusterPt m (Filter.map (fun i ↦ (WithSetwiseTopology.ofMeasure (ms i) :
      WithLocalConvergence S E)) l) := hm
  have hprin : (Filter.map (fun i ↦ (WithSetwiseTopology.ofMeasure (ms i) :
      WithLocalConvergence S E)) l) ≤ 𝓟 s :=
    Filter.le_principal_iff.2 (Filter.mem_map.2 hle)
  have hmem : m ∈ closure s := mem_closure_iff_clusterPt.2 (hcl.mono hprin)
  rwa [hclosed.closure_eq] at hmem

/-- An upper bound valid along a net at a local event passes to its cluster points. -/
lemma eval_le_of_mapClusterPt {ι : Type*} {l : Filter ι} {A : Set (S → E)}
    (hA : A ∈ localEvents S E) {c : ℝ≥0∞} {ms : ι → ProbabilityMeasure (S → E)}
    {m : WithLocalConvergence S E}
    (hm : MapClusterPt m l fun i ↦ WithSetwiseTopology.ofMeasure (ms i))
    (hle : ∀ᶠ i in l, (ms i : Measure (S → E)) A ≤ c) :
    (m.toMeasure : Measure (S → E)) A ≤ c :=
  mem_of_mapClusterPt_of_isClosed hA (isClosed_Iic (a := c)) hm hle

/-- A lower bound valid along a net at a local event passes to its cluster points. -/
lemma le_eval_of_mapClusterPt {ι : Type*} {l : Filter ι} {A : Set (S → E)}
    (hA : A ∈ localEvents S E) {c : ℝ≥0∞} {ms : ι → ProbabilityMeasure (S → E)}
    {m : WithLocalConvergence S E}
    (hm : MapClusterPt m l fun i ↦ WithSetwiseTopology.ofMeasure (ms i))
    (hle : ∀ᶠ i in l, c ≤ (ms i : Measure (S → E)) A) :
    c ≤ (m.toMeasure : Measure (S → E)) A :=
  mem_of_mapClusterPt_of_isClosed hA (isClosed_Ici (a := c)) hm hle

end MeasureTheory.GibbsMeasure

namespace MeasureTheory.GibbsMeasure.Peierls

/-! ### Georgii's cube-averaged `+`-boundary distributions -/

/-- **Georgii (6.9)/(5.20)(1)**: the cube-averaged Ising distributions with the all-`+` boundary
condition, `μ_N = |Λ_N|⁻¹ ∑_{i ∈ Λ_N} γ^β_{Λ_N + i}(· | ω⁺)`.  The plus phase of the proof of
(6.9) is a cluster point of this sequence. -/
def plusCubeAverage (b : ℝ) (N : ℕ) : ProbabilityMeasure (Site → Bool) :=
  ⟨(isingSpecification (latticeGraph 2) 1 0 b).average
      (Measure.dirac fun _ ↦ true) (cubeTranslates 2 N N),
    (isingSpecification (latticeGraph 2) 1 0 b).isProbabilityMeasure_average _
      (cubeTranslates_nonempty 2 N N)⟩

@[simp] lemma coe_plusCubeAverage (b : ℝ) (N : ℕ) :
    (plusCubeAverage b N : Measure (Site → Bool))
      = (isingSpecification (latticeGraph 2) 1 0 b).average
        (Measure.dirac fun _ ↦ true) (cubeTranslates 2 N N) := rfl

/-- **Georgii (6.9)**: the cube averages have a cluster point in the topology of local
convergence, by compactness of the space of random fields over a finite state space
(Georgii (4.11)(2)). -/
theorem exists_mapClusterPt_plusCubeAverage (b : ℝ) :
    ∃ m : ProbabilityMeasure (Site → Bool),
      MapClusterPt (WithSetwiseTopology.ofMeasure m : WithLocalConvergence Site Bool) atTop
        fun N ↦ WithSetwiseTopology.ofMeasure (plusCubeAverage b N) := by
  obtain ⟨m, hm⟩ := exists_clusterPt_of_compactSpace
    (Filter.map (fun N ↦ (WithSetwiseTopology.ofMeasure (plusCubeAverage b N) :
      WithLocalConvergence (Fin 2 → ℤ) Bool)) atTop)
  exact ⟨m.toMeasure, hm⟩

/-- **Georgii (6.9)**: every cluster point of the cube averages is a Gibbs measure
(Georgii (4.18)). -/
theorem mem_GP_of_mapClusterPt_plusCubeAverage {b : ℝ} {m : ProbabilityMeasure (Site → Bool)}
    (hm : MapClusterPt (WithSetwiseTopology.ofMeasure m : WithLocalConvergence Site Bool) atTop
      fun N ↦ WithSetwiseTopology.ofMeasure (plusCubeAverage b N)) :
    m ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) :=
  (mem_GP_and_measurePreserving_shift_of_mapClusterPt_average_cubeTranslates_dirac
    (Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable uniformSpinMeasure b)
    (isInvariant_shift_isingSpecification 2 1 0 b) true (μs := plusCubeAverage b)
    (fun _ ↦ rfl) hm).1

/-- **Georgii (6.9)**: every cluster point of the cube averages is shift invariant
(Georgii (5.18)/(5.20)(1)); this is why Georgii averages over the cube translates. -/
theorem measurePreserving_shift_of_mapClusterPt_plusCubeAverage {b : ℝ}
    {m : ProbabilityMeasure (Site → Bool)}
    (hm : MapClusterPt (WithSetwiseTopology.ofMeasure m : WithLocalConvergence Site Bool) atTop
      fun N ↦ WithSetwiseTopology.ofMeasure (plusCubeAverage b N)) (j : Site) :
    MeasurePreserving (shift Bool j).toFun (m : Measure (Site → Bool)) m :=
  (mem_GP_and_measurePreserving_shift_of_mapClusterPt_average_cubeTranslates_dirac
    (Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable uniformSpinMeasure b)
    (isInvariant_shift_isingSpecification 2 1 0 b) true (μs := plusCubeAverage b)
    (fun _ ↦ rfl) hm).2 j

/-- **Georgii (6.9)**: the Peierls estimate passes to every cluster point of the cube averages. -/
theorem eq_false_le_of_mapClusterPt_plusCubeAverage_of_cube {ρ : ℝ → ℝ≥0∞} {b : ℝ}
    {m : ProbabilityMeasure (Site → Bool)}
    (hm : MapClusterPt (WithSetwiseTopology.ofMeasure m : WithLocalConvergence Site Bool) atTop
      fun N ↦ WithSetwiseTopology.ofMeasure (plusCubeAverage b N))
    (hcube : ∀ (N : ℕ) (a : Site), isingSpecification (latticeGraph 2) 1 0 b (cube 2 N)
      (fun _ ↦ true) {z : Site → Bool | z a = false} ≤ ρ b) (a : Site) :
    (m : Measure (Site → Bool)) {z : Site → Bool | z a = false} ≤ ρ b :=
  eval_le_of_mapClusterPt (spin_eq_false_mem_localEvents a) hm
    (.of_forall fun N ↦ average_eq_false_le_of_cube hcube N a)

/-- **Georgii (6.9), the plus phase**, for any bound `ρ` dominating the cube estimate: a
shift-invariant Gibbs measure with `μ(σ_a = -1) ≤ ρ(β)` for every site `a`. -/
theorem exists_plus_phase_of_cube {ρ : ℝ → ℝ≥0∞} {b : ℝ}
    (hcube : ∀ (N : ℕ) (a : Site), isingSpecification (latticeGraph 2) 1 0 b (cube 2 N)
      (fun _ ↦ true) {z : Site → Bool | z a = false} ≤ ρ b) :
    ∃ m : ProbabilityMeasure (Site → Bool),
      m ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (m : Measure (Site → Bool)) m) ∧
      ∀ a : Site, (m : Measure (Site → Bool)) {z : Site → Bool | z a = false} ≤ ρ b := by
  obtain ⟨m, hm⟩ := exists_mapClusterPt_plusCubeAverage b
  exact ⟨m, mem_GP_of_mapClusterPt_plusCubeAverage hm,
    measurePreserving_shift_of_mapClusterPt_plusCubeAverage hm,
    fun a ↦ eq_false_le_of_mapClusterPt_plusCubeAverage_of_cube hm hcube a⟩

/-- **Georgii (6.9), the plus phase**: a shift-invariant Gibbs measure with `μ(σ_a = -1) ≤ r(β)`
for every site `a`. -/
theorem exists_plus_phase (b : ℝ) :
    ∃ m : ProbabilityMeasure (Site → Bool),
      m ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (m : Measure (Site → Bool)) m) ∧
      ∀ a : Site, (m : Measure (Site → Bool)) {z : Site → Bool | z a = false} ≤ r b :=
  exists_plus_phase_of_cube fun N a ↦ isingSpecification_cube_eq_false_le b N a

/-! ### M7: the spin flip -/

/-- Negation of a `Bool` spin as a measurable equivalence. -/
def boolNotEquiv : Bool ≃ᵐ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

/-- **Georgii (5.2)(2)**: the spin flip `τ : ω ↦ -ω`. -/
def spinFlip : Transformation Site Bool where
  sites := Equiv.refl Site
  spin _ := boolNotEquiv

@[simp] lemma spinFlip_toFun_apply (z : Site → Bool) (i : Site) :
    spinFlip.toFun z i = !(z i) := rfl

@[simp] lemma spinFlip_inv_toFun_apply (z : Site → Bool) (i : Site) :
    spinFlip.inv.toFun z i = !(z i) := rfl

lemma spin_not (c : Bool) : spin (!c) = - spin c := by cases c <;> simp [spin]

/-- The Ising potential with vanishing external field is invariant under the spin flip. -/
lemma map_spinFlip_isingPotential :
    Potential.map spinFlip (isingPotential (latticeGraph 2) 1 0)
      = isingPotential (latticeGraph 2) 1 0 := by
  funext A z
  rw [Potential.map_apply]
  have hA : A.map spinFlip.sites.symm.toEmbedding = A := by
    ext x
    simp [spinFlip]
  rw [hA]
  simp only [isingPotential, Potential.nearestNeighbourPair]
  by_cases h1 : A.card = 1
  · simp [h1]
  · by_cases h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, (latticeGraph 2).Adj i j
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]
      obtain ⟨u, v, huv, hAuv⟩ := Finset.card_eq_two.1 h2.1
      subst hAuv
      rw [Finset.prod_pair huv, Finset.prod_pair huv]
      simp only [spinFlip_inv_toFun_apply, spin_not]
      ring
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h2]

/-- The uniform spin measure is invariant under negation. -/
lemma measurePreserving_boolNot :
    MeasurePreserving Bool.not uniformSpinMeasure uniformSpinMeasure := by
  refine ⟨Measurable.of_discrete, ?_⟩
  have hsingle : ∀ c : Bool, uniformSpinMeasure {c} = 2⁻¹ := by
    intro c
    show ((2 : ℝ≥0∞)⁻¹ • Measure.count) {c} = 2⁻¹
    rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
  refine Measure.ext_of_singleton fun c ↦ ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton c)]
  have hpre : (Bool.not ⁻¹' {c}) = {!c} := by
    ext d
    cases c <;> cases d <;> simp
  rw [hpre, hsingle, hsingle]

/-- **Georgii (5.9)(b)/(6.9)**: the Ising specification is invariant under the spin flip. -/
lemma isInvariant_spinFlip (b : ℝ) :
    Specification.IsInvariant spinFlip (isingSpecification (latticeGraph 2) 1 0 b) :=
  Potential.isInvariant_gibbsSpecification spinFlip (isingPotential (latticeGraph 2) 1 0)
    uniformSpinMeasure b (fun _ ↦ measurePreserving_boolNot) map_spinFlip_isingPotential

/-! ### Georgii Theorem (6.9): the phase transition -/

lemma ofReal_exp_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) :
    ENNReal.ofReal (Real.exp (-2 * b)) ≤ (65536 : ℝ≥0∞)⁻¹ := by
  have h1 : Real.exp (16 * Real.log 2) = 65536 := by
    rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h2 : Real.exp (-2 * b) ≤ (65536 : ℝ)⁻¹ := by
    have h3 : -2 * b ≤ -(16 * Real.log 2) := by linarith
    calc Real.exp (-2 * b) ≤ Real.exp (-(16 * Real.log 2)) := Real.exp_le_exp.2 h3
      _ = (Real.exp (16 * Real.log 2))⁻¹ := Real.exp_neg _
      _ = (65536 : ℝ)⁻¹ := by rw [h1]
  calc ENNReal.ofReal (Real.exp (-2 * b)) ≤ ENNReal.ofReal ((65536 : ℝ)⁻¹) :=
        ENNReal.ofReal_le_ofReal h2
    _ = (65536 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num

/-- **Georgii (6.9)**: `r(β) ≤ 1/4 < 1/2` at low temperature. -/
theorem r_le_quarter {b : ℝ} (hb : 8 * Real.log 2 ≤ b) : r b ≤ 4⁻¹ := by
  have hx := ofReal_exp_le hb
  have h8 : (8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b)) ≤ 8⁻¹ := by
    calc (8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b)) ≤ 8192 * 65536⁻¹ := by gcongr
      _ = 8⁻¹ := by
          rw [show (65536 : ℝ≥0∞) = 8192 * 8 by norm_num,
            ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have h8' : (8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b)) ≤ 2⁻¹ :=
    le_trans h8 (ENNReal.inv_le_inv.2 (by norm_num))
  calc r b ≤ 2 * (8192 * ENNReal.ofReal (Real.exp (-2 * b))) := r_le_of_ofReal_exp_le h8'
    _ ≤ 2 * 8⁻¹ := by gcongr
    _ = 4⁻¹ := by
        rw [show (8 : ℝ≥0∞) = 2 * 4 by norm_num,
          ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- The two-phase theorem for any bound dominating the cube estimate and `≤ 4⁻¹` at `b`. -/
theorem exists_two_shiftInvariant_gibbs_of_cube {ρ : ℝ → ℝ≥0∞} {b : ℝ}
    (hcube : ∀ (N : ℕ) (a : Site), isingSpecification (latticeGraph 2) 1 0 b (cube 2 N)
      (fun _ ↦ true) {z : Site → Bool | z a = false} ≤ ρ b)
    (hquarter : ρ b ≤ 4⁻¹) :
    ∃ mp mm : ProbabilityMeasure (Site → Bool),
      mp ≠ mm ∧
      mp ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      mm ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mp : Measure (Site → Bool)) mp) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mm : Measure (Site → Bool)) mm) ∧
      (mm : Measure (Site → Bool)) = Measure.map spinFlip.toFun (mp : Measure (Site → Bool)) ∧
      (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} < 2⁻¹ ∧
      2⁻¹ < (mm : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} ∧
      2⁻¹ < (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = true} := by
  obtain ⟨mp, hGP, hshift, hbound⟩ := exists_plus_phase_of_cube hcube
  set mm : ProbabilityMeasure (Site → Bool) :=
    mp.map spinFlip.measurable_toFun.aemeasurable with hmmdef
  have hmmshift : ∀ j : Site,
      MeasurePreserving (shift Bool j).toFun (mm : Measure (Site → Bool)) mm := by
    intro j
    refine ⟨(shift Bool j).measurable_toFun, ?_⟩
    rw [hmmdef, ProbabilityMeasure.toMeasure_map,
      Measure.map_map (shift Bool j).measurable_toFun spinFlip.measurable_toFun,
      show (shift Bool j).toFun ∘ spinFlip.toFun = spinFlip.toFun ∘ (shift Bool j).toFun from
        funext fun z ↦ funext fun i ↦ by simp,
      ← Measure.map_map spinFlip.measurable_toFun (shift Bool j).measurable_toFun,
      (hshift j).map_eq]
  have hmeasF : MeasurableSet {z : Site → Bool | z (0 : Site) = false} := by
    have h : {z : Site → Bool | z (0 : Site) = false}
        = (fun z : Site → Bool ↦ z 0) ⁻¹' {false} := rfl
    rw [h]
    exact (measurable_pi_apply _) (measurableSet_singleton false)
  have hcompl : {z : Site → Bool | z (0 : Site) = true}
      = {z : Site → Bool | z (0 : Site) = false}ᶜ := by
    ext z
    cases h : z 0 <;> simp [h]
  have hmmval : (mm : Measure (Site → Bool)) {z : Site → Bool | z 0 = false}
      = (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = true} := by
    rw [hmmdef, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply spinFlip.measurable_toFun hmeasF]
    congr 1
    ext z
    simp
  have hsum : (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} +
      (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = true} = 1 := by
    rw [hcompl, measure_add_measure_compl hmeasF]
    simp
  have hle : (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} ≤ 4⁻¹ :=
    le_trans (hbound 0) hquarter
  have hlt : (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} < 2⁻¹ :=
    lt_of_le_of_lt hle (by norm_num)
  have hgt : 2⁻¹ < (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = true} := by
    by_contra hcon
    push Not at hcon
    have h1 := add_le_add hle hcon
    rw [hsum] at h1
    have h2 : (4 : ℝ≥0∞)⁻¹ + 2⁻¹ < 1 := by
      rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp
      norm_num
    exact absurd h1 (not_le.2 h2)
  have hgt' : 2⁻¹ < (mm : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} := by
    rw [hmmval]
    exact hgt
  have hne : mp ≠ mm := by
    intro hcon
    rw [hcon] at hlt
    exact absurd hlt (not_lt.2 (le_of_lt hgt'))
  exact ⟨mp, mm, hne, hGP, (isInvariant_spinFlip b).map_mem_GP hGP, hshift, hmmshift,
    hmmdef ▸ ProbabilityMeasure.toMeasure_map _ _, hlt, hgt', hgt⟩

/-- **Georgii Theorem (6.9), the "in particular" part.** For all sufficiently large `β` the
two-dimensional Ising ferromagnet with coupling `1` and no external field has two distinct
shift-invariant Gibbs measures `μ₋ = τ(μ₊)`, exchanged by the spin flip, with
`μ₊(σ₀ = -1) < 1/2 < μ₋(σ₀ = -1)`: spontaneous magnetisation. -/
theorem exists_two_shiftInvariant_gibbs (b : ℝ) (hb : 8 * Real.log 2 ≤ b) :
    ∃ mp mm : ProbabilityMeasure (Site → Bool),
      mp ≠ mm ∧
      mp ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      mm ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mp : Measure (Site → Bool)) mp) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mm : Measure (Site → Bool)) mm) ∧
      (mm : Measure (Site → Bool)) = Measure.map spinFlip.toFun (mp : Measure (Site → Bool)) ∧
      (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} < 2⁻¹ ∧
      2⁻¹ < (mm : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} ∧
      2⁻¹ < (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = true} :=
  exists_two_shiftInvariant_gibbs_of_cube
    (fun N a ↦ isingSpecification_cube_eq_false_le b N a) (r_le_quarter hb)

/-- **Georgii Theorem (6.9)**, the "in particular" half, in the book's `for sufficiently large
`β`` form; `exists_two_shiftInvariant_gibbs` gives the explicit threshold `8 log 2`. -/
theorem exists_two_shiftInvariant_gibbs_of_large_beta :
    ∃ b₀ : ℝ, ∀ b ≥ b₀, ∃ mp mm : ProbabilityMeasure (Site → Bool),
      mp ≠ mm ∧
      mp ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      mm ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mp : Measure (Site → Bool)) mp) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mm : Measure (Site → Bool)) mm) ∧
      (mm : Measure (Site → Bool)) = Measure.map spinFlip.toFun (mp : Measure (Site → Bool)) ∧
      (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} < 2⁻¹ ∧
      2⁻¹ < (mm : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} ∧
      2⁻¹ < (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = true} :=
  ⟨8 * Real.log 2, fun _ hb ↦ exists_two_shiftInvariant_gibbs _ hb⟩

/-! ### The magnetisation (Georgii (6.9), `μ_-(σ₀) < 0 < μ_+(σ₀)`) -/

lemma measurableSet_eq_false (a : Site) : MeasurableSet {z : Site → Bool | z a = false} := by
  have h : {z : Site → Bool | z a = false} = (fun z : Site → Bool ↦ z a) ⁻¹' {false} := rfl
  rw [h]
  exact (measurable_pi_apply _) (measurableSet_singleton false)

lemma setOf_eq_true_eq_compl (a : Site) :
    {z : Site → Bool | z a = true} = {z : Site → Bool | z a = false}ᶜ := by
  ext z
  cases h : z a <;> simp [h]

lemma measureReal_true_add_false (m : ProbabilityMeasure (Site → Bool)) (a : Site) :
    (m : Measure (Site → Bool)).real {z : Site → Bool | z a = true} +
      (m : Measure (Site → Bool)).real {z : Site → Bool | z a = false} = 1 := by
  rw [setOf_eq_true_eq_compl a, add_comm,
    measureReal_add_measureReal_compl (measurableSet_eq_false a)]
  simp

/-- The magnetisation as a function of the probability of a plus spin. -/
lemma integral_spin_eq (m : ProbabilityMeasure (Site → Bool)) :
    ∫ z, spin (z (0 : Site)) ∂(m : Measure (Site → Bool))
      = 2 * (m : Measure (Site → Bool)).real {z : Site → Bool | z 0 = true} - 1 := by
  have hA : MeasurableSet {z : Site → Bool | z (0 : Site) = true} := by
    rw [setOf_eq_true_eq_compl]
    exact (measurableSet_eq_false 0).compl
  have hfun : (fun z : Site → Bool ↦ spin (z (0 : Site)))
      = fun z ↦ {z : Site → Bool | z (0 : Site) = true}.indicator (fun _ ↦ (2 : ℝ)) z - 1 := by
    funext z
    by_cases h : z (0 : Site) = true
    · simp [spin, h]
      norm_num
    · simp only [Bool.not_eq_true] at h
      simp [spin, h]
  rw [hfun, integral_sub ((integrable_const (2 : ℝ)).indicator hA) (integrable_const 1),
    integral_indicator_const _ hA, integral_const]
  simp [mul_comm]

/-- **Georgii (6.9)**: positive magnetisation in the plus phase. -/
lemma integral_spin_pos {m : ProbabilityMeasure (Site → Bool)}
    (h : 2⁻¹ < (m : Measure (Site → Bool)) {z : Site → Bool | z 0 = true}) :
    0 < ∫ z, spin (z (0 : Site)) ∂(m : Measure (Site → Bool)) := by
  have hreal : (2 : ℝ)⁻¹ < (m : Measure (Site → Bool)).real {z : Site → Bool | z 0 = true} := by
    have h1 : ((2 : ℝ≥0∞)⁻¹).toReal <
        ((m : Measure (Site → Bool)) {z : Site → Bool | z 0 = true}).toReal :=
      (ENNReal.toReal_lt_toReal (by finiteness) (measure_ne_top _ _)).2 h
    simpa [measureReal_def] using h1
  rw [integral_spin_eq]
  linarith

/-- **Georgii (6.9)**: negative magnetisation in the minus phase. -/
lemma integral_spin_neg {m : ProbabilityMeasure (Site → Bool)}
    (h : 2⁻¹ < (m : Measure (Site → Bool)) {z : Site → Bool | z 0 = false}) :
    ∫ z, spin (z (0 : Site)) ∂(m : Measure (Site → Bool)) < 0 := by
  have hreal : (2 : ℝ)⁻¹ < (m : Measure (Site → Bool)).real {z : Site → Bool | z 0 = false} := by
    have h1 : ((2 : ℝ≥0∞)⁻¹).toReal <
        ((m : Measure (Site → Bool)) {z : Site → Bool | z 0 = false}).toReal :=
      (ENNReal.toReal_lt_toReal (by finiteness) (measure_ne_top _ _)).2 h
    simpa [measureReal_def] using h1
  have hsum := measureReal_true_add_false m 0
  rw [integral_spin_eq]
  linarith

/-- **Georgii (6.9)**, the set of Gibbs measures is not a singleton at low temperature:
`|𝒢(βΦ)| > 1`. -/
theorem nontrivial_GP_isingSpecification_of_large_beta :
    ∃ b₀ : ℝ, ∀ b ≥ b₀,
      (GP (S := Fin 2 → ℤ) (E := Bool)
        (isingSpecification (latticeGraph 2) 1 0 b)).Nontrivial := by
  obtain ⟨b₀, h⟩ := exists_two_shiftInvariant_gibbs_of_large_beta
  refine ⟨b₀, fun b hb ↦ ?_⟩
  obtain ⟨mp, mm, hne, hp, hm, -, -, -, -, -, -⟩ := h b hb
  exact ⟨mp, hp, mm, hm, hne⟩

/-- **Georgii Theorem (6.9), spontaneous magnetisation**: at low temperature the two-dimensional
Ising ferromagnet has two shift-invariant Gibbs measures, exchanged by the spin flip, with
`μ_-(σ₀) < 0 < μ_+(σ₀)`. -/
theorem exists_spontaneous_magnetisation :
    ∃ b₀ : ℝ, ∀ b ≥ b₀, ∃ mp mm : ProbabilityMeasure (Site → Bool),
      mp ≠ mm ∧
      mp ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      mm ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mp : Measure (Site → Bool)) mp) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mm : Measure (Site → Bool)) mm) ∧
      (mm : Measure (Site → Bool)) = Measure.map spinFlip.toFun (mp : Measure (Site → Bool)) ∧
      ∫ z, spin (z (0 : Site)) ∂(mm : Measure (Site → Bool)) < 0 ∧
      0 < ∫ z, spin (z (0 : Site)) ∂(mp : Measure (Site → Bool)) := by
  obtain ⟨b₀, h⟩ := exists_two_shiftInvariant_gibbs_of_large_beta
  refine ⟨b₀, fun b hb ↦ ?_⟩
  obtain ⟨mp, mm, hne, hp, hm, hsp, hsm, hmap, -, hgt, hgtT⟩ := h b hb
  exact ⟨mp, mm, hne, hp, hm, hsp, hsm, hmap, integral_spin_neg hgt, integral_spin_pos hgtT⟩

end MeasureTheory.GibbsMeasure.Peierls

end

end
