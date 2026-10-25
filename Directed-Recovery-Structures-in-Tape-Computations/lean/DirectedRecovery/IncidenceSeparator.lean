import DirectedRecovery.IncidenceComponents
import DirectedRecovery.StorageCode
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The finite separator bound

Port deletion is paid for by fixing the coordinates incident to the deleted
ports. Coordinates whose prescribed pair has ambient distance at most `K`
are fixed as well. The remaining incidence pairs are disconnected whenever
the surviving port components have at most `K` vertices.

The ambient distance is `SimpleGraph.edist : ℕ∞`; disconnected pairs have
infinite distance and are therefore never counted as short pairs.
-/

namespace DirectedRecovery

open Classical Finset MotionDepthCodes
set_option autoImplicit false

variable {V α : Type*} [DecidableEq V] [Fintype V]

/-- Forget which of the two ports represents a coordinate. -/
def portCoordinate : V ⊕ V → V := Sum.elim id id

/-- Coordinates whose prescribed incidence ports are within distance `K`.
The extended-natural distance excludes disconnected ports. -/
noncomputable def shortPairedCoordinates (N : V → Finset V) (K : ℕ) : Finset V :=
  Finset.univ.filter (fun p =>
    (pairedIncidenceGraph N).edist (Sum.inl p) (Sum.inr p) ≤ K)

/-- The graph after deleting the specified incidence ports. -/
abbrev portDeletedGraph (N : V → Finset V) (Z : Finset (V ⊕ V)) :
    SimpleGraph {v // v ∉ Z} :=
  (pairedIncidenceGraph N).induce {v | v ∉ Z}

/-- Every surviving port lies in a component with at most `K` vertices.
The finite reachability fibre is exactly its connected component. -/
def HasSmallPortComponents (N : V → Finset V) (Z : Finset (V ⊕ V)) (K : ℕ) : Prop :=
  ∀ u : {v // v ∉ Z},
    (Finset.univ.filter (fun v => (portDeletedGraph N Z).Reachable u v)).card ≤ K

/-- A reachable pair in a finite component admits a path shorter than the
component size, and its image in any graph has no larger distance. -/
private theorem mapped_edist_le_of_component_bound {W W' : Type*}
    [Fintype W] [DecidableEq W] {G : SimpleGraph W} {G' : SimpleGraph W'}
    (f : G →g G') {u v : W} (hr : G.Reachable u v) {K : ℕ}
    (hK : (Finset.univ.filter (fun w => G.Reachable u w)).card ≤ K) :
    G'.edist (f u) (f v) ≤ K := by
  obtain ⟨p, hp⟩ := hr.exists_isPath
  have hs : p.support.toFinset ⊆ Finset.univ.filter (fun w => G.Reachable u w) := by
    intro w hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨p.takeUntil w (List.mem_toFinset.mp hw)⟩
  have hlen : p.length + 1 ≤ K := by
    calc
      p.length + 1 = p.support.toFinset.card := by
        rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
      _ ≤ (Finset.univ.filter (fun w => G.Reachable u w)).card := Finset.card_le_card hs
      _ ≤ K := hK
  calc
    G'.edist (f u) (f v) ≤ (p.map f).length := G'.edist_le (p.map f)
    _ = (p.length : ℕ∞) := by rw [SimpleGraph.Walk.length_map]
    _ ≤ (K : ℕ∞) := by exact_mod_cast (by omega : p.length ≤ K)

/-- The induced relation on coordinates whose two ports survive maps into
the graph obtained by deleting the original port set. -/
def inducedToPortDeleted (N : V → Finset V) (Z : Finset (V ⊕ V)) (Q : Finset V)
    (hQ : ∀ q ∈ Q, Sum.inl q ∉ Z ∧ Sum.inr q ∉ Z) :
    pairedIncidenceGraph (inducedNeighborhood N Q) →g portDeletedGraph N Z where
  toFun v := match v with
    | Sum.inl q => ⟨Sum.inl q.val, (hQ q.val q.property).1⟩
    | Sum.inr q => ⟨Sum.inr q.val, (hQ q.val q.property).2⟩
  map_rel' := by
    intro u v h
    cases u with
    | inl p =>
      cases v with
      | inl q => exact h.elim
      | inr q => exact Finset.mem_subtype.mp h
    | inr q =>
      cases v with
      | inl p => exact Finset.mem_subtype.mp h
      | inr p => exact h.elim

/-- Once every coordinate incident to a deleted port, and every short
ambient demand pair, has been fixed, all remaining demand pairs disconnect. -/
theorem separator_induced_pairs_unreachable (N : V → Finset V)
    (Z : Finset (V ⊕ V)) (K : ℕ) (hcomp : HasSmallPortComponents N Z K)
    (Q : Finset V)
    (hQZ : ∀ q ∈ Q, Sum.inl q ∉ Z ∧ Sum.inr q ∉ Z)
    (hQshort : ∀ q ∈ Q, q ∉ shortPairedCoordinates N K) :
    ∀ q : Q, ¬(pairedIncidenceGraph (inducedNeighborhood N Q)).Reachable
      (Sum.inl q) (Sum.inr q) := by
  intro q hr
  let f := inducedToPortDeleted N Z Q hQZ
  have hr' := hr.map f
  let g : portDeletedGraph N Z →g pairedIncidenceGraph N :=
    (SimpleGraph.Embedding.induce {v | v ∉ Z}).toHom
  have hdist := mapped_edist_le_of_component_bound g hr' (hcomp (f (Sum.inl q)))
  apply hQshort q q.property
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩

/-- The exact real-exponent finite separator bound. The alphabet has at
least two symbols. No degree bound or extra structural assumption is used. -/
theorem storageCode_separator_bound [Fintype α] [Nonempty α]
    (N : V → Finset V) (Z : Finset (V ⊕ V)) (K : ℕ)
    (hcomp : HasSmallPortComponents N Z K)
    (ha : 1 < (Fintype.card α : ℝ))
    (C : Finset (V → α)) (hC : IsStorageCode N C) :
    (C.card : ℝ) ≤ (Fintype.card α : ℝ) ^
      (((Fintype.card V : ℝ) + Z.card + (shortPairedCoordinates N K).card) / 2) := by
  let U := Z.image portCoordinate ∪ shortPairedCoordinates N K
  let Q := Uᶜ
  have hU : U.card ≤ Z.card + (shortPairedCoordinates N K).card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right Finset.card_image_le _)
  have hQZ : ∀ q ∈ Q, Sum.inl q ∉ Z ∧ Sum.inr q ∉ Z := by
    intro q hq
    have hnot : q ∉ U := Finset.mem_compl.mp hq
    constructor
    · intro hz
      exact hnot (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Sum.inl q, hz, rfl⟩))
    · intro hz
      exact hnot (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Sum.inr q, hz, rfl⟩))
  have hQshort : ∀ q ∈ Q, q ∉ shortPairedCoordinates N K := by
    intro q hq hshort
    exact (Finset.mem_compl.mp hq) (Finset.mem_union_right _ hshort)
  have hsep := separator_induced_pairs_unreachable N Z K hcomp Q hQZ hQshort
  have hfib : ∀ D : Finset (Q → α), IsStorageCode (inducedNeighborhood N Q) D →
      (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ ((Q.card : ℝ) / 2) := by
    intro D hD
    have h := storageCode_card_le_of_unreachable_pairs (inducedNeighborhood N Q) hsep D hD
    simp only [Fintype.card_coe] at h
    have hnat : (D.card : ℝ) ≤ (Fintype.card α : ℝ) ^ (Q.card / 2) := by
      exact_mod_cast h
    have hfloor : ((Q.card / 2 : ℕ) : ℝ) ≤ (Q.card : ℝ) / 2 := by
      have hn := Nat.mul_div_le Q.card 2
      have hn' : (2 : ℝ) * ((Q.card / 2 : ℕ) : ℝ) ≤ Q.card := by exact_mod_cast hn
      linarith
    exact hnat.trans (by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_le_rpow_left_iff ha).mpr hfloor)
  have hpaid := storageCode_conditioning_bound hC Q (by linarith : 0 < (Fintype.card α : ℝ)) hfib
  have hcompl : Fintype.card {v // v ∉ Q} = U.card := by
    have hUc : U.card ≤ Fintype.card V := Finset.card_le_univ _
    simp only [Fintype.card_subtype_compl, Fintype.card_coe, Q, Finset.card_compl]
    omega
  have hpartition : Q.card + U.card = Fintype.card V := Finset.card_compl_add_card U
  have hpartitionR : (Q.card : ℝ) + U.card = Fintype.card V := by exact_mod_cast hpartition
  have hUR : (U.card : ℝ) ≤ Z.card + (shortPairedCoordinates N K).card := by exact_mod_cast hU
  rw [hcompl] at hpaid
  exact hpaid.trans ((Real.rpow_le_rpow_left_iff ha).mpr (by linarith))

/-- The logarithmic statement of the finite separator theorem for every
nonempty storage code, with the ambient short-pair count `b_E(K)`. -/
theorem storageCode_separator_log_bound [Fintype α] [Nonempty α]
    (N : V → Finset V) (Z : Finset (V ⊕ V)) (K : ℕ)
    (hcomp : HasSmallPortComponents N Z K)
    (ha : 1 < (Fintype.card α : ℝ))
    (C : Finset (V → α)) (hC : IsStorageCode N C) (hCne : C.Nonempty) :
    Real.logb (Fintype.card α) C.card ≤
      ((Fintype.card V : ℝ) + Z.card + (shortPairedCoordinates N K).card) / 2 := by
  have hpos : (0 : ℝ) < C.card := by exact_mod_cast hCne.card_pos
  exact (Real.logb_le_iff_le_rpow ha hpos).mpr (storageCode_separator_bound N Z K hcomp ha C hC)

end DirectedRecovery
