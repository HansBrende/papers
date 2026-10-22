import TransposeFollowup.PacketComponentCount
import TransposeFollowup.CoordinateEntropy

/-! Exact views and record lengths for a selected family of packet components.
No distributional independence is assumed. -/

namespace TransposeFollowup.CoordinateSystem

open Classical
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [Fintype V] {B : ℕ} (C : CoordinateSystem V B)

noncomputable def outsideCoordinates (U : Finset (Finset V)) : Finset V :=
  Finset.univ \ U.biUnion id

noncomputable def selectedPackets (U : Finset (Finset V)) : Finset (Fin B) :=
  U.biUnion C.packetIndices

theorem broadcast_eq_of_selected (U : Finset (Finset V))
    (hU : U ⊆ C.components) {y y' : V → Bool}
    (hout : ∀ v ∈ outsideCoordinates U, y v = y' v)
    (hin : ∀ k ∈ C.selectedPackets U, (C.packet k).eval y = (C.packet k).eval y') :
    C.broadcast y = C.broadcast y' := by
  funext k
  by_cases hk : k ∈ C.selectedPackets U
  · exact hin k hk
  · apply (C.packet k).eval_congr
    intro v hv
    apply hout v
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hvU
    obtain ⟨S, hSU, hvS⟩ := Finset.mem_biUnion.mp hvU
    exact hk (Finset.mem_biUnion.mpr ⟨S, hSU,
      (C.mem_packetIndices S k).mpr ⟨⟨v, hv⟩,
        C.support_subset_component k (hU hSU) hv hvS⟩⟩)

theorem broadcast_eq_of_local_views (U : Finset (Finset V))
    (hU : U ⊆ C.components) {y y' : V → Bool}
    (hout : bitView (outsideCoordinates U) y = bitView (outsideCoordinates U) y')
    (hin : ∀ S ∈ U, bitView (C.packetIndices S) (C.broadcast y) =
      bitView (C.packetIndices S) (C.broadcast y')) :
    C.broadcast y = C.broadcast y' := by
  apply C.broadcast_eq_of_selected U hU
  · exact (bitView_eq_iff _ _ _).mp hout
  · intro k hk
    obtain ⟨S, hS, hkS⟩ := Finset.mem_biUnion.mp hk
    exact (bitView_eq_iff _ _ _).mp (hin S hS) k hkS

omit [Fintype V] in
theorem local_packet_view_factors (S : Finset V) :
    (fun y => bitView (C.packetIndices S) (C.broadcast y)).FactorsThrough (bitView S) := by
  intro y y' h
  apply (bitView_eq_iff _ _ _).mpr
  intro k hk
  apply (C.packet k).eval_congr
  intro v hv
  exact (bitView_eq_iff _ _ _).mp h v (((C.mem_packetIndices S k).mp hk).2 hv)

theorem selected_view_factors (U : Finset (Finset V))
    (hU : U ⊆ C.components) :
    (fun y => (bitView (outsideCoordinates U) y, C.broadcast y)).FactorsThrough
      (fun y => (bitView (outsideCoordinates U) y,
        bitView (C.selectedPackets U) (C.broadcast y))) := by
  intro y y' h
  have he : bitView (outsideCoordinates U) y = bitView (outsideCoordinates U) y' :=
    congrArg (fun z : (V → Bool) × (Fin B → Bool) => z.1) h
  refine Prod.ext he ?_
  apply C.broadcast_eq_of_selected U hU
  · exact (bitView_eq_iff _ _ _).mp he
  · exact (bitView_eq_iff _ _ _).mp (congrArg Prod.snd h)

theorem deficient_packet_card {S : Finset V} (hS : S ∈ C.deficient) :
    (C.packetIndices S).card + 1 = S.card := by
  obtain ⟨hcomp, hlt⟩ := (C.mem_deficient S).mp hS
  have hle := C.component_card_le_packets_add_one hcomp
  omega

/-- Exactly one omitted record bit per selected deficient component. -/
theorem selected_record_card (U : Finset (Finset V)) (hU : U ⊆ C.deficient) :
    (outsideCoordinates U).card + (C.selectedPackets U).card + U.card =
      Fintype.card V := by
  have hcomp : U ⊆ C.components := fun _ h => ((C.mem_deficient _).mp (hU h)).1
  have hd : (U : Set (Finset V)).PairwiseDisjoint id := by
    intro S hS T hT hne
    exact C.components_disjoint (hcomp hS) (hcomp hT) hne
  have hp : (U : Set (Finset V)).PairwiseDisjoint C.packetIndices := by
    intro S hS T hT hne
    exact C.packetIndices_disjoint (hcomp hS) (hcomp hT) hne
  have hcards : (U.biUnion id).card = ∑ S ∈ U, S.card := by
    simpa using Finset.card_biUnion hd
  have hpackets : (C.selectedPackets U).card = ∑ S ∈ U, (C.packetIndices S).card :=
    Finset.card_biUnion hp
  have hsum : (∑ S ∈ U, (C.packetIndices S).card) + U.card = ∑ S ∈ U, S.card := by
    calc
      _ = ∑ S ∈ U, ((C.packetIndices S).card + 1) := by simp [Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl (fun S hS => C.deficient_packet_card (hU hS))
  have hout : (outsideCoordinates U).card + (U.biUnion id).card = Fintype.card V := by
    simpa only [outsideCoordinates, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (U.biUnion id))
  omega

end TransposeFollowup.CoordinateSystem
