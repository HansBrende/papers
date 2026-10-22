import TransposeFollowup.DisjointFlipOrbit
import TransposeFollowup.ComponentDistance
import TransposeFollowup.PacketDistanceBound

/-! The original XOR distance bounds specialize the arbitrary Boolean-packet
theorem. The XOR-specific component and free-flip statements remain available
independently. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u

namespace XorSystem

variable {V : Type u} [Fintype V] {B : ℕ} (C : XorSystem V B)

theorem components_disjoint : (C.components : Set (Finset V)).PairwiseDisjoint id :=
  graphComponents_pairwise_disjoint C.graph ∅

theorem unanchored_disjoint : (C.unanchored : Set (Finset V)).PairwiseDisjoint id := by
  intro S hS T hT hne
  exact C.components_disjoint (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hT).1 hne

theorem unanchored_nonempty {S : Finset V} (hS : S ∈ C.unanchored) : S.Nonempty :=
  C.component_nonempty (Finset.mem_filter.mp hS).1

noncomputable def smallComponents (ell : ℕ) : Finset (Finset V) :=
  C.unanchored.filter (fun S => S.card ≤ ell)

theorem mem_smallComponents (ell : ℕ) (S : Finset V) :
    S ∈ C.smallComponents ell ↔ S ∈ C.unanchored ∧ S.card ≤ ell := by
  simp only [smallComponents, Finset.mem_filter]

theorem smallComponents_disjoint (ell : ℕ) :
    (C.smallComponents ell : Set (Finset V)).PairwiseDisjoint id := by
  intro S hS T hT hne
  exact C.unanchored_disjoint (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hT).1 hne

theorem unanchored_size_bound (ell : ℕ) :
    (ell + 1) * C.unanchored.card ≤ Fintype.card V + ell * (C.smallComponents ell).card :=
  disjoint_family_size_bound C.unanchored (fun _ h => C.unanchored_nonempty h)
    C.unanchored_disjoint ell

end XorSystem

namespace RecodedXorCode

variable {n b B : ℕ} (C : RecodedXorCode n b B)

theorem small_component_count_le_near (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (ell : ℕ) :
    (C.system.smallComponents ell).card ≤ (nearBits (b := b) G ell).card := by
  apply C.flip_orbit_bound (C.system.smallComponents ell)
    (fun S h => C.system.unanchored_nonempty ((C.system.mem_smallComponents ell S).mp h).1)
    (C.system.smallComponents_disjoint ell) (nearBits G ell)
  intro S hS x v hv
  obtain ⟨hu, hs⟩ := (C.system.mem_smallComponents ell S).mp hS
  exact C.small_flip_preserves_far hc G hG hu ell hs x v hv

/-- Integral form of B1. No division, positivity or connectedness assumptions
are needed; ell=0 also gives a valid (though vacuous) inequality. -/
theorem broadcast_lower_bound_scaled (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (ell : ℕ) :
    (ell + 1) * (n * n * b) ≤ (ell + 1) * B + n * n * b +
      ell * (nearBits (b := b) G ell).card :=
  C.toRecodedPacketCode.broadcast_lower_bound_scaled
    (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG) ell

/-- B >= P-(P+ell Q_ell)/(ell+1), with Q_ell counted in raw bit coordinates.
The complete decoding and nonlinear recoding assumptions are explicit. -/
theorem broadcast_lower_bound (hc : C.Correct) (G : SimpleGraph (Fin n))
    (hG : C.LocalTo G) (ell : ℕ) :
    (B : ℝ) ≥ (n * n * b : ℕ) -
      (((n * n * b : ℕ) : ℝ) + ell * (nearBits (b := b) G ell).card) / (ell + 1) :=
  C.toRecodedPacketCode.broadcast_lower_bound
    (C.toRecodedPacketCode_correct hc) G (C.toRecodedPacketCode_local G hG) ell

end RecodedXorCode
end TransposeFollowup
