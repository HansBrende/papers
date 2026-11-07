import DirectedRecovery.StorageCode

/-! # Counting a common fibre and conditioning arbitrary packet alphabets -/

namespace TapeStorageRates

open Finset DirectedRecovery MotionDepthCodes

set_option autoImplicit false

/-- A most frequent attained value pays at most the number of distinct observations on the set. -/
theorem exists_large_observation_fibre {X Y : Type*} [DecidableEq Y] {S : Finset X}
    (hne : S.Nonempty) (f : X → Y) :
    ∃ y ∈ S.image f, S.card ≤ (S.image f).card * (S.filter (fun x => f x = y)).card := by
  obtain ⟨y, hy, hmax⟩ := exists_max_image (S.image f)
    (fun a => (S.filter (fun x => f x = a)).card) (hne.image f)
  refine ⟨y, hy, ?_⟩
  calc
    S.card = ∑ a ∈ S.image f, (S.filter (fun x => f x = a)).card :=
      card_eq_sum_card_fiberwise (fun _ hx => mem_image_of_mem f hx)
    _ ≤ ∑ _a ∈ S.image f, (S.filter (fun x => f x = y)).card :=
      sum_le_sum hmax
    _ = _ := by simp

open Classical in
/-- Fix the omitted coordinates and retain one genuine projected fibre. Its absolute
information deficit cannot increase. The retained coordinates can be chosen using the graph. -/
theorem exists_large_conditioned_code {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    {N : V → Finset V} {C : Finset (V → A)} (hC : IsStorageCode N C) (hne : C.Nonempty)
    (Q : Finset V) :
    ∃ z, (conditionedCode C Q z).Nonempty ∧
      IsStorageCode (inducedNeighborhood N Q) (conditionedCode C Q z) ∧
      C.card ≤ Fintype.card A ^ Qᶜ.card * (conditionedCode C Q z).card := by
  obtain ⟨z, hz, hcard⟩ := exists_large_observation_fibre hne (outsideWord Q)
  obtain ⟨x, hx, hxz⟩ := mem_image.mp hz
  refine ⟨z, ?_, isStorageCode_conditionedCode hC Q z, ?_⟩
  · exact ⟨restrictWord Q x, mem_image_of_mem _ (mem_filter.mpr ⟨hx, hxz⟩)⟩
  rw [conditionedCode_card]
  apply hcard.trans (Nat.mul_le_mul_right _ ?_)
  calc
    (C.image (outsideWord Q)).card ≤ Fintype.card ({v // v ∉ Q} → A) := card_le_univ _
    _ = Fintype.card A ^ Qᶜ.card := by
      rw [Fintype.card_fun]
      congr 1
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => mem_compl.symm)) |>.trans
        (Fintype.card_coe _)

end TapeStorageRates
