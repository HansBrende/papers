import LeanMachine.WholeRow.ParityTrimming

/-! # Reserved free coordinates in the parity record count

Incident coordinates outside every active parity block, possibly pinned,
reduce the all-incident block budget. The enclosing incidence set may
come from a larger original relation while recovery uses trimmed helpers.
This retains the fixed-coordinate correction after heavy-row deletion.
-/

namespace LeanMachine.WholeRow

open Finset
open scoped BigOperators Classical
noncomputable section

variable {R J Λ κ A : Type*} [Fintype R] [Fintype J] [Fintype Λ] [Fintype κ]
variable (D : DisjointSums (LaneCell R J Λ) κ)

omit [Fintype R] [Fintype J] [Fintype Λ] [Fintype κ] in
private theorem packing_reserved (K : Finset κ) (S W : Finset (LaneCell R J Λ))
    (hsize : ∀ k ∈ K, 2 ≤ (D.support k).card)
    (hsub : ∀ k ∈ K, D.support k ⊆ W) (hS : S ⊆ W)
    (hfree : ∀ k, ∀ v ∈ S, v ∉ D.support k) :
    2 * K.card + S.card ≤ W.card := by
  have hc : 2 * K.card ≤ (K.biUnion D.support).card := by
    calc
      _ = ∑ _k ∈ K, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ k ∈ K, (D.support k).card := sum_le_sum hsize
      _ = _ := (card_biUnion (fun k _ l _ h => D.disjoint h)).symm
  have hd : Disjoint (K.biUnion D.support) S := by
    rw [disjoint_left]
    intro v hv hs
    obtain ⟨k, _, hk⟩ := mem_biUnion.mp hv
    exact hfree k v hs hk
  calc
    _ ≤ (K.biUnion D.support).card + S.card := Nat.add_le_add_right hc _
    _ = (K.biUnion D.support ∪ S).card := (card_union_of_disjoint hd).symm
    _ ≤ W.card := card_le_card (union_subset (biUnion_subset.mpr hsub) hS)

variable (ρ ρ₀ : J → Finset R)

/-- Original incidences and trimmed internal records can use different relations. -/
theorem mixed_incidence_budget_le (w t : ℕ)
    (hf : ∀ c, (ρ c).card ≤ w) (hf₀ : ∀ c, (ρ₀ c).card ≤ w)
    (hrev : ∀ a, (univ.filter (fun c => a ∈ ρ c)).card ≤ t) :
    (incidentCells (Λ := Λ) ρ₀).card +
      Fintype.card Λ * ∑ c, (ρ c).card * (overlapColumns ρ c).card ≤
      Fintype.card Λ * Fintype.card J * (w + w * w * t) := by
  rw [card_incidentCells, ← Nat.mul_add]
  have h₁ := sum_le_sum (fun c (_ : c ∈ (univ : Finset J)) => hf₀ c)
  have h₂ : (∑ c, (ρ c).card * (overlapColumns ρ c).card) ≤
      ∑ _c : J, w * w * t := by
    apply sum_le_sum
    intro c _
    have hov := (overlapColumns_card_le ρ c t hrev).trans (Nat.mul_le_mul_right t (hf c))
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul (hf c) hov
  have h := Nat.mul_le_mul_left (Fintype.card Λ) (Nat.add_le_add h₁ h₂)
  simpa only [sum_const, card_univ, smul_eq_mul, ← Nat.mul_add, Nat.mul_assoc] using h

variable [AddCommGroup A] (θ : LaneCell R J Λ → A ≃+ A)
variable (E : Set (LaneCell R J Λ)) (hfree : ∀ k, ∀ v ∈ E, v ∉ D.support k)
variable (C : Set (LaneCell R J Λ → A))
variable (hstable : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
  D.weightedEncode θ z = 0 → Set.EqOn z 0 E → x + z ∈ C)

include hstable hfree in
/-- Reserved incident coordinates outside active blocks reduce the record budget.
The original relation may be larger than the actual recovery relation. -/
theorem recordBlocks_card_bound_reserved [Nontrivial A] (hC : C.Nonempty)
    (hrec : RecoversFromRowsGiven ρ E C)
    (hsize : ∀ k, 2 ≤ (D.support k).card) (hρ : ∀ c, ρ c ⊆ ρ₀ c)
    (S : Finset (LaneCell R J Λ)) (hS : S ⊆ incidentCells ρ₀)
    (hSf : ∀ k, ∀ v ∈ S, v ∉ D.support k) :
    2 * (recordBlocks D ρ).card + S.card ≤ (incidentCells (Λ := Λ) ρ₀).card +
      Fintype.card Λ * ∑ c, (ρ c).card * (overlapColumns ρ c).card := by
  have hinc := packing_reserved D (incidentBlocks D ρ) S (incidentCells ρ₀)
    (fun k _ => hsize k) (fun k hk v hv => by
      have hi := (mem_filter.mp ((mem_filter.mp hk).2 hv)).2
      exact mem_filter.mpr ⟨mem_univ _, hρ v.2.1 hi⟩) hS hSf
  have hint (c : J) : 2 * (internalBlocks D ρ c).card ≤
      Fintype.card Λ * ((ρ c).card * (overlapColumns ρ c).card) := by
    have h := packing_reserved D (internalBlocks D ρ c) ∅
      ((ρ c) ×ˢ ((overlapColumns ρ c) ×ˢ (univ : Finset Λ)))
      (fun k _ => hsize k) (fun k hk =>
        internal_support_subset_rectangle D ρ θ E hfree C hstable hC hrec c k hk (hsize k))
      (empty_subset _) (by simp)
    simpa only [card_empty, add_zero, card_product, card_univ,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hr : (recordBlocks D ρ).card ≤
      (incidentBlocks D ρ).card + ∑ c, (internalBlocks D ρ c).card :=
    (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)
  have hs := sum_le_sum (fun c (_ : c ∈ (univ : Finset J)) => hint c)
  simp only [← mul_sum] at hs
  omega

include hstable hfree in
/-- A squared-cardinality form retains the reserved-coordinate saving exactly. -/
theorem parity_card_sq_le_reserved [Fintype A]
    (hrec : RecoversFromRowsGiven ρ E C)
    (hsize : ∀ k, 2 ≤ (D.support k).card) (hρ : ∀ c, ρ c ⊆ ρ₀ c)
    (S : Finset (LaneCell R J Λ)) (hS : S ⊆ incidentCells ρ₀)
    (hSf : ∀ k, ∀ v ∈ S, v ∉ D.support k) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (2 * (Fintype.card (LaneCell R J Λ) - Fintype.card κ) - S.card +
        (incidentCells (Λ := Λ) ρ₀).card +
        Fintype.card Λ * ∑ c, (ρ c).card * (overlapColumns ρ c).card) := by
  have hc := parity_card_le_record D ρ θ E hfree C hstable hrec
  cases subsingleton_or_nontrivial A with
  | inl h =>
    have hq : Fintype.card A = 1 := Fintype.card_eq_one_iff.mpr ⟨0, fun _ => Subsingleton.elim _ _⟩
    simpa only [hq, one_pow] using Nat.pow_le_pow_left hc 2
  | inr h =>
    by_cases hC : C.Nonempty
    · have hs := recordBlocks_card_bound_reserved D ρ ρ₀ θ E hfree C hstable
        hC hrec hsize hρ S hS hSf
      have hf := (D.withPins (↑S) hSf).card_le
      simp only [Fintype.card_sum] at hf
      have hp := Nat.pow_le_pow_left hc 2
      rw [← pow_mul] at hp
      apply hp.trans
      apply Nat.pow_le_pow_right Fintype.card_pos
      omega
    · rw [Set.not_nonempty_iff_eq_empty.mp hC]
      simp

end
end LeanMachine.WholeRow
