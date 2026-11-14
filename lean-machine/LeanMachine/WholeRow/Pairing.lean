import LeanMachine.InvolutionOmissions
import LeanMachine.WholeRow.ParityReserved

/-! # Whole-row extensions of partially retained pairing shifts

Select omitted nontrivial orbits explicitly. The original fixed-coordinate
shifts remain active, forcing those coordinates to be incident. Reserving
them in the original incidence set cancels the fixed-point term even after
heavy-row trimming pins some of them. All bounds allow nonlinear codes.
-/

namespace LeanMachine.WholeRow

open Finset InvolutionSums
open scoped BigOperators Classical
noncomputable section

variable {R J Λ A : Type*} [Fintype R] [Fintype J] [Fintype Λ]
variable (m : LaneCell R J Λ → LaneCell R J Λ) (hm : Function.Involutive m)
variable (O : Finset (representatives m))
variable [AddCommGroup A] (C : Set (LaneCell R J Λ → A))
variable (hstable : ∀ x ∈ C, ∀ z ∈ activeShifts m hm O, x + z ∈ C)
variable (ρ : J → Finset R)

include hstable in
private theorem pairing_kernel_stable : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
    (activeBlocks m hm O).weightedEncode (weights m) z = 0 →
    Set.EqOn z 0 (↑(omittedCells m hm O)) → x + z ∈ C := by
  classical
  intro x hx z hz hp
  exact hstable x hx z ((active_kernel_iff m hm O z).mp ⟨hz, hp⟩)

include hstable in
/-- Fixed-coordinate shifts are still active initially, so fixed cells are incident. -/
theorem pairing_fixed_incident [Nontrivial A] (hC : C.Nonempty)
    (hrec : RecoversFromRows ρ C) : fixedCells m ⊆ incidentCells ρ := by
  classical
  intro v hv
  have hmv : m v = v := (mem_fixedCells m v).mp hv
  let D := activeBlocks m hm O
  let E : Set (LaneCell R J Λ) := ↑(omittedCells m hm O)
  have hs : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
      (D.withPins E (omitted_free m hm O)).weightedEncode (weights m) z = 0 → x + z ∈ C := by
    intro x hx z hz
    apply hstable x hx z
    rw [← pinned_active_kernel_eq m hm O]
    exact hz
  have hview := (D.withPins E (omitted_free m hm O)).weighted_mem_view_of_free
    (weights m) C hs hC (↑(helperBundle (Λ := Λ) ρ v.2.1)) v (hrec v) (by
      intro p
      cases p with
      | inl p => exact fixed_not_mem_support m hm hmv p.val
      | inr e =>
        change v ∉ ({e.val} : Finset (LaneCell R J Λ))
        simp only [mem_singleton]
        intro he
        exact fixed_not_omitted m hm O hmv (he.symm ▸ e.property))
  exact mem_filter.mpr ⟨mem_univ _, (mem_product.mp hview).1⟩

include hstable in
/-- Exact attained-record count for the explicitly selected active pairing shifts. -/
theorem pairing_record_card_eq (hrec : RecoversFromRows ρ C) :
    Nat.card C = Nat.card (activeShifts (A := A) m hm O) *
      Nat.card ((activeBlocks m hm O).pinnedRecord (↑(omittedCells m hm O))
        (weights m) (recordBlocks (activeBlocks m hm O) ρ) '' C) := by
  classical
  simpa only [pinned_active_kernel_eq] using
    parity_record_card_eq (activeBlocks m hm O) ρ (weights m)
      (↑(omittedCells m hm O)) (omitted_free m hm O) C
      (pairing_kernel_stable m hm O C hstable) (hrec.given _)

include hstable in
/-- Sharp squared bound after any row deletion. Fixed points are reserved against
the original incidence set, while internal records use the trimmed relation. -/
theorem pairing_card_sq_le_after_trim [Fintype A] (hrec : RecoversFromRows ρ C)
    (H : Finset R) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        2 * ((activeBlocks m hm O).touchingBlocks (rowCells H)).card +
        (incidentCells (Λ := Λ) ρ).card + Fintype.card Λ *
          ∑ c, (trimRows ρ H c).card * (overlapColumns (trimRows ρ H) c).card) := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl h =>
    have hc := Nat.card_le_card_of_injective (Subtype.val : C → (LaneCell R J Λ → A))
      Subtype.val_injective
    have hq : Fintype.card A = 1 := Fintype.card_eq_one_iff.mpr ⟨0, fun _ => Subsingleton.elim _ _⟩
    simpa [Nat.card_eq_fintype_card, hq] using Nat.pow_le_pow_left hc 2
  | inr h =>
    by_cases hC : C.Nonempty
    · let D := activeBlocks m hm O
      let F := rowCells (J := J) (Λ := Λ) H
      let E : Set (LaneCell R J Λ) := ↑(omittedCells m hm O)
      let E' := D.deletionPins F E
      have hrec' : RecoversFromRowsGiven (trimRows ρ H) E' C :=
        (hrec.given E).trim H (fun _ he => Or.inl (Or.inl he))
          (fun _ hv => Or.inl (Or.inr hv))
      have hs : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
          (D.deleteTouching F).weightedEncode (weights m) z = 0 →
          Set.EqOn z 0 E' → x + z ∈ C := by
        intro x hx z hz hp
        exact pairing_kernel_stable m hm O C hstable x hx z
          (D.deleted_kernel_le F E (weights m) z hz hp)
          (hp.mono (fun _ he => Or.inl (Or.inl he)))
      have hbound := parity_card_sq_le_reserved (D.deleteTouching F) (trimRows ρ H) ρ
        (weights m) E' (D.deletionPins_free F E (omitted_free m hm O)) C hs hrec'
        (fun p => by simpa [D, DisjointSums.deleteTouching, DisjointSums.restrictBlocks,
          activeBlocks] using le_of_eq (support_card m hm p.val.val).symm)
        (fun _ => sdiff_subset) (fixedCells m)
        (pairing_fixed_incident m hm O C hstable ρ hC hrec)
        (fun p v hv => fixed_not_mem_support m hm ((mem_fixedCells m v).mp hv) p.val.val)
      have hpart := active_card_partition m hm O
      have ht := card_le_univ (D.touchingBlocks F)
      rw [D.card_deleteTouching F] at hbound
      simp only [Fintype.card_coe, card_compl] at hpart ht hbound
      have he : 2 * (Fintype.card (LaneCell R J Λ) -
          ((representatives m).card - O.card - (D.touchingBlocks F).card)) - (fixedCells m).card =
          Fintype.card (LaneCell R J Λ) + 2 * O.card + 2 * (D.touchingBlocks F).card := by
        omega
      rw [he] at hbound
      exact hbound
    · rw [Set.not_nonempty_iff_eq_empty.mp hC]
      simp

include hstable in
/-- The fixed-cell term cancels exactly, including with omitted pairs. -/
theorem pairing_card_sq_le_incidence [Fintype A] (hrec : RecoversFromRows ρ C) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        (incidentCells (Λ := Λ) ρ).card +
        Fintype.card Λ * ∑ c, (ρ c).card * (overlapColumns ρ c).card) := by
  classical
  have ht : trimRows ρ ∅ = ρ := by funext c; simp [trimRows]
  simpa [rowCells, ht, DisjointSums.touchingBlocks] using
    pairing_card_sq_le_after_trim m hm O C hstable ρ hrec ∅

include hstable in
/-- Sharp bounded-degree pairing bound, without a leftover fixed-point term. -/
theorem pairing_card_sq_le_degrees [Fintype A] (hrec : RecoversFromRows ρ C)
    (w t : ℕ) (hf : ∀ c, (ρ c).card ≤ w)
    (hrev : ∀ a, (univ.filter (fun c => a ∈ ρ c)).card ≤ t) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        Fintype.card Λ * Fintype.card J * (w + w * w * t)) := by
  classical
  apply (pairing_card_sq_le_incidence m hm O C hstable ρ hrec).trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  have h := mixed_incidence_budget_le (Λ := Λ) ρ ρ w t hf hf hrev
  omega

include hstable in
/-- Forward width alone suffices, with one symbol per omitted or newly marked pair. -/
theorem pairing_card_sq_le_forward [Fintype A] (hrec : RecoversFromRows ρ C)
    (w t : ℕ) (hf : ∀ c, (ρ c).card ≤ w) :
    Nat.card C ^ 2 ≤ Fintype.card A ^
      (Fintype.card (LaneCell R J Λ) + 2 * O.card +
        2 * (Fintype.card Λ * Fintype.card J * (w * Fintype.card J / (t + 1))) +
        Fintype.card Λ * Fintype.card J * (w + w * w * t)) := by
  classical
  let H := heavyRows ρ t
  have h := pairing_card_sq_le_after_trim m hm O C hstable ρ hrec H
  have hc := mixed_incidence_budget_le (Λ := Λ) (trimRows ρ H) ρ w t
    (fun c => (card_le_card sdiff_subset).trans (hf c)) hf (reverse_trimRows_heavy_le ρ t)
  have ht := (activeBlocks m hm O).touchingBlocks_card_le (rowCells (J := J) (Λ := Λ) H)
  rw [card_rowCells] at ht
  have hH := (Nat.le_div_iff_mul_le (Nat.succ_pos t)).mpr (heavyRows_card_mul_succ_le ρ w t hf)
  have hp : ((activeBlocks m hm O).touchingBlocks (rowCells H)).card ≤
      Fintype.card Λ * Fintype.card J * (w * Fintype.card J / (t + 1)) :=
    ht.trans (Nat.mul_le_mul_left (Fintype.card Λ * Fintype.card J) hH)
  apply h.trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  omega

private theorem pairing_error_precision (b d w n : ℕ)
    (hd : n * (w + w * w * (2 * w * n)) ≤ d) :
    n * (2 * (b * d * (w * d / (2 * w * n + 1))) +
      b * d * (w + w * w * (2 * w * n))) ≤ 2 * (b * d ^ 2) := by
  classical
  by_cases hw : w = 0
  · simp [hw]
  · have hq := Nat.div_mul_le_self (w * d) (2 * w * n + 1)
    have hq' : 2 * n * (w * d / (2 * w * n + 1)) ≤ d := by
      apply le_of_mul_le_mul_left (a := w) ?_ (Nat.pos_of_ne_zero hw)
      calc
        w * (2 * n * (w * d / (2 * w * n + 1))) =
            (w * d / (2 * w * n + 1)) * (2 * w * n) := by ring
        _ ≤ (w * d / (2 * w * n + 1)) * (2 * w * n + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ ≤ w * d := hq
    have h₁ := Nat.mul_le_mul_left (b * d) hq'
    have h₂ := Nat.mul_le_mul_left (b * d) hd
    nlinarith

include hstable in
/-- Uniform half-rate plus the omitted-pair density and precision `1/n`.
The finite inequality includes empty codes and trivial alphabets; its rate
reading uses positive `n`, nonzero size, and an alphabet of size at least two. -/
theorem pairing_card_pow_le_half [Fintype A] (hrec : RecoversFromRows ρ C)
    (w n : ℕ) (hf : ∀ c, (ρ c).card ≤ w)
    (hsquare : Fintype.card R = Fintype.card J)
    (hd : n * (w + w * w * (2 * w * n)) ≤ Fintype.card J) :
    Nat.card C ^ (2 * n) ≤ Fintype.card A ^
      (n * (Fintype.card (LaneCell R J Λ) + 2 * O.card) +
        2 * Fintype.card (LaneCell R J Λ)) := by
  classical
  have h := pairing_card_sq_le_forward m hm O C hstable ρ hrec w (2 * w * n) hf
  have he := pairing_error_precision (Fintype.card Λ) (Fintype.card J) w n hd
  have hN : Fintype.card (LaneCell R J Λ) = Fintype.card Λ * Fintype.card J ^ 2 := by
    simp only [LaneCell, Fintype.card_prod, hsquare, pow_two,
      Nat.mul_comm, Nat.mul_left_comm]
  have hp := Nat.pow_le_pow_left h n
  simp only [← pow_mul] at hp
  apply hp.trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  rw [hN] at *
  nlinarith

end
end LeanMachine.WholeRow
