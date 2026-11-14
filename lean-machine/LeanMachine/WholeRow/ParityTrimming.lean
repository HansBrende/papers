import LeanMachine.WholeRow.ParityTemplate
import LeanMachine.DisjointSumsDeletion

/-! # Paid heavy-row trimming for parity-template extensions

Record the heavy rows and all active blocks meeting them. Recovery on the
trimmed relation uses this common raw record. Its raw size cancels the loss
of kernel dimensions, leaving one symbol per discarded block. The resulting
finite bound assumes only forward width, and keeps rectangular and lane
counts explicit.
-/

namespace LeanMachine.WholeRow

open Finset
open scoped BigOperators Classical
noncomputable section

variable {R J Λ κ A : Type*} [Fintype R] [Fintype J] [Fintype Λ] [Fintype κ]

/-- All lane coordinates in the rows being recorded. -/
def rowCells (H : Finset R) : Finset (LaneCell R J Λ) := H ×ˢ (univ ×ˢ univ)

/-- Remove the recorded rows from each helper bundle. -/
def trimRows (ρ : J → Finset R) (H : Finset R) (c : J) : Finset R := ρ c \ H

/-- Rows used by more columns than the chosen reverse-degree threshold. -/
def heavyRows (ρ : J → Finset R) (t : ℕ) : Finset R :=
  univ.filter (fun r => t < (univ.filter (fun c => r ∈ ρ c)).card)

omit [Fintype R] in
/-- The exact coordinate cost of a row record, also for rectangular arrays. -/
theorem card_rowCells (H : Finset R) :
    (rowCells (J := J) (Λ := Λ) H).card = Fintype.card Λ * Fintype.card J * H.card := by
  simp only [rowCells, card_product, card_univ, Nat.mul_comm]

/-- A strict reverse threshold gives its successor in the incidence budget. -/
theorem heavyRows_card_mul_succ_le (ρ : J → Finset R) (w t : ℕ)
    (hf : ∀ c, (ρ c).card ≤ w) :
    (heavyRows ρ t).card * (t + 1) ≤ w * Fintype.card J := by
  have hsum : (∑ r : R, (univ.filter (fun c => r ∈ ρ c)).card) =
      ∑ c : J, (ρ c).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    simp
  calc
    _ = ∑ _r ∈ heavyRows ρ t, (t + 1) := by simp
    _ ≤ ∑ r ∈ heavyRows ρ t, (univ.filter (fun c => r ∈ ρ c)).card :=
      sum_le_sum (fun _ hr => (mem_filter.mp hr).2)
    _ ≤ ∑ r : R, (univ.filter (fun c => r ∈ ρ c)).card :=
      sum_le_sum_of_subset (subset_univ _)
    _ = ∑ c : J, (ρ c).card := hsum
    _ ≤ ∑ _c : J, w := sum_le_sum (fun c _ => hf c)
    _ = _ := by simp [Nat.mul_comm]

/-- Heavy-row deletion bounds every reverse degree, including threshold zero. -/
theorem reverse_trimRows_heavy_le (ρ : J → Finset R) (t : ℕ) (r : R) :
    (univ.filter (fun c => r ∈ trimRows ρ (heavyRows ρ t) c)).card ≤ t := by
  by_cases hr : r ∈ heavyRows ρ t
  · simp [trimRows, hr]
  · have h := hr
    simp only [heavyRows, mem_filter, mem_univ, true_and, not_lt] at h
    simpa [trimRows, hr] using h

omit [Fintype R] in
/-- Original recovery survives trimming when the deleted rows are in the raw record. -/
theorem RecoversFromRowsGiven.trim {ρ : J → Finset R} {C : Set (LaneCell R J Λ → A)}
    {E E' : Set (LaneCell R J Λ)} (hrec : RecoversFromRowsGiven ρ E C)
    (H : Finset R) (hE : E ⊆ E')
    (hH : (↑(rowCells (J := J) (Λ := Λ) H) : Set (LaneCell R J Λ)) ⊆ E') :
    RecoversFromRowsGiven (trimRows ρ H) E' C := by
  intro v x hx y hy hxy
  apply hrec v x hx y hy
  intro u hu
  apply hxy
  rcases hu with hu | hu
  · have hr := (mem_product.mp hu).1
    by_cases hrow : u.1 ∈ H
    · exact Or.inr (hH (mem_product.mpr ⟨hrow, mem_product.mpr ⟨mem_univ _, mem_univ _⟩⟩))
    · exact Or.inl (mem_product.mpr
        ⟨mem_sdiff.mpr ⟨hr, hrow⟩, mem_product.mpr ⟨mem_univ _, mem_univ _⟩⟩)
  · exact Or.inr (hE hu)

variable (D : DisjointSums (LaneCell R J Λ) κ) (ρ : J → Finset R)
variable [AddCommGroup A] (θ : LaneCell R J Λ → A ≃+ A)
variable (E : Set (LaneCell R J Λ)) (hfree : ∀ k, ∀ v ∈ E, v ∉ D.support k)
variable (C : Set (LaneCell R J Λ → A))
variable (hstable : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
  D.weightedEncode θ z = 0 → Set.EqOn z 0 E → x + z ∈ C)

include hstable hfree in
/-- Exact deletion price: one symbol per active block touching the recorded rows.
The raw record is not charged a second time. -/
theorem parity_card_le_delete_rows [Fintype A]
    (hrec : RecoversFromRowsGiven ρ E C) (H : Finset R)
    (r : ℕ) (hr : 2 ≤ r) (hsize : ∀ k, r ≤ (D.support k).card)
    (w t : ℕ) (hf : ∀ c, (ρ c).card ≤ w)
    (hrev : ∀ a, (univ.filter (fun c => a ∈ trimRows ρ H c)).card ≤ t) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card (LaneCell R J Λ) - Fintype.card κ +
      (D.touchingBlocks (rowCells H)).card +
      (Fintype.card Λ * Fintype.card J * (w + w * w * t)) / r) := by
  let F := rowCells (J := J) (Λ := Λ) H
  let E' := D.deletionPins F E
  have hrec' : RecoversFromRowsGiven (trimRows ρ H) E' C :=
    hrec.trim H (fun _ he => Or.inl (Or.inl he)) (fun _ hv => Or.inl (Or.inr hv))
  have hstable' : ∀ x ∈ C, ∀ z : LaneCell R J Λ → A,
      (D.deleteTouching F).weightedEncode θ z = 0 → Set.EqOn z 0 E' → x + z ∈ C := by
    intro x hx z hz hp
    exact hstable x hx z (D.deleted_kernel_le F E θ z hz hp)
      (hp.mono (fun _ he => Or.inl (Or.inl he)))
  have h := parity_card_le_degrees (D.deleteTouching F) (trimRows ρ H) θ E'
    (D.deletionPins_free F E hfree) C hstable' hrec' r hr (fun k => hsize k.val)
    w t (fun c => (card_le_card sdiff_subset).trans (hf c)) hrev
  rw [D.card_deleteTouching F] at h
  have hm := D.card_le
  have ht := card_le_univ (D.touchingBlocks F)
  have he : Fintype.card (LaneCell R J Λ) -
      (Fintype.card κ - (D.touchingBlocks F).card) =
      Fintype.card (LaneCell R J Λ) - Fintype.card κ + (D.touchingBlocks F).card := by
    omega
  rw [he] at h
  exact h

include hstable hfree in
/-- Forward-width-only bound. The rectangular row payment retains its exact floor. -/
theorem parity_card_le_forward [Fintype A]
    (hrec : RecoversFromRowsGiven ρ E C)
    (r : ℕ) (hr : 2 ≤ r) (hsize : ∀ k, r ≤ (D.support k).card)
    (w t : ℕ) (hf : ∀ c, (ρ c).card ≤ w) :
    Nat.card C ≤ Fintype.card A ^ (Fintype.card (LaneCell R J Λ) - Fintype.card κ +
      Fintype.card Λ * Fintype.card J * (w * Fintype.card J / (t + 1)) +
      (Fintype.card Λ * Fintype.card J * (w + w * w * t)) / r) := by
  have h := parity_card_le_delete_rows D ρ θ E hfree C hstable hrec (heavyRows ρ t)
    r hr hsize w t hf (reverse_trimRows_heavy_le ρ t)
  apply h.trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply (D.touchingBlocks_card_le (rowCells (J := J) (Λ := Λ) (heavyRows ρ t))).trans
  rw [card_rowCells]
  apply Nat.mul_le_mul_left
  exact (Nat.le_div_iff_mul_le (Nat.succ_pos t)).mpr
    (heavyRows_card_mul_succ_le ρ w t hf)

private theorem forward_error_mul_le (b d w r n : ℕ) (hr : 2 ≤ r)
    (hd : n * (w + w * w * (2 * w * n)) ≤ d) :
    n * (b * d * (w * d / (2 * w * n + 1)) +
      b * d * (w + w * w * (2 * w * n)) / r) ≤ b * d ^ 2 := by
  by_cases hw : w = 0
  · simp [hw]
  · have hwpos : 0 < w := Nat.pos_of_ne_zero hw
    have hq := Nat.div_mul_le_self (w * d) (2 * w * n + 1)
    have hq' : 2 * n * (w * d / (2 * w * n + 1)) ≤ d := by
      apply le_of_mul_le_mul_left (a := w) ?_ hwpos
      calc
        w * (2 * n * (w * d / (2 * w * n + 1))) =
            (w * d / (2 * w * n + 1)) * (2 * w * n) := by ring
        _ ≤ (w * d / (2 * w * n + 1)) * (2 * w * n + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ ≤ w * d := hq
    have hfirst := Nat.mul_le_mul_left (b * d) hq'
    have hs := Nat.div_mul_le_self (b * d * (w + w * w * (2 * w * n))) r
    have hsecond : 2 * (b * d * (w + w * w * (2 * w * n)) / r) ≤
        b * d * (w + w * w * (2 * w * n)) := by
      exact (Nat.mul_le_mul_right _ hr).trans (by simpa only [Nat.mul_comm] using hs)
    have hsecond' := Nat.mul_le_mul_left n hsecond
    have hdim := Nat.mul_le_mul_left (b * d) hd
    nlinarith

include hstable hfree in
/-- Uniform vanishing excess over the active-template baseline on square-size arrays.
The baseline is `1 - m/N`, with `m` the active blocks disjoint from the pins;
it is not automatically the pairing half-rate.
For precision `1/n`, one explicit dimension threshold suffices for every alphabet,
lane count, template and helper relation of forward width `w`. No reverse cap remains. -/
theorem parity_card_pow_le_baseline [Fintype A]
    (hrec : RecoversFromRowsGiven ρ E C)
    (r : ℕ) (hr : 2 ≤ r) (hsize : ∀ k, r ≤ (D.support k).card)
    (w n : ℕ) (hf : ∀ c, (ρ c).card ≤ w)
    (hsquare : Fintype.card R = Fintype.card J)
    (hd : n * (w + w * w * (2 * w * n)) ≤ Fintype.card J) :
    Nat.card C ^ n ≤ Fintype.card A ^
      (n * (Fintype.card (LaneCell R J Λ) - Fintype.card κ) +
        Fintype.card (LaneCell R J Λ)) := by
  have h := parity_card_le_forward D ρ θ E hfree C hstable hrec r hr hsize
    w (2 * w * n) hf
  have he := forward_error_mul_le (Fintype.card Λ) (Fintype.card J) w r n hr hd
  have hN : Fintype.card (LaneCell R J Λ) = Fintype.card Λ * Fintype.card J ^ 2 := by
    simp only [LaneCell, Fintype.card_prod, hsquare, pow_two,
      Nat.mul_comm, Nat.mul_left_comm]
  have hp := Nat.pow_le_pow_left h n
  rw [← pow_mul] at hp
  apply hp.trans
  apply Nat.pow_le_pow_right Fintype.card_pos
  rw [hN] at *
  nlinarith

end
end LeanMachine.WholeRow
