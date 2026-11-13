import Mathlib.Data.List.Destutter
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Interval overwrites and window-label amortization

The potential is the actual number of constant blocks of a finite label list,
computed by Mathlib's adjacent-duplicate removal.  The update lemma is proved
for a literal interval overwrite, not assumed as a hypothesis.

The adapter from native unit-speed tape walks to interval overwrites is not
formalized here.
-/

namespace LeanBacklog.WindowAmortization

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Number of maximal nonempty constant blocks. -/
def blocks (xs : List α) : ℕ := (xs.destutter (· ≠ ·)).length

@[simp] theorem blocks_nil : blocks ([] : List α) = 0 := rfl

@[simp] theorem blocks_singleton (a : α) : blocks [a] = 1 := rfl

theorem blocks_cons_cons (a b : α) (xs : List α) :
    blocks (a :: b :: xs) = blocks (b :: xs) + if a = b then 0 else 1 := by
  by_cases h : a = b
  · subst b
    simp [blocks, List.destutter_cons']
  · simp [blocks, List.destutter_cons', h, Nat.add_comm]

theorem blocks_append_bounds (xs ys : List α) :
    blocks (xs ++ ys) ≤ blocks xs + blocks ys ∧
      blocks xs + blocks ys ≤ blocks (xs ++ ys) + 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp
      | cons b ys =>
        simp only [List.singleton_append, blocks_singleton, blocks_cons_cons]
        split <;> constructor <;> omega
    | cons b xs =>
      simp only [List.cons_append, blocks_cons_cons] at ih ⊢
      constructor <;> omega

theorem blocks_append_le (xs ys : List α) :
    blocks (xs ++ ys) ≤ blocks xs + blocks ys :=
  (blocks_append_bounds xs ys).1

theorem blocks_add_le_append_add_one (xs ys : List α) :
    blocks xs + blocks ys ≤ blocks (xs ++ ys) + 1 :=
  (blocks_append_bounds xs ys).2

theorem distinct_le_blocks (xs : List α) : xs.toFinset.card ≤ blocks xs := by
  simpa only [List.card_toFinset, blocks] using
    List.IsChain.length_le_length_destutter_ne xs.dedup_sublist xs.nodup_dedup.isChain

theorem blocks_replicate_le_one (n : ℕ) (a : α) :
    blocks (List.replicate n a) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      simpa [List.replicate_succ, blocks_cons_cons] using ih

/-- Overwriting one contiguous interval destroys enough old blocks to pay for
all distinct old labels encountered, at a cost of at most three blocks. -/
theorem interval_overwrite (left middle right : List α) (a : α) :
    blocks (left ++ List.replicate middle.length a ++ right) +
      middle.toFinset.card ≤ blocks (left ++ middle ++ right) + 3 := by
  have hnew₁ := blocks_append_le (left ++ List.replicate middle.length a) right
  have hnew₂ := blocks_append_le left (List.replicate middle.length a)
  have hrep := blocks_replicate_le_one middle.length a
  have hold₁ := blocks_add_le_append_add_one (left ++ middle) right
  have hold₂ := blocks_add_le_append_add_one left middle
  have hlabels := distinct_le_blocks middle
  omega

/-- A literal interval overwrite; the charged labels can be any subset of the
old labels seen in that interval (for example, excluding the “never” label). -/
def IntervalOverwrite (before after : List α) (encountered : Finset α) : Prop :=
  ∃ left middle right a,
    before = left ++ middle ++ right ∧
    after = left ++ List.replicate middle.length a ++ right ∧
    encountered ⊆ middle.toFinset

theorem IntervalOverwrite.potential {before after : List α} {encountered : Finset α}
    (h : IntervalOverwrite before after encountered) :
    blocks after + encountered.card ≤ blocks before + 3 := by
  obtain ⟨left, middle, right, a, rfl, rfl, hlabels⟩ := h
  exact (Nat.add_le_add_left (Finset.card_le_card hlabels) _).trans
    (interval_overwrite left middle right a)

theorem IntervalOverwrite.length_eq {before after : List α} {encountered : Finset α}
    (h : IntervalOverwrite before after encountered) : after.length = before.length := by
  obtain ⟨left, middle, right, a, rfl, rfl, _⟩ := h
  simp

theorem blocks_pos {xs : List α} (h : xs ≠ []) : 0 < blocks xs := by
  apply List.length_pos_iff.mpr
  exact mt (List.destutter_eq_nil (· ≠ ·)).mp h

/-- Exact amortization, retaining the endpoint potentials. -/
theorem sum_encountered_add_final_le (tape : ℕ → List α)
    (encountered : ℕ → Finset α) (N : ℕ)
    (hstep : ∀ i < N, IntervalOverwrite (tape i) (tape (i + 1)) (encountered i)) :
    (∑ i ∈ Finset.range N, (encountered i).card) + blocks (tape N) ≤
      blocks (tape 0) + 3 * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hlast := (hstep N (Nat.lt_succ_self N)).potential
    rw [Finset.sum_range_succ]
    omega

theorem length_eq_initial (tape : ℕ → List α) (encountered : ℕ → Finset α) (N : ℕ)
    (hstep : ∀ i < N, IntervalOverwrite (tape i) (tape (i + 1)) (encountered i)) :
    (tape N).length = (tape 0).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    exact (hstep N (Nat.lt_succ_self N)).length_eq.trans
      (ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)))

/-- The predecessor-label bound for a nonempty tape initially carrying one
constant label. The interval locations and the overwrite labels are arbitrary. -/
theorem sum_encountered_le_three_mul (tape : ℕ → List α)
    (encountered : ℕ → Finset α) (N length : ℕ) (initial : α)
    (hlength : 0 < length) (hinit : tape 0 = List.replicate length initial)
    (hstep : ∀ i < N, IntervalOverwrite (tape i) (tape (i + 1)) (encountered i)) :
    (∑ i ∈ Finset.range N, (encountered i).card) ≤ 3 * N := by
  have hsum := sum_encountered_add_final_le tape encountered N hstep
  have hstart : blocks (tape 0) ≤ 1 := by
    rw [hinit]
    exact blocks_replicate_le_one length initial
  have hlen : (tape N).length = length := by
    rw [length_eq_initial tape encountered N hstep, hinit, List.length_replicate]
  have hnonempty : tape N ≠ [] := by
    intro hempty
    simp only [hempty, List.length_nil] at hlen
    omega
  have hend := blocks_pos hnonempty
  omega

#print axioms interval_overwrite
#print axioms sum_encountered_le_three_mul

end LeanBacklog.WindowAmortization
