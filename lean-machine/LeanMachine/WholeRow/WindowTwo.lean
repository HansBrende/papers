import LeanMachine.WholeRow.AcyclicOrder
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The row-order bound at window two

A least-used row is put last, and its incident columns are removed. The
closed rectangular bound below is preserved by that induction. In the
square case it is d(d+1)/2 + d - 1, including empty helper sets.
-/

namespace LeanMachine.WholeRow.AcyclicOrder

open Finset LiftOrder
open scoped BigOperators Classical
noncomputable section

/-- Bound for n rows and m columns with at most two helpers per column. -/
def windowTwoBound (n m : ℕ) : ℕ :=
  if m < n then n * (n + 1) / 2 - (n - m)
  else n * (n + 1) / 2 + n * (m - n) + (n - 1)

private theorem triangle_twice (n : ℕ) :
    2 * (n * (n + 1) / 2) = n * (n + 1) := by
  have h := sum_range_id_mul_two (n + 1)
  rw [sum_range_id] at h
  simpa [Nat.mul_comm] using h

private theorem triangle_ge (n : ℕ) : n ≤ n * (n + 1) / 2 := by
  cases n with
  | zero => simp
  | succ n => have h := triangle_twice (n + 1); nlinarith

/-- The numerical invariant of the least-used-row step. -/
theorem windowTwoBound_step {n m δ : ℕ} (hn : 1 ≤ n)
    (hδ : δ ≤ m) (havg : n * δ ≤ 2 * m) :
    n * δ + windowTwoBound (n - 1) (m - δ) ≤ windowTwoBound n m := by
  by_cases hn1 : n = 1
  · subst n
    by_cases hm : m = 0
    · subst m; simp_all [windowTwoBound]
    · simp [windowTwoBound, show ¬ m < 1 by omega]
      omega
  have hn2 : 2 ≤ n := by omega
  have hnprev : n - 1 + 1 = n := by omega
  have hnprev2 : n - 1 - 1 + 2 = n := by omega
  have ht := triangle_twice n
  have ht' := triangle_twice (n - 1)
  have hge := triangle_ge n
  have hge' := triangle_ge (n - 1)
  by_cases hm : m < n
  · have hd : δ ≤ 1 := by nlinarith
    have hnm : n - m + m = n := Nat.sub_add_cancel hm.le
    have hg : n - m ≤ n * (n + 1) / 2 := (Nat.sub_le _ _).trans hge
    have hg' := Nat.sub_add_cancel hg
    rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl
    · simp only [Nat.mul_zero, Nat.sub_zero, zero_add]
      by_cases hm' : m < n - 1
      · have he := Nat.sub_add_cancel hm'.le
        have hs : n - 1 - m ≤ (n - 1) * (n - 1 + 1) / 2 :=
          (Nat.sub_le _ _).trans hge'
        have hs' := Nat.sub_add_cancel hs
        simp only [windowTwoBound, ite_eq_left hm, ite_eq_left hm']
        nlinarith
      · have he : m = n - 1 := by omega
        simp only [windowTwoBound, ite_eq_left hm, ite_eq_right hm']
        subst m
        simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
        nlinarith
    · have hm' : m - 1 < n - 1 := by omega
      have he : n - 1 - (m - 1) = n - m := by omega
      have hs : n - m ≤ (n - 1) * (n - 1 + 1) / 2 := by
        have : n - m ≤ n - 1 := by omega
        exact this.trans hge'
      have hs' := Nat.sub_add_cancel hs
      simp only [Nat.mul_one, windowTwoBound, ite_eq_left hm, ite_eq_left hm', he]
      nlinarith
  · have hm0 : n ≤ m := by omega
    have he : m - n + n = m := Nat.sub_add_cancel hm0
    have hd : δ ≤ m - n + 2 := by
      have hmul := Nat.mul_le_mul_right (m - n) hn2
      nlinarith
    have hmd : m - δ + δ = m := Nat.sub_add_cancel hδ
    by_cases hm' : n - 1 ≤ m - δ
    · have he' := Nat.sub_add_cancel hm'
      simp only [windowTwoBound, ite_eq_right hm, ite_eq_right (show ¬ m - δ < n - 1 by omega)]
      nlinarith
    · have hd' : δ = m - n + 2 := by omega
      have hm'' : m - δ = n - 2 := by omega
      have hsub : n - 1 - (m - δ) = 1 := by omega
      have hs : 1 ≤ (n - 1) * (n - 1 + 1) / 2 := by omega
      have hs' := Nat.sub_add_cancel hs
      simp only [windowTwoBound, ite_eq_right hm, ite_eq_left (show m - δ < n - 1 by omega), hsub]
      nlinarith

universe u v

private theorem exists_numbering (n : ℕ) :
    ∀ (R : Type u) (J : Type v) [Fintype R] [Fintype J], Fintype.card R = n →
      ∀ (ρ : J → Finset R), (∀ j, (ρ j).card ≤ 2) →
        ∃ f : R → ℕ, Function.Injective f ∧ (∀ r, f r < n) ∧
          (∑ j, (ρ j).sup (fun r => f r + 1)) ≤ windowTwoBound n (Fintype.card J) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R J _ _ hR ρ h2
    by_cases hn : n = 0
    · have : IsEmpty R := Fintype.card_eq_zero_iff.mp (hR.trans hn)
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · intro r; exact isEmptyElim r
      · intro r; exact isEmptyElim r
      · simp [hn, windowTwoBound, Finset.eq_empty_of_isEmpty]
    have hnpos : 1 ≤ n := by omega
    have : Nonempty R := Fintype.card_pos_iff.mp (by omega)
    let ℓ : R → ℕ := fun r => (univ.filter fun j => r ∈ ρ j).card
    obtain ⟨r, _, hmin⟩ := exists_min_image (univ : Finset R) ℓ univ_nonempty
    let δ := ℓ r
    have hδ : δ ≤ Fintype.card J := card_le_univ _
    have hsum : (∑ r, ℓ r) = ∑ j, (ρ j).card := by
      simp only [ℓ, card_filter]
      rw [sum_comm]
      simp
    have hlower : n * δ ≤ ∑ r, ℓ r := by
      calc
        _ = ∑ _r : R, δ := by simp [hR]
        _ ≤ _ := sum_le_sum fun r' _ => hmin r' (mem_univ _)
    have hupper : (∑ j, (ρ j).card) ≤ 2 * Fintype.card J := by
      simpa [Nat.mul_comm] using sum_le_sum (s := univ) (fun j _ => h2 j)
    have havg : n * δ ≤ 2 * Fintype.card J := by omega
    let R' := {x : R // x ≠ r}
    let J' := {j : J // r ∉ ρ j}
    let ρ' : J' → Finset R' := fun j => (ρ j).subtype fun x => x ≠ r
    have hR' : Fintype.card R' = n - 1 := by
      simp [R', Fintype.card_subtype_compl, hR]
    have hJ' : Fintype.card J' = Fintype.card J - δ := by
      simp only [J', Fintype.card_subtype, δ, ℓ]
      have h := card_filter_add_card_filter_not (s := (univ : Finset J))
        (p := fun j => r ∈ ρ j)
      rw [card_univ] at h
      omega
    have h2' : ∀ j, (ρ' j).card ≤ 2 := by
      intro j
      change ((ρ j).subtype (fun x => x ≠ r)).card ≤ 2
      rw [card_subtype]
      exact (card_filter_le _ _).trans (h2 j)
    obtain ⟨f', hinj', hlt', hcost'⟩ := ih (n - 1) (by omega) R' J' hR' ρ' h2'
    let f : R → ℕ := fun x => if hx : x = r then n - 1 else f' ⟨x, hx⟩
    have hlast : f r = n - 1 := by simp [f]
    have hold (x : R') : f x = f' x := by simp [f, x.property]
    have hlt : ∀ x, f x < n := by
      intro x
      by_cases hx : x = r
      · subst x; rw [hlast]; omega
      · have ht := hlt' ⟨x, hx⟩
        simpa only [f, dite_eq_right hx] using ht.trans_le (Nat.sub_le n 1)
    have hinj : Function.Injective f := by
      intro x y hxy
      by_cases hx : x = r
      · subst x
        by_cases hy : y = r
        · exact hy.symm
        · have ht := hlt' ⟨y, hy⟩
          simp only [hlast, f, dite_eq_right hy] at hxy
          omega
      · by_cases hy : y = r
        · subst y
          have ht := hlt' ⟨x, hx⟩
          simp only [hlast, f, dite_eq_right hx] at hxy
          omega
        · have he : f' ⟨x, hx⟩ = f' ⟨y, hy⟩ := by
            simpa only [f, dite_eq_right hx, dite_eq_right hy] using hxy
          exact congrArg Subtype.val (hinj' he)
    have hremaining (j : J') :
        (ρ j).sup (fun x => f x + 1) = (ρ' j).sup (fun x => f' x + 1) := by
      apply le_antisymm
      · apply Finset.sup_le
        intro x hx
        have hxr : x ≠ r := by rintro rfl; exact j.property hx
        have hx' : (⟨x, hxr⟩ : R') ∈ ρ' j := Finset.mem_subtype.mpr hx
        have h := Finset.le_sup (f := fun a => f' a + 1) hx'
        simpa only [f, dite_eq_right hxr] using h
      · apply Finset.sup_le
        intro x hx
        have hx' : (x : R) ∈ ρ j := Finset.mem_subtype.mp hx
        have h := Finset.le_sup (f := fun a => f a + 1) hx'
        simpa only [hold] using h
    refine ⟨f, hinj, hlt, ?_⟩
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun j => r ∈ ρ j) (fun j => (ρ j).sup (fun x => f x + 1))
    have hused : (∑ j : {j : J // r ∈ ρ j}, (ρ j).sup (fun x => f x + 1)) ≤ n * δ := by
      calc
        _ ≤ ∑ _j : {j : J // r ∈ ρ j}, n := by
          apply sum_le_sum
          intro j _
          exact Finset.sup_le fun x _ => Nat.succ_le_of_lt (hlt x)
        _ = _ := by simp [δ, ℓ, Fintype.card_subtype, Nat.mul_comm]
    have hrem : (∑ j : J', (ρ j).sup (fun x => f x + 1)) ≤
        windowTwoBound (n - 1) (Fintype.card J - δ) := by
      simpa only [hremaining, hJ'] using hcost'
    calc
      _ = (∑ j : {j : J // r ∈ ρ j}, (ρ j).sup (fun x => f x + 1)) +
          ∑ j : J', (ρ j).sup (fun x => f x + 1) := hsplit.symm
      _ ≤ n * δ + windowTwoBound (n - 1) (Fintype.card J - δ) := add_le_add hused hrem
      _ ≤ _ := windowTwoBound_step hnpos hδ havg

variable {R J : Type*} [Fintype R] [Fintype J]

/-- Some row order has cost at most the rectangular window-two invariant. -/
theorem exists_cost_window_two_le (ρ : J → Finset R) (h2 : ∀ j, (ρ j).card ≤ 2) :
    ∃ o : R ≃ Fin (Fintype.card R),
      cost ρ o ≤ windowTwoBound (Fintype.card R) (Fintype.card J) := by
  obtain ⟨f, hinj, hlt, hc⟩ := exists_numbering (Fintype.card R) R J rfl ρ h2
  let g : R → Fin (Fintype.card R) := fun r => ⟨f r, hlt r⟩
  have hg : Function.Injective g := fun _ _ h => hinj (congrArg Fin.val h)
  let o : R ≃ Fin (Fintype.card R) := Equiv.ofBijective g
    ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, by simp⟩)
  exact ⟨o, hc⟩

/-- The square case: cost at most d(d+1)/2 + (d-1). -/
theorem exists_cost_window_two_square (ρ : J → Finset R) (h2 : ∀ j, (ρ j).card ≤ 2)
    (hJ : Fintype.card J = Fintype.card R) :
    ∃ o : R ≃ Fin (Fintype.card R),
      cost ρ o ≤ Fintype.card R * (Fintype.card R + 1) / 2 + (Fintype.card R - 1) := by
  obtain ⟨o, ho⟩ := exists_cost_window_two_le ρ h2
  exact ⟨o, by simpa [windowTwoBound, hJ] using ho⟩

end
end LeanMachine.WholeRow.AcyclicOrder
