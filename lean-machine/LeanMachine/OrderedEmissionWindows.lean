import LeanMachine.ReadOnlyWindows

/-! # Windows extracted from one fixed ordered-emission word

Write positions are public strictly increasing operation indices. The cuts
and window readouts below are constructed from those positions, not supplied
as independent local recovery data.
-/

namespace LeanMachine.OrderedEmissionWindows

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {m N : ℕ}

/-- The actual boundary immediately after the first min(r,m) writes. -/
noncomputable def cut (pos : Fin m → Fin N) (r : ℕ) : ℕ :=
  if h : 0 < min r m then (pos ⟨min r m - 1, by omega⟩).val + 1 else 0

theorem cut_zero (pos : Fin m → Fin N) : cut pos 0 = 0 := by simp [cut]

theorem cut_le_length (pos : Fin m → Fin N) (r : ℕ) : cut pos r ≤ N := by
  unfold cut
  split
  · have hh := (pos ⟨min r m - 1, by omega⟩).isLt
    omega
  · omega

theorem cut_mono (pos : Fin m → Fin N) (hpos : StrictMono pos) : Monotone (cut pos) := by
  intro r s hrs
  have hm : min r m ≤ min s m := min_le_min_right m hrs
  unfold cut
  split
  · rename_i hr
    rw [dite_eq_left (by omega : 0 < min s m)]
    have hh := hpos.monotone (show (⟨min r m - 1, by omega⟩ : Fin m) ≤
        ⟨min s m - 1, by omega⟩ by exact_mod_cast (show min r m - 1 ≤ min s m - 1 by omega))
    exact Nat.add_le_add_right hh 1
  · exact Nat.zero_le _

theorem cut_before_write (pos : Fin m → Fin N) (hpos : StrictMono pos)
    (q : Fin m) {r : ℕ} (hr : r ≤ q.val) : cut pos r ≤ (pos q).val := by
  unfold cut
  split
  · rename_i h
    have hi : (⟨min r m - 1, by omega⟩ : Fin m) < q := by exact_mod_cast (show min r m - 1 < q.val by omega)
    exact Nat.succ_le_of_lt (hpos hi)
  · exact Nat.zero_le _

theorem write_before_cut (pos : Fin m → Fin N) (hpos : StrictMono pos)
    (q : Fin m) {r : ℕ} (hr : q.val < r) : (pos q).val < cut pos r := by
  have hm : q.val < min r m := lt_min hr q.isLt
  unfold cut
  rw [dite_eq_left (by omega : 0 < min r m)]
  have hh := hpos.monotone (show q ≤ (⟨min r m - 1, by omega⟩ : Fin m) by exact_mod_cast (show q.val ≤ min r m - 1 by omega))
  exact Nat.lt_succ_of_le hh

noncomputable def record {O : Type*} (pos : Fin m → Fin N) (value : Fin m → O) : List (Option O) :=
  List.ofFn fun t : Fin N => if h : ∃ q, pos q = t then some (value (Classical.choose h)) else none

theorem record_length {O : Type*} (pos : Fin m → Fin N) (value : Fin m → O) :
    (record pos value).length = N := by simp [record]

theorem record_get_write {O : Type*} (pos : Fin m → Fin N) (hpos : Function.Injective pos)
    (value : Fin m → O) (q : Fin m) : (record pos value)[(pos q).val]? = some (some (value q)) := by
  have hex : ∃ j, pos j = pos q := ⟨q, rfl⟩
  have he : Classical.choose hex = q := hpos (Classical.choose_spec hex)
  simp only [record, List.getElem?_ofFn, dite_eq_left (pos q).isLt, dite_eq_left hex, he]

theorem slice_get_write {O : Type*} (pos : Fin m → Fin N) (hpos : StrictMono pos)
    (value : Fin m → O) (q : Fin m) {r s : ℕ} (hr : r ≤ q.val) (hs : q.val < s) :
    (((record pos value).drop (cut pos r)).take (cut pos s - cut pos r))[(pos q).val - cut pos r]? =
      some (some (value q)) := by
  have hlo := cut_before_write pos hpos q hr
  have hhi := write_before_cut pos hpos q hs
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
  exact record_get_write pos hpos.injective value q

/-- A literal global correctness equation implies every designated emission
inside every actual run slice, starting from its actual global entry state. -/
theorem run_window_get_write {S D O : Type*} (pos : Fin m → Fin N)
    (hpos : StrictMono pos) (value : Fin m → O)
    (steps : List (ReadOnlyStep S D (Option O))) (initial : S) (data : List D)
    (hlen : steps.length = N) (hdata : steps.length = data.length)
    (hcorrect : (ReadOnlyStep.run steps initial data).2 = record pos value)
    (q : Fin m) {r s : ℕ} (hr : r ≤ q.val) (hs : q.val < s) :
    (ReadOnlyStep.run ((steps.drop (cut pos r)).take (cut pos s - cut pos r))
      (ReadOnlyStep.run (steps.take (cut pos r)) initial (data.take (cut pos r))).1
      ((data.drop (cut pos r)).take (cut pos s - cut pos r))).2[(pos q).val - cut pos r]? =
      some (some (value q)) := by
  have hcut : cut pos r ≤ cut pos s := cut_mono pos hpos (by omega)
  rw [ReadOnlyStep.run_slice_output steps initial data hdata _ _ (by
    rw [Nat.add_sub_of_le hcut, hlen]
    exact cut_le_length pos s), hcorrect]
  exact slice_get_write pos hpos value q hr hs

end LeanMachine.OrderedEmissionWindows
