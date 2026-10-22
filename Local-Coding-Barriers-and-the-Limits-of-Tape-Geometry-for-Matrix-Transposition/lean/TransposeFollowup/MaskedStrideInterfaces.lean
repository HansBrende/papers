import TransposeFollowup.MaskedStrideExecution

/-! Preserved IO fields, bounded scratch footprint, and dependence only
on the processed input prefix. These connect the scan to paid raw IO. -/
namespace TransposeFollowup.MaskedStrideGroup
open Classical FixedTapeCompiler ScheduledNativeIO
open MaskedStrideCell (Mode State)
set_option autoImplicit false

theorem result_io (isPrefix : Bool) (mask : ℕ → Bool) (S g : ℕ) (w : List Bool) (c : State) :
    (result isPrefix mask S g w c).inputPos=c.inputPos ∧
    (result isPrefix mask S g w c).outRev=c.outRev := by
  have hs (n : ℕ) : (slots isPrefix mask g w c n).inputPos=c.inputPos ∧
      (slots isPrefix mask g w c n).outRev=c.outRev := by
    induction n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih =>
      by_cases h : n<g <;> simp only [slots,h,ite_true,ite_false] <;> exact ih
  have hr (d : State) (n : ℕ) :
      (trajectory (fun _ => moveBuffer .left) w d n).inputPos=d.inputPos ∧
      (trajectory (fun _ => moveBuffer .left) w d n).outRev=d.outRev := by
    induction n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih => exact ih
  exact ⟨(hr _ S).1.trans (hs S).1,(hr _ S).2.trans (hs S).2⟩

end TransposeFollowup.MaskedStrideGroup

namespace TransposeFollowup.MaskedStrideScan
open Classical FixedTapeCompiler ScheduledNativeIO
open MaskedStrideCell (Mode State bit)
open MaskedStrideGroup (cells)
set_option autoImplicit false

theorem groups_io (isPrefix : Bool) (mask : ℕ → Bool) (S : ℕ) (w : List Bool) (c : State) (r : ℕ) :
    (groups isPrefix mask S w c r).inputPos=c.inputPos ∧
    (groups isPrefix mask S w c r).outRev=c.outRev := by
  induction r with
  | zero => exact ⟨rfl,rfl⟩
  | succ r ih =>
    have h := MaskedStrideGroup.result_io isPrefix (fun j => mask (r*S+j)) S S w (groups isPrefix mask S w c r)
    exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

theorem result_io (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) (c : State) :
    (result isPrefix mask P S w c).inputPos=c.inputPos ∧
    (result isPrefix mask P S w c).outRev=c.outRev := by
  have h := MaskedStrideGroup.result_io isPrefix (fun j => mask (P/S*S+j)) S (P%S) w
    (groups isPrefix mask S w c (P/S))
  exact ⟨h.1.trans (groups_io isPrefix mask S w c (P/S)).1,
    h.2.trans (groups_io isPrefix mask S w c (P/S)).2⟩

theorem groups_scratch_outside (isPrefix : Bool) (mask : ℕ → Bool) (S : ℕ) (w : List Bool)
    (c : State) (hzero : ∀ j < S, bit (cells c 1 (c.work.pos 1+j))=false) (r : ℕ) (z : ℤ)
    (hz : z<c.work.pos 1 ∨ c.work.pos 1+S ≤ z) :
    cells (groups isPrefix mask S w c r) 1 z=cells c 1 z := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hp := (groups_invariant isPrefix mask S w c hzero r).scratch_pos
    rw [groups,MaskedStrideGroup.result_outside isPrefix (fun j => mask (r*S+j)) le_rfl w _ 1 z
      (by simpa only [hp] using hz)]
    exact ih

theorem result_scratch_outside (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) (c : State) (hzero : ∀ j < S, bit (cells c 1 (c.work.pos 1+j))=false)
    (z : ℤ) (hz : z<c.work.pos 1 ∨ c.work.pos 1+S ≤ z) :
    cells (result isPrefix mask P S w c) 1 z=cells c 1 z := by
  have hp := (groups_invariant isPrefix mask S w c hzero (P/S)).scratch_pos
  rw [result,MaskedStrideGroup.result_outside isPrefix (fun j => mask (P/S*S+j)) (Nat.mod_lt P hS).le w _ 1 z
    (by rw [hp]; rcases hz with hz | hz; exact Or.inl hz; exact Or.inr (by have := Nat.mod_lt P hS; omega))]
  exact groups_scratch_outside isPrefix mask S w c hzero (P/S) z hz

theorem value_congr_upto (isPrefix : Bool) (mask x y : ℕ → Bool) {S : ℕ} (hS : 0<S)
    (n : ℕ) (hxy : ∀ j ≤ n, x j=y j) : value isPrefix mask x S n=value isPrefix mask y S n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [value_recurrence isPrefix mask x hS,value_recurrence isPrefix mask y hS,hxy n le_rfl]
    by_cases hn : n<S
    · rw [ite_eq_left hn,ite_eq_left hn]
    · rw [ite_eq_right hn,ite_eq_right hn,
        ih (n-S) (by omega) (fun j hj => hxy j (by omega)),hxy (n-S) (by omega)]

end TransposeFollowup.MaskedStrideScan
