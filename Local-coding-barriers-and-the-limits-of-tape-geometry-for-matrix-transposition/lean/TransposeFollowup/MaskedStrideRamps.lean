import TransposeFollowup.MaskedStrideMotionBounds

/-! Finite capped-ramp expressions for the paid processing paths. The
last, possibly empty group is retained; scratch returns are real moves. -/
namespace TransposeFollowup.MaskedStrideScan
open Classical Finset
set_option autoImplicit false

def rise (S a n : ℕ) : ℕ := min ((n-a)/3) S

def pulse (S a n : ℕ) : ℤ := (rise S a n : ℤ)-(min (n-(a+3*S)) S : ℕ)

theorem rise_before (S a n : ℕ) (hn : n ≤ a) : rise S a n=0 := by
  simp [rise,Nat.sub_eq_zero_of_le hn]

theorem rise_after (S a n : ℕ) (hn : a+3*S ≤ n) : rise S a n=S := by
  unfold rise
  rw [Nat.min_eq_right (by omega)]

theorem pulse_before (S a n : ℕ) (hn : n ≤ a) : pulse S a n=0 := by
  simp [pulse,rise_before S a n hn,Nat.sub_eq_zero_of_le (show n ≤ a+3*S by omega)]

theorem pulse_after (S a n : ℕ) (hn : a+4*S ≤ n) : pulse S a n=0 := by
  rw [pulse,rise_after S a n (by omega),Nat.min_eq_right (by omega)]
  simp

theorem sum_rise (Q : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) :
    ∑ r ∈ range Q, rise S (r*(4*S)) n =
      if n<Q*(4*S) then n/(4*S)*S+rise S 0 (n%(4*S)) else Q*S := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [sum_range_succ,ih]
    by_cases hn : n<Q*(4*S)
    · have hn' : n<(Q+1)*(4*S) := by nlinarith
      simp only [ite_eq_left hn,ite_eq_left hn',rise_before S _ n hn.le,add_zero]
    · rw [ite_eq_right hn]
      by_cases hn' : n<(Q+1)*(4*S)
      · have hq : n/(4*S)=Q := Nat.div_eq_of_lt_le (by omega) hn'
        have hr : n-Q*(4*S)=n%(4*S) := by
          have h := Nat.div_add_mod' n (4*S)
          rw [hq] at h
          omega
        simp only [ite_eq_left hn',hq,rise,Nat.sub_zero,hr]
      · have hr := rise_after S (Q*(4*S)) n (by nlinarith)
        rw [ite_eq_right hn',hr]
        ring

theorem sum_pulse (Q : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) :
    ∑ r ∈ range Q, pulse S (r*(4*S)) n =
      if n<Q*(4*S) then pulse S 0 (n%(4*S)) else 0 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [sum_range_succ,ih]
    by_cases hn : n<Q*(4*S)
    · have hn' : n<(Q+1)*(4*S) := by nlinarith
      simp only [ite_eq_left hn,ite_eq_left hn',pulse_before S _ n hn.le,add_zero]
    · rw [ite_eq_right hn,zero_add]
      by_cases hn' : n<(Q+1)*(4*S)
      · have hq : n/(4*S)=Q := Nat.div_eq_of_lt_le (by omega) hn'
        have hr : n-Q*(4*S)=n%(4*S) := by
          have h := Nat.div_add_mod' n (4*S)
          rw [hq] at h
          omega
        simp only [ite_eq_left hn',pulse,rise,Nat.sub_zero,← Nat.sub_sub,hr]
      · rw [ite_eq_right hn']
        exact pulse_after S (Q*(4*S)) n (by nlinarith)

theorem bankPosition_sum (P : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) :
    bankPosition P S n =
      (∑ r ∈ range (P/S), rise S (r*(4*S)) n)+rise (P%S) (P/S*(4*S)) n := by
  rw [sum_rise _ hS]
  unfold bankPosition
  by_cases hn : n<P/S*(4*S)
  · rw [rise_before (P%S) _ n hn.le]
    simp only [ite_eq_left hn,add_zero,rise,Nat.sub_zero]
  · simp only [ite_eq_right hn,rise]

theorem scratchPosition_sum (P : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) :
    scratchPosition P S (min n (ticks P S)) =
      ∑ r ∈ range (P/S+1), pulse S (r*(4*S)) n := by
  have ht : ticks P S=P/S*(4*S)+4*S := by simp [ticks,Nat.add_mul]
  by_cases hnt : n ≤ ticks P S
  · rw [Nat.min_eq_left hnt,sum_range_succ,sum_pulse _ hS]
    by_cases hn : n<P/S*(4*S)
    · have hm := Nat.mod_lt n (show 0<4*S by omega)
      rw [pulse_before S _ n hn.le]
      simp only [scratchPosition,ite_eq_left hn,add_zero,
        pulse,rise,Nat.sub_zero,zero_add,Nat.min_eq_left (show n%(4*S)-3*S ≤ S by omega)]
    · have hl : n-P/S*(4*S)-3*S ≤ S := by omega
      simp only [scratchPosition,ite_eq_right hn,zero_add,pulse,rise,← Nat.sub_sub,
        Nat.min_eq_left hl]
  · have hlarge : ¬n<(P/S+1)*(4*S) := by unfold ticks at hnt; omega
    rw [Nat.min_eq_right (by omega),sum_pulse _ hS,ite_eq_right hlarge]
    have he : ticks P S-P/S*(4*S)=4*S := by omega
    simp only [scratchPosition,ite_eq_right (show ¬ticks P S<P/S*(4*S) by omega),he]
    have hdiv : S ≤ 4*S/3 := by omega
    rw [Nat.min_eq_right hdiv]
    have hsub : 4*S-3*S=S := by omega
    simp [hsub]

end TransposeFollowup.MaskedStrideScan
