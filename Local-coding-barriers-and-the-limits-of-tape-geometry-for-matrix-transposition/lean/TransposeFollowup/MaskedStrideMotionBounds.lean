import TransposeFollowup.MaskedStrideMotion

/-! Uniform finite-size bounds behind the vanishing-stride limit. The
comparison bank advances at average speed1/4 and stops at the bank length.
The paid last slab and every buffer excursion remain in the estimates. -/
namespace TransposeFollowup.MaskedStrideScan
open Classical
set_option autoImplicit false

theorem ticks_bounds (P : ℕ) {S : ℕ} (hS : 0<S) :
    4*P ≤ ticks P S ∧ ticks P S ≤ 4*P+4*S := by
  have hd := Nat.div_add_mod' P S
  have hm := Nat.mod_lt P hS
  unfold ticks
  constructor <;> nlinarith [Nat.zero_le (P%S)]

theorem bankPosition_error (P : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) :
    |(bankPosition P S n : ℤ)-(min (n/4) P : ℕ)| ≤ S := by
  have hP := Nat.div_mul_le_self P S
  have hp := Nat.div_add_mod' P S
  have hr := Nat.mod_lt P hS
  by_cases hn : n<P/S*(4*S)
  · have hd := Nat.div_add_mod' n (4*S)
    have hm := Nat.mod_lt n (show 0<4*S by omega)
    have he : n=4*(n/(4*S)*S)+n%(4*S) := by nlinarith
    have hq : n/4=n/(4*S)*S+(n%(4*S))/4 := by omega
    have hnp : n/4≤P := by
      have hlt : n<4*P := by nlinarith
      omega
    have hm4 : (n%(4*S))/4≤S := by omega
    have hmin := Nat.min_le_right ((n%(4*S))/3) S
    rw [bankPosition,ite_eq_left hn,Nat.min_eq_left hnp,hq,abs_le]
    constructor <;> omega
  · have hbase : P/S*S≤n/4 := by
      have hle : 4*(P/S*S)≤n := by nlinarith
      omega
    have hlow : P/S*S ≤ min (n/4) P := le_min hbase hP
    have hhigh := Nat.min_le_right (n/4) P
    have hmin := Nat.min_le_right ((n-P/S*(4*S))/3) (P%S)
    rw [bankPosition,ite_eq_right hn,abs_le]
    constructor <;> omega

theorem bankPosition_after (P : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) (hn : ticks P S≤n) :
    bankPosition P S n=P := by
  have ht : P/S*(4*S)+4*S≤n := by simpa only [ticks,Nat.add_mul,Nat.one_mul] using hn
  have hm := Nat.mod_lt P hS
  have harg : P%S≤(n-P/S*(4*S))/3 := by omega
  rw [bankPosition,ite_eq_right (show ¬n<P/S*(4*S) by omega),Nat.min_eq_right harg]
  exact Nat.div_add_mod' P S

theorem bankPosition_freeze (P : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) :
    bankPosition P S (min n (ticks P S))=bankPosition P S n := by
  by_cases hn : n≤ticks P S
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega),bankPosition_after P hS _ le_rfl,bankPosition_after P hS n (by omega)]

theorem scratch_slab_bounds (S n : ℕ) (hn : n≤4*S) :
    0 ≤ ((min (n/3) S : ℕ) : ℤ)-((n-3*S : ℕ) : ℤ) ∧
    ((min (n/3) S : ℕ) : ℤ)-((n-3*S : ℕ) : ℤ) ≤ S := by
  by_cases h : n≤3*S
  · have hd : n/3≤S := by omega
    rw [Nat.min_eq_left hd,Nat.sub_eq_zero_of_le h]
    constructor <;> omega
  · have hd : S≤n/3 := by omega
    rw [Nat.min_eq_right hd]
    constructor <;> omega

theorem scratchPosition_bounds (P : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) (hn : n≤ticks P S) :
    0 ≤ scratchPosition P S n ∧ scratchPosition P S n ≤ S := by
  by_cases h : n<P/S*(4*S)
  · simpa only [scratchPosition,ite_eq_left h] using
      scratch_slab_bounds S (n%(4*S)) (Nat.mod_lt n (by omega)).le
  · have ht : n≤P/S*(4*S)+4*S := by simpa only [ticks,Nat.add_mul,Nat.one_mul] using hn
    simpa only [scratchPosition,ite_eq_right h] using scratch_slab_bounds S (n-P/S*(4*S)) (by omega)

end TransposeFollowup.MaskedStrideScan
