import Transpose.Tape.MStarClass
import Transpose.Tape.CEHint
import Mathlib.Data.Nat.Size

/-! Arithmetic invariants for recovery of the original matrix dimension.
This is a search specification; it does not yet provide a native controller. -/
namespace TransposeFollowup.DimensionCandidate
open Transpose
set_option autoImplicit false

theorem entryBits_mono {a b : ℕ} (h : a ≤ b) : entryBits a ≤ entryBits b := by
  by_cases ha : a ≤ 1
  · have hz : a-1=0 := by omega
    simp only [entryBits,hz,Nat.log2_zero]
    omega
  · have hn : a-1≠0 := by omega
    have hm : b-1≠0 := by omega
    have hp := Nat.log2_self_le hn
    have hl : (a-1).log2 ≤ (b-1).log2 := (Nat.le_log2 hm).mpr (by omega)
    unfold entryBits
    omega

theorem length_strictMono : StrictMono inputLength := by
  intro a b hab
  have hm := entryBits_mono (Nat.le_of_lt hab)
  have hw : 0<entryBits a := by unfold entryBits;omega
  have hs : a*a<b*b := by nlinarith
  unfold inputLength
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hs hw) (Nat.mul_le_mul_left _ hm)

theorem entryBits_step (k : ℕ) (hk : 1 ≤ k) :
    entryBits (k+1)=if k+1 ≤ 2^entryBits k then entryBits k else entryBits k+1 := by
  by_cases h1 : k=1
  · subst k;decide +kernel
  · have hkn : k-1≠0 := by omega
    have hkp : k≠0 := by omega
    have hlow : (k-1).log2 ≤ k.log2 := (Nat.le_log2 hkp).mpr (by have := Nat.log2_self_le hkn;omega)
    have hup : k ≤ 2^entryBits k := Tape.Impl.le_two_pow_entryBits k
    by_cases h : k+1 ≤ 2^entryBits k
    · simp only [h,ite_true]
      have hu : k.log2 < entryBits k := (Nat.log2_lt hkp).mpr (by omega)
      simp only [entryBits,Nat.add_sub_cancel] at hu ⊢
      omega
    · simp only [h,ite_false]
      have he : k=2^entryBits k := by omega
      have hl : k.log2=entryBits k := (congrArg Nat.log2 he).trans Nat.log2_two_pow
      simp only [entryBits,Nat.add_sub_cancel]
      unfold entryBits at hl
      omega

theorem input_size_bound (n : ℕ) : (inputLength n).size ≤ 3*entryBits n+1 := by
  apply Nat.size_le.mpr
  have h := Tape.Impl.inputLength_succ_le n
  change inputLength n+1 ≤ 2^(3*entryBits n+1) at h
  omega

def width (L : ℕ) : ℕ := 2*L.size+4

theorem width_budget (n : ℕ) : width (inputLength n) ≤ 12*entryBits n := by
  have h := input_size_bound n
  have hb : 1 ≤ entryBits n := by unfold entryBits;omega
  unfold width
  omega

theorem search_budget (n : ℕ) (hn : 1 ≤ n) :
    n*entryBits n*width (inputLength n) ≤ 12*inputLength n := by
  have hb := Tape.Impl.entryBits_le_self hn
  have hw := Nat.mul_le_mul_left (n*entryBits n) (width_budget n)
  calc
    n*entryBits n*width (inputLength n) ≤ (12*n*entryBits n)*entryBits n := by nlinarith [hw]
    _ ≤ (12*n*entryBits n)*n := Nat.mul_le_mul_left _ hb
    _ = 12*inputLength n := by unfold inputLength;ring

end TransposeFollowup.DimensionCandidate
