import TapeStorageRates.NativeBatchRecord
import TapeStorageRates.NativeCoarseReplay

/-! # Joint records on actual compiler batch traces

The final drain is a separate, possibly shorter interval. Empty intervals
beyond halt require no special case in the support bound.
-/

namespace TapeStorageRates.NativeBatchRecord

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth Native

set_option autoImplicit false

/-- Every live timestamp stays in the three-block window around its own
batch entrance, for both input and work heads. -/
theorem replay_head_window {k s : ℕ} (hs : 0<s) (r : Fin s)
    (as : List (Descriptor k)) (h : Option (Fin k)) (j t : ℕ)
    (ha : (10*s+1)*j ≤ t)
    (hb : t < min ((10*s+1)*as.length+s) ((10*s+1)*(j+1))) :
    Fits s 0 (headPosition (replay r as) h t -
      headPosition (replay r as) h ((10*s+1)*j)) := by
  obtain ⟨hT,hend⟩ := lt_min_iff.mp hb
  have hj : j ≤ as.length := by
    by_contra! hj
    have hm := Nat.mul_le_mul_left (10*s+1) hj
    rw [Nat.mul_succ] at hm
    omega
  let i := t-(10*s+1)*j
  have ht : (10*s+1)*j+i=t := Nat.add_sub_of_le ha
  have hi : i<10*s+1 := by
    rw [Nat.mul_succ] at hend
    dsimp [i]
    omega
  obtain hj | rfl := lt_or_eq_of_le hj
  · have hz := replay_head_batch hs r as h j hj 0 (by omega)
    simp only [fineOffset_zero hs,add_zero] at hz
    rw [← ht,replay_head_batch hs r as h j hj i hi.le,hz,add_sub_cancel_left]
    simpa only [Fits,Nat.cast_zero,sub_zero,add_zero] using
      fineOffset_window hs (headCarry as[j] h) i hi
  · have hz := replay_head_drain hs r as h 0
    simp only [Nat.add_zero] at hz
    rw [← ht,replay_head_drain hs r as h i,hz,sub_self]
    simp only [Fits,Nat.cast_zero,sub_zero,add_zero]
    constructor <;> omega

/-- The actual complete-batch and drain intervals satisfy every premise of
the generic local-seed support theorem. -/
theorem replay_window_intervals {k s : ℕ} (hs : 0<s) (r : Fin s)
    (as : List (Descriptor k)) (J : Finset ℕ) :
    WindowIntervals (replay r as) s J (fun j => (10*s+1)*j)
      (fun j => min ((10*s+1)*as.length+s) ((10*s+1)*(j+1))) := by
  refine ⟨?_,?_,?_⟩
  · intro j _ t ha hb
    exact replay_head_window hs r as none j t ha hb
  · intro j _ t ha hb h
    exact replay_head_window hs r as (some h) j t ha hb
  · intro j _ t _ hb
    exact (replay_haltsAt r as).1 t (lt_of_lt_of_le hb (min_le_left _ _))

open Classical in
/-- Joint support of all actual records in any selected compiler batches.
The containing batch is the quotient by the exact native core clock; the
terminal drain belongs to the final quotient class. -/
theorem replay_joint_record_support (M : TM) {s : ℕ} (hs : 0<s)
    (r : Fin s) (as : List (Descriptor M.k)) {X : Type*}
    (word : X → List Bool) (S : Finset X)
    (htrace : ∀ x ∈ S, trace (machine M hs) (word x) = replay r as)
    (J Γ : Finset ℕ)
    (hΓ : ∀ t ∈ Γ, t < (10*s+1)*as.length+s ∧ t/(10*s+1) ∈ J) :
    (S.image (fun x => fun t : Γ => blockVal (machine M hs) 1 (word x) t)).card ≤
      2 ^ (batchSeedBits M*s*J.card) := by
  apply compiler_joint_record_support M hs word S (replay r as) J
    (fun j => (10*s+1)*j)
    (fun j => min ((10*s+1)*as.length+s) ((10*s+1)*(j+1))) htrace
    (replay_window_intervals hs r as J) Γ
  intro t ht
  obtain ⟨hT,hj⟩ := hΓ t ht
  refine ⟨t/(10*s+1),hj,?_,lt_min hT ?_⟩
  · simpa only [Nat.mul_comm] using Nat.div_mul_le_self t (10*s+1)
  · have h := (Nat.div_lt_iff_lt_mul (by omega : 0<10*s+1)).mp
      (Nat.lt_succ_self (t/(10*s+1)))
    simpa only [Nat.mul_comm] using h

end TapeStorageRates.NativeBatchRecord
