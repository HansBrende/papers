import MergeDepth.Traces
import Mathlib.Data.Fintype.Card

/-! The exact fine-clock motion of aligned sweeps, including flushing and halting.
The alphabet records one carry per head and one append decision per batch. -/

namespace TapeStorageRates.Native

open Transpose MergeDepth

/-- A batch records an input carry, the work carries and the flush flag. -/
abbrev Descriptor (k : ℕ) := (Fin 3 × (Fin k → Fin 3)) × Bool

def direction (d : Fin 3) : Dir :=
  if d = 0 then .left else if d = 1 then .stay else .right

def straight (k : ℕ) (move : Dir) (append : Bool := false) : Motion k :=
  (move, fun _ => move, append)

/-- The native moves in one batch. Read and write sweeps stay on their last cell. -/
def coreMoves {k : ℕ} (s : ℕ) (a : Descriptor k) : List (Motion k) :=
  List.replicate s (straight k .left) ++
  (List.ofFn (fun i : Fin (3*s) => straight k (if i.val+1<3*s then .right else .stay)) ++
  ([straight k .stay] ++
  (List.ofFn (fun i : Fin (3*s) => straight k (if i.val+1<3*s then .left else .stay)) ++
  (List.replicate s (straight k .right) ++
  (List.replicate s (direction a.1.1, fun h => direction (a.1.2 h), false) ++
  List.replicate s (straight k .stay a.2))))))

theorem length_coreMoves {k s : ℕ} (_hs : 0 < s) (a : Descriptor k) :
    (coreMoves s a).length = 10*s+1 := by
  simp [coreMoves]
  omega

/-- All complete batches, followed by the fixed-length final drain. -/
def fineWord {k : ℕ} (s : ℕ) (residue : Fin s) (as : List (Descriptor k)) :
    List (Motion k) :=
  as.flatMap (coreMoves s) ++
    List.ofFn (fun i : Fin s => straight k .stay (decide (i.val < residue.val)))

theorem length_fineWord {k s : ℕ} (r : Fin s) (as : List (Descriptor k)) :
    (fineWord s r as).length = (10*s+1)*as.length+s := by
  have h : (as.flatMap (coreMoves s)).length = (10*s+1)*as.length := by
    induction as with
    | nil => simp
    | cons a as ih =>
      simp [List.flatMap_cons, length_coreMoves (Nat.zero_lt_of_lt r.isLt), ih, Nat.mul_succ]
      omega
  simp [fineWord, h]

/-- A complete motion word gives precisely the trace that is stationary under halt
from its first missing entry onward. -/
def replay {k s : ℕ} (r : Fin s) (as : List (Descriptor k)) : Trace k :=
  fun t => (fineWord s r as)[t]?

theorem replay_haltsAt {k s : ℕ} (r : Fin s) (as : List (Descriptor k)) :
    (replay r as).HaltsAt ((10*s+1)*as.length+s) := by
  unfold Trace.HaltsAt replay
  rw [← length_fineWord r as]
  exact ⟨fun t ht => by simp [List.getElem?_eq_getElem ht], by simp⟩

theorem card_descriptor (k : ℕ) : Fintype.card (Descriptor k) = 2*3^(k+1) := by
  simp [Descriptor, pow_succ]
  ring

private def codeWord {k R : ℕ} (z : Fin R → Option (Descriptor k)) :
    List (Descriptor k) := (List.ofFn z).filterMap id

private theorem codeWord_pad {k R : ℕ} (as : List (Descriptor k)) (h : as.length ≤ R) :
    codeWord (fun j : Fin R => as[j.val]?) = as := by
  induction R generalizing as with
  | zero =>
    have : as = [] := List.length_eq_zero_iff.mp (by omega)
    simp [this, codeWord]
  | succ R ih =>
    cases as with
    | nil => simp [codeWord]
    | cons a as =>
      rw [codeWord, List.ofFn_succ]
      simp only [Fin.val_zero, List.getElem?_cons_zero, Fin.val_succ, List.getElem?_cons_succ]
      change a :: codeWord (fun j : Fin R => as[j.val]?) = a :: as
      rw [ih as (by simpa using h)]

/-- There are at most the claimed number of full fine traces at a common residue.
The containing finite set works for arbitrary sets of inputs, including infinite sets. -/
theorem replay_support {k s : ℕ} (r : Fin s) (R : ℕ) :
    ∃ S : Finset (Trace k), S.card ≤ (1+2*3^(k+1))^R ∧
      ∀ as : List (Descriptor k), as.length ≤ R → replay r as ∈ S := by
  classical
  let f := fun z : Fin R → Option (Descriptor k) => replay r (codeWord z)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · apply Finset.card_image_le.trans
    simp [pow_succ, Nat.add_comm, Nat.mul_comm]
  · intro as h
    exact Finset.mem_image.mpr ⟨fun j : Fin R => as[j.val]?, Finset.mem_univ _, by
      simp [f, codeWord_pad as h]⟩

theorem replay_support_variable {k : ℕ} (s R : ℕ) :
    ∃ S : Finset (Trace k), S.card ≤ s*(1+2*3^(k+1))^R ∧
      ∀ (r : Fin s) (as : List (Descriptor k)), as.length ≤ R → replay r as ∈ S := by
  classical
  let f := fun z : Fin s × (Fin R → Option (Descriptor k)) => replay z.1 (codeWord z.2)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · apply Finset.card_image_le.trans
    simp [pow_succ, Nat.add_comm, Nat.mul_comm]
  · intro r as h
    exact Finset.mem_image.mpr ⟨(r, fun j : Fin R => as[j.val]?), Finset.mem_univ _, by
      simp [f, codeWord_pad as h]⟩

end TapeStorageRates.Native
