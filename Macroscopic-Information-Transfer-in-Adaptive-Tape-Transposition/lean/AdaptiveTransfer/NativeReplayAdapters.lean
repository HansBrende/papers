import AdaptiveTransfer.AdaptiveReplay
import Transpose.Tape.Counting

/-! Canonical frozen-machine adapters for the adaptive reconstruction core.
Successful prefixes, actual output correctness and raw exterior agreement are
derived from the native run and input coordinates. -/

namespace AdaptiveTransfer

open Transpose Transpose.Tape Transpose.Tape.Impl Finset

namespace ExecutionPrefix

theorem config_eq_run {M : TM} {w : List Bool} {T : ℕ}
    (E : ExecutionPrefix M w T) {t : ℕ} (ht : t ≤ T) :
    E.config t = run M w t := by
  induction t with
  | zero => exact E.initial
  | succ t ih =>
    have hs := E.successful t (by omega)
    rw [ih (by omega)] at hs
    simp only [run, hs, Option.getD_some]

theorem emitted_eq_outBit {M : TM} {w : List Bool} {T : ℕ}
    (E : ExecutionPrefix M w T) {t : ℕ} (ht : t ≤ T) :
    E.emitted t = outBit M w t := by
  change (nativeInstruction M w (E.config t)).bind _ = _
  rw [E.config_eq_run ht]
  rfl

/-- Any successful native prefix is the canonical run, so actual final-output
correctness supplies the local append assertion used by replay. -/
theorem output_correct {M : TM} {P T N : ℕ} {X : Fin P → Bool}
    (E : ExecutionPrefix M (List.ofFn X) T) (π : Fin P → Fin P) (hTN : T ≤ N)
    (houtput : (run M (List.ofFn X) N).outRev.reverse = List.ofFn (fun j => X (π j)))
    {t : ℕ} (ht : t < T) (j : Fin P) (bit : Bool)
    (hcount : (E.config t).outRev.length = j.val) (hemit : E.emitted t = some bit) :
    bit = X (π j) := by
  rw [E.config_eq_run ht.le] at hcount
  rw [E.emitted_eq_outBit ht.le] at hemit
  have hh := output_nth_eq_outBit (List.ofFn X) (ht.trans_le hTN)
    (show (outBit M (List.ofFn X) t).isSome by simp only [hemit, Option.isSome_some])
  rw [houtput, hcount, nth_ofFn _ j.isLt] at hh
  exact (Option.some.inj (hh.trans hemit)).symm

def ofRun (M : TM) (w : List Bool) (T : ℕ)
    (hactive : ∀ t < T, transAt M w t ≠ none) : ExecutionPrefix M w T where
  config := run M w
  initial := rfl
  successful t ht := by
    cases hs : step M w (run M w t) with
    | none => exact (hactive t ht ((step_run_eq_none_iff t).mp hs)).elim
    | some c => simp only [run, hs, Option.getD_some]

@[simp] theorem ofRun_config (M : TM) (w : List Bool) (T : ℕ)
    (hactive : ∀ t < T, transAt M w t ≠ none) (t : ℕ) :
    (ofRun M w T hactive).config t = run M w t := rfl

@[simp] theorem ofRun_emitted (M : TM) (w : List Bool) (T : ℕ)
    (hactive : ∀ t < T, transAt M w t ≠ none) (t : ℕ) :
    (ofRun M w T hactive).emitted t = outBit M w t := rfl

/-- Correct final native output implies correctness of each actual append,
with its actual chronological ordinal. No separate local correctness premise
is needed by the canonical-run application. -/
theorem ofRun_output_correct {M : TM} {P T N : ℕ} (X : Fin P → Bool)
    (π : Fin P → Fin P) (hactive : ∀ t < T, transAt M (List.ofFn X) t ≠ none)
    (hTN : T ≤ N)
    (houtput : (run M (List.ofFn X) N).outRev.reverse = List.ofFn (fun j => X (π j)))
    {t : ℕ} (ht : t < T) (j : Fin P) (bit : Bool)
    (hcount : ((ofRun M (List.ofFn X) T hactive).config t).outRev.length = j.val)
    (hemit : (ofRun M (List.ofFn X) T hactive).emitted t = some bit) :
    bit = X (π j) := by
  have hh := output_nth_eq_outBit (List.ofFn X) (ht.trans_le hTN)
    (show (outBit M (List.ofFn X) t).isSome by simp only [← ofRun_emitted M _ T hactive, hemit, Option.isSome_some])
  change (run M (List.ofFn X) t).outRev.length = j.val at hcount
  rw [houtput, hcount, nth_ofFn _ j.isLt] at hh
  change outBit M (List.ofFn X) t = some bit at hemit
  exact (Option.some.inj (hh.trans hemit)).symm

end ExecutionPrefix

/-- The actual raw-input symbols on a paid set follow from the exterior bits;
negative positions and positions beyond the finite input are public markers. -/
theorem readInput_eq_of_exterior {P : ℕ} {X Y : Fin P → Bool}
    (U : Finset (Fin P)) (I : Set ℤ)
    (hexterior : ∀ p ∉ U, X p = Y p)
    (hdisjoint : ∀ p : Fin P, (p.val : ℤ) ∈ I → p ∉ U)
    {z : ℤ} (hz : z ∈ I) : readInput (List.ofFn X) z = readInput (List.ofFn Y) z := by
  by_cases hneg : z < 0
  · simp only [readInput, ite_eq_left hneg]
  · simp only [readInput, ite_eq_right hneg]
    by_cases hp : z.toNat < P
    · rw [nth_ofFn X hp, nth_ofFn Y hp]
      congr 1
      apply hexterior _ (hdisjoint _ ?_)
      have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (show 0 ≤ z by omega)
      simpa only [hcast] using hz
    · rw [nth_eq_none_of_le (by simpa only [List.length_ofFn] using (le_of_not_gt hp)),
        nth_eq_none_of_le (by simpa only [List.length_ofFn] using (le_of_not_gt hp))]

end AdaptiveTransfer
