import TransposeFollowup.MixedBinaryWordMotion
import TransposeFollowup.BackwardStrideApproximation
import TransposeFollowup.BankRotationApproximation

/-! Analytic slots for bounded mixed words. A missing list entry contributes
zero to the path and curve; it is not an additional machine instruction.
Uniform bounds allow operation types and public parameters to vary. -/
namespace TransposeFollowup.BinaryBankSlot
open Classical AffineMotion
open BinaryBankOperation (Operation)
set_option autoImplicit false

def stride : Option Operation → ℕ
  | some (.forward _ _ S) | some (.backward _ _ S) => S
  | _ => 0

def Valid (P : ℕ) (op : Option Operation) : Prop :=
  ∀ a ∈ op, BinaryBankOperation.Valid P a

def path (P : ℕ) (op : Option Operation) (h : Fin 2) (n : ℕ) : ℤ :=
  op.elim 0 (fun a => BinaryBankOperation.path P a h n)

theorem stride_le (P : ℕ) (op : Option Operation) (hv : Valid P op) : stride op ≤ P := by
  cases op with
  | none => exact Nat.zero_le _
  | some op =>
    have hv := hv op rfl
    cases op with
    | forward pre mask S =>
        exact hv.2
    | backward pre mask S =>
        exact hv.2
    | reverse =>
        exact Nat.zero_le _
    | rotate R =>
        exact Nat.zero_le _

noncomputable def approximation (P A : ℕ) : Option Operation → Fin 2 → ℝ → ℝ
  | some (.forward _ _ S) => MaskedStrideBankStage.approximation P S A
  | some (.backward _ _ S) => BackwardMaskedStride.approximation P S A
  | some .reverse => BankReversal.approximation P A
  | some (.rotate R) => BankRotation.approximation P R A
  | none => fun _ _ => 0

noncomputable def smallApproximation (P A : ℕ) : Option Operation → Fin 2 → ℝ → ℝ
  | some (.forward _ _ _) => MaskedStrideBankStage.smallApproximation P A
  | some (.backward _ _ S) => BackwardMaskedStride.smallApproximation P S A
  | some .reverse => BankReversal.approximation P A
  | some (.rotate R) => BankRotation.approximation P R A
  | none => fun _ _ => 0

def coverBound (B : ℕ) : ℕ := 81*81*81*(9^(B+1)*9)

theorem coverBound_pos (B : ℕ) : 0 < coverBound B := by unfold coverBound; positivity

theorem approximation_cover (P A B : ℕ) (op : Option Operation)
    (hB : P/stride op ≤ B) {H : ℝ} (hH : 0 ≤ H) (h : Fin 2) :
    HasAffineIntervalCover (coverBound B) (approximation P A op h) H := by
  have hp : 1 ≤ 9^(B+1) := Nat.one_le_pow _ _ (by decide)
  cases op with
  | none => exact (HasAffineIntervalCover.const hH 0).mono (by omega) (by unfold coverBound; nlinarith)
  | some op =>
    cases op with
    | forward pre mask S =>
        exact (MaskedStrideBankStage.approximation_cover P S A B hB hH h).mono (by positivity)
          (by unfold coverBound; nlinarith)
    | backward pre mask S =>
        exact (BackwardMaskedStride.approximation_cover P S A B hB hH h).mono (by positivity)
          (by unfold coverBound; nlinarith)
    | reverse =>
        exact (BankReversal.approximation_cover P A hH h).mono (by norm_num)
          (by unfold coverBound; nlinarith)
    | rotate R =>
        exact (BankRotation.approximation_cover P R A hH h).mono (by norm_num)
          (by unfold coverBound; nlinarith)

theorem smallApproximation_cover (P A : ℕ) (op : Option Operation) {H : ℝ}
    (hH : 0 ≤ H) (h : Fin 2) : HasAffineIntervalCover (coverBound 0) (smallApproximation P A op h) H := by
  cases op with
  | none => exact (HasAffineIntervalCover.const hH 0).mono (by norm_num) (by norm_num [coverBound])
  | some op =>
    cases op with
    | forward pre mask S =>
        exact (MaskedStrideBankStage.smallApproximation_cover P A hH h).mono
          (by norm_num) (by norm_num [coverBound])
    | backward pre mask S =>
        exact (BackwardMaskedStride.smallApproximation_cover P S A hH h).mono
          (by norm_num) (by norm_num [coverBound])
    | reverse =>
        exact (BankReversal.approximation_cover P A hH h).mono
          (by norm_num) (by norm_num [coverBound])
    | rotate R =>
        exact (BankRotation.approximation_cover P R A hH h).mono
          (by norm_num) (by norm_num [coverBound])

theorem approximation_error (P A : ℕ) (op : Option Operation) (hv : Valid P op) (h : Fin 2) (t : ℝ) :
    |(path P op h (⌊t⌋₊-A) : ℝ)-approximation P A op h t| ≤ 2*((P/stride op : ℕ) : ℝ)+14 := by
  cases op with
  | none => simp [path,approximation,stride]
  | some op =>
    have hv := hv op rfl
    cases op with
    | forward pre mask S =>
        exact (MaskedStrideBankStage.approximation_error P hv.1 A h t).trans (by dsimp [stride]; linarith)
    | backward pre mask S =>
        exact (BackwardMaskedStride.approximation_error P hv.1 A h t).trans (by dsimp [stride]; linarith)
    | reverse =>
        exact (BankReversal.approximation_error P A h t).trans (by norm_num [stride])
    | rotate R =>
        exact (BankRotation.approximation_error P R A h t).trans (by norm_num [stride])

theorem smallApproximation_error (P A : ℕ) (op : Option Operation) (hv : Valid P op) (h : Fin 2) (t : ℝ) :
    |(path P op h (⌊t⌋₊-A) : ℝ)-smallApproximation P A op h t| ≤ 7*(stride op : ℝ)+14 := by
  cases op with
  | none => simp [path,smallApproximation,stride]
  | some op =>
    have hv := hv op rfl
    cases op with
    | forward pre mask S =>
        exact (MaskedStrideBankStage.smallApproximation_error P hv.1 A h t).trans (by dsimp [stride]; linarith)
    | backward pre mask S =>
        exact (BackwardMaskedStride.smallApproximation_error P hv.1 A h t).trans (by dsimp [stride]; linarith)
    | reverse =>
        exact (BankReversal.approximation_error P A h t).trans (by norm_num [stride])
    | rotate R =>
        exact (BankRotation.approximation_error P R A h t).trans (by norm_num [stride])

end TransposeFollowup.BinaryBankSlot
