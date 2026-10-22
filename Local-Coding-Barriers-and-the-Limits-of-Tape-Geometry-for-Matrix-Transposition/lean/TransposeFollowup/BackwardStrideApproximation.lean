import TransposeFollowup.BackwardStrideMotion
import TransposeFollowup.BankReversalApproximation
import TransposeFollowup.StrideStageApproximation

/-! The backward stage inherits both forward-stride approximation regimes.
The two paid reversals add a constant eight cells to the error and a
fixed factor to the cover size. Public start times remain unrestricted. -/
namespace TransposeFollowup.BackwardMaskedStride
open Classical AffineMotion
set_option autoImplicit false

noncomputable def approximation (P S A : ℕ) (h : Fin 2) (t : ℝ) : ℝ :=
  BankReversal.approximation P A h t+
    MaskedStrideBankStage.approximation P S (A+BankReversal.ticks P) h t+
    BankReversal.approximation P (A+BankReversal.ticks P+MaskedStrideBankStage.ticks P S) h t

theorem approximation_cover (P S A B : ℕ) (hB : P/S≤B) {H : ℝ} (hH : 0≤H) (h : Fin 2) :
    HasAffineIntervalCover (81*(9^(B+1)*9)*81) (approximation P S A h) H := by
  exact ((BankReversal.approximation_cover P A hH h).add
    (MaskedStrideBankStage.approximation_cover P S (A+BankReversal.ticks P) B hB hH h)).add
    (BankReversal.approximation_cover P (A+BankReversal.ticks P+MaskedStrideBankStage.ticks P S) hH h)

theorem approximation_error (P : ℕ) {S : ℕ} (hS : 0<S) (A : ℕ) (h : Fin 2) (t : ℝ) :
    |(path P S h (⌊t⌋₊-A) : ℝ)-approximation P S A h t|≤2*((P/S : ℕ)+2)+8 := by
  have ha := BankReversal.approximation_error P A h t
  have hb := MaskedStrideBankStage.approximation_error P hS (A+BankReversal.ticks P) h t
  have hc := BankReversal.approximation_error P (A+BankReversal.ticks P+MaskedStrideBankStage.ticks P S) h t
  have h1 : ⌊t⌋₊-A-BankReversal.ticks P=⌊t⌋₊-(A+BankReversal.ticks P) := by omega
  have h2 : ⌊t⌋₊-A-BankReversal.ticks P-MaskedStrideBankStage.ticks P S=
      ⌊t⌋₊-(A+BankReversal.ticks P+MaskedStrideBankStage.ticks P S) := by omega
  simp only [path,approximation,Int.cast_add]
  rw [h2,h1,abs_le]
  rw [abs_le] at ha hb hc
  constructor <;> linarith

noncomputable def smallApproximation (P S A : ℕ) (h : Fin 2) (t : ℝ) : ℝ :=
  BankReversal.approximation P A h t+
    MaskedStrideBankStage.smallApproximation P (A+BankReversal.ticks P) h t+
    BankReversal.approximation P (A+BankReversal.ticks P+MaskedStrideBankStage.ticks P S) h t

theorem smallApproximation_cover (P S A : ℕ) {H : ℝ} (hH : 0≤H) (h : Fin 2) :
    HasAffineIntervalCover (81*9*81) (smallApproximation P S A h) H := by
  exact ((BankReversal.approximation_cover P A hH h).add
    (MaskedStrideBankStage.smallApproximation_cover P (A+BankReversal.ticks P) hH h)).add
    (BankReversal.approximation_cover P (A+BankReversal.ticks P+MaskedStrideBankStage.ticks P S) hH h)

theorem smallApproximation_error (P : ℕ) {S : ℕ} (hS : 0<S) (A : ℕ) (h : Fin 2) (t : ℝ) :
    |(path P S h (⌊t⌋₊-A) : ℝ)-smallApproximation P S A h t|≤7*(S : ℝ)+10 := by
  have ha := BankReversal.approximation_error P A h t
  have hb := MaskedStrideBankStage.smallApproximation_error P hS (A+BankReversal.ticks P) h t
  have hc := BankReversal.approximation_error P (A+BankReversal.ticks P+MaskedStrideBankStage.ticks P S) h t
  have h1 : ⌊t⌋₊-A-BankReversal.ticks P=⌊t⌋₊-(A+BankReversal.ticks P) := by omega
  have h2 : ⌊t⌋₊-A-BankReversal.ticks P-MaskedStrideBankStage.ticks P S=
      ⌊t⌋₊-(A+BankReversal.ticks P+MaskedStrideBankStage.ticks P S) := by omega
  simp only [path,smallApproximation,Int.cast_add]
  rw [h2,h1,abs_le]
  rw [abs_le] at ha hb hc
  constructor <;> linarith

end TransposeFollowup.BackwardMaskedStride
