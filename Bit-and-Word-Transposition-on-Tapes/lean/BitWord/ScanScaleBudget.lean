import BitWord.ScanRawProgram

/-! One common analytical scale for every bank and every layer of the fixed raw
program. Its choice depends only on the public operations, never on the data. -/
namespace BitWord
open scoped BigOperators
open Classical
set_option autoImplicit false

namespace RawScanProgram
variable {P q L m : ℕ} {State : Type*}

noncomputable def badVolume (C : RawScanProgram P q L State) (B : ℕ) : ℕ :=
  ∑ t : Fin L, ∑ a : Fin q, (((C.layer t).stage a).bad B).card

theorem badVolume_castLength {P' : ℕ} (C : RawScanProgram P q L State)
    (h : P=P') (B : ℕ) : (C.castLength h).badVolume B = C.badVolume B := by
  subst P'
  rfl

theorem sum_badVolume_le (C : RawScanProgram P q L State) (B : Fin m → ℕ)
    (hsep : ∀ i j, i<j → Geometry.volume (B i) ≤ B j) :
    ∑ i, C.badVolume (B i) ≤ q*L*P := by
  unfold badVolume
  calc
    _ = ∑ t : Fin L, ∑ a : Fin q, ∑ i, (((C.layer t).stage a).bad (B i)).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_comm
    _ ≤ ∑ t : Fin L, ∑ a : Fin q, P :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum
        (fun a _ => ((C.layer t).stage a).total_bad_volume_le B hsep))
    _ = q*L*P := by simp; ring

/-- Exact integer averaging, avoiding any rounded per-scale payload allowance. -/
theorem exists_scale_badVolume (C : RawScanProgram P q L State) (hm : 0<m)
    (B : Fin m → ℕ) (hsep : ∀ i j, i<j → Geometry.volume (B i) ≤ B j) :
    ∃ i : Fin m, m*C.badVolume (B i) ≤ q*L*P := by
  by_contra hn
  have hall : ∀ i : Fin m, q*L*P < m*C.badVolume (B i) := by
    simpa only [not_exists, not_le] using hn
  have hsum : ∑ i : Fin m, q*L*P < ∑ i : Fin m, m*C.badVolume (B i) := by
    apply Finset.sum_lt_sum
    · exact fun i _ => (hall i).le
    · exact ⟨⟨0,hm⟩,Finset.mem_univ _,hall _⟩
  have hv := Nat.mul_le_mul_left m (C.sum_badVolume_le B hsep)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    ← Finset.mul_sum] at hsum
  omega
end RawScanProgram
end BitWord
