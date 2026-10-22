import TransposeFollowup.MaskedStrideRamps
import TransposeFollowup.ClippedAffineRamps

/-! Explicit finite-affine approximants for the existing paid head paths.
With bounded group count, the normalized rounding error vanishes. No
parameter-limit formula or new compactness theorem is needed. -/
namespace TransposeFollowup.MaskedStrideScan
open Classical Finset AffineMotion
set_option autoImplicit false

noncomputable def bankCurve (P S : ℕ) (t : ℝ) : ℝ :=
  (∑ r ∈ range (P/S), clippedRamp S (r*(4*S) : ℕ) 3 t)+
    clippedRamp (P%S : ℕ) (P/S*(4*S) : ℕ) 3 t

noncomputable def scratchCurve (P S : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ range (P/S+1),
    (clippedRamp S (r*(4*S) : ℕ) 3 t-clippedRamp S (r*(4*S)+3*S : ℕ) 1 t)

theorem bankCurve_error (P : ℕ) {S : ℕ} (hS : 0<S) (t : ℝ) :
    |(bankPosition P S (min ⌊t⌋₊ (ticks P S)) : ℝ)-bankCurve P S t| ≤ (P/S : ℕ)+1 := by
  rw [bankPosition_freeze P hS,bankPosition_sum P hS]
  push_cast
  unfold bankCurve
  have hs : |(∑ r ∈ range (P/S), (rise S (r*(4*S)) ⌊t⌋₊ : ℝ))-
      ∑ r ∈ range (P/S), clippedRamp S (r*(4*S) : ℕ) 3 t| ≤ (P/S : ℕ) := by
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ r ∈ range (P/S), |(rise S (r*(4*S)) ⌊t⌋₊ : ℝ)-clippedRamp S (r*(4*S) : ℕ) 3 t| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ range (P/S), (1 : ℝ) := sum_le_sum fun r _ => by
        simpa only [rise,Nat.cast_ofNat] using clippedRamp_sample_error S (r*(4*S)) 3 t
      _ = _ := by simp
  have hl : |(rise (P%S) (P/S*(4*S)) ⌊t⌋₊ : ℝ)-clippedRamp (P%S : ℕ) (P/S*(4*S) : ℕ) 3 t| ≤ 1 := by
    simpa only [rise,Nat.cast_ofNat] using clippedRamp_sample_error (P%S) (P/S*(4*S)) 3 t
  rw [abs_le] at hs hl ⊢
  constructor <;> linarith

theorem scratchCurve_error (P : ℕ) {S : ℕ} (hS : 0<S) (t : ℝ) :
    |(scratchPosition P S (min ⌊t⌋₊ (ticks P S)) : ℝ)-scratchCurve P S t| ≤ 2*((P/S : ℕ)+1) := by
  rw [scratchPosition_sum P hS]
  push_cast
  unfold scratchCurve
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ range (P/S+1),
        |(pulse S (r*(4*S)) ⌊t⌋₊ : ℝ)-
          (clippedRamp S (r*(4*S) : ℕ) 3 t-clippedRamp S (r*(4*S)+3*S : ℕ) 1 t)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ range (P/S+1), (2 : ℝ) := by
      apply sum_le_sum
      intro r _
      have h1 := clippedRamp_sample_error S (r*(4*S)) 3 t
      have h2 := clippedRamp_sample_error S (r*(4*S)+3*S) 1 t
      simp only [Nat.div_one,Nat.cast_one] at h2
      simp only [pulse,rise,Int.cast_sub,Int.cast_natCast]
      simp only [Nat.cast_ofNat] at h1
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    _ = _ := by simp; ring

theorem bankCurve_cover (P S : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    HasAffineIntervalCover (3^(P/S+1)) (bankCurve P S) H := by
  have hfull : HasAffineIntervalCover (3^(P/S))
      (fun t => ∑ r ∈ range (P/S), clippedRamp S (r*(4*S) : ℕ) 3 t) H :=
    HasAffineIntervalCover.sum_range hH _ (fun _ _ => clippedRamp_cover hH (by positivity) (by positivity) (by norm_num))
  rw [pow_succ]
  exact hfull.add (clippedRamp_cover (L:=(P%S : ℕ)) (a:=(P/S*(4*S) : ℕ)) hH
      (by positivity) (by positivity) (show (0 : ℝ)<3 by norm_num))

theorem scratchCurve_cover (P S : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    HasAffineIntervalCover (9^(P/S+1)) (scratchCurve P S) H := by
  apply HasAffineIntervalCover.sum_range hH
  intro r _
  exact (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<3 by norm_num)).sub
    (clippedRamp_cover hH (by positivity) (by positivity) (show (0 : ℝ)<1 by norm_num))

theorem bounded_curve_covers (P S B : ℕ) (hB : P/S ≤ B) {H : ℝ} (hH : 0 ≤ H) :
    HasAffineIntervalCover (9^(B+1)) (bankCurve P S) H ∧
    HasAffineIntervalCover (9^(B+1)) (scratchCurve P S) H := by
  have hpow : 9^(P/S+1) ≤ 9^(B+1) := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨(bankCurve_cover P S hH).mono (by positivity)
      ((Nat.pow_le_pow_left (by decide : 3 ≤ 9) _).trans hpow),
    (scratchCurve_cover P S hH).mono (by positivity) hpow⟩

theorem normalized_curve_errors {P S : ℕ} (hP : 0<P) (hS : 0<S) (t : ℝ) :
    |(bankPosition P S (min ⌊(P : ℝ)*t⌋₊ (ticks P S)) : ℝ)/P-bankCurve P S ((P : ℝ)*t)/P| ≤
      ((P/S : ℕ)+1)/(P : ℝ) ∧
    |(scratchPosition P S (min ⌊(P : ℝ)*t⌋₊ (ticks P S)) : ℝ)/P-scratchCurve P S ((P : ℝ)*t)/P| ≤
      (2*((P/S : ℕ)+1))/(P : ℝ) := by
  have hp : (0 : ℝ)<P := by exact_mod_cast hP
  constructor <;> rw [← sub_div,abs_div,abs_of_pos hp]
  · exact div_le_div_of_nonneg_right (bankCurve_error P hS _) hp.le
  · exact div_le_div_of_nonneg_right (scratchCurve_error P hS _) hp.le

end TransposeFollowup.MaskedStrideScan
