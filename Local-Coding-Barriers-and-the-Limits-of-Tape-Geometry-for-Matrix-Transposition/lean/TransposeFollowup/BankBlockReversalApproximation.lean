import TransposeFollowup.BankBlockReversalMotion
import TransposeFollowup.ClippedAffineRamps

/-! Four clipped ramps per head approximate the complete paid block
reversal, including all seeks and cleanup. All-time sampling uses the
existing ramp rounding bound and freezes the internal program at its end. -/
namespace TransposeFollowup.BankBlockReversal
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
open CopyMachine (Sym)
set_option autoImplicit false
variable {M : Type*}

noncomputable def approximation (P A : ℕ) (h : Fin 2) (x : ℝ) : ℝ :=
  if h=0 then clippedRamp P A 1 x-clippedRamp P (A+P : ℕ) 4 x+
    clippedRamp P (A+6*P : ℕ) 2 x-clippedRamp P (A+8*P : ℕ) 1 x
  else clippedRamp P (A+P : ℕ) 4 x-clippedRamp P (A+5*P : ℕ) 1 x+
    clippedRamp P (A+6*P : ℕ) 2 x-clippedRamp P (A+9*P : ℕ) 1 x

theorem approximation_cover (P A : ℕ) {H : ℝ} (hH : 0 ≤ H) (h : Fin 2) :
    HasAffineIntervalCover 81 (approximation P A h) H := by
  have hc (a : ℕ) {d : ℝ} (hd : 0<d) :=
    clippedRamp_cover hH (Nat.cast_nonneg P) (Nat.cast_nonneg a) hd
  change HasAffineIntervalCover 81 (fun x => approximation P A h x) H
  by_cases hh : h=0
  · simp only [approximation,ite_eq_left hh]
    exact (((hc A (by norm_num : (0 : ℝ)<1)).sub (hc (A+P) (by norm_num : (0 : ℝ)<4))).add
      (hc (A+6*P) (by norm_num : (0 : ℝ)<2))).sub (hc (A+8*P) (by norm_num : (0 : ℝ)<1))
  · simp only [approximation,ite_eq_right hh]
    exact (((hc (A+P) (by norm_num : (0 : ℝ)<4)).sub (hc (A+5*P) (by norm_num : (0 : ℝ)<1))).add
      (hc (A+6*P) (by norm_num : (0 : ℝ)<2))).sub (hc (A+9*P) (by norm_num : (0 : ℝ)<1))

theorem path_approximation_error (P A : ℕ) (h : Fin 2) (x : ℝ) :
    |(path P h (⌊x⌋₊-A) : ℝ)-approximation P A h x| ≤ 4 := by
  have h0 := clippedRamp_sample_error P A 1 x
  have h1 := clippedRamp_sample_error P (A+P) 4 x
  have h2 := clippedRamp_sample_error P (A+5*P) 1 x
  have h3 := clippedRamp_sample_error P (A+6*P) 2 x
  have h4 := clippedRamp_sample_error P (A+8*P) 1 x
  have h5 := clippedRamp_sample_error P (A+9*P) 1 x
  simp only [Nat.div_one,Nat.cast_one,Nat.cast_ofNat] at h0 h1 h2 h3 h4 h5
  rw [abs_le] at h0 h1 h2 h3 h4 h5
  by_cases hh : h=0
  · simp only [path,approximation,ite_eq_left hh,Int.cast_sub,Int.cast_add,Int.cast_natCast,
      Nat.sub_sub]
    rw [abs_le]; constructor <;> linarith
  · simp only [path,approximation,ite_eq_right hh,Int.cast_sub,Int.cast_add,Int.cast_natCast,
      Nat.sub_sub]
    rw [abs_le]; constructor <;> linarith

theorem schedule_curve_error (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (B n A : ℕ) (hB : 0<B) (w : List Bool) (c : NativeIO.Config (Fin 2) M)
    (x : ℝ) (t : Fin 2) :
    |((trajectory (schedule read write reset B n) w c (min (⌊x⌋₊-A) (ticks B n))).work.pos t : ℝ)-
      c.work.pos t-approximation (n*B) A t x| ≤ 5*B+4 := by
  have h := schedule_path_error read write reset B n hB w c
    (min (⌊x⌋₊-A) (ticks B n)) (Nat.min_le_right _ _) t
  rw [ticks_eq,path_frozen] at h
  have hr : |((trajectory (schedule read write reset B n) w c
      (min (⌊x⌋₊-A) (ticks B n))).work.pos t : ℝ)-c.work.pos t-
      (path (n*B) t (⌊x⌋₊-A) : ℝ)| ≤ 5*B := by
    have he : ((|(trajectory (schedule read write reset B n) w c
        (min (⌊x⌋₊-A) (ticks B n))).work.pos t-c.work.pos t-path (n*B) t (⌊x⌋₊-A)| : ℤ) : ℝ) ≤ 5*B := by
      rw [ticks_eq]
      exact_mod_cast h
    simpa only [Int.cast_abs,Int.cast_sub] using he
  have ha := path_approximation_error (n*B) A t x
  rw [abs_le] at hr ha ⊢
  constructor <;> linarith

theorem scaled_approximation (read : Sym Bool → M) (write : M → Sym Bool) (reset : M)
    (B n : ℕ) (hB : 0<B) (hP : 0<n*B) {H : ℝ} (hH : 0 ≤ H)
    (w : List Bool) (c : NativeIO.Config (Fin 2) M) (t : Fin 2) :
    HasAffineIntervalCover 81 (fun x => approximation (n*B) 0 t ((n*B : ℕ)*x)/(n*B : ℕ)) H ∧
    ∀ x : ℝ,
      |(((trajectory (schedule read write reset B n) w c
          (min ⌊(n*B : ℕ)*x⌋₊ (ticks B n))).work.pos t : ℝ)-c.work.pos t)/(n*B : ℕ)-
        approximation (n*B) 0 t ((n*B : ℕ)*x)/(n*B : ℕ)| ≤ (5*B+4 : ℝ)/(n*B : ℕ) := by
  have hp : (0 : ℝ)<(n*B : ℕ) := by exact_mod_cast hP
  refine ⟨(approximation_cover (n*B) 0 (mul_nonneg hp.le hH) t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (by
    simpa only [Nat.sub_zero] using schedule_curve_error read write reset B n 0 hB w c ((n*B : ℕ)*x) t) hp.le

theorem approximation_error_vanishes {P B : ℕ → ℕ}
    (hP : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    (hB : Tendsto (fun i => (B i : ℝ)/P i) atTop (𝓝 0)) :
    Tendsto (fun i => (5*B i+4 : ℝ)/P i) atTop (𝓝 0) := by
  have hb : Tendsto (fun i => (4 : ℝ)/P i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hP
  simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using (hB.const_mul (5 : ℝ)).add hb

end TransposeFollowup.BankBlockReversal
