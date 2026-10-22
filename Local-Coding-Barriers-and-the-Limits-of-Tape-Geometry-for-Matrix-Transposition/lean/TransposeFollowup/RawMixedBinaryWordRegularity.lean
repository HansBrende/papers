import TransposeFollowup.MixedBinaryWordRegularity
import TransposeFollowup.RawMixedBinaryWordMotion
import TransposeFollowup.RawBankProgramApproximation

/-! Bounded-cover approximants for the actual full native mixed-word
execution, including all setup, output and the frozen halted tail. -/
namespace TransposeFollowup.RawMixedBinaryWord
open Classical Set Filter Topology AffineMotion
open BinaryBankOperation (Operation)
open MixedBinaryWord (Valid)
set_option autoImplicit false

theorem full_affine_approximation_subsequence {K : ℕ} {P : ℕ → ℕ}
    (hP : ∀ i, 0 < P i) (ops : ℕ → List Operation)
    (hv : ∀ᶠ i in atTop, Valid (P i) (ops i))
    (hK : ∀ᶠ i in atTop, (ops i).length ≤ K)
    (hPinf : Tendsto (fun i => (P i : ℝ)) atTop atTop) (inputs : ℕ → List Bool)
    {H : ℝ} (hH : 0 ≤ H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (J : ℕ) (e : ℕ → ℝ) (q : ℕ → Fin 2 → ℝ → ℝ),
      Tendsto e atTop (𝓝 0) ∧ ∀ᶠ i in atTop,
        (∀ h, HasAffineIntervalCover J (q i h) H) ∧
        ∀ h t, |(Transpose.Tape.workTraj (machine (P (φ i)) (ops (φ i))) (inputs (φ i))
          ⌊(P (φ i) : ℝ)*t⌋₊ ((encoding (P (φ i)) (ops (φ i))).port h) : ℝ)/P (φ i)-q i h t| ≤ e i := by
  obtain ⟨φ,hφ,J,e,q,he,hq⟩ := MixedBinaryWord.affine_approximation_subsequence hP ops hv hK hPinf hH
  refine ⟨φ,hφ,J*27,fun i => e i+4/P (φ i),
    fun i h t => q i (4*P (φ i)) h t+
      RawBankProgram.ioCurve (P (φ i)) (MixedBinaryWord.ticks (P (φ i)) (ops (φ i))) h
        ((P (φ i) : ℝ)*t)/P (φ i),?_,?_⟩
  · have hr : Tendsto (fun i => (4 : ℝ)/P (φ i)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hPinf.comp hφ.tendsto_atTop)
    simpa only [add_zero] using he.add hr
  · filter_upwards [hq,hφ.tendsto_atTop.eventually hv] with i hi hv'
    have hp : (0 : ℝ) < P (φ i) := by exact_mod_cast hP (φ i)
    refine ⟨fun h => ((hi (4*P (φ i))).1 h).add
      ((RawBankProgram.ioCurve_cover _ _ (mul_nonneg hp.le hH) h).rescale hp),?_⟩
    intro h t
    rw [workTraj_position _ _ hv']
    have hb := (hi (4*P (φ i))).2 h t
    have hh := RawBankProgram.ioCurve_error (P (φ i)) (body (P (φ i)) (ops (φ i)))
      (motion (P (φ i)) (ops (φ i)) hv') h ((P (φ i) : ℝ)*t)
    have hd : |((path (P (φ i)) (ops (φ i)) h ⌊(P (φ i) : ℝ)*t⌋₊ : ℝ)-
        (MixedBinaryWord.path (P (φ i)) (ops (φ i)) h (⌊(P (φ i) : ℝ)*t⌋₊-4*P (φ i)) : ℝ)-
        RawBankProgram.ioCurve (P (φ i)) (MixedBinaryWord.ticks (P (φ i)) (ops (φ i))) h
          ((P (φ i) : ℝ)*t))/P (φ i)| ≤ 4/P (φ i) := by
      rw [abs_div,abs_of_pos hp]
      exact div_le_div_of_nonneg_right hh hp.le
    rw [sub_div,sub_div,abs_le] at hd
    rw [abs_le] at hb ⊢
    constructor <;> linarith

end TransposeFollowup.RawMixedBinaryWord
