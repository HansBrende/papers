import TransposeFollowup.SchwartzWaveletEstimate
import Mathlib.Topology.Sequences

/-! Affine coefficients with arbitrary L2 test vectors, obtained as
pointwise limits of their Schwartz counterparts. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap Filter
open scoped FourierTransform Topology
set_option autoImplicit false

noncomputable def l2WaveletCoefficient (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) (s t : ℝ) : ℂ :=
  if hs : 0 < s then
    inner ℂ v (((schwartzUnitaryScale u s hs).compSubConstCLM ℂ t).toLp 2 volume)
  else 0

theorem l2WaveletCoefficient_pos (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) {s : ℝ}
    (hs : 0 < s) (t : ℝ) :
    l2WaveletCoefficient u v s t =
      inner ℂ v (((schwartzUnitaryScale u s hs).compSubConstCLM ℂ t).toLp 2 volume) := by
  simp only [l2WaveletCoefficient, dite_eq_left hs]

theorem l2WaveletCoefficient_schwartz (u v : 𝓢(ℝ, ℂ)) (s t : ℝ) :
    l2WaveletCoefficient u (v.toLp 2 volume) s t = waveletCoefficient u v s t := by
  by_cases hs : 0 < s
  · rw [l2WaveletCoefficient_pos u _ hs, waveletCoefficient_eq_inner u v hs]
  · simp [l2WaveletCoefficient, hs, waveletCoefficient,
      Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hs)]

theorem schwartz_toL2_sequence (v : ComplexL2) :
    ∃ w : ℕ → 𝓢(ℝ, ℂ), Tendsto (fun n => (w n).toLp 2 volume) atTop (𝓝 v) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
    (μ := volume) (by norm_num)
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp (hd v)
  choose f hf using hw
  refine ⟨f, ?_⟩
  have he : (fun n => (f n).toLp 2 volume) = w := funext hf
  rw [he]
  exact hlim

theorem l2WaveletCoefficient_tendsto (u : 𝓢(ℝ, ℂ)) {w : ℕ → ComplexL2}
    {v : ComplexL2} (hw : Tendsto w atTop (𝓝 v)) (s t : ℝ) :
    Tendsto (fun n => l2WaveletCoefficient u (w n) s t) atTop
      (𝓝 (l2WaveletCoefficient u v s t)) := by
  by_cases hs : 0 < s
  · simp only [l2WaveletCoefficient, dite_eq_left hs]
    exact hw.inner tendsto_const_nhds
  · simp only [l2WaveletCoefficient, dite_eq_right hs]
    exact tendsto_const_nhds

theorem l2WaveletCoefficient_measurable (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) :
    Measurable (fun z : ℝ × ℝ => l2WaveletCoefficient u v z.1 z.2) := by
  obtain ⟨w, hw⟩ := schwartz_toL2_sequence v
  apply measurable_of_tendsto_metrizable (f := fun n z =>
    l2WaveletCoefficient u ((w n).toLp 2 volume) z.1 z.2)
  · intro n
    simpa only [l2WaveletCoefficient_schwartz] using waveletCoefficient_measurable u (w n)
  · exact tendsto_pi_nhds.mpr (fun z => l2WaveletCoefficient_tendsto u hw z.1 z.2)

end TransposeFollowup
