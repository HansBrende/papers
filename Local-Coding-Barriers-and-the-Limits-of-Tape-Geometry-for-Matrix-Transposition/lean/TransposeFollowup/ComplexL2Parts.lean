import TransposeFollowup.FrequencyCutoff
import TransposeFollowup.RealMobiusL2

/-! Real and imaginary parts of actual L2 classes. These maps permit reuse
of the proved real Mobius action on complex Fourier components. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open RealMobius
set_option autoImplicit false

noncomputable def ofRealL2 : RealL2 →L[ℝ] ComplexL2 := Complex.ofRealCLM.compLpL 2 volume
noncomputable def realPartL2 : ComplexL2 →L[ℝ] RealL2 := Complex.reCLM.compLpL 2 volume
noncomputable def imagPartL2 : ComplexL2 →L[ℝ] RealL2 := Complex.imCLM.compLpL 2 volume

theorem ofRealL2_coe (f : RealL2) : ⇑(ofRealL2 f) =ᵐ[volume] (fun x => (f x : ℂ)) :=
  Complex.ofRealCLM.coeFn_compLpL f

theorem realPartL2_coe (f : ComplexL2) : ⇑(realPartL2 f) =ᵐ[volume] (fun x => (f x).re) :=
  Complex.reCLM.coeFn_compLpL f

theorem imagPartL2_coe (f : ComplexL2) : ⇑(imagPartL2 f) =ᵐ[volume] (fun x => (f x).im) :=
  Complex.imCLM.coeFn_compLpL f

theorem realPartL2_ofReal (f : RealL2) : realPartL2 (ofRealL2 f) = f := by
  apply Lp.ext
  filter_upwards [realPartL2_coe (ofRealL2 f), ofRealL2_coe f] with x hr hf
  rw [hr, hf, Complex.ofReal_re]

theorem imagPartL2_ofReal (f : RealL2) : imagPartL2 (ofRealL2 f) = 0 := by
  apply Lp.ext
  filter_upwards [imagPartL2_coe (ofRealL2 f), ofRealL2_coe f, Lp.coeFn_zero ℝ 2 volume]
    with x hi hf hz
  rw [hi, hf, Complex.ofReal_im]
  exact hz.symm

theorem ofRealL2_norm (f : RealL2) : ‖ofRealL2 f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [complexL2_norm_sq, realL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [ofRealL2_coe f] with x hx
  simp only [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem ofRealL2_inner (f g : RealL2) : inner ℝ (ofRealL2 f) (ofRealL2 g) = inner ℝ f g := by
  have he : inner ℝ (ofRealL2 f) (ofRealL2 g) =
      (‖ofRealL2 f + ofRealL2 g‖ ^ 2 - ‖ofRealL2 f‖ ^ 2 - ‖ofRealL2 g‖ ^ 2) / 2 := by
    nlinarith [norm_add_sq_real (ofRealL2 f) (ofRealL2 g)]
  rw [he, ← map_add, ofRealL2_norm, ofRealL2_norm, ofRealL2_norm]
  nlinarith [norm_add_sq_real f g]

theorem complexL2_norm_sq_parts (f : ComplexL2) :
    ‖f‖ ^ 2 = ‖realPartL2 f‖ ^ 2 + ‖imagPartL2 f‖ ^ 2 := by
  rw [complexL2_norm_sq, realL2_norm_sq, realL2_norm_sq,
    ← integral_add (Lp.memLp (realPartL2 f)).integrable_sq (Lp.memLp (imagPartL2 f)).integrable_sq]
  apply integral_congr_ae
  filter_upwards [realPartL2_coe f, imagPartL2_coe f] with x hr hi
  rw [hr, hi, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem complexL2_inner_parts (f g : ComplexL2) :
    inner ℝ f g = inner ℝ (realPartL2 f) (realPartL2 g) +
      inner ℝ (imagPartL2 f) (imagPartL2 g) := by
  have h := complexL2_norm_sq_parts (f + g)
  simp only [map_add, norm_add_sq_real, complexL2_norm_sq_parts f, complexL2_norm_sq_parts g] at h
  linarith

theorem realPartL2_I_smul (f : ComplexL2) : realPartL2 (Complex.I • f) = -imagPartL2 f := by
  apply Lp.ext
  filter_upwards [realPartL2_coe (Complex.I • f), Lp.coeFn_smul Complex.I f,
    imagPartL2_coe f, Lp.coeFn_neg (imagPartL2 f)] with x hr hs hi hn
  rw [hr, hs, hn]
  change (Complex.I * f x).re = -imagPartL2 f x
  rw [hi]
  simp

theorem imagPartL2_I_smul (f : ComplexL2) : imagPartL2 (Complex.I • f) = realPartL2 f := by
  apply Lp.ext
  filter_upwards [imagPartL2_coe (Complex.I • f), Lp.coeFn_smul Complex.I f,
    realPartL2_coe f] with x hi hs hr
  rw [hi, hs, hr]
  change (Complex.I * f x).im = (f x).re
  simp

end TransposeFollowup
