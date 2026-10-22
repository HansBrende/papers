import TransposeFollowup.LocalizedCentralizerSample
import TransposeFollowup.CentralizerCubicPacking
import TransposeFollowup.SL2AdjointSpan

/-! Connect the retained commuting sample to the existing cubic-packing
theorem. Matrix products, scalar coordinates, source witnesses, localization
loss and required input spacing are all explicit. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix BoundedCoordinatePacking
open scoped Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem matrixConjugation_trace_det_norm (g : G) (b : RMat) {H N : ℝ}
    (hH : 0 ≤ H) (hg : ∀ i j, |g i j| ≤ H) (hb : ‖b‖ ≤ N) :
    Matrix.trace (matrixConjugationLinear g b) = Matrix.trace b ∧
      (matrixConjugationLinear g b).det = b.det ∧
      ‖matrixConjugationLinear g b‖ ≤ 4 * H ^ 2 * N := by
  have hgi : ((g⁻¹ : G) : RMat) * (g : RMat) = 1 :=
    congrArg (fun z : G => (z : RMat)) (inv_mul_cancel g)
  refine ⟨?_, ?_, ?_⟩
  · rw [matrixConjugationLinear_apply, Matrix.trace_mul_cycle, hgi, one_mul]
  · simp only [matrixConjugationLinear_apply, Matrix.det_mul,
      Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]
  · have hn := frobenius_norm_le_of_entry_bound hH hg
    have hni := frobenius_norm_le_of_entry_bound hH (RealMobius.matrixEntryBox_inv hg)
    have hh := norm_mul_le_of_le (norm_mul_le_of_le hn hb) hni
    calc
      _ ≤ (2 * H * N) * (2 * H) := hh
      _ = _ := by ring

theorem matrixConjugation_scalarAffine (g : G) (b : RMat) (c t : ℝ) :
    matrixConjugationLinear g (scalarAffine b c t) =
      scalarAffine (matrixConjugationLinear g b) c t := by
  have he : matrixConjugationLinear g (1 : RMat) = 1 := by
    change (g : RMat) * 1 * ((g⁻¹ : G) : RMat) = 1
    rw [mul_one]
    exact congrArg (fun z : G => (z : RMat)) (mul_inv_cancel g)
  simp only [scalarAffine_eq_smul_add, map_add, map_smul, he]

theorem conjugated_centered_cubic_packing (F : Finset ℝ) (b : RMat)
    (w : ℝ → G) (a : ℝ → ℝ) (u v : G) {H N M r d : ℝ} {η : ℝ≥0}
    (hH : 1 ≤ H) (hN : 1 ≤ N) (hM : 1 ≤ M) (hscale : 4 * H ^ 2 * N ≤ M)
    (hu : ∀ i j, |u i j| ≤ H) (hv : ∀ i j, |v i j| ≤ H)
    (hb : Matrix.trace b = 0) (hbn : ‖b‖ ≤ N) (hbd : |b.det| ≤ N)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hd : 0 < d)
    (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hdet : d ≤ |(directionFrame b (matrixConjugationLinear u b)
      (matrixConjugationLinear v b)).det|)
    (hw : ∀ x ∈ F, (w x : RMat) = scalarAffine b (a x) x)
    (ha : ∀ x ∈ F, 1 / 2 ≤ a x) (ht : ∀ x ∈ F, |x| ≤ r)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      384 * M ^ 4 / d * (η : ℝ) < |x - y|) :
    let S := Set.range (fun x : Fin 3 → ↥F =>
      ((w (x 0) * (u * w (x 1) * u⁻¹) * (v * w (x 2) * v⁻¹) : G) : RMat))
    Metric.externalCoveringNumber η S ≠ ⊤ ∧
      (F.card : ℝ) ^ 3 ≤ (Metric.externalCoveringNumber η S : ℝ≥0∞).toReal := by
  have hNM : N ≤ M := by
    have hHsq : 1 ≤ H ^ 2 := one_le_pow₀ hH
    nlinarith
  obtain ⟨htu, hdu, hnu⟩ := matrixConjugation_trace_det_norm u b (by linarith) hu hbn
  obtain ⟨htv, hdv, hnv⟩ := matrixConjugation_trace_det_norm v b (by linarith) hv hbn
  let bs : Fin 3 → RMat := ![b, matrixConjugationLinear u b, matrixConjugationLinear v b]
  let ws : Fin 3 → ℝ → G := ![w, fun x => u * w x * u⁻¹, fun x => v * w x * v⁻¹]
  let T := directionFrame b (matrixConjugationLinear u b) (matrixConjugationLinear v b)
  have htr : ∀ i, Matrix.trace (bs i) = 0 := by
    intro i
    fin_cases i
    · exact hb
    · exact htu.trans hb
    · exact htv.trans hb
  have hn : ∀ i, ‖bs i‖ ≤ M := by
    intro i
    fin_cases i
    · exact hbn.trans hNM
    · exact hnu.trans hscale
    · exact hnv.trans hscale
  have hde : ∀ i, |(bs i).det| ≤ M := by
    intro i
    fin_cases i
    · exact hbd.trans hNM
    · change |(matrixConjugationLinear u b).det| ≤ M
      rw [hdu]
      exact hbd.trans hNM
    · change |(matrixConjugationLinear v b).det| ≤ M
      rw [hdv]
      exact hbd.trans hNM
  have hcolumns : ∀ i j, T i j.succ = matrixCoordinates (bs j) i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hcoords (i : Fin 4) (j : Fin 3) : |matrixCoordinates (bs j) i| ≤ M := by
    have he (k l : Fin 2) : |(bs j) k l| ≤ M := by
      have hh := entry_error_le_frobenius_dist (bs j) 0 k l
      simp only [Matrix.zero_apply, sub_zero, dist_zero_right] at hh
      exact hh.trans (hn j)
    fin_cases i <;> exact he _ _
  have hT : ∀ i j, |T i j| ≤ M := by
    intro i j
    refine Fin.cases ?_ (fun k => ?_) j
    · fin_cases i <;> simp [T, directionFrame] <;> linarith
    · rw [hcolumns]
      exact hcoords i k
  have hconj (g : G) (x : ℝ) (hx : x ∈ F) :
      ((g * w x * g⁻¹ : G) : RMat) =
        scalarAffine (matrixConjugationLinear g b) (a x) x := by
    change matrixConjugationLinear g (w x : RMat) = _
    rw [hw x hx, matrixConjugation_scalarAffine]
  have hws : ∀ i x, x ∈ F → (ws i x : RMat) = scalarAffine (bs i) (a x) x := by
    intro i x hx
    fin_cases i
    · exact hw x hx
    · exact hconj u x hx
    · exact hconj v x hx
  exact centered_triple_product_cubic_packing F bs ws (fun _ => a) T
    hM hr hr1 hd hsmall habsorb hT hdet hcolumns htr hn hde hws (fun _ => ha) ht hsep

theorem exists_localized_conjugated_cubic_packing {ι : Type*} [Fintype ι]
    (f : ι → G) (b : RMat) (c t : ι → ℝ) (u v : G)
    {B H N M ρ r δ d : ℝ} {η : ℝ≥0} {m : ℕ}
    (hB : 1 ≤ B) (hH : 1 ≤ H) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hscale : 4 * H ^ 2 * N ≤ M)
    (hu : ∀ i j, |u i j| ≤ H) (hv : ∀ i j, |v i j| ≤ H)
    (hρ : 0 < ρ) (hδ : 0 < δ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m)
    (hb : Matrix.trace b = 0) (hbn : ‖b‖ ≤ N) (hbd : |b.det| ≤ N)
    (hpivot : ∃ i, ρ ≤ |noncentralCoordinates b i|)
    (hf : ∀ x i j, |f x i j| ≤ B)
    (hform : ∀ x, (f x : RMat) = scalarAffine b (c x) (t x))
    (hbranch : 8 * B * δ ≤ 1) (hradius : 8 * B * δ ≤ ρ * r)
    (hcard : binCount B δ ^ 4 * m ≤ Fintype.card ι)
    (hd : 0 < d) (hsmall : 3 * M * r ≤ 1) (habsorb : 36864 * M ^ 6 * r ≤ d)
    (hdet : d ≤ |(directionFrame b (matrixConjugationLinear u b)
      (matrixConjugationLinear v b)).det|)
    (hsep : ∀ x y, x ≠ y →
      10 * B * M * (384 * M ^ 4 / d * (η : ℝ)) < dist (f x : RMat) (f y : RMat)) :
    ∃ x₀ : ι, ∃ F : Finset ℝ, ∃ s : ℝ → ι,
      m ≤ F.card ∧
      (∀ x ∈ F, dist (f (s x) : RMat) (f x₀ : RMat) ≤ 2 * δ) ∧
      let w := fun x => (f x₀)⁻¹ * f (s x)
      let S := Set.range (fun x : Fin 3 → ↥F =>
        ((w (x 0) * (u * w (x 1) * u⁻¹) * (v * w (x 2) * v⁻¹) : G) : RMat))
      Metric.externalCoveringNumber η S ≠ ⊤ ∧
        (m : ℝ) ^ 3 ≤ (Metric.externalCoveringNumber η S : ℝ≥0∞).toReal := by
  have hNM : N ≤ M := by
    have hHsq : 1 ≤ H ^ 2 := one_le_pow₀ hH
    nlinarith
  obtain ⟨x₀, F, s, a, hF, hw, ha, hclose, hs⟩ :=
    exists_localized_scalar_sample f b c t hB hM hρ hδ
      (by positivity : 0 ≤ 384 * M ^ 4 / d * (η : ℝ))
      hr hr1 hm hb (hbn.trans hNM) (hbd.trans hNM) hpivot hf hform hbranch hradius hcard hsep
  obtain ⟨hfin, hpack⟩ := conjugated_centered_cubic_packing F b
    (fun x => (f x₀)⁻¹ * f (s x)) a u v hH hN hM hscale hu hv hb hbn hbd
    hr hr1 hd hsmall habsorb hdet hw (fun x hx => (ha x hx).1) (fun x hx => (ha x hx).2) hs
  refine ⟨x₀, F, s, hF, hclose, hfin, ?_⟩
  exact (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m) (by exact_mod_cast hF) 3).trans hpack

end TransposeFollowup.SL2Projection
