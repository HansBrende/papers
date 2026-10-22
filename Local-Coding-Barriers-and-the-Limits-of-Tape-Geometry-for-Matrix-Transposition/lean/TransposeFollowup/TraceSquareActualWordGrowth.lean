import TransposeFollowup.TraceSquareMixedCells
import TransposeFollowup.TraceSquarePairedEnlargement
import TransposeFollowup.TraceSquareReadoutParameters

/-! Turn ring growth of the retained scalar set into trace growth of an
actual finite word family. Both orientations are permitted, with the
larger readout coefficient assigned to the enlarged factor. Every chosen
word retains the same length, near-radius and quantitative distance bounds. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius OAI.Falconer
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

/-- An actual source-word conclusion, including geometric separation.
The scalar sum/product alternative is the input to this transfer lemma;
no covering bound for the mixed scalar sum is assumed. -/
theorem trace_square_actual_word_growth (P : Finset (G × G)) (b : RMat) (g : G)
    {A : Set G} {m k : ℕ} {δ : ℝ≥0} {α R ε M ρ s σ K gain : ℝ}
    (hP : P.Nonempty) (hA1 : 1 ∈ A) (hAi : A⁻¹=A)
    (hα : 0 < α) (hαone : α ≤ 1) (hA : A ⊆ mobiusIdentityBall α)
    (hδ : 0 < δ) (hR : 1 ≤ R) (hε : 0 ≤ ε) (hM : 32 ≤ M)
    (hρ : 0 < ρ) (hσ : 0 ≤ σ)
    (hb : Matrix.trace b = 0) (hdet : b.det ≠ 0) (hbn : ‖b‖ ≤ M) (hbd : |b.det| ≤ 32)
    (hbg : ‖matrixConjugationLinear g b‖ ≤ M)
    (hD : ρ ≤ |(b*(g : RMat)-(g : RMat)*b).det|)
    (hD' : ρ ≤ |(b*(g : RMat)-(g : RMat)*b).det-4*b.det|)
    (hsource : ∀ w ∈ P, w.2 ∈ A^m) (hgA : g ∈ A^k)
    (hform : ∀ w ∈ P, ∃ c t : ℝ, (w.1 : RMat) = scalarAffine b c t)
    (hnear : ∀ w ∈ P, dist (w.1 : RMat) 1 ≤ 1/64)
    (hfar : ∀ w ∈ P, s ≤ dist (w.1 : RMat) 1)
    (hbound : ∀ w ∈ P, ∀ i j, |w.1 i j| ≤ R ∧ |w.2 i j| ≤ R)
    (hg : ∀ i j, |g i j| ≤ R)
    (hclose : ∀ w ∈ P, dist (w.1 : RMat) (w.2 : RMat) ≤ ε)
    (hscale : (δ : ℝ) ≤ (3*ρ/256)*σ)
    (hscalarError : 1024*(2*R^2)^7*(8*R^2*ε) ≤ (δ : ℝ))
    (hfarError : 512*(2*R^2)^7*(8*R^2*ε) ≤ ρ*s/(288*M^2))
    (hbudget : 560*gain^2 ≤ K) :
    let X := P.image (fun w => traceSquareScalar w.1)
    (∀ x ∈ X, ∀ y ∈ X, x ≠ y → σ ≤ |x-y|) →
    (K*(X.card : ℝ) < (scalarCells δ (X+X)).card ∨
      K*(X.card : ℝ) < (scalarCells δ (X*X)).card) →
    ∃ D : Finset G, D.Nonempty ∧ (D : Set G) ⊆ A^(6*m+2*k) ∧
      (∀ w ∈ D, dist (w : RMat) 1 ≤ (5 : ℝ)^(6*m+2*k)*α ∧
        ρ*s/(288*M^2) ≤ dist (w : RMat) 1) ∧
      gain*(X.card : ℝ) < 25*(Metric.externalCoveringNumber δ
        ((D.image (fun w : G => Matrix.trace (w : RMat))) : Set ℝ) : ℝ≥0∞).toReal := by
  intro X hsep hgrowth
  let E := P ∪ P*P ∪ P*P⁻¹
  let F := P.image Prod.fst
  let Y := E.image (fun w => traceSquareScalar w.1)
  let d := (b*(g : RMat)-(g : RMat)*b).det
  let a₁ := 3*d/(8*b.det)
  let a₂ := 3*(4*b.det-d)/(8*b.det)
  let D₁ := (P ×ˢ E).image (fun w => w.2.2*w.1.2⁻¹*g*(w.2.2*w.1.2)*g⁻¹)
  let D₂ := (E ×ˢ P).image (fun w => w.2.2*w.1.2⁻¹*g*(w.2.2*w.1.2)*g⁻¹)
  have hPE : P ⊆ E := Finset.subset_union_left.trans Finset.subset_union_left
  have hE : E.Nonempty := hP.mono hPE
  have hX : X.Nonempty := hP.image _
  have hEnlarge := paired_source_enlargement P b hA1 hAi hR hε hsource hform hnear hbound hclose
  have hFform : ∀ u ∈ F, ∃ c t : ℝ, (u : RMat) = scalarAffine b c t := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    exact hform w hw
  have hXeq : F.image traceSquareScalar = X := by
    simp only [F, X, Finset.image_image, Function.comp_def]
  have hYeq : (F ∪ F*F ∪ F*F⁻¹).image traceSquareScalar = Y := by
    rw [← paired_enlargement_first_image P]
    simp only [E, Y, Finset.image_image, Function.comp_def]
  obtain ⟨hXY, hproduct⟩ := traceSquareScalar_finite_product_enlargement b F hb hFform
  rw [hXeq, hYeq] at hXY hproduct
  obtain ⟨ha₁, ha₂, _hsum, hmax⟩ := normalized_trace_square_coefficients hdet hbd hρ.le hD hD'
  change 3*ρ/256 ≤ |a₁| at ha₁
  change 3*ρ/256 ≤ |a₂| at ha₂
  change 3/4 ≤ max |a₁| |a₂| at hmax
  have ha₁ne : a₁ ≠ 0 := abs_pos.mp ((by positivity : 0 < 3*ρ/256).trans_le ha₁)
  have ha₂ne : a₂ ≠ 0 := abs_pos.mp ((by positivity : 0 < 3*ρ/256).trans_le ha₂)
  have hscale₁ : (δ : ℝ) ≤ |a₁| *σ := hscale.trans (mul_le_mul_of_nonneg_right ha₁ hσ)
  have hscale₂ : (δ : ℝ) ≤ |a₂| *σ := hscale.trans (mul_le_mul_of_nonneg_right ha₂ hσ)
  have hRlarge : R ≤ 2*R^2 := by nlinarith only [hR]
  have hR' : 1 ≤ 2*R^2 := hR.trans hRlarge
  have hε' : 0 ≤ 8*R^2*ε := by positivity
  have hMone : 1 ≤ M := (by norm_num : (1 : ℝ) ≤ 32).trans hM
  have hg' : ∀ i j, |g i j| ≤ 2*R^2 := fun i j => (hg i j).trans hRlarge
  have hformE : ∀ w ∈ E, ∃ c t : ℝ, (w.1 : RMat) = scalarAffine b c t :=
    fun w hw => (hEnlarge w hw).2.1
  have hboundE : ∀ w ∈ E, ∀ i j, |w.1 i j| ≤ 2*R^2 ∧ |w.2 i j| ≤ 2*R^2 :=
    fun w hw => (hEnlarge w hw).2.2.2.1
  have hcloseE : ∀ w ∈ E, dist (w.1 : RMat) (w.2 : RMat) ≤ 8*R^2*ε :=
    fun w hw => (hEnlarge w hw).2.2.2.2
  have hPEunion : P ∪ E ⊆ E := Finset.union_subset hPE (Finset.Subset.refl _)
  have hEPunion : E ∪ P ⊆ E := Finset.union_subset (Finset.Subset.refl _) hPE
  have hcells₁ := mixed_trace_cells_le_actual_cover P E b g hδ hR' hε' hb hdet
    (fun w hw => hformE w (hPEunion hw)) (fun w hw => hboundE w (hPEunion hw)) hg'
    (fun w hw => hcloseE w (hPEunion hw)) hscalarError
  have hcells₂ := mixed_trace_cells_le_actual_cover E P b g hδ hR' hε' hb hdet
    (fun w hw => hformE w (hEPunion hw)) (fun w hw => hboundE w (hEPunion hw)) hg'
    (fun w hw => hcloseE w (hEPunion hw)) hscalarError
  have hpair (u v : G × G) (huv : (u ∈ P ∧ v ∈ E) ∨ (u ∈ E ∧ v ∈ P)) :
      v.2*u.2⁻¹*g*(v.2*u.2)*g⁻¹ ∈ A^(6*m+2*k) ∧
      dist ((v.2*u.2⁻¹*g*(v.2*u.2)*g⁻¹ : G) : RMat) 1 ≤ (5 : ℝ)^(6*m+2*k)*α ∧
      ρ*s/(288*M^2) ≤ dist ((v.2*u.2⁻¹*g*(v.2*u.2)*g⁻¹ : G) : RMat) 1 := by
    have huE : u ∈ E := huv.elim (fun h => hPE h.1) (fun h => h.1)
    have hvE : v ∈ E := huv.elim (fun h => h.2) (fun h => hPE h.2)
    obtain ⟨cu,tu,huf⟩ := hformE u huE
    obtain ⟨cv,tv,hvf⟩ := hformE v hvE
    have hfarPair : s ≤ max (dist (u.1 : RMat) 1) (dist (v.1 : RMat) 1) := by
      rcases huv with h | h
      · exact (hfar u h.1).trans (le_max_left _ _)
      · exact (hfar v h.2).trans (le_max_right _ _)
    have hfarWord := mixed_readout_source_far b u.1 v.1 u.2 v.2 g
      hMone hρ hb hbn (hbd.trans hM) hbg huf hvf
      ((hEnlarge u huE).2.2.1.trans (by norm_num))
      ((hEnlarge v hvE).2.2.1.trans (by norm_num)) hD hD' hfarPair
      hR' hε' (fun i j => (hboundE u huE i j).1) (fun i j => (hboundE v hvE i j).1)
      (fun i j => (hboundE u huE i j).2) (fun i j => (hboundE v hvE i j).2)
      hg' (hcloseE u huE) (hcloseE v hvE) hfarError
    have hgeom : v.2*u.2⁻¹*g*(v.2*u.2)*g⁻¹ ∈ A^(6*m+2*k) ∧
        dist ((v.2*u.2⁻¹*g*(v.2*u.2)*g⁻¹ : G) : RMat) 1 ≤ (5 : ℝ)^(6*m+2*k)*α := by
      rcases huv with h | h
      · simpa only [show 2*m+2*(2*m)+2*k = 6*m+2*k by omega] using
          mixed_readout_word_geometry hAi hα hαone hA (hsource u h.1) (hEnlarge v h.2).1 hgA
      · simpa only [show 2*(2*m)+2*m+2*k = 6*m+2*k by omega] using
          mixed_readout_word_geometry hAi hα hαone hA (hEnlarge u h.1).1 (hsource v h.2) hgA
    exact ⟨hgeom.1, hgeom.2, hfarWord⟩
  have hD₁ : D₁.Nonempty ∧ (D₁ : Set G) ⊆ A^(6*m+2*k) ∧
      ∀ w ∈ D₁, dist (w : RMat) 1 ≤ (5 : ℝ)^(6*m+2*k)*α ∧
        ρ*s/(288*M^2) ≤ dist (w : RMat) 1 := by
    refine ⟨(hP.product hE).image _, ?_, ?_⟩
    · intro w hw
      obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
      exact (hpair u v (Or.inl (Finset.mem_product.mp huv))).1
    · intro w hw
      obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
      exact (hpair u v (Or.inl (Finset.mem_product.mp huv))).2
  have hD₂ : D₂.Nonempty ∧ (D₂ : Set G) ⊆ A^(6*m+2*k) ∧
      ∀ w ∈ D₂, dist (w : RMat) 1 ≤ (5 : ℝ)^(6*m+2*k)*α ∧
        ρ*s/(288*M^2) ≤ dist (w : RMat) 1 := by
    refine ⟨(hE.product hP).image _, ?_, ?_⟩
    · intro w hw
      obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
      exact (hpair u v (Or.inr (Finset.mem_product.mp huv))).1
    · intro w hw
      obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hw
      exact (hpair u v (Or.inr (Finset.mem_product.mp huv))).2
  have hinv (a : ℝ) (ha : a ≠ 0) (hbig : 3/4 ≤ |a|) : |a⁻¹| ≤ 2 := by
    rw [abs_inv, ← one_div, div_le_iff₀ (abs_pos.mpr ha)]
    linarith only [hbig]
  rcases le_max_iff.mp hmax with hbig₁ | hbig₂
  · have hmix := ScalarMetric.scalar_ring_growth_forces_mixed_growth
      (show 0 < (δ : ℝ) from hδ) ha₂ne ha₁ne (hinv a₁ ha₁ne hbig₁)
      X Y hX hXY hproduct hsep hscale₂ hbudget hgrowth
    refine ⟨D₂, hD₂.1, hD₂.2.1, hD₂.2.2, hmix.trans_le ?_⟩
    change ((scalarCells δ (Y.image (fun y => a₁*y)+X.image (fun x => a₂*x))).card : ℝ) ≤
      25*(Metric.externalCoveringNumber δ
        ((D₂.image (fun w : G => Matrix.trace (w : RMat))) : Set ℝ) : ℝ≥0∞).toReal at hcells₂
    simpa only [add_comm] using hcells₂
  · have hmix := ScalarMetric.scalar_ring_growth_forces_mixed_growth
      (show 0 < (δ : ℝ) from hδ) ha₁ne ha₂ne (hinv a₂ ha₂ne hbig₂)
      X Y hX hXY hproduct hsep hscale₁ hbudget hgrowth
    exact ⟨D₁, hD₁.1, hD₁.2.1, hD₁.2.2, hmix.trans_le hcells₁⟩

end TransposeFollowup.SL2Projection
