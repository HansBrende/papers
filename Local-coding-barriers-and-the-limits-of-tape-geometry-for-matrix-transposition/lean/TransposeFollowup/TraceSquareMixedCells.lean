import TransposeFollowup.CentralizerScalarSumProduct
import TransposeFollowup.MixedReadoutSourceTransfer
import TransposeFollowup.ScalarMetricBridge

/-! The smaller readout coefficient is paid by scalar separation. A
mixed scalar sum controls the ring operations by the imported estimates,
and its cells transfer to traces of actual source words at the same radius. -/
namespace TransposeFollowup.ScalarMetric
open Classical Finset OAI.Falconer
open scoped Pointwise
set_option autoImplicit false

theorem scalar_dilated_cells_card {δ σ a : ℝ} (hδ : 0 < δ) (ha : a ≠ 0)
    (X : Finset ℝ) (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → σ ≤ |x-y|)
    (hscale : δ ≤ |a| *σ) :
    (scalarCells δ (X.image (fun x => a*x))).card = X.card := by
  have hsep' : ∀ x ∈ X.image (fun x => a*x), ∀ y ∈ X.image (fun x => a*x),
      x ≠ y → δ ≤ |x-y| := by
    intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
    rw [← mul_sub, abs_mul]
    exact hscale.trans (mul_le_mul_of_nonneg_left
      (hsep u hu v hv (fun h => hne (congrArg (a*·) h))) (abs_nonneg a))
  exact (card_image_of_injOn (scalarCells_injective hδ hsep')).trans
    (card_image_of_injective _ (mul_right_injective₀ ha))

/-- This explicitly pays the square-root loss of the mixed-sum estimate.
The scalar growth factor `K` must dominate `560*G^2`. -/
theorem scalar_ring_growth_forces_mixed_growth {δ σ a b K G : ℝ}
    (hδ : 0 < δ) (ha : a ≠ 0) (hb : b ≠ 0) (hbinv : |b⁻¹| ≤ 2)
    (X Y : Finset ℝ) (hX : X.Nonempty) (hXY : X ⊆ Y)
    (hproduct : X*X ⊆ (Y+Y).image (fun y => (2/3 : ℝ)*y))
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → σ ≤ |x-y|)
    (hscale : δ ≤ |a| *σ) (hbudget : 560*G^2 ≤ K)
    (hgrowth : K*(X.card : ℝ) < (scalarCells δ (X+X)).card ∨
      K*(X.card : ℝ) < (scalarCells δ (X*X)).card) :
    G*(X.card : ℝ) < (scalarCells δ
      (X.image (fun x => a*x)+Y.image (fun y => b*y))).card := by
  have hm : 0 < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hcard := scalar_dilated_cells_card hδ ha X hsep hscale
  by_contra hfail
  have hsmall := le_of_not_gt hfail
  obtain ⟨hadd, hmul⟩ := scalar_ring_cells_of_two_term_readout hδ X Y hX hm hb hbinv
    hXY hproduct (by exact_mod_cast hcard.ge) hsmall
  have hbound : 560*(G*(X.card : ℝ))^2 ≤ K*(X.card : ℝ)^2 := by
    calc
      _ = (560*G^2)*(X.card : ℝ)^2 := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (sq_nonneg _)
  rcases hgrowth with h | h
  · have ht := mul_lt_mul_of_pos_right h hm
    have hp : 112*(G*(X.card : ℝ))^2 ≤ 560*(G*(X.card : ℝ))^2 := by
      nlinarith only [sq_nonneg (G*(X.card : ℝ))]
    nlinarith only [ht, hadd.trans (hp.trans hbound)]
  · have ht := mul_lt_mul_of_pos_right h hm
    nlinarith only [ht, hmul.trans hbound]

end TransposeFollowup.ScalarMetric

namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius OAI.Falconer
open scoped Pointwise Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

/-- No abstract mixed-cell covering hypothesis is used: each scalar pair
is compared with the trace of its actual source word. -/
theorem mixed_trace_cells_le_actual_cover (P Q : Finset (G × G)) (b : RMat) (g : G)
    {δ : ℝ≥0} {R ε : ℝ} (hδ : 0 < δ) (hR : 1 ≤ R) (hε : 0 ≤ ε)
    (hb : Matrix.trace b = 0) (hdet : b.det ≠ 0)
    (hform : ∀ w ∈ P ∪ Q, ∃ c t : ℝ, (w.1 : RMat) = scalarAffine b c t)
    (hbound : ∀ w ∈ P ∪ Q, ∀ i j, |w.1 i j| ≤ R ∧ |w.2 i j| ≤ R)
    (hg : ∀ i j, |g i j| ≤ R)
    (hclose : ∀ w ∈ P ∪ Q, dist (w.1 : RMat) (w.2 : RMat) ≤ ε)
    (herror : 1024*R^7*ε ≤ (δ : ℝ)) :
    let X := P.image (fun w => traceSquareScalar w.1)
    let Y := Q.image (fun w => traceSquareScalar w.1)
    let d := (b*(g : RMat)-(g : RMat)*b).det
    let a₁ := 3*d/(8*b.det)
    let a₂ := 3*(4*b.det-d)/(8*b.det)
    let D := (P ×ˢ Q).image (fun w => w.2.2*w.1.2⁻¹*g*(w.2.2*w.1.2)*g⁻¹)
    ((scalarCells δ (X.image (fun x => a₁*x)+Y.image (fun y => a₂*y))).card : ℝ) ≤
      25*(Metric.externalCoveringNumber δ
        ((D.image (fun w : G => Matrix.trace (w : RMat))) : Set ℝ) : ℝ≥0∞).toReal := by
  intro X Y d a₁ a₂ D
  let T := D.image (fun w : G => Matrix.trace (w : RMat))
  have hnear : ∀ x ∈ X.image (fun x => a₁*x)+Y.image (fun y => a₂*y),
      ∃ y ∈ T, |x-y| ≤ (δ : ℝ) := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx₀
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy₀
    have hu' := Finset.mem_union_left Q hu
    have hv' := Finset.mem_union_right P hv
    obtain ⟨c, t, huf⟩ := hform u hu'
    obtain ⟨p, q, hvf⟩ := hform v hv'
    have hread := traceSquareScalar_linear_readout b u.1 v.1 g hb hdet huf hvf
    have herr := mixed_readout_source_error u.1 v.1 u.2 v.2 g hR hε
      (fun i j => (hbound u hu' i j).1) (fun i j => (hbound v hv' i j).1)
      (fun i j => (hbound u hu' i j).2) (fun i j => (hbound v hv' i j).2)
      hg (hclose u hu') (hclose v hv')
    have htrace := (trace_error_le_frobenius_dist
      ((v.1*u.1⁻¹*g*(v.1*u.1)*g⁻¹ : G) : RMat)
      ((v.2*u.2⁻¹*g*(v.2*u.2)*g⁻¹ : G) : RMat)).trans
        (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2))
    refine ⟨Matrix.trace ((v.2*u.2⁻¹*g*(v.2*u.2)*g⁻¹ : G) : RMat), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr
        ⟨(u,v), Finset.mem_product.mpr ⟨hu,hv⟩, rfl⟩, rfl⟩
    · change Matrix.trace ((v.1*u.1⁻¹*g*(v.1*u.1)*g⁻¹ : G) : RMat) =
        a₁*traceSquareScalar u.1+a₂*traceSquareScalar v.1 at hread
      rw [← hread]
      exact htrace.trans (by nlinarith only [herror])
  have hcells := scalarCells_near_card_nat (show 0 < (δ : ℝ) from hδ)
    (X.image (fun x => a₁*x)+Y.image (fun y => a₂*y)) T 1
    (by simpa only [Nat.cast_one, one_mul] using hnear)
  have hcellsR : ((scalarCells δ (X.image (fun x => a₁*x)+Y.image (fun y => a₂*y))).card : ℝ) ≤
      5*(scalarCells δ T).card := by exact_mod_cast hcells
  have hcover := ScalarMetric.scalarCells_card_le_externalCoveringNumber hδ T
  calc
    _ ≤ 5*((scalarCells δ T).card : ℝ) := hcellsR
    _ ≤ 5*(5*(Metric.externalCoveringNumber δ (T : Set ℝ) : ℝ≥0∞).toReal) :=
      mul_le_mul_of_nonneg_left hcover (by norm_num)
    _ = _ := by ring

end TransposeFollowup.SL2Projection
