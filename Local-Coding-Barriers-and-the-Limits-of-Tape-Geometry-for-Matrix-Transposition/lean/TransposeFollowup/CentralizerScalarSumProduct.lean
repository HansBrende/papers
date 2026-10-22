import TransposeFollowup.CentralizerTraceSquareScalar
import TransposeFollowup.ScalarRingProjection
import OAI.MeasureTheory.Falconer.Estimates.ScalarPluennecke

/-! One mixed scalar sum controls both sums and products of the actual
trace-square coordinates. All additive combinatorics is imported; the
matrix family is enlarged explicitly by products and quotients. -/
namespace TransposeFollowup.ScalarMetric
open Classical Finset OAI.Falconer
open scoped Pointwise
set_option autoImplicit false

theorem scalar_double_cells_of_mixed {δ a b T m : ℝ} (hδ : 0<δ)
    (Z Y : Finset ℝ) (hZ : Z.Nonempty) (hm : 0 < m) (hb : b ≠ 0) (hbinv : |b⁻¹| ≤ 2)
    (hbase : m≤(scalarCells δ (Z.image (fun y=>a*y))).card)
    (hmixed : ((scalarCells δ (Z.image (fun y=>a*y)+Y.image (fun y=>b*y))).card:ℝ)≤T) :
    ((scalarCells δ (Y+Y)).card:ℝ)*m ≤ 112*T^2 := by
  let A := Z.image (fun y=>a*y)
  let B := Y.image (fun y=>b*y)
  let M := ((scalarCells δ A).card:ℝ)
  have hM : 0<M := hm.trans_le hbase
  have hsmall : ((scalarCells δ (A+B)).card:ℝ)≤(T/M)*M := by
    rw [div_mul_cancel₀ T hM.ne']
    exact hmixed
  have hp := scalar_pluennecke δ A B (hZ.image _) hsmall 2 0
  have hp' : ((scalarCells δ (B+B)).card:ℝ)≤4*(2*(T/M))^2*M := by
    simpa only [Nat.cast_zero,Nat.cast_ofNat,add_zero,zero_nsmul,sub_zero,two_nsmul,
      show (2:ℝ)+2=4 by norm_num,M] using hp
  have hpM : ((scalarCells δ (B+B)).card:ℝ)*M≤16*T^2 := by
    calc
      _ ≤ (4*(2*(T/M))^2*M)*M := mul_le_mul_of_nonneg_right hp' hM.le
      _ = _ := by field_simp; ring
  have heq : (B+B).image (fun y=>b⁻¹*y)=Y+Y := by
    have himage : (B+B).image (fun y=>b⁻¹*y) =
        B.image (fun y=>b⁻¹*y) + B.image (fun y=>b⁻¹*y) :=
      Finset.image_add (AddMonoidHom.mulLeft b⁻¹)
    rw [himage]
    have hi : B.image (fun y=>b⁻¹*y)=Y := by
      dsimp only [B]
      rw [Finset.image_image]
      simp only [Function.comp_def,← mul_assoc,inv_mul_cancel₀ hb,one_mul,Finset.image_id']
    rw [hi]
  have hdilate := scalar_dilation_cells hδ (B+B) 2 (by exact_mod_cast hbinv)
  rw [heq] at hdilate
  have hdilateR : ((scalarCells δ (Y+Y)).card:ℝ)≤7*(scalarCells δ (B+B)).card := by
    exact_mod_cast hdilate
  have hpm : ((scalarCells δ (B+B)).card:ℝ)*m≤16*T^2 :=
    (mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg _)).trans hpM
  nlinarith only [mul_le_mul_of_nonneg_right hdilateR hm.le,hpm]

theorem scalar_ring_cells_of_two_term_readout {δ a b T m : ℝ} (hδ : 0<δ)
    (X Y : Finset ℝ) (hX : X.Nonempty) (hm : 0 < m) (hb : b ≠ 0) (hbinv : |b⁻¹| ≤ 2)
    (hXY : X⊆Y)
    (hproduct : X*X⊆(Y+Y).image (fun y=>(2/3:ℝ)*y))
    (hbase : m≤(scalarCells δ (X.image (fun y=>a*y))).card)
    (hmixed : ((scalarCells δ (X.image (fun y=>a*y)+Y.image (fun y=>b*y))).card:ℝ)≤T) :
    ((scalarCells δ (X+X)).card:ℝ)*m≤112*T^2 ∧
      ((scalarCells δ (X*X)).card:ℝ)*m≤560*T^2 := by
  have hsum := scalar_double_cells_of_mixed hδ X Y hX hm hb hbinv hbase hmixed
  have hXX : X+X⊆Y+Y := Finset.add_subset_add hXY hXY
  have hadd : ((scalarCells δ (X+X)).card:ℝ)≤(scalarCells δ (Y+Y)).card := by
    exact_mod_cast Finset.card_le_card (scalarCells_mono δ hXX)
  have hprod : ((scalarCells δ (X*X)).card:ℝ)≤5*(scalarCells δ (Y+Y)).card := by
    have hs := Finset.card_le_card (scalarCells_mono δ hproduct)
    have hd := scalar_dilation_cells hδ (Y+Y) 1 (by norm_num : |(2/3:ℝ)|≤(1:ℕ))
    exact_mod_cast hs.trans hd
  exact ⟨(mul_le_mul_of_nonneg_right hadd hm.le).trans hsum,
    by nlinarith only [mul_le_mul_of_nonneg_right hprod hm.le,hsum]⟩

end TransposeFollowup.ScalarMetric

namespace TransposeFollowup.SL2Projection
open Classical Matrix Finset
open scoped Pointwise
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem traceSquareScalar_finite_product_enlargement (b:RMat) (F:Finset G)
    (hb:Matrix.trace b=0) (hform:∀u∈F,∃s t:ℝ,(u:RMat)=scalarAffine b s t) :
    let X := F.image traceSquareScalar
    let Y := (F ∪ F*F ∪ F*F⁻¹).image traceSquareScalar
    X⊆Y ∧ X*X⊆(Y+Y).image (fun y=>(2/3:ℝ)*y) := by
  dsimp only
  constructor
  · exact Finset.image_subset_image (Finset.subset_union_left.trans Finset.subset_union_left)
  · intro w hw
    obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_mul.mp hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨s,t,hs⟩ := hform u hu
    obtain ⟨p,q,hp⟩ := hform v hv
    refine Finset.mem_image.mpr ⟨traceSquareScalar (u*v)+traceSquareScalar (u*v⁻¹),?_,?_⟩
    · apply Finset.add_mem_add
      · exact Finset.mem_image.mpr ⟨u*v,
          Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mul_mem_mul hu hv)),rfl⟩
      · exact Finset.mem_image.mpr ⟨u*v⁻¹,
          Finset.mem_union_right _ (Finset.mul_mem_mul hu (Finset.inv_mem_inv hv)),rfl⟩
    · exact (traceSquareScalar_product b u v hb hs hp).symm

end TransposeFollowup.SL2Projection
