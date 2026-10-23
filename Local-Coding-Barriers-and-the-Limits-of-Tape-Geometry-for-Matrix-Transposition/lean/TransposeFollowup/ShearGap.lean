import TransposeFollowup.ExpanderShearCut
import TransposeFollowup.ExpanderShearSupport
import TransposeFollowup.ShearGapEntropy

/-! Expansion and sparse rank force a macroscopic recovery gap for the shear.
The two halves may be chosen independently on input and output rows. -/
namespace TransposeFollowup.ExpanderShear
open scoped BigOperators
open Classical
set_option autoImplicit false

/-- The larger of the two complementary cut ranks is a fixed fraction of the
number of rows.  The degree hypotheses refer to the actual matrix L. -/
theorem balanced_cross_rank_sharp {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (D : ℕ) (hrow : ∀ j, (Finset.univ.filter (fun i => L j i ≠ 0)).card ≤ D)
    (hcol : ∀ i, (Finset.univ.filter (fun j => L j i ≠ 0)).card ≤ D)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta2 : eta ≤ 2)
    (hexp : ∀ S : Finset (Row m), 2 * S.card ≤ 2 * m →
      eta * S.card ≤ (outsideNeighbors (coreGraph L) S).card)
    (I J : Finset (Row m)) (hI : I.card = m) (hJ : J.card = m) :
    eta * (2 * m) / (4 * ((D : ℝ) + 1)^2) ≤
      max ((crossMatrix (matrix L) J I).rank : ℝ)
        ((crossMatrix (matrix L) Jᶜ Iᶜ).rank : ℝ) := by
  have hc := balanced_cross_nnz_sharp L eta heta0 heta2 hexp I J hI hJ
  have h₁ := cross_nnz_le_rank_mul_sq L D hrow hcol I J
  have h₂ := cross_nnz_le_rank_mul_sq L D hrow hcol Iᶜ Jᶜ
  have hn : ((nnz (crossMatrix (matrix L) J I) +
      nnz (crossMatrix (matrix L) Jᶜ Iᶜ) : ℕ) : ℝ) ≤
      (((crossMatrix (matrix L) J I).rank : ℝ) +
       ((crossMatrix (matrix L) Jᶜ Iᶜ).rank : ℝ)) * ((D : ℝ) + 1)^2 := by
    exact_mod_cast (show nnz (crossMatrix (matrix L) J I) +
        nnz (crossMatrix (matrix L) Jᶜ Iᶜ) ≤
        ((crossMatrix (matrix L) J I).rank + (crossMatrix (matrix L) Jᶜ Iᶜ).rank) *
          (D + 1)^2 by nlinarith [h₁, h₂])
  have hm₁ := mul_le_mul_of_nonneg_right
    (le_max_left ((crossMatrix (matrix L) J I).rank : ℝ)
      ((crossMatrix (matrix L) Jᶜ Iᶜ).rank : ℝ)) (sq_nonneg ((D : ℝ) + 1))
  have hm₂ := mul_le_mul_of_nonneg_right
    (le_max_right ((crossMatrix (matrix L) J I).rank : ℝ)
      ((crossMatrix (matrix L) Jᶜ Iᶜ).rank : ℝ)) (sq_nonneg ((D : ℝ) + 1))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((D : ℝ) + 1)^2)).mpr
  nlinarith only [hc, hn, hm₁, hm₂]

/-- Arbitrary-law recovery obstruction. Entropies use natural logarithms;
dividing by log 2 gives the bit statement with c₀ = eta/(4(D+1)²). -/
theorem balanced_conditional_gap_sharp {Ω : Type*} [Fintype Ω] {m W : ℕ}
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → Bank m W) (L : Matrix (Fin m) (Fin m) Bit)
    (D : ℕ) (hrow : ∀ j, (Finset.univ.filter (fun i => L j i ≠ 0)).card ≤ D)
    (hcol : ∀ i, (Finset.univ.filter (fun j => L j i ≠ 0)).card ≤ D)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta2 : eta ≤ 2)
    (hexp : ∀ S : Finset (Row m), 2 * S.card ≤ 2 * m →
      eta * S.card ≤ (outsideNeighbors (coreGraph L) S).card)
    (I J : Finset (Row m)) (hI : I.card = m) (hJ : J.card = m) :
    eta / (4 * ((D : ℝ) + 1)^2) * (2 * m * W) * Real.log 2 -
      ((2 * m * W : ℝ) * Real.log 2 - observationEntropy p X) ≤
    max (conditionalObservationEntropy p (fun ω => rowView I (X ω))
          (fun ω => rowView J (shear L (X ω))))
      (conditionalObservationEntropy p (fun ω => rowView Iᶜ (X ω))
          (fun ω => rowView Jᶜ (shear L (X ω)))) := by
  have hcard : Fintype.card (Row m) = 2 * m := by simp [Row]; omega
  have hIJ : I.card = J.card := hI.trans hJ.symm
  have hIJc : Iᶜ.card = Jᶜ.card := by simp only [Finset.card_compl, hIJ]
  have h₁ := conditional_rowView_ge_cross_rank p hp hp1 (matrix L) I J hIJ W X
  have h₂ := conditional_rowView_ge_cross_rank p hp hp1 (matrix L) Iᶜ Jᶜ hIJc W X
  have hmap : rowMap (matrix L) = shear (W := W) L := by
    funext x r w
    exact (shear_eq_mulVec L x r w).symm
  rw [hmap, hcard] at h₁ h₂
  push_cast at h₁ h₂
  have hr := balanced_cross_rank_sharp L D hrow hcol eta heta0 heta2 hexp I J hI hJ
  have hlog : 0 ≤ (W : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hscaled := mul_le_mul_of_nonneg_right hr hlog
  rw [max_mul_of_nonneg _ _ hlog] at hscaled
  have hm := max_le_max h₁ h₂
  have he : max
      (((crossMatrix (matrix L) J I).rank : ℝ) * W * Real.log 2 -
        ((2 : ℝ) * m * W * Real.log 2 - observationEntropy p X))
      (((crossMatrix (matrix L) Jᶜ Iᶜ).rank : ℝ) * W * Real.log 2 -
        ((2 : ℝ) * m * W * Real.log 2 - observationEntropy p X)) =
      max (((crossMatrix (matrix L) J I).rank : ℝ) * (W * Real.log 2))
        (((crossMatrix (matrix L) Jᶜ Iᶜ).rank : ℝ) * (W * Real.log 2)) -
        ((2 : ℝ) * m * W * Real.log 2 - observationEntropy p X) := by
    rw [max_sub_sub_right]
    simp only [mul_assoc]
  rw [he] at hm
  calc
    _ = eta * (2 * m) / (4 * ((D : ℝ) + 1)^2) * (W * Real.log 2) -
        ((2 : ℝ) * m * W * Real.log 2 - observationEntropy p X) := by ring
    _ ≤ _ := (sub_le_sub_right hscaled _).trans hm

/-- Comparison with the original, weaker recovery coefficient. -/
theorem recovery_coefficient_le_sharp (D : ℕ) (eta : ℝ) (heta0 : 0 ≤ eta) :
    eta / (8 * ((D : ℝ) + 1)^2) ≤ eta / (4 * ((D : ℝ) + 1)^2) := by
  apply div_le_div_of_nonneg_left heta0 (by positivity)
  nlinarith [sq_nonneg ((D : ℝ) + 1)]

theorem balanced_cross_rank {m : ℕ} (L : Matrix (Fin m) (Fin m) Bit)
    (D : ℕ) (hrow : ∀ j, (Finset.univ.filter (fun i => L j i ≠ 0)).card ≤ D)
    (hcol : ∀ i, (Finset.univ.filter (fun j => L j i ≠ 0)).card ≤ D)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hexp : ∀ S : Finset (Row m), 2 * S.card ≤ 2 * m →
      eta * S.card ≤ (outsideNeighbors (coreGraph L) S).card)
    (I J : Finset (Row m)) (hI : I.card = m) (hJ : J.card = m) :
    eta * (2 * m) / (8 * ((D : ℝ) + 1)^2) ≤
      max ((crossMatrix (matrix L) J I).rank : ℝ)
        ((crossMatrix (matrix L) Jᶜ Iᶜ).rank : ℝ) := by
  have h := balanced_cross_rank_sharp L D hrow hcol eta heta0 (by linarith) hexp I J hI hJ
  exact (div_le_div_of_nonneg_left (mul_nonneg heta0 (by positivity))
    (by positivity) (by nlinarith [sq_nonneg ((D : ℝ) + 1)])).trans h

theorem balanced_conditional_gap {Ω : Type*} [Fintype Ω] {m W : ℕ}
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (X : Ω → Bank m W) (L : Matrix (Fin m) (Fin m) Bit)
    (D : ℕ) (hrow : ∀ j, (Finset.univ.filter (fun i => L j i ≠ 0)).card ≤ D)
    (hcol : ∀ i, (Finset.univ.filter (fun j => L j i ≠ 0)).card ≤ D)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hexp : ∀ S : Finset (Row m), 2 * S.card ≤ 2 * m →
      eta * S.card ≤ (outsideNeighbors (coreGraph L) S).card)
    (I J : Finset (Row m)) (hI : I.card = m) (hJ : J.card = m) :
    eta / (8 * ((D : ℝ) + 1)^2) * (2 * m * W) * Real.log 2 -
      ((2 * m * W : ℝ) * Real.log 2 - observationEntropy p X) ≤
    max (conditionalObservationEntropy p (fun ω => rowView I (X ω))
          (fun ω => rowView J (shear L (X ω))))
      (conditionalObservationEntropy p (fun ω => rowView Iᶜ (X ω))
          (fun ω => rowView Jᶜ (shear L (X ω)))) := by
  have h := balanced_conditional_gap_sharp p hp hp1 X L D hrow hcol eta heta0
    (by linarith) hexp I J hI hJ
  have hc := mul_le_mul_of_nonneg_right (recovery_coefficient_le_sharp D eta heta0)
    (show 0 ≤ (2 * m * W : ℝ) * Real.log 2 by positivity)
  simp only [← mul_assoc] at hc
  linarith

end TransposeFollowup.ExpanderShear
