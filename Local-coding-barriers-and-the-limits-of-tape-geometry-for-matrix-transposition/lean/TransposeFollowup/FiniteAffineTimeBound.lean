import TransposeFollowup.OmittedVisitBound
import TransposeFollowup.AffineBranchCuts

/-! Quantitative omitted-time obstruction. The abbreviation below packages
the restriction of the original M* inequality to 0 < θ < 1/2, retaining
its original crossing and labeling definitions. This restriction suffices
for the omitted-time obstruction; full M* implies it. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Transpose.Tape
open scoped ENNReal BigOperators
set_option autoImplicit false

abbrev SatisfiesStar {k : ℕ} (P : Fin k → ℝ → ℝ) (c₀ : ℝ) : Prop :=
  ∀ (θ : ℝ≥0∞), 0 < θ → θ < 1/2 → ∀ (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
    PiecewiseConstOn β S c₀ → (∀ ℓ, volume {u | u ∈ Icc 0 c₀ ∧ u ∉ S ∧ β u=ℓ} ≤ θ) →
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p)+2*θ+2*k*volume (S ∩ Icc 0 c₀)

theorem one_le_of_star_small_cuts {k : ℕ} {P : Fin k → ℝ → ℝ} {c₀ : ℝ}
    (hstar : SatisfiesStar P c₀) (B : ℝ≥0∞)
    (hsmall : ∀ θ ε : ℝ, 0 < θ → 0 < ε → ∃ β : ℝ → ℕ,
      PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Icc 0 c₀ ∧ β x=n} ≤ ENNReal.ofReal θ) ∧
      (∑ t, ∫⁻ p, levelCross (P t) ∅ β c₀ p) ≤ B+ENNReal.ofReal ε) : 1 ≤ B := by
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  let θ : ℝ := min ((δ : ℝ)/4) (1/4)
  have hθ : 0 < θ := lt_min (by exact div_pos hδ (by norm_num)) (by norm_num)
  have hθδ : θ ≤ (δ : ℝ)/4 := min_le_left _ _
  have hθq : θ ≤ 1/4 := min_le_right _ _
  have hq : ENNReal.ofReal (1/4)=(1/4 : ℝ≥0∞) := by norm_num [ENNReal.ofReal_div_of_pos]
  have hθhalf : ENNReal.ofReal θ < 1/2 :=
    (ENNReal.ofReal_le_ofReal hθq).trans_lt (by rw [hq]; norm_num)
  obtain ⟨β,hpc,hm,hcut⟩ := hsmall θ θ hθ hθ
  have hclass (ℓ : ℕ) : volume {u | u ∈ Icc 0 c₀ ∧ u ∉ (∅ : Set ℝ) ∧ β u=ℓ} ≤
      ENNReal.ofReal θ := by simpa only [Set.mem_empty_iff_false,not_false_eq_true,true_and] using hm ℓ
  have hs := hstar (ENNReal.ofReal θ) (ENNReal.ofReal_pos.mpr hθ) hθhalf ∅ β
    Impl.finUnionIcc_empty hpc hclass
  simp only [Set.empty_inter,measure_empty,mul_zero,add_zero] at hs
  calc
    1 ≤ (∑ t, ∫⁻ p, levelCross (P t) ∅ β c₀ p)+2*ENNReal.ofReal θ := hs
    _ ≤ (B+ENNReal.ofReal θ)+2*ENNReal.ofReal θ := add_le_add hcut le_rfl
    _ = B+ENNReal.ofReal (3*θ) := by
      rw [add_assoc,show (2 : ℝ≥0∞)=ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num),← ENNReal.ofReal_add hθ.le (by positivity)]
      congr 2
      ring
    _ ≤ B+(δ : ℝ≥0∞) := by
      apply add_le_add le_rfl
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by dsimp [θ] at *; linarith)

theorem star_half_le_finite_affine_omission {k : ℕ} {ι : Type*} [Fintype ι]
    {c₀ : ℝ} (hc : 0 ≤ c₀) (P : Fin k → ℝ → ℝ)
    (hP : ∀ t, LipschitzOnWith 1 (P t) (Icc 0 c₀))
    (a b : Fin k → ι → ℝ) (J : Fin k → ι → Set ℝ)
    (hJm : ∀ t i, MeasurableSet (J t i)) (hJi : ∀ t i, J t i ⊆ Icc 0 c₀)
    (hE : ∀ t, IsCompact (Icc 0 c₀ \ ⋃ i, J t i))
    (hPa : ∀ t i x, x ∈ J t i → P t x=a t i*x+b t i)
    (hstar : SatisfiesStar P c₀) :
    (1/2 : ℝ≥0∞) ≤ ∑ t, volume (Icc 0 c₀ \ ⋃ i, J t i) := by
  apply (ENNReal.div_le_iff' (by norm_num) (by norm_num)).mpr
  apply one_le_of_star_small_cuts hstar
  intro θ ε hθ hε
  obtain ⟨β,_,hpc,hm,hcut⟩ := exists_finite_affine_branch_small_cut hc P a b J hJm hJi hPa hθ hε
  refine ⟨β,hpc,hm,?_⟩
  calc
    _ ≤ ∑ t, ((∫⁻ p, ({q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, J t i ∧ q.2 ∈ ⋃ i, J t i}.ncard : ℝ≥0∞))+
          2*volume (Icc 0 c₀ \ ⋃ i, J t i)) :=
      Finset.sum_le_sum (fun t _ => lintegral_levelCross_delete_le (hP t) β _ (hE t))
    _ = (∑ t, ∫⁻ p, ({q ∈ crossPairs (P t) ∅ β c₀ p |
        q.1 ∈ ⋃ i, J t i ∧ q.2 ∈ ⋃ i, J t i}.ncard : ℝ≥0∞))+
          2*∑ t, volume (Icc 0 c₀ \ ⋃ i, J t i) := by rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := by
      simpa only [add_comm] using add_le_add hcut.le
        (le_refl (2*∑ t, volume (Icc 0 c₀ \ ⋃ i, J t i)))

end TransposeFollowup.AffineMotion
