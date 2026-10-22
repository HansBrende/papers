import TransposeFollowup.FiniteAffineTimeBound

/-! A closed finite-case consequence for the original M* condition. The
countable-branch and positive-exceptional-time endpoints remain separate
obligations; a finite cover is not substituted for those requirements. -/
namespace TransposeFollowup.AffineMotion
open Classical Set Finset MeasureTheory Transpose.Tape
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem exists_finite_affine_path_small_cut {τ ι : Type*} [Fintype τ] [Fintype ι]
    {c₀ : ℝ} (hc : 0 ≤ c₀) (P : τ → ℝ → ℝ)
    (a b : τ → ι → ℝ) (J : τ → ι → Set ℝ)
    (hJm : ∀ t i, MeasurableSet (J t i))
    (hJi : ∀ t i, J t i ⊆ Icc 0 c₀)
    (hcover : ∀ t, Icc 0 c₀ ⊆ ⋃ i, J t i)
    (hP : ∀ t i x, x ∈ J t i → P t x=a t i*x+b t i)
    {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ β : ℝ → ℕ, Measurable β ∧ PiecewiseConstOn β ∅ c₀ ∧
      (∀ n, volume {x | x ∈ Icc 0 c₀ ∧ β x=n} ≤ ENNReal.ofReal θ) ∧
      (∑ t, ∫⁻ p, levelCross (P t) ∅ β c₀ p) < ENNReal.ofReal ε := by
  obtain ⟨β,hβ,hpc,hm,hcut⟩ :=
    exists_finite_affine_branch_small_cut hc P a b J hJm hJi hP hθ hε
  refine ⟨β,hβ,hpc,hm,lt_of_le_of_lt ?_ hcut⟩
  apply Finset.sum_le_sum
  intro t _
  apply lintegral_mono
  intro p
  have he : {q ∈ crossPairs (P t) ∅ β c₀ p |
      q.1 ∈ ⋃ i, J t i ∧ q.2 ∈ ⋃ i, J t i}=crossPairs (P t) ∅ β c₀ p := by
    ext q
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,hcover t h.1.1.1,hcover t h.1.2.1.1⟩
  dsimp only
  rw [he]
  unfold levelCross
  split_ifs
  · exact le_rfl
  · exact zero_le

theorem not_star_of_finite_affine_cover {k : ℕ} {ι : Type*} [Fintype ι]
    {c₀ : ℝ} (hc : 0 ≤ c₀) (P : Fin k → ℝ → ℝ)
    (a b : Fin k → ι → ℝ) (J : Fin k → ι → Set ℝ)
    (hJm : ∀ t i, MeasurableSet (J t i))
    (hJi : ∀ t i, J t i ⊆ Icc 0 c₀)
    (hcover : ∀ t, Icc 0 c₀ ⊆ ⋃ i, J t i)
    (hP : ∀ t i x, x ∈ J t i → P t x=a t i*x+b t i)
    (hstar : ∀ (θ : ℝ≥0∞), 0 < θ → θ < 1 / 2 → ∀ (S : Set ℝ) (β : ℝ → ℕ), FinUnionIcc S →
      PiecewiseConstOn β S c₀ → (∀ ℓ, volume {u | u ∈ Icc 0 c₀ ∧ u ∉ S ∧ β u=ℓ} ≤ θ) →
      1 ≤ (∑ t, ∫⁻ p, levelCross (P t) S β c₀ p)+2*θ+2*k*volume (S ∩ Icc 0 c₀)) : False := by
  have hbad : (1 : ℝ≥0∞) ≤ 0 := one_le_of_star_small_cuts hstar 0 (by
    intro θ ε hθ hε
    obtain ⟨β,_,hpc,hm,hcut⟩ := exists_finite_affine_path_small_cut
      hc P a b J hJm hJi hcover hP hθ hε
    exact ⟨β,hpc,hm,by simpa only [zero_add] using hcut.le⟩)
  norm_num at hbad

end TransposeFollowup.AffineMotion
