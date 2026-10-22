import TransposeFollowup.CellCenteredRelativeError
import Mathlib.Algebra.Order.Floor.Ring

/-! One compatible choice of the grid-dependent expansion margin,
cell-uniformity tolerance and integer trimming width. -/
namespace TransposeFollowup
open Classical Set MeasureTheory
set_option autoImplicit false

noncomputable def expansionMargin (K : ℕ) : ℝ := 1/(100*(K:ℝ)^2)

noncomputable def uniformityTolerance (K : ℕ) : ℝ :=
  (K:ℝ)*((K-1:ℕ):ℝ)*expansionMargin K

noncomputable def trimWidth (K : ℕ) (eta : ℝ) : ℕ := ⌈8*eta*(K:ℝ)⌉₊

theorem expansionMargin_pos {K : ℕ} (hK : 0<K) : 0<expansionMargin K := by
  unfold expansionMargin
  positivity

theorem expansionMargin_small {K : ℕ} (hK : 10000 ≤ K) : expansionMargin K ≤ 1/2000 := by
  have hk : (10000:ℝ) ≤ K := by exact_mod_cast hK
  unfold expansionMargin
  apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(K:ℝ)^2)).2
  nlinarith

theorem uniformityTolerance_bounds {K : ℕ} (hK : 1 ≤ K) :
    0 ≤ uniformityTolerance K ∧ uniformityTolerance K ≤ 1/100 := by
  have hk : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hs := (expansionMargin_pos (by omega : 0<K)).le
  have hsub : ((K-1:ℕ):ℝ) ≤ (K:ℝ) := by exact_mod_cast Nat.sub_le K 1
  refine ⟨by unfold uniformityTolerance; positivity,?_⟩
  calc
    _ ≤ (K:ℝ)*(K:ℝ)*expansionMargin K :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsub hk.le) hs
    _ = 1/100 := by unfold expansionMargin; field_simp

theorem trimWidth_displacement {K : ℕ} (hK : 0<K) (eta : ℝ) :
    8*eta ≤ (trimWidth K eta:ℝ)/(K:ℝ) := by
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  exact (le_div_iff₀ hk).2 (Nat.le_ceil (8*eta*(K:ℝ)))

theorem trimWidth_fraction {K : ℕ} (hK : 10000 ≤ K) {eta : ℝ}
    (he0 : 0 ≤ eta) (he : eta ≤ 1/1000000) :
    2*(trimWidth K eta:ℝ)/(K:ℝ) ≤ 1/2000 := by
  have hk : (10000:ℝ) ≤ K := by exact_mod_cast hK
  have hkp : (0:ℝ)<K := by linarith
  have hc := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 8*eta*(K:ℝ))
  have heK := mul_le_mul_of_nonneg_right he hkp.le
  apply (div_le_iff₀ hkp).2
  change 2*(⌈8*eta*(K:ℝ)⌉₊:ℝ) ≤ _
  nlinarith only [hc,heK,hk]

theorem trimWidth_twice_le {K : ℕ} (hK : 10000 ≤ K) {eta : ℝ}
    (he0 : 0 ≤ eta) (he : eta ≤ 1/1000000) : 2*trimWidth K eta ≤ K := by
  have hk : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hb := (div_le_iff₀ hk).1 (trimWidth_fraction hK he0 he)
  have hm : (2:ℝ)*(trimWidth K eta:ℝ) ≤ (K:ℝ) := by linarith
  exact_mod_cast hm

namespace RationalUnitMobius

theorem augmented_correlation_with_parameters {c K : ℕ} (F : Fin c → RationalUnitMobius)
    (hK : 10000 ≤ K) {eta : ℝ} (hnear : ∀ p,(F p).NearIdentity eta)
    (he : eta ≤ 1/1000000) {A : Set ℝ} (hA : MeasurableSet A)
    (hunit : A⊆Icc (0:ℝ) 1) (hhalf : volume.real A ≤ 1/2)
    (hsmall : volume.real (restrictedImageUnion
      (augmentedFamily F (unitStep K) (unitStep_small (by omega : 2 ≤ K))) A) ≤
        (1+expansionMargin K)*volume.real A) (p : Fin c) :
    let T := gridTrim A (centralCells K (trimWidth K eta))
    let f := cellCenteredIndicator K T
    (3/4)*(∫ x,(f x)^2) ≤ (∫ x in Icc (0:ℝ) 1,(F p).whole.weightedPullback f x*f x) ∧
    (3/4)*(∫ x,(f x)^2) ≤ (∫ x in Icc (0:ℝ) 1,(F p).inverse.whole.weightedPullback f x*f x) := by
  have he0 := (hnear p).nonneg
  have hs := (expansionMargin_pos (by omega : 0<K)).le
  have hd := uniformityTolerance_bounds (by omega : 1 ≤ K)
  have hu := augmented_cell_uniformity F (by omega : 2 ≤ K) hA hunit (expansionMargin K) hs hsmall
  exact augmented_central_correlation F (by omega) (trimWidth_twice_le hK he0 he) p (hnear p) he
    (trimWidth_displacement (by omega) eta) hs (expansionMargin_small hK) hd.1 hd.2
    (trimWidth_fraction hK he0 he) hA hunit hhalf hu hsmall

end RationalUnitMobius
end TransposeFollowup
