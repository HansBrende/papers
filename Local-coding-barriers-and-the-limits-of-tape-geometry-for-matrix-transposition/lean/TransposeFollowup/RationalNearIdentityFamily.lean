import TransposeFollowup.DyadicFreeFamily
import TransposeFollowup.MobiusWalkEntrySupport
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Rational free generators at every sufficiently small real radius.
This proves the generator construction only; it does not assume or prove
random-walk flattening. -/
namespace TransposeFollowup.RationalFreePair
open Classical
set_option autoImplicit false

theorem exists_dyadic_radius_near {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 32) :
    ∃ r : ℕ, 5 ≤ r ∧ ε / 2 ≤ dyadicRadius r ∧ dyadicRadius r < ε := by
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near
    ((le_div_iff₀ hε).mpr (by simpa using hε1)) (by norm_num : (1 : ℝ) < 2)
  have hnear : dyadicRadius (n + 1) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ (n + 1))).mpr
    have h := (div_lt_iff₀ hε).mp hn'
    linarith
  have hr : 5 ≤ n + 1 := by
    by_contra h
    have hp : (2 : ℝ) ^ (n + 1) ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h := (div_lt_iff₀ hε).mp (hn'.trans_le hp)
    norm_num at h
    linarith
  refine ⟨n + 1, hr, ?_, hnear⟩
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (n + 1))).mpr
  have h := (le_div_iff₀ hε).mp hn
  rw [pow_succ]
  nlinarith

theorem inverse_dyadic_radius_le {ε : ℝ} {r : ℕ} (hε : 0 < ε)
    (hnear : ε / 2 ≤ dyadicRadius r) : 1 / dyadicRadius r ≤ 2 / ε := by
  apply (div_le_div_iff₀ (dyadicRadius_pos r) hε).mpr
  linarith

theorem exists_rational_near_identity_free_family {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 32) :
    ∃ (m Q : ℕ) (g : Fin m → Group),
      2 ≤ m ∧ 0 < Q ∧
      (1 / ε) ^ 3 ≤ (m : ℝ) ∧
      1 / ε ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ (1 / ε) ^ 3840 ∧ Q ≤ m ^ 640 ∧
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (Finset.univ.image g).card = m ∧
      (Finset.univ.image (realEmbedding ∘ g)).card = m ∧
      ∀ k, HasDenominator Q (g k) ∧
        realEmbedding (g k) ∈ RealMobius.mobiusIdentityBall ε ∧
        (realEmbedding (g k))⁻¹ ∈ RealMobius.mobiusIdentityBall ε ∧
        realEmbedding (g k) ∈ RealMobius.matrixEntryBox 2 := by
  obtain ⟨r, hr, hnear, hrad⟩ := exists_dyadic_radius_near hε hεsmall
  obtain ⟨g, hg, hgr, hc, hcr, hn⟩ := exists_dyadic_free_family hr
  have hinv : 1 / ε ≤ 1 / dyadicRadius r :=
    one_div_le_one_div_of_le (dyadicRadius_pos r) hrad.le
  have hm : (1 / ε) ^ 3 ≤ ((2 ^ (3 * r) : ℕ) : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity) hinv 3
    simpa only [dyadicRadius, one_div_one_div, Nat.cast_pow, Nat.cast_ofNat,
      ← pow_mul, mul_comm r 3] using h
  have hQ : (dyadicDenominator r : ℝ) ≤ (1 / ε) ^ 3840 := by
    have htwo : 2 / ε ≤ (1 / ε) ^ 2 := by
      have hεhalf : ε ≤ 1 / 2 := by linarith
      have hi : 2 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith)
      have h0 : 0 ≤ 1 / ε := by positivity
      rw [show 2 / ε = 2 * (1 / ε) by ring]
      nlinarith
    calc
      _ ≤ (1 / dyadicRadius r) ^ 1920 := dyadicDenominator_radius_upper r
      _ ≤ (2 / ε) ^ 1920 := pow_le_pow_left₀ (by dsimp [dyadicRadius]; positivity)
        (inverse_dyadic_radius_le hε hnear) _
      _ ≤ ((1 / ε) ^ 2) ^ 1920 := pow_le_pow_left₀ (by positivity) htwo _
      _ = _ := by rw [← pow_mul]
  have hballs : RealMobius.mobiusIdentityBall (dyadicRadius r) ⊆
      RealMobius.mobiusIdentityBall ε := by
    intro a ha
    exact ha.trans_le ((sq_le_sq₀ (dyadicRadius_pos r).le hε.le).mpr hrad.le)
  have hbox := RealMobius.mobiusIdentityBall_subset_entryBox_two hε (show ε ≤ 1 by linarith)
  refine ⟨2 ^ (3 * r), dyadicDenominator r, g, ?_, dyadicDenominator_pos r,
    hm, hinv.trans (dyadicDenominator_radius_lower r), hQ,
    dyadicDenominator_card_bound r, hg, hgr, hc, hcr, ?_⟩
  · simpa using (pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2)
      (show 1 ≤ 3 * r by omega))
  · intro k
    exact ⟨(hn k).1, hballs (hn k).2.1, hballs (hn k).2.2, hbox (hballs (hn k).2.1)⟩

end TransposeFollowup.RationalFreePair
