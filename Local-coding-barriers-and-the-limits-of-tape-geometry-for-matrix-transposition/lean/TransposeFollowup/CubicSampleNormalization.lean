import TransposeFollowup.SpanningCommutingExtraction
import TransposeFollowup.SeparatedMatrixSample
import OAI.MeasureTheory.Falconer.Geometry.ScalarBallCandidates

/-! Normalize a cubic cluster bound by the retained sample. The input
cube is exactly the spanning extraction inequality; the mixed-cover
and sampling losses remain explicit. Small clusters are paid for by
the actual separated distribution at twice the native cover radius. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius ENNReal NNReal
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem scalarBallMass_image {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : Function.Injective a) (v r : ℝ) :
    OAI.Falconer.scalarBallMass (Finset.univ.image a) v r =
      (Fintype.card {i : ι // |a i - v| ≤ r} : ℝ) := by
  classical
  unfold OAI.Falconer.scalarBallMass
  rw [Finset.filter_image, Finset.card_image_of_injective _ ha]
  congr 1
  exact (Fintype.card_subtype _).symm

theorem spanning_cube_sample_normalization {η θ N T V P H S m : ℝ}
    (hη : 0 < η) (hN : 0 < N) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hcube : η ^ θ * N ^ 4 ≤ (9 * T * H * V) ^ 3)
    (hmixed : T ≤ P * N) (hretain : V ≤ S * m) :
    N ≤ ((9 * P * H) ^ 3 * η ^ (-θ) * S ^ 3) * m ^ 3 := by
  have hbound : 9 * T * H * V ≤ 9 * (P * N) * H * (S * m) :=
    mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmixed (by norm_num)) hH) hretain hV
      (by positivity)
  have hc : (η ^ θ * N) * N ^ 3 ≤
      ((9 * P * H) ^ 3 * S ^ 3 * m ^ 3) * N ^ 3 := by
    calc
      _ = η ^ θ * N ^ 4 := by ring
      _ ≤ (9 * T * H * V) ^ 3 := hcube
      _ ≤ (9 * (P * N) * H * (S * m)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hbound 3
      _ = _ := by ring
  have hc' := (mul_le_mul_iff_left₀ (pow_pos hN 3)).mp hc
  have hi := mul_le_mul_of_nonneg_left hc' (Real.rpow_nonneg hη.le (-θ))
  have hinv : η ^ (-θ) * η ^ θ = 1 := by
    rw [← Real.rpow_add hη, neg_add_cancel, Real.rpow_zero]
  calc
    N = η ^ (-θ) * (η ^ θ * N) := by rw [← mul_assoc, hinv, one_mul]
    _ ≤ η ^ (-θ) * ((9 * P * H) ^ 3 * S ^ 3 * m ^ 3) := hi
    _ = _ := by ring

theorem coveringNumber_lower_of_distribution {A : Set G} {κ γ : ℝ} {η : ℝ≥0}
    (hη : 0 < η) (hwindow : 2 * (η : ℝ) < (η : ℝ) ^ γ)
    (hfin : Metric.externalCoveringNumber η
      ((fun x : G => (x : RMat)) '' A) ≠ ⊤)
    (hdistribution : ∀ ρ : ℝ, (η : ℝ) < ρ → ρ < (η : ℝ) ^ γ →
      ∃ T : Finset G, (T : Set G) ⊆ A ∧
        Metric.IsSeparated (ENNReal.ofReal ρ)
          ((fun x : G => (x : RMat)) '' (T : Set G)) ∧
        ρ ^ (-κ) ≤ (T.card : ℝ)) :
    (2 * (η : ℝ)) ^ (-κ) ≤
      (Metric.externalCoveringNumber η
        ((fun x : G => (x : RMat)) '' A) : ℝ≥0∞).toReal := by
  classical
  have hηR : 0 < (η : ℝ) := hη
  obtain ⟨T, hTA, hsep, hcard⟩ := hdistribution (2 * (η : ℝ)) (by linarith) hwindow
  let F := T.image (fun x : G => (x : RMat))
  have hFcard : F.card = T.card :=
    Finset.card_image_of_injective _ Subtype.coe_injective
  have hFsub : (F : Set RMat) ⊆ (fun x : G => (x : RMat)) '' A := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨g, hTA hg, rfl⟩
  have hFsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → 2 * (η : ℝ) < dist x y := by
    intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hs := hsep ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ hne
    change ENNReal.ofReal (2 * (η : ℝ)) < edist (u : RMat) (v : RMat) at hs
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at hs
    exact hs
  have hc := separated_matrix_card_le_coveringNumber F hFsub hFsep hfin
  rw [hFcard] at hc
  exact hcard.trans hc

theorem one_le_scaled_cover_of_lower {η r κ N : ℝ}
    (hη : 0 < η) (hr : η ≤ r) (hκ : 0 ≤ κ)
    (hN : (2 * η) ^ (-κ) ≤ N) :
    1 ≤ (2 : ℝ) ^ κ * r ^ κ * N := by
  have hN0 : 0 ≤ N := (Real.rpow_nonneg (by positivity) _).trans hN
  calc
    1 = (2 * η) ^ κ * (2 * η) ^ (-κ) := by
      rw [← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero]
    _ ≤ (2 * η) ^ κ * N := mul_le_mul_of_nonneg_left hN (by positivity)
    _ ≤ (2 * r) ^ κ * N :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) (by linarith) hκ) hN0
    _ = _ := by rw [Real.mul_rpow (by norm_num) (hη.le.trans hr)]

theorem normalized_count_of_cubic {m n N A W C r κ : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hA : 0 ≤ A) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hlocal : n ^ 3 ≤ A * r ^ κ * N) (hglobal : N ≤ W * m ^ 3)
    (hbudget : A * W ≤ C ^ 3) :
    n ≤ C * r ^ (κ / 3) * m := by
  have he : (r ^ (κ / 3)) ^ 3 = r ^ κ := by
    rw [← Real.rpow_mul_natCast hr]
    congr 1
    norm_num
  apply (pow_le_pow_iff_left₀ hn (by positivity : 0 ≤ C * r ^ (κ / 3) * m)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  calc
    n ^ 3 ≤ A * r ^ κ * N := hlocal
    _ ≤ A * r ^ κ * (W * m ^ 3) :=
      mul_le_mul_of_nonneg_left hglobal (by positivity)
    _ = (A * W) * (r ^ κ * m ^ 3) := by ring
    _ ≤ C ^ 3 * (r ^ κ * m ^ 3) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = (C * r ^ (κ / 3) * m) ^ 3 := by rw [mul_pow, mul_pow, he]; ring

/-- The whole-family cover cube and the sampler's upper cardinality
bound retain an ambient dimension gap, with every power loss included. -/
theorem sample_cardinality_upper_of_cubic
    {η κ s l e p m V N T S L E S₀ L₀ E₀ J₀ C : ℝ}
    (hη : 0 < η) (hηone : η ≤ 1) (hκ : κ ≤ 3) (he : 0 ≤ e) (hp : 0 ≤ p)
    (hm : 0 ≤ m) (hT : 0 ≤ T) (hS : 0 ≤ S) (hL : 0 ≤ L)
    (hS₀ : 0 ≤ S₀) (hL₀ : 0 ≤ L₀) (hE₀ : 0 ≤ E₀) (hJ₀ : 0 ≤ J₀)
    (hC : 0 ≤ C)
    (hcard : m ≤ V) (hcube : V ^ 3 ≤ 4 * (S * L) ^ 3 * (E * T + 1))
    (hNbound : N ≤ η ^ (-(3 - κ)))
    (hTbound : T ≤ J₀ * η ^ (-p) * N)
    (hSbound : S ≤ S₀ * η ^ (-s)) (hLbound : L ≤ L₀ * η ^ (-l))
    (hEbound : E ≤ E₀ * η ^ (-e))
    (hconstant : 4 * (S₀ * L₀) ^ 3 * (E₀ * J₀ + 1) ≤ C ^ 3) :
    m ≤ C * η ^ (-(s + l + (3 - κ + e + p) / 3)) := by
  let ν := 3 - κ + e + p
  let D := 4 * (S₀ * L₀) ^ 3 * (E₀ * J₀ + 1)
  have hν : 0 ≤ ν := by dsimp only [ν]; linarith only [hκ, he, hp]
  have hpower : 1 ≤ η ^ (-ν) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hηone (neg_nonpos.mpr hν)
  have hT' : T ≤ J₀ * η ^ (-p) * η ^ (-(3 - κ)) :=
    hTbound.trans (mul_le_mul_of_nonneg_left hNbound (by positivity))
  have hET : E * T + 1 ≤ (E₀ * J₀ + 1) * η ^ (-ν) := by
    have hpowers : η ^ (-e) * η ^ (-p) * η ^ (-(3 - κ)) = η ^ (-ν) := by
      rw [← Real.rpow_add hη, ← Real.rpow_add hη]
      congr 1
      dsimp only [ν]
      ring
    have hh := mul_le_mul hEbound hT' hT (by positivity : 0 ≤ E₀ * η ^ (-e))
    have hh' : E * T ≤ E₀ * J₀ * η ^ (-ν) := by
      calc
        _ ≤ (E₀ * η ^ (-e)) * (J₀ * η ^ (-p) * η ^ (-(3 - κ))) := hh
        _ = (E₀ * J₀) * (η ^ (-e) * η ^ (-p) * η ^ (-(3 - κ))) := by ring
        _ = _ := by rw [hpowers]
    nlinarith only [hh', hpower]
  have hSL : S * L ≤ S₀ * L₀ * η ^ (-(s + l)) := by
    have hpowers : η ^ (-s) * η ^ (-l) = η ^ (-(s + l)) := by
      rw [← Real.rpow_add hη]
      congr 1
      ring
    calc
      _ ≤ (S₀ * η ^ (-s)) * (L₀ * η ^ (-l)) :=
        mul_le_mul hSbound hLbound hL (by positivity)
      _ = (S₀ * L₀) * (η ^ (-s) * η ^ (-l)) := by ring
      _ = _ := by rw [hpowers]
  have hpowers : (η ^ (-(s + l))) ^ 3 * η ^ (-ν) =
      η ^ (-(3 * (s + l) + ν)) := by
    rw [← Real.rpow_mul_natCast hη.le, ← Real.rpow_add hη]
    congr 1
    norm_num
    ring
  have hlocal : m ^ 3 ≤ D * η ^ (-(3 * (s + l) + ν)) * 1 := by
    calc
      _ ≤ V ^ 3 := pow_le_pow_left₀ hm hcard 3
      _ ≤ 4 * (S * L) ^ 3 * (E * T + 1) := hcube
      _ ≤ 4 * (S * L) ^ 3 * ((E₀ * J₀ + 1) * η ^ (-ν)) :=
        mul_le_mul_of_nonneg_left hET (by positivity)
      _ ≤ 4 * (S₀ * L₀ * η ^ (-(s + l))) ^ 3 *
          ((E₀ * J₀ + 1) * η ^ (-ν)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hS hL) hSL 3)
            (by norm_num)) (by positivity)
      _ = D * ((η ^ (-(s + l))) ^ 3 * η ^ (-ν)) := by
        dsimp only [D]
        ring
      _ = _ := by rw [hpowers, mul_one]
  have hh := normalized_count_of_cubic (by norm_num : (0 : ℝ) ≤ 1) hm
    (by dsimp only [D]; positivity : 0 ≤ D) hC hη.le hlocal
    (by norm_num : (1 : ℝ) ≤ 1 * 1 ^ 3)
    (by simpa only [D, mul_one] using hconstant)
  simpa only [mul_one, show -(3 * (s + l) + ν) / 3 =
    -(s + l + (3 - κ + e + p) / 3) by dsimp only [ν]; ring] using hh

end TransposeFollowup.SL2Projection
