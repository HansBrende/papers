import TransposeFollowup.SL2TranslatedCluster

/-! Actual matrix bounds for a bounded word and for normalizing a
retained subset by that word. The original identity-ball definition is
identified with its ambient Frobenius distance. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix Set RealMobius
open scoped Matrix.Norms.Frobenius Pointwise
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => RealMobius.Group

theorem mobiusIdentityBall_iff_frobenius_dist (g : G) {α : ℝ} (hα : 0 < α) :
    g ∈ mobiusIdentityBall α ↔ dist (g : RMat) 1 < α := by
  have he : dist (g : RMat) 1 ^ 2 = mobiusIdentityDistanceSq g := by
    rw [frobenius_dist_sq]
    norm_num [mobiusIdentityDistanceSq, Fin.sum_univ_two, Matrix.one_apply]
    ring
  change mobiusIdentityDistanceSq g < α ^ 2 ↔ dist (g : RMat) 1 < α
  rw [← he]
  exact sq_lt_sq₀ dist_nonneg hα.le

theorem set_pow_dist_from_one_le {A : Set G} {α : ℝ}
    (hα : 0 < α) (hαone : α ≤ 1) (hA : A ⊆ mobiusIdentityBall α) (n : ℕ) :
    ∀ x ∈ A ^ n, dist (x : RMat) 1 ≤ (5 : ℝ) ^ n * α := by
  have hAb : A ⊆ matrixEntryBox 2 := hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  induction n with
  | zero =>
    intro x hx
    have he : x = 1 := by simpa only [pow_zero, Set.mem_one] using hx
    subst x
    simpa using hα.le
  | succ n ih =>
    rw [pow_succ]
    rintro x ⟨u, hu, v, hv, rfl⟩
    have hvd : dist (v : RMat) 1 ≤ α := ((mobiusIdentityBall_iff_frobenius_dist v hα).mp (hA hv)).le
    have hvn : ‖(v : RMat)‖ ≤ 4 := by
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
        frobenius_norm_le_of_entry_bound (by norm_num : (0 : ℝ) ≤ 2) (hAb hv)
    have hmul : dist ((u * v : G) : RMat) (v : RMat) ≤ dist (u : RMat) 1 * ‖(v : RMat)‖ := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul, one_mul] using frobenius_dist_right_mul (u : RMat) 1 (v : RMat)
    have hone : 1 ≤ (5 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have halpha : α ≤ (5 : ℝ) ^ n * α := by nlinarith
    calc
      _ ≤ dist ((u * v : G) : RMat) (v : RMat) + dist (v : RMat) 1 := dist_triangle _ _ _
      _ ≤ dist (u : RMat) 1 * ‖(v : RMat)‖ + α := add_le_add hmul hvd
      _ ≤ ((5 : ℝ) ^ n * α) * 4 + α := add_le_add
        (mul_le_mul (ih u hu) hvn (norm_nonneg _) (by positivity)) le_rfl
      _ ≤ ((5 : ℝ) ^ n * α) * 4 + (5 : ℝ) ^ n * α := add_le_add le_rfl halpha
      _ = _ := by rw [pow_succ]; ring

theorem dist_normalized_from_one_le (h x : G) {H : ℝ}
    (hH : 0 ≤ H) (hh : ∀ i j, |h i j| ≤ H) :
    dist ((h⁻¹ * x : G) : RMat) 1 ≤ 2 * H * dist (x : RMat) (h : RMat) := by
  have he : ((h⁻¹ : G) : RMat) * (h : RMat) = 1 := by
    exact congrArg (fun z : G => (z : RMat)) (show h⁻¹ * h = 1 by group)
  have hd := frobenius_dist_left_mul ((h⁻¹ : G) : RMat) (x : RMat) (h : RMat)
  rw [he] at hd
  exact hd.trans (mul_le_mul_of_nonneg_right
    (frobenius_norm_le_of_entry_bound hH (matrixEntryBox_inv hh)) dist_nonneg)

theorem dist_le_normalized_from_one (h x : G) {H : ℝ}
    (hH : 0 ≤ H) (hh : ∀ i j, |h i j| ≤ H) :
    dist (x : RMat) (h : RMat) ≤ 2 * H * dist ((h⁻¹ * x : G) : RMat) 1 := by
  have he : (h : RMat) * ((h⁻¹ * x : G) : RMat) = (x : RMat) := by
    exact congrArg (fun z : G => (z : RMat)) (show h * (h⁻¹ * x) = x by group)
  have hd := frobenius_dist_left_mul (h : RMat) ((h⁻¹ * x : G) : RMat) 1
  rw [he, mul_one] at hd
  exact hd.trans (mul_le_mul_of_nonneg_right (frobenius_norm_le_of_entry_bound hH hh) dist_nonneg)

theorem normalized_subset_geometry (n : ℕ) (h : G) {A R : Set G} {α H r : ℝ}
    (hα : 0 < α) (hαone : α ≤ 1) (hA : A ⊆ mobiusIdentityBall α) (hRA : R ⊆ A)
    (hhpow : h ∈ A ^ n) (hH : 1 ≤ H) (hh : ∀ i j, |h i j| ≤ H)
    (hsmall : 8 * H * (1 + (5 : ℝ) ^ n) * α ≤ 1)
    (hfar : ∀ x ∈ R, r ≤ dist (x : RMat) (h : RMat)) :
    let D := (fun x : G => h⁻¹ * x) '' R
    D ⊆ mobiusIdentityBall (1 / 2) ∧
      (∀ g ∈ D, ∀ i j, |g i j| ≤ 4 * H) ∧
      (∀ g ∈ D, r / (2 * H) ≤ dist (g : RMat) 1) := by
  have hHpos : 0 < H := by linarith
  have hAb : A ⊆ matrixEntryBox 2 := hA.trans (mobiusIdentityBall_subset_entryBox_two hα hαone)
  have hhd := set_pow_dist_from_one_le hα hαone hA n h hhpow
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨x, hx, rfl⟩
    apply (mobiusIdentityBall_iff_frobenius_dist _ (by norm_num : (0 : ℝ) < 1 / 2)).mpr
    have hxd := ((mobiusIdentityBall_iff_frobenius_dist x hα).mp (hA (hRA hx))).le
    have hxh : dist (x : RMat) (h : RMat) ≤ (1 + (5 : ℝ) ^ n) * α := by
      have ht := dist_triangle (x : RMat) 1 (h : RMat)
      rw [dist_comm 1 (h : RMat)] at ht
      nlinarith
    have hd := (dist_normalized_from_one_le h x hHpos.le hh).trans
      (mul_le_mul_of_nonneg_left hxh (by positivity))
    nlinarith
  · rintro g ⟨x, hx, rfl⟩ i j
    have hb := matrixEntryBox_mul (matrixEntryBox_inv hh) (hAb (hRA hx)) i j
    convert hb using 1; ring
  · rintro g ⟨x, hx, rfl⟩
    apply (div_le_iff₀ (by positivity : 0 < 2 * H)).mpr
    calc
      r ≤ dist (x : RMat) (h : RMat) := hfar x hx
      _ ≤ 2 * H * dist ((h⁻¹ * x : G) : RMat) 1 := dist_le_normalized_from_one h x hHpos.le hh
      _ = _ := mul_comm _ _

end TransposeFollowup.SL2Projection
