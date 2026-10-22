import TransposeFollowup.MobiusColumnHaar

/-! Explicit coordinate boxes around the identity. They compare the
existing Frobenius-radius smoothing ball with ordinary three-dimensional
rectangles in the proved column/shear Haar coordinates. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
set_option autoImplicit false

def identityColumnBox (s t : ℝ) : Set ((Fin 2 → ℝ) × ℝ) :=
  {z | |z.1 0 - 1| ≤ s ∧ |z.1 1| ≤ s ∧ |z.2| ≤ t}

theorem identityColumnBox_eq_prod (s t : ℝ) :
    identityColumnBox s t =
      Icc ![1 - s, -s] ![1 + s, s] ×ˢ Icc (-t) t := by
  ext z
  change (|z.1 0 - 1| ≤ s ∧ |z.1 1| ≤ s ∧ |z.2| ≤ t) ↔
    ((∀ i, ![1 - s, -s] i ≤ z.1 i) ∧ (∀ i, z.1 i ≤ ![1 + s, s] i)) ∧ -t ≤ z.2 ∧ z.2 ≤ t
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩
    exact ⟨⟨⟨by linarith, h3⟩, ⟨by linarith, h4⟩⟩, h5, h6⟩
  · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5, h6⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨h2, h4⟩, h5, h6⟩

theorem columnChart_identity_distance_le {t : ℝ} (ht : 0 ≤ t) (htsmall : t ≤ 1 / 4)
    {v : Fin 2 → ℝ} {b : ℝ} (hx : |v 0 - 1| ≤ t) (hy : |v 1| ≤ t) (hb : |b| ≤ t) :
    mobiusIdentityDistanceSq (columnChart (v, b)) ≤ 67 * t ^ 2 := by
  let q := columnSqNorm v
  have hxlo : 3 / 4 ≤ v 0 := by have := (abs_le.mp hx).1; linarith
  have hq : 1 / 2 ≤ q := by
    dsimp [q, columnSqNorm]
    nlinarith [sq_nonneg (v 0 - 3 / 4), sq_nonneg (v 1)]
  have hqpos : 0 < q := by linarith
  have hv : v ≠ 0 := by
    intro he
    rw [he] at hxlo
    norm_num at hxlo
  have hxabs : |v 0| ≤ 2 := by
    rw [abs_le]
    obtain ⟨hl, hu⟩ := abs_le.mp hx
    constructor <;> linarith
  have hysq : v 1 ^ 2 ≤ t ^ 2 := sq_le_sq' (abs_le.mp hy).1 (abs_le.mp hy).2
  have htsq : t ^ 2 ≤ t := by nlinarith
  have hyq : |v 1 / q| ≤ 2 * t := by
    rw [abs_div, abs_of_pos hqpos, div_le_iff₀ hqpos]
    have hh := mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ 2 * t)
    nlinarith only [hy, hh]
  have hbx : |b * v 0| ≤ 2 * t := by
    rw [abs_mul]
    simpa only [mul_comm] using mul_le_mul hb hxabs (abs_nonneg _) ht
  have h01 : |b * v 0 - v 1 / q| ≤ 4 * t := by
    have hh : |b * v 0 - v 1 / q| ≤ |b * v 0| + |v 1 / q| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (b * v 0) (-(v 1 / q))
    linarith
  have hnum : |v 0 - q| ≤ 3 * t := by
    calc
      _ = |v 0 * (1 - v 0) - v 1 ^ 2| := by congr 1; dsimp [q, columnSqNorm]; ring
      _ ≤ |v 0 * (1 - v 0)| + |v 1 ^ 2| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (v 0 * (1 - v 0)) (-(v 1 ^ 2))
      _ = |v 0| * |v 0 - 1| + v 1 ^ 2 := by
        rw [abs_mul, abs_sub_comm 1 (v 0), abs_of_nonneg (sq_nonneg (v 1))]
      _ ≤ 2 * t + t ^ 2 := add_le_add
        (mul_le_mul hxabs hx (abs_nonneg _) (by norm_num)) hysq
      _ ≤ _ := by linarith
  have hratio : |v 0 / q - 1| ≤ 6 * t := by
    rw [show v 0 / q - 1 = (v 0 - q) / q by field_simp]
    rw [abs_div, abs_of_pos hqpos, div_le_iff₀ hqpos]
    have hh := mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ 6 * t)
    nlinarith only [hnum, hh]
  have hby : |b * v 1| ≤ t := by
    rw [abs_mul]
    exact (mul_le_mul hb hy (abs_nonneg _) ht).trans (by simpa only [pow_two] using htsq)
  have h11 : |b * v 1 + v 0 / q - 1| ≤ 7 * t := by
    rw [show b * v 1 + v 0 / q - 1 = b * v 1 + (v 0 / q - 1) by ring]
    have hh := abs_add_le (b * v 1) (v 0 / q - 1)
    linarith
  rw [columnChart, dite_eq_left hv]
  change (v 0 - 1) ^ 2 + (b * v 0 - v 1 / q) ^ 2 + v 1 ^ 2 +
    (b * v 1 + v 0 / q - 1) ^ 2 ≤ _
  have hx2 := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
  have h012 := sq_le_sq' (abs_le.mp h01).1 (abs_le.mp h01).2
  have h112 := sq_le_sq' (abs_le.mp h11).1 (abs_le.mp h11).2
  nlinarith only [hx2, hysq, h012, h112]

theorem column_box_subset_mobiusIdentityBall {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    columnCoordinates ⁻¹' identityColumnBox (η / 16) (η / 16) ⊆ mobiusIdentityBall η := by
  intro g hg
  obtain ⟨hx, hy, hb⟩ := hg
  have he := columnChart_identity_distance_le (by positivity : (0 : ℝ) ≤ η / 16)
    (by linarith : η / 16 ≤ 1 / 4) hx hy hb
  change mobiusIdentityDistanceSq (columnChart (columnCoordinates g)) ≤ 67 * (η / 16) ^ 2 at he
  rw [columnChart_columnCoordinates] at he
  change mobiusIdentityDistanceSq g < η ^ 2
  nlinarith [sq_pos_of_pos hη]

theorem mobiusIdentityBall_columnShear_le {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    {g : Group} (hg : g ∈ mobiusIdentityBall η) : |columnShear g| ≤ 12 * η := by
  obtain ⟨h00, h01, h10, h11⟩ := mobiusIdentityBall_entry_bounds hη hg
  have hxlo : 1 / 2 ≤ g 0 0 := by have := (abs_lt.mp h00).1; linarith
  have hq : 1 / 4 ≤ columnSqNorm (firstColumn g) := by
    change 1 / 4 ≤ g 0 0 ^ 2 + g 1 0 ^ 2
    nlinarith [sq_nonneg (g 0 0 - 1 / 2), sq_nonneg (g 1 0)]
  have hqpos := columnSqNorm_pos (firstColumn_ne_zero g)
  have hxabs : |g 0 0| ≤ 3 / 2 := by
    rw [abs_le]
    obtain ⟨hl, hu⟩ := abs_lt.mp h00
    constructor <;> linarith
  have hvabs : |g 1 1| ≤ 3 / 2 := by
    rw [abs_le]
    obtain ⟨hl, hu⟩ := abs_lt.mp h11
    constructor <;> linarith
  have hn : |g 0 0 * g 0 1 + g 1 0 * g 1 1| ≤ 3 * η := by
    calc
      _ ≤ |g 0 0 * g 0 1| + |g 1 0 * g 1 1| := abs_add_le _ _
      _ = |g 0 0| * |g 0 1| + |g 1 0| * |g 1 1| := by rw [abs_mul, abs_mul]
      _ ≤ (3 / 2) * η + η * (3 / 2) := add_le_add
        (mul_le_mul hxabs h01.le (abs_nonneg _) (by norm_num))
        (mul_le_mul h10.le hvabs (abs_nonneg _) hη.le)
      _ = _ := by ring
  rw [columnShear, abs_div, abs_of_pos hqpos, div_le_iff₀ hqpos]
  have hh := mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ 12 * η)
  nlinarith only [hn, hh]

theorem mobiusIdentityBall_subset_column_box {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    mobiusIdentityBall η ⊆ columnCoordinates ⁻¹' identityColumnBox η (12 * η) := by
  intro g hg
  obtain ⟨h00, _, h10, _⟩ := mobiusIdentityBall_entry_bounds hη hg
  exact ⟨h00.le, h10.le, mobiusIdentityBall_columnShear_le hη hηhalf hg⟩

end TransposeFollowup.RealMobius
