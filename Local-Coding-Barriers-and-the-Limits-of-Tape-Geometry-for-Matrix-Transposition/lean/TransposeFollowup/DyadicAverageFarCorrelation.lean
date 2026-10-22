import TransposeFollowup.ComplexAverageActionSum
import TransposeFollowup.UniformDyadicConstants

/-! Uniform distant-band control for the actual symmetric average.
The inverse matrices require only the same bounded diagonal and lower-left entries. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

theorem dyadicBand_average_upper_far_sum_le {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (hG : ∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2)
    (D M : ℕ) (indices : ℕ → Finset ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    let u := fun k => smoothBand hf hs (dyadicAnnularCutoff k) (dyadicAnnularCutoff_hasCompactSupport k)
    (∑ r ∈ Finset.range M, ∑ j ∈ indices r,
      |inner ℝ (complexAverage G ((u j).toLp 2 volume)) ((u (j + (D + r))).toLp 2 volume)|) ≤
      ((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant * ‖hf.toLp f‖ ^ 2 := by
  classical
  let u := fun k => smoothBand hf hs (dyadicAnnularCutoff k) (dyadicAnnularCutoff_hasCompactSupport k)
  let A := fun (g : Group) r j =>
    |inner ℝ (schwartzActionL2 g (u j)) ((u (j + (D + r))).toLp 2 volume)|
  let B := ((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant * ‖hf.toLp f‖ ^ 2
  have hforward (i : Fin c) : (∑ r ∈ Finset.range M, ∑ j ∈ indices r, A (G i) r j) ≤ B :=
    dyadicBand_upper_far_sum_le_universal D M indices hf hs (G i) (hG i).1 (hG i).2.1
  have hinverse (i : Fin c) : (∑ r ∈ Finset.range M, ∑ j ∈ indices r, A (G i)⁻¹ r j) ≤ B := by
    apply dyadicBand_upper_far_sum_le_universal D M indices hf hs (G i)⁻¹
    · simpa only [inverse_entry_zero_zero] using (hG i).2.2
    · simpa only [inverse_entry_one_zero, abs_neg] using (hG i).2.1
  change (∑ r ∈ Finset.range M, ∑ j ∈ indices r,
    |inner ℝ (complexAverage G ((u j).toLp 2 volume)) ((u (j + (D + r))).toLp 2 volume)|) ≤ B
  calc
    _ ≤ ∑ r ∈ Finset.range M, ∑ j ∈ indices r,
        (2 * (c : ℝ))⁻¹ * ∑ i : Fin c, (A (G i) r j + A (G i)⁻¹ r j) :=
      Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ =>
        complexAverage_schwartz_inner_abs_le G (u j) _))
    _ = (2 * (c : ℝ))⁻¹ * ∑ i : Fin c,
        ((∑ r ∈ Finset.range M, ∑ j ∈ indices r, A (G i) r j) +
          (∑ r ∈ Finset.range M, ∑ j ∈ indices r, A (G i)⁻¹ r j)) := by
      simp_rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_comm (s := indices _), Finset.sum_comm (s := Finset.range M),
        Finset.sum_add_distrib]
    _ ≤ (2 * (c : ℝ))⁻¹ * ∑ _i : Fin c, (B + B) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        add_le_add (hforward i) (hinverse i))) (by positivity)
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
      field_simp
      ring

theorem dyadicBand_average_lower_far_sum_le {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (hG : ∀ i, |G i 0 0| ≤ 2 ∧ |G i 1 0| ≤ 2 ∧ |G i 1 1| ≤ 2)
    (D M : ℕ) (indices : ℕ → Finset ℕ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    let u := fun k => smoothBand hf hs (dyadicAnnularCutoff k) (dyadicAnnularCutoff_hasCompactSupport k)
    (∑ r ∈ Finset.range M, ∑ j ∈ indices r,
      |inner ℝ (complexAverage G ((u (j + (D + r))).toLp 2 volume)) ((u j).toLp 2 volume)|) ≤
      ((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant * ‖hf.toLp f‖ ^ 2 := by
  dsimp only
  refine le_trans ?_ (dyadicBand_average_upper_far_sum_le G hc hG D M indices hf hs)
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro j _
  apply le_of_eq
  congr 1
  exact (complexAverage_symmetric G _ _).trans (real_inner_comm _ _)

end TransposeFollowup.RealMobius
