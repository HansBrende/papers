import Transpose.Tape.MStarTM
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! Continuous representations of actual unit-step walks and a quantitative
comparison with the original block trajectory. All representations agree at
integer ticks; the rounding error is proved from the original block bounds. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false

theorem exists_lipschitz_real_walk {h : ℕ → ℤ} (hh : UnitSteps h) :
    ∃ f : ℝ → ℝ, LipschitzWith 1 f ∧ ∀ n : ℕ, f n=(h n : ℝ) := by
  let F : ℝ → ℝ := fun x => (h ⌊x⌋₊ : ℝ)
  have hF : LipschitzOnWith 1 F (Set.range (fun n : ℕ => (n : ℝ))) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro x ⟨n,rfl⟩ y ⟨m,rfl⟩
    have hd : |(h n : ℝ)-(h m : ℝ)| ≤ |(n : ℝ)-m| := by
      exact_mod_cast unitSteps_dist' hh m n
    simpa [F,Real.dist_eq] using hd
  obtain ⟨f,hf,hagree⟩ := hF.extend_real
  exact ⟨f,hf,fun n => (by simpa [F] using (hagree (Set.mem_range_self n)).symm)⟩

noncomputable def physicalPath (L : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := f (L*t)/L

theorem physicalPath_lipschitz {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : LipschitzWith 1 f) : LipschitzWith 1 (physicalPath L f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hf.dist_le_mul (L*x) (L*y)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at h ⊢
  rw [physicalPath,physicalPath,← sub_div,abs_div,abs_of_pos hL,div_le_iff₀ hL]
  calc
    |f (L*x)-f (L*y)| ≤ |L*x-L*y| := h
    _ = |x-y| * L := by rw [← mul_sub,abs_mul,abs_of_pos hL]; ring

theorem block_physical_sample_error {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    {h : ℕ → ℤ} {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    (he : ∀ m : ℕ, f m=(h m : ℝ)) {u : ℝ} (hu : 0 ≤ u) :
    |blockTraj r n h u-physicalPath ((n : ℝ)*r) f u| ≤ 2/(n : ℝ) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let N : ℕ := ⌊u*n⌋₊
  let A : ℤ := blockOf r (h (N*r))
  have hround : |(A : ℝ)*r-(h (N*r) : ℝ)| ≤ r := by
    have hs := blockOf_spec hr (h (N*r))
    have hs1 : (A : ℝ)*r ≤ (h (N*r) : ℝ) := by exact_mod_cast hs.1
    have hs2 : (h (N*r) : ℝ) < ((A : ℝ)+1)*r := by exact_mod_cast hs.2
    rw [abs_le]
    constructor <;> nlinarith
  have htime : |((N*r : ℕ) : ℝ)-((n : ℝ)*r)*u| ≤ r := by
    have hl : (N : ℝ) ≤ u*n := Nat.floor_le (mul_nonneg hu hnp.le)
    have hh : u*n < (N : ℝ)+1 := Nat.lt_floor_add_one _
    push_cast
    rw [abs_le]
    constructor <;> nlinarith
  have hsample : |(h (N*r) : ℝ)-f (((n : ℝ)*r)*u)| ≤ r := by
    have hs := hf.dist_le_mul ((N*r : ℕ) : ℝ) (((n : ℝ)*r)*u)
    simp only [NNReal.coe_one,one_mul,Real.dist_eq,he] at hs
    exact hs.trans htime
  change |(A : ℝ)/n-f (((n : ℝ)*r)*u)/((n : ℝ)*r)| ≤ 2/(n : ℝ)
  rw [show (A : ℝ)/n-f (((n : ℝ)*r)*u)/((n : ℝ)*r)=
      ((A : ℝ)*r-f (((n : ℝ)*r)*u))/((n : ℝ)*r) by field_simp,
    abs_div,abs_of_pos (mul_pos hnp hrp),div_le_iff₀ (mul_pos hnp hrp)]
  calc
    |(A : ℝ)*r-f (((n : ℝ)*r)*u)| ≤
        |(A : ℝ)*r-(h (N*r) : ℝ)|+|(h (N*r) : ℝ)-f (((n : ℝ)*r)*u)| :=
      abs_sub_le _ _ _
    _ ≤ (r : ℝ)+r := add_le_add hround hsample
    _ = 2/(n : ℝ)*((n : ℝ)*r) := by field_simp; norm_num


theorem real_walk_floor_error {h : ℕ → ℤ} {f : ℝ → ℝ}
    (hf : LipschitzWith 1 f) (he : ∀ m : ℕ, f m=(h m : ℝ))
    {x : ℝ} (hx : 0 ≤ x) : |f x-(h ⌊x⌋₊ : ℝ)| ≤ 1 := by
  have hd := hf.dist_le_mul x (⌊x⌋₊ : ℝ)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,he] at hd
  apply hd.trans
  rw [abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le hx))]
  linarith [Nat.lt_floor_add_one x]

theorem physicalPath_sample_error {L : ℝ} (hL : 0 < L) {h : ℕ → ℤ} {f : ℝ → ℝ}
    (hf : LipschitzWith 1 f) (he : ∀ m : ℕ, f m=(h m : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    |physicalPath L f t-(h ⌊L*t⌋₊ : ℝ)/L| ≤ 1/L := by
  rw [physicalPath,← sub_div,abs_div,abs_of_pos hL]
  exact div_le_div_of_nonneg_right (real_walk_floor_error hf he (mul_nonneg hL.le ht)) hL.le

end TransposeFollowup.RegularMotion
